// Copyright 2020 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of mouse-sync
//
//  mouse-sync is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  mouse-sync is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with mouse-sync.  If not, see <http://www.gnu.org/licenses/>.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `LruHashSet` is a thread-safe hash set to order the elements by "Least Recently Used (LRU)".

use super::bucket_chain::BucketChain;
use super::node::Node;
use crate::{Lock8, Mutex8, Mutex8Guard};
use core::alloc::{GlobalAlloc, Layout};
use core::cell::Cell;
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::ptr::null_mut;
use std::alloc::handle_alloc_error;
use std::borrow::Borrow;

/// Entry of `LruHashSet` .
///
/// The node of `LruHashSet` will be `Node<Entry<T>>` .
/// It has 2 links to order the nodes by "LRU".
struct Entry<T> {
    element: T,
    prev: *mut Node<Self>,
    next: *mut Node<Self>,
}

impl<T> From<T> for Entry<T> {
    fn from(element: T) -> Self {
        Self {
            element,
            prev: null_mut(),
            next: null_mut(),
        }
    }
}

impl<T> Hash for Entry<T>
where
    T: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.element.hash(state);
    }
}

impl<T> Deref for Entry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.element
    }
}

/// Implementation of thread-safe hash set, which orders the elements by "Least Recent Used (LRU)".
pub struct LruHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    chain: BucketChain<Entry<T>, B>,

    order_mutex: Mutex8,
    lru: Cell<*mut Node<Entry<T>>>,
    mru: Cell<*mut Node<Entry<T>>>,

    alloc: A,
}

impl<T, B, A> LruHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    /// Creates a new instance.
    ///
    /// `LruHashSet` is a chaining hash set and `bucket_count` is the length of the bucket chain.
    ///
    /// It has the following affects to make `bucket_count` large.
    ///
    /// - Reducing hash conflict properbility. (This is characteristics of chaining hash set.)
    /// - Reducing lock wait time.
    ///   (Because `LruHashSet` locks each bucket. More bucket will reduce hash conflict and lock competition.)
    /// - Increasing memory usage for bucket_chain.
    pub fn new(bucket_count: usize, hasher_builder: B, alloc: A) -> Self {
        Self {
            chain: BucketChain::new(bucket_count, hasher_builder, &alloc),

            order_mutex: Mutex8::new(),
            lru: Cell::new(null_mut()),
            mru: Cell::new(null_mut()),

            alloc,
        }
    }
}

impl<T, B, A> Drop for LruHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        unsafe {
            let mut ptr = self.lru.get();

            while let Some(node) = ptr.as_mut() {
                let next = node.as_ref().next;

                ptr.drop_in_place();

                let layout = Layout::new::<Node<Entry<T>>>();
                self.alloc.dealloc(ptr as *mut u8, layout);

                ptr = next;
            }

            self.chain.pre_drop(&self.alloc);
        }
    }
}

impl<T, B, A> LruHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    /// Returns a reference to the element which equals to `element` if any, otherwise inserts
    /// `element` into `self` and returns it.
    ///
    /// The return value is `(ref_T, is_new)` , where `ref_T` is a reference to the element
    /// stored in `self` wrapped in the lock and `is_new` is inserted newly or not.
    ///
    /// # Safety
    ///
    /// The return value owns a lock.
    /// The caller should not call another methods of `self` before dropping `ref_T` to escape
    /// dead lock.
    pub unsafe fn get_or_insert(&self, element: T) -> (Mutex8Guard<T>, bool)
    where
        T: Hash + Eq,
    {
        let (lock, bucket) = self.chain.bucket(&element);

        let (node, is_new) = match bucket.get(&element) {
            None => {
                let ptr = self.alloc_node(element);
                let node = &mut *ptr;
                bucket.push(node);
                self.push_back(node);
                (node, true)
            }
            Some(ptr) => {
                let node = &mut *ptr;
                self.move_back(node);
                (node, false)
            }
        };

        let element = &node.as_ref().element;
        (Mutex8Guard::new(lock, element), is_new)
    }

    /// Returns a reference to the element which equals to `element` if any.
    ///
    /// # Safety
    ///
    /// The returned value is wrapped by the lock.
    /// The caller should not call another methods of `self` before dropping it to escape
    /// dead lock.
    pub unsafe fn get<U>(&self, value: &U) -> Option<Mutex8Guard<T>>
    where
        T: Borrow<U>,
        U: Hash + Eq,
    {
        let (lock, bucket) = self.chain.bucket(&value);

        bucket.get(&value).map(|p_node| {
            let node = &mut *p_node;
            self.move_back(node);

            let element = &node.as_ref().element;

            Mutex8Guard::new(lock, element)
        })
    }

    /// Returns true if `self` contains element which equals to `value` , or false.
    pub fn contains<U>(&self, value: &U) -> bool
    where
        T: Borrow<U>,
        U: Hash + Eq,
    {
        let (_lock, bucket) = self.chain.bucket(&value);
        bucket
            .get(&value)
            .map(|p_node| unsafe {
                let node = &mut *p_node;
                self.move_back(node);
            })
            .is_some()
    }

    /// Does nothing and returns false if empty, otherwise, removes the LRU element and returns true.
    pub fn pop_lru(&self) -> bool
    where
        T: Hash,
    {
        match self.pop_from_order_list() {
            None => false,
            Some(lru) => {
                self.remove_from_hash_set(lru);

                let ptr = lru as *mut Node<Entry<T>>;
                unsafe { ptr.drop_in_place() };
                let layout = Layout::new::<Node<Entry<T>>>();
                unsafe { self.alloc.dealloc(ptr as *mut u8, layout) };

                true
            }
        }
    }

    /// Returns an iterator.
    ///
    /// # Safety
    ///
    /// The returned value owns lock of `self` .
    /// All other methods will cause a dead lock while the returned value is.
    pub unsafe fn iter(&mut self) -> Iter<T> {
        let _lock = self
            .order_mutex
            .lock(Self::LRU_LOCK_BIT + Self::MRU_LOCK_BIT);

        let entry = self.lru.get().as_ref().map(|n| n.as_ref());

        Iter { _lock, entry }
    }

    const LRU_LOCK_BIT: u8 = 0x01;
    const MRU_LOCK_BIT: u8 = 0x02;

    /// Allocates and initializes a new node.
    fn alloc_node(&self, element: T) -> *mut Node<Entry<T>> {
        let layout = Layout::new::<Node<Entry<T>>>();
        let ptr = unsafe { self.alloc.alloc(layout) as *mut Node<Entry<T>> };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        let entry = Entry::from(element);
        let node = Node::from(entry);
        unsafe { ptr.write(node) };

        ptr
    }

    /// Makes a new node least recently used element.
    fn push_back(&self, node: &mut Node<Entry<T>>) {
        debug_assert!(node.as_ref().prev.is_null());
        debug_assert!(node.as_ref().next.is_null());

        // Append node to the next of self.mru when self.mru is not null.
        let mut append = || {
            let prev_mru = unsafe { &mut *self.mru.get() };
            prev_mru.as_mut().next = node;

            node.as_mut().prev = prev_mru;
            self.mru.set(node);
        };

        let lock = self.order_mutex.lock(Self::MRU_LOCK_BIT);

        if self.mru.get().is_null() {
            // This is the first element.
            drop(lock);
            let _lock = self
                .order_mutex
                .lock(Self::LRU_LOCK_BIT + Self::MRU_LOCK_BIT);

            // Make sure again that no other element is.
            if self.mru.get().is_null() {
                self.mru.set(node);
                self.lru.set(node);
            } else {
                // Another element is inserted while acquiring the lock.
                append();
            }
        } else {
            // This is not the first element.
            append();
        }
    }

    /// Makes a node LRU.
    fn move_back(&self, node: &mut Node<Entry<T>>) {
        let _lock = self
            .order_mutex
            .lock(Self::LRU_LOCK_BIT + Self::MRU_LOCK_BIT);

        // Pop node from the order list.
        {
            // Fix the prev link of the next node.
            match unsafe { node.as_ref().next.as_mut() } {
                // Do nothing if node is already the LRU.
                None => return,
                // Fix the link.
                Some(next) => next.as_mut().prev = node.as_ref().prev,
            }

            // Fix the next link of the previous node.
            if let Some(prev) = unsafe { node.as_ref().prev.as_mut() } {
                // node is not the LRU.
                prev.as_mut().next = node.as_ref().next;
            } else {
                // node is LRU currently.
                self.lru.set(node.as_ref().next);
            }
        }

        // Append node to the end of the list.
        {
            let prev_mru = unsafe { &mut *self.mru.get() };

            node.as_mut().next = null_mut();
            node.as_mut().prev = prev_mru;
            prev_mru.as_mut().next = node;
            self.mru.set(node);
        }
    }

    /// Removes the node from the hash set.
    fn remove_from_hash_set(&self, node: &Node<Entry<T>>)
    where
        T: Hash,
    {
        let element = &node.as_ref().element;
        let (_lock, bucket) = self.chain.bucket(&element);
        unsafe { bucket.remove(node) };
    }

    /// Removes the LRU element from the order list if any.
    fn pop_from_order_list(&self) -> Option<&mut Node<Entry<T>>> {
        // Pop the last element from the order list.
        // Both locks for lru and mru are required.
        let pop_last_one = || -> bool {
            if self.lru.get() != self.mru.get() {
                // Do nothing if 2 or more than 2 elements are.
                false
            } else {
                self.lru.set(null_mut());
                self.mru.set(null_mut());
                true
            }
        };

        // Pop the LRU element when 2 or more than 2 elements are.
        // Lock for lru is required.
        let pop_lru = |lru: &Node<Entry<T>>| -> bool {
            match unsafe { lru.as_ref().next.as_mut() } {
                None => false, // Only one element is.
                Some(next) => {
                    next.as_mut().prev = null_mut();
                    self.lru.set(next);
                    true
                }
            }
        };

        loop {
            // Assume 2 or more than 2 elements are.
            {
                let _lock = self.order_mutex.lock(Self::LRU_LOCK_BIT);
                match unsafe { self.lru.get().as_mut() } {
                    None => return None, // No element is.
                    Some(lru) => {
                        if pop_lru(lru) {
                            return Some(lru);
                        }
                    }
                }
            }

            // Assume only one element is.
            {
                let _lock = self
                    .order_mutex
                    .lock(Self::LRU_LOCK_BIT + Self::MRU_LOCK_BIT);
                match unsafe { self.lru.get().as_mut() } {
                    None => return None, // No element is.
                    Some(lru) => {
                        if pop_last_one() {
                            return Some(lru);
                        }
                    }
                }
            }
        }
    }
}

/// Iterator for LruHashSet.
///
/// # Wargnings
///
/// This struct owns global lock of the `LruHashSet` .
/// All methods of the `LruHashSet` will cause dead lock while this struct is.
pub struct Iter<'a, T> {
    _lock: Lock8<'a>,
    entry: Option<&'a Entry<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.entry.map(|entry| {
            let next_node = unsafe { entry.next.as_ref() };
            let next_entry = next_node.map(|node| node.as_ref());
            self.entry = next_entry;

            &entry.element
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_alloc::{TestAlloc, TestBox};
    use std::collections::hash_map::RandomState;

    fn construct<T>(bucket_count: usize) -> LruHashSet<T, RandomState, TestAlloc> {
        LruHashSet::new(bucket_count, RandomState::new(), TestAlloc::default())
    }

    #[test]
    fn constructor() {
        let _lru = construct::<i32>(100);
        let _lru = construct::<TestBox<i32>>(100);
    }

    #[test]
    fn get_or_insert_int() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            let (j, b) = unsafe { lru.get_or_insert(i) };
            assert_eq!(i, *j);
            assert_eq!(true, b);
        }

        // Insert elements again.
        for i in 0..100 {
            let (j, b) = unsafe { lru.get_or_insert(i) };
            assert_eq!(i, *j);
            assert_eq!(false, b);
        }
    }

    #[test]
    fn get_or_insert_box() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            let (j, b) = unsafe { lru.get_or_insert(TestBox::from(i)) };
            assert_eq!(i, **j);
            assert_eq!(true, b);
        }

        // Insert elements again.
        for i in 0..100 {
            let (j, b) = unsafe { lru.get_or_insert(TestBox::from(i)) };
            assert_eq!(i, **j);
            assert_eq!(false, b);
        }
    }

    #[test]
    fn get_int() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            unsafe { lru.get_or_insert(i) };
        }

        // Get elements in lru.
        for i in 0..100 {
            let j = unsafe { lru.get(&i).unwrap() };
            assert_eq!(i, *j);
        }

        // Try to get elements not in lru.
        for i in -100..0 {
            assert!(unsafe { lru.get(&i).is_none() });
        }
    }

    #[test]
    fn get_box() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            unsafe { lru.get_or_insert(TestBox::from(i)) };
        }

        // Get elements in lru.
        for i in 0..100 {
            let j = unsafe { lru.get(&i).unwrap() };
            assert_eq!(i, **j);
        }

        // Try to get elements not in lru.
        for i in -100..0 {
            assert!(unsafe { lru.get(&i).is_none() });
        }
    }

    #[test]
    fn contains_int() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            unsafe { lru.get_or_insert(i) };
        }

        // Get elements in lru.
        for i in 0..100 {
            assert_eq!(true, lru.contains(&i));
        }

        // Try to get elements not in lru.
        for i in -100..0 {
            assert_eq!(false, lru.contains(&i));
        }
    }

    #[test]
    fn contains_box() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            unsafe { lru.get_or_insert(TestBox::from(i)) };
        }

        // Get elements in lru.
        for i in 0..100 {
            assert_eq!(true, lru.contains(&i));
        }

        // Try to get elements not in lru.
        for i in -100..0 {
            assert_eq!(false, lru.contains(&i));
        }
    }

    #[test]
    fn pop_int() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            for j in 0..i {
                unsafe { lru.get_or_insert(j) };
            }
            for _ in 0..i {
                assert_eq!(true, lru.pop_lru());
            }
            for _ in 0..10 {
                assert_eq!(false, lru.pop_lru());
            }
        }
    }

    #[test]
    fn pop_box() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            for j in 0..i {
                unsafe { lru.get_or_insert(TestBox::from(j)) };
            }
            for _ in 0..i {
                assert_eq!(true, lru.pop_lru());
            }
            for _ in 0..10 {
                assert_eq!(false, lru.pop_lru());
            }
        }
    }

    #[test]
    fn iter() {
        let mut lru = construct(10);

        unsafe {
            // Insert elements.
            for i in 0..100 {
                lru.get_or_insert(i);
            }

            // Check the order.
            let mut iter = lru.iter();
            (0..100).for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert!(iter.next().is_none());
            drop(iter);

            // pop '0' and check the order again.
            lru.pop_lru();
            let mut iter = lru.iter();
            (1..100).for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert!(iter.next().is_none());
            drop(iter);

            // Make '50' MRU by 'contains()'.
            assert_eq!(true, lru.contains(&50));
            let mut iter = lru.iter();
            (1..50)
                .chain(51..100)
                .chain(50..51)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Nothing is changed if 'contains()' returns false.
            assert_eq!(false, lru.contains(&100));
            let mut iter = lru.iter();
            (1..50)
                .chain(51..100)
                .chain(50..51)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Make '51' MRU by 'get()'.
            assert!(lru.get(&51).is_some());
            let mut iter = lru.iter();
            (1..50)
                .chain(52..100)
                .chain(50..52)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Nothing is changed if 'get()' returns None,
            assert!(lru.get(&100).is_none());
            let mut iter = lru.iter();
            (1..50)
                .chain(52..100)
                .chain(50..52)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Make '52' MRU by 'get_or_insert()'.
            lru.get_or_insert(52);
            let mut iter = lru.iter();
            (1..50)
                .chain(53..100)
                .chain(50..53)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Inert '0' by 'get_or_insert()'.
            lru.get_or_insert(0);
            let mut iter = lru.iter();
            (1..50)
                .chain(53..100)
                .chain(50..53)
                .chain(0..1)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Make the LRU element MRU.
            assert_eq!(true, lru.contains(&1));
            let mut iter = lru.iter();
            (2..50)
                .chain(53..100)
                .chain(50..53)
                .chain(0..2)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);

            // Nothing is changed to get MRU.
            assert!(lru.get(&1).is_some());
            let mut iter = lru.iter();
            (2..50)
                .chain(53..100)
                .chain(50..53)
                .chain(0..2)
                .for_each(|i| assert_eq!(&i, iter.next().unwrap()));
            assert_eq!(true, iter.next().is_none());
            drop(iter);
        }
    }
}
