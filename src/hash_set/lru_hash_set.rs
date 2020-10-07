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
use crate::{Mutex8, Mutex8Guard};
use core::alloc::{GlobalAlloc, Layout};
use core::cell::Cell;
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::ptr::null_mut;
use std::alloc::handle_alloc_error;

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
    /// The caller should not call another methods of `self` before dropping `ref_T` to escape
    /// dead lock.
    pub fn get_or_insert(&self, element: T) -> (Mutex8Guard<T>, bool)
    where
        T: Hash + Eq,
    {
        let (lock, bucket) = self.chain.bucket(&element);

        let (node, is_new) = match bucket.get(&element) {
            None => {
                let ptr = self.alloc_node(element);
                let node = unsafe { &mut *ptr };
                bucket.push(node);
                self.push_back(node);
                (node, true)
            }
            Some(ptr) => {
                let node = unsafe { &mut *ptr };
                self.move_back(node);
                (node, false)
            }
        };

        let element = &node.as_ref().element;

        unsafe { (Mutex8Guard::new(lock, element), is_new) }
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
            let (j, b) = lru.get_or_insert(i);
            assert_eq!(i, *j);
            assert_eq!(true, b);
        }

        // Insert elements again.
        for i in 0..100 {
            let (j, b) = lru.get_or_insert(i);
            assert_eq!(i, *j);
            assert_eq!(false, b);
        }
    }

    #[test]
    fn get_or_insert_box() {
        let lru = construct(10);

        // Insert elements.
        for i in 0..100 {
            let (j, b) = lru.get_or_insert(TestBox::from(i));
            assert_eq!(i, **j);
            assert_eq!(true, b);
        }

        // Insert elements again.
        for i in 0..100 {
            let (j, b) = lru.get_or_insert(TestBox::from(i));
            assert_eq!(i, **j);
            assert_eq!(false, b);
        }
    }
}
