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

//! `multi_hash_set` provides implementations of thread-safe hash set

use super::bucket_chain::BucketChain;
use super::node::Node;
use crate::Mutex8Guard;
use core::alloc::{GlobalAlloc, Layout};
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::handle_alloc_error;

/// Entry of `MultiHashSet` .
///
/// The node of `MultiHashSet` will be `Node<Entry<T>>` .
/// `MultiHashSet` enables to store the same value many times and
/// this has the counter of the element.
struct Entry<T> {
    element: T,
    count: AtomicUsize,
}

impl<T> From<T> for Entry<T> {
    fn from(element: T) -> Self {
        Self {
            element,
            count: AtomicUsize::new(1),
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

/// Implementation of thread-safe hash set, which enables to store the same value
/// many times and removes elements fully to be removed as many times to be inserted.
pub struct MultiHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    chain: BucketChain<Entry<T>, B>,
    alloc: A,
}

impl<T, B, A> MultiHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    /// Creates a new instance.
    ///
    /// `MultiHashSet` is a chaining hash set and `bucket_count` is the length of the bucket chain.
    ///
    /// It has the following affects to make `bucket_count` large.
    ///
    /// - Reducing hash conflict properbility. (This is characteristics of chaining hash set.)
    /// - Reducing lock wait time.
    ///   (Because `MultiHashSet` locks each bucket. More bucket will reduce hash conflict and lock competition.)
    /// - Increasing memory usage for bucket_chain.
    pub fn new(bucket_count: usize, hasher_builder: B, alloc: A) -> Self {
        Self {
            chain: BucketChain::new(bucket_count, hasher_builder, &alloc),
            alloc,
        }
    }
}

impl<T, B, A> Drop for MultiHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        unsafe {
            for (_, bucket) in self.chain.iter() {
                for node in bucket.iter() {
                    node.drop_in_place();
                    let layout = Layout::new::<Node<Entry<T>>>();
                    self.alloc.dealloc(node as *mut u8, layout);
                }
            }

            self.chain.pre_drop(&self.alloc);
        }
    }
}

impl<T, B, A> MultiHashSet<T, B, A>
where
    B: BuildHasher,
    A: GlobalAlloc,
{
    /// Tries to find element to equal to `element` and increments the counter if any, otherwise,
    /// adds `element` to `self` .
    ///
    /// This method returns `(referecne, count)` , where `reference` is a reference to the element
    /// wrapped in the lock, and `count` is how many times the element was added before this method
    /// is called. (i.e. if `element` is added newly, `count` will be 0.)
    ///
    /// Don't call method of `self` before dropping the return value to escape a dead lock.
    pub fn get_or_insert(&self, element: T) -> (Mutex8Guard<T>, usize)
    where
        T: Hash + Eq,
    {
        let (lock, bucket) = self.chain.bucket(&element);
        let (node, count) = match bucket.get(&element) {
            None => {
                let node = unsafe { &mut *self.alloc_node(element) };
                bucket.push(node);
                (node, 0)
            }
            Some(p_node) => {
                let node = unsafe { &mut *p_node };
                let entry = node.as_ref();
                let count = entry.count.fetch_add(1, Ordering::Acquire);
                (node, count)
            }
        };

        let element = &node.as_ref().element as *const T;
        (unsafe { Mutex8Guard::new(lock, &*element) }, count)
    }

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_alloc::{TestAlloc, TestBox};
    use std::collections::hash_map::RandomState;

    fn construct<T>(bucket_count: usize) -> MultiHashSet<T, RandomState, TestAlloc> {
        MultiHashSet::new(bucket_count, RandomState::new(), TestAlloc::default())
    }

    #[test]
    fn constructor() {
        let _multi = construct::<i32>(100);
        let _multi = construct::<TestBox<i32>>(100);
    }

    #[test]
    fn get_or_insert_int() {
        let multi = construct(10);

        for i in 0..10 {
            for j in 0..100 {
                let (r, c) = multi.get_or_insert(j);
                assert_eq!(j, *r);
                assert_eq!(i, c);
            }
        }
    }

    #[test]
    fn get_or_insert_box() {
        let multi = construct(10);

        for i in 0..10 {
            for j in 0..100 {
                let (r, c) = multi.get_or_insert(TestBox::from(j));
                assert_eq!(j, **r);
                assert_eq!(i, c);
            }
        }
    }
}
