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
use core::alloc::GlobalAlloc;
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::sync::atomic::AtomicUsize;

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
