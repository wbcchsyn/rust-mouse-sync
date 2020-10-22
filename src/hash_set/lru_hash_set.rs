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
use crate::Mutex8;
use core::alloc::GlobalAlloc;
use core::cell::Cell;
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::ptr::null_mut;

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
