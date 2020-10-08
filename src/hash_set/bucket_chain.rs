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

use super::bucket::Bucket;
use crate::Mutex8;
use core::alloc::{GlobalAlloc, Layout};
use core::hash::BuildHasher;
use std::alloc::handle_alloc_error;

/// Buckets for a "chaining hash set".
pub struct BucketChain<T, B>
where
    B: BuildHasher,
{
    buckets_ptr: *mut Bucket<T>,
    buckets_len: usize,

    mutexes_ptr: *const Mutex8,

    hasher_builder: B,
}

impl<T, B> BucketChain<T, B>
where
    B: BuildHasher,
{
    /// Creates a new instance.
    pub fn new<A>(chain_len: usize, hasher_builder: B, alloc: &A) -> Self
    where
        A: GlobalAlloc,
    {
        let (layout, offset) = layout::<T>(chain_len);

        let ptr = unsafe { alloc.alloc(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        let buckets_ptr = ptr as *mut Bucket<T>;
        unsafe {
            for i in 0..chain_len {
                buckets_ptr.add(i).write(Bucket::default());
            }
        };

        let mutexes_ptr = unsafe { ptr.add(offset) as *mut Mutex8 };
        unsafe {
            for i in 0..mutex8_count(chain_len) {
                mutexes_ptr.add(i).write(Mutex8::new());
            }
        };

        Self {
            buckets_ptr,
            buckets_len: chain_len,
            mutexes_ptr,
            hasher_builder,
        }
    }

    /// Deallocate `buckets_ptr` and `mutex_ptr` .
    ///
    /// This method must be called before dropped.
    ///
    /// # Safety
    ///
    /// After this method is called, no method can be called except for `drop` .
    ///
    pub unsafe fn pre_drop<A>(&mut self, alloc: &A)
    where
        A: GlobalAlloc,
    {
        let (layout, _) = layout::<T>(self.buckets_len);
        let ptr = self.buckets_ptr as *mut u8;
        alloc.dealloc(ptr, layout);

        self.buckets_ptr = core::ptr::null_mut();
        self.mutexes_ptr = core::ptr::null();
    }
}

impl<T, B> Drop for BucketChain<T, B>
where
    B: BuildHasher,
{
    fn drop(&mut self) {
        assert!(self.buckets_ptr.is_null());
        assert!(self.mutexes_ptr.is_null());
    }
}

/// Returns necessary and sufficient count of `Mutex8` to protect `chain_len` count
/// objects.
fn mutex8_count(chain_len: usize) -> usize {
    (chain_len + Mutex8::len() - 1) / Mutex8::len()
}

/// Calculates `Layout` to allocate both `[Bucket<T>; chain_len]` and `[Mutex8]` to protect the each bucket
/// at once.
///
/// Returns `(layout, offset)`, where `layout` is the calculated `Layout` and `offset` is the relative location
/// (in bytes,) to start at `[Mutex8]` .
/// (`[Bucket]` starts at offset 0.)
fn layout<T>(chain_len: usize) -> (Layout, usize) {
    let buckets_layout = Layout::array::<Bucket<T>>(chain_len).unwrap();
    let mutexes_layout = Layout::array::<Mutex8>(mutex8_count(chain_len)).unwrap();

    buckets_layout.extend(mutexes_layout).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_alloc::{TestAlloc, TestBox};
    use std::collections::hash_map::RandomState;

    #[test]
    fn constructor() {
        {
            let alloc = TestAlloc::default();
            let mut chain = BucketChain::<i32, RandomState>::new(100, RandomState::new(), &alloc);
            unsafe { chain.pre_drop(&alloc) };
        }

        {
            let alloc = TestAlloc::default();
            let mut chain =
                BucketChain::<TestBox<i32>, RandomState>::new(100, RandomState::new(), &alloc);
            unsafe { chain.pre_drop(&alloc) };
        }
    }
}
