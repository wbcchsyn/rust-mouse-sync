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
use core::hash::BuildHasher;

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

/// Returns necessary and sufficient count of `Mutex8` to protect `chain_len` count
/// objects.
fn mutex8_count(chain_len: usize) -> usize {
    (chain_len + Mutex8::len() - 1) / Mutex8::len()
}
