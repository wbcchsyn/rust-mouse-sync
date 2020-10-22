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

use core::alloc::{GlobalAlloc, Layout};
use core::ops::Deref;
use std::alloc::{handle_alloc_error, System};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::sync::Mutex;

/// `TestAlloc` behaves like `std::alloc::System` except for the followings.
///
/// - `TestAlloc::dealloc(&self, ptr: *mut u8, layout: Layout)` checks relation among
/// `self` , `ptr` , and `layout` .
/// - `TestAlloc` checks all allocated memories have been deallocated on drop.
pub struct TestAlloc {
    alloc: System,
    allocatings: Mutex<HashMap<*mut u8, Layout>>,
}

impl Default for TestAlloc {
    fn default() -> Self {
        Self {
            alloc: System,
            allocatings: Mutex::default(),
        }
    }
}

impl Drop for TestAlloc {
    fn drop(&mut self) {
        let allocatings = self.allocatings.get_mut().unwrap();
        assert!(allocatings.is_empty());
    }
}

unsafe impl GlobalAlloc for TestAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = self.alloc.alloc(layout);
        if !ptr.is_null() {
            let mut allocatings = self.allocatings.lock().unwrap();
            assert!(allocatings.insert(ptr, layout).is_none());
        }

        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut allocatings = self.allocatings.lock().unwrap();
        let l = allocatings
            .remove(&ptr)
            .expect("Deallocating pointer which is not allocated.");
        if l != layout {
            panic!("Deallocating layout is not fit to the pointer.");
        }

        self.alloc.dealloc(ptr, layout);
    }
}

/// `TestBox` behaves like `std::boxed::Box` except for using `TestAlloc` .
pub struct TestBox<T> {
    ptr: *mut T,
    alloc: TestAlloc,
}

impl<T> From<T> for TestBox<T> {
    fn from(val: T) -> Self {
        let alloc = TestAlloc::default();

        let layout = Layout::new::<T>();
        let ptr = unsafe { alloc.alloc(layout) } as *mut T;
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        unsafe { ptr.write(val) };

        Self { ptr, alloc }
    }
}

impl<T> Drop for TestBox<T> {
    fn drop(&mut self) {
        unsafe {
            self.ptr.drop_in_place();
            let layout = Layout::new::<T>();
            self.alloc.dealloc(self.ptr as *mut u8, layout);
        }
    }
}

impl<T> Deref for TestBox<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

impl<T> Borrow<T> for TestBox<T> {
    fn borrow(&self) -> &T {
        unsafe { &*self.ptr }
    }
}
