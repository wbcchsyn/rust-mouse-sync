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

//! `mutex` provides struct `Mutex8`

use core::sync::atomic::{AtomicU8, Ordering};

/// `Mutex8` is constituded of 8 mutexes.
pub struct Mutex8 {
    mutexes: AtomicU8,
}

impl Mutex8 {
    /// Creates a new instance without any lock.
    pub const fn new() -> Self {
        Self {
            mutexes: AtomicU8::new(0),
        }
    }
}

/// `Lock8` is a RAII Lock object of Mutex8.
pub struct Lock8<'a> {
    mutex8: &'a Mutex8,
    holdings_: u8,
}

impl Lock8<'_> {
    /// Returns a bits representing holding locks.
    pub fn holdings(&self) -> u8 {
        self.holdings_
    }

    /// Releases some of the holding lock(s).
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `locks` includes bit(s) not holding.
    pub unsafe fn release(&mut self, locks: u8) {
        debug_assert_eq!(locks, self.holdings() & locks);

        let _prev = self.mutex8.mutexes.fetch_sub(locks, Ordering::Release);
        debug_assert_eq!(locks, _prev & locks);

        self.holdings_ -= locks;
    }
}

impl Drop for Lock8<'_> {
    fn drop(&mut self) {
        if self.holdings() != 0 {
            unsafe { self.release(self.holdings()) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructor() {
        let _mutexes = Mutex8::new();
    }
}
