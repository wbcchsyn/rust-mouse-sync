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

use core::result::Result;
use core::sync::atomic::{AtomicU8, Ordering};
pub use std::sync::{TryLockError, TryLockResult};

/// `Mutex8` is constituded of 8 mutexes.
/// This does not adopt poison strategy.
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

    #[cfg(test)]
    /// Returns a bit indicating currently locked state.
    fn state(&self) -> u8 {
        self.mutexes.load(Ordering::SeqCst)
    }

    /// Tries to lock `new_locks` and returns it if succeeded; otherwise, i.e.
    /// in case of lock competition, returns an error.
    /// (Because `Mutex8` does not adopt poison strategy, this method won't fail
    /// unless lock competition.)
    ///
    /// This method will not block.
    pub fn try_lock(&self, new_locks: u8) -> TryLockResult<Lock8> {
        let mut expected = 0;
        loop {
            match unsafe { Lock8::new(self, expected, new_locks) } {
                Ok(g) => return Ok(g),
                Err(current) => {
                    if (current & new_locks) == 0 {
                        expected = current;
                        continue;
                    } else {
                        return Err(TryLockError::WouldBlock);
                    }
                }
            }
        }
    }

    /// Acquires `new_locks` and returns them.
    ///
    /// If any of `new_locks` is locked, block till it is released.
    pub fn lock(&self, new_locks: u8) -> Lock8 {
        let mut expected = 0;
        loop {
            match unsafe { Lock8::new(self, expected, new_locks) } {
                Ok(g) => return g,
                Err(current) => {
                    if (current & new_locks) == 0 {
                        expected = current;
                        continue;
                    } else {
                        std::thread::yield_now();
                    }
                }
            }
        }
    }
}

/// `Lock8` is a RAII Lock object of Mutex8.
pub struct Lock8<'a> {
    mutex8: &'a Mutex8,
    holdings_: u8,
}

impl<'a> Lock8<'a> {
    /// Tries to create a new instance holding `new_locks`.
    ///
    /// `expected` is assumption of bits currently locked.
    /// If the assumption is right, returns `Self` wrapped with Ok, or current lock state wrapped with Err.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if any bit is included both in `expected` and `new_locks` .
    unsafe fn new(mutex8: &'a Mutex8, expected: u8, new_locks: u8) -> Result<Self, u8> {
        debug_assert_eq!(0, expected & new_locks);

        let current =
            mutex8
                .mutexes
                .compare_and_swap(expected, expected + new_locks, Ordering::Acquire);
        if current == expected {
            Ok(Self {
                mutex8,
                holdings_: new_locks,
            })
        } else {
            Err(current)
        }
    }
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

    #[test]
    fn lock_guard8_constructor() {
        let mutexes = Mutex8::new();

        for i in 0..=u8::MAX {
            assert_eq!(0, mutexes.state());
            let guard = unsafe { Lock8::new(&mutexes, 0, i).unwrap() };
            assert_eq!(i, guard.holdings());
            assert_eq!(i, mutexes.state());
        }
    }

    #[test]
    fn try_lock() {
        let mutex8 = Mutex8::new();

        for i in 0..=u8::MAX {
            assert_eq!(0, mutex8.state());
            let guard = mutex8.try_lock(i).unwrap();
            assert_eq!(i, guard.holdings());

            for j in 0..=u8::MAX {
                let r = mutex8.try_lock(j);

                if (i & j) == 0 {
                    let guard = r.unwrap();
                    assert_eq!(j, guard.holdings());
                    assert_eq!(i + j, mutex8.state());
                } else {
                    assert!(r.is_err());
                    assert_eq!(i, guard.holdings());
                }
            }
        }
    }

    #[test]
    fn lock() {
        let mutex8 = Mutex8::new();

        for i in 0..=u8::MAX {
            assert_eq!(0, mutex8.state());
            let guard = mutex8.lock(i);
            assert_eq!(i, guard.holdings());
            assert_eq!(i, mutex8.state());
        }
    }
}
