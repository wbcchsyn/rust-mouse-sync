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

use super::node::Node;
use core::ops::Deref;
use std::borrow::Borrow;

/// Bucket for "chaining hash set".
///
/// This struct forms forward linked list by itself.
pub struct Bucket<T>(*mut Node<T>);

impl<T> Default for Bucket<T> {
    fn default() -> Self {
        Self(core::ptr::null_mut())
    }
}

impl<T> Iterator for Bucket<T> {
    type Item = *mut Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.0.as_mut().map(|r| {
                self.0 = r.next();
                r as *mut Node<T>
            })
        }
    }
}

impl<T> Bucket<T> {
    /// Appends `node` to `self` .
    ///
    /// This method should compute in O(1) time.
    ///
    /// # Warnings
    ///
    /// This method will not check duplication at all.
    pub fn push(&mut self, node: &mut Node<T>) {
        node.set_next(self.0);
        self.0 = node
    }

    /// Returns true if `self` has an element which equals to `value` , or false.
    pub fn contains<U: ?Sized, V: ?Sized>(&self, value: &V) -> bool
    where
        T: Deref<Target = U>,
        U: Borrow<V>,
        V: Eq,
    {
        let predicate = |item: *mut Node<T>| unsafe {
            let t: &T = (&*item).as_ref();
            let u: &U = &*t;
            let v: &V = u.borrow();
            value == v
        };

        self.iter().any(predicate)
    }

    /// Returns a pointer to the element which equals to `value` if any.
    pub fn get<U: ?Sized, V: ?Sized>(&mut self, value: &V) -> Option<*mut Node<T>>
    where
        T: Deref<Target = U>,
        U: Borrow<V>,
        V: Eq,
    {
        let predicate = |item: &*mut Node<T>| unsafe {
            let t: &T = (&**item).as_ref();
            let u: &U = &*t;
            let v: &V = u.borrow();

            value == v
        };

        self.iter().find(predicate)
    }

    /// Removes `node` from `self` .
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `self` does not own `node` .
    pub unsafe fn remove(&mut self, node: &Node<T>) {
        // If node is the first element, remove it and return.
        if (self.0 as *const Node<T>) == node {
            self.0 = node.next();
            return;
        }

        // This dereference is OK because self must has node.
        let mut prev = &mut *self.0;
        let mut cur = prev.next();
        loop {
            if (cur as *const Node<T>) == node {
                prev.set_next(node.next());
                return;
            } else {
                prev = &mut *cur;
                cur = (&*cur).next();
            }
        }
    }

    fn iter(&self) -> Self {
        Self(self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_alloc::TestBox;

    #[test]
    fn constructor() {
        let _bucket = Bucket::<i32>::default();
        let _bucket = Bucket::<TestBox<i32>>::default();
    }

    #[test]
    fn push_int() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<i32>> = (0..10).map(Node::from).collect();

        for i in 0..nodes.len() {
            assert_eq!(i, bucket.iter().count());
            bucket.push(&mut nodes[i]);
        }
    }

    #[test]
    fn push_box() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<TestBox<i32>>> =
            (0..10).map(|i| Node::from(TestBox::from(i))).collect();

        for i in 0..nodes.len() {
            assert_eq!(i, bucket.iter().count());
            bucket.push(&mut nodes[i]);
        }
    }

    #[test]
    fn contains_int() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<Box<i32>>> = (0..3).map(Box::new).map(Node::from).collect();

        assert_eq!(false, bucket.contains(&0));
        assert_eq!(false, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[0]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(false, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[1]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(true, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[2]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(true, bucket.contains(&1));
        assert_eq!(true, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));
    }

    #[test]
    fn contains_box() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<TestBox<i32>>> =
            (0..3).map(|i| Node::from(TestBox::from(i))).collect();

        assert_eq!(false, bucket.contains(&0));
        assert_eq!(false, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[0]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(false, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[1]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(true, bucket.contains(&1));
        assert_eq!(false, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));

        bucket.push(&mut nodes[2]);
        assert_eq!(true, bucket.contains(&0));
        assert_eq!(true, bucket.contains(&1));
        assert_eq!(true, bucket.contains(&2));
        assert_eq!(false, bucket.contains(&3));
    }

    #[test]
    fn get_int() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<Box<i32>>> = (0..3).map(Box::new).map(Node::from).collect();

        unsafe {
            assert!(bucket.get(&0).is_none());
            assert!(bucket.get(&1).is_none());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[0]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert!(bucket.get(&1).is_none());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[1]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert_eq!(nodes.as_ptr().add(1), bucket.get(&1).unwrap());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[2]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert_eq!(nodes.as_ptr().add(1), bucket.get(&1).unwrap());
            assert_eq!(nodes.as_ptr().add(2), bucket.get(&2).unwrap());
            assert!(bucket.get(&3).is_none());
        }
    }

    #[test]
    fn get_box() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<TestBox<i32>>> =
            (0..3).map(|i| Node::from(TestBox::from(i))).collect();

        unsafe {
            assert!(bucket.get(&0).is_none());
            assert!(bucket.get(&1).is_none());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[0]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert!(bucket.get(&1).is_none());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[1]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert_eq!(nodes.as_ptr().add(1), bucket.get(&1).unwrap());
            assert!(bucket.get(&2).is_none());
            assert!(bucket.get(&3).is_none());

            bucket.push(&mut nodes[2]);
            assert_eq!(nodes.as_ptr().add(0), bucket.get(&0).unwrap());
            assert_eq!(nodes.as_ptr().add(1), bucket.get(&1).unwrap());
            assert_eq!(nodes.as_ptr().add(2), bucket.get(&2).unwrap());
            assert!(bucket.get(&3).is_none());
        }
    }

    #[test]
    fn remove_int() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<Box<i32>>> = (0..5).map(Box::new).map(Node::from).collect();

        for n in nodes.iter_mut() {
            bucket.push(n);
        }

        unsafe {
            assert_eq!(5, bucket.iter().count());

            assert_eq!(true, bucket.contains(&0));
            bucket.remove(&nodes[0]);
            assert_eq!(false, bucket.contains(&0));

            assert_eq!(4, bucket.iter().count());

            assert_eq!(true, bucket.contains(&4));
            bucket.remove(&nodes[4]);
            assert_eq!(false, bucket.contains(&4));

            assert_eq!(3, bucket.iter().count());

            assert_eq!(true, bucket.contains(&2));
            bucket.remove(&nodes[2]);
            assert_eq!(false, bucket.contains(&2));

            assert_eq!(2, bucket.iter().count());

            assert_eq!(true, bucket.contains(&1));
            bucket.remove(&nodes[1]);
            assert_eq!(false, bucket.contains(&1));

            assert_eq!(1, bucket.iter().count());

            assert_eq!(true, bucket.contains(&3));
            bucket.remove(&nodes[3]);
            assert_eq!(false, bucket.contains(&3));
        }
    }

    #[test]
    fn remove_box() {
        let mut bucket = Bucket::default();
        let mut nodes: Vec<Node<TestBox<i32>>> =
            (0..5).map(|i| Node::from(TestBox::from(i))).collect();

        for n in nodes.iter_mut() {
            bucket.push(n);
        }

        unsafe {
            assert_eq!(5, bucket.iter().count());

            assert_eq!(true, bucket.contains(&0));
            bucket.remove(&nodes[0]);
            assert_eq!(false, bucket.contains(&0));

            assert_eq!(4, bucket.iter().count());

            assert_eq!(true, bucket.contains(&4));
            bucket.remove(&nodes[4]);
            assert_eq!(false, bucket.contains(&4));

            assert_eq!(3, bucket.iter().count());

            assert_eq!(true, bucket.contains(&2));
            bucket.remove(&nodes[2]);
            assert_eq!(false, bucket.contains(&2));

            assert_eq!(2, bucket.iter().count());

            assert_eq!(true, bucket.contains(&1));
            bucket.remove(&nodes[1]);
            assert_eq!(false, bucket.contains(&1));

            assert_eq!(1, bucket.iter().count());

            assert_eq!(true, bucket.contains(&3));
            bucket.remove(&nodes[3]);
            assert_eq!(false, bucket.contains(&3));
        }
    }
}
