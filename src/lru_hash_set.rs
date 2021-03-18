// Copyright 2021 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
//
// This is part of mouse-containers
//
//  mouse-containers is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  mouse-containers is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with mouse-containers.  If not, see <http://www.gnu.org/licenses/>.
//
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
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

//! Module `lru_hash_set` provides struct `LruHashSet` and the related things.

use core::alloc::GlobalAlloc;
use core::hash::{BuildHasher, Hash};
use core::ops::Deref;
use std::borrow::Borrow;

pub use crate::raw_lru_hash_set::Entry as RawEntry;
use crate::raw_lru_hash_set::RawLruHashSet;

/// `Entry` is the entry of [`LruHashSet`] .
///
/// This instance includes an RAII lock guard.
/// User can sure that no other thread drops nor modifies the element while the instance is.
///
/// User can access to the element via the `Deref` implementation.
///
/// # Warnings
///
/// Some entries shares the same mutex.
/// ([`LruHashSet`] adopts chain way to implement hash set, and entries in the same bucket shares
/// the same mutex.)
///
/// It may cause a dead lock to call methods of [`LruHashSet`] while the thread holds an instance
/// of `Entry` .
///
/// [`LruHashSet`]: struct.LruHashSet.html
pub struct Entry<'a, T>(RawEntry<'a, T>);

unsafe impl<T> Sync for Entry<'_, T> where T: Send {}

impl<T> Deref for Entry<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

/// `LruHashSet` is a thread-safe LRU hash set.
pub struct LruHashSet<T, A, S>
where
    A: GlobalAlloc,
{
    raw: RawLruHashSet<T, A, S>,
}

impl<T, A, S> LruHashSet<T, A, S>
where
    A: GlobalAlloc,
{
    /// Creates a new instance without initialization.
    ///
    /// The instance is not ready for use till method [`init`] is called.
    ///
    /// [`init`]: #method.init
    pub fn new(alloc: A, build_hasher: S) -> Self {
        Self {
            raw: RawLruHashSet::new(alloc, build_hasher),
        }
    }

    /// Initializes `self` and make `self` ready for use.
    ///
    /// # Panics
    ///
    /// Panics if `chain_len` equals to 0, or if `self` has already been initialized.
    pub fn init(&mut self, chain_len: usize) {
        self.raw.init(chain_len);
    }
}

impl<T, A, S> LruHashSet<T, A, S>
where
    A: GlobalAlloc,
    S: BuildHasher,
{
    /// Inserts `val` as the 'Most Recently Used (MRU)' element and returns `(None, new_entry)` if
    /// `val` is new to `self` (i.e. if `self` did not have such an element that equals to `val` .)
    ///
    /// Otherwise, i.e. if `self` had the element that equals to `val` , calls
    /// `op(holding_element, val)` and returns the result of `op` and the entry.
    ///
    /// Note that if `self` had `val` , this method will not make the entry the
    /// 'Most Recently Used (MRU)'.
    /// Call [`Entry.to_mru`] if necessary.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `op` changes the hash of the element in `self` .
    ///
    /// It may cause a dead lock to call this method while the thread owns an instance of
    /// [`Entry`] .
    ///
    /// [`Entry`]: struct.Entry.html
    /// [`Entry.to_mru`]: struct.Entry.html#method.to_mru
    pub unsafe fn insert_with<F, R>(&self, val: T, op: F) -> (Option<R>, RawEntry<T>)
    where
        T: Eq + Hash,
        F: FnOnce(&mut T, T) -> R,
    {
        let eq = |new_val: &T, old_val: &T| new_val == old_val;
        self.raw.insert_with(val, op, eq)
    }

    /// Finds an element that equals to `key` and returns the entry if any.
    ///
    /// Note that this method will not made the entry the 'Most Recently Used (MRU).'
    /// Call [`Entry.to_mru`] if necessary
    ///
    ///
    /// # Safety
    ///
    /// It may cause a dead lock to call this method while the thread owns an instance of
    /// [`Entry`] .
    ///
    /// [`Entry`]: struct.Entry.html
    /// [`Entry.to_mru`]: struct.Entry.html#method.to_mru
    pub unsafe fn get<K>(&self, key: &K) -> Option<RawEntry<T>>
    where
        T: Borrow<K>,
        K: Eq + Hash,
    {
        let eq = |k: &K, v: &T| -> bool { k == v.borrow() };
        self.raw.get(key, eq)
    }

    /// Removes the 'Least Recently Used (LRU)' element and returns true if any, or does nothing
    /// and returns true.
    ///
    /// # Safety
    ///
    /// It may cause a dead lock to call this method while the thread has an instance of
    /// [`Entry`] .
    ///
    /// [`Entry`]: struct.Entry.html
    pub unsafe fn expire(&self) -> bool
    where
        T: Hash,
    {
        self.raw.expire()
    }
}

#[cfg(test)]
mod lru_hash_set_tests {
    use gharial::{GAlloc, GBox};
    use std::collections::hash_map::RandomState;

    type LruHashSet = super::LruHashSet<GBox<usize>, GAlloc, RandomState>;

    fn op(a: &mut GBox<usize>, b: GBox<usize>) -> usize {
        assert_eq!(**a, *b);
        *b
    }

    #[test]
    fn new() {
        let alloc = GAlloc::default();
        let _hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
    }

    #[test]
    fn init() {
        let alloc = GAlloc::default();
        {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(1);
        }

        {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(100);
        }
    }

    #[test]
    fn insert_with() {
        let alloc = GAlloc::default();

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(1);

            for i in 0..10 {
                let (r, _) = hash_set.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(None, r);
            }
            for i in 0..10 {
                let (r, _) = hash_set.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(Some(i), r);
            }
        }

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(100);

            for i in 0..100 {
                let (r, _) = hash_set.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(None, r);
            }
            for i in 0..100 {
                let (r, _) = hash_set.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(Some(i), r);
            }
        }
    }

    #[test]
    fn get() {
        let alloc = GAlloc::default();

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(1);

            for i in 0..10 {
                for j in 0..10 {
                    let r = hash_set.get(&j);
                    if j < i {
                        assert_eq!(j, **r.unwrap());
                    } else {
                        assert_eq!(true, r.is_none());
                    }
                }
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }
        }

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(100);

            for i in 0..100 {
                for j in 0..100 {
                    let r = hash_set.get(&j);
                    if j < i {
                        assert_eq!(j, **r.unwrap());
                    } else {
                        assert_eq!(true, r.is_none());
                    }
                }
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }
        }
    }

    #[test]
    fn expire() {
        let alloc = GAlloc::default();

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(1);

            assert_eq!(false, hash_set.expire());

            for i in 0..10 {
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }

            for i in 0..10 {
                for j in 0..i {
                    assert_eq!(true, hash_set.get(&j).is_none());
                }
                for j in i..10 {
                    assert_eq!(true, hash_set.get(&j).is_some());
                }
                hash_set.expire();
            }

            assert_eq!(false, hash_set.expire());
            for i in 0..10 {
                assert_eq!(true, hash_set.get(&i).is_none());
            }
        }

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(100);

            assert_eq!(false, hash_set.expire());

            for i in 0..100 {
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }

            for i in 0..100 {
                for j in 0..i {
                    assert_eq!(true, hash_set.get(&j).is_none());
                }
                for j in i..100 {
                    assert_eq!(true, hash_set.get(&j).is_some());
                }
                hash_set.expire();
            }

            assert_eq!(false, hash_set.expire());
            for i in 0..100 {
                assert_eq!(true, hash_set.get(&i).is_none());
            }
        }
    }

    #[test]
    fn move_to_back() {
        let alloc = GAlloc::default();

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(1);

            assert_eq!(false, hash_set.expire());

            for i in 0..3 {
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }

            // [0, 1, 2] -> [0, 1, 2]
            {
                let e = hash_set.get(&2).unwrap();
                e.to_mru();
            }

            // [0, 1, 2] -> [1, 2, 0]
            {
                let e = hash_set.get(&0).unwrap();
                e.to_mru();
            }

            // [1, 2, 0] -> [1, 0, 2]
            {
                let e = hash_set.get(&2).unwrap();
                e.to_mru();
            }

            // [1, 0, 2] -> [0, 2]
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_some());
            assert_eq!(true, hash_set.get(&2).is_some());

            // [0, 2] -> [2]
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_none());
            assert_eq!(true, hash_set.get(&2).is_some());

            // [2] -> []
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_none());
            assert_eq!(true, hash_set.get(&2).is_none());
        }

        unsafe {
            let mut hash_set = LruHashSet::new(alloc.clone(), RandomState::new());
            hash_set.init(100);

            assert_eq!(false, hash_set.expire());

            for i in 0..3 {
                hash_set.insert_with(GBox::new(i, alloc.clone()), op);
            }

            // [0, 1, 2] -> [0, 1, 2]
            {
                let e = hash_set.get(&2).unwrap();
                e.to_mru();
            }

            // [0, 1, 2] -> [1, 2, 0]
            {
                let e = hash_set.get(&0).unwrap();
                e.to_mru();
            }

            // [1, 2, 0] -> [1, 0, 2]
            {
                let e = hash_set.get(&2).unwrap();
                e.to_mru();
            }

            // [1, 0, 2] -> [0, 2]
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_some());
            assert_eq!(true, hash_set.get(&2).is_some());

            // [0, 2] -> [2]
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_none());
            assert_eq!(true, hash_set.get(&2).is_some());

            // [2] -> []
            hash_set.expire();
            assert_eq!(true, hash_set.get(&1).is_none());
            assert_eq!(true, hash_set.get(&0).is_none());
            assert_eq!(true, hash_set.get(&2).is_none());
        }
    }
}
