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

use core::ptr::null_mut;
use std::borrow::Borrow;

/// `RawEntry` is an entry of [`Cache`]
///
/// It forms a forward linked list by itself.
///
/// [`Cache`]: struct.Cache.html
struct RawEntry<T: ?Sized> {
    tail: *mut Self,
    val: T,
}

impl<T> RawEntry<T> {
    /// Creates a new instance followed by `tail` .
    pub fn new(val: T, tail: *mut Self) -> Self {
        Self { tail, val }
    }

    /// Removes `entry` from `bucket` and returns a new bucket excluding `entry`.
    /// The entries are compared by the address.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `bucket` did not include `entry` .
    pub unsafe fn remove(bucket: *mut Self, entry: &mut Self) -> *mut Self {
        if bucket == entry {
            let ret = entry.tail;
            entry.tail = null_mut();
            return ret;
        }

        let mut prev = &mut *bucket;
        loop {
            let next = &mut *prev.tail;

            if prev.tail == entry {
                prev.tail = next.tail;
                return bucket;
            }

            prev = next;
        }
    }
}

impl<T: ?Sized> RawEntry<T> {
    /// Find the entry that equals to `key` , and returns the pointer if any.
    pub fn get<K>(bucket: *mut Self, key: &K) -> Option<*mut Self>
    where
        T: Borrow<K>,
        K: Eq,
    {
        let mut cur = bucket;
        while !cur.is_null() {
            let entry = unsafe { &mut *cur };
            if entry.val.borrow() == key {
                return Some(cur);
            }
            cur = entry.tail;
        }

        None
    }
}

#[cfg(test)]
mod raw_entry_tests {
    use super::*;

    #[test]
    fn get() {
        let r = RawEntry::<i32>::get(null_mut(), &1);
        assert!(true, r.is_none());

        let mut v = Vec::with_capacity(10);
        v.push(RawEntry::<usize>::new(0, null_mut()));
        for i in 1..10 {
            let tail = &mut v[i - 1] as *mut RawEntry<usize>;
            v.push(RawEntry::new(i, tail));
        }

        for i in 0..10 {
            for j in 0..10 {
                let bucket = &mut v[i];
                if i < j {
                    assert_eq!(true, RawEntry::get(bucket, &j).is_none());
                } else {
                    let ptr = RawEntry::get(bucket, &j).unwrap();
                    assert_eq!(j, unsafe { (&*ptr).val });
                }
            }
        }
    }

    #[test]
    fn remove() {
        let mut v = Vec::with_capacity(5);
        v.push(RawEntry::<usize>::new(0, null_mut()));
        for i in 1..5 {
            let tail = &mut v[i - 1] as *mut RawEntry<usize>;
            v.push(RawEntry::new(i, tail));
        }

        let mut bucket = &mut v[4] as *mut RawEntry<usize>;

        // [0, 1, 2, 3, 4] -> [1, 2, 3, 4]
        bucket = unsafe { RawEntry::remove(bucket, &mut v[0]) };
        for i in &[0] {
            assert_eq!(true, RawEntry::get(bucket, i).is_none());
        }
        for i in &[1, 2, 3, 4] {
            let ptr = RawEntry::get(bucket, i).unwrap();
            assert_eq!(*i, unsafe { (&*ptr).val });
        }

        // [1, 2, 3, 4] -> [1, 2, 3]
        bucket = unsafe { RawEntry::remove(bucket, &mut v[4]) };
        for i in &[0, 4] {
            assert_eq!(true, RawEntry::get(bucket, i).is_none());
        }
        for i in &[1, 2, 3] {
            let ptr = RawEntry::get(bucket, i).unwrap();
            assert_eq!(*i, unsafe { (&*ptr).val });
        }

        // [1, 2, 3] -> [1, 3]
        bucket = unsafe { RawEntry::remove(bucket, &mut v[2]) };
        for i in &[0, 2, 4] {
            assert_eq!(true, RawEntry::get(bucket, i).is_none());
        }
        for i in &[1, 3] {
            let ptr = RawEntry::get(bucket, i).unwrap();
            assert_eq!(*i, unsafe { (&*ptr).val });
        }

        // [1, 3] -> [3]
        bucket = unsafe { RawEntry::remove(bucket, &mut v[1]) };
        for i in &[0, 1, 2, 4] {
            assert_eq!(true, RawEntry::get(bucket, i).is_none());
        }
        for i in &[3] {
            let ptr = RawEntry::get(bucket, i).unwrap();
            assert_eq!(*i, unsafe { (&*ptr).val });
        }

        // [3] -> []
        bucket = unsafe { RawEntry::remove(bucket, &mut v[3]) };
        assert_eq!(true, bucket.is_null());
    }
}
