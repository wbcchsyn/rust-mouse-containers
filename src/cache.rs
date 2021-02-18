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

use bulk_allocator::UnLayoutBulkA;
use core::alloc::{GlobalAlloc, Layout};
use core::hash::{BuildHasher, Hash, Hasher};
use core::ptr::null_mut;
use spin_sync::{Mutex, Mutex8, Mutex8Guard};
use std::alloc::handle_alloc_error;
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

    /// Drops and deallocates `bucket` and instances following `bucket` .
    pub fn destroy(bucket: *mut Self, alloc: &dyn GlobalAlloc) {
        let mut cur = bucket;
        while !cur.is_null() {
            unsafe {
                let ptr = cur;
                let entry = &mut *ptr;
                cur = entry.tail;

                ptr.drop_in_place();
                alloc.dealloc(ptr as *mut u8, Layout::new::<Self>());
            }
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

/// `BucketChain` is a thread-safe chaining hash set.
///
/// Each bucket includes 0 or more than 0 entries.
/// Each mutex protect one associated bucket.
struct BucketChain<T, A, S>
where
    A: GlobalAlloc,
{
    mutexes: *mut Mutex8,
    buckets: *mut *mut RawEntry<T>,
    len: usize,

    alloc: Mutex<UnLayoutBulkA<A>>,
    build_hasher: S,
}

impl<T, A, S> Drop for BucketChain<T, A, S>
where
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        let alloc = &*self.alloc.lock().unwrap();
        let mutexes_count = (self.len + Mutex8::LEN - 1) / Mutex8::LEN;

        // Dropping and deallocating all the entries.
        for i in 0..self.len {
            let bucket = unsafe { *self.buckets.add(i) };
            RawEntry::destroy(bucket, alloc);
        }

        // Dropping 'mutexes'
        for i in 0..mutexes_count {
            unsafe {
                let mutex = self.mutexes.add(i);
                mutex.drop_in_place();
            }
        }

        // Deallocating 'mutexes' and 'buckets'
        {
            let layout0 = Layout::array::<*mut RawEntry<T>>(self.len).unwrap();
            let layout1 = Layout::array::<Mutex8>(mutexes_count).unwrap();
            let (layout, _) = layout0.extend(layout1).unwrap();
            unsafe { alloc.backend().dealloc(self.buckets as *mut u8, layout) };
        }
    }
}

impl<T, A, S> BucketChain<T, A, S>
where
    A: GlobalAlloc,
{
    /// Creates a new instance with `chain_len` count of buckets.
    ///
    /// # Panics
    ///
    /// Panics if `chain_len` equals to 0.
    pub fn new(chain_len: usize, alloc: A, build_hasher: S) -> Self {
        assert!(0 < chain_len);

        let mutexes_count = (chain_len + Mutex8::LEN - 1) / Mutex8::LEN;

        // Allocating 'mutexes' and 'buckets'
        let (mutexes, buckets) = {
            let layout0 = Layout::array::<*mut RawEntry<T>>(chain_len).unwrap();
            let layout1 = Layout::array::<Mutex8>(mutexes_count).unwrap();
            let (layout, offset) = layout0.extend(layout1).unwrap();

            let ptr = unsafe { alloc.alloc(layout) };
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            let mutexes = unsafe { ptr.add(offset) as *mut Mutex8 };
            let buckets = ptr as *mut *mut RawEntry<T>;

            (mutexes, buckets)
        };

        // Initializing 'mutexes'
        for i in 0..mutexes_count {
            unsafe {
                let ptr = mutexes.add(i);
                ptr.write(Mutex8::new());
            }
        }

        // Initializing 'buckets'
        for i in 0..chain_len {
            unsafe {
                let ptr = buckets.add(i);
                ptr.write(null_mut());
            }
        }

        let alloc = UnLayoutBulkA::new(Layout::new::<RawEntry<T>>(), alloc);

        Self {
            mutexes,
            buckets,
            len: chain_len,
            alloc: Mutex::new(alloc),
            build_hasher,
        }
    }
}

impl<T, A, S> BucketChain<T, A, S>
where
    A: GlobalAlloc,
    S: BuildHasher,
{
    /// Inserts `val` and returns `(None, lock_guard, new_created_entry)` if `self` did not have
    /// the element that equals to `val` ; otherwise, i.e. if `self` includes the element that
    /// equals to `val` , calls `op(holding_element, val)` and returns the pair of
    /// `Some(op_result)` and the entry holding the element.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `op` changes the hash of the element in `self` .
    ///
    /// It may cause a dead lock to call this method while the thread owns an instance of
    /// `Mutex8Guard` .
    pub unsafe fn insert_with<F, R>(
        &self,
        val: T,
        op: F,
    ) -> (Option<R>, Mutex8Guard, &mut RawEntry<T>)
    where
        T: Eq + Hash,
        F: FnOnce(&mut T, T) -> R,
    {
        let (guard, bucket) = self.get_bucket(&val);

        match RawEntry::get(*bucket, &val) {
            None => {
                // Inserting 'val'
                let layout = Layout::new::<RawEntry<T>>();
                let alloc = self.alloc.lock().unwrap();
                let ptr = alloc.alloc(layout) as *mut RawEntry<T>;
                if ptr.is_null() {
                    handle_alloc_error(layout);
                }

                ptr.write(RawEntry::new(val, *bucket));
                *bucket = ptr;

                (None, guard, &mut *ptr)
            }
            Some(ptr) => {
                // Update the current element.
                let entry = &mut *ptr;
                let r = op(&mut entry.val, val);
                (Some(r), guard, entry)
            }
        }
    }

    /// Acquires the lock and returns a reference to the bucket corresponding to `key` .
    ///
    /// # Safety
    ///
    /// It may cause a dead lock to call this method while the thread has an instance of
    /// `Mutex8Guard` .
    unsafe fn get_bucket<K>(&self, key: &K) -> (Mutex8Guard, &mut *mut RawEntry<T>)
    where
        K: Hash,
    {
        let mut hasher = self.build_hasher.build_hasher();
        key.hash(&mut hasher);
        let index = (hasher.finish() as usize) % self.len;

        let mutex = &*self.mutexes.add(index / Mutex8::LEN);
        let guard = mutex.lock((index % Mutex8::LEN) as u8);

        let bucket = &mut *self.buckets.add(index);

        (guard, bucket)
    }
}

#[cfg(test)]
mod bucket_chain_tests {
    use super::*;
    use gharial::{GAlloc, GBox};
    use std::collections::hash_map::RandomState;

    type Chain = BucketChain<GBox<usize>, GAlloc, RandomState>;

    fn op(a: &mut GBox<usize>, b: GBox<usize>) -> usize {
        assert_eq!(**a, *b);
        **a
    }

    #[test]
    fn new() {
        let alloc = GAlloc::default();
        let _chain = Chain::new(1, alloc.clone(), RandomState::new());
        let _chain = Chain::new(100, alloc.clone(), RandomState::new());
    }

    #[test]
    fn insert_with() {
        let alloc = GAlloc::default();

        // bucket count = 1
        unsafe {
            let chain = Chain::new(1, alloc.clone(), RandomState::new());

            for i in 0..10 {
                let (r, _, _) = chain.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(true, r.is_none());
            }

            for i in 0..10 {
                let (r, _, _) = chain.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(i, r.unwrap());
            }
        }

        // bucket count = 100
        unsafe {
            let chain = Chain::new(100, alloc.clone(), RandomState::new());

            for i in 0..100 {
                let (r, _, _) = chain.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(true, r.is_none());
            }

            for i in 0..100 {
                let (r, _, _) = chain.insert_with(GBox::new(i, alloc.clone()), op);
                assert_eq!(i, r.unwrap());
            }
        }
    }
}
