#![allow(unused)]
extern crate core;

use std::cmp::{max, min, min_by, Ordering, Reverse};
use std::collections::{BinaryHeap, BTreeMap, BTreeSet, HashMap, HashSet, LinkedList, VecDeque};
use std::error::Error;
use std::fmt::{Debug, Display, format};
use std::io::{stdout, stdin, Write, BufReader, BufWriter, BufRead, Stdin, Stdout, Read};
use std::ops::{Add, Deref, DerefMut, Index, RangeBounds, Rem};
use std::process::exit;
use std::ptr::replace;
use std::str::FromStr;
use std::cell::{Ref, RefCell};
use std::cmp::Ordering::{Equal, Greater, Less};
use std::fs::remove_dir;
use std::mem::{forget, swap};
use std::rc::Rc;
use std::str;
use crate::segment_tree::SegmentTree;
use crate::sparse_table::{Loc, SparseTable};
use crate::z_func::*;
use std::iter::FromIterator;
use std::pin::Pin;
use crate::minmax_struct::{MinMaxSegment, MinMaxStack, Mode};
use crate::trie::{Enumerable, Trie};

const MOD: i64 = 1e9 as i64 + 7;
// const MOD: i64 = 998_244_353;
// const MOD: i64 = i64::MAX;
const EPS: f64 = 1e-6;

#[cfg(test)]

mod tests {
    #[test]
    fn it_works() {

    }
}

fn main() -> Result<(), Box<dyn Error>> {
    unsafe {
        solve()?;
        // so_solve()?;
    }
    Ok(())
}

fn so_solve() -> Result<(), Box<dyn Error>> {
    let mut io = IO::new();

    Ok(())

}

// #[target_feature(enable = "avx2")]
unsafe fn solve() -> Result<(), Box<dyn Error>> {
    let mut io = IO::new();

    Ok(())
}


trait SafeGet {
    type Item;

    fn get_s(&self, index: i32) -> Option<&Self::Item>;
    fn get_ms(&mut self, index: i32) -> Option<&mut Self::Item>;
}

impl<T> SafeGet for Vec<T> {
    type Item = T;

    #[inline]
    fn get_s(&self, index: i32) -> Option<&Self::Item> {
        return if index >= 0 {
            self.get(index as usize)
        } else {
            None
        }
    }

    #[inline]
    fn get_ms(&mut self, index: i32) -> Option<&mut Self::Item> {
        return if index >= 0 {
            self.get_mut(index as usize)
        } else {
            None
        }
    }
}

trait SuffixFunc {
    type Item;
    fn suffix_func(&mut self, func: fn(Self::Item, Self::Item) -> Self::Item) -> Vec<Self::Item>;
}

impl<'a, T: Clone> SuffixFunc for [T] {
    type Item = T;

    fn suffix_func(&mut self, func: fn(Self::Item, Self::Item) -> Self::Item) -> Vec<Self::Item> {
        let mut ans = Vec::new();
        if let Some(v) = self.get(0) {
            ans.push(v.clone());
        }
        for v in self.iter().skip(1) {
            ans.push(func(ans.last().unwrap().clone(), v.clone()));
        }

        ans
    }
}

trait IndexReverse {
    type Item;
    fn index_reverse<'a>(&self, max_val: &Self::Item) -> Vec<usize>;
}

impl<T: Enumerable> IndexReverse for Vec<T> {
    type Item = T;

    fn index_reverse(&self, max_val: &T) -> Vec<usize> {
        let mut ans = vec![0; max_val.get_index()];
        for (i, val) in self.iter().enumerate() {
            ans[val.get_index()] = i;
        }
        ans
    }
}

trait Implication {
    fn implication(self, other: Self) -> bool;
}

impl Implication for bool {
    fn implication(self, other: bool) -> bool {
        !self || other
    }
}

mod z_func {
    use std::cmp::{max, min};

    pub trait ZFunc {
        fn z_func(&self) -> Vec<usize>;
    }


    impl ZFunc for String {
        fn z_func(&self) -> Vec<usize> {
            let bytes = self.as_bytes();
            let mut ans = vec![0; bytes.len()];
            let mut l = 0;
            let mut r = 0;

            for i in 1..bytes.len() {
                if i <= r {
                    ans[i] = min(ans[i - l], r - i + 1);
                }
                while i + ans[i] < bytes.len() && (bytes[i + ans[i]] == bytes[ans[i]]) {
                    ans[i] += 1;
                }
                if i + ans[i] - 1 > r {
                    l = i;
                    r = i + ans[i] - 1;
                }
            }

            ans
        }
    }
}
trait SuffixArray {
    fn suffix_array(&mut self) -> Vec<usize>;
}

impl SuffixArray for String {
    fn suffix_array(&mut self) -> Vec<usize> {
        self.push('\0');
        let data = self.as_bytes();

        let mut start = Vec::with_capacity(data.len());
        for i in 0..data.len() {
            start.push(i);
        }
        start.sort_unstable_by_key(|v| data[*v]);
        let mut prev = vec![0; data.len() * 2];
        prev[start[0]] = 0;
        for i in 1..data.len() {
            if data[start[i]] == data[start[i - 1]] {
                prev[start[i]] = prev[start[i - 1]];
            } else {
                prev[start[i]] = prev[start[i - 1]] + 1;
            }
        }
        for i in data.len()..(data.len() * 2) {
            prev[i] = prev[i - data.len()];
        }

        let mut k = 0;
        for _ in 0..(data.len() as u32).lg2() + 1 {
            let mut start = Vec::with_capacity(data.len());
            for i in 0..data.len() {
                start.push(i);
            }
            let delta = usize::pow(2, k);
            start.sort_unstable_by_key(|v| (prev[*v], prev[*v + delta]));

            let mut new_prev = vec![0; data.len() * 2];
            new_prev[start[0]] = 0;
            for i in 1..data.len() {
                if prev[start[i]] == prev[start[i - 1]] && prev[start[i] + delta] == prev[start[i - 1] + delta] {
                    new_prev[start[i]] = new_prev[start[i - 1]];
                } else {
                    new_prev[start[i]] = new_prev[start[i - 1]] + 1;
                }
            }
            prev = new_prev;
            for i in data.len()..(data.len() * 2) {
                prev[i] = prev[i - data.len()];
            }

            k += 1;
        }

        let mut ans = vec![0; data.len()];

        for (i, val) in prev.iter().take(data.len()).enumerate() {
            ans[*val] = i;
        }

        self.pop();
        return ans;
    }
}

fn generate_lcp(data: &mut String, suffix_arr: &[usize]) -> Vec<usize> {
    let big_str = data;
    let big_str_arr = big_str.as_bytes();

    let mut index = vec![0; suffix_arr.len()];
    for i in 0..suffix_arr.len() {
        index[suffix_arr[i]] = i;
    }

    let mut lcp = vec![0; big_str_arr.len()];

    let mut k = 0;
    big_str.push('\0');
    let big_str_arr = big_str.as_bytes();

    for start in 0..(big_str_arr.len() - 1) {
        k = max(0, k as i32 - 1) as usize;

        while big_str_arr[start + k] == big_str_arr[suffix_arr[index[start] - 1] + k] {
            k += 1;
        }
        lcp[index[start] - 1] = k;
    }
    big_str.pop();

    return lcp;
}



trait Log {
    type Item;

    fn lg2(self) -> Self::Item;
}

impl Log for u32 {
    type Item = u32;

    fn lg2(self) -> u32 {
        32 - self.leading_zeros() - 1 // self != 0
    }
}

trait Norm {
    type Item;

    fn norm(self) -> Self::Item;
}

impl Norm for i64 {
    type Item = i64;

    fn norm(self) -> i64 {
        let mut result = self % MOD;

        // if result * MOD < 0 {
        if result < 0 {
            result += MOD;
        }
        return result;
    }
}


fn assert(val: bool) -> Result<(), ()> {
    if val {
        return Ok(());
    }
    return Err(());
}


mod minmax_struct {
    use std::cmp::{max, min};
    use std::collections::VecDeque;

    #[derive(Clone, Copy)]
    pub enum Mode {
        Min, Max
    }

    pub struct MinMaxStack<T> {
        stack: VecDeque<(T, T)>,
        minmax_func_ref: for<'a> fn(&'a T, &'a T) -> &'a T
    }

    impl<T: Ord + Clone> MinMaxStack<T> {
        pub fn new(mode: Mode) -> Self {

            let minmax_func_ref: for<'a> fn(&'a T, &'a T) -> &'a T = match mode {
                Mode::Min => { |a, b| min(a, b) },
                Mode::Max => { |a, b| max(a, b) }
            };

            Self {
                stack: VecDeque::new(),
                minmax_func_ref
            }
        }

        pub fn push(&mut self, v: T) {
            let new_minmax = if let Some(prev) = self.minmax() {
                (self.minmax_func_ref)(&v, prev).clone()
            } else {
                v.clone()
            };
            self.stack.push_front((v, new_minmax));
        }

        pub fn pop(&mut self) -> Option<(T, T)> {
            self.stack.pop_front()
        }

        pub fn peek(&self) -> Option<*const (T, T)> {
            let res = self.stack.front();
            match res {
                None => { None }
                Some(v) => { Some(v) }
            }
        }

        pub fn size(&self) -> usize {
            self.stack.len()
        }

        pub fn clear(&mut self) {
            self.stack.clear();
        }

        pub fn minmax(&self) -> Option<&T> {
            if let Some(v) = self.stack.front() {
                Some(&v.1)
            } else {
                None
            }
        }
    }

    pub struct MinMaxSegment<T> {
        f: MinMaxStack<T>,
        s: MinMaxStack<T>,
    }

    impl<T: Ord + Clone> MinMaxSegment<T> {
        pub fn new(mode: Mode) -> Self {

            Self {
                f: MinMaxStack::new(mode),
                s: MinMaxStack::new(mode)
            }
        }

        fn swap_to_s(&mut self) {
            while let Some(v) = self.f.pop() {
                self.s.push(v.0);
            }
        }

        pub fn push(&mut self, v: T) {
            self.f.push(v);
        }


        pub fn pop(&mut self) -> Option<(T, T)> {
            if let Some(v) = self.s.pop() {
                Some(v)
            } else {
                self.swap_to_s();

                if let Some(last) = self.s.pop() {
                    Some(last)
                } else {
                    None
                }
            }
        }

        pub fn peek(&mut self) -> Option<*const (T, T)> {
            if let Some(v) = self.s.peek() {
                Some(v)
            } else {
                self.swap_to_s();

                if let Some(last) = self.s.peek() {
                    Some(last)
                } else {
                    None
                }
            }
        }

        pub fn size(&self) -> usize {
            self.f.size() + self.s.size()
        }

        pub fn clear(&mut self) {
            self.f.clear();
            self.s.clear();
        }

        pub fn minmax(&self) -> Option<&T> {
            if let Some(f_res) = self.f.minmax() {
                if let Some(s_res) = self.s.minmax() {
                    return Some((self.f.minmax_func_ref)(f_res, s_res));
                } else {
                    return Some(f_res);
                }
            };
            if let Some(s_res) = self.s.minmax() {
                return Some(s_res);
            }
            None
        }
    }
}

mod trie {
    use std::collections::{BTreeMap, HashMap};
    use std::hash::Hash;
    use std::thread::current;

    pub trait Enumerable {
        fn get_index(&self) -> usize;
    }

    macro_rules! impl_enumerable {
    ($($t: ty),+) => {
        $(
            impl Enumerable for $t {
                fn get_index(&self) -> usize {
                    return *self as usize;
                }
            }
        )+
    }
    }

    impl_enumerable!(u8, u16, u32, u64, usize);

    #[derive(Debug)]
    pub struct Node {
        childs: Vec<Option<Box<Node>>>,
        values: u32
    }

    impl Node {
        fn new(n: usize, values: u32) -> Self {
            Self {
                childs: (0..n).map(|v| None).collect(),
                values
            }
        }

        fn add_child(&mut self, index: usize, child: Box<Node>) {
            self.childs[index] = Some(child);
        }
    }

    #[derive(Debug)]
    pub struct Trie {
        childs: Vec<Option<Box<Node>>>,
        lang_size: usize
    }


    impl Trie {
        pub fn new(n: usize) -> Self {
            Self {
                childs: (0..n).map(|v| None).collect(),
                lang_size: n
            }
        }

        pub fn add_val<T: Enumerable>(&mut self, mut val_iter: impl Iterator<Item=T>) {
            let mut current_node;

            if let Some(v) = val_iter.next() {
                if let Some(child) = &mut self.childs[v.get_index()] {
                    current_node = child;
                } else {
                    let mut child = Box::new(Node::new(self.lang_size, 0));
                    self.childs[v.get_index()] =  Some(child);
                    current_node = self.childs[v.get_index()].as_mut().unwrap();

                }
            } else {
                return;
            }

            for val in val_iter {

                if current_node.childs[val.get_index()].is_some() {
                    current_node = current_node.childs[val.get_index()].as_mut().unwrap();
                } else {
                    let child = Box::new(Node::new(self.lang_size, 0));
                    current_node.add_child(val.get_index(), child);
                    current_node = current_node.childs[val.get_index()].as_mut().unwrap();
                }
            }
            current_node.values += 1;
        }

        // pub fn contains_val<'a, T: Enumerable>(&self, mut val_iter: Box<dyn Iterator<Item=&T> + 'a>) -> bool {
        pub fn contains_val<'a, T: 'a + Enumerable>(&self, mut val_iter: impl Iterator<Item=&'a T>) -> bool {
            let mut current_node;

            if let Some(v) = val_iter.next() {
                if let Some(child) = &self.childs[v.get_index()] {
                    current_node = child;
                } else {
                    return false;
                }
            } else {
                return true;
            }

            for val in val_iter {
                if let Some(child) = &current_node.childs[val.get_index()] {
                    current_node = child;
                } else {
                    return false;
                }
            }
            return true;
        }

        pub fn iter(&self) -> TrieIter {
            TrieIter::new(self)
        }
    }


    pub struct TrieIter<'a> {
        trie: &'a Trie,
        cur_node: Option<&'a Box<Node>>,
    }

    impl<'a> TrieIter<'a> {

        pub fn new(trie: &'a Trie) -> Self {
            Self {
                trie,
                cur_node: None,
            }
        }

        pub fn next(mut self, next_index: Option<usize>) -> Option<(&'a Vec<Option<Box<Node>>>, Self)> {

            return if let Some(next_index) = next_index {
                if let Some(cur) = self.cur_node {
                    self.cur_node = Some(cur.childs[next_index].as_ref().unwrap());
                } else {
                    self.cur_node = Some(self.trie.childs[next_index].as_ref().unwrap());
                }
                Some((&self.cur_node.unwrap().childs, self))
            } else {
                if let Some(cur) = self.cur_node {
                    Some((&cur.childs, self))
                } else {
                    Some((&self.trie.childs, self))
                }
            }
        }
    }
}


mod sparse_table {
    use crate::{assert, Log};

    pub struct SparseTable<T: Clone + Copy> {
        table: Vec<Vec<T>>,
        func: fn(T, T) -> T
    }

    pub enum Loc {
        Left, Right
    }

    impl<T: Clone + Copy + PartialEq> SparseTable<T> {
        pub fn new(raw: Vec<T>, func: fn(T, T) -> T) -> Self {
            let count = u32::lg2(raw.len() as u32) as usize;
            let mut table = vec![vec![raw[0]; raw.len()]; count + 1];

            table[0] = raw;

            for i in 1..=count {
                for j in 0..(table[0].len() - (1 << (i - 1))) {
                    table[i][j] = func(table[i - 1][j], table[i - 1][j + (1 << (i - 1))]);
                }
            }

            SparseTable {
                table,
                func
            }

        }

        pub fn get(&self, left: usize, right: usize) -> T {
            let log2distance = ((right - left + 1) as u32).lg2();

            (self.func)(
                self.table[log2distance as usize][left],
                self.table[log2distance as usize][right + 1 - (1 << log2distance)]
            )
        }



        pub fn binary_lifting(&self, pos: usize, loc_type: Loc) -> usize {
            let mut cur_pos: i32 = pos as i32;
            for shift in (0..self.table.len()).rev() {
                match loc_type {
                    Loc::Left => {
                        if cur_pos + 1 < (1 << shift) {
                            continue;
                        }
                        // if self.get(cur_pos as usize + 1 - (1 << shift), cur_pos as usize) == self.table[0][pos] {
                        if self.get(cur_pos as usize + 1 - (1 << shift), pos) == self.table[0][pos] {
                            cur_pos -= 1 << shift;
                        }
                    }
                    Loc::Right => {
                        if cur_pos as usize + (1 << shift) - 1 >= self.table[0].len() {
                            continue;
                        }
                        // if self.get(cur_pos as usize, cur_pos as usize + (1 << shift) - 1) == self.table[0][pos] {
                        if self.get(pos, cur_pos as usize + (1 << shift) - 1) == self.table[0][pos] {
                            cur_pos += 1 << shift;
                        }
                    }
                }
            }

            return match loc_type {
                Loc::Left => { cur_pos + 1 }
                Loc::Right => { cur_pos - 1 }
            } as usize;
        }

        // pub fn binary_lifting(&self, pos: usize, loc_type: Loc) -> usize {
        //     self.binary_lifting_with_val(pos, self.table[0][pos], loc_type)
        // }
    }
}


static mut FACTORIAL: Factorial = Factorial::empty();

struct Factorial {
    data: Vec<i32>,
    count: usize
}

impl Factorial {

    const fn empty() -> Factorial {
        Factorial {
            data: Vec::new(),
            count: 0
        }
    }

    fn new(init: usize) -> Factorial {
        let mut data = Vec::with_capacity(init);
        data.push(1);
        Factorial {
            data,
            count: 1
        }
    }

    fn get(&mut self, i: usize) -> i32 {
        if self.count < i {
            for l_i in self.count + 1..=i {
                self.data.push((self.data[l_i - 2] as i64 * l_i as i64 % MOD) as i32);
            }
            self.count += i - self.count;
        }

        if self.data[i - 1] < 0 {
            panic!("factorial error");
        }
        self.data[i - 1]
    }

}

struct DSU {
    data: Vec<(i32, i32)>,
    rank: Vec<i32> // depth
}

impl DSU {

    fn new(count: usize) -> DSU {
        DSU {
            data: vec![(-1, -1); count],
            rank: vec![1; count]
        }
    }

    fn break_union(&mut self, f: i32, s: i32) {
        self.data[(f - 1) as usize].1 = -1;
        self.data[(s - 1) as usize].0 = -1;
    }

    fn union(&mut self, mut f: i32, mut s: i32) {
        f -= 1;
        s -= 1;

        let mut f_root = (self.find_set(f + 1) - 1) as usize;
        let mut s_root = (self.find_set(s + 1) - 1) as usize;

        if f_root != s_root {
            if self.rank[f_root] < self.rank[s_root] {
                swap(&mut f_root, &mut s_root);
            }
            self.data[s_root].1 = f_root as i32;
            self.data[f_root].0 = s_root as i32;

            self.rank[f_root] += self.rank[s_root];
            // if self.rank[f_root] == self.rank[s_root] {
            //     self.rank[f_root] += 1;
            // }
        }
    }


    fn find_set(&mut self, mut v: i32) -> i32 {
        v -= 1;

        if self.data[v as usize].1 == -1 {
            return v + 1;
        }

        self.data[v as usize].1 = self.find_set(self.data[v as usize].1 + 1) - 1;
        return self.data[v as usize].1 + 1;
    }

    /*
    fn get_union(&mut self, mut i: i32) -> Vec<i32> {
        let mut ans = Vec::new();

        i -= 1;

        while self.data[i as usize].0 != -1 {
            i = self.data[i as usize].0;
        }

        while i != -1 {
            ans.push(i + 1 as i32);
            i = self.data[i as usize].1;
        }

        ans
    }

     */
}

struct Math {}

macro_rules! impl_gcd { // maybe u32
    ($target: ident, $($t: ty, $t_name: ident),+) => {
        $(
            fn $t_name(a: $t, b: $t) -> $t {
                if b == 0 {
                    return a;
                }
                return $target::$t_name(b, a % b);
            }
        )+
    }
}


macro_rules! impl_lcm {
    ($target: ident, $($t: ty, $t_name: ident, $gcd_name: ident),+) => {
        $(
            fn $t_name(a: $t, b: $t) -> $t {
                return a / $target::$gcd_name(a, b) * b;
            }
        )+
    }
}

macro_rules! impl_math_mid {
    ($($t: ty, $t_name: ident),+) => {
        $(
            #[inline]
            fn $t_name(a: $t, b: $t) -> $t {
                return min(a, b) + ((b - a) >> 1);
            }
        )+
    }
}

trait Mid {
    fn mid(&self, other: Self) -> Self;
}

macro_rules! impl_mid {
    ($($t: ty),+) => {
        $(
            impl Mid for $t {

                #[inline]
                fn mid(&self, other: Self) -> Self {
                    // return min(self, &other) + ((other - self) >> 1);
                    return self + ((other - self) >> 1);
                }
            }
        )+
    }
}

impl_mid! { i8, i16, i32, i64, i128, usize, u8, u16, u32, u64, u128 }



impl Math {

    impl_gcd! { Math, i8, gcd_i8, i16, gcd_i16, i32, gcd_i32, i64, gcd_i64, u32, gcd_u32 }
    impl_lcm! { Math, i8, lcm_i8, gcd_i8, i16, lcm_i16, gcd_i16, i32, lcm_i32, gcd_i32, i64, lcm_i64, gcd_i64 }
    impl_math_mid! { i8, mid_i8, i16, mid_i16, i32, mid_i32, i64, mid_i64, usize, mid_usize }

    unsafe fn solve_c(max_v: i32, c: &[i32]) -> i32 {
        let mut bottom: i64 = 1;

        let mut deg = 0;
        for val in c {
            deg += val;
            bottom *= FACTORIAL.get(*val as usize) as i64;
            bottom %= MOD;
        }

        if deg != max_v {
            panic!("err input data");
        }

        let m_bottom = Math::bin_pow(bottom as i32, (MOD - 2) as u64);

        ((FACTORIAL.get(max_v as usize) as i64 * m_bottom as i64) % MOD) as i32
    }


    fn bin_pow(base: i32, degree: u64) -> i32 {
        if degree == 0 || base == 1 {
            return 1;
        }

        return if (degree & 1) == 0 {
            let res = Math::bin_pow(base, degree >> 1) as i64;
            res * res % MOD
        } else {
            (base as i64 % MOD) * Math::bin_pow(base, degree - 1) as i64 % MOD
        } as i32
    }

    #[inline]
    fn mid_f32(l: f32, r: f32) -> f32 {
        ((l as f64 + r as f64) / 2f64) as f32
    }

    fn get_prime_nums(max: i32) -> Vec<i32> {
        let mut data = vec![0; max as usize];

        let mut start = 2;

        while (start) < (max >> 1) {
            if data[start as usize - 1] == 0 {

                for i in ((start << 1)..=max).step_by(start as usize) {
                    data[i as usize - 1] = 1;
                }
            }
            start += 1;
        }

        return data.into_iter().enumerate()
            .filter(|v| v.1 == 0)
            .map(|v| v.0 as i32 + 1)
            .collect();
    }

}

struct DijkstraObj<T> {
    val: T,
    cost: i32
}

impl<T> PartialOrd for DijkstraObj<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialEq for DijkstraObj<T> {
    fn eq(&self, other: &Self) -> bool {
        self.cost == other.cost
    }
}

impl<T> Eq for DijkstraObj<T> { }

impl<T> Ord for DijkstraObj<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cost.cmp(&other.cost).reverse()
    }
}


impl<T> DijkstraObj<T> {

    fn new(val: T, cost: i32) -> Self {
        DijkstraObj {
            val,
            cost
        }
    }

}

struct Graph {
    data: Rc<RefCell<Vec<Vec<usize>>>>,
    ancestors: Vec<i32>,
    used: Vec<bool>,
    depth: Vec<i32>
}

impl Graph {

    fn new(data: Vec<Vec<usize>>) -> Self {
        Graph {
            ancestors: vec![-1; data.len()],
            used: vec![false; data.len()],
            depth: vec![0; data.len()],
            data: Rc::new(RefCell::new(data))
        }
    }



    fn dfs(&mut self, cur: usize, cur_depth: i32) -> bool {
        self.used[cur] = true;
        self.depth[cur] = cur_depth;

        for next in &self.data.clone().borrow()[cur] {
            if !self.used[*next] {
                if self.dfs(*next, (cur_depth + 1) % 2) {
                    return true;
                }
            } else if cur_depth == self.depth[*next] {
                return true;
            }
        }
        return false;
    }

    fn restart(&mut self) {
        self.ancestors.fill(-1);
    }


    fn bfs(&mut self, from: usize, to: usize) -> i32 {
        self.restart();

        // let mut queue = BinaryHeap::new();
        let mut queue = VecDeque::new();
        queue.push_back(DijkstraObj::new(from - 1, 0));

        let mut dist = vec![i32::MAX; self.data.borrow().len()];
        dist[from - 1] = 0;

        while let Some(cur) = queue.pop_front() {

            if cur.cost >= dist[to - 1] {
                return dist[to - 1];
            }

            for next in &self.data.borrow()[cur.val] {

                if dist[*next] > cur.cost + 1 {
                    queue.push_back(DijkstraObj::new(*next, cur.cost + 1));
                    self.ancestors[*next] = cur.val as i32;
                    dist[*next] = cur.cost + 1;

                    // if *next == to - 1 {
                    //     return cur.cost + 1;
                    // }
                }
            }
        }
        return if dist[to - 1] == i32::MAX { -1 } else { dist[to - 1] };
    }

}


mod segment_tree {
    use std::cmp::{max, min};
    use crate::segment_tree::UpdatedVal::{Undefined, Val};

    #[derive(Clone)]
    enum UpdatedVal<T: Clone> {
        Undefined,
        Val(T)
    }

    pub struct SegmentTree<T: Clone> {
        segment_array: Vec<T>,
        updated_val: Vec<Option<T>>,
        size: usize,
        neutral: T,
        // func: Box<dyn Fn(T, T) -> T>,
        merge_func: fn(T, T) -> T,
        // mult_func: Option<fn(T, u32) -> T>,
        mult_func: Option<Box<dyn Fn(T, u32) -> T>>,
    }

    impl<T: Clone> SegmentTree<T> {

        // pub fn new(arr: &[T], neutral: T, func: impl Fn(T, T) -> T + 'static) -> Self {
        // pub fn new(arr: &[T], neutral: T, merge_func: fn(T, T) -> T, mult_func: Option<fn(T, u32) -> T>) -> Self {
        pub fn new(arr: &[T], neutral: T, merge_func: fn(T, T) -> T, mult_func: Option<Box<dyn Fn(T, u32) -> T>>) -> Self {
            let mut len;
            let mut segment_arr_len;
            if arr.len() == 1 {
                segment_arr_len = 1;
                len = 2;
            } else {
                let len_with_dec = arr.len() - 1;
                segment_arr_len = (len_with_dec & (1 << len_with_dec.ilog2())) << 1;
                len = segment_arr_len << 1;
            }
            let mut res = SegmentTree {
                segment_array: vec![neutral.clone(); len],
                updated_val: vec![None; len],
                size: segment_arr_len,
                neutral,
                // merge_func: Box::new(func),
                merge_func,
                // mult_func: Box::new(func),
                mult_func
            };

            // res.build(arr, 1, 0, arr.len() - 1);
            res.build(arr, 1, 0, res.size - 1);

            res
        }

        fn build(&mut self, arr: &[T], v: usize, tl: usize, tr: usize) {
            if tl == tr {
                self.segment_array[v] = arr.get(tl).unwrap_or(&self.neutral).clone();
            } else {
                let tm = (tl + tr) / 2;
                self.build(arr, v * 2, tl, tm);
                self.build(arr, v * 2 + 1, tm + 1, tr);
                self.segment_array[v] = (self.merge_func)(self.segment_array[v * 2].clone(),
                                                          self.segment_array[v * 2 + 1].clone());
            }
        }

        pub fn get_value(&mut self, left: usize, right: usize) -> T { // include borders
            return self.sum(1, 0, self.size - 1, left, right);
        }

        fn sum(&mut self, v: usize, tl: usize, tr: usize, l: usize, r: usize) -> T {
            if l > r {
                return self.neutral.clone();
            }
            if l == tl && r == tr {
                return self.segment_array[v].clone();
            }

            self.push(v);

            let tm = (tl + tr) / 2;
            return (self.merge_func)(self.sum(v * 2, tl, tm, l, min(r, tm)),
                                     self.sum(v * 2 + 1, tm + 1, tr, max(l, tm + 1), r));
        }

        pub fn replace_value(&mut self, index: usize, value: T) {
            self.update(1, 0, self.size - 1, index, value);
        }

        fn update(&mut self, v: usize, tl: usize, tr: usize, pos: usize, new_val: T) {
            if tl == tr {
                self.segment_array[v] = new_val;
            } else {
                self.push(v);

                let tm = (tl + tr) / 2;
                if pos <= tm {
                    self.update(v * 2, tl, tm, pos, new_val);
                } else {
                    self.update(v * 2 + 1, tm + 1, tr, pos, new_val);
                }

                self.segment_array[v] = (self.merge_func)(self.segment_array[v * 2].clone(),
                                                          self.segment_array[v * 2 + 1].clone());
            }
        }


        #[inline]
        fn count_leaves(&self, v: usize) -> u32{
            1 << ((self.segment_array.len() - 1).ilog2() - v.ilog2())
        }

        fn push(&mut self, v: usize) {
            if let Some(val) = self.updated_val[v].clone() {
                self.updated_val[v * 2] = Some(val.clone());
                self.segment_array[v * 2] = self.mult_func.as_ref().unwrap()(val.clone(), self.count_leaves(v * 2));

                self.updated_val[v * 2 + 1] = Some(val.clone());
                self.segment_array[v * 2 + 1] = self.mult_func.as_ref().unwrap()(val, self.count_leaves(v * 2 + 1));

                self.segment_array[v] = (self.merge_func)(self.segment_array[v * 2].clone(),
                                                          self.segment_array[v * 2 + 1].clone());

                self.updated_val[v] = None;
            }

        }

        pub fn update_segment(&mut self, l: usize, r: usize, new_val: T) {
            assert_eq!(self.mult_func.is_some(), true);
            self.update_segment_impl(1, 0, self.size - 1, l, r, new_val);
        }

        fn update_segment_impl(&mut self, v: usize, tl: usize, tr: usize, pos_l: usize, pos_r: usize, new_val: T) {
            if pos_l > pos_r {
                return;
            }

            if tl == pos_l && tr == pos_r {
                self.updated_val[v] = Some(new_val.clone());
                self.segment_array[v] = self.mult_func.as_ref().unwrap()(new_val, self.count_leaves(v));
            } else {
                self.push(v);

                let tm = (tl + tr) / 2;
                self.update_segment_impl(v * 2, tl, tm, pos_l, min(tm, pos_r), new_val.clone());
                self.update_segment_impl(v * 2 + 1, tm + 1, tr, max(tm + 1, pos_l), pos_r, new_val);

                self.segment_array[v] = (self.merge_func)(self.segment_array[v * 2].clone(),
                                                          self.segment_array[v * 2 + 1].clone());

            }
        }
    }
}


struct IO {
    reader: BufReader<Stdin>,
    writer: BufWriter<Stdout>,
    local_buffer: Vec<String>
}

impl Drop for IO {
    fn drop(&mut self) {
        self.flush();
    }
}

macro_rules! impl_read_simple {
    ($($t: ty, $t_name: ident), +) => {
        $(
            fn $t_name(&mut self) -> Result<$t, Box<dyn Error>> {
                let mut res = String::new();
                self.reader.read_line(&mut res)?;
                return Ok(res.trim().parse()?);
            }
        )+
    }
}

macro_rules! impl_read_array {
    ($($t: ty, $t_name: ident), +) => {
        $(
            fn $t_name(&mut self, split: &str) -> Vec<$t> {
                let mut res = String::new();
                self.reader.read_line(&mut res).expect("error read");
                return res.trim().split(split).filter(|v| !v.is_empty()).map(|v| v.parse()
                    .expect(&("not is ".to_owned() + stringify!($t)))).collect::<Vec<$t>>();
            }
        )+
    }
}

impl IO {

    impl_read_simple! { i8, read_i8, i16, read_i16, i32, read_i32, i64, read_i64,
        u8, read_u8, u16, read_u16, u32, read_u32, u64, read_u64,
        usize, read_usize,
        f32, read_f32, f64, read_f64,
        String, read_str
    }

    impl_read_array! { i8, read_array_i8, i16, read_array_i16, i32, read_array_i32, i64, read_array_i64,
        u8, read_array_u8, u16, read_array_u16, u32, read_array_u32, u64, read_array_u64,
        usize, read_array_usize,
        f32, read_array_f32, f64, read_array_f64,
        String, read_array_str
    }

    pub fn new() -> IO {
        IO {
            reader: BufReader::new(stdin()),
            writer: BufWriter::new(stdout()),
            local_buffer: Vec::new()
        }
    }


    pub fn read_array<T: FromStr>(&mut self, split: &str) -> Vec<T> {
        let mut res = String::new();
        self.reader.read_line(&mut res).expect("error read");
        return res.trim().split(split).filter(|v| !v.is_empty()).map(|v| v.parse().ok()
            .expect("Failed parse")).collect::<Vec<T>>();
    }

    pub fn write<T: Display>(&mut self, value: T, end: &str) {
        self.writer.write(value.to_string().as_bytes()).expect("error write");
        self.writer.write(end.as_bytes()).expect("error write");
    }

    pub fn new_line(&mut self) {
        self.writer.write("\n".as_bytes()).expect("error write");
    }

    pub fn write_ref<T: Display>(&mut self, value: &T, end: &str) {
        self.writer.write(value.to_string().as_bytes()).expect("error write");
        self.writer.write(end.as_bytes()).expect("error write");
    }

    pub fn flush(&mut self) {
        self.writer.flush().expect("error flush");
    }

    fn next<T: FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.local_buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            self.reader.read_line(&mut input).expect("Failed read");
            self.local_buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}