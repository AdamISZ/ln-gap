//! The authenticated jump list (S. D. Lerner, "Latest innovations in
//! BitVMX", June 2024): each step's hash commits to the previous step's
//! and to one earlier step's, the long jump, chosen by the step number
//! alone, so that any step reaches any earlier one in a few times
//! `log2(n)` hops: `3 log2(n) + 1` for Lerner's 32-bit words; in general
//! `2^(counter + 1) + data - 2`, where `counter` and `data` are the
//! counter's and the data's bits (86 for the Groth16 verifier's 29-bit
//! steps: measured exhaustively on small words, where the greedy path
//! below is also the shortest for every pair).
//!
//! A step number is a word of `bits` bits: its low `counter` bits are a
//! counter, the rest data. The counter `c` selects bit `c` of the word.
//! If `c` is a data bit and it is set, the long jump goes to the number
//! with bit `c` cleared, the data bits below it set and the counter kept,
//! less one (so the counter becomes `c - 1`, borrowing from the data bits
//! at 0). Otherwise the step has no long jump of its own, and we let it
//! jump to the previous step.

/// A jump list's shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JumpList {
    /// The word's bits: `log2(max_steps)`.
    pub bits: u32,
    /// The counter's bits: enough to count the word's bit positions.
    pub counter: u32,
}

/// A hop of a path, backwards: to the previous step, or the long jump.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hop {
    Short,
    Long,
}

impl JumpList {
    /// For steps below `2^bits`.
    pub fn new(bits: u32) -> JumpList {
        let counter = 32 - (bits - 1).leading_zeros();
        assert!(bits > counter, "a word of {bits} bits leaves no data bits");
        JumpList { bits, counter }
    }
    /// From BitVMX's search definition (`max_steps` a power of two).
    pub fn for_max_steps(max_steps: u64) -> JumpList {
        assert!(max_steps.is_power_of_two(), "max_steps is a power of two");
        JumpList::new(max_steps.trailing_zeros())
    }
    /// Step `i`'s long jump (`i - 1` if it has none). `i >= 1`.
    pub fn jump(&self, i: u64) -> u64 {
        assert!(i >= 1, "step 0 has no predecessor");
        let c = (i & ((1 << self.counter) - 1)) as u32;
        if c < self.counter || c >= self.bits || (i >> c) & 1 == 0 {
            return i - 1;
        }
        let above = (i >> (c + 1)) << (c + 1);
        let data_below = ((1u64 << c) - 1) & !((1u64 << self.counter) - 1);
        let t = above | data_below | u64::from(c);
        // bit c clear, data below set, the counter kept, then less one
        t - 1
    }
    /// Whether step `i` has a long jump of its own.
    pub fn has_long(&self, i: u64) -> bool {
        self.jump(i) != i - 1
    }
    /// A path from `from` back to `to <= from`: the hops, in order, and the
    /// steps they reach (`to` last). Greedy: take the long jump whenever it
    /// doesn't pass `to` (the shortest path, on every pair of every small
    /// word checked against a breadth-first search).
    pub fn path(&self, from: u64, to: u64) -> Vec<(Hop, u64)> {
        assert!(to <= from, "a path goes back");
        let mut v = vec![];
        let mut s = from;
        while s > to {
            let j = self.jump(s);
            if j != s - 1 && j >= to {
                v.push((Hop::Long, j));
                s = j;
            } else {
                v.push((Hop::Short, s - 1));
                s -= 1;
            }
        }
        v
    }
    /// The longest path's hops: `2^(counter + 1) + data - 2`.
    pub fn bound(&self) -> usize {
        (2usize << self.counter) + (self.bits - self.counter) as usize - 2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_shape() {
        let j = JumpList::new(29);
        assert_eq!((j.bits, j.counter), (29, 5));
        assert_eq!(JumpList::for_max_steps(1 << 29), j);
        assert_eq!(JumpList::new(32).counter, 5);
        assert_eq!(JumpList::new(11).counter, 4);
    }

    #[test]
    fn jumps_go_back() {
        let j = JumpList::new(12);
        for i in 1..(1u64 << 12) {
            let t = j.jump(i);
            assert!(t < i, "{i} -> {t}");
        }
        // a long jump: counter 7 selects bit 7, which is set
        let i = (1 << 7) | (1 << 10) | 7;
        let t = j.jump(i);
        assert_eq!(t, ((1 << 10) | (0b111 << 4) | 7) - 1);
    }

    /// Every pair of steps of a small word: the greedy path reaches the
    /// target within the bound, each hop a real hop.
    #[test]
    fn every_path_is_short() {
        for bits in [9u32, 10, 11] {
            let j = JumpList::new(bits);
            let n = 1u64 << bits;
            let mut worst = 0;
            for from in 1..n {
                for to in 0..from {
                    let p = j.path(from, to);
                    assert_eq!(p.last().unwrap().1, to);
                    let mut s = from;
                    for &(h, x) in &p {
                        assert_eq!(x, if h == Hop::Long { j.jump(s) } else { s - 1 });
                        s = x;
                    }
                    worst = worst.max(p.len());
                }
            }
            println!("JUMP {bits} bits: the longest greedy path {worst} hops (bound {})", j.bound());
            assert_eq!(worst, j.bound(), "{bits} bits: the bound is reached exactly");
        }
    }

    #[test]
    fn long_paths_at_29_bits() {
        let j = JumpList::new(29);
        let mut worst = 0;
        let mut x: u64 = 0x9e3779b97f4a7c15;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let from = (x % ((1 << 29) - 1)) + 1;
            let to = (x >> 31) % from;
            let p = j.path(from, to);
            assert_eq!(p.last().map_or(from, |h| h.1), to);
            worst = worst.max(p.len());
        }
        println!("JUMP 29 bits: the longest of 20,000 random greedy paths {worst} hops (bound {})", j.bound());
        assert!(worst <= j.bound());
    }
}
