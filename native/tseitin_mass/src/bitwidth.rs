//! Bitmask resolution-width oracle (CPU). Vars ≤ 32 → clause = (pos_bits, neg_bits).

use crate::clause::Clause;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct BitClause {
    pub pos: u32,
    pub neg: u32,
}

impl BitClause {
    #[inline]
    pub fn width(self) -> u32 {
        (self.pos | self.neg).count_ones()
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.pos == 0 && self.neg == 0
    }

    #[inline]
    pub fn is_tautology(self) -> bool {
        self.pos & self.neg != 0
    }

    pub fn from_lits(lits: &[i16]) -> Option<Self> {
        let mut pos = 0u32;
        let mut neg = 0u32;
        for &lit in lits {
            let v = lit.unsigned_abs() as u32;
            if v == 0 || v > 32 {
                return None;
            }
            let bit = 1u32 << (v - 1);
            if lit > 0 {
                pos |= bit;
            } else {
                neg |= bit;
            }
        }
        let c = Self { pos, neg };
        if c.is_tautology() {
            None
        } else {
            Some(c)
        }
    }

    /// Resolve on exactly one complementary variable; None if 0 or ≥2 pivots.
    pub fn resolve(self, other: Self) -> Option<Self> {
        let piv_pos = self.pos & other.neg;
        let piv_neg = self.neg & other.pos;
        let piv = piv_pos | piv_neg;
        if piv.count_ones() != 1 {
            return None;
        }
        let out = Self {
            pos: (self.pos | other.pos) & !piv,
            neg: (self.neg | other.neg) & !piv,
        };
        if out.is_tautology() {
            None
        } else {
            Some(out)
        }
    }
}

pub fn clauses_to_bits(axioms: &[Clause]) -> Option<Vec<BitClause>> {
    let mut out = Vec::with_capacity(axioms.len());
    for c in axioms {
        out.push(BitClause::from_lits(c)?);
    }
    Some(out)
}

/// Width-bounded saturation using bit clauses. Very fast for Tseitin (few vars).
pub fn has_width_refutation_bits(
    axioms: &[BitClause],
    width: usize,
    max_clauses: usize,
) -> bool {
    use std::collections::{HashSet, VecDeque};

    let mut set: HashSet<(u32, u32)> = HashSet::new();
    let mut list: Vec<BitClause> = Vec::new();
    let mut pending: VecDeque<usize> = VecDeque::new();

    let mut add = |c: BitClause, set: &mut HashSet<(u32, u32)>, list: &mut Vec<BitClause>, pending: &mut VecDeque<usize>| -> bool {
        if c.width() as usize > width || c.is_tautology() {
            return false;
        }
        let key = (c.pos, c.neg);
        if !set.insert(key) {
            return false;
        }
        let i = list.len();
        list.push(c);
        pending.push_back(i);
        if c.is_empty() {
            return true;
        }
        false
    };

    for &a in axioms {
        if a.is_empty() {
            return true;
        }
        if add(a, &mut set, &mut list, &mut pending) {
            return true;
        }
    }

    while let Some(i) = pending.pop_front() {
        if list.len() > max_clauses {
            return false;
        }
        let a = list[i];
        let n = list.len();
        for j in 0..n {
            if i == j {
                continue;
            }
            if let Some(r) = a.resolve(list[j]) {
                if r.width() as usize > width {
                    continue;
                }
                if add(r, &mut set, &mut list, &mut pending) {
                    return true;
                }
            }
        }
    }
    false
}

pub fn min_width_bits(axioms: &[BitClause], hi: usize) -> Option<usize> {
    let aw = axioms.iter().map(|c| c.width() as usize).max().unwrap_or(0);
    if axioms.iter().any(|c| c.is_empty()) {
        return Some(0);
    }
    for w in aw..=hi {
        if has_width_refutation_bits(axioms, w, 25_000) {
            return Some(w);
        }
    }
    None
}
