//! Width oracle: prefer bitmask path (≤32 vars), else classic HashSet path.

use crate::bitwidth::{clauses_to_bits, has_width_refutation_bits, min_width_bits};
use crate::clause::{resolve, Clause};
use std::collections::{HashMap, HashSet, VecDeque};

pub fn has_width_refutation(axioms: &[Clause], width: usize, max_clauses: usize) -> (bool, usize) {
    if let Some(bits) = clauses_to_bits(axioms) {
        let ok = has_width_refutation_bits(&bits, width, max_clauses);
        return (ok, 0);
    }

    let mut clauses: HashSet<Clause> = HashSet::new();
    let mut by_lit: HashMap<i16, HashSet<Clause>> = HashMap::new();
    let mut pending: VecDeque<Clause> = VecDeque::new();

    let add = |c: Clause,
               clauses: &mut HashSet<Clause>,
               by_lit: &mut HashMap<i16, HashSet<Clause>>,
               pending: &mut VecDeque<Clause>| {
        if clauses.contains(&c) {
            return false;
        }
        for &lit in &c {
            by_lit.entry(lit).or_default().insert(c.clone());
        }
        clauses.insert(c.clone());
        pending.push_back(c);
        true
    };

    for a in axioms {
        if a.is_empty() {
            return (true, 1);
        }
        if a.len() <= width {
            add(a.clone(), &mut clauses, &mut by_lit, &mut pending);
        }
    }
    if clauses.iter().any(|c| c.is_empty()) {
        return (true, clauses.len());
    }

    while let Some(a) = pending.pop_front() {
        if clauses.len() > max_clauses {
            return (false, clauses.len());
        }
        let mut partners: HashSet<Clause> = HashSet::new();
        for &lit in &a {
            if let Some(set) = by_lit.get(&-lit) {
                for b in set {
                    partners.insert(b.clone());
                }
            }
        }
        for b in partners {
            if a == b {
                continue;
            }
            if let Some(r) = resolve(&a, &b) {
                if r.len() > width {
                    continue;
                }
                let empty = r.is_empty();
                if add(r, &mut clauses, &mut by_lit, &mut pending) && empty {
                    return (true, clauses.len());
                }
            }
        }
    }
    (false, clauses.len())
}

pub fn min_resolution_width(axioms: &[Clause], hi: usize) -> Option<usize> {
    if let Some(bits) = clauses_to_bits(axioms) {
        return min_width_bits(&bits, hi);
    }
    let axiom_w = axioms.iter().map(|c| c.len()).max().unwrap_or(0);
    if axioms.iter().any(|c| c.is_empty()) {
        return Some(0);
    }
    for w in axiom_w..=hi {
        let (ok, _) = has_width_refutation(axioms, w, 25_000);
        if ok {
            return Some(w);
        }
    }
    None
}
