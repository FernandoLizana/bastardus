//! Compact clause algebra for resolution (signed literals as i16).

use std::collections::{HashMap, HashSet};

pub type Lit = i16;
pub type Clause = Vec<Lit>;

#[inline]
pub fn norm(mut c: Clause) -> Option<Clause> {
    c.sort_unstable();
    c.dedup();
    let set: HashSet<Lit> = c.iter().copied().collect();
    for &x in &c {
        if x != 0 && set.contains(&-x) {
            return None; // tautology
        }
    }
    Some(c)
}

#[inline]
pub fn resolve(a: &[Lit], b: &[Lit]) -> Option<Clause> {
    let sa: HashSet<Lit> = a.iter().copied().collect();
    let sb: HashSet<Lit> = b.iter().copied().collect();
    let pivots: Vec<Lit> = sa.iter().copied().filter(|x| sb.contains(&-x)).collect();
    // unique pivot variable
    let mut vars: HashSet<i16> = HashSet::new();
    for p in &pivots {
        vars.insert(p.abs());
    }
    if vars.len() != 1 {
        return None;
    }
    let p = pivots[0];
    let out: Clause = sa
        .union(&sb)
        .copied()
        .filter(|&x| x != p && x != -p)
        .collect();
    norm(out)
}

/// XOR(lits) = charge  → CNF clauses of width |lits|.
pub fn xor_cnf(lits: &[Lit], charge: u8) -> Vec<Clause> {
    let k = lits.len();
    if k == 0 {
        return if charge % 2 == 1 {
            vec![vec![]]
        } else {
            vec![]
        };
    }
    let mut out = Vec::with_capacity(1 << (k.saturating_sub(1)));
    for mask in 0..(1u32 << k) {
        let parity = mask.count_ones() % 2;
        if parity == charge as u32 % 2 {
            continue;
        }
        let mut clause = Vec::with_capacity(k);
        for i in 0..k {
            let bit = (mask >> i) & 1;
            let lit = lits[i];
            clause.push(if bit == 0 { lit } else { -lit });
        }
        if let Some(n) = norm(clause) {
            out.push(n);
        }
    }
    out
}

pub struct ProofBuilder {
    pub delta: usize,
    pub axioms: Vec<Clause>,
    pub steps: Vec<Clause>,
    pub parents: Vec<Option<(usize, usize)>>,
    pub index: HashMap<Clause, usize>,
}

impl ProofBuilder {
    pub fn new(axioms: Vec<Clause>, delta: usize) -> Self {
        let mut b = Self {
            delta,
            axioms: axioms.clone(),
            steps: Vec::new(),
            parents: Vec::new(),
            index: HashMap::new(),
        };
        for a in axioms {
            let _ = b.put(a, None);
        }
        b
    }

    pub fn put(&mut self, clause: Clause, parent: Option<(usize, usize)>) -> Result<usize, String> {
        if let Some(&i) = self.index.get(&clause) {
            return Ok(i);
        }
        if clause.len() > self.delta {
            return Err(format!(
                "clause width {} > Δ={}: {:?}",
                clause.len(),
                self.delta,
                clause
            ));
        }
        let i = self.steps.len();
        self.index.insert(clause.clone(), i);
        self.steps.push(clause);
        self.parents.push(parent);
        Ok(i)
    }

    pub fn resolve_to(&mut self, j: usize, k: usize) -> Result<usize, String> {
        let r = resolve(&self.steps[j], &self.steps[k])
            .ok_or_else(|| format!("cannot resolve {} & {}", j, k))?;
        self.put(r, Some((j, k)))
    }

    pub fn verify(&self) -> Result<(), String> {
        let axiom_set: HashSet<&Clause> = self.axioms.iter().collect();
        let mut mw = 0usize;
        for (i, c) in self.steps.iter().enumerate() {
            mw = mw.max(c.len());
            if c.len() > self.delta {
                return Err(format!("step {i} width {} > Δ", c.len()));
            }
            match self.parents[i] {
                None => {
                    if !axiom_set.contains(c) {
                        return Err(format!("step {i} fake axiom {:?}", c));
                    }
                }
                Some((j, k)) => {
                    if j >= i || k >= i {
                        return Err(format!("bad parents at {i}"));
                    }
                    let r = resolve(&self.steps[j], &self.steps[k]);
                    if r.as_ref() != Some(c) {
                        return Err(format!("resolve mismatch at {i}"));
                    }
                }
            }
        }
        if !self.steps.iter().any(|c| c.is_empty()) {
            return Err("empty clause missing".into());
        }
        if mw > self.delta {
            return Err(format!("max_width {mw} > Δ"));
        }
        Ok(())
    }
}
