//! Constructive Tseitin width proofs (trees / cycles) — low-level, no heap thrash.

use crate::clause::{xor_cnf, Clause, Lit, ProofBuilder};
use crate::graph::{edge_var_map, Graph};
use std::collections::HashMap;

fn incident_lits(g: &Graph, e_index: &HashMap<(u16, u16), Lit>, v: usize) -> Vec<Lit> {
    let mut nbrs: Vec<u16> = g.adj[v].clone();
    nbrs.sort_unstable();
    nbrs.into_iter()
        .map(|u| {
            let a = (v as u16).min(u);
            let b = (v as u16).max(u);
            e_index[&(a, b)]
        })
        .collect()
}

fn xor_at(g: &Graph, e_index: &HashMap<(u16, u16), Lit>, v: usize, charge: u8) -> Vec<Clause> {
    xor_cnf(&incident_lits(g, e_index, v), charge)
}

fn all_axioms(g: &Graph, charges: &[u8], e_index: &HashMap<(u16, u16), Lit>) -> Vec<Clause> {
    let mut axioms = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for v in 0..g.n {
        for c in xor_at(g, e_index, v, charges[v]) {
            if seen.insert(c.clone()) {
                axioms.push(c);
            }
        }
    }
    axioms
}

/// Public Tseitin CNF axioms for connected graph + charges.
pub fn tseitin_axioms(g: &Graph, charges: &[u8]) -> Vec<Clause> {
    let e_index = edge_var_map(g);
    all_axioms(g, charges, &e_index)
}

fn derive_by_unit(builder: &mut ProofBuilder, clauses: &[Clause], unit: &Clause) -> Result<(), String> {
    if unit.len() != 1 {
        return Err("need unit".into());
    }
    let lit = unit[0];
    let u_i = *builder
        .index
        .get(unit)
        .ok_or_else(|| format!("unit missing: {:?}", unit))?;
    for c in clauses {
        if c.contains(&-lit) {
            let ci = *builder
                .index
                .get(c)
                .ok_or_else(|| format!("clause missing: {:?}", c))?;
            builder.resolve_to(ci, u_i)?;
        }
    }
    Ok(())
}

/// Inductive leaf-peeling: Width ≤ Δ for trees with odd total charge.
pub fn prove_tree(g: &Graph, charges: &[u8]) -> Result<(), String> {
    if !g.is_tree() {
        return Err("not a tree".into());
    }
    let odd: u32 = charges.iter().map(|&c| c as u32 % 2).sum();
    if odd % 2 == 0 {
        return Err("even charge (SAT)".into());
    }
    let e_index = edge_var_map(g);
    let delta = g.max_degree();

    if g.n == 1 {
        let axioms = vec![vec![]];
        let b = ProofBuilder::new(axioms, 0);
        return b.verify();
    }

    let axioms = all_axioms(g, charges, &e_index);
    let mut builder = ProofBuilder::new(axioms, delta.max(1));

    // Working copy: adjacency + charges
    let mut adj = g.adj.clone();
    let mut alive = vec![true; g.n];
    let mut c = charges.iter().map(|&x| x % 2).collect::<Vec<u8>>();
    let mut alive_count = g.n;

    while alive_count >= 2 {
        let leaf = (0..g.n)
            .find(|&v| alive[v] && adj[v].iter().filter(|&&u| alive[u as usize]).count() == 1)
            .ok_or("no leaf")?;
        let nbr = *adj[leaf]
            .iter()
            .find(|&&u| alive[u as usize])
            .ok_or("leaf nbr")?;
        let a = (leaf as u16).min(nbr);
        let b = (leaf as u16).max(nbr);
        let var = e_index[&(a, b)];
        let chi = c[leaf];
        let unit: Clause = if chi == 1 { vec![var] } else { vec![-var] };
        if !builder.index.contains_key(&unit) {
            return Err(format!("leaf unit missing from proof: {:?}", unit));
        }

        if alive_count == 2 {
            let other: Clause = if c[nbr as usize] == 1 {
                vec![var]
            } else {
                vec![-var]
            };
            if !builder.index.contains_key(&other) {
                return Err(format!("final unit missing: {:?}", other));
            }
            if unit == other {
                return Err("parity invariant broken".into());
            }
            let ui = builder.index[&unit];
            let oi = builder.index[&other];
            builder.resolve_to(ui, oi)?;
            return builder.verify();
        }

        // Neighbor XOR under current alive graph
        let mut nbr_lits = Vec::new();
        let mut nbrs: Vec<u16> = adj[nbr as usize]
            .iter()
            .copied()
            .filter(|&u| alive[u as usize])
            .collect();
        nbrs.sort_unstable();
        for u in nbrs {
            let aa = nbr.min(u);
            let bb = nbr.max(u);
            nbr_lits.push(e_index[&(aa, bb)]);
        }
        let xor_nbr = xor_cnf(&nbr_lits, c[nbr as usize]);
        for cl in &xor_nbr {
            if !builder.index.contains_key(cl) {
                return Err(format!(
                    "expected XOR clause absent (induction invariant): {:?}",
                    cl
                ));
            }
        }
        derive_by_unit(&mut builder, &xor_nbr, &unit)?;

        c[nbr as usize] = (c[nbr as usize] + chi) % 2;
        alive[leaf] = false;
        alive_count -= 1;
        // scrub leaf from nbr adjacency (optional; filtered by alive)
    }
    Err("unreachable".into())
}

/// Width-2 saturation certificate for cycles with odd charge.
pub fn prove_cycle(g: &Graph, charges: &[u8]) -> Result<(), String> {
    if !g.is_cycle() {
        return Err("not a cycle".into());
    }
    let odd: u32 = charges.iter().map(|&c| c as u32 % 2).sum();
    if odd % 2 == 0 {
        return Err("even charge (SAT)".into());
    }
    let e_index = edge_var_map(g);
    let axioms = all_axioms(g, charges, &e_index);
    let mut builder = ProofBuilder::new(axioms, 2);
    let mut pending: Vec<usize> = (0..builder.steps.len()).collect();
    let mut seen_pair = std::collections::HashSet::new();

    while let Some(i) = pending.pop() {
        let nsteps = builder.steps.len();
        for j in 0..nsteps {
            let (a, b) = if i < j { (i, j) } else { (j, i) };
            if a == b || !seen_pair.insert((a, b)) {
                continue;
            }
            if let Some(r) = crate::clause::resolve(&builder.steps[a], &builder.steps[b]) {
                if r.len() > 2 {
                    continue;
                }
                if !builder.index.contains_key(&r) {
                    let empty = r.is_empty();
                    let idx = builder.put(r, Some((a, b)))?;
                    pending.push(idx);
                    if empty {
                        return builder.verify();
                    }
                }
            }
        }
    }
    Err("cycle width-2 saturation failed".into())
}

/// Unicyclic: peel pending trees then width-2-saturate residual cycle. Width ≤ Δ.
pub fn prove_unicyclic(g: &Graph, charges: &[u8]) -> Result<(), String> {
    if !g.is_unicyclic() {
        return Err("not unicyclic".into());
    }
    let odd: u32 = charges.iter().map(|&c| c as u32 % 2).sum();
    if odd % 2 == 0 {
        return Err("even charge (SAT)".into());
    }
    let e_index = edge_var_map(g);
    let delta = g.max_degree().max(2);
    let axioms = all_axioms(g, charges, &e_index);
    let mut builder = ProofBuilder::new(axioms, delta);

    let adj = g.adj.clone();
    let mut alive = vec![true; g.n];
    let mut c: Vec<u8> = charges.iter().map(|&x| x % 2).collect();
    let mut alive_count = g.n;

    loop {
        let leaf = (0..g.n).find(|&v| {
            alive[v] && adj[v].iter().filter(|&&u| alive[u as usize]).count() == 1
        });
        let Some(leaf) = leaf else {
            break;
        };
        let nbr = *adj[leaf]
            .iter()
            .find(|&&u| alive[u as usize])
            .ok_or("leaf nbr")?;
        let aa = (leaf as u16).min(nbr);
        let bb = (leaf as u16).max(nbr);
        let var = e_index[&(aa, bb)];
        let chi = c[leaf];
        let unit: Clause = if chi == 1 { vec![var] } else { vec![-var] };
        if !builder.index.contains_key(&unit) {
            return Err(format!("leaf unit missing: {:?}", unit));
        }
        if alive_count == 2 {
            let other: Clause = if c[nbr as usize] == 1 {
                vec![var]
            } else {
                vec![-var]
            };
            if unit == other {
                return Err("parity broken".into());
            }
            let ui = builder.index[&unit];
            let oi = *builder
                .index
                .get(&other)
                .ok_or("other unit missing")?;
            builder.resolve_to(ui, oi)?;
            return builder.verify();
        }
        let mut nbrs: Vec<u16> = adj[nbr as usize]
            .iter()
            .copied()
            .filter(|&u| alive[u as usize])
            .collect();
        nbrs.sort_unstable();
        let nbr_lits: Vec<Lit> = nbrs
            .iter()
            .map(|&u| {
                let a = nbr.min(u);
                let b = nbr.max(u);
                e_index[&(a, b)]
            })
            .collect();
        let xor_nbr = xor_cnf(&nbr_lits, c[nbr as usize]);
        for cl in &xor_nbr {
            if !builder.index.contains_key(cl) {
                return Err(format!("XOR missing: {:?}", cl));
            }
        }
        derive_by_unit(&mut builder, &xor_nbr, &unit)?;
        c[nbr as usize] = (c[nbr as usize] + chi) % 2;
        alive[leaf] = false;
        alive_count -= 1;
    }

    // Residual must be a cycle: every alive vertex degree 2 among alive.
    for v in 0..g.n {
        if !alive[v] {
            continue;
        }
        let d = adj[v].iter().filter(|&&u| alive[u as usize]).count();
        if d != 2 {
            return Err(format!("residual not cycle: deg[{v}]={d}"));
        }
    }

    // Ensure residual XORs present, then saturate at width 2 among len≤2 clauses.
    for v in 0..g.n {
        if !alive[v] {
            continue;
        }
        let mut nbrs: Vec<u16> = adj[v]
            .iter()
            .copied()
            .filter(|&u| alive[u as usize])
            .collect();
        nbrs.sort_unstable();
        let lits: Vec<Lit> = nbrs
            .iter()
            .map(|&u| {
                let a = (v as u16).min(u);
                let b = (v as u16).max(u);
                e_index[&(a, b)]
            })
            .collect();
        for cl in xor_cnf(&lits, c[v]) {
            if !builder.index.contains_key(&cl) {
                return Err(format!("residual XOR missing: {:?}", cl));
            }
        }
    }

    let mut pending: Vec<usize> = builder
        .steps
        .iter()
        .enumerate()
        .filter(|(_, cl)| cl.len() <= 2)
        .map(|(i, _)| i)
        .collect();
    let mut seen_pair = std::collections::HashSet::new();
    while let Some(i) = pending.pop() {
        if builder.steps[i].len() > 2 {
            continue;
        }
        let partners: Vec<usize> = builder
            .steps
            .iter()
            .enumerate()
            .filter(|(_, cl)| cl.len() <= 2)
            .map(|(j, _)| j)
            .collect();
        for j in partners {
            let (a, b) = if i < j { (i, j) } else { (j, i) };
            if a == b || !seen_pair.insert((a, b)) {
                continue;
            }
            if let Some(r) = crate::clause::resolve(&builder.steps[a], &builder.steps[b]) {
                if r.len() > 2 {
                    continue;
                }
                if !builder.index.contains_key(&r) {
                    let empty = r.is_empty();
                    let idx = builder.put(r, Some((a, b)))?;
                    pending.push(idx);
                    if empty {
                        return builder.verify();
                    }
                }
            }
        }
    }
    Err("unicyclic saturation failed".into())
}

/// Fast tree check without keeping full parent certificate (same algorithm, lighter verify).
pub fn prove_tree_fast(g: &Graph, charges: &[u8]) -> Result<(), String> {
    prove_tree(g, charges)
}
