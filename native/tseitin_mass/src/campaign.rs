//! Parallel campaign runners over combinatorial families + Aut orbits.

use crate::graph::{
    charges_from_mask, cycle, cycle_odd_charge_orbit_reps, for_each_labeled_tree,
    odd_charge_orbit_reps, path, path_odd_charge_orbit_reps, star, star_odd_charge_orbit_reps,
    Graph,
};
use crate::proof::{prove_cycle, prove_tree};
use rayon::prelude::*;
use serde::Serialize;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

#[derive(Clone, Serialize)]
pub struct VariantResult {
    pub variant: String,
    pub checked: u64,
    pub failed: u64,
    pub elapsed_ms: u128,
    pub note: String,
    pub first_failure: Option<String>,
}

pub(crate) fn run_parallel_jobs<F>(jobs: Vec<(String, Graph, Vec<u8>)>, prove: F) -> (u64, u64, Option<String>)
where
    F: Fn(&Graph, &[u8]) -> Result<(), String> + Sync,
{
    let failed = AtomicU64::new(0);
    let checked = AtomicU64::new(0);
    let first: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

    jobs.into_par_iter().for_each(|(label, g, c)| {
        checked.fetch_add(1, Ordering::Relaxed);
        if let Err(e) = prove(&g, &c) {
            failed.fetch_add(1, Ordering::Relaxed);
            let mut lock = first.lock().unwrap();
            if lock.is_none() {
                *lock = Some(format!("{label}: {e}"));
            }
        }
    });

    (
        checked.load(Ordering::Relaxed),
        failed.load(Ordering::Relaxed),
        first.into_inner().unwrap(),
    )
}

/// V1a: all labeled trees n∈[n_lo,n_hi], ALL odd charges (no Aut — labeled redundancy OK).
pub fn campaign_trees_all_odd(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        assert!(n <= 20);
        let mut trees = Vec::new();
        for_each_labeled_tree(n, |g| trees.push(g));
        let limit = 1u32 << n;
        for (ti, g) in trees.into_iter().enumerate() {
            for mask in 0..limit {
                if mask.count_ones() % 2 == 0 {
                    continue;
                }
                jobs.push((
                    format!("tree_n{n}_t{ti}_c{mask}"),
                    g.clone(),
                    charges_from_mask(mask, n),
                ));
            }
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V1_trees_labeled_allOddCharges_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Claim: Width=Δ. Enumerates all labeled trees × all odd GF(2) charges (no Aut filter)."
            .into(),
        first_failure: first,
    }
}

/// V1b: small n only — Aut(G)-orbit representatives of odd charges.
pub fn campaign_trees(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let mut trees = Vec::new();
        for_each_labeled_tree(n, |g| trees.push(g));
        for (ti, g) in trees.into_iter().enumerate() {
            let reps = odd_charge_orbit_reps(&g);
            for mask in reps {
                let c = charges_from_mask(mask, n);
                jobs.push((format!("tree_n{n}_t{ti}_c{mask}"), g.clone(), c));
            }
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V1b_trees_labeled_AutChargeOrbits_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Group: Aut(G) on GF(2)^V. Use only for tiny n (Aut search is n!-ish)."
            .into(),
        first_failure: first,
    }
}

/// V2: paths n∈[n_lo,n_hi], all Aut-orbit odd charges (path Aut ≅ Z2).
pub fn campaign_paths(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let g = path(n);
        for mask in path_odd_charge_orbit_reps(n) {
            jobs.push((
                format!("path_n{n}_c{mask}"),
                g.clone(),
                charges_from_mask(mask, n),
            ));
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V2_paths_Z2ChargeOrbits_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Paths ⊆ trees ⇒ Width=Δ (=2 for n≥3). Group ℤ₂ (reversal).".into(),
        first_failure: first,
    }
}

/// V3: stars — Δ=n-1, Aut ≅ S_{n-1} on leaves; orbit reps of odd charges.
pub fn campaign_stars(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let g = star(n);
        for mask in star_odd_charge_orbit_reps(n) {
            jobs.push((
                format!("star_n{n}_c{mask}"),
                g.clone(),
                charges_from_mask(mask, n),
            ));
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V3_stars_SymChargeOrbits_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Stars: Width=Δ=n-1. Group S_{n-1} via sorted leaf-charge canonicalization.".into(),
        first_failure: first,
    }
}

/// V4: cycles — Width=2 via certified saturation; Dihedral charge orbits.
pub fn campaign_cycles(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let g = cycle(n);
        for mask in cycle_odd_charge_orbit_reps(n) {
            jobs.push((
                format!("cycle_n{n}_c{mask}"),
                g.clone(),
                charges_from_mask(mask, n),
            ));
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_cycle);
    VariantResult {
        variant: format!("V4_cycles_DihedralChargeOrbits_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Claim: Width=Δ=2. Group: D_n acting on GF(2)^n charges.".into(),
        first_failure: first,
    }
}

/// V5: single-odd-charge on all labeled trees (smaller than full orbits; sanity flood).
pub fn campaign_trees_unit_charge(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let mut trees = Vec::new();
        for_each_labeled_tree(n, |g| trees.push(g));
        for (ti, g) in trees.into_iter().enumerate() {
            // one job per vertex placement of the single 1 (Aut would collapse; keep all for stress)
            for v in 0..n {
                let mut c = vec![0u8; n];
                c[v] = 1;
                jobs.push((format!("treeUC_n{n}_t{ti}_v{v}"), g.clone(), c));
            }
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V5_trees_unitChargeFlood_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "All labeled trees × all single-1 charge positions.".into(),
        first_failure: first,
    }
}

/// V6: binary weight-3 odd charges on paths (odd weight always).
pub fn campaign_paths_weight3(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        let g = path(n);
        for i in 0..n {
            for j in (i + 1)..n {
                for k in (j + 1)..n {
                    let mut c = vec![0u8; n];
                    c[i] = 1;
                    c[j] = 1;
                    c[k] = 1;
                    jobs.push((format!("pathW3_{n}_{i}_{j}_{k}"), g.clone(), c));
                }
            }
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V6_paths_weight3_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "All weight-3 charge patterns on paths.".into(),
        first_failure: first,
    }
}

/// V7: caterpillars = path spine + pending leaves (Δ≥3 variants).
pub fn campaign_caterpillars(spine: usize, max_pending: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    let base = max_pending + 1;
    let total = (base as u64).pow(spine as u32);
    for code in 0..total {
        let mut pending = vec![0usize; spine];
        let mut t = code;
        let mut n = spine;
        for i in 0..spine {
            pending[i] = (t % base as u64) as usize;
            t /= base as u64;
            n += pending[i];
        }
        let mut g = Graph::with_n(n);
        for i in 0..spine.saturating_sub(1) {
            g.add_edge(i as u16, (i + 1) as u16);
        }
        let mut next = spine as u16;
        for i in 0..spine {
            for _ in 0..pending[i] {
                g.add_edge(i as u16, next);
                next += 1;
            }
        }
        if n <= 8 {
            let limit = 1u32 << n;
            for mask in 0..limit {
                if mask.count_ones() % 2 == 0 {
                    continue;
                }
                jobs.push((
                    format!("cat_s{spine}_code{code}_c{mask}"),
                    g.clone(),
                    charges_from_mask(mask, n),
                ));
            }
        } else {
            let mut c = vec![0u8; n];
            c[0] = 1;
            jobs.push((format!("cat_s{spine}_code{code}"), g, c));
        }
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_tree);
    VariantResult {
        variant: format!("V7_caterpillars_spine{spine}_pend≤{max_pending}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Caterpillar trees (path + pending). Still trees ⇒ Width=Δ.".into(),
        first_failure: first,
    }
}
