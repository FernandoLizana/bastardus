//! Frontier campaigns: hunt Width(T(G,c)) vs Δ(G) outside trees/cycles.
//!
//! Category C/D research toward proof-complexity lower bounds — NOT Camino B (P≠NP).
//! Resolution is a restricted proof system; these LBs do not settle P vs NP.

use crate::campaign::{run_parallel_jobs, VariantResult};
use crate::graph::{charges_from_mask, cycle, for_each_labeled_tree, path, Graph};
use crate::proof::{prove_unicyclic, tseitin_axioms};
use crate::width_oracle::{has_width_refutation, min_resolution_width};
use rayon::prelude::*;
use serde::Serialize;
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone, Serialize)]
pub struct FrontierHit {
    pub family: String,
    pub n: usize,
    pub delta: usize,
    pub width: usize,
    pub charge_mask: u32,
    pub note: String,
}

#[derive(Clone, Serialize)]
pub struct FrontierReport {
    pub variant: String,
    pub checked: u64,
    pub width_gt_delta: u64,
    pub width_eq_delta: u64,
    pub width_lt_delta: u64,
    pub inconclusive: u64,
    pub elapsed_ms: u128,
    pub hits_gt: Vec<FrontierHit>,
    pub note: String,
}

fn unit_charge(n: usize) -> Vec<u8> {
    let mut c = vec![0u8; n];
    c[0] = 1;
    c
}

fn analyze(g: &Graph, charges: &[u8], family: &str, mask: u32) -> Result<(usize, usize, FrontierHit), String> {
    let delta = g.max_degree();
    if delta > 4 {
        return Err(format!("skip Δ={delta}>4"));
    }
    let axioms = tseitin_axioms(g, charges);
    // Fast path: try width=Δ first (common case W=Δ). Bitmask oracle preferred.
    let (ok_delta, _) = has_width_refutation(&axioms, delta, 25_000);
    let w = if ok_delta {
        delta
    } else {
        let hi = (delta + 3).min(8);
        min_resolution_width(&axioms, hi).ok_or_else(|| format!("no refutation ≤{hi}"))?
    };
    let hit = FrontierHit {
        family: family.into(),
        n: g.n,
        delta,
        width: w,
        charge_mask: mask,
        note: format!("W={w} Δ={delta}"),
    };
    Ok((w, delta, hit))
}

/// Unicyclic: labeled trees on n + chord, unit charge. Skip trees with Δ>3 before chord.
pub fn frontier_unicyclic(n_lo: usize, n_hi: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let jobs: Mutex<Vec<(Graph, String)>> = Mutex::new(Vec::new());
    for n in n_lo..=n_hi {
        for_each_labeled_tree(n, |tree| {
            if tree.max_degree() > 3 {
                return;
            }
            let edges: std::collections::HashSet<(u16, u16)> =
                tree.edges_sorted().into_iter().collect();
            for u in 0..n {
                for v in (u + 1)..n {
                    let e = (u as u16, v as u16);
                    if edges.contains(&e) {
                        continue;
                    }
                    let mut g = tree.clone();
                    g.add_edge(u as u16, v as u16);
                    // Strict Δ≤3 for the extended conjecture surface
                    if g.max_degree() > 3 {
                        continue;
                    }
                    let label = format!("uni_n{n}_chord{u}_{v}");
                    jobs.lock().unwrap().push((g, label));
                }
            }
        });
    }
    let job_vec = jobs.into_inner().unwrap();
    tally_jobs(job_vec, "unicyclic_unit_charge", max_hits, t0)
}

/// Bicyclic: labeled tree + two distinct chords, Δ≤3, unit charge. Hunt W>Δ.
/// For large n, `tree_stride` keeps only every k-th Prüfer tree (k=1 ⇒ all).
pub fn frontier_bicyclic(
    n_lo: usize,
    n_hi: usize,
    max_hits: usize,
    tree_stride: usize,
) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let stride = tree_stride.max(1);
    let jobs: Mutex<Vec<(Graph, String)>> = Mutex::new(Vec::new());
    for n in n_lo..=n_hi {
        let mut tree_idx = 0usize;
        for_each_labeled_tree(n, |tree| {
            let keep = tree_idx % stride == 0;
            tree_idx += 1;
            if !keep {
                return;
            }
            if tree.max_degree() > 3 {
                return;
            }
            let edges: std::collections::HashSet<(u16, u16)> =
                tree.edges_sorted().into_iter().collect();
            let mut non: Vec<(u16, u16)> = Vec::new();
            for u in 0..n {
                for v in (u + 1)..n {
                    let e = (u as u16, v as u16);
                    if !edges.contains(&e) {
                        non.push(e);
                    }
                }
            }
            for i in 0..non.len() {
                for j in (i + 1)..non.len() {
                    let mut g = tree.clone();
                    g.add_edge(non[i].0, non[i].1);
                    g.add_edge(non[j].0, non[j].1);
                    if g.max_degree() > 3 {
                        continue;
                    }
                    if !g.is_bicyclic() {
                        continue;
                    }
                    let label = format!(
                        "bi_n{n}_c{}-{}_{}-{}",
                        non[i].0, non[i].1, non[j].0, non[j].1
                    );
                    jobs.lock().unwrap().push((g, label));
                }
            }
        });
    }
    let job_vec = jobs.into_inner().unwrap();
    tally_jobs(
        job_vec,
        &format!("bicyclic_unit_charge_dleq3_stride{stride}"),
        max_hits,
        t0,
    )
}

/// Bicyclic Δ≤3 with ALL odd charge vectors (small n only).
pub fn frontier_bicyclic_all_odd(n_lo: usize, n_hi: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let mut cleaned: Vec<(Graph, String, Option<u32>)> = Vec::new();
    for n in n_lo..=n_hi {
        assert!(n <= 6, "all-odd bicyclic only for n<=6");
        for_each_labeled_tree(n, |tree| {
            if tree.max_degree() > 3 {
                return;
            }
            let edges: std::collections::HashSet<(u16, u16)> =
                tree.edges_sorted().into_iter().collect();
            let mut non: Vec<(u16, u16)> = Vec::new();
            for u in 0..n {
                for v in (u + 1)..n {
                    let e = (u as u16, v as u16);
                    if !edges.contains(&e) {
                        non.push(e);
                    }
                }
            }
            for i in 0..non.len() {
                for j in (i + 1)..non.len() {
                    let mut g = tree.clone();
                    g.add_edge(non[i].0, non[i].1);
                    g.add_edge(non[j].0, non[j].1);
                    if g.max_degree() > 3 || !g.is_bicyclic() {
                        continue;
                    }
                    let limit = 1u32 << n;
                    for mask in 0..limit {
                        if mask.count_ones() % 2 == 0 {
                            continue;
                        }
                        cleaned.push((
                            g.clone(),
                            format!(
                                "biOdd_n{n}_{}-{}-{}-{}_c{mask}",
                                non[i].0, non[i].1, non[j].0, non[j].1
                            ),
                            Some(mask),
                        ));
                    }
                }
            }
        });
    }
    tally_jobs_charged(cleaned, "bicyclic_all_odd_dleq3", max_hits, t0)
}

/// Tricyclic: tree + three chords, Δ≤3, unit charge. Hunt first W>Δ.
pub fn frontier_tricyclic(
    n_lo: usize,
    n_hi: usize,
    max_hits: usize,
    tree_stride: usize,
) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let stride = tree_stride.max(1);
    let jobs: Mutex<Vec<(Graph, String)>> = Mutex::new(Vec::new());
    for n in n_lo..=n_hi {
        let mut tree_idx = 0usize;
        for_each_labeled_tree(n, |tree| {
            let keep = tree_idx % stride == 0;
            tree_idx += 1;
            if !keep {
                return;
            }
            if tree.max_degree() > 3 {
                return;
            }
            let edges: std::collections::HashSet<(u16, u16)> =
                tree.edges_sorted().into_iter().collect();
            let mut non: Vec<(u16, u16)> = Vec::new();
            for u in 0..n {
                for v in (u + 1)..n {
                    let e = (u as u16, v as u16);
                    if !edges.contains(&e) {
                        non.push(e);
                    }
                }
            }
            let m = non.len();
            for i in 0..m {
                for j in (i + 1)..m {
                    for k in (j + 1)..m {
                        let mut g = tree.clone();
                        g.add_edge(non[i].0, non[i].1);
                        g.add_edge(non[j].0, non[j].1);
                        g.add_edge(non[k].0, non[k].1);
                        if g.max_degree() > 3 || !g.is_tricyclic() {
                            continue;
                        }
                        let label = format!(
                            "tri_n{n}_{}-{}-{}-{}-{}-{}",
                            non[i].0,
                            non[i].1,
                            non[j].0,
                            non[j].1,
                            non[k].0,
                            non[k].1
                        );
                        jobs.lock().unwrap().push((g, label));
                    }
                }
            }
        });
    }
    let job_vec = jobs.into_inner().unwrap();
    tally_jobs(
        job_vec,
        &format!("tricyclic_unit_charge_dleq3_stride{stride}"),
        max_hits,
        t0,
    )
}

/// Constructive unicyclic certificates (not just width oracle).
pub fn campaign_unicyclic_constructive(n_lo: usize, n_hi: usize) -> VariantResult {
    let t0 = Instant::now();
    let mut jobs = Vec::new();
    for n in n_lo..=n_hi {
        for_each_labeled_tree(n, |tree| {
            if tree.max_degree() > 3 {
                return;
            }
            let edges: std::collections::HashSet<(u16, u16)> =
                tree.edges_sorted().into_iter().collect();
            for u in 0..n {
                for v in (u + 1)..n {
                    let e = (u as u16, v as u16);
                    if edges.contains(&e) {
                        continue;
                    }
                    let mut g = tree.clone();
                    g.add_edge(u as u16, v as u16);
                    if g.max_degree() > 3 || !g.is_unicyclic() {
                        continue;
                    }
                    let mut c = vec![0u8; n];
                    c[0] = 1;
                    jobs.push((format!("uniC_n{n}_{u}_{v}"), g, c));
                }
            }
        });
    }
    let (checked, failed, first) = run_parallel_jobs(jobs, prove_unicyclic);
    VariantResult {
        variant: format!("V8_unicyclic_constructive_n{n_lo}..{n_hi}"),
        checked,
        failed,
        elapsed_ms: t0.elapsed().as_millis(),
        note: "Constructive peel+cycle certificates for Width≤Δ on unicyclic Δ≤3.".into(),
        first_failure: first,
    }
}

/// Cycle with one pendant leaf (almost unicyclic / lollipop-lite).
pub fn frontier_cycle_pendant(n_cycle: usize, n_hi_extra: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let mut job_vec = Vec::new();
    for extra in 0..=n_hi_extra {
        // cycle on n_cycle, then path of `extra` pending on vertex 0
        let n = n_cycle + extra;
        let mut g = Graph::with_n(n);
        for i in 0..n_cycle {
            g.add_edge(i as u16, ((i + 1) % n_cycle) as u16);
        }
        for i in 0..extra {
            let a = if i == 0 { 0u16 } else { (n_cycle + i - 1) as u16 };
            let b = (n_cycle + i) as u16;
            g.add_edge(a, b);
        }
        job_vec.push((g, format!("lol_c{n_cycle}_e{extra}")));
    }
    tally_jobs(job_vec, "cycle_pendant_unit_charge", max_hits, t0)
}

/// Two cliques of size k joined by a bridge (barbell), n=2k.
pub fn frontier_barbells(k_lo: usize, k_hi: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let mut job_vec = Vec::new();
    for k in k_lo..=k_hi {
        let n = 2 * k;
        let mut g = Graph::with_n(n);
        for i in 0..k {
            for j in (i + 1)..k {
                g.add_edge(i as u16, j as u16);
            }
        }
        for i in 0..k {
            for j in (i + 1)..k {
                g.add_edge((k + i) as u16, (k + j) as u16);
            }
        }
        g.add_edge(0, k as u16);
        job_vec.push((g, format!("barbell_k{k}")));
    }
    tally_jobs(job_vec, "barbell_unit_charge", max_hits, t0)
}

/// Small complete graphs Kn (n≥3) with odd charge — dense Δ=n-1.
pub fn frontier_completes(n_lo: usize, n_hi: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let mut job_vec = Vec::new();
    for n in n_lo..=n_hi {
        let mut g = Graph::with_n(n);
        for i in 0..n {
            for j in (i + 1)..n {
                g.add_edge(i as u16, j as u16);
            }
        }
        job_vec.push((g, format!("K{n}")));
    }
    tally_jobs(job_vec, "complete_unit_charge", max_hits, t0)
}

/// Parallel edges between two apexes (series-parallel), unit + all odd charges for tiny m.
pub fn frontier_diamonds(m_lo: usize, m_hi: usize, max_hits: usize) -> (VariantResult, FrontierReport) {
    let t0 = Instant::now();
    let mut cleaned: Vec<(Graph, String, Option<u32>)> = Vec::new();
    for m in m_lo..=m_hi {
        let n = 2 + m;
        let mut g = Graph::with_n(n);
        for i in 0..m {
            let mid = (2 + i) as u16;
            g.add_edge(0, mid);
            g.add_edge(1, mid);
        }
        if m <= 5 {
            let limit = 1u32 << n;
            for mask in 0..limit {
                if mask.count_ones() % 2 == 0 {
                    continue;
                }
                cleaned.push((g.clone(), format!("diamond_m{m}_c{mask}"), Some(mask)));
            }
        } else {
            cleaned.push((g, format!("diamond_m{m}"), Some(1)));
        }
    }
    tally_jobs_charged(cleaned, "diamond_parallel_odd_charges", max_hits, t0)
}

fn tally_jobs(
    job_vec: Vec<(Graph, String)>,
    variant: &str,
    max_hits: usize,
    t0: Instant,
) -> (VariantResult, FrontierReport) {
    let charged: Vec<(Graph, String, Option<u32>)> = job_vec
        .into_iter()
        .map(|(g, l)| (g, l, Some(1u32)))
        .collect();
    tally_jobs_charged(charged, variant, max_hits, t0)
}

fn tally_jobs_charged(
    job_vec: Vec<(Graph, String, Option<u32>)>,
    variant: &str,
    max_hits: usize,
    t0: Instant,
) -> (VariantResult, FrontierReport) {
    let gt = Mutex::new(0u64);
    let eq = Mutex::new(0u64);
    let lt = Mutex::new(0u64);
    let inc = Mutex::new(0u64);
    let checked = Mutex::new(0u64);
    let hits: Mutex<Vec<FrontierHit>> = Mutex::new(Vec::new());

    job_vec.into_par_iter().for_each(|(g, label, mask_opt)| {
        let mask = mask_opt.unwrap_or(1);
        let charges = if mask == 1 {
            unit_charge(g.n)
        } else {
            charges_from_mask(mask, g.n)
        };
        *checked.lock().unwrap() += 1;
        match analyze(&g, &charges, &label, mask) {
            Ok((w, delta, hit)) => {
                if w > delta {
                    *gt.lock().unwrap() += 1;
                    let mut h = hits.lock().unwrap();
                    if h.len() < max_hits {
                        h.push(hit);
                    }
                } else if w == delta {
                    *eq.lock().unwrap() += 1;
                } else {
                    *lt.lock().unwrap() += 1;
                    let mut h = hits.lock().unwrap();
                    if h.len() < max_hits {
                        h.push(hit);
                    }
                }
            }
            Err(_) => {
                *inc.lock().unwrap() += 1;
            }
        }
    });

    let checked_n = *checked.lock().unwrap();
    let gt_n = *gt.lock().unwrap();
    let eq_n = *eq.lock().unwrap();
    let lt_n = *lt.lock().unwrap();
    let inc_n = *inc.lock().unwrap();
    let hits_gt = hits.into_inner().unwrap();
    let first = hits_gt.first().map(|h| format!("{} W={} Δ={}", h.family, h.width, h.delta));

    let fr = FrontierReport {
        variant: variant.into(),
        checked: checked_n,
        width_gt_delta: gt_n,
        width_eq_delta: eq_n,
        width_lt_delta: lt_n,
        inconclusive: inc_n,
        elapsed_ms: t0.elapsed().as_millis(),
        hits_gt,
        note: "Resolution width lower bounds on Tseitin; restricted system ≠ P≠NP.".into(),
    };
    let vr = VariantResult {
        variant: format!("FRONTIER_{variant}"),
        checked: checked_n,
        failed: lt_n, // anomalous Width < Δ under odd connected — investigate
        elapsed_ms: fr.elapsed_ms,
        note: format!(
            "W>Δ={gt_n} W=Δ={eq_n} W<Δ={lt_n} inconclusive={inc_n}"
        ),
        first_failure: first,
    };
    (vr, fr)
}

/// Smoke sanity: known cycle Width=2=Δ and a path Width=Δ.
pub fn frontier_sanity() -> VariantResult {
    let t0 = Instant::now();
    let g = cycle(5);
    let c = unit_charge(5);
    let axioms = tseitin_axioms(&g, &c);
    let w = min_resolution_width(&axioms, 4).unwrap_or(999);
    let ok = w == 2;
    let g2 = path(6);
    let axioms2 = tseitin_axioms(&g2, &unit_charge(6));
    let w2 = min_resolution_width(&axioms2, 4).unwrap_or(999);
    let ok2 = w2 == 2;
    VariantResult {
        variant: "FRONTIER_sanity_cycle_path".into(),
        checked: 2,
        failed: if ok && ok2 { 0 } else { 1 },
        elapsed_ms: t0.elapsed().as_millis(),
        note: format!("C5 W={w} (expect 2); P6 W={w2} (expect 2)"),
        first_failure: if ok && ok2 {
            None
        } else {
            Some("sanity failed".into())
        },
    }
}
