mod bitwidth;
mod campaign;
mod clause;
mod frontier;
mod graph;
mod pool;
mod proof;
mod width_oracle;

use campaign::*;
use frontier::*;
use serde::Serialize;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

#[derive(Serialize)]
struct Report {
    evidence_level: &'static str,
    claim_type: &'static str,
    disclaimer: &'static str,
    profile: String,
    elapsed_ms: u128,
    variants: Vec<VariantResult>,
    frontier: Vec<FrontierReport>,
    total_checked: u64,
    total_failed: u64,
    camino_b_status: &'static str,
    compute: String,
}

fn main() {
    let mut profile = "laptop".to_string();
    let mut out_dir = PathBuf::from("../../reports/discovery");
    let mut threads = pool::default_thread_count();
    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--profile" => {
                i += 1;
                profile = args.get(i).cloned().unwrap_or(profile);
            }
            "--out-dir" => {
                i += 1;
                if let Some(p) = args.get(i) {
                    out_dir = PathBuf::from(p);
                }
            }
            "--threads" => {
                i += 1;
                threads = args
                    .get(i)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(threads);
            }
            "--gpu" | "--cpu-only" => {
                // GPU batches live in Python OpenCL helper (wgpu needs MSVC dlltool on this host).
                eprintln!(
                    "note: native GPU via wgpu unavailable on GNU rustc without dlltool; \
                     use: python -m backend.proof_complexity.gpu_width_opencl"
                );
            }
            "-h" | "--help" => {
                eprintln!(
                    "tseitin_mass --profile smoke|laptop|heavy|frontier|classify [--threads N] [--out-dir DIR]"
                );
                eprintln!("  default threads = logical_cpus-2 (leave headroom for UI/GPU driver)");
                return;
            }
            other => {
                eprintln!("unknown arg: {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    pool::init_rayon_threads(threads);
    eprintln!("compute=CPU bitmask (threads={threads}; leave 2 cores free by default)");

    let t0 = Instant::now();
    let mut variants = Vec::new();
    let mut frontier_reports = Vec::new();

    match profile.as_str() {
        "smoke" => {
            variants.push(campaign_paths(2, 6));
            variants.push(campaign_stars(3, 5));
            variants.push(campaign_cycles(3, 6));
            variants.push(campaign_trees_all_odd(2, 4));
            variants.push(frontier_sanity());
        }
        "classify" => {
            let (v, f) = frontier_bicyclic_all_odd(4, 5, 64);
            variants.push(v);
            frontier_reports.push(f);
            let (v, f) = frontier_tricyclic(5, 5, 64, 1);
            variants.push(v);
            frontier_reports.push(f);
        }
        "frontier" => {
            variants.push(frontier_sanity());
            let (v, f) = frontier_unicyclic(4, 5, 32);
            variants.push(v);
            frontier_reports.push(f);
            let (v, f) = frontier_tricyclic(5, 5, 32, 1);
            variants.push(v);
            frontier_reports.push(f);
        }
        "heavy" => {
            variants.push(campaign_trees_all_odd(2, 7));
            variants.push(campaign_paths(2, 20));
            let (v, f) = frontier_unicyclic(4, 6, 64);
            variants.push(v);
            frontier_reports.push(f);
        }
        _ => {
            profile = "laptop".into();
            variants.push(campaign_trees_all_odd(2, 6));
            variants.push(campaign_paths(2, 16));
            let (v, f) = frontier_unicyclic(4, 6, 24);
            variants.push(v);
            frontier_reports.push(f);
        }
    }

    let total_checked: u64 = variants.iter().map(|v| v.checked).sum();
    let total_failed: u64 = variants.iter().map(|v| v.failed).sum();

    let report = Report {
        evidence_level: "E2_certified_computation",
        claim_type: "observation_experimental_mass_verification",
        disclaimer: "Mass verification is NOT a proof of P vs NP.",
        profile: profile.clone(),
        elapsed_ms: t0.elapsed().as_millis(),
        variants,
        frontier: frontier_reports,
        total_checked,
        total_failed,
        camino_b_status: "BLOCKED: resolution-width LBs are restricted-model",
        compute: format!("cpu_bitmask threads={threads}"),
    };

    let _ = fs::create_dir_all(&out_dir);
    let out = out_dir.join(format!("mass_verify_{profile}_latest.json"));
    fs::write(&out, serde_json::to_string_pretty(&report).unwrap()).unwrap();

    println!("profile={profile}");
    println!("compute={}", report.compute);
    println!("checked={} failed={}", report.total_checked, report.total_failed);
    println!("elapsed_ms={}", report.elapsed_ms);
    println!("report={}", out.display());
}
