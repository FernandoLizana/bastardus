//! Thread-pool policy: never pin all logical CPUs by default (leave headroom for UI/GPU driver).

use std::sync::Once;

static INIT: Once = Once::new();

/// Initialize Rayon with an explicit thread count (idempotent for first call wins).
pub fn init_rayon_threads(threads: usize) {
    INIT.call_once(|| {
        let n = threads.max(1);
        let _ = rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .build_global();
        eprintln!("rayon threads={n} (CPU headroom reserved for UI/GPU)");
    });
}

/// Default: leave 2 logical CPUs free (min 2 worker threads).
pub fn default_thread_count() -> usize {
    let cpus = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    (cpus.saturating_sub(2)).max(2)
}
