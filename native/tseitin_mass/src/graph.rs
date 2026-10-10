//! Compact adjacency graphs + Prüfer enumeration + Aut helpers.

use std::collections::{HashSet, VecDeque};

#[derive(Clone, Debug)]
pub struct Graph {
    pub n: usize,
    pub adj: Vec<Vec<u16>>,
}

impl Graph {
    pub fn with_n(n: usize) -> Self {
        Self {
            n,
            adj: vec![Vec::new(); n],
        }
    }

    pub fn add_edge(&mut self, u: u16, v: u16) {
        self.adj[u as usize].push(v);
        self.adj[v as usize].push(u);
    }

    pub fn degree(&self, v: usize) -> usize {
        self.adj[v].len()
    }

    pub fn max_degree(&self) -> usize {
        self.adj.iter().map(|a| a.len()).max().unwrap_or(0)
    }

    pub fn edges_sorted(&self) -> Vec<(u16, u16)> {
        let mut e = Vec::new();
        for u in 0..self.n {
            for &v in &self.adj[u] {
                if (u as u16) < v {
                    e.push((u as u16, v));
                }
            }
        }
        e.sort_unstable();
        e
    }

    pub fn is_tree(&self) -> bool {
        if self.n == 0 {
            return false;
        }
        if self.edges_sorted().len() != self.n.saturating_sub(1) {
            return false;
        }
        self.is_connected()
    }

    pub fn is_connected(&self) -> bool {
        if self.n == 0 {
            return true;
        }
        let mut seen = vec![false; self.n];
        let mut q = VecDeque::new();
        q.push_back(0usize);
        seen[0] = true;
        let mut count = 0;
        while let Some(u) = q.pop_front() {
            count += 1;
            for &v in &self.adj[u] {
                let v = v as usize;
                if !seen[v] {
                    seen[v] = true;
                    q.push_back(v);
                }
            }
        }
        count == self.n
    }

    pub fn is_cycle(&self) -> bool {
        if self.n < 3 {
            return false;
        }
        if self.edges_sorted().len() != self.n {
            return false;
        }
        if self.adj.iter().any(|a| a.len() != 2) {
            return false;
        }
        self.is_connected()
    }

    /// Connected simple graph with exactly one more edge than a tree: |E|=|V|.
    pub fn is_unicyclic(&self) -> bool {
        self.n >= 3 && self.is_connected() && self.edges_sorted().len() == self.n
    }

    /// Connected with cyclomatic number 2: |E|=|V|+1.
    pub fn is_bicyclic(&self) -> bool {
        self.n >= 4 && self.is_connected() && self.edges_sorted().len() == self.n + 1
    }

    /// Connected with cyclomatic number 3: |E|=|V|+2.
    pub fn is_tricyclic(&self) -> bool {
        self.n >= 4 && self.is_connected() && self.edges_sorted().len() == self.n + 2
    }
}

pub fn path(n: usize) -> Graph {
    let mut g = Graph::with_n(n);
    for i in 0..n.saturating_sub(1) {
        g.add_edge(i as u16, (i + 1) as u16);
    }
    g
}

pub fn cycle(n: usize) -> Graph {
    let mut g = Graph::with_n(n);
    for i in 0..n {
        g.add_edge(i as u16, ((i + 1) % n) as u16);
    }
    g
}

pub fn star(n: usize) -> Graph {
    let mut g = Graph::with_n(n);
    for i in 1..n {
        g.add_edge(0, i as u16);
    }
    g
}

pub fn forest_two_stars(a: usize, b: usize) -> Graph {
    // Two disjoint stars (components)
    let n = a + b;
    let mut g = Graph::with_n(n);
    for i in 1..a {
        g.add_edge(0, i as u16);
    }
    let root = a as u16;
    for i in 1..b {
        g.add_edge(root, root + i as u16);
    }
    g
}

/// Decode Prüfer code of length n-2 into a labeled tree on 0..n-1.
pub fn from_prufer(code: &[u16]) -> Graph {
    let n = code.len() + 2;
    let mut degree = vec![1usize; n];
    for &x in code {
        degree[x as usize] += 1;
    }
    let mut g = Graph::with_n(n);
    let mut code_q: VecDeque<u16> = code.iter().copied().collect();
    for _ in 0..(n - 2) {
        let leaf = (0..n).find(|&i| degree[i] == 1).expect("leaf") as u16;
        let parent = code_q.pop_front().unwrap_or(0);
        g.add_edge(leaf, parent);
        degree[leaf as usize] -= 1;
        degree[parent as usize] -= 1;
    }
    let rem: Vec<u16> = (0..n as u16).filter(|&i| degree[i as usize] == 1).collect();
    debug_assert_eq!(rem.len(), 2);
    g.add_edge(rem[0], rem[1]);
    g
}

/// Iterate all Prüfer codes (all labeled trees).
pub fn for_each_labeled_tree(n: usize, mut f: impl FnMut(Graph)) {
    if n == 1 {
        f(Graph::with_n(1));
        return;
    }
    if n == 2 {
        let mut g = Graph::with_n(2);
        g.add_edge(0, 1);
        f(g);
        return;
    }
    let m = n - 2;
    let total = (n as u64).pow(m as u32);
    let mut code = vec![0u16; m];
    for idx in 0..total {
        let mut t = idx;
        for i in 0..m {
            code[i] = (t % n as u64) as u16;
            t /= n as u64;
        }
        f(from_prufer(&code));
    }
}

/// Edge → variable id (1-based).
pub fn edge_var_map(g: &Graph) -> std::collections::HashMap<(u16, u16), i16> {
    let mut m = std::collections::HashMap::new();
    for (i, &(u, v)) in g.edges_sorted().iter().enumerate() {
        m.insert((u, v), (i + 1) as i16);
    }
    m
}

/// Naive Aut(G): all permutations of V that preserve adjacency (OK for n≤10).
pub fn automorphisms(g: &Graph) -> Vec<Vec<u16>> {
    let n = g.n;
    if n == 0 {
        return vec![vec![]];
    }
    // Degree signature pruning
    let deg: Vec<usize> = (0..n).map(|v| g.degree(v)).collect();
    let mut perms = Vec::new();
    let mut used = vec![false; n];
    let mut cur = vec![0u16; n];

    // Edge set for quick check
    let edges: HashSet<(u16, u16)> = g.edges_sorted().into_iter().collect();

    fn rec(
        pos: usize,
        n: usize,
        deg: &[usize],
        used: &mut [bool],
        cur: &mut [u16],
        edges: &HashSet<(u16, u16)>,
        g: &Graph,
        out: &mut Vec<Vec<u16>>,
    ) {
        if pos == n {
            // verify homomorphism
            for u in 0..n {
                for &v in &g.adj[u] {
                    let a = cur[u].min(cur[v as usize]);
                    let b = cur[u].max(cur[v as usize]);
                    if !edges.contains(&(a, b)) {
                        return;
                    }
                }
            }
            out.push(cur.to_vec());
            return;
        }
        for cand in 0..n {
            if used[cand] {
                continue;
            }
            if deg[cand] != deg[pos] {
                continue;
            }
            // Partial edge check against already assigned
            let mut ok = true;
            for u in 0..pos {
                let connected = g.adj[u].contains(&(pos as u16));
                let a = cur[u].min(cand as u16);
                let b = cur[u].max(cand as u16);
                let img = edges.contains(&(a, b));
                if connected != img {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            used[cand] = true;
            cur[pos] = cand as u16;
            rec(pos + 1, n, deg, used, cur, edges, g, out);
            used[cand] = false;
        }
    }

    rec(0, n, &deg, &mut used, &mut cur, &edges, g, &mut perms);
    if perms.is_empty() {
        // identity always exists; enumeration bug ⇒ fall back
        perms.push((0..n as u16).collect());
    }
    perms
}

/// Orbit-min representatives of odd-parity charge vectors under Aut(G).
/// Charges packed as bitmask (bit v = charge of vertex v).
pub fn odd_charge_orbit_reps(g: &Graph) -> Vec<u32> {
    let n = g.n;
    assert!(n <= 24, "n too large for bit charge enum");
    let auts = automorphisms(g);
    let mut seen = HashSet::new();
    let mut reps = Vec::new();
    let limit = 1u32 << n;
    for mask in 0..limit {
        if mask.count_ones() % 2 == 0 {
            continue; // even total charge ⇒ SAT for connected graphs
        }
        // canonical: minimal image under Aut
        let mut canon = mask;
        for pi in &auts {
            let mut img = 0u32;
            for v in 0..n {
                if (mask >> v) & 1 == 1 {
                    img |= 1u32 << pi[v];
                }
            }
            canon = canon.min(img);
        }
        if seen.insert(canon) {
            reps.push(canon);
        }
    }
    reps
}

pub fn charges_from_mask(mask: u32, n: usize) -> Vec<u8> {
    (0..n).map(|v| ((mask >> v) & 1) as u8).collect()
}

/// Dihedral group D_n acting on GF(2)^n charge vectors of a cycle.
pub fn cycle_odd_charge_orbit_reps(n: usize) -> Vec<u32> {
    assert!(n <= 24);
    let mut seen = HashSet::new();
    let mut reps = Vec::new();
    let limit = 1u32 << n;
    for mask in 0..limit {
        if mask.count_ones() % 2 == 0 {
            continue;
        }
        let mut canon = mask;
        for r in 0..n {
            let mut rot = 0u32;
            for v in 0..n {
                if (mask >> v) & 1 == 1 {
                    rot |= 1u32 << ((v + r) % n);
                }
            }
            canon = canon.min(rot);
        }
        for s in 0..n {
            let mut refl = 0u32;
            for v in 0..n {
                if (mask >> v) & 1 == 1 {
                    refl |= 1u32 << ((n - v + s) % n);
                }
            }
            canon = canon.min(refl);
        }
        if seen.insert(canon) {
            reps.push(canon);
        }
    }
    reps
}

/// Path Aut ≅ ℤ₂ (reverse). Vertex labels 0..n-1 along the path.
pub fn path_odd_charge_orbit_reps(n: usize) -> Vec<u32> {
    assert!(n <= 24);
    let mut seen = HashSet::new();
    let mut reps = Vec::new();
    let limit = 1u32 << n;
    for mask in 0..limit {
        if mask.count_ones() % 2 == 0 {
            continue;
        }
        let mut rev = 0u32;
        for v in 0..n {
            if (mask >> v) & 1 == 1 {
                rev |= 1u32 << (n - 1 - v);
            }
        }
        let canon = mask.min(rev);
        if seen.insert(canon) {
            reps.push(canon);
        }
    }
    reps
}

/// Star with center 0, leaves 1..n-1. Aut ≅ S_{n-1} on leaves.
/// Canonical: keep center bit, sort leaf bits into a multiset via sorting the leaf-bit string.
pub fn star_odd_charge_orbit_reps(n: usize) -> Vec<u32> {
    assert!(n <= 24 && n >= 1);
    let mut seen = HashSet::new();
    let mut reps = Vec::new();
    let limit = 1u32 << n;
    for mask in 0..limit {
        if mask.count_ones() % 2 == 0 {
            continue;
        }
        let center = mask & 1;
        let mut leaf_bits: Vec<u8> = (1..n).map(|v| ((mask >> v) & 1) as u8).collect();
        leaf_bits.sort_unstable(); // non-decreasing ⇒ canonical under S_{n-1}
        let mut canon = center;
        for (i, bit) in leaf_bits.into_iter().enumerate() {
            if bit == 1 {
                canon |= 1u32 << (i + 1);
            }
        }
        if seen.insert(canon) {
            reps.push(canon);
        }
    }
    reps
}
