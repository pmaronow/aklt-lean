// almbig.rs (agent 76): the same orbit-reduced window matrix as almorb.rs, for larger windows (m = k = 9, 10),
// with the exact part of the certificate moved into integer arithmetic here:
//   1. enumerate windows, D4-orbits, and for each orbit representative all k-step continuations (definitions as in
//      almorb.rs: history = list of sites, linear scans), storing per row the integer counts per (column orbit,
//      monomial (a, t, r));
//   2. for each parameter triple (c_s, c_t, rhat): float power iteration for a positive test vector h on orbits
//      (floored at FLOOR * max h), quantised to positive integers hnum (exact from here on);
//   3. S[row][monomial] = sum over entries of count * hnum[col], exactly, in u128;
//   4. print "P cs ct rhat", then "h row hnum" and "S row a t r S" lines.
// The exact rational evaluation lambda = max_row sum_mono S * ws^a wt^t rhat^r / hnum[row] is done by
// alm_big_exact.py.  Usage: almbig m k FLOOR cs ct rnum rden [cs ct rnum rden ...]   (cs, ct as decimals)
use std::collections::HashMap;
use std::io::{self, BufWriter, Write};

const DX: [i32; 4] = [1, 0, -1, 0];
const DY: [i32; 4] = [0, 1, 0, -1];

fn dirs_of(code: u64, m: usize) -> Vec<u8> {
    (0..m).map(|i| ((code >> (2 * i)) & 3) as u8).collect()
}
fn sites(d: &[u8]) -> Vec<(i32, i32)> {
    let mut p = vec![(0, 0)];
    for &x in d {
        let (a, b) = *p.last().unwrap();
        p.push((a + DX[x as usize], b + DY[x as usize]));
    }
    p
}
fn is_trail(d: &[u8]) -> bool {
    let p = sites(d);
    for i in 0..d.len() {
        for j in (i + 1)..d.len() {
            if (p[i] == p[j] && p[i + 1] == p[j + 1]) || (p[i] == p[j + 1] && p[i + 1] == p[j]) {
                return false;
            }
        }
    }
    true
}
fn canonical(d: &[u8]) -> u64 {
    let mut best = u64::MAX;
    for s in [1i32, -1] {
        for r in 0..4i32 {
            let mut c = 0u64;
            for (i, &x) in d.iter().enumerate() {
                c |= (((s * x as i32 + r).rem_euclid(4)) as u64) << (2 * i);
            }
            best = best.min(c);
        }
    }
    best
}
fn bond_used(hist: &[(i32, i32)], y: (i32, i32), z: (i32, i32)) -> bool {
    (0..hist.len() - 1).any(|i| (hist[i] == y && hist[i + 1] == z) || (hist[i] == z && hist[i + 1] == y))
}
fn left_before(hist: &[(i32, i32)], y: (i32, i32)) -> bool {
    hist[..hist.len() - 1].iter().any(|&p| p == y)
}

struct Ctx<'a> {
    m: usize,
    k: usize,
    orbit_of_canon: &'a HashMap<u64, u32>,
    acc: HashMap<(u32, u8), u32>,   // (col orbit, monomial index) -> count
    mono_index: Vec<Vec<u8>>,       // [a][t] -> index (r = k - a - t)
}

fn dfs(ctx: &mut Ctx, hist: &mut Vec<(i32, i32)>, dirs: &mut Vec<u8>, step: usize, a: usize, t: usize) {
    if step == ctx.k {
        let n = dirs.len();
        let o = *ctx.orbit_of_canon.get(&canonical(&dirs[n - ctx.m..])).expect("not a window");
        let mi = ctx.mono_index[a][t];
        *ctx.acc.entry((o, mi)).or_insert(0) += 1;
        return;
    }
    let y = *hist.last().unwrap();
    let last = *dirs.last().unwrap();
    let rev = left_before(hist, y);
    for d in 0u8..4 {
        let z = (y.0 + DX[d as usize], y.1 + DY[d as usize]);
        if bond_used(hist, y, z) {
            continue;
        }
        let (na, nt) = if rev { (a, t) } else if d == last { (a + 1, t) } else { (a, t + 1) };
        hist.push(z);
        dirs.push(d);
        dfs(ctx, hist, dirs, step + 1, na, nt);
        hist.pop();
        dirs.pop();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let m: usize = args[1].parse().unwrap();
    let k: usize = args[2].parse().unwrap();
    let floor: f64 = args[3].parse().unwrap();
    let mut monos: Vec<(usize, usize, usize)> = Vec::new();
    let mut mono_index = vec![vec![255u8; k + 1]; k + 1];
    for a in 0..=k {
        for t in 0..=(k - a) {
            mono_index[a][t] = monos.len() as u8;
            monos.push((a, t, k - a - t));
        }
    }
    let mut orbit_of_canon: HashMap<u64, u32> = HashMap::new();
    let mut reps: Vec<u64> = Vec::new();
    let mut size: Vec<u64> = Vec::new();
    let mut nwin = 0u64;
    for c in 0..(1u64 << (2 * m)) {
        let d = dirs_of(c, m);
        if !is_trail(&d) {
            continue;
        }
        nwin += 1;
        let cc = canonical(&d);
        let o = *orbit_of_canon.entry(cc).or_insert_with(|| {
            reps.push(cc);
            size.push(0);
            (reps.len() - 1) as u32
        });
        size[o as usize] += 1;
    }
    let norb = reps.len();
    eprintln!("m={} k={} windows={} orbits={}", m, k, nwin, norb);
    // rows: Vec of (col, mono, cnt)
    let mut rows: Vec<Vec<(u32, u8, u32)>> = Vec::with_capacity(norb);
    let mut ctx = Ctx { m, k, orbit_of_canon: &orbit_of_canon, acc: HashMap::new(), mono_index };
    let mut total: u128 = 0;
    for (o, &c) in reps.iter().enumerate() {
        let d = dirs_of(c, m);
        let mut hist = sites(&d);
        let mut dirs = d.clone();
        ctx.acc.clear();
        dfs(&mut ctx, &mut hist, &mut dirs, 0, 0, 0);
        let mut v: Vec<(u32, u8, u32)> = ctx.acc.iter().map(|(&(col, mi), &cnt)| (col, mi, cnt)).collect();
        v.sort();
        total += size[o] as u128 * v.iter().map(|x| x.2 as u128).sum::<u128>();
        rows.push(v);
    }
    let nnz: usize = rows.iter().map(|r| r.len()).sum();
    eprintln!("stored entries = {}, sum |O| * continuations = {} (= t_(m+k))", nnz, total);
    let out = io::stdout();
    let mut w = BufWriter::new(out.lock());
    writeln!(w, "H {} {} {} {} {}", m, k, nwin, norb, total).unwrap();
    for o in 0..norb {
        writeln!(w, "O {} {} {}", o, reps[o], size[o]).unwrap();
    }
    let mut ai = 4;
    while ai + 3 < args.len() {
        let cs: f64 = args[ai].parse().unwrap();
        let ct: f64 = args[ai + 1].parse().unwrap();
        let rn: f64 = args[ai + 2].parse().unwrap();
        let rd: f64 = args[ai + 3].parse().unwrap();
        ai += 4;
        let (ws, wt, wr) = (1.0 / (3.0 * cs), 1.0 / (3.0 * ct), rn / rd);
        let mw: Vec<f64> = monos.iter().map(|&(a, t, r)| ws.powi(a as i32) * wt.powi(t as i32) * wr.powi(r as i32)).collect();
        let mut h = vec![1.0f64; norb];
        let mut y = vec![0.0f64; norb];
        for _ in 0..1500 {
            let mut mx = 0.0f64;
            for o in 0..norb {
                let s: f64 = rows[o].iter().map(|&(col, mi, cnt)| cnt as f64 * mw[mi as usize] * h[col as usize]).sum();
                y[o] = s;
                if s > mx {
                    mx = s;
                }
            }
            for o in 0..norb {
                h[o] = y[o] / mx;
            }
        }
        let hmax = h.iter().cloned().fold(0.0, f64::max);
        let scale = (1u64 << 40) as f64 / hmax;
        let hnum: Vec<u64> = h.iter().map(|&x| ((x.max(floor * hmax)) * scale).round() as u64 + 1).collect();
        writeln!(w, "P {} {} {} {}", args[ai - 4], args[ai - 3], args[ai - 2], args[ai - 1]).unwrap();
        for o in 0..norb {
            writeln!(w, "h {} {}", o, hnum[o]).unwrap();
        }
        for o in 0..norb {
            let mut s = vec![0u128; monos.len()];
            for &(col, mi, cnt) in &rows[o] {
                s[mi as usize] += cnt as u128 * hnum[col as usize] as u128;
            }
            for (mi, &val) in s.iter().enumerate() {
                if val > 0 {
                    let (a, t, r) = monos[mi];
                    writeln!(w, "S {} {} {} {} {}", o, a, t, r, val).unwrap();
                }
            }
        }
        w.flush().unwrap();
    }
}
