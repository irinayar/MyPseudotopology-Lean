using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using I = System.Int128;

// Exact least witness height for a single target t:
//   h(t) = min { |k| : P_3(k) < 1/D and P_2(k - t) < 1/D }.
// Method: all k in [-X, X] are enumerated by a sorted CRT window (prefix residues of the two balls,
// remaining levels tested exactly); X is multiplied by 4 until a witness exists.
// Usage: witness D tFrom tTo [brute]
class W {
  static I FloorDiv(I a, I b) { I q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
  static I Pow(int p, int e) { I r = 1; for (int i = 0; i < e; i++) r *= p; return r; }
  static List<I> Residues(int prime, I D, int level, out I modulus, int cap = int.MaxValue) {
    var values = new List<I> { 0 }; modulus = 1;
    for (int index = 1; index <= level; index++) {
      I prev = modulus; modulus = Pow(prime, index * index);
      I bound = (modulus - 1) / D; var next = new List<I>();
      foreach (var x in values) {
        I lo = -FloorDiv(bound + x, prev), hi = FloorDiv(bound - x, prev);
        for (I j = lo; j <= hi; j++) { next.Add(x + j * prev); if (next.Count > cap) return null; }
      }
      values = next;
    }
    I mm = modulus;
    return values.Select(x => { I m = x % mm; if (m < 0) m += mm; return m; }).ToList();
  }
  static I ModInv(I a, I m) {
    I aa = a % m; I t0 = m, t1 = aa; I s0 = 0, s1 = 1;
    while (t1 != 0) { I q = t0 / t1; (t0, t1) = (t1, t0 - q * t1); (s0, s1) = (s1, s0 - q * s1); }
    if (t0 != 1) throw new Exception("no inverse"); I r = s0 % m; if (r < 0) r += m; return r;
  }
  static I MulMod(I a, I b, I m) { return (I)((BigInteger)a * (BigInteger)b % (BigInteger)m); }
  static int Lower(I[] arr, I v) { int lo = 0, hi = arr.Length; while (lo < hi) { int mid = (lo + hi) / 2; if (arr[mid] < v) lo = mid + 1; else hi = mid; } return lo; }
  static int Upper(I[] arr, I v) { int lo = 0, hi = arr.Length; while (lo < hi) { int mid = (lo + hi) / 2; if (arr[mid] <= v) lo = mid + 1; else hi = mid; } return lo; }
  static bool InBall(I v, int p, I D, int fromLevel, I maxabs) {
    for (int n = fromLevel; ; n++) {
      I q = Pow(p, n * n); if (q > D * maxabs) return true;
      I r = v % q; if (r < 0) r += q; I d = I.Min(r, q - r);
      if (D * d >= q) return false;
    }
  }
  static void Auto(I D, I maxmod, int limit, out int bl, out int tl) {
    bl = 1; tl = 1;
    while (true) {
      bool can2 = Pow(2, (bl + 1) * (bl + 1)) <= maxmod, can3 = Pow(3, (tl + 1) * (tl + 1)) <= maxmod;
      if (can2) { var t = Residues(2, D, bl + 1, out _, limit); if (t == null) can2 = false; }
      if (can3) { var t = Residues(3, D, tl + 1, out _, limit); if (t == null) can3 = false; }
      if (!can2 && !can3) break;
      I m2 = Pow(2, (bl + 1) * (bl + 1)), m3 = Pow(3, (tl + 1) * (tl + 1));
      if (can2 && (!can3 || m2 <= m3)) bl++; else tl++;
    }
  }
  // all witnesses k with |k| <= X
  static List<I> Witnesses(I D, I t, I X, int limit) {
    I Wd = 2 * X; I maxabs = X + (t < 0 ? -t : t) + 1;
    Auto(D, D * (Wd + maxabs), limit, out int bl, out int tl);
    var R2 = Residues(2, D, bl, out I Q2); var R3 = Residues(3, D, tl, out I Q3);
    // u = k + X : u = (k - t) + t + X  (mod Q2 from binary ball), u = k + X (mod Q3 from ternary ball)
    var xs = R2.Select(b => { I m = (b + t + X) % Q2; if (m < 0) m += Q2; return m; }).ToList();
    var ys = R3.Select(a => { I m = (a + X) % Q3; if (m < 0) m += Q3; return m; }).ToList();
    I inv = ModInv(Q2, Q3);
    var transformed = ys.Select(y => MulMod(y, inv, Q3)).ToArray(); Array.Sort(transformed);
    var res = new List<I>();
    foreach (var x in xs) {
      if (x > Wd) continue;
      I offset = MulMod(x, inv, Q3); I last = offset + (Wd - x) / Q2; I cycles = last / Q3;
      for (I cycle = 0; cycle <= cycles; cycle++) {
        I bse = cycle * Q3; int s = Lower(transformed, offset - bse), e = Upper(transformed, last - bse);
        for (int i = s; i < e; i++) {
          I u = x + Q2 * (transformed[i] + bse - offset); I k = u - X;
          if (InBall(k, 3, D, tl + 1, maxabs) && InBall(k - t, 2, D, bl + 1, maxabs)) res.Add(k);
        }
      }
    }
    return res;
  }
  public static (I k, I X) Least(I D, I t, I Xmax) {
    I X = 1;
    while (X <= Xmax) {
      var w = Witnesses(D, t, X, 2000000);
      if (w.Count > 0) { I best = w[0]; foreach (var k in w) { I ak = k < 0 ? -k : k, ab = best < 0 ? -best : best; if (ak < ab || (ak == ab && k > best)) best = k; } return (best, X); }
      X *= 4;
    }
    return (0, -1);
  }
  static bool Good(I v, int p, I D) { return InBall(v, p, D, 1, v < 0 ? -v : v); }
  static void Main(string[] a) {
    if (a.Length > 1 && a[1] == "check") {
      // witness D check X count seed tmin tmax : for pseudo-random targets t in [tmin,tmax] enumerate all witnesses with |k|<=X
      I Dc = I.Parse(a[0]); I Xc = I.Parse(a[2]); int cnt = int.Parse(a[3]); var rng = new Random(int.Parse(a[4])); I tmin = I.Parse(a[5]), tmax = I.Parse(a[6]);
      for (int j = 0; j < cnt; j++) {
        long span = (long)(tmax - tmin); I t = tmin + (I)(long)(rng.NextDouble() * span);
        if (j == 0) t = tmax; if (j == 1) t = tmin;
        var sw = System.Diagnostics.Stopwatch.StartNew(); var w = Witnesses(Dc, t, Xc, 2000000);
        I best = 0; bool any = w.Count > 0; if (any) { best = w[0]; foreach (var k in w) { I ak = k < 0 ? -k : k, ab = best < 0 ? -best : best; if (ak < ab) best = k; } }
        Console.WriteLine($"D={Dc} X={Xc} t={t}: witnesses={w.Count} least|k|={(any ? (best < 0 ? -best : best).ToString() : "NONE")} ({sw.Elapsed.TotalSeconds:F1}s)");
      }
      return;
    }
    I D = I.Parse(a[0]); I t1 = I.Parse(a[1]), t2 = I.Parse(a[2]);
    bool brute = a.Length > 3 && a[3] == "brute";
    for (I t = t1; t <= t2; t++) {
      var (k, X) = Least(D, t, I.Parse("100000000000000000000000000000000000"));
      string extra = "";
      if (brute) {
        // direct search by increasing |k|
        I best = -1; for (I m = 0; m <= 3000000; m++) { if (Good(m, 3, D) && Good(m - t, 2, D)) { best = m; break; } if (Good(-m, 3, D) && Good(-m - t, 2, D)) { best = -m; break; } }
        extra = best == -1 ? " brute: none up to 3e6" : $" brute: {best}";
      }
      Console.WriteLine($"D={D} t={t} least |k|={(k < 0 ? -k : k)} (k={k}) found at X={X}{extra}");
    }
  }
}
