using System;
using System.Collections.Generic;
using System.Numerics;
using System.Linq;
using I = System.Int128;

// Exact finite collision certificate (C# port of crt_collision_certificate.py + JA_pair_recursion.pair_counter).
// Usage: crt D X binaryLevel ternaryLevel
// D = 1/r.  Balls: {k : P_p(k) < 1/D}.  Energy E = |A||B| + 2 sum_{h>0} rA(h) rB(h); C = (2X+1)E/(|A||B|)^2.
class PairCounter {
  readonly I p; readonly I D; readonly I h;
  readonly Dictionary<int, I> mod = new(); readonly Dictionary<int, (I, I)[]> allowedC = new();
  readonly Dictionary<int, I> fullC = new(); readonly Dictionary<(int, I), I> prefC = new();
  public PairCounter(int p, I D, I h) { this.p = p; this.D = D; this.h = h; }
  I Modulus(int n) { if (mod.TryGetValue(n, out var v)) return v; I r = 1; for (int i = 0; i < n * n; i++) r *= p; mod[n] = r; return r; }
  static List<(I, I)> Cyc(I start, I length, I q) {
    start %= q; if (start < 0) start += q;
    if (start + length <= q) return new() { (start, start + length) };
    return new() { (0, start + length - q), (start, q) };
  }
  (I, I)[] Allowed(int n) {
    if (allowedC.TryGetValue(n, out var v)) return v;
    I q = Modulus(n); I T = (q - 1) / D; I L = 2 * T + 1;
    var Iv = Cyc(-T, L, q); var Jv = Cyc(-T - h, L, q);
    var K = new List<(I, I)>();
    foreach (var (l, u) in Iv) foreach (var (vv, w) in Jv) { I a = l > vv ? l : vv; I b = u < w ? u : w; if (a < b) K.Add((a, b)); }
    K.Sort(); var outl = new List<(I, I)>();
    foreach (var (l, u) in K) { if (outl.Count > 0 && l <= outl[^1].Item2) outl[^1] = (outl[^1].Item1, I.Max(u, outl[^1].Item2)); else outl.Add((l, u)); }
    var arr = outl.ToArray(); allowedC[n] = arr; return arr;
  }
  I Full(int n) {
    if (n == 0) return 1; if (fullC.TryGetValue(n, out var v)) return v;
    I s = 0; foreach (var (l, u) in Allowed(n)) s += Prefix(n - 1, u) - Prefix(n - 1, l);
    fullC[n] = s; return s;
  }
  I Prefix(int n, I Y) {
    if (Y <= 0) return 0; if (n == 0) return Y;
    if (prefC.TryGetValue((n, Y), out var v)) return v;
    I q = Modulus(n); I a = Y / q, r = Y % q;
    I s = a * Full(n);
    foreach (var (l, u) in Allowed(n)) s += Prefix(n - 1, I.Min(r, u)) - Prefix(n - 1, I.Min(r, l));
    prefC[(n, Y)] = s; return s;
  }
  public I Count(I X) {
    if (h > X) return 0; int n = 0; while (Modulus(n + 1) <= D * X) n++;
    return Prefix(n, X - h + 1);
  }
}
class Prog {
  static int PB = 2, PT = 3;
  static List<I> Residues(int prime, I denominator, int level, out I modulus, int cap = int.MaxValue) {
    var values = new List<I> { 0 }; modulus = 1;
    for (int index = 1; index <= level; index++) {
      I prev = modulus; modulus = 1; for (int i = 0; i < index * index; i++) modulus *= prime;
      I bound = (modulus - 1) / denominator; var next = new List<I>();
      foreach (var x in values) {
        I lo = -FloorDiv(bound + x, prev), hi = FloorDiv(bound - x, prev);
        for (I j = lo; j <= hi; j++) { next.Add(x + j * prev); if (next.Count > cap) return null; }
      }
      values = next;
    }
    I mm = modulus;
    return values.Select(x => { I m = x % mm; if (m < 0) m += mm; return m; }).ToList();
  }
  static I FloorDiv(I a, I b) { I q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
  static I ModInv(I a, I m) {
    I aa = a % m; I t0 = m, t1 = aa; I s0 = 0, s1 = 1;
    while (t1 != 0) { I q = t0 / t1; (t0, t1) = (t1, t0 - q * t1); (s0, s1) = (s1, s0 - q * s1); }
    if (t0 != 1) throw new Exception("no inverse"); I r = s0 % m; if (r < 0) r += m; return r;
  }
  static I MulMod(I a, I b, I m) { return (I)((BigInteger)a * (BigInteger)b % (BigInteger)m); }
  static int Lower(I[] arr, I v) { int lo = 0, hi = arr.Length; while (lo < hi) { int mid = (lo + hi) / 2; if (arr[mid] < v) lo = mid + 1; else hi = mid; } return lo; }
  static int Upper(I[] arr, I v) { int lo = 0, hi = arr.Length; while (lo < hi) { int mid = (lo + hi) / 2; if (arr[mid] <= v) lo = mid + 1; else hi = mid; } return lo; }
  static void Auto(I denominator, I height, int limit, out int bl, out int tl) {
    I relaxed = denominator / 2; bl = 1; tl = 1;
    while (true) {
      I m2 = 1; for (int i = 0; i < (bl+1)*(bl+1); i++) m2 *= PB; I m3 = 1; for (int i = 0; i < (tl+1)*(tl+1); i++) m3 *= PT;
      bool can2 = m2 <= relaxed * height, can3 = m3 <= relaxed * height; if (can2) { var t = Residues(PB, relaxed, bl+1, out _, limit); if (t == null) can2 = false; } if (can3) { var t = Residues(PT, relaxed, tl+1, out _, limit); if (t == null) can3 = false; }
      if (!can2 && !can3) break;
      if (can2 && (!can3 || m2 <= m3)) bl++; else tl++;
    }
  }
  static IEnumerable<I> Candidates(I denominator, I height, int bl, int tl) {
    I relaxed = denominator / 2;
    var left = Residues(PB, relaxed, bl, out I binary); var right = Residues(PT, relaxed, tl, out I ternary);
    I inverse = ModInv(binary, ternary);
    var transformed = right.Select(x => MulMod(x, inverse, ternary)).ToArray(); Array.Sort(transformed);
    var extra = new List<(I, I)>();
    foreach (var (prime, start) in new[] { (PB, bl + 1), (PT, tl + 1) }) {
      int index = start;
      while (true) { I modulus = 1; for (int i = 0; i < index * index; i++) modulus *= prime; if (modulus > relaxed * height) break; extra.Add((modulus, (modulus - 1) / relaxed)); index++; }
    }
    extra.Sort();
    foreach (var x in left) {
      if (x > height) continue;
      I offset = MulMod(x, inverse, ternary);
      I last = offset + (height - x) / binary;
      I cycles = last / ternary;
      for (I cycle = 0; cycle <= cycles; cycle++) {
        I bse = cycle * ternary;
        int s = Lower(transformed, offset - bse), e = Upper(transformed, last - bse);
        for (int i = s; i < e; i++) {
          I hh = x + binary * (transformed[i] + bse - offset);
          if (hh == 0) continue; bool ok = true;
          foreach (var (q, bound) in extra) { I r = hh % q; if (bound < r && r < q - bound) { ok = false; break; } }
          if (ok) yield return hh;
        }
      }
    }
  }
  static I MaxOf(int p, I D, I X, I countAtX) {
    var c = new PairCounter(p, D, 0); I lo = 0, hi = X;
    while (lo < hi) { I mid = (lo + hi) / 2; if (c.Count(mid) == countAtX) hi = mid; else lo = mid + 1; }
    return lo;
  }
  class Res { public I N2, N3; public BigInteger E, Range, HullRange; public long Tested, Contrib; public double C, Lambda; public I MB, MT; public int Bl, Tl; public List<(BigInteger, I, I, I)> Top = new(); }
  static Res Run(I D, I X, int bl, int tl, bool wantMax) {
    if (bl <= 0) Auto(D, X, 2000000, out bl, out tl);
    var R = new Res { Bl = bl, Tl = tl };
    I left = new PairCounter(PB, D, 0).Count(X), right = new PairCounter(PT, D, 0).Count(X);
    BigInteger mass = (BigInteger)left * (BigInteger)right; BigInteger energy = mass;
    foreach (var h in Candidates(D, X, bl, tl)) {
      R.Tested++; var lc = new PairCounter(PB, D, h).Count(X);
      if (lc != 0) {
        var rc = new PairCounter(PT, D, h).Count(X);
        if (rc != 0) {
          R.Contrib++; BigInteger w = 2 * (BigInteger)lc * (BigInteger)rc; energy += w; if (Environment.GetEnvironmentVariable("DUMP") != null) Console.Error.WriteLine("SH " + h + " " + lc + " " + rc + " " + w);
          R.Top.Add((w, h, lc, rc)); R.Top.Sort((u, v) => v.Item1.CompareTo(u.Item1)); if (R.Top.Count > 5) R.Top.RemoveAt(5);
        }
      }
    }
    R.N2 = left; R.N3 = right; R.E = energy;
    R.C = (double)((BigInteger)(2 * X + 1) * energy * 1000000000 / (mass * mass)) / 1e9;
    R.Lambda = (double)mass / (double)(2 * X + 1);
    if (wantMax) {
      R.MB = MaxOf(PB, D, X, left); R.MT = MaxOf(PT, D, X, right);
      BigInteger lower = (mass * mass + energy - 1) / energy;
      R.Range = 2 * lower - (BigInteger)(2 * X + 1) - 1; R.HullRange = 2 * lower - (BigInteger)R.MB - (BigInteger)R.MT - 2;
    }
    return R;
  }
  static List<I> Umax(int p, I D, double limit) {
    var res = new List<I>(); I prev = 1; I U = 0;
    for (int n = 1; n < 12; n++) {
      I q = 1; for (int i = 0; i < n * n; i++) q *= p; I J = (q - 1) / (D * prev);
      if (J > 0) { U += J * prev; if ((double)U > limit) break; res.Add(U); }
      prev = q;
    }
    return res;
  }
  static void Main(string[] a) {
    PB = int.Parse(Environment.GetEnvironmentVariable("PB") ?? "2"); PT = int.Parse(Environment.GetEnvironmentVariable("PT") ?? "3");
    I D = I.Parse(a[0]);
    if (a.Length > 1 && a[1] == "maxes") {
      for (int ai = 2; ai < a.Length; ai++) {
        I Xm = I.Parse(a[ai]); I l = new PairCounter(PB, D, 0).Count(Xm), r = new PairCounter(PT, D, 0).Count(Xm);
        Console.WriteLine($"{D} {Xm} {MaxOf(PB, D, Xm, l)} {MaxOf(PT, D, Xm, r)}");
      }
      return;
    }
    if (a.Length > 1 && a[1] == "stages") {
      // crt D stages Xlo Xhi : heights X = max(U2(a),U3(b)) at completed stages of both balls
      double lo = double.Parse(a[2], System.Globalization.CultureInfo.InvariantCulture), hi = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture);
      var U2 = Umax(PB, D, hi * 3); var U3 = Umax(PT, D, hi * 3);
      var hs = new SortedSet<I>(); foreach (var u in U2) foreach (var v in U3) { I x = I.Max(u, v); if (x >= (I)lo && x <= (I)hi) hs.Add(x); }
      Console.WriteLine("D X N2 N3 candidates lambda C excess levels");
      foreach (var X in hs) { var R = Run(D, X, 0, 0, false); Console.WriteLine($"{D} {X} {R.N2} {R.N3} {R.Tested} {R.Lambda:F3} {R.C:F4} {R.C - 1 / R.Lambda - 4.0 / 3:F4} ({R.Bl},{R.Tl})"); }
      return;
    }
    if (a.Length > 1 && a[1] == "sweep") {
      // crt D sweep Xlo Xhi ratio
      double lo = double.Parse(a[2], System.Globalization.CultureInfo.InvariantCulture), hi = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture), ratio = double.Parse(a[4], System.Globalization.CultureInfo.InvariantCulture);
      Console.WriteLine("D X N2 N3 candidates lambda C excess levels");
      for (double x = lo; x <= hi; x *= ratio) {
        I X = (I)x; var R = Run(D, X, 0, 0, false);
        Console.WriteLine($"{D} {X} {R.N2} {R.N3} {R.Tested} {R.Lambda:F3} {R.C:F4} {R.C - 1 / R.Lambda - 4.0 / 3:F4} ({R.Bl},{R.Tl})");
      }
      return;
    }
    I Xs = I.Parse(a[1]); int bl = int.Parse(a[2]), tl = int.Parse(a[3]);
    var S = Run(D, Xs, bl, tl, true);
    Console.WriteLine($"D={D} X={Xs} levels=({S.Bl},{S.Tl}) N2={S.N2} N3={S.N3} E={S.E} candidates={S.Tested} contributing={S.Contrib}");
    Console.WriteLine($"C={S.C:F6} lambda=NN/(2X+1)={S.Lambda:F3} 1/lambda={1 / S.Lambda:F4} excess=C-1/lambda-4/3={S.C - 1 / S.Lambda - 4.0 / 3:F4} binary_max={S.MB} ternary_max={S.MT}");
    Console.WriteLine($"target_range={S.Range} hull_target_range={S.HullRange}");
    foreach (var t in S.Top) Console.WriteLine($"  top h={t.Item2} rB={t.Item3} rA={t.Item4} share={(double)(t.Item1 * 1000000 / S.E) / 1e6:F4}");
  }
}
