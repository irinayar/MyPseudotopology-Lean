using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Heuristic prediction of the unit-target height from exact ball counts.
// N_p(X) = #{k in [0,X] : P_p(k) < 1/D} by the digit description (levels n with range J_n = floor(p^(2n-1)/D), weight p^((n-1)^2)),
// counted exactly by a top-down recursion; expected number of unit witnesses in [0,X] under independence: M(X) = N_2(X) N_3(X) / (X+1).
// usage: modelcount brute D X      (check N_p against the definition)
//        modelcount pred D1,D2,...  [steps]   (first X on a geometric grid with M(X) >= 1, and the first with M >= 10)
class P {
  static BigInteger Pow(int b, int e) => BigInteger.Pow(b, e);
  class Ball {
    public int p; public BigInteger D; public List<BigInteger> W = new(); public List<BigInteger> J = new(); public List<BigInteger> U = new(); public List<BigInteger> Tsize = new();
    public Ball(int p, BigInteger D, BigInteger maxX) {
      this.p = p; this.D = D; BigInteger u = 0, ts = 1; // index n = 0 is empty set {0}
      W.Add(1); J.Add(0); U.Add(0); Tsize.Add(1);
      for (int n = 1; ; n++) {
        BigInteger w = Pow(p, (n - 1) * (n - 1)); BigInteger j = Pow(p, 2 * n - 1) / D;
        W.Add(w); J.Add(j); u += j * w; U.Add(u); ts *= (2 * j + 1); Tsize.Add(ts);
        if (w > maxX * 4 && j > 0) break; if (n > 400) throw new Exception("too many levels");
      }
    }
    BigInteger Floor(BigInteger a, BigInteger b) { var q = BigInteger.DivRem(a, b, out var r); if (r < 0) q -= 1; return q; }
    BigInteger Ceil(BigInteger a, BigInteger b) => -Floor(-a, b);
    // number of elements of T_n (digits of levels 1..n) in [lo,hi]
    public BigInteger Count(int n, BigInteger lo, BigInteger hi) {
      if (lo > hi) return 0; if (n == 0) return (lo <= 0 && hi >= 0) ? 1 : 0;
      if (lo <= -U[n] && hi >= U[n]) return Tsize[n];
      if (lo > U[n] || hi < -U[n]) return 0;
      BigInteger w = W[n], jn = J[n], um = U[n - 1];
      BigInteger dmin = BigInteger.Max(-jn, Ceil(lo - um, w)), dmax = BigInteger.Min(jn, Floor(hi + um, w));
      if (dmin > dmax) return 0;
      // d is "interior" iff lo <= d w - um and d w + um <= hi
      BigInteger imin = BigInteger.Max(dmin, Ceil(lo + um, w)), imax = BigInteger.Min(dmax, Floor(hi - um, w));
      BigInteger tot = 0;
      if (imin <= imax) { tot += (imax - imin + 1) * Tsize[n - 1]; }
      for (BigInteger d = dmin; d <= dmax; d++) {
        if (imin <= imax && d >= imin && d <= imax) { d = imax; continue; }
        tot += Count(n - 1, lo - d * w, hi - d * w);
        if (d - dmin > 8 && (imin > imax)) throw new Exception("too many boundary digits");
      }
      return tot;
    }
    public BigInteger NUpTo(BigInteger X) { int n = W.Count - 1; return Count(n, 0, X); }
  }
  static bool InBall(long k, int p, int D) { for (int n = 1; ; n++) { var q = Pow(p, n * n); if (q > (BigInteger.Abs(k) + 2) * D) return true; var rm = BigInteger.Remainder(k, q); if (rm < 0) rm += q; var dist = BigInteger.Min(rm, q - rm); if (dist * D >= q) return false; } }
  static double Ln(BigInteger x) { long bits = (long)x.GetBitLength(); if (bits < 1000) return Math.Log((double)x); int sh = (int)(bits - 900); return Math.Log((double)(x >> sh)) + sh * Math.Log(2.0); }
  static void Main(string[] a) {
    if (a[0] == "brute") {
      int D = int.Parse(a[1]); long X = long.Parse(a[2]);
      foreach (int p in new[] { 2, 3 }) { long c = 0; for (long k = 0; k <= X; k++) if (InBall(k, p, D)) c++; var b = new Ball(p, D, X); Console.WriteLine($"p={p} D={D} X={X}: brute {c}, digits {b.NUpTo(X)}"); }
      return;
    }
    if (a[0] == "ath") { // ath file : for every plateau (D1 D2 digits h ...) of the staircase file, M(h) at D1 and D2 (skipping powers of 2 and 3)
      foreach (var line in System.IO.File.ReadAllLines(a[1])) {
        if (line.StartsWith("#") || line.Trim().Length == 0) continue; var f = line.Split(' ', StringSplitOptions.RemoveEmptyEntries); int d1 = int.Parse(f[0]), d2 = int.Parse(f[1]); BigInteger h = BigInteger.Parse(f[3]);
        foreach (int D in new[] { d1, d2 }) {
          bool pw = false; foreach (int p in new[] { 2, 3 }) { BigInteger q = 1; while (q < D) q *= p; if (q == D) pw = true; } if (pw) { Console.WriteLine($"D={D}: power of 2 or 3, skipped"); continue; }
          var b2 = new Ball(2, D, h); var b3 = new Ball(3, D, h); BigInteger n2 = b2.NUpTo(h), n3 = b3.NUpTo(h);
          double lm = Ln(n2) + Ln(n3) - Ln(h + 1); Console.WriteLine($"D={D}: ln h={Ln(h):F2} lnM(h)={lm:F3} M(h)={Math.Exp(lm):G4} {(D == d1 ? "first" : "last")}");
        }
      }
      return;
    }
    if (a[0] == "predbig") { // predbig D1,D2,... : first lnX (grid 0.25, then refined) with M(X) >= 1, for large D (given as decimal strings)
      foreach (var ds in a[1].Split(',')) {
        BigInteger D = BigInteger.Parse(ds); double L = Ln(D); double lx0 = 0.5 * L * L; double? found = null;
        BigInteger maxX = BigInteger.Pow(2, (int)(4.0 * L * L / Math.Log(2)));
        var b2 = new Ball(2, D, maxX); var b3 = new Ball(3, D, maxX);
        for (double lx = lx0; lx < 4.0 * L * L; lx += 0.25) {
          double bits = lx / Math.Log(2); int ib = (int)Math.Floor(bits); BigInteger X = (new BigInteger(Math.Pow(2, bits - ib) * (1L << 50))) << Math.Max(0, ib - 50);
          BigInteger n2 = b2.NUpTo(X), n3 = b3.NUpTo(X); if (n2.IsZero || n3.IsZero) continue;
          double lm = Ln(n2) + Ln(n3) - Ln(X + 1); if (lm >= -Math.Log(2.0)) { found = lx; break; }
        }
        Console.WriteLine($"D={ds}: L={L:F2} lnX*={(found.HasValue ? found.Value.ToString("F2") : "-")} e_pred={(found.HasValue ? (found.Value / (L * L)).ToString("F4") : "-")}");
      }
      return;
    }
    if (a[0] == "atall") { // atall file : 2*M(h_D) for every D of the staircase file (skipping powers of 2 and 3); positive and negative k both counted
      foreach (var line in System.IO.File.ReadAllLines(a[1])) {
        if (line.StartsWith("#") || line.Trim().Length == 0) continue; var f = line.Split(' ', StringSplitOptions.RemoveEmptyEntries); int d1 = int.Parse(f[0]), d2 = int.Parse(f[1]); BigInteger h = BigInteger.Parse(f[3]);
        for (int D = d1; D <= d2; D++) {
          bool pw = false; foreach (int p in new[] { 2, 3 }) { BigInteger q = 1; while (q < D) q *= p; if (q == D) pw = true; } if (pw) continue;
          var b2 = new Ball(2, D, h); var b3 = new Ball(3, D, h); BigInteger n2 = b2.NUpTo(h), n3 = b3.NUpTo(h);
          Console.WriteLine($"{D} {d1} {2.0 * Math.Exp(Ln(n2) + Ln(n3) - Ln(h + 1)):G6}");
        }
      }
      return;
    }
    if (a[0] == "tgt") { // tgt file : 2*M(h_D(t)) for lines "t=.. D=.. h=.." with h > 100|t| and D not a power of 2 or 3
      foreach (var line in System.IO.File.ReadAllLines(a[1])) {
        var m = System.Text.RegularExpressions.Regex.Match(line, @"^t=(\d+) D=(\d+) h=(\d+)"); if (!m.Success) continue;
        int tt = int.Parse(m.Groups[1].Value), D = int.Parse(m.Groups[2].Value); BigInteger h = BigInteger.Parse(m.Groups[3].Value);
        if (h <= 100 * tt) continue;
        bool pw = false; foreach (int p in new[] { 2, 3 }) { BigInteger q = 1; while (q < D) q *= p; if (q == D) pw = true; } if (pw) continue;
        var b2 = new Ball(2, D, h); var b3 = new Ball(3, D, h); BigInteger n2 = b2.NUpTo(h), n3 = b3.NUpTo(h);
        Console.WriteLine($"{tt} {D} {2.0 * Math.Exp(Ln(n2) + Ln(n3) - Ln(h + 1)):G6}");
      }
      return;
    }
    if (a[0] == "pred") {
      var Ds = a[1].Split(',').Select(int.Parse).ToArray(); double step = a.Length > 2 ? double.Parse(a[2]) : 0.05; // grid in ln X
      foreach (int D in Ds) {
        BigInteger maxX = BigInteger.Pow(10, 90); var b2 = new Ball(2, D, maxX); var b3 = new Ball(3, D, maxX);
        double? x1 = null, x10 = null; BigInteger X = 1;
        for (double lx = 1; lx < 200; lx += step) {
          X = new BigInteger(Math.Exp(Math.Min(lx, 40))); if (lx > 40) { X = BigInteger.Pow(2, (int)(lx / Math.Log(2) - 40 / Math.Log(2))) * new BigInteger(Math.Exp(40)); }
          BigInteger n2 = b2.NUpTo(X), n3 = b3.NUpTo(X); if (n2.IsZero || n3.IsZero) continue;
          double lm = Ln(n2) + Ln(n3) - Ln(X + 1);
          if (x1 == null && lm >= 0) x1 = lx; if (x10 == null && lm >= Math.Log(10)) { x10 = lx; break; }
        }
        Console.WriteLine($"D={D}: lnX(M>=1)={(x1.HasValue ? x1.Value.ToString("F2") : "-")} lnX(M>=10)={(x10.HasValue ? x10.Value.ToString("F2") : "-")}");
      }
    }
  }
}
