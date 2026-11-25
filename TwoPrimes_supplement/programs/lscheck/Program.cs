using System;
using System.Numerics;
// Exact check of the level-structure construction (proof of the suitable-heights proposition) for {2,3}.
// For an integer D (regular for 2 and 3) and x1 = xS + eps, B: s* = x1 L^2, N* = ceil(sqrt((s*+L)/ln2)), M* = ceil(sqrt((s*+L)/ln3)).
// Search N in N*..N*+3 and M in M*..M*+6 for overlapping intervals; X = max(lower ends, s*) rounded up to an integer.
// Then verify in exact integer arithmetic: X >= D u, X >= D v, X < q_N / D, X < q_M / D (cut inside the top level), J'_A, J'_B >= D,
// lambda lower bound from exact products of (2 J_n + 1), and ln X <= B L^2.
class P {
  static void Simplest(BigInteger ln, BigInteger ld, BigInteger hn, BigInteger hd, out BigInteger p, out BigInteger q) {
    BigInteger fl = BigInteger.Divide(ln, ld);
    if (fl * ld == ln) { p = fl; q = 1; return; }
    if ((fl + 1) * hd <= hn) { p = fl + 1; q = 1; return; }
    BigInteger a1, b1; Simplest(hd, hn - fl * hd, ld, ln - fl * ld, out a1, out b1); p = fl * a1 + b1; q = a1;
  }
  static BigInteger Pw(int b, long e) { return BigInteger.Pow(b, (int)e); }
  static double LnT(int l, BigInteger D, int upto) { double s = 0; for (int n = 1; n <= upto; n++) { BigInteger J = (Pw(l, (long)n * n) - 1) / (D * Pw(l, (long)(n - 1) * (n - 1))); s += BigInteger.Log(2 * J + 1); } return s; }
  static void Main(string[] a) {
    double eps = double.Parse(a[0], System.Globalization.CultureInfo.InvariantCulture), Bex = double.Parse(a[1], System.Globalization.CultureInfo.InvariantCulture);
    double L0 = double.Parse(a[2], System.Globalization.CultureInfo.InvariantCulture), L1 = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture), st = double.Parse(a[4], System.Globalization.CultureInfo.InvariantCulture);
    double Aa = 1 / Math.Sqrt(Math.Log(2)) + 1 / Math.Sqrt(Math.Log(3)), c = 0.25 * (1 / Math.Log(2) + 1 / Math.Log(3)); double xS = Math.Pow((Aa + Math.Sqrt(Aa * Aa - 4 * c)) / 2, 2);
    Console.WriteLine($"xS={xS:F6} x1={xS + eps:F6} B={Bex}");
    double ln2 = Math.Log(2), ln3 = Math.Log(3); int ok = 0, tot = 0, fail = 0, resbad = 0; double minlam = 1e300, maxx = 0;
    for (double Lr = L0; Lr <= L1; Lr += st) {
      BigInteger D = (BigInteger)Math.Exp(Math.Min(Lr, 700)); if (Lr > 700) D = BigInteger.Pow(10, (int)(Lr / Math.Log(10))); if (D % 2 == 0) D += 1; while (D % 3 == 0) D += 2; // regular (odd, not multiple of 3)
      double L = BigInteger.Log(D); double sstar = (xS + eps) * L * L;
      int Ns = (int)Math.Ceiling(Math.Sqrt((sstar + L) / ln2)), Ms = (int)Math.Ceiling(Math.Sqrt((sstar + L) / ln3));
      bool found = false; string msg = "";
      for (int N = Ns; N <= Ns + 3 && !found; N++) for (int M = Ms; M <= Ms + 8 && !found; M++) {
        double lowN = (N - 1.0) * (N - 1) * ln2 + L, upN = N * (double)N * ln2 - L, lowM = (M - 1.0) * (M - 1) * ln3 + L, upM = M * (double)M * ln3 - L;
        double lo = Math.Max(Math.Max(lowN, lowM), sstar), hi = Math.Min(upN, upM); if (lo >= hi - 2) continue;
        double s = lo + 1; // inside, integer rounding margin
        BigInteger X = (BigInteger)BigInteger.Parse(Math.Floor(Math.Exp(Math.Min(s, 700))).ToString("F0")); if (s > 700) { X = BigInteger.Pow(10, 0); }
        // exact X via logs for large s: X = floor(exp(s)) using BigInteger power of 2 scaling
        { double s2 = s / Math.Log(2); long k = (long)Math.Floor(s2) - 50; double frac = Math.Pow(2, s2 - k); X = new BigInteger(frac) << (int)k; }
        BigInteger u = Pw(2, (long)(N - 1) * (N - 1)), v = Pw(3, (long)(M - 1) * (M - 1)), qN = Pw(2, (long)N * N), qM = Pw(3, (long)M * M);
        bool c1 = X >= D * u && X >= D * v && X * D < qN && X * D < qM;
        BigInteger JN = (qN - 1) / (D * u), JM = (qM - 1) / (D * v); BigInteger JA = BigInteger.Min(JN, X / u), JB = BigInteger.Min(JM, X / v);
        bool c2 = JA >= D && JB >= D;
        double lnA = Math.Log(0.5) + BigInteger.Log(JA) + LnT(2, D, N - 1) , lnB = Math.Log(0.5) + BigInteger.Log(JB) + LnT(3, D, M - 1); // |A+| >= (J'/2)|Y|
        double lnlam = lnA + lnB - BigInteger.Log(2 * X + 1); double xs = BigInteger.Log(X) / (L * L);
        bool c3 = lnlam >= Math.Log(5) && xs <= Bex;
        BigInteger sm = BigInteger.Min(u, v), gm = BigInteger.Max(u, v); BigInteger Jsm = X / sm; BigInteger epsN = 9 * gm * (gm + sm), epsD = sm * sm * D * Jsm;
        BigInteger pp, qq; BigInteger lon = gm * epsD - sm * epsN; if (lon <= 0) lon = 1; Simplest(lon, sm * epsD, gm * epsD + sm * epsN, sm * epsD, out pp, out qq);
        bool c4 = 2 * pp > D; if (c1 && c2 && c3 && !c4) resbad++;
        c3 = c3 && c4;
        tot++; if (c1 && c2 && c3) { ok++; found = true; if (lnlam < minlam) minlam = lnlam; if (xs > maxx) maxx = xs; } else { msg = $"N={N} M={M} c1={c1} c2={c2} c3={c3} lnlam={lnlam:F2} x={xs:F4}"; }
      }
      if (!found) { fail++; Console.WriteLine($"FAIL L={L:F2}: {msg}"); }
    }
    Console.WriteLine($"L in [{L0},{L1}] step {st}: failures={fail}; resonance-flagged candidates={resbad}; min ln(lambda lower bound)={minlam:F3} (ln 5 = {Math.Log(5):F3}); max x={maxx:F4}");
  }
}
