using System;
using System.Numerics;
// Exact check of the level-structure construction for a general pair of primes p < q.
// Usage: lscheck2 p q eps x2 L0 L1 step
// x0 = xS(p,q) + eps. For an integer D coprime to pq: s* = x0 L^2; N* = ceil(sqrt((s*+L)/ln p)), M* likewise; search N in N*..N*+6, M in M*..M*+14 for overlapping intervals.
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
    int p = int.Parse(a[0]), q = int.Parse(a[1]); var ci = System.Globalization.CultureInfo.InvariantCulture;
    double eps = double.Parse(a[2], ci), x2 = double.Parse(a[3], ci), L0 = double.Parse(a[4], ci), L1 = double.Parse(a[5], ci), st = double.Parse(a[6], ci);
    double lp = Math.Log(p), lq = Math.Log(q);
    double Aa = 1 / Math.Sqrt(lp) + 1 / Math.Sqrt(lq), c = 0.25 * (1 / lp + 1 / lq); double xS = Math.Pow((Aa + Math.Sqrt(Aa * Aa - 4 * c)) / 2, 2);
    Console.WriteLine($"pair {{{p},{q}}} xS={xS:F6} x0={xS + eps:F6} x2={x2}");
    int tot = 0, fail = 0, resbad = 0; double minlam = 1e300, maxx = 0; int maxK = 0;
    for (double Lr = L0; Lr <= L1; Lr += st) {
      BigInteger D = (BigInteger)Math.Exp(Lr); while (BigInteger.GreatestCommonDivisor(D, p) != 1 || BigInteger.GreatestCommonDivisor(D, q) != 1) D += 1;
      double L = BigInteger.Log(D); double sstar = (xS + eps) * L * L;
      int Ns = (int)Math.Ceiling(Math.Sqrt((sstar + L) / lp)), Ms = (int)Math.Ceiling(Math.Sqrt((sstar + L) / lq));
      bool found = false; string msg = ""; int kused = 0;
      for (int N = Ns; N <= Ns + 6 && !found; N++) for (int M = Ms; M <= Ms + 14 && !found; M++) {
        double lowN = (N - 1.0) * (N - 1) * lp + L, upN = N * (double)N * lp - L, lowM = (M - 1.0) * (M - 1) * lq + L, upM = M * (double)M * lq - L;
        double lo = Math.Max(Math.Max(lowN, lowM), sstar), hi = Math.Min(upN, upM); if (lo >= hi - 2) continue;
        double s = lo + 1; double s2 = s / Math.Log(2); long k = (long)Math.Floor(s2) - 50; BigInteger X = new BigInteger(Math.Pow(2, s2 - k)) << (int)k;
        BigInteger u = Pw(p, (long)(N - 1) * (N - 1)), v = Pw(q, (long)(M - 1) * (M - 1)), qN = Pw(p, (long)N * N), qM = Pw(q, (long)M * M);
        bool c1 = X >= D * u && X >= D * v && X * D < qN && X * D < qM;
        BigInteger JN = (qN - 1) / (D * u), JM = (qM - 1) / (D * v); BigInteger JA = BigInteger.Min(JN, X / u), JB = BigInteger.Min(JM, X / v);
        bool c2 = JA >= D && JB >= D;
        double lnA = Math.Log(0.5) + BigInteger.Log(JA) + LnT(p, D, N - 1), lnB = Math.Log(0.5) + BigInteger.Log(JB) + LnT(q, D, M - 1);
        double lnlam = lnA + lnB - BigInteger.Log(2 * X + 1); double xs = BigInteger.Log(X) / (L * L);
        bool c3 = lnlam >= Math.Log(5) && xs <= x2;
        BigInteger sm = BigInteger.Min(u, v), gm = BigInteger.Max(u, v); BigInteger Jsm = X / sm; BigInteger epsN = 9 * gm * (gm + sm), epsD = sm * sm * D * Jsm;
        BigInteger pp, qq; BigInteger lon = gm * epsD - sm * epsN; if (lon <= 0) lon = 1; Simplest(lon, sm * epsD, gm * epsD + sm * epsN, sm * epsD, out pp, out qq);
        bool c4 = 2 * pp > D; if (c1 && c2 && c3 && !c4) resbad++;
        tot++; if (c1 && c2 && c3 && c4) { found = true; kused = N - Ns + 1; if (lnlam < minlam) minlam = lnlam; if (xs > maxx) maxx = xs; } else msg = $"N={N} M={M} c1={c1} c2={c2} c3={c3} c4={c4} x={xs:F4}";
      }
      if (!found) { fail++; Console.WriteLine($"FAIL L={L:F2}: {msg}"); } else if (kused > maxK) maxK = kused;
    }
    Console.WriteLine($"L in [{L0},{L1}] step {st}: failures={fail}; resonance-flagged candidates={resbad}; max block index used (K)={maxK}; min ln(lambda lower bound)={minlam:F2}; max x={maxx:F4}");
  }
}
