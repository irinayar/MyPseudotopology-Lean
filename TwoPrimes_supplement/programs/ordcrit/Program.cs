using System;
using System.Collections.Generic;
using System.Numerics;
// Resonance-order criterion for (H) at the top heights J_A = J_N (X about r q_N).
// For levels (N for base 2, M for base l): u = 2^((N-1)^2), v = l^((M-1)^2); small step s, big step b, rho = big/small >= 1.
// Bad if there is a rational a/c within eps = K*rho*(1+rho)/(D*Jsmall) of rho with numerator a <= AMAX*D (a = coordinate on the small-step lattice).
// Fitted law (ordscan): peak excess about 0.45 D/a for a <~ 0.35 D, half-width |c*rho-a| = 3 a (1+rho)/(D J); here K = 9 (factor 3 safety) and AMAX = 0.5.
// Usage: ordcrit l D1 D2 step [K] [AMAX]    scans D = D1, D1+step, ..., D2 (regular D only)
class P {
  static BigInteger Gcd(BigInteger a, BigInteger b) { return BigInteger.GreatestCommonDivisor(a, b); }
  // simplest rational p/q with lo <= p/q <= hi (lo = ln/ld, hi = hn/hd), positive
  static void Simplest(BigInteger ln, BigInteger ld, BigInteger hn, BigInteger hd, out BigInteger p, out BigInteger q) {
    BigInteger fl = BigInteger.Divide(ln, ld);
    if (fl * ld == ln) { p = fl; q = 1; return; }           // lo integer
    if ((fl + 1) * hd <= hn) { p = fl + 1; q = 1; return; }  // integer in (lo, hi]
    // lo, hi in (fl, fl+1): x -> 1/(x - fl) swaps the order
    BigInteger a1, b1; // new lo' = 1/(hi - fl) = hd/(hn - fl*hd), hi' = 1/(lo - fl) = ld/(ln - fl*ld)
    Simplest(hd, hn - fl * hd, ld, ln - fl * ld, out a1, out b1);
    // r = a1/b1 ; result = fl + 1/r = fl + b1/a1 = (fl*a1 + b1)/a1
    p = fl * a1 + b1; q = a1;
  }
  static double XLO = double.Parse(Environment.GetEnvironmentVariable("XLO") ?? "3.4", System.Globalization.CultureInfo.InvariantCulture);
  static double LAM = double.Parse(Environment.GetEnvironmentVariable("LAM") ?? "5", System.Globalization.CultureInfo.InvariantCulture);
  static double XHI = double.Parse(Environment.GetEnvironmentVariable("XHI") ?? "6.0", System.Globalization.CultureInfo.InvariantCulture);
  static double HDIV = double.Parse(Environment.GetEnvironmentVariable("HDIV") ?? "0", System.Globalization.CultureInfo.InvariantCulture);
  static int HIMAX = int.Parse(Environment.GetEnvironmentVariable("HIMAX") ?? "12");
  static double[] LnT(int p, long D, int nmax) { var r = new double[nmax + 2]; double s = 0; r[0] = 0; for (int n = 1; n <= nmax + 1; n++) { BigInteger q = BigInteger.Pow(p, n * n), qp = BigInteger.Pow(p, (n - 1) * (n - 1)); BigInteger J = (q - 1) / (D * qp); r[n] = r[n - 1] + BigInteger.Log(2 * J + 1); } return r; }
  static bool Regular(long D, int l) { long x = D; while (x % l == 0) x /= l; return x != 1; }
  static void Main(string[] args) {
    int l = int.Parse(args[0]); long D1 = long.Parse(args[1]), D2 = long.Parse(args[2]), st = long.Parse(args[3]);
    long K = args.Length > 4 ? long.Parse(args[4]) : 9; double AMAX = args.Length > 5 ? double.Parse(args[5], System.Globalization.CultureInfo.InvariantCulture) : 0.5;
    for (long D = D1; D <= D2; D = (st == 0 ? ((double)D * 1.37 > 4e18 ? long.MaxValue : (long)(D * 1.37) + 1) : D + st)) {
      if (!Regular(D, 2) || !Regular(D, l)) continue;
      double Ln = Math.Log(D), L2 = Ln * Ln; int nmax = (int)Math.Sqrt(6.2 * L2 / Math.Log(2)) + 3, mmax = (int)Math.Sqrt(6.2 * L2 / Math.Log(l)) + 3;
      int valid = 0, good = 0; double bestRatio = 0; string bestS = ""; double minx = 99; string minS = ""; var lnTA = LnT(2, D, nmax); var lnTB = LnT(l, D, mmax);
      for (int N = 2; N <= nmax; N++) {
        BigInteger qN = BigInteger.Pow(2, N * N), u = BigInteger.Pow(2, (N - 1) * (N - 1)); BigInteger JN = (qN - 1) / (D * u);
        if (JN < D) continue;
        // X = J_N * u (top height); use a few heights: J_A = J_N (top)
        for (int hi = 0; hi < HIMAX; hi++) {
        BigInteger JAx = HDIV > 0 ? new BigInteger((double)JN / Math.Pow(HDIV, hi)) : (JN >> hi); if (JAx < D) break;
        BigInteger X = JAx * u;
        double lnX = BigInteger.Log(X); double xr = lnX / L2; if (xr < XLO || xr > XHI) continue;
        for (int M = 2; M <= mmax; M++) {
          BigInteger qM = BigInteger.Pow(l, M * M), v = BigInteger.Pow(l, (M - 1) * (M - 1)); BigInteger JM = (qM - 1) / (D * v);
          BigInteger JB = X / v; if (JB < D || JB > JM) continue;
          valid++;
          // small step s, big step g
          BigInteger s = BigInteger.Min(u, v), g = BigInteger.Max(u, v); BigInteger Jsmall = X / s;
          // rho = g/s ; eps = K*rho*(1+rho)/(D*Jsmall) = K*g*(g+s)/(s*s*D*Jsmall)
          BigInteger epsN = K * g * (g + s), epsD = s * s * D * Jsmall;
          BigInteger lo_n = g * epsD - s * epsN, lo_d = s * epsD, hi_n = g * epsD + s * epsN, hi_d = s * epsD;
          BigInteger p, q; 
          if (lo_n <= 0) { lo_n = 1; }
          Simplest(lo_n, lo_d, hi_n, hi_d, out p, out q);
          // p/q is the minimal-denominator rational; numerator a = p (coordinate on the small-step lattice)
          double ratio = (double)p / D; // a / D
          // criterion: bad iff a <= AMAX * D
          bool bad = (double)p <= AMAX * D;
          double lnA = Math.Log((double)JAx + 0.5) + lnTA[N - 1], lnB = Math.Log((double)JB + 0.5) + lnTB[M - 1]; double lam = Math.Exp(lnA + lnB - BigInteger.Log(2 * X + 1)); if (lam < LAM) bad = true;
          if (Environment.GetEnvironmentVariable("V") == "2") Console.WriteLine($"ALL {D} {N} {M} {JAx} {JB} {(bad ? 1 : 0)} {p}");
          if (bad && Environment.GetEnvironmentVariable("V") != null) Console.WriteLine($"  BAD D={D} N={N} M={M} hi={hi} JA={JAx} JB={JB} a={p} c={q} rho={(double)g/(double)s:G5} x={xr:F2}");
          if (!bad) { good++; if (xr < minx) { minx = xr; minS = $"minx N={N} M={M} hi={hi} lam={lam:G4} a/D={(double)p / D:G4}"; } if (ratio > bestRatio) { bestRatio = ratio; bestS = $"N={N} M={M} a_min/D={(double)p / D:G4} x={xr:F2}"; } }
        }
        }
      }
      Console.WriteLine($"D={D} l={l} validpairs={valid} good={good} minx={minx:F3} {minS}");
    }
  }
}
