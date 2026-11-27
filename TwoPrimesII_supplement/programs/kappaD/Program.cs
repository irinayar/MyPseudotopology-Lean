using System;
using System.Collections.Generic;
using System.Numerics;
using System.Threading.Tasks;

// kappaD: the weighted one-modulus quantity at a far-apart height X = D v,
//   kappa_D = sum_{xi mod u} |phi_Y(xi/u)|^2 |phi_Z(xi/u)|^2 K_D(xi v/u) / K_D(0),
//   K_D(theta) = sum_{|m|<D} (D-|m|)^2 e(m theta) = 2 sum_{j<D} F_j + F_D,  F_j = |sum_{l<j} e(l theta)|^2,
// and the two-sided bounds for the exact energy
//   (v/u)(|Y|^2|Z|^2/u) sum G K^-  <=  E  <=  (v/u)(|Y|^2|Z|^2/u) sum G K^+,
//   K^- = 2 sum_{j<=D-2} F_j + (2-eps) F_{D-1},  K^+ = 2 sum_{j<=D} F_j + eps F_{D+1},  eps = 3/D.
// u = q^(s^2), v = p^(t^2), Y = lower digit set of q (s levels), Z of p (t levels), radius 1/D.
// usage: kappaD p q D s t
class P {
  static void Main(string[] a) {
    int p = int.Parse(a[0]), q = int.Parse(a[1]), D = int.Parse(a[2]), s = int.Parse(a[3]), t = int.Parse(a[4]);
    BigInteger uB = BigInteger.Pow(q, s * s), vB = BigInteger.Pow(p, t * t);
    if (uB > 3000000000L) { Console.WriteLine("u too large"); return; }
    long u = (long)uB, v = (long)vB, vm = (long)(vB % uB), X = checked(D * v);
    var yw = new List<(long w, long J)>(); var zw = new List<(long w, long J)>();
    double sizeY = 1, sizeZ = 1;
    for (int n = 1; n <= s; n++) { long J = (long)(BigInteger.Pow(q, 2 * n - 1) / D); if (J == 0) continue; yw.Add(((long)BigInteger.Pow(q, (n - 1) * (n - 1)), J)); sizeY *= 2 * J + 1; }
    for (int m = 1; m <= t; m++) { long J = (long)(BigInteger.Pow(p, 2 * m - 1) / D); if (J == 0) continue; zw.Add(((long)BigInteger.Pow(p, (m - 1) * (m - 1)), J)); sizeZ *= 2 * J + 1; }
    long MulMod(long x, long y) => (long)((UInt128)(ulong)x * (ulong)y % (ulong)u);
    double Phi2(List<(long w, long J)> L, long xi) {
      double val = 1;
      foreach (var (w, J) in L) {
        long r = MulMod(w % u, xi); if (r == 0) continue;
        if (2 * r > u) r = u - r;
        long N = 2 * J + 1;
        long rn = (long)((UInt128)(ulong)N * (ulong)r % (ulong)(2 * u));
        double f = Math.Sin(Math.PI * rn / (double)u) / (N * Math.Sin(Math.PI * r / (double)u));
        val *= f * f; if (val < 1e-18) return 0;
      }
      return val;
    }
    double eps = 3.0 / D;
    // returns (K^-, K_D, K^+) at theta = r/u
    (double lo, double mid, double up) Kern(long r) {
      double sum = 0, Sm2 = 0, Sm1 = 0, Fdm1 = 0, Fd = 0, Fdp1 = 0;
      double den = r == 0 ? 0 : Math.Sin(Math.PI * r / (double)u);
      for (int j = 1; j <= D + 1; j++) {
        double F;
        if (r == 0) F = (double)j * j;
        else { long jr = MulMod(j, r); double x = Math.Sin(Math.PI * jr / (double)u) / den; F = x * x; }
        if (j == D - 1) { Sm2 = sum; Fdm1 = F; }
        if (j == D) { Sm1 = sum; Fd = F; }
        if (j == D + 1) { Fdp1 = F; break; }
        sum += F;
      }
      double SD = sum;   // sum_{j<=D} F_j
      return (2 * Sm2 + (2 - eps) * Fdm1, 2 * Sm1 + Fd, 2 * SD + eps * Fdp1);
    }
    var k0 = Kern(0);
    object gate = new object(); double slo = 0, smid = 0, sup = 0, splain = 0;
    long half = u / 2;
    Parallel.For(0, 64, c => {
      double lo = 0, mid = 0, up = 0, pl = 0;
      for (long xi = 1 + c; xi <= half; xi += 64) {
        double g = Phi2(yw, xi); if (g == 0) continue;
        g *= Phi2(zw, xi); if (g == 0) continue;
        double mult = (2 * xi == u) ? 1 : 2;
        var K = Kern(MulMod(vm, xi));
        pl += mult * g; lo += mult * g * K.lo; mid += mult * g * K.mid; up += mult * g * K.up;
      }
      lock (gate) { slo += lo; smid += mid; sup += up; splain += pl; }
    });
    slo += k0.lo; smid += k0.mid; sup += k0.up;
    double kappa = 1 + splain, kappaD = smid / k0.mid;
    // exact sizes
    var Y = new List<long> { 0 }; foreach (var (w, J) in yw) { var T = new List<long>(); foreach (var x in Y) for (long j = -J; j <= J; j++) T.Add(x + j * w); Y = T; }
    double sizeA = 0; foreach (var y in Y) { long jmin = y >= 0 ? 0 : 1, jmax = (X - y) / u; sizeA += jmax - jmin + 1; }
    double sizeB = D * sizeZ + 1;
    double pref = (double)v / u * (sizeY * sizeY * sizeZ * sizeZ / u);
    double Clo = (2.0 * X + 1) * pref * slo / (sizeA * sizeA * sizeB * sizeB);
    double Cup = (2.0 * X + 1) * pref * sup / (sizeA * sizeA * sizeB * sizeB);
    Console.WriteLine($"p={p} q={q} D={D} s={s} t={t} v/(Du)={(double)v / D / u:F1} kappa={kappa:F6} kappaD={kappaD:F6} (4/3)kappaD={4.0 / 3 * kappaD:F5} C_lower={Clo:F5} C_upper={Cup:F5}");
  }
}
