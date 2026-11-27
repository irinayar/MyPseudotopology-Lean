using System;
using System.Collections.Generic;
using System.Numerics;
using System.Threading.Tasks;

// kappa: the one-modulus quantity  kappa = u * P( z + y = z' + y'  mod u ) = sum_{xi mod u} |phi_Y(xi/u)|^2 |phi_Z(xi/u)|^2 ,
// u = q^(s^2), y,y' uniform in the lower digit set T_s of q, z,z' uniform in T_t of p (radius 1/D),
// phi the characteristic function = product over digit levels of Dirichlet kernels.
// usage: kappa p q D s t [direct]       (direct: also count by enumeration, small sets only)
class P {
  static void Main(string[] a) {
    int p = int.Parse(a[0]), q = int.Parse(a[1]); long D = long.Parse(a[2]); int s = int.Parse(a[3]), t = int.Parse(a[4]);
    BigInteger uB = BigInteger.Pow(q, s * s); if (uB > 3000000000L) { Console.WriteLine("u too large"); return; }
    long u = (long)uB;
    // digit levels: (weight mod u, range J)
    var yw = new List<(long w, long J)>(); var zw = new List<(long w, long J)>();
    double sizeY = 1, sizeZ = 1;
    for (int n = 1; n <= s; n++) { long J = (long)(BigInteger.Pow(q, 2 * n - 1) / D); if (J == 0) continue; yw.Add(((long)(BigInteger.Pow(q, (n - 1) * (n - 1)) % u), J)); sizeY *= 2 * J + 1; }
    for (int m = 1; m <= t; m++) { long J = (long)(BigInteger.Pow(p, 2 * m - 1) / D); if (J == 0) continue; zw.Add(((long)(BigInteger.Pow(p, (m - 1) * (m - 1)) % u), J)); sizeZ *= 2 * J + 1; }
    double Phi2(List<(long w, long J)> L, long xi) {
      double v = 1;
      foreach (var (w, J) in L) {
        long r = (long)((UInt128)(ulong)w * (ulong)xi % (ulong)u); if (r == 0) continue;
        if (2 * r > u) r = u - r;
        long N = 2 * J + 1;
        long rn = (long)((UInt128)(ulong)N * (ulong)r % (ulong)(2 * u));   // N r mod 2u, to take sin(pi N r / u) accurately
        double f = Math.Sin(Math.PI * rn / (double)u) / (N * Math.Sin(Math.PI * r / (double)u));
        v *= f * f; if (v < 1e-18) return 0;
      }
      return v;
    }
    object gate = new object(); double sum = 0, max = 0;
    long half = u / 2;
    Parallel.For(0, 64, c => {
      double loc = 0, locMax = 0;
      for (long xi = 1 + c; xi <= half; xi += 64) {
        double y = Phi2(yw, xi); if (y == 0) continue;
        double val = y * Phi2(zw, xi); double mult = (2 * xi == u) ? 1 : 2;
        loc += mult * val; if (val > locMax) locMax = val;
      }
      lock (gate) { sum += loc; if (locMax > max) max = locMax; }
    });
    double kappa = 1 + sum;
    Console.WriteLine($"p={p} q={q} D={D} s={s} t={t} u={u} |Y|={sizeY:G6} |Z|={sizeZ:G6} u/(|Y||Z|)={u / (sizeY * sizeZ):G4} kappa={kappa:F6} max_term={max:G3}");
    if (a.Length > 5) {
      List<long> Set(List<(long w, long J)> L) { var S = new List<long> { 0 }; foreach (var (w, J) in L) { var T = new List<long>(); foreach (var x in S) for (long j = -J; j <= J; j++) T.Add((long)(((x + (BigInteger)j * w) % u + u) % u)); S = T; } return S; }
      var Y = Set(yw); var Z = Set(zw); var cnt = new long[u]; foreach (var z in Z) foreach (var y in Y) cnt[(z + y) % u]++;
      double N2 = 0; foreach (var c2 in cnt) N2 += (double)c2 * c2;
      Console.WriteLine($"   direct kappa={u * N2 / ((double)Y.Count * Y.Count * Z.Count * Z.Count):F6}");
    }
  }
}
