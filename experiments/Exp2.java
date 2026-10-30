import java.util.*;
public class Exp2 {
  static double nrm(double x) { double f = x - Math.rint(x); return Math.abs(f); }
  public static void main(String[] args) {
    double delta = Double.parseDouble(args[0]);
    double eps = 2 * delta;
    long[] Ns = new long[args.length - 1];
    for (int i = 1; i < args.length; i++) Ns[i - 1] = Long.parseLong(args[i]);
    for (long N : Ns) {
      List<Integer> A = new ArrayList<>(), B = new ArrayList<>();
      for (int k = 0; k <= N; k++) { double p = Exp1.pk(k); if (p < delta) A.add(k); if (p < eps) B.add(k); }
      int nA = A.size();
      long M = 100 * N;
      double tol = N / (2.0 * M);
      long cntG = 0, cntK2lo = 0, cntK2hi = 0, cntK1lo = 0, cntK1hi = 0, cntS = 0;
      for (long m = 0; m < M; m++) {
        double g = (double) m / M;
        // proof's grid test: Q(g) >= |A|^2/4
        double C = 0, S = 0;
        for (int k : A) { double t = 2 * Math.PI * k * g; C += Math.cos(t); S += Math.sin(t); }
        double Q = C * C + S * S;
        if (Q >= (double) nA * nA / 4) cntG++;
        if (Math.sqrt(Q) >= nA / 2.0) cntS++;
        double c = (m + 0.5) / M;
        boolean ok2hi = true, ok2lo = true;
        for (int k : A) { double v = nrm(k * c); if (v > 0.125 + tol) { ok2hi = false; ok2lo = false; break; } if (v > 0.125 - tol) ok2lo = false; }
        if (ok2hi) cntK2hi++; if (ok2lo) cntK2lo++;
        boolean ok1hi = true, ok1lo = true;
        for (int k : B) { double v = nrm(k * c); if (v > 0.25 + tol) { ok1hi = false; ok1lo = false; break; } if (v > 0.25 - tol) ok1lo = false; }
        if (ok1hi) cntK1hi++; if (ok1lo) cntK1lo++;
      }
      long dN = 2 + (long) Math.floor(Math.sqrt(Math.log(N / delta) / Math.log(2))) + (long) Math.floor(Math.sqrt(Math.log(N / delta) / Math.log(3)));
      long Lq = (long) Math.floor(1 / delta) + 1;
      System.out.printf("N=%d delta=%.2f eps=%.2f |A|=%d |B_eps∩[0,N]|=%d M=%d%n", N, delta, eps, nA, B.size(), M);
      System.out.printf("  proof grid cells G (Q>=|A|^2/4): %d   Parseval bound 4M/|A| = %.1f   paper bound 400*L^d = %.3e (L=%d,d=%d)%n", cntG, 4.0 * M / nA, 400 * Math.pow(Lq, dN), Lq, dN);
      System.out.printf("  cells of K'={||k a||<=1/8 on A}: between %d and %d  (measure ~%.5f)%n", cntK2lo, cntK2hi, cntK2hi / (double) M);
      System.out.printf("  cells of K_eps superset {||k a||<=1/4 on B_eps∩[0,N]}: between %d and %d (measure ~%.5f)%n", cntK1lo, cntK1hi, cntK1hi / (double) M);
      System.out.printf("  measure{|S_A|>=|A|/2} = %.5f   Chebyshev bound 4/|A| = %.5f%n", cntS / (double) M, 4.0 / nA);
    }
  }
}
