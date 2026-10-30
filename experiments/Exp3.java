import java.util.*;
public class Exp3 {
  static double nrm(double x) { double f = x - Math.rint(x); return Math.abs(f); }
  public static void main(String[] args) {
    double delta = 0.2; long N = Long.parseLong(args[0]);
    List<Integer> A = new ArrayList<>();
    for (int k = 0; k <= N; k++) if (Exp1.pk(k) < delta) A.add(k);
    long M = 100 * N; double tol = N / (2.0 * M);
    List<long[]> clusters = new ArrayList<>();
    long start = -1, prev = -2;
    for (long m = 0; m < M; m++) {
      double c = (m + 0.5) / M; boolean ok = true;
      for (int k : A) if (nrm(k * c) > 0.125 + tol) { ok = false; break; }
      if (ok) { if (m != prev + 1) { if (start >= 0) clusters.add(new long[]{start, prev}); start = m; } prev = m; }
    }
    if (start >= 0) clusters.add(new long[]{start, prev});
    System.out.println("N=" + N + " |A|=" + A.size() + " clusters of K' (cells of width 1/(100N)): " + clusters.size());
    for (long[] cl : clusters) {
      double lo = cl[0] / (double) M, hi = (cl[1] + 1) / (double) M, mid = (lo + hi) / 2;
      // nearest {2,3}-smooth fraction u/(2^a 3^b), a<=6,b<=4
      double best = 1e9; String bs = "";
      for (int a2 = 0; a2 <= 6; a2++) for (int b3 = 0; b3 <= 4; b3++) {
        long q = (long) Math.pow(2, a2) * (long) Math.pow(3, b3);
        long u = Math.round(mid * q); double dist = Math.abs(mid - (double) u / q);
        if (dist < best - 1e-12 || (Math.abs(dist - best) < 1e-12 && q < Long.parseLong(bs.isEmpty() ? "999999" : bs.split("/")[1]))) { best = dist; bs = u + "/" + q; }
      }
      System.out.printf("  [%.6f, %.6f] width %.2e  nearest 2^a3^b-fraction %s (dist %.1e)%n", lo, hi, hi - lo, bs, best);
    }
    // Weyl average |S_A(alpha)|/|A| for named alphas
    String[] names = {"0", "1/2", "1/3", "1/6", "1/4", "1/9", "1/5", "1/7", "golden (sqrt5-1)/2", "sqrt2-1", "e-2", "pi-3", "0.123456789"};
    double[] al = {0, 0.5, 1.0 / 3, 1.0 / 6, 0.25, 1.0 / 9, 0.2, 1.0 / 7, (Math.sqrt(5) - 1) / 2, Math.sqrt(2) - 1, Math.E - 2, Math.PI - 3, 0.123456789};
    System.out.println("  |S_A(alpha)|/|A| (1 = all frequencies aligned) and max_k in A of ||k alpha||:");
    for (int i = 0; i < al.length; i++) {
      double C = 0, S = 0, mx = 0;
      for (int k : A) { double t = 2 * Math.PI * k * al[i]; C += Math.cos(t); S += Math.sin(t); mx = Math.max(mx, nrm(k * al[i])); }
      System.out.printf("    %-22s %.4f   %.4f%n", names[i], Math.hypot(C, S) / A.size(), mx);
    }
    // random alphas
    Random r = new Random(1); double sum = 0, mxS = 0; int T = 100000;
    for (int t = 0; t < T; t++) { double al0 = r.nextDouble(), C = 0, S = 0; for (int k : A) { double th = 2 * Math.PI * k * al0; C += Math.cos(th); S += Math.sin(th); }
      double v = Math.hypot(C, S) / A.size(); sum += v; mxS = Math.max(mxS, v); }
    System.out.printf("  random alpha (%d samples): mean |S|/|A| = %.4f (1/sqrt|A| = %.4f), max = %.4f%n", T, sum / T, 1 / Math.sqrt(A.size()), mxS);
  }
}
