import java.util.*;

/** Exp12: numerical test of the non-degeneracy property (TVGaddmore_v12 Remark 7.14 / v13 Remark 7.15), S={2,3}.
 *  Step 1: list every k <= K (multiples of 6) with P(k) < T0, P computed in double from exact integer remainders.
 *  Step 2: for each listed k and each centre pair (P2,P3) in 1..CM, E(k;P2,P3) = max over l,n of ||k/l^(n^2)|| / r^|n-P_l|
 *          (the smallest eps for which k has profile (eps,r;P2,P3)); E(k) = min over centres.
 *  Step 3: for a list of parameters x, report max and mean of ||kx||/E(k) per level of E, and residues of k mod small primes.
 *  Usage: java Exp12 K T0 r */
public class Exp12 {
    static final long[] BASES = {2, 3};

    static double pk(long k, double stop) {
        double m = 0;
        for (long base : BASES) {
            for (long n = 1; ; n++) {
                long q = 1; long e = n * n;
                boolean big = false;
                for (long i = 0; i < e; i++) { if (q > Long.MAX_VALUE / base) { big = true; break; } q *= base; }
                double t;
                if (big) t = 0; else { long r = k % q; long s = Math.min(r, q - r); t = (double) s / (double) q; }
                if (t > m) m = t;
                if (m >= stop) return m;
                if (big || q > 2 * k) break;
            }
        }
        return m;
    }

    static double nrm(double t) { t = t - Math.floor(t); return Math.min(t, 1 - t); }

    /** ||k x|| for x given as double, k up to 1e11: reduce k*x mod 1 using BigDecimal-free trick (long double not available):
     *  use x = num/den rational where possible, else split x into high and low parts. */
    static double kx(long k, double x) {
        // exact-ish: split k = a*2^20 + b
        long a = k >> 20, b = k & ((1L << 20) - 1);
        double xa = x * (double) (1L << 20); xa = xa - Math.floor(xa);
        double r = (a % 1000003L) * 0.0; // placeholder to keep the compiler quiet
        double t1 = fracMul(a, xa);
        double t2 = fracMul(b, x);
        return nrm(t1 + t2);
    }
    static double fracMul(long a, double y) { // frac(a*y) with a < 2^40, y in [0,1): split a
        long a1 = a >> 20, a0 = a & ((1L << 20) - 1);
        double y1 = y * (double) (1L << 20); y1 -= Math.floor(y1);
        double p1 = (a1 * y1); p1 -= Math.floor(p1);
        double p0 = (a0 * y); p0 -= Math.floor(p0);
        double s = p1 + p0; return s - Math.floor(s);
    }

    public static void main(String[] args) {
        long K = Long.parseLong(args[0]); double T0 = Double.parseDouble(args[1]); double r = Double.parseDouble(args[2]);
        int CM = 9;
        ArrayList<Long> L = new ArrayList<>(); ArrayList<Double> PL = new ArrayList<>();
        for (long k = 6; k <= K; k += 6) {
            double p = pk(k, T0);
            if (p < T0) { L.add(k); PL.add(p); }
        }
        System.out.println("K=" + K + " T0=" + T0 + " count(P<T0)=" + L.size());
        // E(k)
        int N = L.size(); double[] E = new double[N]; int[] c2 = new int[N], c3 = new int[N];
        for (int i = 0; i < N; i++) {
            long k = L.get(i); double best = 1e9;
            // per-scale values
            double[][] v = new double[2][];
            for (int bi = 0; bi < 2; bi++) {
                long base = BASES[bi]; ArrayList<Double> t = new ArrayList<>();
                for (long n = 1; ; n++) {
                    long q = 1; for (long j = 0; j < n * n; j++) q *= base;
                    long rr = k % q; long s = Math.min(rr, q - rr); t.add((double) s / (double) q);
                    if (q > 2 * k) break;
                }
                v[bi] = new double[t.size()]; for (int j = 0; j < t.size(); j++) v[bi][j] = t.get(j);
            }
            for (int P2 = 1; P2 <= CM; P2++) for (int P3 = 1; P3 <= CM; P3++) {
                double e = 0;
                for (int j = 0; j < v[0].length; j++) e = Math.max(e, v[0][j] / Math.pow(r, Math.abs((j + 1) - P2)));
                for (int j = 0; j < v[1].length; j++) e = Math.max(e, v[1][j] / Math.pow(r, Math.abs((j + 1) - P3)));
                if (e < best) { best = e; c2[i] = P2; c3[i] = P3; }
            }
            E[i] = best;
        }
        String[] names = {"1/5", "2/5", "1/7", "1/11", "1/13", "1/25", "1/4(H)", "1/3(H)", "5/12(H)", "1/9(H)", "sqrt2", "phi", "pi", "e", "ln2", "Liouville"};
        double lio = 0; for (int n = 1; n <= 6; n++) lio += Math.pow(2, -n * n) + Math.pow(3, -n * n);
        double[] xs = {1.0 / 5, 2.0 / 5, 1.0 / 7, 1.0 / 11, 1.0 / 13, 1.0 / 25, 0.25, 1.0 / 3, 5.0 / 12, 1.0 / 9,
                Math.sqrt(2) - 1, (1 + Math.sqrt(5)) / 2 - 1, Math.PI - 3, Math.E - 2, Math.log(2), lio};
        double[] levels = {0.12, 0.10, 0.08, 0.07, 0.06, 0.05, 0.04, 0.035};
        System.out.println("generators sorted by E (first 25): k, P(k), E(k), centres, k mod 5,7,11,13");
        Integer[] idx = new Integer[N]; for (int i = 0; i < N; i++) idx[i] = i;
        Arrays.sort(idx, (a, b) -> Double.compare(E[a], E[b]));
        for (int j = 0; j < Math.min(25, N); j++) { int i = idx[j]; long k = L.get(i);
            System.out.printf("  k=%d P=%.5f E=%.5f c=(%d,%d) mod5,7,11,13=%d,%d,%d,%d%n", k, PL.get(i), E[i], c2[i], c3[i], k % 5, k % 7, k % 11, k % 13); }
        System.out.println();
        for (double lv : levels) {
            int cnt = 0; for (int i = 0; i < N; i++) if (E[i] < lv) cnt++;
            System.out.printf("level E<%.2f: generators=%d%n", lv, cnt);
            if (cnt == 0) continue;
            // residues mod p
            for (int p : new int[]{5, 7, 11, 13}) {
                int[] h = new int[p]; for (int i = 0; i < N; i++) if (E[i] < lv) h[(int) (L.get(i) % p)]++;
                System.out.println("   residues mod " + p + ": " + Arrays.toString(h));
            }
            for (int xi = 0; xi < xs.length; xi++) {
                double mx = 0, sum = 0; int arg = -1; double minRatioZero = 0;
                for (int i = 0; i < N; i++) if (E[i] < lv) {
                    double a = kx(L.get(i), xs[xi]); double ratio = a / E[i]; sum += ratio; if (ratio > mx) { mx = ratio; arg = i; }
                }
                System.out.printf("   x=%-9s max ||kx||/E = %8.3f  mean = %8.3f%n", names[xi], mx, sum / cnt);
            }
        }
    }
}
