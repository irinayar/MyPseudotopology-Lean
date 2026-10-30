import java.math.*;
import java.util.*;
import java.io.*;

/** Exp13: re-run of Exp12 with (i) high-precision character values (BigDecimal, 80 digits; rationals exact),
 *  (ii) separate reporting of mean ||kx|| and mean ||kx||/E, (iii) the generator list saved to a file,
 *  (iv) exact rational E for r=1/2 (E as a fraction numerator/denominator in BigInteger, then compared via double only for sorting).
 *  Usage: java Exp13 K T0 outfile.csv   (r = 1/2 fixed; the tail cutoff is proved for r=1/2 only) */
public class Exp13 {
    static final long[] BASES = {2, 3};
    static final MathContext MC = new MathContext(80);

    static double pk(long k, double stop) {
        double m = 0;
        for (long base : BASES) {
            for (long n = 1; ; n++) {
                long q = 1; boolean big = false;
                for (long i = 0; i < n * n; i++) { if (q > Long.MAX_VALUE / base) { big = true; break; } q *= base; }
                double t = 0;
                if (!big) { long r = k % q; long s = Math.min(r, q - r); t = (double) s / (double) q; }
                if (t > m) m = t;
                if (m >= stop) return m;
                if (big || q > 2 * k) break;
            }
        }
        return m;
    }

    static BigDecimal frac(BigDecimal v) { return v.subtract(new BigDecimal(v.setScale(0, RoundingMode.FLOOR).toBigInteger())); }
    static BigDecimal nrm(BigDecimal v) { BigDecimal f = frac(v); BigDecimal g = BigDecimal.ONE.subtract(f); return f.compareTo(g) < 0 ? f : g; }

    public static void main(String[] args) throws Exception {
        long K = Long.parseLong(args[0]); double T0 = Double.parseDouble(args[1]);
        ArrayList<Long> L = new ArrayList<>();
        for (long k = 6; k <= K; k += 6) if (pk(k, T0) < T0) L.add(k);
        int N = L.size();
        System.out.println("K=" + K + " T0=" + T0 + " count=" + N);
        // exact E with r=1/2: E = max over l,n of (s/q) * 2^{|n-P|}; use BigInteger fractions num/den
        BigInteger[] En = new BigInteger[N], Ed = new BigInteger[N]; double[] E = new double[N];
        for (int i = 0; i < N; i++) {
            long k = L.get(i); BigInteger bestN = null, bestD = null;
            ArrayList<BigInteger[]> sc2 = new ArrayList<>(), sc3 = new ArrayList<>(); // {s, q}
            for (int bi = 0; bi < 2; bi++) {
                BigInteger base = BigInteger.valueOf(BASES[bi]);
                for (int n = 1; ; n++) {
                    BigInteger q = base.pow(n * n); BigInteger kk = BigInteger.valueOf(k);
                    BigInteger r = kk.mod(q); BigInteger s = r.min(q.subtract(r));
                    (bi == 0 ? sc2 : sc3).add(new BigInteger[]{s, q});
                    if (q.compareTo(kk.shiftLeft(1)) > 0) break;
                }
            }
            for (int P2 = 1; P2 <= 9; P2++) for (int P3 = 1; P3 <= 9; P3++) {
                BigInteger eN = BigInteger.ZERO, eD = BigInteger.ONE;
                for (int bi = 0; bi < 2; bi++) {
                    ArrayList<BigInteger[]> sc = bi == 0 ? sc2 : sc3; int P = bi == 0 ? P2 : P3;
                    for (int j = 0; j < sc.size(); j++) {
                        int d = (j + 1) - P; BigInteger num = sc.get(j)[0], den = sc.get(j)[1];
                        num = num.shiftLeft(Math.abs(d)); // weight 2^{|n-P|}
                        // compare num/den with eN/eD
                        if (num.multiply(eD).compareTo(eN.multiply(den)) > 0) { eN = num; eD = den; }
                    }
                }
                if (bestN == null || eN.multiply(bestD).compareTo(bestN.multiply(eD)) < 0) { bestN = eN; bestD = eD; }
            }
            En[i] = bestN; Ed[i] = bestD; E[i] = new BigDecimal(bestN).divide(new BigDecimal(bestD), MC).doubleValue();
        }
        try (PrintWriter pw = new PrintWriter(args[2])) {
            pw.println("k,E_num,E_den,E");
            for (int i = 0; i < N; i++) pw.println(L.get(i) + "," + En[i] + "," + Ed[i] + "," + E[i]);
        }
        String[] names = {"sqrt2-1", "phi-1", "pi-3", "e-2", "ln2", "1/5", "2/5", "1/7", "1/11", "1/13", "1/25", "1/4", "1/3", "5/12", "1/9"};
        BigDecimal sqrt2 = new BigDecimal(2).sqrt(MC), sqrt5 = new BigDecimal(5).sqrt(MC);
        BigDecimal[] xs = new BigDecimal[15];
        xs[0] = sqrt2.subtract(BigDecimal.ONE, MC); xs[1] = BigDecimal.ONE.add(sqrt5, MC).divide(new BigDecimal(2), MC).subtract(BigDecimal.ONE, MC);
        xs[2] = new BigDecimal("0.14159265358979323846264338327950288419716939937510582097494459230781640628620899");
        xs[3] = new BigDecimal("0.71828182845904523536028747135266249775724709369995957496696762772407663035354759");
        xs[4] = new BigDecimal("0.69314718055994530941723212145817656807550013436025525412068000949339362196969471");
        int[][] rat = {{1, 5}, {2, 5}, {1, 7}, {1, 11}, {1, 13}, {1, 25}, {1, 4}, {1, 3}, {5, 12}, {1, 9}};
        for (int i = 0; i < 10; i++) xs[5 + i] = new BigDecimal(rat[i][0]).divide(new BigDecimal(rat[i][1]), MC);
        double[] levels = {0.12, 0.10, 0.08, 0.07, 0.06, 0.05};
        for (double lv : levels) {
            int cnt = 0; for (int i = 0; i < N; i++) if (E[i] < lv) cnt++;
            System.out.printf("level E<%.2f: generators=%d%n", lv, cnt);
            for (int xi = 0; xi < 15; xi++) {
                double mx = 0, sumR = 0, sumN = 0, minN = 1;
                for (int i = 0; i < N; i++) if (E[i] < lv) {
                    BigDecimal a;
                    if (xi >= 5) { int[] pq = rat[xi - 5]; BigInteger num = BigInteger.valueOf(L.get(i)).multiply(BigInteger.valueOf(pq[0])).mod(BigInteger.valueOf(pq[1]));
                        long nn = Math.min(num.longValue(), pq[1] - num.longValue()); a = new BigDecimal(nn).divide(new BigDecimal(pq[1]), MC); }
                    else a = nrm(new BigDecimal(L.get(i)).multiply(xs[xi], MC));
                    double ad = a.doubleValue(); double ratio = ad / E[i];
                    sumN += ad; sumR += ratio; if (ratio > mx) mx = ratio; if (ad < minN) minN = ad;
                }
                System.out.printf("   x=%-8s max ratio=%8.3f  mean ratio=%8.3f  mean ||kx||=%.4f  min ||kx||=%.5f%n", names[xi], mx, sumR / cnt, sumN / cnt, minN);
            }
        }
    }
}
