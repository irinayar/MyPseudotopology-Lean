import java.util.*;

/** Exp6: B_delta for a general finite set S of primes: P_S(k) = max over l in S of sup_n ||k / l^(n^2)||.
 *  Usage: java Exp6 K delta p1 p2 ...  (primes of S).  Prints the count of multiples k <= K of prod(S) with P_S(k) < delta
 *  and, for several primes p outside S, the least element of B_delta not divisible by p. */
public class Exp7 {
    static double pBase(long k, int base, double stopAbove) {
        double sup = 0;
        for (int n = 1; ; n++) {
            long e = (long) n * n;
            long m = 1;
            for (long i = 0; i < e; i++) {
                if (m > (4_000_000_000_000_000_000L) / base) { double v = (double) k / Math.pow(base, e); return Math.max(sup, v); }
                m *= base;
            }
            long r = k % m;
            double d = (double) Math.min(r, m - r) / (double) m;
            if (d > sup) sup = d;
            if (sup >= stopAbove) return sup;
            if (m > 2 * k) return sup;
        }
    }

    static long gcdL(long a, long b) { while (b != 0) { long t = a % b; a = b; b = t; } return a; }
    public static void main(String[] args) {
        long K = Long.parseLong(args[0]);
        double delta = Double.parseDouble(args[1]);
        int[] S = new int[args.length - 2];
        long prod = 1;
        for (int i = 2; i < args.length; i++) { S[i - 2] = Integer.parseInt(args[i]); prod *= S[i - 2]; }
        for (int l : S) if (delta > 1.0 / l) throw new IllegalArgumentException("need delta <= 1/l for the n=1 shortcut");
        int[] test = {2, 3, 5, 7, 11, 13, 17, 19, 23};
        List<Integer> outside = new ArrayList<>();
        for (int p : test) { boolean in = false; for (int l : S) if (l == p) in = true; if (!in) outside.add(p); }
        long[] firstNot = new long[outside.size()];
        long count = 0; long gg = 0; List<Long> first = new ArrayList<>();
        for (long k = prod; k <= K; k += prod) {
            boolean ok = true;
            for (int l : S) { if (pBase(k, l, delta) >= delta) { ok = false; break; } }
            if (!ok) continue;
            count++; gg = gcdL(gg, k);
            if (first.size() < 8) first.add(k);
            for (int i = 0; i < outside.size(); i++) if (firstNot[i] == 0 && k % outside.get(i) != 0) firstNot[i] = k;
        }
        StringBuilder sb = new StringBuilder();
        sb.append("S=" + Arrays.toString(S) + " delta=" + delta + " K=" + K + " gcd=" + gg + " count=" + count + " first=" + first + "\n  least k not divisible by p:");
        for (int i = 0; i < outside.size(); i++) sb.append(" p=" + outside.get(i) + ":" + (firstNot[i] == 0 ? "none" : firstNot[i]));
        System.out.println(sb);
    }
}
