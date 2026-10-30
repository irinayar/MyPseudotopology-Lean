import java.util.*;

/** Exp5: the sets B_delta = {k >= 1 : P(k) < delta}, P(k) = max( sup_n ||k/2^(n^2)||, sup_n ||k/3^(n^2)|| ).
 *  Prints counts up to powers of ten and, for small primes p, the least k in B_delta not divisible by p. */
public class Exp5 {
    // distance of k/m to the nearest integer, as a double in [0, 1/2]
    static double dist(long k, long m) {
        long r = k % m;
        long s = Math.min(r, m - r);
        return (double) s / (double) m;
    }

    // sup over n >= 1 of ||k / base^(n^2)||; for base^(n^2) > 2k the value is k/base^(n^2) and decreasing,
    // so we may stop after the first n with base^(n^2) > k.
    static double pBase(long k, int base, double stopAbove) {
        double sup = 0;
        for (int n = 1; ; n++) {
            long e = (long) n * n;
            // compute base^e capped at about 4e18
            long m = 1; boolean big = false;
            for (long i = 0; i < e; i++) {
                if (m > Long.MAX_VALUE / base) { big = true; break; }
                m *= base;
            }
            if (big) { double v = (double) k / Math.pow(base, e); if (v > sup) sup = v; return sup; }
            double d = dist(k, m);
            if (d > sup) sup = d;
            if (sup >= stopAbove) return sup;
            if (m > 2 * k) return sup;
        }
    }

    static double P(long k, double stopAbove) {
        double a = pBase(k, 2, stopAbove);
        if (a >= stopAbove) return a;
        double b = pBase(k, 3, stopAbove);
        return Math.max(a, b);
    }

    public static void main(String[] args) {
        long K = args.length > 0 ? Long.parseLong(args[0]) : 1000000000L;
        double[] deltas = {0.30, 0.25, 0.20, 0.15, 0.10};
        int[] primes = {5, 7, 11, 13, 17, 19, 23};
        for (double delta : deltas) {
            long[] firstNot = new long[primes.length];
            long count = 0; long nextPow = 10;
            StringBuilder cnt = new StringBuilder();
            List<Long> first = new ArrayList<>();
            for (long k = 1; k <= K; k++) {
                if ((k & 1) != 0) continue;           // n = 1 for base 2 forces k even whenever delta < 1/2
                if (k % 3 != 0) continue;             // n = 1 for base 3 forces 3 | k whenever delta < 1/3
                if (P(k, delta) >= delta) continue;
                count++;
                if (first.size() < 12) first.add(k);
                for (int i = 0; i < primes.length; i++) if (firstNot[i] == 0 && k % primes[i] != 0) firstNot[i] = k;
                while (k >= nextPow) { cnt.append(String.format(" 10^%d:%d", (int) Math.round(Math.log10(nextPow)), count - 0)); nextPow *= 10; }
            }
            System.out.println("delta=" + delta + "  |B_delta ∩ [1,K]|=" + count);
            System.out.println("  first elements: " + first);
            StringBuilder sb = new StringBuilder("  least k in B_delta not divisible by p:");
            for (int i = 0; i < primes.length; i++) sb.append(" p=" + primes[i] + ":" + (firstNot[i] == 0 ? "none<=K" : firstNot[i]));
            System.out.println(sb);
        }
    }
}
