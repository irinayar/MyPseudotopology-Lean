import java.util.*;

/** Exp8: exact version of Exp6/Exp7. delta = a/b is an exact rational; every comparison is done in integer arithmetic:
 *  ||k/q|| < a/b  <=>  b*min(r, q-r) < a*q   with r = k mod q.
 *  Usage: java Exp8 K a b p1 p2 ...   (checks multiples of prod(p_i) up to K; requires delta <= 1/p_i for all i)
 *         java Exp8 K a b nofilter p1 p2 ...   (checks every k <= K; slow, used to cross-check Lemma 2.1(4)) */
public class Exp8 {
    static long gcdL(long x, long y) { while (y != 0) { long t = x % y; x = y; y = t; } return x; }

    // exact test: is sup_n ||k / base^(n^2)|| < a/b ?
    static boolean small(long k, long base, long a, long b) {
        for (long n = 1; ; n++) {
            long e = n * n; long q = 1;
            for (long i = 0; i < e; i++) q = Math.multiplyExact(q, base);
            long r = k % q; long s = Math.min(r, q - r);
            if (Math.multiplyExact(b, s) >= Math.multiplyExact(a, q)) return false;
            if (q > 2 * k) return true;
        }
    }

    public static void main(String[] args) {
        long K = Long.parseLong(args[0]), a = Long.parseLong(args[1]), b = Long.parseLong(args[2]);
        int idx = 3; boolean filter = true;
        if (args[idx].equals("nofilter")) { filter = false; idx++; }
        int r = args.length - idx; long[] S = new long[r]; long prod = 1;
        for (int i = 0; i < r; i++) { S[i] = Long.parseLong(args[idx + i]); prod *= S[i]; }
        if (filter) for (long l : S) if (a * l > b) throw new IllegalArgumentException("need delta <= 1/l");
        long step = filter ? prod : 1; long count = 0, g = 0, nonmult = 0;
        List<Long> first = new ArrayList<>();
        for (long k = step; k <= K; k += step) {
            boolean ok = true;
            for (long l : S) if (!small(k, l, a, b)) { ok = false; break; }
            if (!ok) continue;
            count++; g = gcdL(g, k); if (k % prod != 0) nonmult++;
            if (first.size() < 8) first.add(k);
        }
        System.out.println("S=" + Arrays.toString(S) + " delta=" + a + "/" + b + " K=" + K + " filter=" + filter + " count=" + count + " gcd=" + g + " nonmultiples_of_s=" + nonmult + " first=" + first);
    }
}
