# Numerical test of TVGadd-v4 Theorem 8.1 (mixed-prime character group)

Code: `Exp1.java` (density of B_delta in [0,N]), `Exp1b.java` (list of elements), `Exp2.java` (covering counts, Parseval sharpness),
`Exp3.java` (the exceptional set K' and test alphas), `Exp4.java` (crossover N).  Run with `javac *.java; java Exp1` etc. (Java 17).
Notation: P(k) = max_{l in {2,3}} sup_n || k / l^(n^2) ||,  B_delta = {k : P(k) < delta},  A_N = B_delta ∩ [0,N],
K' = {alpha : ||k alpha|| <= 1/8 for all k in A_N}  (the superset of K_eps that the proof actually covers, delta = eps/2).

## 1. How big are the integer sets?  (Exp1, Exp1b)
count(B_delta ∩ [0,N]) -- the proved bound is (N+1)/L^(d_N), L = floor(1/delta)+1.

| delta | N=10^3 | 10^4 | 10^5 | 10^6 | 10^7 | 10^8 |
|---|---|---|---|---|---|---|
| 0.40 | 281 | 2222 | 17683 | 180455 | 1797748 | 11786553 |
| 0.30 | 41 | 230 | 1380 | 14163 | 140382 | 504854 |
| 0.20 | 11 | 41 | 161 | 1660 | 11071 | 21949 |
| 0.10 | 2 | 4 | 8 | 34 | 112 | 112 |
| 0.05 | 1 | 1 | 1 | 6 | 9 | 9 |

* For delta = 0.1 there is NO new element between 3.3e6 and 1e8: B_0.1 starts 0, 480, 1056, 1536, 59376, ... (multiples of 48),
  112 elements below 1e8, all <= 3345456.  For delta = 0.05: 0, 392688, 393744, 394224, 786432, 787968, 1180656, 1181712, 1574400.
* The proved lower bound is satisfied but is < 1 integer for every N tested with delta <= 0.2.
* Where is the bound informative?  (Exp4)  Covering bound 400 L^d below the total number 100N of grid cells:
  delta=0.4: N >= 10^4.9;  0.3: 10^6.0;  0.2: 10^9.2;  0.1: 10^15.2;  0.05: 10^21.8.
  Density >= 1/sqrt(N) guaranteed only for N >= 10^11.5 (0.4), 10^18 (0.3), 10^28 (0.2), 10^52 (0.1), 10^82 (0.05).
  So "N^(1-o(1))" is a genuinely asymptotic statement: o(1) = O(sqrt(log L / log N)) is not small at any computable N.

## 2. Does the covering bound locate good/bad lattice generators?  (Exp2, Exp3)  delta = 0.2 (eps = 0.4), M = 100N grid cells
| N | |A_N| | proof grid cells G (Q >= |A|^2/4) | Parseval bound 4M/|A| | paper bound 400 L^d | true cells of K' | measure{|S_A| >= |A|/2} | Chebyshev 4/|A| |
|---|---|---|---|---|---|---|---|
| 2000 | 21 | 8666 | 38095 | 1.1e8 | 148-176 | 0.0433 | 0.190 |
| 20000 | 41 | 46290 | 195122 | 4.0e9 | 788-920 | 0.0232 | 0.098 |

* The final bound 400 L^d exceeds the number M of cells (vacuous) at these N; the Parseval step itself is within a factor ~4 of G,
  but the true exceptional set K' is 50-60 times smaller than G.
* Structure of K' at N = 20000: 19 clusters, each centred (to 1e-7) on a {2,3}-smooth rational:
  0, 1/6, 1/3, 1/2, 2/3, 5/6 (width ~7e-5) and u/16, odd u/48 (width ~3e-6).  This is exactly the dyadic/triadic picture
  Z[1/6]/Z ⊆ H of Theorem 8.1; there is no other exceptional alpha.
* Weyl average |S_A(alpha)|/|A| (1 = all frequencies aligned):  alpha = 0, 1/2, 1/3, 1/6: 1.000;  1/4: 0.22;  1/9: 0.11;
  1/5: 0.058; 1/7: 0.053; (sqrt5-1)/2: 0.114; sqrt2-1: 0.078; e-2: 0.070; pi-3: 0.043; random alpha: mean 0.108 (1/sqrt|A| = 0.156).
  Classical good generators (bounded partial quotients) are at the random level; nothing beats them.

## Conclusion
* Point 1: the integer sets B_delta are real but extremely sparse and highly structured (multiples of 48, ...); the asymptotic
  density statement is not visible at computable N.
* Point 2: the covering bound does not produce lattice generators; it only says the bad parameters are a thin set, and numerically the
  bad set is the explicit list of low-height {2,3}-smooth rationals.  Avoiding neighbourhoods of such rationals is the usual
  Diophantine criterion and gives no gain over bounded-partial-quotient generators.
* A possible genuine use: frequency sets with this 2-adic/3-adic structure (digit-aligned, e.g. in Walsh/digital-type spectra) --
  there the generators to avoid are exactly the smooth rationals.  This is a hypothesis, not tested here.
