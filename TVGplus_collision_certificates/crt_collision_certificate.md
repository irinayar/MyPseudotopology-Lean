# Finite collision certificates for smaller radii

2026-11-09, America/Phoenix. Exact arithmetic outside Lean.

For the binary and ternary balls of radius \(1/60\) in \([0,X]\), at \(X=300000000000000000\), the exact sizes and raw collision energy are

$$
N_2=852609713,\qquad N_3=5001301139,\qquad
E=48428383056151506507.
$$

The normalized collision energy is approximately \(1.59802900357616\). There are 9088 positive candidate shifts in both relaxed balls of radius \(1/30\), of which 2693 contribute a positive product of overlap counts.

Write \(V=A-B\), with \(A\) the ternary ball and \(B\) the binary ball. Cauchy–Schwarz gives \(|V|\ge\lceil (N_2N_3)^2/E\rceil\). For any integer \(t\) with

$$
|t|\le 2\left\lceil\frac{(N_2N_3)^2}{E}\right\rceil-(2X+1)-1
=150925044110321510,
$$

the two sets \(V\) and \(V+t\) intersect. Their union lies in an interval of \(2X+1+|t|\) integers, fewer than twice the lower bound for \(|V|\). Writing \(t=(a'-b')-(a-b)\) and \(k=a'-a\), subadditivity gives \(|k|\le X\), \(P_3(k)<1/30\), and \(P_2(k-t)<1/30\). This extends the finite interval certificate at radius \(1/20\) in v32 to a smaller radius. The uniform shifted-height bound remains open.

## Exact enumeration

For each prime, choose a prefix of the relaxed tests. Starting from zero, lift each balanced residue by multiples of the preceding period, taking only the multiples in the next allowed centered interval. The strict inequality at an integer radius denominator is implemented with the integer endpoint \(\lfloor(q-1)/D\rfloor\).

Let \(Q_2,Q_3\) be the two prefix periods. For each allowed binary residue \(x\), a candidate has the form \(x+jQ_2\) with \(0\le j\le\lfloor(X-x)/Q_2\rfloor\). If \(y\) is its ternary residue, \(j\) is congruent to \((y-x)Q_2^{-1}\) modulo \(Q_3\). Sort the transformed ternary residues \(yQ_2^{-1}\bmod Q_3\) once. Binary searches in this list, translated by full periods as needed, enumerate precisely the allowed \(j\) in that finite interval. Distinct binary residues and distinct ternary classes within each translated interval give distinct integers. Test the remaining relaxed coordinates with periods at most \(30X\), which suffices because the larger periods automatically pass.

The triangle inequality puts every shift with a positive overlap in both original balls in this candidate set. For each candidate use the existing exact pair recursion in \(\texttt{JA\_pair\_recursion.py}\) at denominator 60. At each level the local pair condition is the intersection of the centered residue interval with its shift. Counting full periods and recursively clipping the residual intervals gives the exact overlap. The zero term is \(N_2N_3\), and each positive shift contributes twice the product of the two counts. The implementation is \(\texttt{crt\_collision\_certificate.py}\) in this directory. It reproduces the published denominator-40 certificate at height \(10^{15}\), including both positive-shift counts and its exact energy.

The binary/ternary prefix levels (6,4) and (5,5) give identical counts and energy for the new certificate. At the same radius the normalized energy is approximately 3.16569 at height \(10^{16}\) and 2.04956 at height \(10^{18}\). Those two heights fail the global threshold of two, so the finite certificate depends on the height choice.

## The actual difference interval gives a certificate at radius one thirty-fifth

The diameter of the difference set is exactly \(U_2+U_3\), where \(U_p\) is the maximum in the original one-prime ball. Both balls contain zero. A binary search with the exact prefix counter finds \(U_p\) by locating the first height at which the count attains its final value. Replacing the generic interval length \(2X+1\) by the actual length \(U_2+U_3+1\) improves the certified range to

$$
2\left\lceil\frac{(N_2N_3)^2}{E}\right\rceil-U_2-U_3-2.
$$

At original radius \(1/70\) and \(X=263524915338707879\), the exact values are

$$
N_2=292308863,\qquad N_3=1884840395,\qquad E=1432952605922554617,
$$

$$
U_2=263468619353489920,\qquad U_3=152238287575628928.
$$

Both choices of prefix levels reproduce the 575 positive candidates, 325 positive products and the same exact energy. The interval calculation certifies \(|t|\le7966590582731556\) at radius \(1/35\) and height at most \(X\). The normalization based on the full interval is approximately \(2.488\), so the full-interval test at this height yields no range. At original radius \(1/64\) and height \(288230376151711743\), the actual interval similarly certifies \(|t|\le79688670312494094\) at radius \(1/32\). These are finite statements. They do not provide the uniform shifted-height estimate.

The CRT candidate set also matched direct enumeration in three small cases, and the raw energy matched direct pair enumeration in two of them.

## Whole-bin lower bounds give a certificate at radius one thirty-sixth

At original radius \(1/72\) and \(X=256204778801521549\), the exact energy is \(1075188141959408680\), with binary count \(265217153\) and ternary count \(1724089574\). Both CRT prefixes give 498 positive candidates and 276 positive products. The full-interval and actual-interval versions of the global certificate both give a negative range at this height.

Partition the nonnegative integer axis into bins of width \(w=125099989649181\). Obtain the population of each bin for each ball by differences of exact prefix counts. If two bins have indices \(i,j\), their pair differences lie between \((i-j)w-w+1\) and \((i-j)w+w-1\), inclusive. For the equal-width difference blocks \([sBw,(s+1)Bw-1]\), with \(B=384\), count the entire product of the two bin populations if \(sB<i-j<(s+1)B\). Omit the boundary classes. This gives a certified lower mass \(M_s^-\) for each difference block. Blocks with zero lower mass may be included with zero contribution.

The resulting exact sum is

$$
2\sum_s (M_s^-)^2=55597770828349998389545436769417814.
$$

The block argument of v32 gives a witness for every integer \(|t|\le T\) whenever this sum exceeds \(E(Bw+T)\). Taking \(T=3671410527295474\) satisfies the strict inequality. Thus at radius \(1/36\) every integer target in that range has a signed witness of height at most \(256204778801521549\). This certificate uses conservative lower masses, so it needs no approximation of the difference distribution.
