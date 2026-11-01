# Lean formalization of joint approximation (JA): status and roadmap

Date: 30 October 2026. Prepared by Claude at the user's request ("Try to Lean-proof JA in full").
Statement targeted: for every `delta > 0` there is an integer `k` with `P_3 k < delta` and `P_2 (k-1) < delta`, where `P_p k = sup_n ‖k / p^(n^2)‖`.

## Short answer

A complete machine-checked proof of JA is **not achievable in one session**, and it is not a matter of effort alone: the proof of TVGaddmore (v27) uses two results that Mathlib does not contain.

1. **Matveev's lower bound for linear forms in logarithms** (used for the close pairs of periods, Section "normalized product"). Mathlib has no Baker-type theorem. Formalizing even the two-logarithm case from scratch is a research project of its own. The only honest ways to include it are (a) as an explicit *hypothesis* of the final theorem, so the result reads "Matveev's bound implies JA", or (b) as a separate long-term formalization.
2. **Character separation on a compact abelian group** (used to turn "the quotient `Q` is compact and has trivial dual" into `Q = 0`, Theorem on the quotient obstruction). Mathlib has finite abelian Pontryagin duality, not the compact case.

Everything else is elementary but long: several thousand lines of Lean (windows and tails, finite Fourier analysis, a Fejér-kernel estimate, buffered heights, the random-translation averaging, the packing and the assembly). These are my estimates, not measured.

## Status by component

Legend: **done** = compiled, standard axioms only; **todo-elementary** = formalizable with current Mathlib, not yet done; **blocked** = needs a result missing from Mathlib.

| # | Component (v27 location) | Status |
|---|---|---|
| 1 | Far-field recursion, geometric specialization | done (`MixedPrimeProduct`: `farfield`, `farfield_geom`) |
| 2 | Center maximality of nonnegative cosine series (finite and infinite) | done (`center_max`; `MixedPrimeAnalytic.cosine_series_center_max`) |
| 3 | Product telescoping; bounded product with exceptions; lower product bound | done (`telescope`; `product_bound_with_exceptions`; `relative_mass_product_bounds`) |
| 4 | Fourier nonnegativity of the discrete window kernel (autocorrelation identity) | done (`autocorr`, `kernel_fourier_nonneg`) |
| 5 | Coprime two-term nonvanishing | done (`two_term_ne`) |
| 6 | Geometric sums, paired prefix sums | done (`geometric_sum_le_two`, `paired_geometric_sum`, `paired_geometric_prefix`) |
| 7 | Numerical square-level spacing; two-colour three-level span | done (`square_level_gap`, `two_colour_three_level_span`) |
| 8 | Finite packing to finite cover | done (`finite_cover_of_bounded_packing`) |
| 9 | Finite cyclic-character translation orthogonality | done (`finite_translation_orthogonality`) |
| 10 | Weighted Cauchy-Schwarz for difference sets; disjoint-translate counting | done (`JAEnergy`: `sum_rep`, `cs_difference`, `cs_difference_interval`, `card_sq_le_card_mul_energy`, `disjoint_translates_of_not_mem`, `packing_card_le`; compiled 30 Oct 2026, standard axioms only; source at D:IrinaBackupMyPseudotopologyeancheckeancheckjaenergy.lean, not yet in the public repository) |
| 11 | Concrete window `w_D`, means `I_1, I_2`, mass `B_D`, tail bound `A_D u^-3` (second differences) | todo-elementary |
| 12 | Merged-growth lemma for the actual prime-square sequences; counting of non-deep levels | **done in abstract form** (`JAMerged`: `same_chain_gap`, `merged_gap3`, `merged_gap_seq`, `merged_gap_seq_odd`, `merged_growth_exp`, `window_card_le_two`; compiled 30 Oct 2026, standard axioms only). Not done: the asymptotic statement that the non-deep window has width `O((log log X)^2)` |
| 13 | Separated-level and deep-level estimates; assembly of the normalized product | todo-elementary given 1-3, 6, 11, 12, **and the separation input of 14** |; **partial**: the uniform summability `sum t^-3 <= const` is done (`JAMerged.sum_inv_cube_le`); the factor estimates `f_i - 1 <= ...` and the final product are not done |
| 14 | Two-term separation `‖r/Q_i + s/Q_{i+1}‖ >= Q_i^-1 exp(-A log^2(2+t))` | **blocked** (Matveev) |
| 15 | Random-translation averaging and lift-mass bounds | todo-elementary (uses 9) |
| 16 | Spectral window `∫ Psi_L dnu <= 5 L^3 nu{‖t‖<=1/L}` (Fejer kernel estimates) | **partial** (`JASpectral`: `spectral_step`, `fej_eq_sq`, `fej_nonneg`, `fej_le_sq`, `fej_mul`, `fej_mul_le_four`; finite cosine sums for finitely supported measures, standard axioms only). Localization (`JALocalize`) and block summation (`JABlocks`: `fej_far`, `ann_mass`, `fej_block_sum`, `spectral_window`) are done in the finite-group form: for a nonnegative measure on `ZMod N` with real nonnegative Fourier coefficients and `m = ceil(N/L)`, `sum nu Psi_L <= 3 L^3 nu(arc(m-1))`. Not done: the transfer from the expected spectral measures of the construction to a measure on `ZMod N` |
| 17 | Buffered heights; support argument `A_p - A_p ⊂ U_{p,2/D}`; syndetic packing | **packing and assembly done** (`JAAssembly`: `card_V_ge`, `syndetic_of_dense_difference`, `syndeticW_of_dense`). Not done: the support argument itself (it depends on the actual window supports) and the abundance of buffered heights |
| 18 | Deduction JA from `W_eps` syndetic for every `eps` (quotient `Q`, completeness, total boundedness, trivial dual) | **blocked** (compact abelian character separation) unless replaced by an elementary argument |; **reduced to one explicit hypothesis**: `JAAssembly.CompactQuotientCriterion`, and `JA_of_dense_differences` (Stage A) proves JA from it together with the density input |
| 19 | Triviality of the dual of `Q` (one-prime duals + coprimality) | todo-elementary given the one-prime dual theorem (to be located in the existing library) |

## A realistic staging

* **Stage A (conditional theorem).** State JA with two explicit hypotheses `[MatveevTwoTerm]` and `[CompactMonotheticSeparates]` (each a closed `Prop`, not an axiom) and prove everything else. Components 11-13, 15-17, 19 are the work. This is the maximum that is reachable without new library theory, and it would make the structure of the proof checkable.
* **Stage B.** Replace `[CompactMonotheticSeparates]` by a proof for compact monothetic groups (Weyl-type argument), or find an elementary route from syndeticity to `J_1 = 0`.
* **Stage C.** Matveev (or a weaker Baker-type statement sufficient for primes 2 and 3).

No statement of this roadmap is a claim that JA has been verified. The article's wording ("selected abstract components have been checked ...") stays correct.

## Update, 30 October 2026 (evening)

New checked modules, all compiled by Lean 4.35.0 with Mathlib, no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`: `JAMerged`, `JAAssembly`, `JASpectral` (plus `JAEnergy`). The Stage A theorem is `JAAssembly.JA_of_dense_differences : CompactQuotientCriterion -> (forall eps > 0, DenseDifferences eps) -> JAProp`. What is still missing for a complete proof: (i) `DenseDifferences eps` for every eps (the normalized-product argument with Matveev's two-term separation, the window kernels, random translations, support argument); (ii) `CompactQuotientCriterion` (compact abelian character separation and the one-prime dual theorem).

## Update, 31 October 2026 (localization)

`JALocalize.lean` (compiled, standard axioms only): for a nonnegative measure `nu` on `ZMod N` with real nonnegative Fourier coefficients, `loc_fourier` says the translated autocorrelation of any real window has integral at most that of the untranslated one; `loc_mass` and `loc_mass_half` give: the `nu`-mass of the arc `y + {+-k : k <= m/2}` is at most twice the mass of the arc `{+-k : k < m}`, for `1 <= m <= N` (window `1_[0,m)`). This replaces the infinite Fourier series of the triangular cutoff by finite sums. Still open in component 16: the block summation over arcs, using `JASpectral.fej_le_sq` and `fej_mul_le_four`.

## Update, 31 October 2026 (block summation)

`JABlocks.lean` (compiled, standard axioms only): `fej_far` (Fejer kernel `<= N^2/(4(r+1)^2)` off the arc of radius `r`), `ann_mass` (each annulus `{+-k : jm <= k <= (j+1)m-1}` has mass `<= 4B`, from two applications of `loc_mass_half`), `fej_block_sum` (`sum nu F_L <= 3 L^2 B`, central arc `L^2 B` plus `sum_j L^2 B/j^2 <= 2 L^2 B`), `spectral_window` (`sum nu Psi_L <= 3 L^3 B` with `B = nu(arc N (m-1))`, `N <= L m`; since `arc N (m-1)` lies in `{||t|| < 1/L}` for `m = ceil(N/L)` this gives the constant 5 of `lem:weighted-spectral`). Component 16 is therefore done in the finite-group form; what is left of it is the transfer from the expected spectral measure of the construction to a measure on `ZMod N` (the nonnegative real coefficients come from `kernel_fourier_nonneg` and products of such), and the passage to the weighted energy.

## Update, 31 October 2026 (transfer to ZMod N)

`JATransfer.lean` (compiled, standard axioms only): `PD nu` (nonnegative, all Fourier coefficients real and nonnegative); `PD.conv` (preserved by convolution, via `fourier_conv`: the transform is multiplicative); `PD.smul`; `kern_PD` (the kernel measure `K_w(y) = sum_r |W(r)|^2 [y = r N/Q]` of a nonnegative window `w` on `ZMod Q`, `N = Q d`, is `PD`: its coefficient at `s` is `Q * sum_x w(x) w(x+s)`, from `autocorr`); `spectral_window_conv` (for a `PD` seed and any list of `PD` factors, `nu = seed * K_1 * ... * K_k` satisfies `sum nu Psi_L <= 3 L^3 nu(arc(m-1))`, uniformly in the number of factors). Component 16 is complete in the finite-group form except for: the seed measure of the construction being `PD`, and the link to the weighted energy `lem:weighted-spectral` (normalizations `Z`, `c_{p,-}`, the restriction to `[0,X]`).

## Update, 31 October 2026 (seed PD and the weighted energy)

New checked modules (compiled, standard axioms only): `JAEnergyLink`, `JAEnergyIdentity`, `JAEnergyFinal` (and `JATransfer` with the new `kern_coef`).

* **The seed is PD**: the spectral measure `|f^|^2` of any nonnegative periodic weight is `PD` (`kern_PD`), with explicit coefficient `q * sum_{x<q} f(x) f(x+h)` (`JATransfer.kern_coef`, `JAEnergyLink.coef_pi`, `nu_cos`).
* **Weighted energy vs spectral window** (`JAEnergyLink`): `alpha_le` (incomplete periods), `total_ge` (complete periods), `energy_le_psi`, `energy_le_arc` (`E <= 3 L^3 nu(arc(m-1)) / (q2 q3)^2`), `energy_normalized` (`E <= K (T2 T3)^2`).
* **Energy identity** (`JAEnergyIdentity`): `sum_sq_rep` (`sum_d R(d)^2 = sum_h r_F(h) r_G(h)`, any finite `A`, weights) and `sum_sq_rep_energyE` (it equals `energyE` for the periodic weights on `[0,X]`).
* **Difference set** (`JAEnergyFinal`): `card_V_ge_spectral`: for supports `A_2, A_3` of the weights in `[0,X]`, `|A_3 - A_2| >= 1/K`, `K = 3 L^3 nu(arc(m-1)) / ((X+1-q2)^2 (X+1-q3)^2 (S2 S3)^2)`.

This closes the chain: spectral window -> weighted energy -> `|V_X|` lower bound (the hypothesis `hV` of `JAAssembly.syndetic_of_dense_difference`), for FIXED weights. What is still missing for `DenseDifferences eps`: (i) the expectation over the random translations (`lem:random-transfer`: expected spectral measure = seed * kernels, the mass bounds `c_{p,-} <= S/Z <= c_{p,+}`), (ii) the uniform bound `nu(arc(m-1)) <= C` (normalized product argument, component 13, needs the two-term separation), (iii) the support argument `A_p - A_p subset U_{p,2/D}` from the window supports (component 17), and the choice of the weights as a function of `eps`. Compact-quotient criterion remains a hypothesis.

## Update, 31 October 2026 (random-translation averaging, component 15)

`JARandom.lean` (compiled, standard axioms only): for a weight `f` of period `P`, a window `w` of period `Q = P alpha` and `g_tau(x) = f(x mod P - tau) w(x)`, `amp_avg`: `P * sum_{tau in ZMod P} |g^_tau(j)|^2 = sum_{l in ZMod P} |f^(l)|^2 |W^(j + alpha l)|^2` for every frequency `j in ZMod Q` (the exact averaged transfer of `lem:random-transfer`, `E_tau |a_new(j)|^2 = sum_l kappa_Q(j - alpha l) |a(l)|^2` after the normalizations); `mass_avg`: `sum_tau sum_x g_tau(x) = (sum f)(sum w)` (exact average of the total weight). The proof expands `|g^_tau|^2` as a double sum over positions, sums over `tau` to the autocorrelation of `f` (`tau_acorr`), expands it with `autocorr`, and compares `e_P(l (x mod P))` with `e_Q(alpha l x)` (`e_compat`); no Fourier inversion is used.

Still open in component 15: (i) the measure-level packaging (`E sigma_{g_tau} = P^-2 sigma_f * K_w` on `ZMod N`, with the reflection `l -> -l` and `|f^(-l)| = |f^(l)|`), which feeds `spectral_window_conv`; (ii) the mass bounds `c_{p,-} <= S/Z <= c_{p,+}` for the actual windows (they need the window sums of component 11: lift sums within two of `alpha I_1`).

## Update, 31 October 2026 (measure-level packaging, component 15)

`JAPackaging.lean` (compiled, standard axioms only): `fourier_inj` (two real functions on `ZMod N` with the same Fourier coefficients are equal); `sum_acorr_tau` (`sum_tau acorr g_tau (t) = acorr w (t) * acorr f (t mod P)`); `expected_measure` (with `Q = P alpha`, `N = Q dQ = P dP`: `(1/P) sum_tau kern N Q dQ g_tau = P^-2 * (kern N P dP f) * (kern N Q dQ w)` pointwise on `ZMod N`, i.e. the expected spectral measure of the translated lifted weight is the convolution of the seed's spectral measure with the kernel measure of the window; proved by comparing Fourier coefficients through `kern_coef`, so no reflection `l -> -l` is needed); `spectral_window_expected` (`sum_y E_tau[kern(g_tau)](y) Psi_L(y) <= 3 L^3 E_tau[kern(g_tau)](arc(m-1))` for nonnegative `f`, `w`, `m <= N <= L m`).

Component 15 is therefore done in the finite-group form, with one remaining piece: the mass bounds `c_{p,-} <= S/Z <= c_{p,+}` for the actual windows, which need the window sums of component 11 (lift sums within two of `alpha I_1`). `mass_avg` (`JARandom`) already gives the exact average of the total weight. What remains for the density input `DenseDifferences eps` is, besides component 11: the uniform central bound (component 13, two-term separation), the support argument, the choice of weights as a function of `eps`, and the compact-quotient criterion.

## Update, 31 October 2026 (realization of the shifts)

`JARealization.lean` (compiled, standard axioms only): `sum_conv` (independence: `sum_i sum_k (A_i * B_k) = (sum_i A_i) * (sum_k B_k)`), `realization`: for two independently translated lifted weights `g_a(tau_a)`, `g_b(tau_b)` (periods `P_a | Q_a | N`, `P_b | Q_b | N`, nonnegative `f_p`, `w_p`, `m <= N <= L m`, `L = X+1+Q_a+Q_b`) there are shifts `tau_a, tau_b` such that the weighted collision energy `energyE` of the pair, restricted to `[0, X]`, satisfies `E <= 3 L^3 (C_a * C_b)(arc(m-1)) / ((Q_a Q_b)^2 (P_a P_b)^2)`, `C_p = kern(f_p) * kern(w_p)`. Proof: each realization is bounded by the spectral window (`energy_le_psi`); the average over `(tau_a, tau_b)` of the realized spectral measures is `(P_a P_b)^-1 C_a * C_b` (`expected_measure`, `sum_conv`), which is PD, so `spectral_window` applies; some pair is at most the mean (`Finset.exists_le_of_sum_le`).

The elementary chain is now complete up to normalization: spectral mass of the central arc (expected measure) -> energy of one realization -> `|A_3 - A_2|` (`JAEnergyFinal.card_V_ge_spectral`, applied to the realized weights). What is missing for `DenseDifferences eps`: (1) the mass lower bounds `T_p >= ` a deterministic constant for EVERY realization (component 11: lift sums within two of `alpha I_1`, window `w_D`), needed to normalize `E` by `(T_a T_b)^2`; (2) the uniform bound on `(C_a * C_b)(arc(m-1))` (component 13: normalized product, two-term separation); (3) the support argument; (4) the compact-quotient criterion (hypothesis).

## Update, 31 October 2026 (window kernel, component 11, first part)

`JAWindow.lean` (compiled, standard axioms only): the window `wD D t = (max 0 (1 - D^2 t^2))^2` with `0 <= wD <= 1`, even, continuous, nonincreasing on `[0,inf)`, zero for `|t| >= 1/D`; `integral_wD` (`I_1 = 16/(15 D)`), `integral_wD_sq` (`I_2 = 256/(315 D)`); `half_lattice` (one-sided lattice-sum estimate for a nonincreasing `0 <= f <= 1`: `int_0^T f - h <= h sum f(p_0 + i h) <= int_0^T f + h`, `T = p_0 + k h`, `p_0 in [0,h]`); `two_sided` (even function supported in `[-R,R]`: `|h (sum_+ + sum_-) - 2 int_0^R f| <= 2h` for the lattice `{p_0 + i h} union {-(h-p_0) - i h}`); `lattice_wD`, `lattice_wD_sq` (`|h * lattice sum of w_D - 16/(15D)| <= 2h`, same for `w_D^2` with `256/(315D)`). These are the real-line forms of: `|m_Q - I_1| <= 2/Q` (step `h = 1/Q`), `K_Q(T) -> I_2/I_1^2 = 5D/7`, and the lift-sum estimate `|sum - alpha I_1| <= 2` (step `h = 1/alpha`) that gives the mass bounds `c_{p,-} <= S/Z <= c_{p,+}`.

Not done in component 11: (i) the bridge from the circle sums over `ZMod Q` (balanced representatives `valMinAbs`) to the one-sided lattice sums (index bookkeeping); (ii) the Parseval identity `K_Q(T) = Q sum w^2 / (sum w)^2` in that setting (it is `autocorr` at `t = 0`); (iii) the tail bound `sum_{|r|>u} kappa_Q(r) <= A_D u^-3` by second differences (needs `sum_x |Delta^2 w| <= V_2/Q`, i.e. a bound on the total variation of `w_D'`).

## Update, 31 October 2026 (window kernel, component 11, second part)

`JAWindowQ.lean` (compiled, standard axioms only): `wQ D Q x = wD D (x.valMinAbs / Q)` on `ZMod Q`; `wQ_eq` (`|valMinAbs| = min (val x) (Q - val x)`), `sum_fold` (fold the sum over `ZMod Q` into two one-sided lattice sums, `p_0 = 0`, `h = 1/Q`), `sum_wQ` (`|m_Q - I_1| <= 2/Q`), `sum_wQ_sq` (`|(1/Q) sum w_Q^2 - I_2| <= 2/Q`) for `D >= 3`; `parseval_Fq` (`sum_r |W^(r)|^2 = Q sum w^2`), `Fq_zero`, `norm_Fq_zero` (`kappa_Q(0) = 1`); `KQ` and `KQ_le` (`K_Q(T) <= 30 D / 7` for `D >= 3`, `Q >= 25 D`; actual bound from the sum estimates is about `0.917 D`).

Component 11 now lacks only the tail bound `sum_{|r|>u} kappa_Q(r) <= A_D u^(-3)` (second differences). Still open for JA: per-realization mass bounds, support argument, Matveev separation (13), compact-quotient criterion. JA is NOT proved in Lean.

## Update, 31 October 2026 (window kernel, component 11, third part: tail bound; component 11 complete)

`JAWindowTail.lean` (compiled, standard axioms only): `phi_second_diff` (`|phi(s+a)+phi(s-a)-2 phi(s)| <= 32 a^2`, by cases: all three points inside `[-1,1]` -> polynomial `a^2(12 s^2+2a^2-4)`; otherwise every point is within `2a` of the boundary, so `0 <= phi <= 16 a^2`); `wQ_shift` / `wQ_succ` / `wQ_pred` (shifting the balanced representative by `+-1` on `ZMod Q`, wrap-around harmless for `Q >= 25 D >= 75`); `sd_bound` (`|Delta^2 w_Q(x)| <= 32 (D/Q)^2`), `sum_sd_le` (`sum_x |Delta^2 w_Q(x)| <= 96 D / Q`, support `<= 3Q/D` points); `Fq_shift`, `Fq_lin`, `Fq_d2` (`FT(Delta^2 w)(r) = (e(-r)+e(r)-2) W^(r)`), `psi_pair`, `cos_gap` (`2-2cos(2 pi m/Q) >= 16 m^2/Q^2`), `Fq_bound` (`|W^(r)| <= 6 D Q / r~^2`), `sum_ge` (`sum w_Q >= 74 Q/(75 D)`), `kappa_le` (`kappa_Q(r) <= 37 D^4 / r~^4`), `inv4_aux`/`inv4_tail` (`sum_{k>u} k^-4 <= 1/(3u^3)`), `tail_bound` (`sum_{|r~|>u} kappa_Q(r) <= 25 D^4 / u^3`, `D >= 3`, `Q >= 25 D`, `u >= 1`).

Component 11 (window kernel) is complete: lattice sums, `K_Q(T) <= 30 D/7`, tail bound. Still open for JA: per-realization mass bounds, support argument, Matveev separation (13), compact-quotient criterion. JA is NOT proved in Lean.

## Update, 31 October 2026 (per-realization mass bounds)

`JAMass.lean` (compiled, standard axioms only): `wQ_val` (for `v = val x`, `w_Q(x) = w_D(v/Q) + w_D((v-Q)/Q)`, `D >= 2`), `fiber_sum` (the fibre of `rd : ZMod Q -> ZMod P` over `y` is `{y.val + P k : k < alpha}`, a bijection with `range alpha`), `lift_sum` (`|sum_{x : x mod P = y} w_Q(x) - alpha I_1| <= 2`, `I_1 = 16/(15 D)`, via `lattice_wD` with step `1/alpha`, start `y.val/Q`, second lattice by reflection `k -> alpha-1-k`), `mass_bounds` (for EVERY shift `tau`: `(alpha I_1 - 2) sum f <= sum_x f(x mod P - tau) w_Q(x) <= (alpha I_1 + 2) sum f`, `f >= 0`, `D >= 3`), `mass_range` (same for `sum_{x in range Q} fn g_tau x`, the quantity `S_p` of `energy_normalized` / `card_V_ge_spectral`), `mass_ge_half` (`alpha I_1 >= 4` gives `S >= (alpha I_1 / 2) sum f`), `mass_pos`.

This closes item (1) of the realization update: the energy of the realized pair can now be normalized by `(S_a S_b)^2` with a deterministic lower bound for `S_p(tau_p)` valid for the (unknown) chosen shifts. Still open for `DenseDifferences eps`: the bookkeeping that combines `realization` with these bounds, the uniform bound on `(C_a * C_b)(arc(m-1))` (component 13, Matveev two-term separation), the support argument `A_p - A_p subset U_{p,2/D}`, and the compact-quotient criterion (hypothesis). JA is NOT proved in Lean.

## Update, 31 October 2026 (constant bookkeeping: realization + mass bounds)

`JADense.lean` (compiled, standard axioms only): `card_V_ge_of_energy` (for weights `f_2, f_3` with supports `A_p` inside `[0, X]`: `energyE f_2 f_3 X <= R`, `0 < M <= T_2 T_3` (`T_p = sum_{x <= X} fn f_p x`), `R > 0` imply `M^2 / R <= |A_3 - A_2|`; same proof as `card_V_ge_spectral` with an arbitrary energy bound), `total_lower` (for EVERY shift: `T(tau) >= ((X+1-Q)/Q) (alpha I_1 - 2) sum f`), `realized_difference_bound` (data: `Q_p = P_p alpha_p`, `N = Q_p dQ_p = P_p dP_p`, `f_p >= 0` with `sum f_p > 0`, windows `wQ D_p Q_p` with `D_p >= 3`, `alpha_p I_1(D_p) > 2`, `Q_p < X+1`, `m <= N <= (X+1+Q_a+Q_b) m`, `B > 0`; conclusion: there are shifts `tau_a, tau_b` such that for all supports `A_a, A_b` inside `[0, X]` outside which the WINDOWS vanish, `((X+1-Q_a)(X+1-Q_b)(alpha_a I_a - 2)(alpha_b I_b - 2) sum f_a sum f_b P_a P_b)^2 / (3 L^3 B) <= |A_b - A_a|`, `L = X+1+Q_a+Q_b`, `B = (C_a * C_b)(arc(m-1))`, `C_p = kern f_p * kern w_p`).

For `X >> Q_a + Q_b` the prefactor is about `X`, so `|A_b - A_a| >= c X` follows once `B <= C ((alpha_a I_a - 2)(alpha_b I_b - 2) sum f_a sum f_b P_a P_b)^2` with a seed-independent constant `C` (uniform central bound, component 13). Still open for `DenseDifferences eps`: that bound (Matveev two-term separation), the support argument `A_p - A_p subset U_{p,2/D}`, the choice of weights as a function of `eps`, and the compact-quotient criterion (hypothesis). JA is NOT proved in Lean.

## Update, 31 October 2026 (support argument `A_p - A_p subset U_{p,2/D}`, component 17)

`JASupport.lean` (compiled, standard axioms only), cascade model `q_k = p^(k^2)`, `g_{k+1}(x) = g_k(x mod q_k - tau_k) w_{q_{k+1}}(x)` (hypothesis `hrec`, arbitrary shifts): `wQ_ne_zero` (`w_Q(x) != 0` implies `|x~| < Q/D`), `window_diff` (`w_Q` nonzero at `a, a'` implies `||(a-a')/Q|| < 2/D`), `support_diff` (induction on `L`: `g_L(a) != 0 != g_L(a')` implies `||(a-a')/q_i|| < 2/D` for EVERY level `1 <= i <= L`; the shifts cancel in the difference), `exists_lt_bound` (a finite family of values `< r` has a common bound `< r`), `support_Pn` (if `D X < p^((L+1)^2)` and `a, a'` in `[0, X]` lie in the support, then `Pn (sqScales p) (a - a') < 2/D`: levels `n <= L` by `support_diff`, levels `n > L` by `||(a-a')/p^(n^2)|| <= X/p^((L+1)^2) < 1/D`), `suppSet` / `suppSet_subset` / `suppSet_vanish` / `mem_suppSet`, `suppSet_diff_Pn` (`A = suppSet (g L) X`: `A subset Aset X`, `g_L` vanishes outside `A`, and `A - A subset U_{p,2/D}`).

`JADense.realized_difference_bound_supp`: the bound of `realized_difference_bound` with supports only required to contain the support of the REALIZED weights `g(tau)` (fits `suppSet`).

Remaining caveat: `realized_difference_bound` takes the seed `f_p` (previous-level weight) as given and produces only the LAST shift by averaging; `support_diff` is valid for arbitrary shifts, but the energy bound for the whole cascade needs the product formula (component 13). Still open for `DenseDifferences eps`: the uniform central bound on `B` (Matveev), the choice of weights as a function of `eps` with buffered heights, and the compact-quotient criterion (hypothesis). JA is NOT proved in Lean.

## Update, 31 October 2026 (DenseDifferences assembly; conditional)

`JAFinal.lean` (compiled, standard axioms only). Proved: `cascadeG` (`g_0 = 1`, `g_{k+1}(x) = g_k(x mod q_k - tau_k) w_{q_{k+1}}(x)`, `q_k = p^(k^2)`, arbitrary shifts), `cascadeG_nonneg`, `Pn_of_levels`, `support_last` (support argument for the last level with an arbitrary last shift), `centralMass` (def: `(C_a * C_b)(arc(m-1))` on `ZMod (Q_a Q_b)`), `centralMass_pos`, `final_ineq` (`(2X+1)/(64 C) <= ((X+1-Q_a)(X+1-Q_b) Y)^2 / (3 L^3 B)` for `4 Q_p <= X`, `B <= C Y^2`; tight), `dense_step` (one height: seeds + bound on the central mass + difference properties of the supports give `A_2, A_3` in `[0,X]` with `P_p < eps` on differences and `|A_3 - A_2| >= (2X+1)/(64 C)`, via `JADense.realized_difference_bound_supp`), `denseDifferences_of_heightBounds` (`HeightBound D C X` for arbitrarily large `X`, `3 <= D`, `2/D <= eps`, `C > 0` gives `DenseDifferences eps` with `c = 1/(64 C)`), `JA_of_heightBounds` (`CompactQuotientCriterion` + height bounds at every precision give `JAProp`).

`HeightBound D C X` is an explicit HYPOTHESIS (not proved): levels `n_2, n_3` and earlier-level shifts with the last scales the largest `p^(n^2) <= D X`, buffered (`4 Q_p <= X`), `alpha_p I_1 > 2`, positive seed mass, and for some `m` with `Q_a Q_b <= (X+1+Q_a+Q_b) m` the bound `B <= C ((alpha_a I_a - 2)(alpha_b I_b - 2) S_a S_b P_a P_b)^2`. Not formalized behind it: (a) arbitrarily large buffered heights (log counting for 2 and 3); (b) positive seed mass at coarse levels; (c) the uniform central bound (component 13, Matveev) together with its passage from the expectation over ALL earlier shifts to one choice (a multi-level realization theorem: average over all shifts, spectral window on the averaged measure, selection compatible with the mass lower bounds). JA is NOT proved in Lean.

## Update, 31 October 2026 (multi-level realization; deterministic height hypothesis)

`JAMulti.lean` (compiled, standard axioms only): `Chain` (scales `q_0 | q_1 | ...`, windows `w_k`), `Chain.weights` (`g_0 = seed`, `g_{k+1}(x) = g_k(x mod q_k - tau_k) w_{k+1}(x)`), `weights_cons`, `kernq`, `Mavg` (iterated expected kernel measure: `Mavg_{n+1}(s) = Mavg_n^{tail}((1/q_0^2) (s * kernq(w_1)))`), `Mavg_sum` / `Mavg_smul` (linear in the seed measure), `Mavg_PD`, `Phi` (`sum_x (nu_a * nu_b)(x) Psi_L(x)`), `Phi_sum`, `Phi_sum_left`, `Phi_smul`, `Phi_smul_left`, `Phi_comm`, `Claim`, `Claim_step` (peel the first level of one chain: average over the first shift is `P` times the next-level functional, by `expected_measure` and linearity; pigeonhole), `Claim_swap`, `multi_exists` (for ANY seeds and chains of depths `n_a, n_b` there are shifts at ALL levels with `Phi(kern g^a, kern g^b) <= Phi(Mavg_a, Mavg_b)`).

`JAMulti2.lean` (compiled, standard axioms only): `multi_realization` (`E <= 3 L^3 (Mavg_a * Mavg_b)(arc(m-1)) / (Q_a Q_b)^2`), `Mavg_nonneg_pos0` (positivity of the central mass), `mass_chain` / `total_lower_chain` (for EVERY choice of shifts the total mass of the `n`-th weight is at least `prod_{k<n}(alpha_k I_1 - 2) * sum seed`, and over `[0, X]` at least `(X+1-Q)/Q` times that), `support_chain` (seed supported at `0`, windows `w_{q_k}`: `q_0 | a - a'` and `||(a-a')/q_i|| < 2/D` for `1 <= i <= n`, arbitrary shifts), `dense_step_multi` (`DenseDifferences` at one height from the deterministic bound `(Mavg_a * Mavg_b)(arc(m-1)) <= C (prod_a (alpha I_1 - 2) prod_b (alpha I_1 - 2) sum seed_a sum seed_b)^2`).

`JAFinal2.lean` (compiled, standard axioms only): `chainP` (`q_k = p^((s+k)^2)`, windows `w_{q_k}`), `deltaSeed` (indicator of `0`; handles the coarse scales: differences are multiples of `p^(s^2)`), `Pn_of_chainP`, `HeightBound2 D C X` (hypothesis: start levels `s_2, s_3`, depths `n_2, n_3`, last scales the largest `p^(j^2) <= D X`, buffered `4 Q <= X`, `alpha_k I_1 > 2` for all levels, and for some `m` with `N <= (X+1+Q_a+Q_b) m` the deterministic central bound), `denseDifferences_of_heightBounds2` (`c = 1/(64 C)`), `JA_of_heightBounds2` (`CompactQuotientCriterion` + `HeightBound2` at every precision give `JAProp`).

`JAFinal.HeightBound` (with earlier-level shifts in the statement) is superseded by `HeightBound2` (no shifts). Modelling choice to be checked by Codex: scales below `p^(s^2)` are collapsed into the seed `delta_0`; `HeightBound2` is exactly component 13 for this chain and seed. Still open: (1) the uniform central bound for `Mavg` (Matveev two-term separation), (2) arbitrarily large buffered heights with start levels `s_p` such that `p^(2s+1) 16/(15 D) > 2`, (3) the compact-quotient criterion (hypothesis). JA is NOT proved in Lean.

## Update, 31 October 2026 (buffered heights and start levels)

`JAHeights.lean` (compiled, standard axioms only), plus a refactoring of `JAFinal2.lean` (`HeightBound2` is now the scale data plus `CentralAt`, the existence of `m` with `N <= (X+1+Q_a+Q_b) m` and the central arc bound for `Mavg_a * Mavg_b`). `sD D = ceil D` (common start level), `alpha_large` (for `p >= 2`, all `k`: `p^(2(s+k)+1) * 16/(15 D) > 2`, so `alpha_k I_1 > 2` holds automatically), `Buffered D X na nb` (`D X < 2^((s+na+1)^2)`, `D X < 3^((s+nb+1)^2)`, `4 * 2^((s+na)^2) <= X`, `4 * 3^((s+nb)^2) <= X`), `exists_floor_sq`, `exists_buffered` (for `D >= 3` and every `M`: a height `X >= M` and depths `na, nb` with `Buffered`; construction without real logarithms: `X_0 = 4 * 3^(j'^2)` with `j'` large, `j` the 2-level of `X_0`, and if `D X_0 >= 2^((j+1)^2)` then `X = 2^ceil(4D) * X_0`), `CentralBound D C` (hypothesis: for all buffered `X >= X_0` the `CentralAt` bound holds with a constant independent of the height), `heightBound2_of_central`, `JA_of_centralBound` (`CompactQuotientCriterion` + `CentralBound` for suitable `D, C` at every `eps` give `JAProp`).

The Lean chain now has exactly two unproved inputs: `CentralBound` (component 13: uniform central bound for the deterministic measure `Mavg_a * Mavg_b`, seed `delta_0` at the start scale, Matveev two-term separation) and `CompactQuotientCriterion`. JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 1 of about 7; CentralBound NOT proved)

`JAProduct.lean` (compiled, standard axioms only): `conv_assoc`, `convList_smul`, `kernList`, `Mavg_eq_convList` (`Mavg_n(s) = (prod_{k<n} q_k^-2) * (s * kappa_1 * ... * kappa_n)`, `kappa_k = kernq(q_k, w_k)`), `Hs` (tails `H_i = K_{i+1} * ... * K_L * F`), `conv_convList_right` (`((mu * K_1 * ... * K_L) * F)(x) = (mu * H_0)(x)`), `Hs_zero_prod` (`H_0(0) = F(0) prod f_i`, `f_i = H_{i-1}(0)/H_i(0)`, when all `H_i(0) > 0`), `product_identity` (`((mu * K_1 * ... * K_L) * F)(0) = S_0 F(0) prod f_i`, `S_0 = (mu * H_0)(0)/H_0(0)`): the exact algebraic part of the normalized-product argument on `ZMod N`.

`CentralBound` (component 13) remains an unproved hypothesis. Plan for the rest, following the proof of `thm:normalized-bound` (size estimates mine, not measured):
* S2 (~300 lines): arc mass <= 2 * integral of a triangle `F_eps` on `ZMod N` with nonnegative Fourier coefficients (autocorrelation of an interval, `JALocalize`); merge the two chains into one sorted kernel list; rescale `kernq(w_k) = (Z_k)^2 K_{Q_k}` with `Z_k = sum w_k` and show `prod (Z_k/q_{k-1})^2 / prod (alpha_k I_1 - 2)^2` is bounded (from `sum_wQ`, geometric growth of `alpha_k`).
* S3 (~300): `0 <= h_i <= 1` (center maximality of positive definite functions on `ZMod N`, needs finite Fourier inversion), unit atom `H_i(0) >= 1`, `1 <= f_i <= B_D` (`KQ_le`).
* S4 (~300): far-field first-large-step expansion on `ZMod N` (torus version exists: `MixedPrimeProduct.farfield`; either bridge or reprove).
* S5 (~200): merged growth `Q_{i+2}/Q_i >= e^{t_i}` for the sorted list (`JAMerged`, abstract form done).
* S6 (~600): separated levels `f_i - 1 <= C(t_i^-6 + t_i^-3 + e^{-3 t_i})` (uses `tail_bound`), close pairs with the two-term separation `||r/Q_i + s/Q_{i+1}|| >= Q_i^-1 exp(-A log^2(2+t_i))` (Matveev; to be an explicit hypothesis `TwoTermSeparation`), deep levels and the bounded number of non-deep levels.
* S7 (~200): final product bound (`log f_i <= f_i - 1`, `sum t_i^-3 < infinity`, `product_bound_with_exceptions`).
After S2-S7 the only external inputs are `TwoTermSeparation` and `CompactQuotientCriterion`. JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 2: arc mass reduction and kernel merging; CentralBound NOT proved)

`JAProduct2.lean` (compiled, standard axioms only): `conv_smul_right`, `convList_append`, `conv_convList_left`, `conv_convList` (`(mu_a * K^a_1 * ... ) * (mu_b * K^b_1 * ...) = (mu_a * mu_b) * K^a_1 * ... * K^b_{n_b}`), `convList_perm` (the product is independent of the order of the kernel list); `Ftri` (triangle `acorr(1_[0,2m))/(2m)` on `ZMod N`), `Ftri_nonneg`, `Ftri_symm`, `Ftri_ge_half` (on `arc N (m-1)`), `Ftri_zero` (`F(0) = 1`), `arc_mass_le` (`sum_{arc(m-1)} nu <= 2 (nu * F)(0)` for `nu >= 0`); `normK` (`K = kappa / Z^2`), `normK_zero_ge` (`K(0) >= 1`), `kernq_eq_scale`, `normKernList`, `convList_range_scale`, `Mavg_eq_norm` (`Mavg_n(s) = (prod_k Z_{k+1}^2 / q_k^2) * (s * K_1 * ... * K_n)`), `convList_nonneg`, `Hs_atom` (all tails `H_i >= 0`, `H_i(0) >= 1`), `arc_mass_product` (for nonnegative seed measures `A, B`, `2m <= N` and ANY order `ks'` of the merged normalized kernel list: `sum_{arc(m-1)} (Mavg_a * Mavg_b) <= 2 Sc S_0 prod f_i`, with the explicit scalar `Sc = prod Z^2/q^2`, `S_0 = ((A*B)*H_0)(0)/H_0(0)`, `f_i = H_{i-1}(0)/H_i(0)`).

Still to do for `CentralBound`: S2b (the scalar `Sc <= C (prod (alpha_k I_1 - 2))^2`, from `Z_{k+1}/q_k <= alpha_k I_1 + 2`, `prod(1 + 4/(alpha_k I_1 - 2)) <= exp(sum ...)`, geometric `alpha_k`), S3 (`1 <= f_i <= B_D`, center maximality on `ZMod N`), S4 (far field), S5 (sorted merged growth), S6 (separated/close/deep levels; Matveev as hypothesis `TwoTermSeparation`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 2b: the scalar; CentralBound NOT proved)

`JAScalar.lean` (compiled, standard axioms only): `level_bound` (`0 <= z <= u + 2`, `u >= 4` give `z^2 <= exp(16/u) (u-2)^2`), `geom_quarter` (`sum_{k<n} (1/4)^k <= 4/3`), `scalar_bound` (chain with windows `w_{q_{k+1}}`, `q_{k+1} = q_k alpha_k`, `4 <= alpha_0 I_1`, `4 alpha_k <= alpha_{k+1}`: `prod_{k<n} Z_{k+1}^2 / q_k^2 <= exp(16/3) (prod_{k<n} (alpha_k I_1 - 2))^2`, uniformly in `n`), `alpha0_large` (start level `ceil D`: `4 <= p^(2s+1) 16/(15 D)` for `p >= 2`, `D >= 3`), `chainP_scalar_bound` (the same for `chainP p (sD D) D` with `alpha_k = p^(2(s+k)+1)`).

With `arc_mass_product` the arc mass of `Mavg_a * Mavg_b` is at most `2 exp(32/3) (prod_a (alpha I_1 - 2) prod_b (alpha I_1 - 2))^2 * S_0 prod f_i`; the target of `CentralAt` follows once `S_0 prod f_i <= C'(D)` uniformly in the height (seeds: kernel measures of `delta_0` at the start scale, `S_0` bounded in terms of `D` only).

Still to do for `CentralBound`: S3 (`1 <= f_i <= B_D`, `S_0` bounded, center maximality on `ZMod N`), S4 (far field), S5 (sorted merged growth), S6 (separated/close/deep levels; Matveev as `TwoTermSeparation`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 3: center maximality and the bounds 1 <= f_i <= B_D; CentralBound NOT proved)

`JACenter.lean` (compiled, standard axioms only): `fourier_inversion` (`sum_s (sum_x w(x) e(sx)) e(-sy) = N w(y)`), `PD.apply_le` (center maximality: a positive definite function on `ZMod N` satisfies `nu(y) <= nu(0)`), `Ftri_coef` / `Ftri_PD` (the triangle has Fourier coefficients `|w^(s)|^2/(2m) >= 0`), `Hs_PD` (all tails `H_i` are positive definite), `sum_kern` (`sum_x kern(w)(x) = sum_r |w^(r)|^2`), `sum_normK_le` (`sum K = K_Q(T) <= 30 D / 7` for `Q >= 25 D`, via `KQ_le`), `normK_PD`, `normK_props` (positive definite, `K(0) >= 1`, `sum K <= 30 D/7`), `sum_conv_total` (`sum (A * B) = (sum A)(sum B)`), `factor_bounds` (`1 <= (K*H)(0)/H(0) <= B`), `S0_bounds` (`0 <= S_0 <= sum mu`), `factors_bounded` (every `f_i` of a list of good kernels is in `[1, B]`).

Consequence: each `f_i` lies in `[1, 30D/7]`; the product of `L` factors is at most `(30D/7)^L`, which is NOT uniform in the number of levels. Small remaining item for `S_0`: `sum kernq(delta_0) = q_0` (Parseval for the delta seed), giving `S_0 <= q_0^a q_0^b`.

Still to do for `CentralBound`: S4 (far-field recursion on `ZMod N`), S5 (sorted merged growth), S6 (separated/close/deep levels; Matveev as `TwoTermSeparation`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 4: the far-field recursion on ZMod N; CentralBound NOT proved)

`JAFar.lean` (compiled, standard axioms only): `cn` (circle norm of `d/N` on `ZMod N`, via `ZMod.toAddCircle`), `cn_neg`, `cn_natCast_le`, `zinst` (the induced `SeminormedAddCommGroup` on `ZMod N`, used locally through the explicit-instance form of `MixedPrimeProduct.farfield_geom`), `Ftri_vanish` (`F(y) = 0` for `cn y >= 2m/N`), `getD_props`, `far_field_ZN`: for a list `ks` of good kernels (positive definite, `K >= 0`, `K(0) >= 1`, `sum K <= B`, `B >= 0`), `u >= 0`, `2m/N <= 3u/4`, `k + n = |ks|`, `cn y >= u`: `h_k(y) <= sum_{j<n} B^j sum_{d : cn d > u/2^(j+3)} K_{k+j+1}(d)` with `h_k = H_k/H_k(0)`, `H_k = K_{k+1} * ... * K_L * F`. The weights are `w_j(d) = K_j(-d)` (reflection; no symmetry of the kernels needed), the one-step inequality uses `H_{k+1}(0)/H_k(0) <= 1` (`factor_bounds`), the terminal condition uses `h_L = F`.

Still to do for `CentralBound`: S5 (sorted merged growth for the merged list; `JAMerged` abstract form), a conversion from kernel tails to the tails of `kappa_Q(r)` at the atoms `r N / Q` (then `tail_bound` applies), S6 (separated/close/deep levels; Matveev as `TwoTermSeparation`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 4b: kernel tail conversion; CentralBound NOT proved)

`JAKernTail.lean` (compiled, standard axioms only): `cn_atom` (`cn(a_r) = ||r.val/Q||_{R/Z}` for the atom `a_r = r (N/Q)` of the kernel), `nrm_val_eq` (`||r.val/Q|| = |r~|/Q`, balanced representative), `tail_conv` (`sum_{d : v < cn d} K(d) = sum_{r : v < |r~|/Q} kappa_Q(r)`), `kernel_tail_le` (`D >= 3`, `Q >= 25 D`, `Q | N`, `v >= 0`, `1 <= floor(vQ)`: tail `<= 25 D^4 / floor(vQ)^3`, from `JAWindowTail.tail_bound`), `kernel_tail_le'` (if `vQ >= 2`: tail `<= 200 D^4 / (vQ)^3`).

With `far_field_ZN` this gives the ingredients of (far-separated) `Phi_i(1/Q_i) <= C_D((Q_i/Q_{i+1})^3 + e^{-3 t_i})`; still to do: S5 (sorted merged growth) and the geometric-series assembly, S6 (separated/close/deep levels; Matveev as `TwoTermSeparation`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step 5: merged growth and the far-separated estimate; CentralBound NOT proved)

`JAFarSep.lean` (compiled, standard axioms only): `merged_gap_fin`, `merged_growth_fin` (finite-prefix form of `JAMerged.merged_gap_seq_odd`: `Q_i exp(t_i floor(m/2)) <= Q_{i+m}` for a strictly increasing selection of length `L`, `i+m < L`), `kernel_tail_all` (`sum_{d : v < cn d} K(d) <= C_1/(vQ)^3` for all `v > 0`, `C_1 = 200 D^4 + 8 (30D/7)`), `pair_geom` (`sum_{j<M} q^(j/2) <= 4` for `0 <= q <= 1/2`), `ratio_cube`, `term_algebra`, `far_separated` (the paper's (far-separated): for kernels `K_j = normK(Q_j)` with `Q_j >= 25D`, `Q_j | N`, merged growth, `2m/N <= 3/(4 Q_p)` and `(8B)^2 e^{-3 t_p} <= 1/2`, `B = 30D/7`: `h_{p+1}(y) <= 512 C_1 ((Q_p/Q_{p+1})^3 + 4 (8B)^2 e^{-3 t_p})` for `cn y >= 1/Q_p`), `exp_lp`, `log_scale`, `hgrow_of_merged`, `far_separated_primes` (the same for scales `b_j^(n_j^2)` of a strictly increasing selection, growth discharged).

Still to do for `CentralBound`: (a) the sorted enumeration of the pairs `(b, n)` of the two chains and the permutation statement (distinct pairs have distinct scales), (b) S6: separated levels `f_i - 1 <= C(t_i^-6 + t_i^-3 + e^{-3 t_i})` (truncation at `M_i = ceil(t_i^2)`, `tail_bound`), close pairs with `TwoTermSeparation` (Matveev), deep levels and the bounded number of non-deep levels, (c) S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound: sorted enumeration of the two chains; CentralBound NOT proved)

`JASorted.lean` (compiled, standard axioms only): `pairsOf` (pairs `(base, exponent)` of the levels of the chains of 2 and 3), `key` (`b^(e^2)`), `mem_pairsOf`, `key_inj_on` (distinct pairs have distinct scales; `2^(x^2) = 3^(y^2)` impossible by parity), `pairsOf_nodup`, `sortedPairs` (core `List.mergeSort` by scale), `sortedPairs_perm`, `sortedPairs_length`, `sortedPairs_pairwise`, `sorted_strict` (scale strictly increasing), `Fker` (kernel of a pair, `dite` so no instance depends on the pair), `Fker_eq`, `map_range_getD`, `pairs_map_Fker`, `getD_mem`, `exists_sorted` (sequences `b, n : N -> N` with `b i in {2,3}`, `lp` strictly increasing below `n_a + n_b`, each `(b_j, n_j)` a pair of a chain, and `[normK(b_j^(n_j^2))]_{j < n_a+n_b}` a permutation of `normKernList(chain 2) ++ normKernList(chain 3)`), `arc_mass_sorted` (with `arc_mass_product`: for the chains of 2 and 3 and nonnegative seed measures, the arc mass of `Mavg_a * Mavg_b` is at most `2 Sc S_0 prod f_i` along the sorted kernel list).

Still to do for `CentralBound`: S6 (estimates for the factors `f_i` of the sorted list: separated levels via truncation at `M_i = ceil(t_i^2)`, `tail_bound`, `far_separated`; close pairs with `TwoTermSeparation` (Matveev) and the deep-level condition; bounded number of non-deep levels via `JAMerged.window_card_le_two`), S7 (final product bound). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step S6a: the separated-level estimate; CentralBound NOT proved)

`JASep.lean` (compiled, standard axioms only): `atom_eq_zero` (the only atom at `0` is the origin one), `normK_zero_eq` (`K(0) = 1` for the unit-atom kernel), `support_cn` (a nonzero point of the support of `K` has `cn >= 1/Q`), `separated_factor` (for the sorted kernel list `ks` of `far_separated`, `p + 1 <= L`, `t = sqrt(log Q_p) >= 2`, `t Q_p <= Q_{p+1}` and the hypotheses of `far_separated`: `f_p - 1 <= 200 D^4 / t^6 + B * 512 C_1 (t^-3 + 4 (8B)^2 e^{-3t})`, `B = 30D/7`, `C_1 = 200 D^4 + 8B`; this is the paper's (separated-factor)). Proof: `f_p = sum_d K_p(d) h_{p+1}(-d)`; the origin atom contributes exactly 1; atoms beyond `M/Q`, `M = ceil(t^2)`, contribute at most the kernel tail `200 D^4 / t^6` (`kernel_tail_le'`); the remaining nonzero atoms have `cn >= 1/Q` so `h_{p+1}` is bounded by `far_separated`, with total mass `<= B`.

Still to do for `CentralBound`: S6b (close levels `Q_{p+1} < t_p Q_p`: two-term separation `||r/Q_p + s/Q_{p+1}|| >= Q_p^-1 exp(-A log^2(2+t_p))` as the hypothesis `TwoTermSeparation` (Matveev), deep-level condition, `f_p - 1 <= C(t^-6 + t^-9 + e^{-t})`), S6c (count of non-deep levels: `JAMerged.window_card_le_two`, window width `O((log log X)^2)`), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step S6b: close levels; PARTIAL; CentralBound NOT proved)

`JAClose.lean` (compiled, standard axioms only): `atom_of_support`, `val_div_eq`, `cn_atom_balanced` (`cn(a_r) = |r~|/Q`), `cn_add_atoms` (`cn(a_r + a'_s) = ||r~/Q + s~/Q'||`), `far_beyond` (far field after TWO levels, any `u > 0`: `h_{p+2}(y) <= 2048 C_1 (1/(u Q_p))^3 (8B)^2 e^{-3t}` for `cn y >= u`), `close_factor` (for a close pair: `f_p - 1 <= 200 D^4/t^6 + B*200 D^4/(4t^3)^3 + B^2 * 2048 C_1 (1/(u Q_p))^3 (8B)^2 e^{-3t}` with `u = exp(-A log^2(2+t))/Q_p`, GIVEN the two-term separation `hTT` for the atoms `0 < |r| <= ceil(t^2)`, `|s| <= ceil(4t^3)`), `TwoTermSeparation A` (the statement of the external Matveev input, opposite-sign case, for pairs `2^(a^2), 3^(b^2)`), `two_term_easy` (the case `s = 0` or equal signs is elementary and proved).

NOT done in S6b: the derivation of `hTT` from `TwoTermSeparation` (needs `2(ceil t^2 + ceil 4t^3) <= Q`, i.e. `exp(t^2) >= 2(t^2 + 4t^3 + 2)` for `t >= 8`; my attempt `radii_le_exp` failed and was removed), and the simplification `exp(3A log^2(2+t) - 3t) <= e^{-t}` for large `t`. Still open: S6c (non-deep levels), S7 (final product). JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step S6b completed except packaging; CentralBound NOT proved)

`JAClose.lean` now also has `radii_le_exp` (`2(ceil t^2 + ceil 4t^3) <= exp(t^2)` for `t >= 18`) and `hTT_of_two_term` (for `A >= 0` and `TwoTermSeparation A` there is `T_1` such that the hypothesis `hTT` of `close_factor` holds, for all signs, for close pairs of prime-square periods with `t >= T_1`; opposite signs = the hypothesis, other cases = `two_term_easy`). Compiled, standard axioms only.

Still open: `exp(3A log^2(2+t) - 3t) <= e^{-t}` for large `t`; packaging `close_factor` + `hTT_of_two_term` for the sorted list; S6c (deep-level condition, count of non-deep levels); S7 (final product). Please audit the exact form of `TwoTermSeparation` against Matveev Cor. 2.3. JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step S6c: non-deep levels; CentralBound NOT proved)

New module `JANonDeep.lean` (compiled, standard axioms only, no external hypothesis): `deep_radius` (a deep level, `X >= 4Q exp(A log^2(2+t))`, has `2(2/X) <= Q^-1 exp(-A log^2(2+t))`), `log_le_four_rootroot`, `log_sq_le`, `poly_eventually` (for large `S`, `w^2 + w <= S^2` with `w = c + A log^2(2+S)`: the non-deep window has width `O((log log X)^2) <= sqrt(log X)`), and `non_deep_card_le_two` (for `D >= 1`, `A >= 0` and large `X`, at most two distinct periods `b^(n^2) <= DX` are non-deep; the paper's bound is four).

Still open for `CentralBound`: packaging of S6b (`exp(3A log^2(2+t) - 3t) <= e^{-t}`; `close_factor` + `hTT_of_two_term` on the sorted list), S7 (final product with `log f <= f - 1`, `sum t^-3 <= const`, `product_bound_with_exceptions`, `f <= B_D` on the at most two non-deep levels, fixed factor for early levels), assembly from `TwoTermSeparation`. Then `CompactQuotientCriterion`. JA is NOT proved in Lean.

## Update, 31 October 2026 (central bound, step S7: the final product; CentralBound NOT proved)

New module `JAProductFinal.lean` (compiled, standard axioms only, no external hypothesis): `product_final` (abstract: strictly increasing periods, `1 <= f_i <= B`, at most `K` exceptional indices, `f_i <= 1 + Cf t_i^-3` for the other levels with `t_i >= T` gives `prod f_i <= B^(K + 2 floor(2T)) exp(Cf * 2((sqrt log 2)^-3 + (sqrt log 3)^-3))`, independent of the number of levels), `sep_cube` (`separated_factor` RHS `<= Cs t^-3`), `close_cube` (`close_factor` RHS `<= Cc t^-3` for `t >= max(1,(16A+6)^2)`; includes `exp(3A log^2(2+t) - 3t) <= t^-3`, so the S6b simplification is done in this stronger form).

What remains for `CentralBound` is the assembly only: sorted enumeration (`arc_mass_sorted`), exceptional set = non-deep levels (`JANonDeep.non_deep_card_le_two`) plus early levels (`T` in `product_final`), per-level bound from `separated_factor` / `close_factor` + `hTT_of_two_term` + `sep_cube` / `close_cube`, side conditions (`htop`, `ht2`, `hgrow_of_merged`, `deep_radius`, divisibility), seed factor (`S0_bounds`), scalar (`chainP_scalar_bound`). Then `CompactQuotientCriterion`. JA is NOT proved in Lean.

## Update, 31 October 2026 (CentralBound assembled; JA machine-checked CONDITIONAL on two named inputs)

New modules (compiled, standard axioms only, no `sorry`): `JAAssemble.lean` (`level_sep`, `level_close`, `bases_differ`, `fac_bounds`, `HTT`), `JACentral.lean` (`prod_f_bound`: for large `X` the product of all factors `f_i` is at most `Cp(D,A)`, independent of the number of levels, of `N`, of `m` given `2m/N <= 3/X`), `JACentral2.lean` (`central_bound`: for `D >= 3`, `A >= 0` and `TwoTermSeparation A` there is `C > 0` with `CentralBound D C`), `JAMain.lean` (`JA_of_inputs`). `JAProductFinal.lean` changed only by weakening `hn` to `i < L`.

**Main theorem `JAMain.JA_of_inputs`: `CompactQuotientCriterion` and `TwoTermSeparation A` (some `A >= 0`) imply `JAProp`.** JA is therefore machine-checked conditional on exactly two named inputs: (1) the two-term separation (Matveev, as stated in `JAClose.TwoTermSeparation`; needs an audit against Cor. 2.3, and if it were false the theorem would be vacuous), (2) `CompactQuotientCriterion` (`SyndeticW -> JAProp`, character separation on a compact abelian group). JA is NOT proved unconditionally.

Remaining for a full proof: Matveev's theorem (two-logarithm case) and the compact-quotient criterion, neither in Mathlib.

## Update, 31 October 2026 (compact-quotient criterion: reduced to Weil's theorem for Z)

New modules (compiled, standard axioms only, no `sorry`): `JAOnePrime.lean` (`step1`, `oneprime`: a `P_l`-continuous parameter `alpha` has `l^(j^2) alpha` in `Z`; `oneprime_two_three`: continuity for both `P_2` and `P_3` forces `alpha` in `Z`) and `JACompact.lean` (`PrecompactMAP`, `compactQuotient_of_MAP`: `PrecompactMAP -> CompactQuotientCriterion`, `JA_of_matveev_and_MAP`).

`PrecompactMAP` is Weil's theorem for `Z`: a precompact group topology on `Z`, given by a neighbourhood base `V(eps)` of `0`, is maximally almost periodic (if `m` is not in the closure of `{0}` there is a continuous character `n -> e(n alpha)` with `||m alpha|| > 0`). It does not mention `P_2`, `P_3`; the problem-specific part (one-prime dual, intersection `Z[1/2] cap Z[1/3] = Z`, the identification of `W_eps` with the neighbourhood base, continuity for `P_3` via `n = k` and for `P_2` via `n = -k`) is now proved in Lean.

**JA is machine-checked conditional on exactly two inputs: `TwoTermSeparation` (Matveev, two-logarithm case) and `PrecompactMAP` (general Peter-Weyl-type fact).** Plan for `PrecompactMAP`: Mathlib here has compact symmetric operators (`IsCompactOperator`, `eq_zero_of_forall_hasEigenvalue_eq_zero`, `finite_dimensional_eigenspace`); route: completion of `(Z, J)` is a compact normed group, a convolution operator on `L^2` of Haar measure is compact and symmetric, a nonzero-eigenvalue eigenvector on mean-zero functions gives the character.

## Update, 31 October 2026 (Weil's theorem for Z proved; the compact-quotient criterion is PROVED; JA conditional on Matveev only)

New modules (compiled, standard axioms only, no `sorry`): `JAWeilA.lean` (Haar probability measure on a compact normed abelian group `G`, `H = L^2(G)`, translation operators `tau a`, `tau_add`, `tau_inner` (adjoint = `tau (-a)`), `tau_toLp`), `JAWeilB.lean` (convolution operator `Cop` with kernel `||x - y||`: compact by Arzela-Ascoli on `{<K x, g>}`, commutes with translations, `Cop_tau_ne`), `JAWeilC.lean` (`T = C* P C`, `P = 1 - tau a / 2 - tau (-a) / 2`; compact, symmetric, nonzero; `weil_abstract`: for `m . g != 0` there are `zeta`, `|zeta| = 1`, `zeta^m != 1`, and continuous `F != 0` with `F (x + g) = zeta F x`), `JAWeilD.lean` (`weil_seminorm`: a precompact group seminorm `S` on `Z` with `S m > 0` gives `alpha` with `n -> e(n alpha)` `S`-continuous and `||m alpha|| > 0`; completion `ZG S` is compact; Jordan's inequality), `JAWeilE.lean` (the seminorm `Jsem`, `{J < eps} = W_eps`, **`compactQuotientCriterion : CompactQuotientCriterion`** and **`JA_of_matveev : TwoTermSeparation A -> JAProp`**).

**JA is now machine-checked conditional on exactly ONE external hypothesis: `TwoTermSeparation` (Matveev's two-logarithm bound, as stated in `JAClose`).** `JACompact.lean` (reduction to `PrecompactMAP`) is superseded. Audit needed: the exact form of `TwoTermSeparation` against Matveev Cor. 2.3 (if false as stated the theorem is vacuous). To remove it: prove the two-logarithm case of Matveev's theorem (not in Mathlib).

## Update, 1 November 2026 (the single hypothesis weakened: any separation Q^-1 exp(-c sqrt(log Q)), c < 1, suffices)

The chain from the two-term separation to JA now depends on the separation only through a *profile* `a(t)`: the separation radius at a close pair of scale `Q`, `t = sqrt(log Q)`, is `Q^-1 exp(-a(t))`. New module `JAProfile.lean` defines `WindowProfile a` (`a >= 0`, monotone, and for every `c >= 0` the inequality `(c + a S)^2 + (c + a S) <= S^2` for large `S`; used for the non-deep levels) and `CloseGrowth a` (`a t + log t <= t` for large `t`; used for the close levels), and proves both for the linear profile `a(t) = c t`, `0 <= c < 1` (`windowProfile_weak`, `closeGrowth_weak`).

Changes (all compiled, standard axioms only, no `sorry`): `JANonDeep.non_deep_card_le_two` takes `a` and `WindowProfile a` (`windowProfile_A` shows that `A log^2(2+t)` is one); `JAClose` has `TwoTermSep a` (and `TwoTermSeparation A := TwoTermSep (A log^2(2+t))`), `close_factor` and `hTT_of_two_term_G` for a general `a`; `JAProductFinal` has `exp_close_le_G`, `close_cube_G`, `closeGrowth_A`; `JAAssemble`, `JACentral`, `JACentral2` (`central_bound`), `JAMain.JA_of_profile` carry the profile; the old statements (`hTT_of_two_term`, `close_cube`, `JA_of_inputs`, `JA_of_matveev`) are kept with unchanged signatures as wrappers.

**New theorem `JAWeil.JA_of_weak_separation`: if for some `0 <= c < 1` the separation `||r/Q + s/Q'|| >= Q^-1 exp(-c sqrt(log Q))` holds for the close pairs of prime-square periods (opposite-sign atoms `0 < |r| <= ceil t^2`, `|s| <= ceil 4 t^3`), then JA holds.** JA is still conditional on one separation hypothesis; the hypothesis is only weaker (the profile `c t` dominates `A log^2(2+t)`), so a proof of it needs a weaker form of the two-logarithm bound than Matveev's. JA is NOT proved unconditionally.

## Update, 1 November 2026 (TVGplus: exact gcd and logarithmic order in Lean)

New modules (compiled, standard axioms only, no `sorry`; not pushed): `TVGPlusGcd.lean`, `TVGPlusOrderA.lean` ... `TVGPlusOrderE.lean`, `TVGPlusOrder.lean`, `TVGPlusPairGcd.lean`.

* **`g_S(delta) = D_S(delta)`** (`TVGPlusGcd.gcd_iff`): under diagonal density `DD S`, an integer divides every element of the ball `B^S_delta` iff it divides `D_S(delta)`. The character argument of the article (dual group of the completion) is replaced by an elementary construction (`exists_not_dvd`): for a prime `r` not in `S`, take `y_p` with `y_p = 1 (mod r)` and `P_p(y_p) < delta/2`, approximate the integer targets `(y_p - 1)/r` by `w` in all `P_p` (this is `DD S`), and note `1 + r w` lies in the ball and is not divisible by `r`. `TVGPlusPairGcd`: the same for `S = {2,3}` from `JAProp`, from the Matveev separation, and from the weak separation `exp(-c sqrt(log Q))`.
* **Theorem 3.2 (logarithmic order)** with `L = log(1/delta)`, `c_S = sum 1/(4 log p)`, `A_S = sum 1/sqrt(log p)`, `x_S = ((A_S + sqrt(A_S^2 - 4 c_S))/2)^2`: `TVGPlusOrder.uS_lower` (every `b < c_S`: `exp(b L^2) <= u_S(delta)` for small `delta`), `uS_upper` (every `B > x_S`: `u_S(delta) <= 2 exp(B L^2)` for small `delta`), `cS_le_xS`, `xS_singleton` (`x = c = 1/(4 log p)` for one prime) and `uS_singleton` (`u_{p}(delta) = p^(a_p(delta)^2)` exactly). The refined pigeonhole on multiples of `D_S(delta)` is `TVGPlusOrderA` (`pigeonhole_mult`, `upper_mult`); the counting of retained coordinates is `TVGPlusOrderD.count_bound`; `f(B) = B - A_S sqrt B + c_S > 0` for `B > x_S` is `TVGPlusOrderC.f_pos`. The statements are in the `delta_0` form of the `liminf`/`limsup` bounds (equivalent to the filter statements). Neither result uses joint approximation except `gcd_iff` (through `DD S`).

## Update, 1 November 2026 (TVGplus questions 2 and 3: block reduction of diagonal density)

New module `TVGPlusDD.lean` (compiled, standard axioms only, no `sorry`; not pushed): `DD_union` (`DD A`, `DD B`, `JAblock A B` imply `DD (A ∪ B)`), `JAblock_of_DD` (converse for disjoint `A`, `B`), `DD_insert_iff` (`DD (insert p T) ↔ DD T ∧ JAblock {p} T`), `affine_target` (an arbitrary pair of integer targets reduces to the unit target by `k = t_B + (t_A - t_B) m`). So `DD({p,q,r})` is equivalent to the pair property and the new block property `JA({p},{q,r})`. Questions 2 (effective bound for a shifted target) and 3 (`DD(S)` for three or more primes) are NOT resolved; see `TVGplus_questions_2_3.md`.

## Update, 1 November 2026 (TVGPlusSizes: explicit sizes and the rest of the logarithmic-order theorem; not pushed)

`TVGPlusSizes.lean` (compiled, standard axioms only, no `sorry`): `block_combine` (the `DD_union` construction with the size bound `|k| <= (|m|+1)(|a|+|b|)`), `affine_target_size`, `aS_sq_sub_four_cS`, `xS_lt_aS_sq`, `order_singleton_limit`. With these, the only parts of the TVGplus theorem on the logarithmic order that are not formalized are none of the stated inequalities; the character argument of Lemma 4.1 and the numerical computations remain outside Lean.

## Update, 1 November 2026 (TVGplus Lemma "dual under density" formalized; not pushed)

`TVGPlusDual.lean` (compiled, standard axioms only, no `sorry`): `contAt_of_denominator` (if `M alpha` is an integer with every prime factor of `M` in `S`, then the character `k -> e(k alpha)` is continuous at `0` for the `P_S`-topology; no density needed) and **`dual_of_DD`** (under `DD S`, every `P_S`-continuous `alpha` has `M alpha` in `Z` for such an `M`; i.e. `H_S = sum_{p in S} H_p = Z[1/S]/Z`). The proof is elementary: idempotent-like integers `k_p` from `DD S`, a convergent subsequence on the compact circle, limit parameters `alpha_p` with `sum alpha_p = alpha`, each `P_p`-continuous, and the one-prime theorem `JAOnePrime.oneprime`. `TVGPlusPairDual.lean`: for `S = {2,3}` the dual is `Z[1/6]/Z` given `JAProp`, under the Matveev separation, and under the weak separation. With these, the character argument behind Lemma 4.1 of TVGplus is formalized.
