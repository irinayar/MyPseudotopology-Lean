# TVGplus: Lean checks of the jump argument, the collision-energy criterion and shifted witnesses (6 November 2026)

Modules: `LeanCheck/TVGShiftedJump.lean`, `LeanCheck/TVGShiftedEnergy.lean`, `LeanCheck/TVGShiftedCert.lean` (imported by `LeanCheck.lean`) and the audit entry point `LeanCheck/TVGShiftedAxioms.lean` (output in `verification/tvgshifted-check.txt`). They build on the existing TVGplus modules (`TVGPlusOrderB`, `MixedPrimeColoured`; the universal divisor `forced`, `Dvis`, `cS`). A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article statements needs mathematical review.

## Jump argument (`TVGShiftedJump`)

Two disjoint finite sets `S1`, `S2` of primes; `Wsh S1 S2 δ = {k | InBall S1 δ (k-1) ∧ InBall S2 δ k}` (for `S1 = {2}`, `S2 = {3}`: `P_2(k-1) < δ`, `P_3(k) < δ`); `rad n = e^{-n}`; `height n` is the least `|k|` in `Wn n = Wsh S1 S2 (rad n)`; `Dn n = Dvis S1 (rad n) · Dvis S2 (rad n)`.

| Declaration | Statement |
|---|---|
| `exists_jump`, `jump_abstract` | For an antitone family of nonempty sets of integers with empty intersection, `height n < height (n+1)` for arbitrarily large `n`; there, if two different members of `W n` differ by at least `Dn n`, then `Dn n ≤ 2 · height (n+1)`. |
| `Dvis_unbounded` | `D_S(e^{-n})` is unbounded for a nonempty set `S` of primes. |
| `shifted_jump` | The jump inequality for the shifted problem, using `forced`. |
| `shifted_limsup_lower` | If every `Wn n` is nonempty, then for every `0 ≤ b < c_{S1} + c_{S2}` and every `N` there is `m ≥ N` with `exp (b m²) ≤ height m` (that is, `limsup log height / n² ≥ c_{S1} + c_{S2}`). |

The existence of witnesses at every radius is a hypothesis. Not formalized: the congruence-problem statement (CRT upper bound, limsup exactly `c_S`) and the variant for positive minima.

## Collision-energy criterion (`TVGShiftedEnergy`)

For nonempty scale sets `Sq`, `Sp`, `X : ℕ`, `r : ℝ`: `A = {a ∈ [0,X] : Pn Sq a < r}`, `B` likewise for `Sp`, `V = A - B`, `R t` the number of representations `t = a - b`, `E = ∑ R t²`, `M = 2X+1`, `L = ⌈(|A||B|)²/E⌉`.

| Declaration | Statement |
|---|---|
| `cs_bound`, `Lbound_le_card` | `(|A||B|)² ≤ |V| E`, hence `L ≤ |V|`. |
| `energy_criterion`, `energy_criterion_sq` | Every integer `t` with `|t| + M + 1 ≤ 2L` has `k` with `|k| ≤ X`, `Pn Sq k < 2r`, `Pn Sp (k - t) < 2r` (also for `Sq = sqScales q`, `Sp = sqScales p`). |
| `energy_arithmetic`, `unit_target_iff` | `2·1418493632083 - (2·10^12+1) - 1 = 836987264164`; a unit target needs `L ≥ X + 2`. |

The energy certificate `L = 1418493632083` at `r = 1/20`, `X = 10^12` is a finite computation that is not part of the Lean files.

## Membership certificates (`TVGShiftedCert`)

`CertOK p k num den N` is a decidable certificate for `P_p(k) ≤ num/den`; `Pn_sq_le` and `mem_Wsh_of_cert` turn a pair of certificates into membership in `Wsh {2} {3} (1/m)` for all `1 ≤ m ≤ mmax` (`num · mmax < den`). Certificates are checked with `decide +kernel`.

| Theorem | Witness `k` | `m` up to |
|---|---|---|
| `fwd627_mem` | 66907291982889809579769849953882135494393857 | 664 |
| `fwd665_mem` | 178421516210482934465929494559209061458378753 | 682 |
| `rev665_mem` | 1 - 223014257629644121148604218508658631111606272 | 682 |
| `fwd683_mem` | 223038646310390834811416967750970593196900353 | 714 |
| `rev683_mem` | 1 - 245323044659160427845920760406465283677487104 | 703 |
| `sgn715_mem` | -267606999048097958924495329266879805341564927 | 904 |

These are **membership statements only**. The minimality of the witnesses (exclusion searches up to `10^44`) was computed outside Lean and is not formalized, nor is the sharpness of the upper endpoints.

## Not covered

The abc-conditional lower bound of `TVGplus_v23`; minimality of the witnesses; the energy certificate at `r = 1/20`, `X = 10^12`; a new proof of the universal-divisor theorem (the existing `forced` is used).
