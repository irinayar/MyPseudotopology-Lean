# Lean formalizations for MyPseudotopology

Lean 4 and Mathlib sources supporting selected results about Hamel topologies,
topological vector groups, rational scalar actions, and mixed-prime character groups.

## Build and audit

The exact Lean toolchain is in `lean-toolchain`; `lake-manifest.json` pins dependencies.
Install Lean through elan, then run from this directory:

```sh
lake exe cache get
lake build LeanCheck
lake env lean LeanCheck/Axioms.lean
lake env lean LeanCheck/MixedPrimeAxioms.lean
```

The large `.lake/` dependency and build directory is intentionally excluded.
Lake recreates dependencies and can fetch the Mathlib cache. The workflow template runs the library build
and the two existing axiom reports. Source inclusion is not a claim that CI has passed;
automatic CI is currently inactive because the upload token lacks GitHub workflow permission. The template is saved as `docs/ci/lean.yml`; activate it under `.github/workflows/` using an appropriately authorized account.

## Verification scope

- `LeanCheck.lean` is the main library import target; `LeanCheck/` contains the formalization modules and audit entry points.
- `scratch/` and `AdditionalProbe.lean` contain supplementary probes or drafts; they are preserved for completeness but are not part of the default build or certified by any future library CI result.
- `experiments/` contains supporting numerical source code, data, and notes. These are not Lean proofs and are not run by Lean CI.
- The complete analytic mixed-prime joint-approximation proof has **not** been formalized. `MixedPrimeProduct.lean` checks selected abstract components, not the full analytic cascade or the complete JA deduction.
- A Lean proof verifies its formal statement under its hypotheses. The correspondence with a paper statement still requires mathematical review. The historical mapping below records earlier work; its counts are not a fresh audit of every declaration.

This source snapshot preserves the original modules. Local build wrappers have been
replaced with portable wrappers; generated files and the original release/update/Pages
workflows are excluded. No license is inferred or assigned by this export.

## Historical statement mapping

# LeanCheck - machine-checked parts of HamelCharactersTVG

Lean 4 (v4.35.0) + Mathlib. Build: `lake build LeanCheck`; axioms: `lake env lean LeanCheck/Axioms.lean`.
(On drives that do not record ownership, git needs `safe.directory`; set it per process with
`GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'` before `lake`.)

## LeanCheck/AppendixB.lean  (paper: HamelCharactersTVG_v12, Appendix B)  -- compiles, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only.

| Paper | Lean | Notes |
|---|---|---|
| Lemma B.1 | `lemmaB1` | exactly as stated, `t` in `AddCircle (1:ℝ)`, `0<ε<1/8` |
| Prop. B.2 | `propB2` | `A = ℚ/ℤ` modelled as the finite-order points of the circle; hypothesis `∀ c ∈ segSet J, ‖c•x‖ < ε` (weaker than `P_C(x) < ε`), conclusion `x = 0`; `J : ℕ → ℕ` any function with `J k ≥ k` |
| Prop. B.3 | `propB3`, `odd_half_not_hausdorff` | continuity is expressed by the paper's quarter-arc criterion (exists `ε`, `‖ψ x‖ ≤ 1/4` on the ball); the equivalence of that criterion with topological continuity is quoted in the paper, not re-proved here |

Supporting lemmas: `exists_centered` (centered representative, norm = |x|), `norm_two_nsmul`,
`inv_le_norm` (nonzero point killed by `m` has norm >= 1/m), `psi_half` (value of the series at 1/2).

## LeanCheck/ChainLemmas.lean and LeanCheck/ChainDigits.lean  (paper: ChainSubsetTheorem_note.md, Theorems F, G, H)
## compile, no `sorry`, axioms: propext, Classical.choice, Quot.sound only.

Stated over `ℝ`/`ℚ` with "within δ of an integer" written as an existential integer (no circle group needed).

| Note | Lean | Statement |
|---|---|---|
| contraction (G failure direction; F(a); used in H) | `contraction_step` | `|x|,|x'|<δ`, `r ≤ A`, `δ(1+A)<1`, `x'-r x ∈ ℤ` ⇒ `x' = r x` |
| ditto, along a run | `run_contraction`, `run_bottom_small` | ratios `2 ≤ r_i ≤ A` ⇒ `|w_0| 2^L ≤ |w_L|`, so `|w_0| < δ/2^L` |
| single-digit bound (G, Step 1) | `near_of_all_multiples` | `∀ρ ≤ R, ρθ` within `1/4` of an integer ⇒ `θ` within `1/(4R)` of an integer |
| threshold crossing (G, Case II) | `crossing` | steps in `[c, 1/8]`, `c>0` ⇒ some partial sum lies in `(1/4, 3/8]` |
| geometric tail (`P_C(x) ≤ 2η`) | `geom_tail` | `a_{j+1} ≤ a_j/2`, `a_j ≥ 0` ⇒ `∑ a_j ≤ 2 a_0` |
| digit calculus (G) | `Mseq`, `xval`, `wval`, `digit_int`, `digit_rec`, `digit_zeta` | `M_i x - w_i ∈ ℤ`; `w_i = (ρ_i + w_{i+1})/α_i`; `(∑ e_i M_i) x - ∑ e_i w_i ∈ ℤ` |
| one-digit witness (G, Steps 1 and 4) | `single_digit_small`, `single_digit_int` | `x = ρ/M_{i+1}`: `0 ≤ M_j x ≤ ρ/α_i` for `j ≤ i`, `M_j x ∈ ℤ` for `j > i` |

## LeanCheck/ChainDichotomy.lean  -- Theorem G, compatible direction (Case I / Case II), compiles, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only.

Model. `α : ℕ → ℕ` ratios (`α i ≥ 2`, `α i → ∞`), `M = Mseq α`. A profinite integer `ζ` is a compatible residue system
`z : ℕ → ℤ` with `M k ∣ z (k+1) - z k`; on `x = ∑_{j<K} ρ_j / M_{j+1}` it takes the value `chi α z ρ K = ∑ ρ_j θ_j`
(mod 1), `θ_j = z_{j+1}/M_{j+1}` (`thetaR`). `Cont α z δ` is quarter-arc continuity with radius `δ`: whenever every
`M_i x` (`i ≤ K`) is within `δ` of an integer, `chi` is within `1/4` of an integer.

| Note | Lean | Statement |
|---|---|---|
| geometric digit bound | `digit_bound` | `|ρ_t| ≤ η α_t` for all `t` ⇒ `|w_n| ≤ 2η` |
| Step 1 | `step1` (with `xval_unit`, `chi_unit`) | `Cont` and `α_i ≥ 8/δ` ⇒ `θ_i` within `2/(δ α_i)` of an integer |
| Step 2 | `theta_rel` | `α_{i+1}(θ_{i+1} - m_{i+1}) - (θ_i - m_i)` is an integer |
| Case I | `caseI` | if that integer is `0` for all `i ≥ i₁`, then `z_{i+1} - M_{i+1} m_i` is constant (this covers negative integers) |
| Case II | `caseII_false` | if it is nonzero for infinitely many `i`, `Cont` fails (one-digit witnesses at the levels `Nat.nth p`, `crossing`, `geom_tail`) |
| Dichotomy | `case_dichotomy` | `Cont α z δ` ⇒ `∃ u i₁, ∀ i ≥ i₁, M_{i+1} ∣ z_{i+1} - u`, i.e. `ζ = u ∈ ℤ` |

Constants as in the note: `η₁ = δ/4`, `κ = 2/δ`, `η₂ = δ/16`, threshold `α_i ≥ 32/δ`.
Modelling assumptions NOT formalized (each is one line on paper): (i) continuity of `ζ` for `λ_C` gives `Cont` (a neighbourhood
maps into the open quarter arc, and `P_C(x) < δ` says every `M_i x` is within `δ` of an integer); (ii) `ζ(x) = ∑ ρ_j θ_j` for `x`
with digits `ρ` (because `ζ ≡ z_{j+1}` mod `M_{j+1}`); (iii) `Ẑ = lim ℤ/M_k` when every integer divides some `M_k`.

## LeanCheck/ChainCRT.lean and LeanCheck/ChainG.lean  -- the two-chain construction (Theorem H), compile, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only.

| Note | Lean | Statement |
|---|---|---|
| CRT with one non-coprime pair | `crt_solvable` | `0<L, 0<E`, `gcd L E ∣ g` ⇒ for every `B` there is `X ≥ B` with `L ∣ X`, `E ∣ X + g` (Bezout) |
| gcd/lcm distributivity | `gcd_lcm_dvd` | `gcd (lcm a b) c ∣ lcm (gcd a c) (gcd b c)` (via factorizations) |
| one step | `crt_step` | `g ∣ g'`, `W ∣ g'` ⇒ `M' ≥ B` with `M ∣ M'`, `W ∣ M'`, `(M+g) ∣ (M'+g')`; this is exactly `gcd(lcm(M,W), M+g) ∣ g'` |
| the whole sequence | `two_chains_exists` | for any chain `g` (`g_0=1`, `g_n ∣ g_{n+1}`) and `W_{n+1} ∣ g_{n+1}`: `M` with `M_0=1`, `M_n ∣ M_{n+1}`, `W_{n+1} ∣ M_{n+1}`, `E_n ∣ E_{n+1}` (`E_n = M_n+g_n`), `R_n M_n ≤ M_{n+1}`, `g_{n+1} ≤ M_{n+1}` |
| concrete `G` | `rG`, `gG`, `gG_runs`, `factorial_dvd_gG`, `gG_null`, `WG`, `WG_dvd`, `WG_null` | ratios `s+1` at `k=(s)²` and `2` elsewhere; arbitrarily long runs of ratio 2; `(S+1)! ∣ g_n` for `n > S²`; `W_n = ⌊√(n-1)⌋!` divides `g_n` |
| everything together | `theoremH_data` | `M_n` and `E_n = M_n + g_n` are divisibility chains with ratios `≥ n+2` and `≥ (n+2)/2`, and every positive integer divides `M_n`, `E_n`, `g_n` for large `n` |

(The paper's `G` used stretches of `s+3` ratio-2 steps; the Lean `G` uses `2s` ratio-2 steps between consecutive squares. Both have
arbitrarily long ratio-2 runs and profinitely null products, which is all Theorem H uses.)

## LeanCheck/ChainJoin.lean  -- the join argument (triangle inequality + contraction), compiles, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only (all 34 checked declarations in Axioms.lean).

| Note | Lean | Statement |
|---|---|---|
| bottom of a ratio-2 run | `run_near` | `g_{a+j+1} = 2 g_{a+j}` for `j < L`, `3δ' < 1`, every `g_n x` within `δ'` of an integer ⇒ `g_a x` within `δ'/2^L` of an integer |
| join ball ⇒ `ζ_G` small | `join_cont` | `M_n x` and `(M_n + g_n) x` within `δ < 1/16` of integers for all `n` ⇒ for every `S`, `∑_{s<S} g_{a_s} x` is within `1/4` of an integer (triangle inequality `g_n x = E_n x - M_n x`, then `run_near`, then the geometric sum with `L_s ≥ s+1`) |
| core of Theorem H | `counterexample_core` | there are `M` and run bottoms `a` with all the divisibility/growth/nullness data of `theoremH_data` AND the join statement above for the concrete `G` |

Here `x` is any real number (a representative of an element of `ℚ/ℤ`); the finite partial sums stand for `ζ_G x`, since `g_{a_s} x ∈ ℤ`
for large `s` when `x` is rational (profinite nullness of `G`, `gG_null`).

## LeanCheck/ChainNonInt.lean  -- `ζ_G = ∑_s g_{a_s}` is not an integer of the profinite completion, compiles, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only (all 42 checked declarations in Axioms.lean).

`aG s = (s+1)² + 1` (in `ChainG.lean`, with `gG_run_aG`: the run at `a_s` has `s+1` ratio-2 steps), `Psum S = ∑_{s<S} g_{a_s}`.

| Note | Lean | Statement |
|---|---|---|
| growth of run bottoms | `q_double`, `q_ge`, `Psum_le` | `2^{s+1} g_{a_s} ≤ g_{a_{s+1}}`; `2^s ≤ g_{a_s}`; `2 P_s ≤ g_{a_s}` for `s ≥ 1` |
| tails | `tail_dvd` | if `d ∣ g_{a_t}` for all `t ≥ s` then `d ∣ P_S - P_s` |
| non-integrality | `zetaG_not_integer` | there is no integer `u` with `ζ_G ≡ u (mod N)` for every `N > 0` (i.e. `N ∣ P_S - u` for all large `S`) |
| residues modulo a null chain | `zetaG_residues_exist` | for any divisibility chain `M` with `M_n > 0`, there is a compatible system `z` (`M_k ∣ z_{k+1} - z_k`) with `z_k ≡ P_S (mod M_k)` for large `S` |
| in the sense of `case_dichotomy` | `zetaG_not_M_integer` | for a null chain `M` and such `z`: there are no `u`, `i₁` with `M_{i+1} ∣ z_{i+1} - u` for all `i ≥ i₁` |

Proof idea of `zetaG_not_integer`: modulo `g_{a_s}` and modulo `g_{a_s + 1} = 2 g_{a_s}` the partial sums `P_s` and `P_{s+1} = P_s + g_{a_s}`
are both `≡ u`, which forces `(P_s - u)/g_{a_s}` to be odd, hence `|P_s - u| ≥ g_{a_s}`; with `0 ≤ P_s ≤ g_{a_s}/2` this gives
`2|u| ≥ g_{a_s} ≥ 2^s`, impossible for `s = |u| + 1`.

Not formalized: Theorem 24.3 (quotient lifting), the quarter-arc criterion as an equivalence, and the three modelling assumptions
of `case_dichotomy`; the glue "compatible by `case_dichotomy` for each chain, `ζ_G` continuous for the join by `join_cont`, `ζ_G` not an integer by
`zetaG_not_M_integer`" is therefore an argument on paper, with each ingredient machine-checked. (The ℚ-side irrationality of
`γ = ∑ 1/M_{b_i}` of Theorem F is also not formalized; it is not used in Theorem H.)
(First full `lake build` after adding files can take 15-20 minutes on this drive while Mathlib traces are re-hashed; later builds ~1 minute.)

## LeanCheck/ChainCapstone.lean  -- the finite-level statement of Theorem H, compiles, no `sorry`,
## axioms: standard only (all 44 checked declarations in Axioms.lean; `Mseq_of_chain` uses only propext and Quot.sound).

`capstone` is one theorem about the explicit chains `F₁ = {M_n}` (ratios `α¹_n = M_{n+1}/M_n`) and `F₂ = {1} ∪ {M_n + g_n}`
(`M2`, ratios `α²_n`), with `Mseq α¹ = M` and `Mseq α² = M2 M`. It asserts, with no hypotheses:

1. `2 ≤ α¹_i`, `2 ≤ α²_i`, and both ratio sequences tend to infinity; `Mseq α¹ 0 = Mseq α² 0 = 1`; `Mseq α² (n+1) = Mseq α¹ n + g_n`.
2. `ζ_G` has compatible residue systems `z` modulo both chains (`Compat`, `Represents`).
3. For each chain and every `δ > 0`, **no** such residue system is quarter-arc continuous: `¬ Cont α z δ`
   (`case_dichotomy` for the chain, then `zetaG_not_M_integer`).
4. On the join ball (`M_n x`, `M²_n x` within `δ < 1/16` of integers for all `n`) every finite partial sum `∑_{s<S} g_{a_s} x` is within
   `1/4` of an integer (`join_cont`).

Together: `ζ_G` is a non-integer profinite integer that is discontinuous for each chain topology and quarter-arc continuous for their join.
(`capstone` also exports the profinite nullness of both chains, needed below.)

## LeanCheck/ChainTop.lean, ChainTopZeta.lean, ChainTopDict.lean, ChainTopMain.lean  -- the dictionary and the TOPOLOGICAL capstone,
## compile, no `sorry`, axioms: standard only (all 56 checked declarations in Axioms.lean).

The dictionary is now a theorem, not a paper line. Definitions:
* `TorsA` = the torsion subgroup of the circle `AddCircle 1` (= `ℚ/ℤ`); `obs C δ = {x | ∀ c ∈ C, ‖c • x‖ < δ}`;
* `basisOf C : AddGroupFilterBasis TorsA` (sets `obs C δ`, `δ > 0`; the group-topology axioms are proved), `(basisOf C).topology = λ_C`;
  the join of two such topologies is Mathlib's `⊓` (the finer topology).

| Lean | Statement |
|---|---|
| `quarter_of_continuous` | a character continuous for `λ_C` is `< 1/4` in norm on some ball `obs C δ` |
| `continuous_of_quarter`, `continuous_of_quarter_join` | conversely, if a character is `< 1/4` on a ball then it is continuous for `λ_C` (resp. for `λ_{C₁} ⊓ λ_{C₂}`, ball `obs C₁ δ ∩ obs C₂ δ`); uses `near_of_all_multiples` and `nhds_inf` |
| `zetaHom` (+ `zetaHom_apply`, `zsmul_eq`) | the profinite integer given by a compatible residue system `z` is a well-defined additive character `ℚ/ℤ → ℝ/ℤ`: `ζ x = z k • x` for any `k` with `M k • x = 0` |
| `xe`, `xe_obs`, `chi_eq` | the digit element `x = ∑ ρ_j/M_{j+1}` lies in the ball when all `M_i x` are within `δ` of integers, and `chi = z_K x + (integer)` |
| `cont_of_continuous` | **the dictionary lemma**: if `ζ_z` is continuous for `λ_{range (Mseq α)}` then `Cont α z δ` for some `δ > 0` |
| `zeta_not_continuous` | for ratios `≥ 2` tending to infinity and `z` representing `ζ_G`, `ζ_z` is NOT continuous for `λ_{range (Mseq α)}` (dictionary + `case_dichotomy` + `zetaG_not_M_integer`) |
| `zeta_eq_Psum` | every such `ζ_z` agrees with `x ↦ P_S • x` for large `S`, so all residue systems of `ζ_G` give the same character |
| `topological_capstone` | for the explicit chains `M1 = Mseq α¹`, `M2 = Mseq α²` there is one character `ζ : ℚ/ℤ → ℝ/ℤ` with: not continuous for `λ_{range M1}`, not continuous for `λ_{range M2}`, **continuous for the join `λ_{range M1} ⊓ λ_{range M2}`**, and `ζ ≠ u • id` for every integer `u` |

## LeanCheck/ChainHom.lean  -- `Hom(ℚ/ℤ, 𝕋) = Ẑ`, exact duals, and the FINAL capstone
## compiles, no `sorry`, axioms: standard only (all 64 checked declarations in Axioms.lean).

| Lean | Statement |
|---|---|
| `torsion_form` | if `m • y = 0` in the circle (`m > 0`) then `y = n • (1/m)` for an integer `n` |
| `eE`, `kill_e` | the element `1/M_k` of `ℚ/ℤ` and `M_k • (1/M_k) = 0` |
| `hom_is_zeta` | **`Hom(ℚ/ℤ, 𝕋) = Ẑ`**: for a null divisibility chain `M`, every additive character `χ : ℚ/ℤ → ℝ/ℤ` equals `ζ_z` for a compatible residue system `z` (`z_k` read off from `χ(1/M_k)`) |
| `intHom_continuous` | for `1 ∈ range M`, each `x ↦ u • x` is continuous for `λ_{range M}` |
| `dual_exact` | **compatibility**: for ratios `≥ 2` tending to infinity, `M 0 = 1`, null: a character is continuous for `λ_{range (Mseq α)}` **iff** it is `x ↦ u • x` for an integer `u` (the dual is exactly `ℤι`) |
| `t2_basisOf` | `λ_C` is Hausdorff when `1 ∈ C` |
| `zeta_join_continuous`, `zeta_not_int` | the two halves of the join argument (join continuity of `ζ_G`; `ζ_G ≠ u • id`) |
| `final_capstone` | there are `M1, M2` (`1 ∈` both ranges) and a character `ζ` such that: `λ_{range M1}`, `λ_{range M2}` are Hausdorff group topologies on `ℚ/ℤ` whose continuous characters are EXACTLY the maps `x ↦ u • x`; yet `ζ` is continuous for the join `λ_{range M1} ⊓ λ_{range M2}` and `ζ ≠ u • id` for all integers `u` |

`final_capstone` is precisely the hypothesis of Theorem 24.3 (two topologies `λ₁, λ₂` on `ℚ/ℤ` with character set exactly `ℤι` whose join has a continuous
character that is not `nι`), except that local quasi-convexity of `λ_C` is not formalized (Mathlib has no `lqc`); on paper `λ_C` is the topology of uniform
convergence on a set of characters, hence lqc.

What is left on paper: (a) local quasi-convexity of `λ_C` (the paper's remark that the closed balls of radius `1/(4n)` are intersections of preimages of quasi-convex arcs),
(b) the TVGQ transfer (the lift to ℚ is `lift_capstone`, the transfer `T_f` to ℝ is `transfer_capstone_exact`)
(and, via TVGQ-v5 Theorem `transfer-q`, to the TVGQ class); these are statements about topologies on `ℚ` and `ℝ`, not formalized here.

## LeanCheck/ChainLift.lean  -- the lift from `ℚ/ℤ` to `ℚ` (Theorem 24.3)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 72 declarations).

`γ_λ` := the initial topology on `ℚ` of the maps `t ↦ π(r t)`, `r ∈ ℚ` (`π : ℚ → ℚ/ℤ`).

| Lean | Statement |
|---|---|
| `piHom`, `piHom_surjective`, `hq r` | the quotient `π : ℚ → ℚ/ℤ` (onto the torsion subgroup of the circle) and `t ↦ π(r t)` |
| `gam`, `gam_group`, `hq_continuous` | `γ_λ` is a group topology on `ℚ` making every `hq r` continuous |
| `gam_scalar` | every rational multiplication `x ↦ s x` is `γ_λ`-continuous |
| `gam_t2` | if `λ` is Hausdorff then so is `γ_λ` (injectivity of `x ↦ (π(r x))_r`) |
| `dual_gam_mp` | if the continuous characters of `λ` are exactly `x ↦ u • x`, every `γ_λ`-continuous character of `ℚ` is `t ↦ r t mod 1` for a rational `r` (finite intersection over `r ∈ I`, common denominator `d`, descent along `hq (1/d)`, kernel killed by `eq_zero_of_multiples`) |
| `dual_gam_mpr`, `dual_gam` | converse; the dual of `γ_λ` is EXACTLY `Γ = {t ↦ r t mod 1}` |
| `lift_incompatible` | a character `ζ` of `ℚ/ℤ`, continuous for `λ₁ ⊓ λ₂` but not of the form `u • id`, yields `ψ = ζ ∘ π`, continuous for `γ_{λ₁} ⊓ γ_{λ₂}` and not in `Γ` |
| `lift_capstone` | **there are two Hausdorff group topologies `γ₁, γ₂` on `ℚ`, each with dual exactly `Γ`, whose join (`⊓` of Mathlib topologies) has a continuous character not in `Γ`** (`final_capstone` + `gam_group` + `gam_t2` + `dual_gam` + `lift_incompatible`) |

Note: `⊓` on `TopologicalSpace` is the *finer* topology, i.e. the join of the two group topologies.
Not covered here: local quasi-convexity of `γ_λ` (Mathlib has no `lqc`), and the transfer `T_f` to `𝒞_f` / TVGQ class.

## LeanCheck/ChainTransfer.lean, ChainTransferDual.lean  -- the transfer `T_f` from `ℚ` to `ℝ` (Theorem `transfer-v8`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 92 declarations).

`f : ℝ →+ ℚ` is a coefficient function (`f u = 1`), `f_a(x) = f(a x)`, `T_f(δ) = usual ⊓ ⨅_a induced f_a δ`
(`⊓` of Mathlib topologies is the join = finer topology), `χ_{c,a}(x) = p(c x + f(a x))`, `H_f = {χ_{c,a}}`.

| Lean | Statement |
|---|---|
| `Tf`, `Tf_le_usual`, `fa_cont` | the definition; `T_f(δ)` is finer than usual and every `f_a : (ℝ,T_f δ) → (ℚ,δ)` is continuous |
| `Tf_group`, `Tf_t2`, `Tf_dilation` | `T_f(δ)` is a Hausdorff group topology and every fixed dilation `x ↦ c x` is continuous (TVG) |
| `Tf_mono`, `Tf_inf` | `T_f` is monotone and `T_f(δ₁) ∨ T_f(δ₂) = T_f(δ₁ ∨ δ₂)` |
| `chiH_continuous` | every `χ_{c,a}` is `T_f(δ)`-continuous if `p : ℚ → 𝕋` is `δ`-continuous |
| `ker_uncountable`, `f_ratmul` | `ker f` is uncountable; `f` is `ℚ`-linear |
| `transfer_obstruction` | a `δ₁ ∨ δ₂`-continuous character `ψ` of `ℚ` outside `Γ` gives `ψ ∘ f`, continuous for `T_f(δ₁) ∨ T_f(δ₂)` and NOT any `χ_{c,a}` (the annihilator calculation of Lemma `quotient-v8`: `c = 0` because `ker f` is uncountable and divisible; then evaluate at `s·u`) |
| `linearize` | a character that is `< 1/4` near `0` on a dense `ℚ`-subspace `N ⊂ ℝ` is `x ↦ c x mod 1` on `N` (extension step of Lemma `finite-quotient`) |
| `Hker_dense`, `Hmap_surj`, `Hker_qmul` | the joint kernel `⋂ ker f_{b_j}` is a dense `ℚ`-subspace (countable quotient + `AddSubgroup.dense_or_isCyclic`); independent `f_{b_j}` give a surjective joint map `ℝ → ℚ^κ` |
| `indep_reduction`, `pi_box`, `packaged` | finitely many `f_a` are replaced by a `ℚ`-independent spanning subfamily (`f_a` is `ℚ`-linear in `a`), and `δ`-neighbourhood conditions by a box in `ℚ^κ` (uses rational scalar continuity) |
| `dual_Tf_mp`, `dual_Tf` | **the continuous characters of `T_f(δ)` are EXACTLY `H_f`** when `δ` is a group topology on `ℚ` with continuous rational multiplications and dual exactly `Γ` (`T_f(δ) ∈ 𝒬`-compatible) |
| `lift_capstone_scalar`, `exists_coefficient` | `lift_capstone` with scalar continuity; coefficient functions exist (`f 1 = 1`) |
| `transfer_capstone`, `transfer_capstone_exact` | **for every coefficient function `f` there are two Hausdorff TVG group topologies `T₁,T₂ ≤ usual` on `ℝ`, each with continuous character group EXACTLY `H_f`, whose join `T₁ ⊓ T₂` has a continuous character outside `H_f`** |

So the incompatible-join obstruction passes from `ℚ/ℤ` (final_capstone) to `ℚ` (lift_capstone) to `ℝ` (transfer_capstone_exact).
Not formalized: see the end of the ChainTransferQ section.

## LeanCheck/ChainLQC.lean  -- local quasi-convexity, and membership in `𝒞_f`
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 105 declarations).

Definition (paper, Section "Compatible topologies and the Mackey question"): `U` is *quasi-convex* if every `x ∉ U`
is separated from `U` by a continuous character `χ` with `χ(U) ⊆ [-1/4,1/4]+ℤ` and `χ(x) ∉ [-1/4,1/4]+ℤ`;
a topology is *locally quasi-convex* if it has a zero-neighbourhood base of quasi-convex sets.

| Lean | Statement |
|---|---|
| `QuasiConvex τ U`, `LocQC τ` | exactly the definition above (`∃ χ, Continuous χ ∧ (∀ y ∈ U, ‖χ y‖ ≤ 1/4) ∧ 1/4 < ‖χ x‖`; neighbourhood base of such `U`) |
| `qc_mono`, `qc_biInter`, `qc_inter`, `qc_preimage` | quasi-convexity is monotone in the topology, stable under intersections, and under preimages by continuous homomorphisms |
| `lqc_induced`, `lqc_inf`, `lqc_iInf` | local quasi-convexity passes to induced topologies, joins (`⊓`) and arbitrary initial topologies (`⨅`) |
| `lqc_uR` | the usual topology of `ℝ`: `[-e,e]` is quasi-convex (separating character `x ↦ (y₀/x)·t`, `y₀ = min(|x|/4e, 1/2)`) |
| `lqc_basisOf` | `λ_C` on `ℚ/ℤ`: the sets `{x : ‖(m c)·x‖ ≤ 1/4  ∀c∈C, m≤n}` are quasi-convex neighbourhoods inside `obs C δ` (`mult_le`: the non-strict quarter-arc bound) |
| `lqc_gam`, `lqc_Tf` | `γ_λ` and `T_f(δ)` are locally quasi-convex when `λ`, `δ` are |
| `final_capstone_lqc` | the chain topologies on `ℚ/ℤ`: Hausdorff, locally quasi-convex, dual exactly `ℤι`, join has an extra character |
| `lift_capstone_lqc` | the lifted `γ₁, γ₂` on `ℚ`: Hausdorff, locally quasi-convex, rational scalars continuous, dual exactly `Γ`, join has an extra character |
| `transfer_capstone_Cf` | **the two topologies on `ℝ` are Hausdorff, locally quasi-convex TVG topologies with character group exactly `H_f`, i.e. members of `𝒞_f`, and their join is NOT in `𝒞_f`** |

## LeanCheck/ChainTransferOpen.lean  -- openness of `f` and order reflection (rest of `transfer-v8`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 113 declarations).

Hypotheses: `δ` a group topology on `ℚ` with every rational multiplication continuous, `f u = 1`.

| Lean | Statement |
|---|---|
| `tf_nhds_sub` | every `T_f δ`-neighbourhood of `0` contains a basic one `{|x|<ε, f(a x) ∈ U_a (a ∈ I)}` |
| `Tf_image_nhds` | the `f`-image of a `T_f δ`-neighbourhood of `0` is a `δ`-neighbourhood of `0` (independent reduction of the `f_a` together with `f`; a box `∏ W_j`; a preimage `y` with `Σ q_j y_j = t` and a dense-kernel correction into `(-ε,ε)`) |
| `Tf_isOpenMap` | **`f : (ℝ, T_f δ) → (ℚ, δ)` is an open map** (translation argument in the topological group) |
| `f_surjective`, `Tf_coinduced` | `f` is onto, and `δ` is exactly the quotient topology of `T_f δ` along `f` |
| `Tf_le_iff` | **order embedding**: `T_f δ₁ ≤ T_f δ₂ ↔ δ₁ ≤ δ₂` (reflection through `coinduced_mono`) |
| `Tf_injective` | `δ ↦ T_f δ` is injective on such `δ` |
| `transfer_join_quotient` | for the incompatible pair `γ₁,γ₂` on `ℚ`: `f` is open from `T_f γ_i` onto `(ℚ,γ_i)`, `T_f γ₁ ∨ T_f γ₂ = T_f(γ₁ ∨ γ₂)`, and `f` is open from that join onto `(ℚ, γ₁ ∨ γ₂)`, which carries a continuous character outside `Γ` |

All statements of Theorem `transfer-v8` are now machine-checked except the TVGQ version (`transfer-q`, rational dilations).

## LeanCheck/ChainTransferQ.lean  -- the TVGQ transfer (Theorem `transfer-q` of TVGQ-v7)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 129 declarations).

TVGQ: only rational dilations. `S_f(δ) = init{id : ℝ → ℝ_usual, f : ℝ → (ℚ,δ)}` (`Tq f δ`);
`H_{f,ℚ} = {x ↦ p(c x + r f(x)) : c ∈ ℝ, r ∈ ℚ}` (written `chiH f c (r:ℝ)`).

| Lean | Statement |
|---|---|
| `Tq`, `Tq_group`, `Tq_t2`, `lqc_Tq` | `S_f δ` is a Hausdorff, locally quasi-convex group topology finer than usual |
| `Tq_rat_dilation` | every rational dilation `x ↦ q x` is continuous (the TVGQ property; needs `δ` scalar-continuous) |
| `Tq_mono`, `Tq_inf` | monotone, and `S_f δ₁ ∨ S_f δ₂ = S_f (δ₁ ∨ δ₂)` |
| `Tq_image_nhds`, `Tq_isOpenMap`, `Tq_coinduced` | `f : (ℝ, S_f δ) → (ℚ, δ)` is an open continuous surjection and `δ` is its quotient topology |
| `Tq_le_iff` | order embedding: `S_f δ₁ ≤ S_f δ₂ ↔ δ₁ ≤ δ₂` |
| `dual_Tq_mp`, `dual_Tq` | the continuous characters of `S_f δ` are EXACTLY `H_{f,ℚ}` when `δ` is a group topology with dual `Γ` (linearization on the dense kernel of `f`, then a character of `(ℚ,δ)`) |
| `transferQ_obstruction` | an extra character of `δ₁ ∨ δ₂` transfers to a character of `S_f δ₁ ∨ S_f δ₂` outside `H_{f,ℚ}` |
| `Tq_join_compat` | `S_f δ₁ ∨ S_f δ₂` has dual `H_{f,ℚ}` **iff** `δ₁ ∨ δ₂` has dual `Γ` |
| `gamma0`, `sigmaQ`, `Tq_gamma0` | `S_f(γ₀) = σ_{f,ℚ}` |
| `transfer_capstone_Q` | **two Hausdorff locally quasi-convex group topologies on `ℝ`, finer than usual, with continuous rational dilations and dual exactly `H_{f,ℚ}` (i.e. members of `𝒞^ℚ_{f,ℚ}`), whose join has a continuous character outside `H_{f,ℚ}`; so `(ℝ, H_{f,ℚ})` has no greatest compatible TVGQ topology** |

Together with `transfer_capstone_Cf` (TVG) this covers both halves of TVGQ-v7 Theorem `twochains:transfer`.
Not formalized: the Hamel-side statements about `β_{f,S}`, `σ_{f,S}`, `τ_{f,S}` beyond `σ_{f,ℚ} = S_f(γ₀)`, rational saturation (`thm:saturation`), and the real-analytic material of the rest of the papers.

## LeanCheck/ChainSaturation.lean  -- rational scalar saturation (TVGQ-v7 Theorem `saturation`, Corollary `mackey-equivalence`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 141 declarations).

Setting: `G` a `ℚ`-vector space, `H` a set of characters with `RatInv H` (`χ ∈ H ⇒ χ ∘ (q·) ∈ H`).
`satn η n` = pullback of `η` under `x ↦ x/n!`; `sat η = ⨅ n, satn η n` (= `⋁ η_n`, since Mathlib's `⊓` is the join).
`Lcls H` = Hausdorff locally quasi-convex group topologies with full character set `H`; `Ccls H` = those with all rational dilations continuous.

| Lean | Statement |
|---|---|
| `satn_zero`, `satn_succ_le`, `satn_anti` | `η₀ = η` and `η_{n+1} ≤ η_n` (i.e. `η_n ⊆ η_{n+1}`: integer multiplication is continuous and `m_{1/n!} = m_{n+1} ∘ m_{1/(n+1)!}`) |
| `sat_group`, `sat_t2`, `sat_lqc`, `sat_le` | `η^[ℚ]` is a group topology, Hausdorff and locally quasi-convex when `η` is, and `η ⊆ η^[ℚ]` |
| `sat_rat_cont` | **every rational dilation is `η^[ℚ]`-continuous** (for `q = a/b` choose `k = n!·b` with `b·n! ∣ k!`: `m_{1/n!} ∘ m_q = m_{a t} ∘ m_{1/k!}`, `k! = n!·b·t`) |
| `sat_least` | `η^[ℚ]` is the least rational-scalar-continuous group topology containing `η` |
| `satn_dual`, `sat_dual` | dual of `η_n` is `H`; dual of `η^[ℚ]` is `H` (quarter-arc argument: finitely many `η_n` in a neighbourhood are dominated by one `η_M`) |
| `saturation` | **Theorem**: `η ∈ ℒ(H) ⇒ η^[ℚ] ∈ 𝒞_ℚ(H)`, `η ⊆ η^[ℚ]`, leastness |
| `mackey_equivalence` | **Corollary**: `μ` is greatest in `𝒞_ℚ(H)` iff it is greatest in `ℒ(H)`; maximal members of `ℒ(H)` lie in `𝒞_ℚ(H)` |
| `Hq`, `Hq_ratInv` | `H_{f,ℚ}` is rationally invariant |
| `no_greatest_compatible_Q` | **neither `ℒ(H_{f,ℚ})` nor `𝒞_ℚ(H_{f,ℚ})` has a greatest member: the dual pair `(ℝ, H_{f,ℚ})` has no Mackey topology** (transfer_capstone_Q + mackey_equivalence) |

## LeanCheck/ChainHamel*.lean  -- the Hamel-side topologies `β_{f,S}`, `σ_{f,S}`, `τ_{f,S}` (TVGQ-v7)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 191 declarations).

Files: ChainHamel (definitions, relations), ChainHamelDual (characters), ChainHamelStrict (strict separation),
ChainHamelTau (real-valued dual of `τ`), ChainHamelScalar (scalar rings, order), ChainHamelFinal (non-discreteness,
unboundedness of `β`, incomparability, summary).  `S` is a `ℚ`-subspace of `ℝ` (`Submodule ℚ ℝ`), `f u = 1`.

* `betaT = init{x ↦ p(bx), x ↦ p(f(ax)) : b ∈ ℝ, a ∈ S}`, `sigmaT = TfS f S γ₀ = tu ∨ β` (`sigmaT_eq`),
  `tauT = TfS f S (ℚ_usual) = init{id, f_a : ℝ → ℚ_usual}`.  Mathlib's `⊓` is the join, so `β ⊆ σ ⊆ τ` is `τ ≤ σ ≤ β`.

| Lean | Statement (TVGQ-v7) |
|---|---|
| `hamel_prop_basic` | **Prop. basic**: the three topologies are Hausdorff non-discrete group topologies with continuous rational dilations; `τ ≤ σ ≤ β`; `σ = tu ∨ β` |
| `circ_dual`, `gamma0_dual` | continuous characters of `ℚ/ℤ` with the circle topology are `ℤι`; the dual of `γ₀ = init{p(r·)}` is `Γ` |
| `mixed_zero`, `chiH_unique` | **Lemma mixed**: `p(cx+f(ax)) ≡ 0 ⇒ c = a = 0`; the parameters of `H_{f,S}` are unique |
| `dual_TfS_mp`, `dual_sigma`, `dual_beta` | **Thm characters**: the continuous characters of `σ_{f,S}` and of `β_{f,S}` are exactly `H_{f,S} = {p(cx+f(ax)) : c ∈ ℝ, a ∈ S}` (`a ∈ S`) |
| `usual_char`, `pfHom_not_usual` | **Lemma usual**: usual-continuous characters are `p(cx)`; `p∘f_a` is not usual-continuous for `a ≠ 0` |
| `sigmaT_lt_usual` | **Thm strict (1)**: `tu ⊊ σ_{f,S}` |
| `sigma_nhds_sub`, `sigma_unbounded` | every nonzero rational-valued additive `g` is unbounded on every `σ_{f,S}`-neighbourhood of `0` (pigeonhole/dense kernels) |
| `not_cont_sigma_rat`, `no_rat_dual_beta` | the continuous rational-valued additive duals of `σ` and `β` are zero |
| `tauT_lt_sigmaT` | **Thm strict (2)**: `σ_{f,S} ⊊ τ_{f,S}` |
| `beta_not_le_usual`, `usual_not_le_beta` | `β_{f,S}` is incomparable with the usual topology |
| `dual_sigma_real` | `Hom_cont((ℝ,σ_{f,S}), ℝ_usual) = ℝ·id` |
| `dual_beta_real`, `beta_unbounded` | `Hom_cont((ℝ,β_{f,S}), ℝ_usual) = 0` (`β`-neighbourhoods are unbounded: pigeonhole in the compact torus) |
| `dual_tau_real` | **Thm realcompletion (dual part)**: continuous additive `g : (ℝ,τ_{f,S}) → ℝ` are `c x + ∑ d_j f(b_j x)`, `b_j ∈ S` (`f_{b_j}` `ℚ`-independent) |
| `scalar_tau`, `scalar_sigma`, `scalar_beta` | **Thm scalar**: `m_r` is continuous for `τ`, `σ`, `β` iff `r S ⊆ S`, i.e. `C_η = M(S)` |
| `scalarRing_algebra` | **Cor. algebra**: `M(A) = A` for every unital `ℚ`-subalgebra `A`, so every such `A` occurs as exact scalar ring |
| `order_beta`, `order_sigma`, `order_tau` | **Thm order**: `S ⊆ T ⇔ β_S ⊆ β_T ⇔ σ_S ⊆ σ_T ⇔ τ_S ⊆ τ_T`; hence `betaT_injective`, `sigmaT_injective`, `tauT_injective` |

Not formalized (Hamel side): the completion theorems `Comp(σ) ≅ ℝ × K_S`, `Comp(β) ≅ K_ℝ × K_S`, `Comp(τ) ≅ ℝ × ℝ^B`
(and the rational-case corollary on metrizability/`K_ℚ`), precompactness of `β` as a formal statement
(only its consequence `beta_unbounded` is proved), the transcendental-scalar example, the sequence-separation theorems
(Pell sequence, universal sequences), the classification of precompact TVGQ topologies (`θ_H`), and the isomorphism classification.

## LeanCheck/ChainPrecompact.lean  -- classification of precompact TVGQ topologies (TVGQ-v7 Theorem `classification`, Prop. `minimal`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 216 declarations).

`Chars = Hom(ℝ, 𝕋)`; `theta H = init{χ : χ ∈ H}` (`θ_H`); `Separates H`; `Precompact τ` (finitely many translates of every
neighbourhood of 0 cover); `PTVGQ τ` = Hausdorff precompact group topology with continuous rational dilations.

**Unconditional (proved from scratch):**

| Lean | Statement |
|---|---|
| `theta_group`, `theta_t2`, `sep_of_theta_t2` | `θ_H` is a group topology; Hausdorff iff `H` separates points |
| `theta_precompact` | `θ_H` is precompact for every `H` (compactness of the torus `𝕋^I`, finite sub-cover) |
| `precompact_of_le` | coarser topologies of a precompact one are precompact |
| `theta_mono`, `theta_cont_of_mem` | `H ⊆ H' ⇒ θ_{H'} ≤ θ_H`; characters in `H` are `θ_H`-continuous |
| `theta_ratdil`, `theta_ptvgq`, `dualGroup_ratInv` | `H` rationally invariant ⇒ `θ_H` is TVGQ; conversely the dual of a TVGQ group topology is rationally invariant |
| `betaT_eq_theta`, `dual_theta_Hset` | `β_{f,S} = θ_{H_{f,S}}`, and (F1) holds for `H_{f,S}` |
| `HQ_separates`, `HQ_ratInv`, `thetaQ_ptvgq`, `thetaQ_eq`, `thetaQ_metrizable` | **Prop. minimal (unconditional part)**: `θ_ℚ = θ_{H_ℚ}` is a Hausdorff precompact TVGQ topology, and it is metrizable (embedding into `ℚ → 𝕋`) |

**Conditional on `PrecompactDuality`** -- the two standard facts the paper quotes from compact duality (Weil; Comfort–Ross), which
Mathlib cannot supply (no Pontryagin duality / Peter–Weyl): (F1) for point-separating `H`, the continuous characters of `θ_H` are exactly `H`;
(F2) every Hausdorff precompact group topology is `θ` of its dual. They enter as the explicit hypothesis `hD : PrecompactDuality`.

| Lean | Statement (under `hD`) |
|---|---|
| `classification` | **Thm classification**: (1) `θ_H` is Hausdorff precompact TVGQ for point-separating rational `H`; (2) every such topology is `θ_H`; (3) `H ↦ θ_H` is injective and order-preserving in both directions |
| `classificationEquiv` | the bijection `{H // Separates ∧ RatInv} ≃ {τ // PTVGQ τ}` |
| `theta_injective`, `theta_le_iff`, `dualGroup_theta` | injectivity, order isomorphism, `dual(θ_H) = H` |
| `theta_scalar` | `C_{θ_H} = { a : ∀ χ ∈ H, χ ∘ m_a ∈ H }` |
| `thetaQ_scalar` | `C_{θ_ℚ} = ℚ` |
| `thetaQ_minimal` | `θ_ℚ` is minimal among Hausdorff TVGQ topologies |
| `thetaQ_lt_bohr` | `θ_ℚ` is strictly coarser than the Bohr topology `init{p(b x)}` |

Cross-check: `scalar_beta` (proved earlier, unconditionally) is the instance `H = H_{f,S}` of `theta_scalar`.
Not formalized at the time of this section: proofs of (F1)/(F2) themselves -- (F1) is proved in ChainDuality, and (F2) is now proved in ChainPW1..PW7 (see the last section); the `*_unc` theorems in ChainPW8 are the unconditional versions.

## LeanCheck/ChainDualityCore.lean, ChainDuality.lean  -- the duality fact (F1) is now PROVED; TVG classification
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 233 declarations).

(F1): for every subgroup `H ≤ 𝒜 = Hom(ℝ,𝕋)`, the continuous characters of `θ_H` are exactly `H`.

| Lean | Statement |
|---|---|
| `integral_char_eq_zero` | orthogonality: a multiplicative `ψ ≠ 1` integrates to `0` against an invariant (Haar) measure |
| `char_in_span` | **Fourier core**: on a compact Hausdorff abelian group `T` with finitely many continuous characters `z_i : T → 𝕋` separating points, every continuous character `w` is an integer combination `∑ k_i z_i` (Stone–Weierstrass for the span of the monomials + Haar orthogonality) |
| `fourier_reduction` | a character `χ` of an abelian group `G`, small on `Φ⁻¹(U)` for `Φ : G → 𝕋^I`, `U ∈ 𝓝 0`, equals `∑ k_i Φ_i`: apply `char_in_span` on the closure of the image of `(Φ,χ)` in `𝕋^I × 𝕋` (the coordinates of `Φ` separate its points because a subgroup of `𝕋` inside `[-1/4,1/4]` is `0`) |
| `dual_theta_iff`, `dualThetaFact` | **(F1)**: `χ` is `θ_H`-continuous iff `χ ∈ H` (no hypotheses on `H`) |
| `theta_injective_unc`, `theta_le_iff_unc`, `theta_scalar_unc` | injectivity of `H ↦ θ_H`, order isomorphism, scalar formula `C_{θ_H} = {a : χ∘m_a ∈ H ∀χ∈H}` -- now unconditional |
| `thetaQ_scalar_unc`, `thetaQ_lt_bohr_unc` | `C_{θ_ℚ} = ℚ` and `θ_ℚ ⊊ Bohr`, unconditional |
| `PrecompactDuality.of_generated` | the full duality hypothesis follows from (F2) alone |

Real scalars (TVG): `RealInv`, `PTVG`, `theta_realdil`, `theta_ptvg`, `dualGroup_realInv`;
`classification_TVG` -- point-separating real subspaces of `𝒜` ↔ Hausdorff precompact TVG topologies (only (F2) assumed);
`no_greatest_compatible_TVG` -- the class of Hausdorff locally quasi-convex TVG topologies with character group `H_f` has no greatest member
(the TVG counterpart of `no_greatest_compatible_Q`).

(F2) = `GeneratedFact` was assumed here; it is now PROVED (`generatedFact`, ChainPW7), so `classification`, `classificationEquiv`, `thetaQ_minimal`, `classification_TVG` hold unconditionally (`classification_unc`, ... in ChainPW8).
It is used by `classification`, `classificationEquiv`, `thetaQ_minimal`, `classification_TVG` (part 2 only).

## LeanCheck/ChainPell.lean, ChainUniversal.lean, ChainUniversal2.lean  -- sequence separation (TVGQ-v7, §"Sequence separation and its quantifiers")
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 267 declarations).

`pz n = n! (3 - 2√2)^{n²} = n! (P_n - Q_n √2)` with `(3 + 2√2)^k = P_k + Q_k √2` (`pq`, `pq_plus`, `pq_minus`).
A sequence *separates* `σ_{f,S}` from `τ_{f,S}` if it is `σ`-null and not `τ`-null; *universal* = separates for every nonzero `f : ℝ →+ ℚ`.

| Lean | Statement |
|---|---|
| `pz_tendsto_zero`, `qn_tendsto` | `z_n → 0` usually; `n! Q_{n²} → ∞` |
| `tendsto_TfS_iff`, `tendsto_sigma_iff`, `tendsto_tau_iff` | convergence in `σ_{f,S}` = usual convergence + `p(f(a x_n)) → 0`; in `τ_{f,S}` = usual convergence + `f(a x_n) → 0` |
| `g_pz`, `g_pz_real`, `g_pz_int`, `abs_g_pz_tendsto` | the Pell identities: `f(t z_n) = n!(P f(t) - Q f(t√2))` (eventually an integer) and `f(t z_n) = f(t) z_n + n!Q(√2 f(t) - f(t√2))` (divergent when the bracket ≠ 0) |
| `modular_conv`, `modular_conv_beta` | `y · z_n → 0` in `σ_{f,S}` and `β_{f,S}` for every `y`, `f`, `S` |
| `pell_criterion` | **Thm pell-criterion**: `z_n → 0` in `σ`, `β` for every `f`; it fails to converge in `τ_{f,S}` iff `f` is nonzero on `S + √2 S` |
| `pell_separates_iff` | `z_n` separates for every nonzero `f` iff `S + √2 S = ℝ` |
| `pell_scaled` | **Thm scaled-sequence**: for every nonzero `f` and nonzero `S` there is `y ≠ 0` with `y z_n → 0` in `σ`, `β`, not in `τ`, `|f(a₀ y z_n)| → ∞`, `{0, x_n}` compact for `σ`, `β` and not compact for `τ` |
| `no_universal`, `no_universal_sequence`, `no_universal_separating` | **Thm no-universal**: if `dim_ℚ S < 𝔠` every sequence is killed by some nonzero `f` (cardinality of a Hamel basis), so a usually-null sequence is `τ`-null and no universal sequence exists |
| `finite_universal` | **Lemma finite-universal**: if a sequence is `σ_{f,S}`-null for every nonzero `f`, its rational span is finite-dimensional |
| `universal_necessary`, `universal_sufficient`, `reduce_irrational` | the two directions of the complete criterion (sufficiency by interleaved Diophantine approximants `n!(p - qθ_i)`, `q > n`) |
| `universal_complete` | **Thm universal-complete**: a universal separating sequence exists iff finitely many reals `b_t` satisfy `∑ b_t S = ℝ` |
| `universal_complete_beta`, `finite_codim_universal` | the sequence also converges in every `β_{f,S}`; every nonzero `S` of finite rational codimension (e.g. `S = ℝ`) admits a universal sequence |

The field case of Corollary `field-universal` (Artin–Schreier) is now formalized: see ChainArtinSchreier.lean and ChainFieldUniversal.lean at the end of this file.

## LeanCheck/ChainIso1.lean ... ChainIso7.lean  -- isomorphism classification (TVGQ-v7, §"Isomorphism classification of the modular families" and §"Additive isomorphisms of the real-valued observation spaces")
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 318 declarations).

Notation: `Fset f S = {f_a : a ∈ S}`, `FsetScaled g c T = {g_{ca} : a ∈ T}`, `IsoTop η₁ η₂` = an additive bijection `ℝ ≃+ ℝ`
continuous in both directions, `scalarCont η` = the real scalars `r` with `x ↦ r x` continuous.

**ChainIso1 / ChainIso2 -- `β` and `σ` (Thm isomorphism-v3, Cor isomorphism-v3)**

| Lean | Statement |
|---|---|
| `rigidity_beta`, `rigidity_sigma` | every continuous additive `L : (ℝ, η_{f,S}) → (ℝ, η_{g,T})` is `x ↦ c x` (no real linearity assumed) |
| `scale_cont_beta_iff`, `scale_cont_sigma_iff` | `m_c` is continuous iff `FsetScaled g c T ⊆ Fset f S` |
| `iso_iff_beta`, `iso_iff_sigma` | isomorphic iff `FsetScaled g c T = Fset f S` for some `c ≠ 0` |
| `scalarCont_eq_of_iso_beta/_sigma`, `iso_algebra_beta/_sigma` | the continuous scalar ring is an isomorphism invariant; distinct subalgebras (intermediate fields) as parameter spaces give non-isomorphic groups |
| `iso_fixed_beta/_sigma` | for fixed `f ≠ 0`: isomorphic iff `S = c T` (injectivity of `a ↦ f_a`: `fa_inj`) |
| `iso_Q_beta/_sigma` | for `S = T = ℚ` (`ratSub`): iff `g(cx) = r f(x)` with `c ≠ 0`, `r ∈ ℚ \ {0}` |
| `not_iso_beta_sigma`, `not_iso_sigma_beta` | `β_{f,S}` (precompact) is never isomorphic to `σ_{g,T}` (usual line is a continuous quotient) |

**ChainIso3 -- Lemma tauiso:maps, Thm tauiso:hom**

| Lean | Statement |
|---|---|
| `rat_dual_tau`, `tau_rat_iff` | the continuous rational-valued additive maps on `τ_{f,S}` are exactly `Fset f S` |
| `tau_real_iff` | the continuous real-valued ones are exactly `c x + ∑ d_j f(b_j x)`, `b_j ∈ S` |
| `tau_hom_necessary`, `tau_hom_sufficient`, `tau_hom_iff` | `L : τ_{f,S} → τ_{g,T}` is continuous iff it has that form and (for `c ≠ 0`) `FsetScaled g c T ⊆ Fset f S` (automatic for `c = 0`: `fscaled_zero_sub`) |

**ChainIso4 / ChainIso5 -- Thm tauiso:iso, Cor tauiso:types**

| Lean | Statement |
|---|---|
| `tau_iso_criterion` | `L = m_c ∘ (id + Λ)`, `Λ x = ∑ σ_j f(b_j x)`, is an isomorphism iff `A = (id+Λ)|_W` is invertible on `W = span_ℚ{σ_j}` (`AInv`, `Wsp`) and `FsetScaled g c T = Fset f S` |
| `tau_iso_inverse` | the inverse formula `L⁻¹ y = y/c − ∑ τ_j f(b_j (y/c))` with `τ_j = A⁻¹σ_j` (`Ninv`, `Ninv_spec`) |
| `tau_iso_rep`, `tau_iso_iff` | every isomorphism has the form with `c ≠ 0` (countable-image argument, `eq_zero_of_span`); isomorphic iff `FsetScaled g c T = Fset f S` for some `c ≠ 0` |
| `scalarCont_eq_of_iso_tau`, `iso_algebra_tau`, `iso_fixed_tau`, `iso_Q_tau` | scalar-ring invariance, subalgebra distinction, `S = cT`, and the `ℚ` criterion for `τ` |

**ChainIso6 -- Cor tauiso:auto**

| Lean | Statement |
|---|---|
| `tau_auto_iff` | the automorphisms of `(ℝ, τ_{f,ℚ})` are exactly `L_{c,s} x = c x + s f(x)` (`Lcs`) with `c ∈ ℚ \ {0}`, `c + f(s) ≠ 0` |
| `Lcs_comp`, `Lcs_Linv`, `Linv_Lcs` | `L_{c,s} ∘ L_{c',s'} = L_{cc', c s' + c' s + s f(s')}`; the inverse `y/c − s f(y)/(c(c + f s))` |
| `ainv_unit_iff` | in the one-term case `A` is invertible iff `1 + f(σ₀) ≠ 0` |
| `Mshear_comp`, `shear_hom`, `shear_section`, `shear_section_mul`, `shear_kernel` | the shears `M_s = L_{1,s}`: `M_s ↦ 1 + f(s)` is multiplicative, onto `ℚ \ {0}` with multiplicative section `q ↦ M_{(q-1)u}` (`f u = 1`), kernel `{M_k : f k = 0}` composing additively (the split-extension structure, stated as identities, not as a packaged semidirect product) |
| `shear_comm_left`, `shear_comm_right`, `shear_nonabelian` | `M_u M_k = M_{u+k}`, `M_k M_u = M_{u+2k}`, hence nonabelian |
| `shear_auto` | if `1 ∈ S` and `1 + f(s) ≠ 0`, `M_s` is an automorphism of `(ℝ, τ_{f,S})` |

**ChainIso7 -- exactly `2^𝔠` isomorphism types**

| Lean | Statement |
|---|---|
| `isoTop_refl/_symm/_trans`, `isoSetoid` | isomorphism is an equivalence relation on an indexed family of topologies |
| `count_types` | abstract counting: `#X = 2^𝔠` and every class `≤ 𝔠` give `#(X/≈) = 2^𝔠` |
| `card_addHom`, `card_nonzero_addHom` | `#(ℝ →+ ℚ) = #{f ≠ 0} = 2^𝔠` (Hamel basis of size `𝔠`) |
| `class_le` | for fixed `f`, `{g : g(cx) = r f(x)}` has size `≤ 𝔠` since `g(x) = r f(x/c)` |
| `count_beta_types`, `count_sigma_types`, `count_tau_types` | exactly `2^𝔠` isomorphism types in each of `{β_{f,ℚ}}`, `{σ_{f,ℚ}}`, `{τ_{f,ℚ}}` |

Nothing here assumes (F2); this section is unconditional.
## LeanCheck/ChainKronecker.lean, ChainComp1.lean ... ChainComp6.lean  -- completions (TVGQ-v7, §"Completions and the full modular character groups", Thm realcompletion, Cor rational)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 350 declarations). Unconditional (no F2).

"`Comp(ℝ,η) ≅ X`" is formalized as the standard characterization of the completion: a topological-group embedding
`J : (ℝ,η) → X` (`IsInducing`) with dense range into a complete (locally compact) Hausdorff abelian group `X`.
The identification with Mathlib's abstract `UniformSpace.Completion` (uniqueness of completions) is *not* constructed.
`PD A = Hom(A_d, 𝕋)` (`abbrev PD A := A →+ Circ`) carries the topology of pointwise convergence (as `UniformSpace.comap` of the
product), so `K_S = PD S`, `K_ℝ = PD ℝ`; `S = ℚ` is `ratSub`.

| Lean | Statement |
|---|---|
| `kronecker_mem`, `kronecker_range` | **Kronecker** for a finite torus `𝕋^I`: if `C ≤ 𝕋^I` is a closed subgroup and `s₀` satisfies every integer relation holding on `C`, then `s₀ ∈ C`; so the closure of `Ψ(G)` contains every point obeying the integer relations of `Ψ`. Proof: Haar measure on `C` + trigonometric polynomials dense (`trig_dense`, Stone–Weierstrass) + orthogonality (`integral_char_eq_zero`) |
| `PD.compact`, `PD.complete`, `PD.isUniformAddGroup`, `PD.t2`, `pd_isClosedEmbedding` | `K_A` is a compact Hausdorff (hence complete) uniform additive group |
| `eHom`, `jHom`, `ISigma`, `JBeta` | `e(x)(b) = p(bx)`, `j_S(x)(a) = p(f(ax))`, `I_S(x) = (x, j_S x)`, `J_S(x) = (e x, j_S x)` |
| `ISigma_inducing`, `JBeta_inducing` | `I_S` induces exactly `σ_{f,S}`, `J_S` induces exactly `β_{f,S}` |
| `approx_chars` | simultaneous approximation of `ψ ∈ K_ℝ`, `φ ∈ K_S` by orbits `x` (Kronecker + `mixed_zero`: the characters `p(cx + f(ax))` are independent) |
| `ISigma_denseRange`, `JBeta_denseRange` | the images are dense (σ: plus density of the joint kernel `Hker_dense` for the real coordinate) |
| `completion_sigma`, `completion_beta` | **Thm completion**: `Comp(ℝ,σ_{f,S}) ≅ ℝ × K_S`, `Comp(ℝ,β_{f,S}) ≅ K_ℝ × K_S` |
| `GTau`, `Fa_indep`, `faR_cont_span`, `GTau_inducing`, `GTau_denseRange`, `completion_tau` | **Thm realcompletion**: for a rational basis `{b_j}` of `S`, `G_B(x) = (x,(f(b_j x))_j)` embeds `τ_{f,S}` densely into `ℝ × ℝ^B`. The continuous real-valued maps are `tau_real_iff` (ChainIso3) |
| `beta_not_firstCountable`, `beta_not_metrizable` | `β_{f,S}` is not first countable (hence not metrizable) for **every** `S` -- via the duality fact F1 (`dual_theta_iff`): a countable neighbourhood base would make `θ_H = θ_{H₀}` for a countable `H₀` whose dual is `H₀`, but the dual `H_{f,S}` is uncountable |
| `sigma_metrizable_Q`, `tau_metrizable_Q` | `σ_{f,ℚ}`, `τ_{f,ℚ}` are metrizable (embeddings into `ℝ × K_ℚ`, `ℝ²`; `K_ℚ` is a countable product) |
| `completion_rational` | **Cor rational**: completions `K_ℝ×K_ℚ`, `ℝ×K_ℚ`, `ℝ²` and metrizability `σ,τ` yes / `β` no, all in one statement |
| `eS`, `thetaS`, `completion_thetaS`, `thetaQ_eq_thetaS`, `completion_thetaQ` | `Comp(ℝ,θ_S) ≅ K_S` for every rational subspace `S`; in particular `Comp(ℝ,θ_ℚ) ≅ K_ℚ` |

Already formalized earlier and part of **Thm characters**: `dual_sigma`, `dual_beta` (full character groups `H_{f,S}`), `chiH_unique` (unique parameters),
`dual_sigma_real` (`Hom_cont(σ,ℝ) = ℝ·id`), `dual_beta_real` (`= 0`).

## LeanCheck/ChainComp7.lean, ChainArtinSchreier.lean, ChainFieldUniversal.lean, ChainPW1.lean ... ChainPW8.lean
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 377 declarations). Everything in this repository is now unconditional.

**Uniqueness of completions (literal `Comp ≅`)** -- ChainComp7

| Lean | Statement |
|---|---|
| `completion_unique` | two dense uniform embeddings of a uniform abelian group into complete Hausdorff uniform abelian groups are related by a uniformly bicontinuous isomorphism compatible with the embeddings (extension along dense uniform embeddings) |
| `completion_iso_completion` | taking one target to be Mathlib's `UniformSpace.Completion`: `Completion α ≃+ X` |
| `RT η`, `RT.sigma_group/beta_group/tau_group/theta_group` | `ℝ` with a group topology `η`, as a uniform group (right uniformity) |
| `completion_literal_sigma/_beta/_tau/_thetaS` | **`Completion (RT η) ≃+ X` literally**, for `η = σ_{f,S}`, `β_{f,S}`, `τ_{f,S}`, `θ_S` and `X = ℝ×K_S`, `K_ℝ×K_S`, `ℝ×ℝ^B`, `K_S`, uniformly bicontinuous and extending the embeddings |

**Artin–Schreier for subfields of `ℝ`** -- ChainArtinSchreier, ChainFieldUniversal (Corollary `field-universal`)

| Lean | Statement |
|---|---|
| `no_prime_index_odd` | no field `M` with `[ℂ:M] = p` odd prime and `ζ_p ∈ M` (Mathlib's Kummer theory: `ℂ = M(α)`, `α^p ∈ M`; then `X^{p²} - a` is irreducible over `M`, giving an element of degree `p² > p`) |
| `no_prime_index_two` | same for `p = 2` when `i ∈ M` (direct computation with the minimal polynomial of a fourth root) |
| `finrank_eq_one_of_I_mem` | a field `K` with `[ℂ:K] < ∞` and `i ∈ K` has `K = ℂ` (descent through the fixed field of a subgroup of order `p` of the Galois group, after adjoining `ζ_p`) |
| `finite_index_subfield_real` | an intermediate field `F ⊆ ℝ` with `[ℝ:F] < ∞` is `ℝ` |
| `field_cover_iff`, `field_universal` | **Cor field-universal**: a universal separating sequence exists for an intermediate field `F` iff `F = ℝ` (iff `[ℝ:F] < ∞`) |

**F2 (Peter–Weyl) proved** -- ChainPW1 ... ChainPW8

| Lean | Statement |
|---|---|
| `PW.Tk`, `PW.Tk_compact` | integral operators on `L²(Haar)` with continuous kernel (defined through `x ↦ ⟪ι conj k(x,·), h⟫`, so no Fubini / product measurability, hence no second countability) are bounded and compact (rank-one tensors, Stone–Weierstrass, closedness of compact operators) |
| `PW.exists_common_eigenvector` | a commuting family of operators on a finite-dimensional complex space has a common eigenvector |
| `PW.tr`, `PW.Tconv_comm` | translations on `L²`, linear isometries; convolution operators commute with them |
| `PW.Dop_ne_zero`, `PW.Bop_*` | `D = (tr x₀ - 1) T_f ≠ 0` when `f(x₀) ≠ f(0)`; `B = D†D` is compact self-adjoint and commutes with translations |
| `PW.exists_char_ne` | **continuous characters separate the points of a compact Hausdorff abelian group** (spectral theorem for compact self-adjoint operators from Mathlib) |
| `exists_circ_char`, `finite_chars_in_nhds` | circle-valued form; every neighbourhood of `0` contains a finite intersection of character balls |
| `completion_compactSpace` | the completion of a totally bounded uniform abelian group is compact |
| `generatedFact` | **(F2)**: every Hausdorff precompact group topology `τ` on `ℝ` equals `θ(dual τ)` |
| `precompactDuality`, `classification_unc`, `classificationEquiv_unc`, `thetaQ_minimal_unc`, `classification_TVG_unc` | the theorems that assumed `PrecompactDuality` / `GeneratedFact`, now unconditional |

Remaining paper-only: Glicksberg / Mackey-group literature results, the open mixed-prime problem (outside the scope of verification).

## LeanCheck/ChainBaire.lean  -- the rational quotient and the Baire obstruction (TVGQ-v7 Lemma `quotient-v4`, Theorem `nonbaire-v4`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 391 declarations).

Setting: `η` a Hausdorff locally quasi-convex group topology on `ℝ` whose full character group is exactly `H_{f,ℚ}` (`η ∈ Lcls (Hq f)`;
no rational scalar continuity is assumed), `f u = 1`.  `RT W.t` is `ℝ` with the topology `η = W.t` (wrapper `TopW` avoids local-instance capture);
`QuotQ W f` is `ℚ ≅ ℝ/N` with the quotient (coinduced) topology `λ_η` of `fQ = f`.

| Lean | Statement |
|---|---|
| `ker_closed` | `N = ker f = ⋂_q ker(p∘qf)` is closed |
| `fQ_continuous`, `fQ_surjective`, `fQ_isOpenMap`, `fQ_openQuotient` | `f : (ℝ,η) → (ℚ,λ_η)` is an open continuous surjection (preimage of the image is `⋃_{n∈N}(V+n)`) |
| `QuotQ_isTopologicalAddGroup`, `QuotQ_t2` | `λ_η` is a Hausdorff group topology (product of open quotient maps; `N` closed) |
| `QuotQ_dual` | the full character group of `(ℚ,λ_η)` is exactly `Γ = {q ↦ p(rq) : r ∈ ℚ}` (pull back to `p(cx + r f(x))`, `c N ⊆ ℤ`, `N` divisible and nonzero ⇒ `c = 0`) |
| `QuotQ_not_discrete` | `λ_η` is not discrete (the irrational character `q ↦ p(√2 q)` would be continuous) |
| `quotient_lemma` | **Lemma `quotient-v4`**, all assertions together (local quasi-convexity of the quotient is, as in the paper, not asserted) |
| `not_baire` | **Thm `nonbaire-v4`**: every `η ∈ ℒ(H_{f,ℚ})` is non-Baire (the sets `{x : f x ≠ q}`, `q ∈ ℚ`, are countably many dense open sets with empty intersection; an isolated point of `λ_η` would make the group discrete) |
| `not_baire_Ccls`, `not_locallyCompact`, `not_completelyMetrizable` | in particular every compatible TVGQ topology is non-Baire, not locally compact, and not completely metrizable |

## LeanCheck/ChainNecessaryMackey.lean  -- a necessary Mackey topology on the rational quotient (TVGQ-v7 Theorem `necessary-rational-v4`)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 398 declarations).

`Gam` = `Γ = {q ↦ p(rq)}` as a set of characters of `ℚ`; `Lcls Gam` / `Ccls Gam = 𝒟_Γ` as in ChainSaturation (Mathlib's `≤` is the reverse of the paper's inclusion, so "greatest" = `ν ≤ δ` for all `δ`).

| Lean | Statement |
|---|---|
| `Gam_ratInv` | `Γ` is rationally invariant |
| `lamTop`, `lamTop_dual` | the quotient topology `λ_μ` on `ℚ` (coinduced along `f`) has full dual `Γ` (from `QuotQ_dual`) |
| `Tq_mem_Ccls` | `S_f(δ) ∈ 𝒞^ℚ_{f,ℚ}` for every `δ ∈ 𝒟_Γ` (group, Hausdorff, lqc, dual `H_{f,ℚ}`, rational dilations) |
| `lam_le` | if `μ` is greatest in `𝒞^ℚ_{f,ℚ}`, then every compatible `δ` satisfies `δ ⊆ δ^[ℚ] ⊆ λ_μ` (saturation + transfer + universal property of the quotient topology) |
| `necessary_mackey_rational` | **Thm `necessary-rational-v4`**: if `𝒞^ℚ_{f,ℚ}` has a greatest member `μ`, then `(ℚ,Γ)` has a greatest compatible Hausdorff locally quasi-convex group topology `ν = λ_qc` (the join of all such topologies coarser than `λ_μ`; nonempty family, squeezed between `λ_μ` and a compatible topology so its dual is `Γ`), and `ν` is also the greatest member of `𝒟_Γ` (via `mackey_equivalence`) |
| `no_mackey_rational` | the necessary condition fails: `(ℚ,Γ)` has no Mackey topology in the lqc class (two lifted chain topologies with incompatible join) |
| `no_greatest_via_quotient` | hence `𝒞^ℚ_{f,ℚ}` has no greatest member -- a second proof of the conclusion of `no_greatest_compatible_Q`, through the rational quotient |

Note: `λ_μ` itself need not be locally quasi-convex (the paper does not assert it); that is why `λ_qc` is introduced.


## Second round (files ChainX1-X4, ChainT1-T5, ChainY1-Y7, ChainZ1-Z5, ChainW1-W2, ChainV1-V4, ChainU1-U3, ChainD1-D7, ChainE1-E7)
## compiles, no `sorry`, axioms: standard only (Axioms.lean now checks 603 declarations; `lake build LeanCheck` succeeds).

Conventions: Mathlib's `≤` on topologies is "finer than", so the paper's join `∨` is `⊓`/`⨅` and "greatest member" means `μ ≤ τ` for all members `τ`.
`Kcls H S` (ChainD1) is the generic class "Hausdorff locally quasi-convex group topologies with character group exactly `H` in which every map in `S` is
continuous"; `ℒ_f = Kcls H_f ∅`, `𝒞_f = Kcls H_f realDil`. `Cp p = {p^(n²)}`, `xi C` is `ξ_C` on `ℚ`, `Gam` is `Γ`.

| Paper statement | Lean file : theorem(s) |
|---|---|
| HamelCharactersTVG 6.1, 6.2, 6.3, 10.4 | ChainT1 : `tvg_totally_disconnected`, `lift_unique`, `lift_pf`, `lift_chi` |
| 11.1, 11.2, 13.1, 13.2, 13.3 | ChainT2 : `modular_comparison`, `modular_count`, `tvg_rigidity`, `tvg_isomorphism_classification`, `tvg_maps_between_families` |
| 5.1, 5.3, 8.1, 4.2 | ChainT3/T4 : `vanishing_family`, `representation_failure`, `family_properties`, `family_joins`, `bohr_lt_beta` |
| 7.1 | ChainT5 : `tvg_coarser_iff`, `tvg_finer_iff`, `tvg_weaker_consequences` |
| TVGQ 2.2, 2.4, 7.1 (homeomorphism sentence), 7.3 | ChainX1 : `tvgq_division_equiv`, `scalarCont_subring`, `homeo_iff_scalar_*`, `transcendental_example` |
| TVGQ 11.1, 12.1, 12.2 | ChainX2 : `directed_join_Lcls/Ccls`, `compatible_scalars`, `greatest_criterion` |
| TVGQ 13.2, 13.6 | ChainX3 : `strict_compatible_refinement`, `greatest_restrictions`, `greatest_rational_restrictions` |
| TVGQ 14.1, 14.2 | ChainX4 : `scalarCont_subfield`, `joint_continuity_of_orbit` |
| TVGQ 17.3 / TVG D.3 (Theorem F) | ChainY1-Y7 : `xi_dual_seq`, `chains_F` |
| TVGQ 17.6 / TVG D.6 (Theorem G) | ChainZ1-Z5 : `tors_neg`, `tors_pos`, `chains_G_seq` (iff `H(M)`), `tors_dual_finite` |
| TVGQ 17.2, 17.4, 17.7 / TVG D.2, D.4, D.7 | ChainW1-W2 : `HSet_union`, `chains_F_set`, `Fjoin`, `compat_iff_HSet`, `Gjoin` |
| TVGQ 17.5, 17.8, 17.9, 13.7 / TVG D.5, D.8, D.9, C.1 | ChainV1-V3 : `irrational_probe_sequences`, `irrational_join_test`, `qfac_null`, `fac_fac_not_null`, `dyadic_partition` |
| TVG A.1, B.3 | ChainV4 : `alternating_blocks`, `odd_segments_not_T2`, `odd_segments_character_discontinuous` |
| TVG 14.1 (sequence part), 14.2, 14.3 (not the Bohr converse), 14.5, 14.6, 14.7 | ChainU1-U3 : `bohr_to_usual`, `conv_*_iff`, `pell_unscaled_top`, `finite_span_*`, `one_dim_no_separation`, `two_dim_separation`, `compact_sigma_iff`, `compact_tau_iff`, `compact_beta_of` |
| 18.1, 24.1 | ChainD1 : `directed_join_mem`, `exists_minimal_ext`, `greatest_iff_binary`, `binary_join_mem_iff` |
| 26.1, 26.2, 26.3, 26.4, 26.6 (first implication) | ChainD2-D3 : `Hf_dilInv`, `aut_converse`, `automatic_tvg`, `rho_le_iff`, `rho_directed_iff`, `real_saturation`, `mackey_implies_conjecture` |
| 19.1, 19.4, 26.6 | ChainD4, ChainE7 : `quotient_lemma_F`, `lamTop_rational_scalar`, `necessary_mackey_F`, `sandwich` |
| 22.1 (membership of `γ_p` in `𝒬_Γ`; not metrizability / precompactness), 22.2 | ChainD5-D6 : `gamma_p_dual`, `gamma_p_mem`, `prime_not_finer`, `gamma2_gamma3_incomparable` |
| 20.1, 20.2, 23.1 | ChainD7 : `ultralimit_test`, `ultralimit_incompatible`, `ulimChar_of_tendsto`, `ultrafilter_criterion`, `conditional_witness` |
| 17.1, 17.2, 17.3 (Zorn part, finer than usual and Bohr), 21.3 | ChainE1 : `discrete_of_countable_nhd`, `join_usual_nondiscrete`, `join_precompact_nondiscrete`, `exists_maximal_nondiscrete`, `torsionfree_Q`, `torsionfree_Hf` |
| 16.1, 26.5 (without the nuclear remark) | ChainE2 : `beta_least`, `sigma_least`, `additive_dual`, `sigma_mem_Kcls`, `necessary_condition` |
| 16.2, 16.4 (explicit factorial-chain topology) | ChainE3 : `rational_target_lemma`, `strictly_finer_compatible` |
| 15.2 | ChainE4 : `minimal_iff_line`, `no_least_TVG` |
| 12.1 (all but connectedness of the completions) | ChainE5 : `sigma_not_firstCountable`, `sigma_not_complete`, `beta_not_complete`, `sigma_not_locallyCompact`, `beta_not_locallyCompact`, `sigma_completion_not_firstCountable`, `beta_completion_not_firstCountable` |
| 22.4 | ChainE6 : `integer_polar_reduction` (`γ_2 ∨ γ_3` is compatible with `Γ` iff every `α` with `k ↦ p(αk)` continuous for the integer metric `P` is rational) |
| 15.3 (counting precompact and minimal topologies) | ChainF1 : `card_Chars`, `card_chooseBasisIndex`, `card_precompact_TVG`, `card_minimal_TVG`, `precompact_count` (the character group is a real vector space of dimension `2^𝔠`) |
| 22.3 (join of the prime-square topologies is weaker than usual) | ChainF2 : `dirichlet_multi`, `exists_large_in_joint`, `join_contains_large_integers`, `join_weaker_than_usual` |
| E.1 / TVGQ 18.1 complete (incl. profinite compactness), E.2 / 18.2 | ChainF3 : `tendsto_profT_zero`, `isCompact_of_null`, `twochains_complete`, `twochains_compact_union` |
| TVGadd-v2 6.2 (sequences converging for every functional) | ChainG1 : `seq_universal_tau`, `seq_universal_sigma`, `seq_universal_beta` |
| TVGadd-v2 6.3 (dependence on the functional) | ChainG2 : `exists_decay_functional`, `seq_dependence` |
| TVGadd-v2 5.2, explicit part | ChainG3 : `aSeq_weak_null`, `aSeq_not_gamma` |

| 16.3 (finite coefficient quotients) | ChainH1 : `HM_surj`, `HM_ker_dense`, `HM_openSurj`, `HM_openSurj_gamma0`, `nu_dual_mp` |
| 17.4 (disjoint subspaces with all finite scalar patterns) | ChainK1 : `exists_patterns` (transfinite recursion along the initial ordinal of the continuum) |
| 17.5, 17.6 (no greatest nondiscrete TVG; nonunique maximal extensions) | ChainK2 : `no_greatest_nondiscrete`, `nonunique_maximal` |
| 21.1 (reduction to metrizable topologies) | ChainM1 : `exists_metrizable_between`, `reduction_to_metrizable` |
| 22.1 (metrizable, not precompact) | ChainL1 : `metrizable_rat`, `gamma_p_metrizable`, `gamma_p_not_precompact` |
| TVGadd-v4 8.1 = TVGadd-v6 7.1 (dimension zero of the mixed-prime dual) | ChainN1-N2 : `sum_cos_grid`, `sum_Qf_grid`, `exists_large_Pl_set`, `cover_Kset`, `covering_exp_bound`, `Kset_dimH`, `mixed_dual_dimH_zero`, `Hint_Z16`, `mixed_dual_null` (grid orthogonality replaces the integral Parseval step; `Hint` is the set of continuous-character parameters, as in 22.4) |

TVGadd numbering follows its sections: 2.1-2.9 = TVG D.1-D.9, 3.1-3.3 = E.1-E.3, 4.1-4.5 = F.1-F.5, 6.1 = TVG 14.6.
`AdditionalResults.lean` is a separate file that is NOT imported by `LeanCheck.lean`; it is not covered by the build or the axiom audit.
The axiom audit (`Axioms.lean`) covers 603 selected declarations (statements and key lemmas), not every helper lemma.

## Not formalized (and why)
* Glicksberg's theorem (compact sets of a locally compact abelian group and of its Bohr topology coincide): the compact-set half of 14.1 and 14.3 for `β_f`,
  and "compact subsets of a maximal member are finite / convergent sequences eventually constant / not first countable" in 17.3.
* Pontryagin duality or the theory of nuclear groups, quoted from the literature: connectedness of the completions in 12.1, 21.2, 25.2, 25.3,
  the last sentence of 26.5, and TVGadd-v2 5.1, 5.3 and the "not nuclear" conclusion of 5.2 (Mathlib has no notion of nuclear group).
* Not attempted: nothing further is planned; every remaining item above needs one of the three quoted theories.
* Local precompactness in 22.1 and Proposition 21.2 use Pontryagin duality (see above).

## LeanCheck/MixedPrime*.lean  (paper: TVGaddmore_v17)  -- compile, no `sorry`,
## axioms: propext, Classical.choice, Quot.sound only (checked by `LeanCheck/MixedPrimeAxioms.lean`).

Model. `nrm x = ‖(x : ℝ/ℤ)‖` (distance to the nearest integer, via `AddCircle (1:ℝ)`); for a set `S : Set ℕ` of positive scales
`Pn S k = ⨆ q ∈ S, nrm (k / q)`. The paper's `P_S` is `Pn` of `{ℓ^(n^2) | ℓ ∈ S, n ≥ 1}` (`Sc L` in `MixedPrimeProfile`,
`S23 = sqScales 2 ∪ sqScales 3` in `MixedPrimeRadii`). Statements hold for arbitrary scale sets unless noted.
"Continuity" is the ε-δ condition at 0 (`P`-open = contains a ball).

| Paper (v17) | Lean | Notes |
|---|---|---|
| Prop. 2.5 (necessity), quarter-arc ⇒ Lipschitz | `lipschitz_of_quarter` | `‖kx‖ ≤ P(k)/(2δ)` from quarter-arc continuity; uses `near_of_all_multiples` |
| Theorem "flatness" (both directions) | `flatness_necessity`, `continuity_iff_flat` | block construction, any infinite scale set; first-crossing at `1/8`, `3/16 < 1/2` |
| Prop. "divisibility-radii", valuation lemma | `valuation_bound` | `ℓ^a ∤ k ⇒ P_ℓ(k) ≥ ℓ^(-(2⌊√(a-1)⌋+1))`, `ℓ` prime |
| exact radii `μ(9)=μ(18)=μ(27)=μ(81)=1/27`, `μ(2^a)=1/32` (`5≤a≤9`) | `mu_three_family`, `mu_two_power`, `P_393744_le/ge`, `P_603519984_le/ge` | `IsLeast` statements; witnesses `393744`, `603519984` by exact finite certificate (`Pn_S23_le`) |
| Prop. "coloured" | `B_subset_D`, `D_subset_B2`, `D_subset_iff_disjoint`, `open_iff_disjoint` | `B_ε ⊆ D_ε ⊆ B_{2ε}`; `D_ε ⊆ pℤ ⇔` coloured sets pairwise disjoint; `pℤ` open `⇔ ∃ε` disjoint |
| Lemma 7.11 (profile summation) | `geomZ_le`, `profile_sum` | `(1+r)/(1-r)` constant, distinct centres per base |
| Theorem 7.17 (uniform bound, summability), finite form | `profile_summability` | `∑ ‖h_i x‖/ε_i ≤ 2 C A_r` for `ε_i ≤ 1/(16 C A_r)` |
| Corollary 7.18 (tests 1 and 2) | `not_lipschitz_of_divergent`, `not_lipschitz_of_fixed_scale` | conclusion: no Lipschitz constant exists |
| Lemma "sparse-tail" | `Tl_bounds`, `sparse_decomp`, `sparse_tail`, `sqrt_log_lower`, `sparse_relative` | `1/Q ≤ T_J ≤ 2/Q`; `P(k) ≥ 2^{-(2√log₂(2|k|)+2)}`; relative tail bound; `x = ∑ 1/q_s` with `q_s = 2^(n_s^2)` (0-indexed) |
| Prop. "sparse-tests", part (b) | `sparse_exclusion_b` | one-sided saturation witnesses exclude a Lipschitz bound |
| Theorem "density", upper bound | `lift_card`, `Afin_succ`, `density_upper`, `density_ball` | `#{k<K : ‖k/ℓ^(n²)‖<δ, n≤N} ≤ 2 K e^{1/δ} (2δ)^N` for `K ≥ ℓ^(N²)` (the "≤ 2δa+2 lifts" step is `lift_card`) |

NOT formalized (v17): the density lower bound / the specialisation `N = ⌊√log_ℓ K⌋` giving `exp(-c√ln K)`; Theorem "stationary"
(square residues modulo `L`, Chinese remainder, digit-vanishing); Proposition "thickness" (Newhouse thickness) and the cited theorems
of Glasscock–Moreira–Richter and Yavicoli–Yu (external, not assumed as axioms); part (a) of "sparse-tests" beyond the relative tail
lemma (the limit statement "tends to zero for K ≤ Q^θ" is calculus, not formalized); Remark "near-resonances".
Earlier v10-v16 items (Prop. 7.8 lacunary computation, Prop. 7.12 pigeonhole existence, Prop. 4.3) are not covered here.

### Joint approximation implies splitting (new, after v17)  `LeanCheck/MixedPrimeSplit.lean`
`split_of_joint`: if `x` has the Lipschitz bound `nrm (k x) ≤ C · Pn (S2 ∪ S3) k`, and there are integers `k_j` with
`Pn S3 (k_j) → 0` and `Pn S2 (k_j - 1) → 0`, then there is `y` (a cluster point of `k_j x` on the circle) with
`nrm (m y) ≤ C · Pn S2 m` and `nrm (m (x - y)) ≤ C · Pn S3 m` for all `m`. Axioms: propext, Classical.choice, Quot.sound.
Consequence on paper: under this joint-approximation hypothesis `H_{S2 ∪ S3} = H_{S2} + H_{S3}`; for `S2={2}`, `S3={3}` this is
`ℤ[1/6]/ℤ`. The existence of such a sequence `k_j` is NOT proved (numerical evidence: `experiments/Exp17.java`, `Exp18.java`).
