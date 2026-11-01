import LeanCheck.TVGPlusOrderB
import LeanCheck.JAOnePrime
import LeanCheck.MixedPrimeSplit

/-!
# TVGplus: the dual group under diagonal density (Lemma "The dual under density")

`ContAt S α` says that the character `k ↦ e(kα)` is continuous at `0` for the `P_S`-topology.

* `contAt_of_denominator`: if `M α ∈ ℤ` for some `M > 0` all of whose prime factors lie in `S`, then `ContAt S α`
  (this direction needs no density hypothesis: `M` divides `D_S(δ)` for small `δ`, and `D_S(δ)` divides every element of the ball).
* `dual_of_DD`: under `DD S`, every `α` with `ContAt S α` has `M α ∈ ℤ` for such an `M`; i.e. `H_S = ∑_{p∈S} H_p = ℤ[1/S]/ℤ`.
  The proof is elementary: with idempotent-like integers `k_p ≈ e_p` (from `DD S`), compactness of the circle gives limit parameters
  `α_p` with `α = ∑ α_p`, each `α_p` is `P_p`-continuous, and the one-prime theorem (`JAOnePrime.oneprime`) gives their denominators.

No external hypothesis other than `DD S`; no `sorry`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The character `k ↦ e(kα)` is continuous at `0` for the `P_S`-topology. -/
def ContAt (S : Finset ℕ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, InBall S δ k → nrm ((k : ℝ) * α) < ε

theorem contAt_of_denominator {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ r : ℕ, r.Prime → r ∣ M → r ∈ S) {α : ℝ} {z : ℤ} (h : (M : ℝ) * α = z) : ContAt S α := by
  classical
  intro ε hε
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = (2 * M + 1) * (∑ p ∈ S, Real.log p) + 1 := ⟨_, rfl⟩
  have hSum : 0 ≤ ∑ p ∈ S, Real.log p := Finset.sum_nonneg (fun p hp => (log_pos_of_prime (hS p hp)).le)
  have hL₀1 : 1 ≤ L₀ := by rw [hL₀]; have : (0 : ℝ) ≤ (2 * M + 1) * ∑ p ∈ S, Real.log p := by positivity
                           linarith
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  intro k hk
  have hδ0 : 0 < Real.exp (-L₀) := Real.exp_pos _
  have hLδ : Real.log (1 / Real.exp (-L₀)) = L₀ := by
    rw [one_div, Real.log_inv, Real.log_exp]; ring
  -- `M ∣ D_S(δ)`
  have hMD : M ∣ Dvis S (Real.exp (-L₀)) := by
    have hD0 : Dvis S (Real.exp (-L₀)) ≠ 0 := by
      unfold Dvis
      exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
    rw [← Nat.factorization_prime_le_iff_dvd hM0.ne' hD0]
    intro r hr
    by_cases hrS : r ∈ S
    · have hl := log_pos_of_prime hr
      have hga := aThr_ge hr hδ0
      rw [hLδ] at hga
      have hlr : Real.log r ≤ ∑ q ∈ S, Real.log q :=
        Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ))
          (fun q hq => (log_pos_of_prime (hS q hq)).le) hrS
      have hge : (M : ℝ) ≤ (aThr r (Real.exp (-L₀)) : ℝ) := by
        have h1 : (2 * (M : ℝ) + 1) * Real.log r ≤ L₀ := by
          rw [hL₀]
          have := mul_le_mul_of_nonneg_left hlr (by positivity : (0 : ℝ) ≤ 2 * M + 1)
          linarith
        have h2 : (2 * (M : ℝ) + 1) ≤ L₀ / Real.log r := by rw [le_div_iff₀ hl]; exact h1
        linarith
      have hMa : M ≤ aThr r (Real.exp (-L₀)) := by exact_mod_cast hge
      have hMa2 : M ≤ aThr r (Real.exp (-L₀)) ^ 2 := le_trans hMa (by nlinarith [Nat.zero_le (aThr r (Real.exp (-L₀)))])
      have hdv : r ^ (aThr r (Real.exp (-L₀)) ^ 2) ∣ Dvis S (Real.exp (-L₀)) := by
        unfold Dvis; exact Finset.dvd_prod_of_mem (fun p => p ^ (aThr p (Real.exp (-L₀)) ^ 2)) hrS
      have h3 : aThr r (Real.exp (-L₀)) ^ 2 ≤ (Dvis S (Real.exp (-L₀))).factorization r :=
        (hr.pow_dvd_iff_le_factorization hD0).mp hdv
      have h4 : M.factorization r < M := Nat.factorization_lt r hM0.ne'
      omega
    · have : M.factorization r = 0 := by
        by_contra hc
        exact hrS (hM r hr (Nat.dvd_of_factorization_pos hc))
      omega
  have hdk := forced hS hδ0 hk
  have hMk : (M : ℤ) ∣ k := (Int.natCast_dvd_natCast.mpr hMD).trans hdk
  obtain ⟨t, ht⟩ := hMk
  have : (k : ℝ) * α = (t * z : ℤ) := by
    rw [ht]; push_cast
    have e : (M : ℝ) * (t : ℝ) * α = (t : ℝ) * ((M : ℝ) * α) := by ring
    rw [e, h]
  rw [this, nrm_int]; exact hε

#print axioms contAt_of_denominator

private lemma coe_mul_int (k : ℤ) (b : ℝ) : (((k : ℝ) * b : ℝ) : Circ) = k • ((b : ℝ) : Circ) := by
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]

private lemma nrm_eq_norm_zsmul (k : ℤ) (b : ℝ) : nrm ((k : ℝ) * b) = ‖k • ((b : ℝ) : Circ)‖ := by
  unfold nrm; rw [coe_mul_int]

private lemma coe_sum_circ {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ)) : Circ) = ∑ i ∈ s, ((f i : ℝ) : Circ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddCircle.coe_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCircle.coe_add, ih]

private lemma coe_int_circ_zero (z : ℤ) : (((z : ℝ)) : Circ) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]; exact ⟨z, by simp⟩

/-- **The dual under density**: if `DD S` holds, every `P_S`-continuous parameter `α` satisfies `M α ∈ ℤ` for some `M > 0`
whose prime factors lie in `S`; that is `H_S = ∑_{p ∈ S} H_p = ℤ[1/S]/ℤ`. -/
theorem dual_of_DD {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {α : ℝ} (hα : ContAt S α) :
    ∃ M : ℕ, 0 < M ∧ (∀ r : ℕ, r.Prime → r ∣ M → r ∈ S) ∧ ∃ z : ℤ, (M : ℝ) * α = z := by
  classical
  have hk : ∀ (n p : ℕ), ∃ k : ℤ, p ∈ S → ∀ q ∈ S,
      Pn (sqScales q) (k - (if q = p then 1 else 0)) < 1 / ((n : ℝ) + 1) := by
    intro n p
    obtain ⟨k, hk⟩ := hDD (fun q => if q = p then 1 else 0) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨k, fun _ q hq => hk q hq⟩
  choose kk hkk using hk
  obtain ⟨xs, hxs⟩ : ∃ xs : ℕ → (S → Circ), xs = fun n p => ((((kk n p.1 : ℤ) : ℝ) * α : ℝ) : Circ) :=
    ⟨_, rfl⟩
  obtain ⟨x, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq xs
  have hlimp : ∀ p : S, Filter.Tendsto (fun n => xs (φ n) p) Filter.atTop (nhds (x p)) :=
    fun p => tendsto_pi_nhds.mp hlim p
  have hsurj : ∀ y : Circ, ∃ b : ℝ, (b : Circ) = y := fun y => QuotientAddGroup.mk_surjective y
  choose β hβ using fun p : S => hsurj (x p)
  obtain ⟨δ₀, hδ₀, hδ₀c⟩ := hα (1 / 8) (by norm_num)
  -- each limit parameter is `P_p`-continuous
  have hcont : ∀ p : S, ∀ k : ℤ, Pn (sqScales p.1) k < δ₀ → nrm ((k : ℝ) * β p) < 1 / 4 := by
    intro p k hk
    have hp := p.2
    obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = δ₀ - Pn (sqScales p.1) k := ⟨_, rfl⟩
    have hγ0 : 0 < γ := by rw [hγ]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (|(k : ℝ)| / γ)
    have hev : ∀ n ≥ N, nrm ((k : ℝ) * (((kk (φ n) p.1 : ℤ) : ℝ) * α)) < 1 / 8 := by
      intro n hn
      have hεn : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
        linarith
      have hkε : |(k : ℝ)| * (1 / ((φ n : ℝ) + 1)) < γ := by
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have h1 : |(k : ℝ)| * (1 / ((φ n : ℝ) + 1)) ≤ |(k : ℝ)| * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hεn (abs_nonneg _)
        have h2 : |(k : ℝ)| * (1 / ((n : ℝ) + 1)) < γ := by
          rw [mul_one_div, div_lt_iff₀ (by positivity)]
          have := (div_lt_iff₀ hγ0).mp hN
          nlinarith
        linarith
      have hball : InBall S δ₀ (k * kk (φ n) p.1) := by
        intro q hq
        have hk1 := hkk (φ n) p.1 hp q hq
        by_cases hqp : q = p.1
        · rw [hqp] at hk1 ⊢
          rw [if_pos rfl] at hk1
          have e : k * kk (φ n) p.1 = k + k * (kk (φ n) p.1 - 1) := by ring
          rw [e]
          have h1 := Pn_add_le (sq_nonempty p.1) k (k * (kk (φ n) p.1 - 1))
          have h2 := Pn_zsmul_le (sq_nonempty p.1) k (kk (φ n) p.1 - 1)
          have h3 : |(k : ℝ)| * Pn (sqScales p.1) (kk (φ n) p.1 - 1) ≤ |(k : ℝ)| * (1 / ((φ n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hk1.le (abs_nonneg _)
          linarith
        · simp only [hqp, if_false, sub_zero] at hk1
          have h2 := Pn_zsmul_le (sq_nonempty q) k (kk (φ n) p.1)
          have h3 : |(k : ℝ)| * Pn (sqScales q) (kk (φ n) p.1) ≤ |(k : ℝ)| * (1 / ((φ n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hk1.le (abs_nonneg _)
          have : 0 ≤ Pn (sqScales p.1) k := Pn_nonneg _ _
          linarith
      have := hδ₀c (k * kk (φ n) p.1) hball
      push_cast at this
      rwa [mul_assoc] at this
    have hnorm : ‖k • x p‖ ≤ 1 / 8 := by
      have ht : Filter.Tendsto (fun n => ‖k • xs (φ n) p‖) Filter.atTop (nhds ‖k • x p‖) :=
        (((continuous_const_smul k).tendsto (x p)).comp (hlimp p)).norm
      refine le_of_tendsto ht ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have e : ‖k • xs (φ n) p‖ = nrm ((k : ℝ) * (((kk (φ n) p.1 : ℤ) : ℝ) * α)) := by
        rw [nrm_eq_norm_zsmul, hxs]
      rw [e]; exact (hev n hn).le
    calc nrm ((k : ℝ) * β p) = ‖k • x p‖ := by rw [nrm_eq_norm_zsmul, hβ]
      _ ≤ 1 / 8 := hnorm
      _ < 1 / 4 := by norm_num
  -- the limit parameters add up to `α`
  have hsum_lim : Filter.Tendsto (fun n => ∑ p : S, xs (φ n) p) Filter.atTop (nhds (∑ p : S, x p)) :=
    tendsto_finsetSum _ (fun p _ => hlimp p)
  have hsum_alpha : Filter.Tendsto (fun n => ∑ p : S, xs n p) Filter.atTop (nhds ((α : ℝ) : Circ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := hα ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((S.card : ℝ) / δ)
    refine ⟨N, fun n hn => ?_⟩
    have hball : InBall S δ ((∑ p ∈ S, kk n p) - 1) := by
      intro q hq
      have hcc : Pn (sqScales q) ((∑ p ∈ S, kk n p) - 1) ≤ (S.card : ℝ) * (1 / ((n : ℝ) + 1)) := by
        apply Pn_le (sq_nonempty q)
        rintro s hs
        obtain ⟨m, hm, rfl⟩ := hs
        have hsum : (((∑ p ∈ S, kk n p) - 1 : ℤ) : ℝ) / ((q ^ (m ^ 2) : ℕ) : ℝ)
            = ∑ p ∈ S, ((((kk n p - (if q = p then 1 else 0) : ℤ)) : ℝ) / ((q ^ (m ^ 2) : ℕ) : ℝ)) := by
          rw [← Finset.sum_div]
          congr 1
          push_cast
          rw [Finset.sum_sub_distrib]
          have : ∑ p ∈ S, (if q = p then (1 : ℝ) else 0) = 1 := by
            rw [Finset.sum_ite_eq]; simp [hq]
          rw [this]
        rw [hsum]
        refine (nrm_sum_le _ _).trans ?_
        calc ∑ p ∈ S, nrm ((((kk n p - (if q = p then 1 else 0) : ℤ)) : ℝ) / ((q ^ (m ^ 2) : ℕ) : ℝ))
            ≤ ∑ p ∈ S, (1 / ((n : ℝ) + 1)) := by
              apply Finset.sum_le_sum
              intro p hp
              have h1 := le_Pn (S := sqScales q) (q := q ^ (m ^ 2)) (mem_sqScales (by omega))
                (kk n p - (if q = p then 1 else 0))
              have h2 := hkk n p hp q hq
              exact h1.trans h2.le
          _ = (S.card : ℝ) * (1 / ((n : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      refine lt_of_le_of_lt hcc ?_
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hδ).mp hN
      nlinarith
    have hnr := hδc _ hball
    have e1 : (∑ p : S, xs n p) = (((∑ p ∈ S, ((kk n p : ℤ) : ℝ)) * α : ℝ) : Circ) := by
      rw [hxs]
      simp only
      rw [Finset.sum_mul, coe_sum_circ]
      exact Finset.sum_coe_sort S (fun p => ((((kk n p : ℤ) : ℝ) * α : ℝ) : Circ))
    rw [dist_eq_norm, e1, ← AddCircle.coe_sub]
    have e2 : (∑ p ∈ S, ((kk n p : ℤ) : ℝ)) * α - α = ((((∑ p ∈ S, kk n p) - 1 : ℤ) : ℝ)) * α := by
      push_cast; ring
    rw [e2]
    exact hnr
  have hsum_eq : (∑ p : S, x p) = ((α : ℝ) : Circ) :=
    tendsto_nhds_unique hsum_lim (hsum_alpha.comp hφ.tendsto_atTop)
  -- denominators
  have hj : ∀ p : S, ∃ j : ℕ, ∃ z : ℤ, (p.1 : ℝ) ^ (j ^ 2) * β p = z := by
    intro p
    exact JAOnePrime.oneprime p.1 (hS p.1 p.2).two_le (β p) δ₀ hδ₀ (hcont p)
  choose j z hjz using hj
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ, e = fun p => if hp : p ∈ S then j ⟨p, hp⟩ ^ 2 else 0 := ⟨_, rfl⟩
  refine ⟨∏ p ∈ S, p ^ (e p), ?_, ?_, ?_⟩
  · exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
  · intro r hr hrd
    obtain ⟨p, hp, hrp⟩ := (hr.prime.dvd_finset_prod_iff _).mp hrd
    have h1 : r ∣ p := hr.prime.dvd_of_dvd_pow hrp
    have h2 : r = p := (Nat.prime_dvd_prime_iff_eq hr (hS p hp)).mp h1
    rw [h2]; exact hp
  · -- `M α ∈ ℤ`
    have hzero : ∀ p : S, (∏ q ∈ S, q ^ (e q)) • x p = 0 := by
      intro p
      have hdvd : p.1 ^ (j p ^ 2) ∣ ∏ q ∈ S, q ^ (e q) := by
        have := Finset.dvd_prod_of_mem (fun q => q ^ (e q)) p.2
        simpa [he, p.2] using this
      obtain ⟨c, hc⟩ := hdvd
      have hb : ((p.1 ^ (j p ^ 2) : ℕ) • ((β p : ℝ) : Circ)) = 0 := by
        rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
        push_cast
        rw [hjz p]; exact coe_int_circ_zero _
      rw [hc, mul_comm, mul_smul, ← hβ p, hb, smul_zero]
    have hM0 : ((∏ q ∈ S, q ^ (e q) : ℕ) • ((α : ℝ) : Circ)) = 0 := by
      rw [← hsum_eq, Finset.smul_sum]
      exact Finset.sum_eq_zero (fun p _ => hzero p)
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hM0
    obtain ⟨n, hn⟩ := hM0
    refine ⟨n, ?_⟩
    rw [nsmul_eq_mul] at hn
    simpa using hn.symm

#print axioms dual_of_DD

end TVGPlus
end LeanCheck
