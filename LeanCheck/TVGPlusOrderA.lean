import LeanCheck.TVGPlusCount

/-!
# TVGplus: pigeonhole for multiples of the universal divisor

`pigeonhole_mult`: among the multiples `D x`, `0 ≤ x ≤ M`, with `m^|C| ≤ M`, two have all the fractional parts `D x / q_c`
(for the retained coordinates `c ∈ C`, `q_c = c.1 ^ (c.2 ^ 2)`) in the same one of `m` boxes; their difference `D j` with
`1 ≤ j ≤ M` is within `1/m` of an integer at every retained coordinate.  (For `D = 1` this is `pigeonhole_box`.)
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

lemma pigeonhole_mult (C : Finset (ℕ × ℕ)) (hq : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2)) (D m M : ℕ)
    (hm : 1 ≤ m) (hM : m ^ C.card ≤ M) :
    ∃ j : ℤ, 1 ≤ j ∧ j ≤ M ∧
      ∀ c ∈ C, nrm (((D : ℝ) * (j : ℝ)) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set q : ℕ × ℕ → ℝ := fun c => ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) with hqdef
  have hqpos : ∀ c ∈ C, 0 < q c := fun c hc => by
    simp only [hqdef]; exact_mod_cast hq c hc
  have hlt : ∀ (c : ℕ × ℕ) (x : ℕ), c ∈ C →
      ⌊(m : ℝ) * Int.fract (((D : ℝ) * (x : ℝ)) / q c)⌋₊ < m := by
    intro c x hc
    rw [Nat.floor_lt (by have := Int.fract_nonneg (((D : ℝ) * (x : ℝ)) / q c); positivity)]
    have := Int.fract_lt_one (((D : ℝ) * (x : ℝ)) / q c)
    nlinarith
  let F : Fin (M + 1) → (C → Fin m) := fun x c =>
    ⟨⌊(m : ℝ) * Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c.1)⌋₊, hlt c.1 x c.2⟩
  have hcard : Fintype.card (C → Fin m) < Fintype.card (Fin (M + 1)) := by
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
    omega
  obtain ⟨x, y, hxy, hF⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  have core : ∀ x y : Fin (M + 1), x < y → F x = F y →
      ∃ j : ℤ, 1 ≤ j ∧ j ≤ M ∧
        ∀ c ∈ C, nrm (((D : ℝ) * (j : ℝ)) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
    intro x y hlt' hFxy
    refine ⟨((y : ℕ) : ℤ) - ((x : ℕ) : ℤ), ?_, ?_, ?_⟩
    · have : (x : ℕ) < (y : ℕ) := hlt'
      omega
    · have := y.2
      have : ((y : ℕ) : ℤ) ≤ M := by omega
      omega
    · intro c hc
      have hfl : ⌊(m : ℝ) * Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c)⌋₊
          = ⌊(m : ℝ) * Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c)⌋₊ := by
        have := congrFun hFxy ⟨c, hc⟩
        exact congrArg Fin.val this
      set a := (m : ℝ) * Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c) with ha
      set b := (m : ℝ) * Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c) with hb
      have ha0 : 0 ≤ a := by
        have := Int.fract_nonneg (((D : ℝ) * ((x : ℕ) : ℝ)) / q c); positivity
      have hb0 : 0 ≤ b := by
        have := Int.fract_nonneg (((D : ℝ) * ((y : ℕ) : ℝ)) / q c); positivity
      have h1 := Nat.floor_le ha0
      have h2 := Nat.lt_floor_add_one a
      have h3 := Nat.floor_le hb0
      have h4 := Nat.lt_floor_add_one b
      rw [hfl] at h1 h2
      have hab : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
      have hfr : |Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c)
          - Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c)| < 1 / m := by
        have e : Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c)
            - Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c) = (b - a) / m := by
          rw [ha, hb]; field_simp
        rw [e, abs_div, abs_of_pos hm0, abs_sub_comm]
        exact div_lt_div_of_pos_right hab hm0
      have e2 : ((D : ℝ) * ((((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) : ℤ) : ℝ)) / q c
          = (Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c)
              - Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c))
            + ((⌊((D : ℝ) * ((y : ℕ) : ℝ)) / q c⌋ - ⌊((D : ℝ) * ((x : ℕ) : ℝ)) / q c⌋ : ℤ) : ℝ) := by
        push_cast
        rw [Int.fract, Int.fract]
        ring
      have e3 : nrm (((D : ℝ) * ((((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) : ℤ) : ℝ)) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ))
          = nrm (Int.fract (((D : ℝ) * ((y : ℕ) : ℝ)) / q c)
              - Int.fract (((D : ℝ) * ((x : ℕ) : ℝ)) / q c)) := by
        have : ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) = q c := rfl
        rw [this, e2, nrm_add_int]
      rw [e3]
      exact lt_of_le_of_lt (nrm_le_abs _) hfr
  rcases lt_or_gt_of_ne hxy with h | h
  · exact core x y h hF
  · exact core y x h hF.symm

/-- **The refined pigeonhole witness** (combinatorial core of the logarithmic order).  Let `D = D_S(δ)`, `M ≥ 1`, `N = D M`,
`m > 1/δ`, and let `r p` (`p ∈ S`) be cut-offs with `N / δ < p^((r p + 1)^2)`.  If `m ^ (∑ (r p - a_p)) ≤ M`, there is a
positive `k ≤ N` in the ball `B^S_δ` (indeed a multiple of `D`). -/
theorem upper_mult {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ) (M m : ℕ) (hM : 1 ≤ M)
    (hm : 1 / δ < m) (r : ℕ → ℕ)
    (hr : ∀ p ∈ S, ((Dvis S δ * M : ℕ) : ℝ) / δ < ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ))
    (hcount : m ^ (∑ p ∈ S, (r p - aThr p δ)) ≤ M) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ ((Dvis S δ * M : ℕ) : ℤ) ∧ InBall S δ k := by
  classical
  set D : ℕ := Dvis S δ with hD
  have hDpos : 0 < D := by
    rw [hD]; unfold Dvis
    exact Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < 1 / δ := by positivity
    have h2 : (0 : ℝ) < m := lt_trans this hm
    exact_mod_cast h2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set C : Finset (ℕ × ℕ) :=
    S.biUnion (fun p => (Finset.Ioc (aThr p δ) (r p)).image (fun n => (p, n))) with hC
  have hCcard : C.card ≤ ∑ p ∈ S, (r p - aThr p δ) := by
    refine (Finset.card_biUnion_le).trans ?_
    apply Finset.sum_le_sum
    intro p hp
    refine (Finset.card_image_le).trans ?_
    simp
  have hCmem : ∀ p n, p ∈ S → aThr p δ < n → n ≤ r p → (p, n) ∈ C := by
    intro p n hp h1 h2
    rw [hC, Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Ioc.mpr ⟨h1, h2⟩, rfl⟩⟩
  have hCpos : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2) := by
    intro c hc
    rw [hC, Finset.mem_biUnion] at hc
    obtain ⟨p, hp, hc'⟩ := hc
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hc'
    exact pow_pos (hS p hp).pos _
  have hcnt : m ^ C.card ≤ M := (Nat.pow_le_pow_right hm1 hCcard).trans hcount
  obtain ⟨j, hj1, hjM, hj⟩ := pigeonhole_mult C hCpos D m M hm1 hcnt
  refine ⟨(D : ℤ) * j, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ D := by exact_mod_cast hDpos
    nlinarith
  · push_cast
    have : (0 : ℤ) ≤ D := by exact_mod_cast hDpos.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjM) this
  · intro p hp
    have hp' := hS p hp
    set N : ℕ := D * M with hN
    have hmδ : 1 / (m : ℝ) < δ := by
      rw [div_lt_iff₀ hm0]
      rw [div_lt_iff₀ hδ] at hm
      linarith
    have hqr : (N : ℝ) / ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ) < δ := by
      have := hr p hp
      have hqp : (0 : ℝ) < ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos hp'.pos _
      rw [div_lt_iff₀ hδ] at this
      rw [div_lt_iff₀ hqp]
      linarith
    refine lt_of_le_of_lt (Pn_le (sq_nonempty p) (c := max (1 / (m : ℝ)) ((N : ℝ) / ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ)))
      ?_) (max_lt hmδ hqr)
    rintro q ⟨n, hn, rfl⟩
    have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp'.pos _
    by_cases h1 : n ≤ aThr p δ
    · -- `p ^ (n^2)` divides `D`
      have hdv : (p ^ (n ^ 2) : ℕ) ∣ D := by
        have h2 : p ^ (n ^ 2) ∣ p ^ (aThr p δ ^ 2) :=
          pow_dvd_pow p (by nlinarith)
        exact h2.trans (by rw [hD]; unfold Dvis; exact Finset.dvd_prod_of_mem (fun p => p ^ (aThr p δ ^ 2)) hp)
      obtain ⟨e, he⟩ := hdv
      have : (((D : ℤ) * j : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) = ((e * j : ℤ) : ℝ) := by
        have hq' : (p : ℝ) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp'.ne_zero)
        have heR : (D : ℝ) = (p : ℝ) ^ (n ^ 2) * e := by exact_mod_cast he
        push_cast
        rw [heR]
        field_simp
      rw [this, nrm_int]
      exact le_max_of_le_left (by positivity)
    · push Not at h1
      by_cases h2 : n ≤ r p
      · have hmem := hCmem p n hp h1 h2
        have h3 := hj (p, n) hmem
        have e : (((D : ℤ) * j : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) =
            ((D : ℝ) * (j : ℝ)) / (((p, n).1 ^ ((p, n).2 ^ 2) : ℕ) : ℝ) := by simp
        rw [e]
        exact h3.le.trans (le_max_left _ _)
      · push Not at h2
        refine (nrm_le_abs _).trans ?_
        rw [abs_div, abs_of_pos hqpos]
        have hk0 : (0 : ℝ) ≤ ((D : ℤ) * j : ℤ) := by
          have : (0 : ℤ) ≤ (D : ℤ) * j := by
            have : (0 : ℤ) ≤ D := by exact_mod_cast hDpos.le
            nlinarith
          exact_mod_cast this
        rw [abs_of_nonneg hk0]
        have hkN : (((D : ℤ) * j : ℤ) : ℝ) ≤ N := by
          have : (D : ℤ) * j ≤ (N : ℤ) := by
            rw [hN]; push_cast
            have : (0 : ℤ) ≤ D := by exact_mod_cast hDpos.le
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjM) this
          exact_mod_cast this
        have hq2 : ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          have : p ^ ((r p + 1) ^ 2) ≤ p ^ (n ^ 2) :=
            Nat.pow_le_pow_right hp'.pos (by nlinarith)
          exact_mod_cast this
        have hqp : (0 : ℝ) < ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ) := by
          exact_mod_cast pow_pos hp'.pos _
        refine le_max_of_le_right ?_
        calc (((D : ℤ) * j : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hkN hqpos.le
          _ ≤ (N : ℝ) / ((p ^ ((r p + 1) ^ 2) : ℕ) : ℝ) :=
              div_le_div_of_nonneg_left (by positivity) hqp hq2

#print axioms upper_mult

#print axioms pigeonhole_mult

end TVGPlus
end LeanCheck
