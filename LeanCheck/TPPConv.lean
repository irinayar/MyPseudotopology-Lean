import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# ThreePrimePlus: the first-large-displacement bound of the normalized convolution (abstract form)

Abstract version of Lemma "Normalized convolution (b)" of ThreePrimePlus.  The functions
`h i : ℝ → ℝ` take values in `[0,1]`, satisfy the one-step inequality
`h i y ≤ Σ_{r ∈ S(i+1)} κ(i+1,r) h(i+1)(y + r/Q(i+1))`, and the last one vanishes when the
"norm" `N y` is at least `ε` (`N` is a seminorm-like function: subadditive and even).
If the displacements `r/Q` have norm at most `|r|/Q`, then a point at norm at least
`ε + Σ θ_m` has `h i y ≤ Σ_m β^m · (weight of the displacements |r| > θ_m Q)`.
-/

namespace TPP

open Finset

variable {I : ℕ} {Q : ℕ → ℝ} {κ : ℕ → ℤ → ℝ} {S : ℕ → Finset ℤ} {h : ℕ → ℝ → ℝ}
  {N : ℝ → ℝ} {β ε : ℝ}

/-- Weight of the displacements that are large at scale `θ`. -/
noncomputable def tail (Q : ℕ → ℝ) (κ : ℕ → ℤ → ℝ) (S : ℕ → Finset ℤ) (j : ℕ) (θ : ℝ) : ℝ :=
  ∑ r ∈ (S j).filter (fun r : ℤ => θ * Q j < |(r : ℝ)|), κ j r

theorem first_large
    (hQ : ∀ j, 0 < Q j) (hκ : ∀ j r, 0 ≤ κ j r) (hβ0 : 0 ≤ β)
    (hβ : ∀ j, ∑ r ∈ S j, κ j r ≤ β)
    (hh0 : ∀ i y, 0 ≤ h i y) (hh1 : ∀ i y, h i y ≤ 1)
    (hrec : ∀ i, i < I → ∀ y, h i y ≤ ∑ r ∈ S (i + 1), κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1)))
    (hterm : ∀ y, ε ≤ N y → h I y = 0)
    (hsub : ∀ x y, N (x + y) ≤ N x + N y) (hneg : ∀ x, N (-x) = N x)
    (hdisp : ∀ j, ∀ r ∈ S j, N ((r : ℝ) / Q j) ≤ |(r : ℝ)| / Q j) :
    ∀ k i, i + k = I → ∀ θ : ℕ → ℝ, (∀ m, 0 ≤ θ m) → ∀ y,
      ε + ∑ m ∈ range k, θ m ≤ N y →
      h i y ≤ ∑ m ∈ range k, β ^ m * tail Q κ S (i + m + 1) (θ m) := by
  intro k
  induction k with
  | zero =>
    intro i hi θ hθ y hy
    simp only [add_zero] at hi
    subst hi
    have : h i y = 0 := hterm y (by simpa using hy)
    simp [this]
  | succ k ih =>
    intro i hi θ hθ y hy
    have hlt : i < I := by omega
    have step := hrec i hlt y
    -- split the sum into large and small displacements
    set P : ℤ → Prop := fun r => θ 0 * Q (i + 1) < |(r : ℝ)| with hP
    have hsplit :
        ∑ r ∈ S (i + 1), κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1)) =
          ∑ r ∈ (S (i + 1)).filter P, κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1)) +
          ∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1)) :=
      (Finset.sum_filter_add_sum_filter_not (S (i + 1)) P _).symm
    -- large part
    have hlarge :
        ∑ r ∈ (S (i + 1)).filter P, κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1))
          ≤ tail Q κ S (i + 1) (θ 0) := by
      unfold tail
      apply Finset.sum_le_sum
      intro r _
      have := hh1 (i + 1) (y + (r : ℝ) / Q (i + 1))
      have hk := hκ (i + 1) r
      nlinarith
    -- small part
    have hsum_range : ∑ m ∈ range (k + 1), θ m = θ 0 + ∑ m ∈ range k, θ (m + 1) := by
      rw [Finset.sum_range_succ']; ring
    have hsmall_each : ∀ r ∈ (S (i + 1)).filter (fun r => ¬ P r),
        h (i + 1) (y + (r : ℝ) / Q (i + 1)) ≤
          ∑ m ∈ range k, β ^ m * tail Q κ S (i + 1 + m + 1) (θ (m + 1)) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨hrS, hrP⟩ := hr
      have hrle : |(r : ℝ)| ≤ θ 0 * Q (i + 1) := le_of_not_gt hrP
      have hQi := hQ (i + 1)
      have hNr : N ((r : ℝ) / Q (i + 1)) ≤ θ 0 := by
        have := hdisp (i + 1) r hrS
        have h2 : |(r : ℝ)| / Q (i + 1) ≤ θ 0 := by
          rw [div_le_iff₀ hQi]; exact hrle
        linarith
      have hNy : N y ≤ N (y + (r : ℝ) / Q (i + 1)) + N ((r : ℝ) / Q (i + 1)) := by
        have := hsub (y + (r : ℝ) / Q (i + 1)) (-((r : ℝ) / Q (i + 1)))
        rw [hneg] at this
        simpa using this
      have hbound : ε + ∑ m ∈ range k, θ (m + 1) ≤ N (y + (r : ℝ) / Q (i + 1)) := by
        rw [hsum_range] at hy
        linarith
      have := ih (i + 1) (by omega) (fun m => θ (m + 1)) (fun m => hθ (m + 1))
        (y + (r : ℝ) / Q (i + 1)) hbound
      simpa using this
    have hsmall :
        ∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1))
          ≤ ∑ m ∈ range k, β ^ (m + 1) * tail Q κ S (i + 1 + m + 1) (θ (m + 1)) := by
      set T : ℝ := ∑ m ∈ range k, β ^ m * tail Q κ S (i + 1 + m + 1) (θ (m + 1)) with hT
      have hT0 : 0 ≤ T := by
        apply Finset.sum_nonneg
        intro m _
        apply mul_nonneg (pow_nonneg hβ0 m)
        unfold tail
        exact Finset.sum_nonneg (fun r _ => hκ _ r)
      calc ∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r * h (i + 1) (y + (r : ℝ) / Q (i + 1))
          ≤ ∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r * T := by
            apply Finset.sum_le_sum
            intro r hr
            exact mul_le_mul_of_nonneg_left (hsmall_each r hr) (hκ _ r)
        _ = (∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r) * T := by rw [Finset.sum_mul]
        _ ≤ β * T := by
            apply mul_le_mul_of_nonneg_right _ hT0
            calc ∑ r ∈ (S (i + 1)).filter (fun r => ¬ P r), κ (i + 1) r
                ≤ ∑ r ∈ S (i + 1), κ (i + 1) r :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    (fun r _ _ => hκ _ r)
              _ ≤ β := hβ (i + 1)
        _ = ∑ m ∈ range k, β ^ (m + 1) * tail Q κ S (i + 1 + m + 1) (θ (m + 1)) := by
            rw [hT, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            ring
    have hrhs : ∑ m ∈ range (k + 1), β ^ m * tail Q κ S (i + m + 1) (θ m)
        = tail Q κ S (i + 1) (θ 0) +
          ∑ m ∈ range k, β ^ (m + 1) * tail Q κ S (i + 1 + m + 1) (θ (m + 1)) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 2
      ring
    rw [hrhs]
    calc h i y ≤ _ := step
      _ = _ := hsplit
      _ ≤ _ := add_le_add hlarge hsmall

/-- Geometric sum used for the thresholds `θ_m = 2^{-(m+3)} u`. -/
theorem geom_thresholds (k : ℕ) : ∑ m ∈ range k, (1 / 2 : ℝ) ^ (m + 3) ≤ 1 / 4 := by
  have : ∀ k : ℕ, ∑ m ∈ range k, (1 / 2 : ℝ) ^ (m + 3) = 1 / 4 - (1 / 2) ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ihk =>
      rw [Finset.sum_range_succ, ihk]
      ring
  rw [this k]
  have : 0 ≤ (1 / 2 : ℝ) ^ (k + 2) := by positivity
  linarith

end TPP
