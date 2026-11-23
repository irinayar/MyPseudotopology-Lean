import Mathlib

/-!
# TwoPrimes: the discrete counting step of the near-uniformity theorem for cut balls (L1c)

A "cut ball" is a union of clusters `j q + Y j` (`j ∈ I`, offsets `Y j ⊂ [-U, U]` with `2 U < q`).  For every
real cut point `x` the number of ball elements `≤ x` lies between the total size of the clusters that lie entirely
below `x` and that total plus `M` (a bound for one cluster): only one cluster can be cut by `x`, because two clusters
that both meet the window `[x - U, x + U]` would differ by less than `q`.  This is the step
"`m' F(x) ∈ [φ + j* + J', φ + j* + J' + 1]`" in the proof of Theorem L1c (note V of the TwoPrimes project).
-/

namespace LeanCheck
namespace TwoPrimes

open Finset

/-- At most one cluster is cut by a given cut point. -/
lemma cluster_mid_card_le_one (I : Finset ℤ) (q U x : ℤ) (hq : 0 < q) (hU : 2 * U < q) :
    (I.filter (fun j => ¬ (j * q + U ≤ x) ∧ j * q - U ≤ x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj j' hj'
  rw [Finset.mem_filter] at hj hj'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : j + 1 ≤ j' := by omega
    have h2 : q ≤ q * (j' - j) := by nlinarith
    nlinarith [hj.2.1, hj'.2.2, hj.2.2, hj'.2.1]
  · have h1 : j' + 1 ≤ j := by omega
    have h2 : q ≤ q * (j - j') := by nlinarith
    nlinarith [hj.2.1, hj'.2.2, hj.2.2, hj'.2.1]

/-- Counting bounds for a cut ball. -/
theorem cut_count_bounds (I : Finset ℤ) (Y : ℤ → Finset ℤ) (q U M : ℤ) (hq : 0 < q) (hU : 2 * U < q)
    (hM0 : 0 ≤ M) (hY : ∀ j ∈ I, ∀ y ∈ Y j, |y| ≤ U) (hM : ∀ j ∈ I, ((Y j).card : ℤ) ≤ M) (x : ℤ) :
    (∑ j ∈ I.filter (fun j => j * q + U ≤ x), ((Y j).card : ℤ)) ≤
        ∑ j ∈ I, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) ∧
      ∑ j ∈ I, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) ≤
        (∑ j ∈ I.filter (fun j => j * q + U ≤ x), ((Y j).card : ℤ)) + M := by
  classical
  set A := I.filter (fun j => j * q + U ≤ x) with hA
  set R := I.filter (fun j => ¬ (j * q + U ≤ x)) with hR
  set Mid := I.filter (fun j => ¬ (j * q + U ≤ x) ∧ j * q - U ≤ x) with hMid
  have hsplit : ∑ j ∈ I, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ)
      = ∑ j ∈ A, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ)
        + ∑ j ∈ R, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) := by
    rw [hA, hR]; exact (Finset.sum_filter_add_sum_filter_not I _ _).symm
  have hfull : ∀ j ∈ A, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) = ((Y j).card : ℤ) := by
    intro j hj
    rw [hA, Finset.mem_filter] at hj
    congr 1
    rw [Finset.filter_true_of_mem]
    intro y hy
    have := hY j hj.1 y hy
    rw [abs_le] at this
    linarith [hj.2, this.2]
  have hnonneg : ∀ j, 0 ≤ (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) := fun j => by positivity
  have hRtoMid : ∑ j ∈ R, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ)
      ≤ ∑ j ∈ Mid, ((Y j).card : ℤ) := by
    have hsub : ∑ j ∈ R, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ)
        = ∑ j ∈ Mid, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) := by
      symm
      apply Finset.sum_subset
      · intro j hj; rw [hMid, Finset.mem_filter] at hj; rw [hR, Finset.mem_filter]; exact ⟨hj.1, hj.2.1⟩
      · intro j hj hjn
        rw [hR, Finset.mem_filter] at hj
        have hlt : x < j * q - U := by
          by_contra hcon
          apply hjn
          rw [hMid, Finset.mem_filter]; exact ⟨hj.1, hj.2, by omega⟩
        have : (Y j).filter (fun y => j * q + y ≤ x) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro y hy
          have := hY j hj.1 y hy
          rw [abs_le] at this
          linarith [this.1]
        rw [this]; simp
    rw [hsub]
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast Finset.card_filter_le _ _
  have hMidM : ∑ j ∈ Mid, ((Y j).card : ℤ) ≤ M := by
    have hc : Mid.card ≤ 1 := cluster_mid_card_le_one I q U x hq hU
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
    · rw [Finset.card_eq_zero.mp h0]; simpa using hM0
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have haI : a ∈ I := by
        have hmem : a ∈ Mid := by rw [ha]; exact Finset.mem_singleton_self a
        rw [hMid, Finset.mem_filter] at hmem; exact hmem.1
      rw [ha, Finset.sum_singleton]; exact hM a haI
  constructor
  · rw [hsplit, Finset.sum_congr rfl hfull]
    have : 0 ≤ ∑ j ∈ R, (((Y j).filter (fun y => j * q + y ≤ x)).card : ℤ) :=
      Finset.sum_nonneg (fun j _ => hnonneg j)
    linarith
  · rw [hsplit, Finset.sum_congr rfl hfull]
    linarith

end TwoPrimes
end LeanCheck
