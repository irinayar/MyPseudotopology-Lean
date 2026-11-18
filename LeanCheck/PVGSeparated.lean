import Mathlib
import LeanCheck.PVGTotBdd

/-!
# PVG: separated sets in `aS` for a topology with the Bohr trace (Lean check)

Scope. Lemma 17.10 of `PVG_v50`/`PVG_v51` (Part II). Let `γ` be a topology on `ℝ`, not necessarily a group topology, `a ∈ ℝ` such that
`γ` and the Bohr topology induce the same topology on `J_a = aS + (-a)S` (`Ja a`), and `W` a `γ`-neighbourhood of `0`.

* `exists_pair_of_hyp` : if `Hyp γ b` (the consequence of the Bohr trace used in `PVGTotBdd`), `N ⊆ ℕ` is infinite and `W ∈ 𝓝 0`, then
  there are `n < m` in `N` with `b s_n - b s_m ∈ W`; this is the ultrafilter step of the proof of Proposition 8.91, extracted;
* `no_separated` : if `Y ⊆ aS` is infinite, then there are `y ≠ y'` in `Y` with `y - y' ∈ W`;
* `no_separated_set` : the same statement as a negation: `aS` contains no infinite set whose pairwise differences avoid `W`.

Neither addition nor symmetry of `W` is used (only `Hyp γ (±a)`, which follows from the Bohr trace on `J_a` by `hyp_of_trace`).
The case `a = 0` is excluded because then `aS = {0}` has no infinite subset.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

lemma sS_lt {n m : ℕ} (h : n < m) : sS n < sS m := by
  unfold sS
  exact pow_lt_pow_right₀ (by norm_num) (Nat.pow_lt_pow_left h (by norm_num))

lemma sS_injective : Function.Injective sS := by
  intro n m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact (sS_lt h1).ne h
  · exact (sS_lt h1).ne' h

/-- The ultrafilter step: from `Hyp γ b` and an infinite index set one finds `n < m` in it with `b s_n - b s_m ∈ W`. -/
theorem exists_pair_of_hyp (γ : TopologicalSpace ℝ) (b : ℝ) (hH : Hyp γ b) (N : Set ℕ)
    (hN : N.Infinite) (W : Set ℝ) (hW : W ∈ @nhds ℝ γ 0) :
    ∃ n ∈ N, ∃ m ∈ N, n < m ∧ b * sS n - b * sS m ∈ W := by
  obtain ⟨U, hU, hNU⟩ := exists_free_ultrafilter_mem hN
  have key := hH U hU W hW
  have h2 : ∀ᶠ n in (U : Filter ℕ), n ∈ N ∧
      ∀ᶠ m in (U : Filter ℕ), n < m ∧ b * sS n - b * sS m ∈ W := by
    filter_upwards [hNU, key] with n hn hkey
    exact ⟨hn, hkey⟩
  obtain ⟨n, hn, hm⟩ := h2.exists
  obtain ⟨m, hmm, hmN⟩ := (hm.and hNU).exists
  exact ⟨n, hn, m, hmN, hmm.1, hmm.2⟩

/-- Lemma 17.10: an infinite subset of `aS` contains two distinct points whose difference lies in `W`. -/
theorem no_separated (γ : TopologicalSpace ℝ) (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop)
    (W : Set ℝ) (hW : W ∈ @nhds ℝ γ 0) (Y : Set ℝ) (hY : ∀ y ∈ Y, ∃ s ∈ Sset, y = a * s)
    (hinf : Y.Infinite) :
    ∃ y ∈ Y, ∃ y' ∈ Y, y ≠ y' ∧ y - y' ∈ W := by
  by_cases ha : a = 0
  · exfalso
    apply hinf
    refine (Set.finite_singleton (0 : ℝ)).subset ?_
    intro y hy
    obtain ⟨s, -, rfl⟩ := hY y hy
    simp [ha]
  · have hHa : Hyp γ a := hyp_of_trace γ a hind
    have hneg : TopologicalSpace.induced (Subtype.val : Ja (-a) → ℝ) γ =
        TopologicalSpace.induced (Subtype.val : Ja (-a) → ℝ) bohrTop := by
      rw [Ja_neg]; exact hind
    have hHb : Hyp γ (-a) := hyp_of_trace γ (-a) hneg
    have claim : ∀ b : ℝ, b ≠ 0 → Hyp γ b →
        Set.Infinite {y | y ∈ Y ∧ ∃ n : ℕ, 1 ≤ n ∧ y = b * sS n} →
        ∃ y ∈ Y, ∃ y' ∈ Y, y ≠ y' ∧ y - y' ∈ W := by
      intro b hb hHb' hYb
      set N : Set ℕ := {n | 1 ≤ n ∧ b * sS n ∈ Y} with hNdef
      have himg : ((fun n : ℕ => b * sS n) '' N).Infinite := by
        refine Set.Infinite.mono ?_ hYb
        rintro y ⟨hyY, n, hn1, rfl⟩
        exact ⟨n, ⟨hn1, hyY⟩, rfl⟩
      have hN : N.Infinite := Set.Infinite.of_image _ himg
      obtain ⟨n, hn, m, hm, hnm, hW'⟩ := exists_pair_of_hyp γ b hHb' N hN W hW
      refine ⟨b * sS n, hn.2, b * sS m, hm.2, ?_, hW'⟩
      intro h
      have h' : sS n = sS m := mul_left_cancel₀ hb h
      exact hnm.ne (sS_injective h')
    have hdiff : (Y \ {0}).Infinite := hinf.sdiff (Set.finite_singleton 0)
    have hsub : Y \ {0} ⊆ {y | y ∈ Y ∧ ∃ n : ℕ, 1 ≤ n ∧ y = a * sS n} ∪
        {y | y ∈ Y ∧ ∃ n : ℕ, 1 ≤ n ∧ y = (-a) * sS n} := by
      rintro y ⟨hyY, hy0⟩
      obtain ⟨s, hs, rfl⟩ := hY y hyY
      rcases hs with rfl | ⟨n, hn, rfl | rfl⟩
      · exact (hy0 (by simp)).elim
      · exact Or.inl ⟨hyY, n, hn, rfl⟩
      · exact Or.inr ⟨hyY, n, hn, by ring⟩
    rcases Set.infinite_union.1 (Set.Infinite.mono hsub hdiff) with h | h
    · exact claim a ha hHa h
    · exact claim (-a) (neg_ne_zero.2 ha) hHb h

/-- The same statement as a negation: `aS` contains no infinite set whose pairwise differences avoid `W`. -/
theorem no_separated_set (γ : TopologicalSpace ℝ) (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop)
    (W : Set ℝ) (hW : W ∈ @nhds ℝ γ 0) :
    ¬ ∃ Y : Set ℝ, Y.Infinite ∧ (∀ y ∈ Y, ∃ s ∈ Sset, y = a * s) ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → y - y' ∉ W := by
  rintro ⟨Y, hinf, hY, hsep⟩
  obtain ⟨y, hy, y', hy', hne, hW'⟩ := no_separated γ a hind W hW Y hY hinf
  exact hsep y hy y' hy' hne hW'

end Lac
end PVG
