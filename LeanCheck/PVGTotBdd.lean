import Mathlib
import LeanCheck.PVGProdLimit

/-!
# PVG: the dilates `aS` are totally bounded (Lean check)

Scope. Proposition 8.91 of `PVG_v43` (Part II). Let `γ` be a topology on `ℝ` and `a ∈ ℝ`. Put `J_a = aS + (-a)S` (`Ja a`).

* `hyp_of_trace` : if `γ` and the Bohr topology induce the same topology on `J_b`, then for every free ultrafilter `U`, every
  `γ`-neighbourhood `W` of `0`, for `U`-most `n` and `U`-most `m`: `n < m` and `b s_n - b s_m ∈ W` (`Hyp γ b`); it uses `prodLimit`
  (Lemma 8.90).
* `totbdd_seq` : if `Hyp γ (-a)`, then for every `γ`-neighbourhood `W` of `0` there is a finite set `F` with `a s_n - f ∈ W` for some
  `f ∈ F`, for every `n ≥ 1` (the sequence `(a s_n)` is totally bounded for `γ`).
* `totbdd` : if `γ` and the Bohr topology induce the same topology on `J_a`, then `aS` is `γ`-totally bounded: for every
  `γ`-neighbourhood `W` of `0` there is a finite `F` such that every `a s`, `s ∈ S`, lies in `F + W`.

No group-topology hypothesis on `γ` is used (only that `W` is a neighbourhood of `0`, hence contains `0`). The proof is the one of the
article: a sequence of points whose pairwise differences avoid `W`, a free ultrafilter containing its index set, and `prodLimit`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

/-- `J_a = aS + (-a)S`. -/
def Ja (a : ℝ) : Set ℝ := {x | ∃ s ∈ Sset, ∃ t ∈ Sset, x = a * s + (-a) * t}

lemma sS_mem_Sset {n : ℕ} (hn : 1 ≤ n) : sS n ∈ Sset := Or.inr ⟨n, hn, Or.inl rfl⟩

lemma neg_sS_mem_Sset {n : ℕ} (hn : 1 ≤ n) : -sS n ∈ Sset := Or.inr ⟨n, hn, Or.inr rfl⟩

lemma zero_mem_Ja (a : ℝ) : (0 : ℝ) ∈ Ja a :=
  ⟨0, zero_mem_Sset, 0, zero_mem_Sset, by ring⟩

lemma Ja_neg (a : ℝ) : Ja (-a) = Ja a := by
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ht, s, hs, by ring⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ht, s, hs, by ring⟩

lemma diff_mem_Ja (a : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) : a * sS n - a * sS m ∈ Ja a :=
  ⟨sS n, sS_mem_Sset hn, sS m, sS_mem_Sset hm, by ring⟩

/-- The consequence of the Bohr trace on `J_b` used in the proof of Proposition 8.91. -/
def Hyp (γ : TopologicalSpace ℝ) (b : ℝ) : Prop :=
  ∀ U : Ultrafilter ℕ, Free U → ∀ W ∈ @nhds ℝ γ 0,
    ∀ᶠ n in (U : Filter ℕ), ∀ᶠ m in (U : Filter ℕ), n < m ∧ b * sS n - b * sS m ∈ W

/-- If `γ` induces on `J_b` the Bohr topology, then `Hyp γ b`. -/
theorem hyp_of_trace (γ : TopologicalSpace ℝ) (b : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja b → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja b → ℝ) bohrTop) : Hyp γ b := by
  intro U hU W hW
  set z0 : Ja b := ⟨0, zero_mem_Ja b⟩ with hz0
  have h1 : (Subtype.val : Ja b → ℝ) ⁻¹' W ∈ @nhds (Ja b) (TopologicalSpace.induced Subtype.val γ) z0 := by
    rw [@nhds_induced ℝ (Ja b) γ Subtype.val z0]
    exact Filter.preimage_mem_comap hW
  rw [hind, @nhds_induced ℝ (Ja b) bohrTop Subtype.val z0] at h1
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 h1
  have hge1 : ∀ᶠ n in (U : Filter ℕ), 1 ≤ n := by
    have h : (U : Filter ℕ) ≤ atTop := by
      have := hU
      unfold Free at this
      rwa [Nat.cofinite_eq_atTop] at this
    exact h (eventually_ge_atTop 1)
  filter_upwards [prodLimit b U hU V hV, hge1] with n hn hn1
  filter_upwards [hn, hge1] with m hm hm1
  refine ⟨hm.1, ?_⟩
  have hmemJ : b * sS n - b * sS m ∈ Ja b := diff_mem_Ja b hn1 hm1
  have : (⟨b * sS n - b * sS m, hmemJ⟩ : Ja b) ∈ (Subtype.val : Ja b → ℝ) ⁻¹' V := hm.2
  exact hVW this

/-- A free ultrafilter containing a given infinite set of indices. -/
lemma exists_free_ultrafilter_mem {N : Set ℕ} (hN : N.Infinite) :
    ∃ U : Ultrafilter ℕ, Free U ∧ N ∈ (U : Filter ℕ) := by
  have hne : (Filter.cofinite ⊓ 𝓟 N : Filter ℕ).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro V hV
    have hVc : Vᶜ.Finite := hV
    have : (N \ Vᶜ).Nonempty := (hN.diff hVc).nonempty
    obtain ⟨x, hxN, hxV⟩ := this
    exact ⟨x, by simpa using hxV, hxN⟩
  refine ⟨Ultrafilter.of (Filter.cofinite ⊓ 𝓟 N), ?_, ?_⟩
  · exact (Ultrafilter.of_le _).trans inf_le_left
  · have := (Ultrafilter.of_le (Filter.cofinite ⊓ 𝓟 N)).trans (inf_le_right : (Filter.cofinite ⊓ 𝓟 N) ≤ 𝓟 N)
    exact this (mem_principal_self N)

/-- The sequence `(a s_n)` is totally bounded for `γ`, assuming `Hyp γ (-a)`. -/
theorem totbdd_seq (γ : TopologicalSpace ℝ) (a : ℝ) (hH : Hyp γ (-a)) (W : Set ℝ)
    (hW : W ∈ @nhds ℝ γ 0) : ∃ F : Finset ℝ, ∀ n : ℕ, 1 ≤ n → ∃ f ∈ F, a * sS n - f ∈ W := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ F, ∃ n, 1 ≤ n ∧ ∀ f ∈ F, a * sS n - f ∉ W`
  have h0W : (0 : ℝ) ∈ W := mem_of_mem_nhds hW
  have step : ∀ N : ℕ, ∃ n : ℕ, 1 ≤ n ∧ N < n ∧ ∀ k ≤ N, a * sS n - a * sS k ∉ W := by
    intro N
    obtain ⟨n, hn1, hn⟩ := hcon ((Finset.range (N + 1)).image (fun k => a * sS k))
    have hnotle : ¬ n ≤ N := by
      intro hle
      have := hn (a * sS n) (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hle), rfl⟩)
      simp at this
      exact this h0W
    refine ⟨n, hn1, not_le.1 hnotle, fun k hk hmem => ?_⟩
    exact hn (a * sS k) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩) hmem
  choose g hg1 hg2 hg3 using step
  let seq : ℕ → ℕ := fun i => Nat.rec (g 0) (fun _ x => g x) i
  have hseq_succ : ∀ i, seq (i + 1) = g (seq i) := fun i => rfl
  have hmono : StrictMono seq := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    rw [hseq_succ]
    exact hg2 (seq i)
  have hsep : ∀ p q : ℕ, p < q → a * sS (seq q) - a * sS (seq p) ∉ W := by
    intro p q hpq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have hle : seq p ≤ seq r := hmono.monotone (by omega)
    rw [hseq_succ]
    exact hg3 (seq r) (seq p) hle
  have hseq1 : ∀ i, 1 ≤ seq i := by
    intro i
    cases i with
    | zero => exact hg1 0
    | succ j => rw [hseq_succ]; exact hg1 _
  have hinf : (Set.range seq).Infinite := Set.infinite_range_of_injective hmono.injective
  obtain ⟨U, hU, hNU⟩ := exists_free_ultrafilter_mem hinf
  have key := hH U hU W hW
  have hcontra : ∃ n m : ℕ, n ∈ Set.range seq ∧ m ∈ Set.range seq ∧ n < m ∧ (-a) * sS n - (-a) * sS m ∈ W := by
    have h2 : ∀ᶠ n in (U : Filter ℕ), n ∈ Set.range seq ∧ ∀ᶠ m in (U : Filter ℕ), n < m ∧ (-a) * sS n - (-a) * sS m ∈ W := by
      filter_upwards [hNU, key] with n hn hkey
      exact ⟨hn, hkey⟩
    obtain ⟨n, hn, hm⟩ := h2.exists
    obtain ⟨m, hmm, hmN⟩ := (hm.and hNU).exists
    exact ⟨n, m, hn, hmN, hmm.1, hmm.2⟩
  obtain ⟨n, m, ⟨p, rfl⟩, ⟨q, rfl⟩, hlt, hmem⟩ := hcontra
  have hpq : p < q := hmono.lt_iff_lt.1 hlt
  apply hsep p q hpq
  have : a * sS (seq q) - a * sS (seq p) = (-a) * sS (seq p) - (-a) * sS (seq q) := by ring
  rw [this]
  exact hmem

/-- Proposition 8.91: if `γ` induces the Bohr topology on `J_a`, then `aS` is `γ`-totally bounded. -/
theorem totbdd (γ : TopologicalSpace ℝ) (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop)
    (W : Set ℝ) (hW : W ∈ @nhds ℝ γ 0) :
    ∃ F : Finset ℝ, ∀ s ∈ Sset, ∃ f ∈ F, a * s - f ∈ W := by
  have hA : Hyp γ a := hyp_of_trace γ a hind
  have hneg : TopologicalSpace.induced (Subtype.val : Ja (-a) → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja (-a) → ℝ) bohrTop := by
    rw [Ja_neg]; exact hind
  have hB : Hyp γ (-a) := hyp_of_trace γ (-a) hneg
  obtain ⟨F1, hF1⟩ := totbdd_seq γ a hB W hW
  obtain ⟨F2, hF2⟩ := totbdd_seq γ (-a) (by simpa using hA) W hW
  refine ⟨insert 0 (F1 ∪ F2), fun s hs => ?_⟩
  rcases hs with rfl | ⟨n, hn, rfl | rfl⟩
  · exact ⟨0, Finset.mem_insert_self _ _, by simpa using mem_of_mem_nhds hW⟩
  · obtain ⟨f, hf, hfW⟩ := hF1 n hn
    exact ⟨f, Finset.mem_insert_of_mem (Finset.mem_union_left _ hf), hfW⟩
  · obtain ⟨f, hf, hfW⟩ := hF2 n hn
    refine ⟨f, Finset.mem_insert_of_mem (Finset.mem_union_right _ hf), ?_⟩
    simpa using hfW

end Lac
end PVG
