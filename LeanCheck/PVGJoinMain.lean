import Mathlib
import LeanCheck.PVGJoinLr

/-!
# PVG: joins in the Boolean algebra of lacunary PVGs (Lean check)

Scope. Theorem 8.65 of PVG_v28 (planned), Addendum O of the research note. For `A, B ⊆ ℕ`, `ξ_{A ∪ B}` is the finest PVG coarser than `ξ_A`
and `ξ_B`: every PVG pseudotopology `conv` on `ℝ` in which every `ξ_A`-convergent and every `ξ_B`-convergent filter converges, has every
`ξ_{A ∪ B}`-convergent filter convergent (`join_least`), and `ξ_{A ∪ B}` is itself a PVG containing both (`subConv_union_isLeast`).

* `sumSetA_union_sub`: `a₁S_{A ∪ B} + … ⊆ (a₁S_A + …) + (a₁S_B + …)`;
* `lam_indep`: for disjoint infinite `A`, `B`: if `λ₁ ∈ Λ_A`, `λ₂ ∈ Λ_B` and `λ₁ + λ₂ ∈ e(ℝ)` then `λ₁ = λ₂ = 0` (Theorem 8.36 in the
  pairwise form `independence_sep` of `PVGSorted` for the two jointly lacunary sequences `y^A`, `y^B`);
* `join_ultra`, `join_core`, `join_least`: the theorem (ultrafilters, disjoint sets, general sets).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-! ### Sum sets of a union -/

lemma sumSetA_union_sub (A B : Set ℕ) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA (A ∪ B) l →
    ∃ y z : ℝ, y ∈ sumSetA A l ∧ z ∈ sumSetA B l ∧ x = y + z
  | [], x, hx => by
    have : x = 0 := hx
    exact ⟨0, 0, rfl, rfl, by simp [this]⟩
  | a :: l, x, hx => by
    obtain ⟨c, hc, w, hw, rfl⟩ := mem_sumSetA_cons.1 hx
    obtain ⟨y', z', hy', hz', rfl⟩ := sumSetA_union_sub A B l w hw
    have hc' : c ∈ SsetA A ∨ c ∈ SsetA B := by
      rcases hc with h0 | ⟨n, hn, h1, h2⟩
      · exact Or.inl (Or.inl h0)
      · rcases hn with hn | hn
        · exact Or.inl (Or.inr ⟨n, hn, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨n, hn, h1, h2⟩)
    rcases hc' with hcA | hcB
    · exact ⟨a * c + y', a * 0 + z', mem_sumSetA_cons.2 ⟨c, hcA, y', hy', rfl⟩, mem_sumSetA_cons.2 ⟨0, zero_mem_SsetA B, z', hz', rfl⟩, by ring⟩
    · exact ⟨a * 0 + y', a * c + z', mem_sumSetA_cons.2 ⟨0, zero_mem_SsetA A, y', hy', rfl⟩, mem_sumSetA_cons.2 ⟨c, hcB, z', hz', rfl⟩, by ring⟩

/-! ### Finite `A` -/

lemma sumSetA_mem_IA (A : Set ℕ) (l : List ℝ) : sumSetA A l ∈ IA A :=
  mem_IA_iff.2 ⟨0, l, fun z hz => ⟨0, z, by simp, hz, by simp⟩⟩

/-- For finite `A`, an ultrafilter on `a₁S_A + … + a_kS_A` has Bohr limit in `e(ℝ)`. -/
lemma lr_of_finite {A : Set ℕ} (hA : A.Finite) (l : List ℝ) (V : Ultrafilter ℝ) (hV : sumSetA A l ∈ V) :
    ∃ y : ℝ, Lr V = e y := by
  obtain ⟨M, hM⟩ := IA_bounded_of_finite hA (sumSetA_mem_IA A l)
  have hI : Icc (-M) M ∈ V := Filter.mem_of_superset hV (fun z hz => by
    have := hM z hz
    exact ⟨by linarith [(abs_le.1 this).1], (abs_le.1 this).2⟩)
  obtain ⟨y, -, hy⟩ := isCompact_Icc.ultrafilter_le_nhds V (Filter.le_principal_iff.2 hI)
  exact ⟨y, Lr_eq_of_tendsto ((continuous_e.tendsto y).comp hy)⟩

/-! ### Limits of ultrafilters on `a₁S_A + … + a_kS_A` for infinite `A` -/

theorem Lr_sumSetA_mem {A : Set ℕ} (hA : A.Infinite) :
    ∀ (l : List ℝ) (V : Ultrafilter ℝ), sumSetA A l ∈ V → Lr V ∈ Esub ⊔ LamA A
  | [], V, hV => by
    have h0 : ({0} : Set ℝ) ∈ V := hV
    have hle : (V : Filter ℝ) ≤ pure 0 := Filter.le_pure_iff.2 h0
    have : Lr V = e 0 := Lr_eq_of_tendsto ((tendsto_pure_nhds e 0).mono_left hle)
    rw [this]
    exact Submodule.mem_sup_left ⟨0, rfl⟩
  | a :: l, V, hV => by
    have hV' : a • SsetA A + sumSetA A l ∈ V := hV
    obtain ⟨V1, V2, h1, h2, -, hLr⟩ := exists_split V hV'
    have hV2 := Lr_sumSetA_mem hA l V2 h2
    obtain ⟨V3, hV3S, hV3⟩ := exists_lift (fun x => a * x) (SsetA A) V1 (by
      refine Filter.mem_of_superset h1 ?_
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.1 hx
      exact ⟨c, hc, by simp [smul_eq_mul]⟩)
    have hV1 : Lr V1 = a • Lr V3 := by rw [← hV3, Lr_smul_map]
    have hV3' := Lr_SsetA_mem hA V3 hV3S
    rw [hLr, hV1]
    exact add_mem (Submodule.smul_mem _ a hV3') hV2

/-! ### Joint separation of the two enumerations -/

/-- The index set of the `j`-th sequence. -/
def nA (A B : Set ℕ) (j : Fin 2) : Set ℕ := if (j : ℕ) = 0 then idx A else idx B

lemma nA_zero (A B : Set ℕ) : nA A B 0 = idx A := by simp [nA]

lemma nA_one (A B : Set ℕ) : nA A B 1 = idx B := by simp [nA]

lemma fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j <;> simp

/-- The two sequences `y^A`, `y^B`. -/
noncomputable def ys (A B : Set ℕ) (j : Fin 2) (k : ℕ) : ℝ := sS (Nat.nth (· ∈ nA A B j) k)

lemma ys_zero (A B : Set ℕ) : ys A B 0 = enumA A := by
  funext k; simp [ys, enumA, nA_zero]

lemma ys_one (A B : Set ℕ) : ys A B 1 = enumA B := by
  funext k; simp [ys, enumA, nA_one]

lemma sS_strictMono : StrictMono (fun n : ℕ => sS n) := by
  intro n m h
  unfold sS
  exact pow_lt_pow_right₀ (by norm_num) (Nat.pow_lt_pow_left h (by norm_num))

lemma nA_infinite {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (j : Fin 2) :
    (setOf fun n => n ∈ nA A B j).Infinite := by
  rcases fin2_cases j with rfl | rfl
  · rw [nA_zero]; exact idx_infinite hA
  · rw [nA_one]; exact idx_infinite hB

lemma nth_inj {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (hAB : Disjoint A B) {p q : Fin 2 × ℕ}
    (h : Nat.nth (· ∈ nA A B p.1) p.2 = Nat.nth (· ∈ nA A B q.1) q.2) : p = q := by
  obtain ⟨j, k⟩ := p
  obtain ⟨j', k'⟩ := q
  simp only at h
  have hiA := nA_infinite hA hB 0
  have hiB := nA_infinite hA hB 1
  rw [nA_zero] at hiA
  rw [nA_one] at hiB
  rcases fin2_cases j with rfl | rfl <;> rcases fin2_cases j' with rfl | rfl
  · rw [nA_zero] at h
    have := (Nat.nth_strictMono hiA).injective h
    rw [this]
  · exfalso
    rw [nA_zero, nA_one] at h
    have hpm := Nat.nth_mem_of_infinite hiA k
    have hqm := Nat.nth_mem_of_infinite hiB k'
    rw [h] at hpm
    exact Set.disjoint_left.1 hAB hpm.1 hqm.1
  · exfalso
    rw [nA_zero, nA_one] at h
    have hpm := Nat.nth_mem_of_infinite hiB k
    have hqm := Nat.nth_mem_of_infinite hiA k'
    rw [← h] at hqm
    exact Set.disjoint_left.1 hAB hqm.1 hpm.1
  · rw [nA_one] at h
    have := (Nat.nth_strictMono hiB).injective h
    rw [this]

lemma ys_joint {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (hAB : Disjoint A B) :
    JointSep (ys A B) := by
  have hnth : ∀ (j : Fin 2) (k : ℕ), k ≤ Nat.nth (· ∈ nA A B j) k :=
    fun j k => (Nat.nth_strictMono (nA_infinite hA hB j)).id_le k
  refine ⟨fun j k => (sS_pos _).ne', ?_, ?_⟩
  · intro t
    obtain ⟨N, hN⟩ := sS_unbounded t
    refine Set.Finite.subset (Set.finite_univ.prod (Set.finite_Iio N)) ?_
    intro p hp
    refine ⟨trivial, ?_⟩
    simp only [Set.mem_Iio]
    by_contra hcon
    push Not at hcon
    have h1 : sS N ≤ sS (Nat.nth (· ∈ nA A B p.1) p.2) := sS_mono (le_trans hcon (hnth p.1 p.2))
    have h2 : |ys A B p.1 p.2| ≤ t := hp
    have h3 : ys A B p.1 p.2 = sS (Nat.nth (· ∈ nA A B p.1) p.2) := rfl
    rw [h3, abs_of_pos (sS_pos _)] at h2
    linarith
  · intro R
    obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
    refine ⟨{p : Fin 2 × ℕ | p.2 < N0}, ?_, ?_⟩
    · exact Set.Finite.subset (Set.finite_univ.prod (Set.finite_Iio N0)) (fun p hp => ⟨trivial, hp⟩)
    · intro p hp q hq hpq
      simp only [Set.mem_setOf_eq, not_lt] at hp hq
      have hmpN : N0 ≤ Nat.nth (· ∈ nA A B p.1) p.2 := le_trans hp (hnth p.1 p.2)
      have hmqN : N0 ≤ Nat.nth (· ∈ nA A B q.1) q.2 := le_trans hq (hnth q.1 q.2)
      have hne : Nat.nth (· ∈ nA A B p.1) p.2 ≠ Nat.nth (· ∈ nA A B q.1) q.2 := fun h => hpq (nth_inj hA hB hAB h)
      have key : ∀ a b : ℕ, N0 ≤ a → a < b → R * sS a ≤ sS b := by
        intro a b ha hab
        have h1 : sS (a + 1) ≤ sS b := sS_mono hab
        have h2 : sS (a + 1) = sS a * 2 ^ (2 * a + 1) := sS_succ a
        have h3 : R ≤ 2 ^ (2 * a + 1) := by
          calc R ≤ 2 ^ N0 := hN0.le
            _ ≤ 2 ^ (2 * a + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        calc R * sS a ≤ 2 ^ (2 * a + 1) * sS a := mul_le_mul_of_nonneg_right h3 (sS_pos a).le
          _ = sS (a + 1) := by rw [h2]; ring
          _ ≤ sS b := h1
      show R * |ys A B p.1 p.2| ≤ |ys A B q.1 q.2| ∨ R * |ys A B q.1 q.2| ≤ |ys A B p.1 p.2|
      have hcp : |ys A B p.1 p.2| = sS (Nat.nth (· ∈ nA A B p.1) p.2) := abs_of_pos (sS_pos _)
      have hcq : |ys A B q.1 q.2| = sS (Nat.nth (· ∈ nA A B q.1) q.2) := abs_of_pos (sS_pos _)
      rw [hcp, hcq]
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl (key _ _ hmpN h)
      · exact Or.inr (key _ _ hmqN h)

/-! ### Independence of `Λ_A` and `Λ_B` -/

lemma smul_zero_K (κ : K) : (0 : ℝ) • κ = 0 := by
  ext b
  simp [smul_apply]

lemma lam_indep {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (hAB : Disjoint A B) {l1 l2 : K}
    (h1 : l1 ∈ LamA A) (h2 : l2 ∈ LamA B) {x : ℝ} (h : l1 + l2 = e x) : l1 = 0 ∧ l2 = 0 := by
  have hjoint := ys_joint hA hB hAB
  set f1 : {W : Ultrafilter ℕ // Free W} → K := fun W => L (enumA A) W.1 with hf1
  set f2 : {W : Ultrafilter ℕ // Free W} → K := fun W => L (enumA B) W.1 with hf2
  have h1' : l1 ∈ Submodule.span ℝ (Set.range f1) := h1
  have h2' : l2 ∈ Submodule.span ℝ (Set.range f2) := h2
  obtain ⟨c1, hc1⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1'
  obtain ⟨c2, hc2⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h2'
  set T : Finset {W : Ultrafilter ℕ // Free W} := c1.support ∪ c2.support with hT
  have hsum1 : l1 = ∑ t ∈ T, c1 t • f1 t := by
    rw [← hc1, Finsupp.sum_of_support_subset c1 (Finset.subset_union_left) (fun i a => a • f1 i) (fun i _ => smul_zero_K _)]
  have hsum2 : l2 = ∑ t ∈ T, c2 t • f2 t := by
    rw [← hc2, Finsupp.sum_of_support_subset c2 (Finset.subset_union_right) (fun i a => a • f2 i) (fun i _ => smul_zero_K _)]
  let tt : Fin T.card → {W : Ultrafilter ℕ // Free W} := fun i => (T.equivFin.symm i).1
  let W' : Fin T.card → Ultrafilter ℕ := fun i => (tt i).1
  have hWi : Function.Injective W' := by
    intro i i' hii
    have h3 : tt i = tt i' := Subtype.ext hii
    have h4 : T.equivFin.symm i = T.equivFin.symm i' := Subtype.ext h3
    exact T.equivFin.symm.injective h4
  have hWf : ∀ i, Free (W' i) := fun i => (tt i).2
  let γ : Fin 2 → Fin T.card → ℝ := fun j i => if (j : ℕ) = 0 then c1 (tt i) else c2 (tt i)
  have hsum : ∑ j : Fin 2, ∑ i : Fin T.card, γ j i • L (ys A B j) (W' i) = l1 + l2 := by
    rw [Fin.sum_univ_two]
    have e0 : ∀ i : Fin T.card, γ 0 i • L (ys A B 0) (W' i) = c1 (tt i) • f1 (tt i) := by
      intro i; simp [γ, ys_zero, f1, W']
    have e1 : ∀ i : Fin T.card, γ 1 i • L (ys A B 1) (W' i) = c2 (tt i) • f2 (tt i) := by
      intro i; simp [γ, ys_one, f2, W']
    simp only [e0, e1]
    rw [hsum1, hsum2]
    have s1 := sum_equivFin T (fun t => c1 t • f1 t)
    have s2 := sum_equivFin T (fun t => c2 t • f2 t)
    exact congrArg₂ (· + ·) s1 s2
  have hall : ∀ j i, γ j i = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j, i, hji⟩ := hcon
    exact independence_sep (ys A B) hjoint.1 hjoint.2.1 hjoint.2.2 W' hWi hWf γ ⟨j, i, hji⟩ x (by rw [hsum, h])
  have hc1T : ∀ t ∈ T, c1 t = 0 := by
    intro t ht
    have := hall 0 (T.equivFin ⟨t, ht⟩)
    simpa [γ, tt] using this
  have hc2T : ∀ t ∈ T, c2 t = 0 := by
    intro t ht
    have := hall 1 (T.equivFin ⟨t, ht⟩)
    simpa [γ, tt] using this
  constructor
  · rw [hsum1]
    exact Finset.sum_eq_zero (fun t ht => by rw [hc1T t ht]; exact smul_zero_K _)
  · rw [hsum2]
    exact Finset.sum_eq_zero (fun t ht => by rw [hc2T t ht]; exact smul_zero_K _)

/-! ### The theorem -/

theorem join_ultra {A B : Set ℕ} (hAB : Disjoint A B) {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv)
    (hA : ∀ (F : Filter ℝ) (x : ℝ), subConv A F x → conv F x)
    (hB : ∀ (F : Filter ℝ) (x : ℝ), subConv B F x → conv F x)
    (U : Ultrafilter ℝ) (x : ℝ) (hU : subConv (A ∪ B) U x) : conv U x := by
  obtain ⟨hle, J, hJU, m, l, hJ'⟩ := hU
  have hX : (Icc (-m) m + sumSetA A l) + sumSetA B l ∈ U := by
    refine Filter.mem_of_superset hJU (fun z hz => ?_)
    obtain ⟨e0, he0, σ, hσ, rfl⟩ := hJ' hz
    obtain ⟨σA, σB, hσA, hσB, rfl⟩ := sumSetA_union_sub A B l σ hσ
    exact ⟨e0 + σA, ⟨e0, he0, σA, hσA, rfl⟩, σB, hσB, by ring⟩
  obtain ⟨V1, VB, hV1, hVB, hUle, hLr1⟩ := exists_split U hX
  obtain ⟨V0, VA, hV0, hVA, hV1le, hLr0⟩ := exists_split V1 hV1
  obtain ⟨y0, -, hy0⟩ := isCompact_Icc.ultrafilter_le_nhds V0 (Filter.le_principal_iff.2 hV0)
  have hLrV0 : Lr V0 = e y0 := Lr_eq_of_tendsto ((continuous_e.tendsto y0).comp hy0)
  have hLrU : Lr U = e x := by
    apply Lr_eq_of_tendsto
    rw [Filter.tendsto_iff_comap, ← nhds_bohr]
    exact hle
  have heq : e x = e y0 + Lr VA + Lr VB := by
    rw [← hLrU, hLr1, hLr0, hLrV0]
  -- the limits of `VA` and `VB` are in `e(ℝ)`
  have hE : (∃ yA : ℝ, Lr VA = e yA) ∧ (∃ yB : ℝ, Lr VB = e yB) := by
    by_cases hAf : A.Finite
    · obtain ⟨yA, hyA⟩ := lr_of_finite hAf l VA hVA
      refine ⟨⟨yA, hyA⟩, ?_⟩
      by_cases hBf : B.Finite
      · exact lr_of_finite hBf l VB hVB
      · refine ⟨x - y0 - yA, ?_⟩
        rw [e_sub, e_sub, ← hyA]
        rw [heq]; abel
    · have hAi : A.Infinite := hAf
      by_cases hBf : B.Finite
      · obtain ⟨yB, hyB⟩ := lr_of_finite hBf l VB hVB
        refine ⟨⟨x - y0 - yB, ?_⟩, ⟨yB, hyB⟩⟩
        rw [e_sub, e_sub, ← hyB]
        rw [heq]; abel
      · have hBi : B.Infinite := hBf
        obtain ⟨p1, hp1, l1, hl1, hpl1⟩ := Submodule.mem_sup.1 (Lr_sumSetA_mem hAi l VA hVA)
        obtain ⟨p2, hp2, l2, hl2, hpl2⟩ := Submodule.mem_sup.1 (Lr_sumSetA_mem hBi l VB hVB)
        obtain ⟨a1, rfl⟩ := hp1
        obtain ⟨a2, rfl⟩ := hp2
        have hsum : l1 + l2 = e (x - y0 - a1 - a2) := by
          rw [e_sub, e_sub, e_sub, heq, ← hpl1, ← hpl2]
          abel
        obtain ⟨h1z, h2z⟩ := lam_indep hAi hBi hAB hl1 hl2 hsum
        refine ⟨⟨a1, ?_⟩, ⟨a2, ?_⟩⟩
        · rw [← hpl1, h1z, add_zero]
        · rw [← hpl2, h2z, add_zero]
  obtain ⟨⟨yA, hyA⟩, ⟨yB, hyB⟩⟩ := hE
  have hsumy : y0 + yA + yB = x := by
    apply e_injective'
    rw [e_add, e_add, ← hyA, ← hyB, heq]
  -- convergence of the pieces
  have hconvA : subConv A VA yA := by
    refine ⟨?_, sumSetA A l, hVA, sumSetA_mem_IA A l⟩
    rw [nhds_bohr, ← Filter.tendsto_iff_comap, ← hyA]
    exact tendsto_Lr VA
  have hconvB : subConv B VB yB := by
    refine ⟨?_, sumSetA B l, hVB, sumSetA_mem_IA B l⟩
    rw [nhds_bohr, ← Filter.tendsto_iff_comap, ← hyB]
    exact tendsto_Lr VB
  have hc0 : conv V0 y0 := hA _ _ (subConv_coarser_euclid A hy0)
  have h01 := hP.add hc0 (hA _ _ hconvA)
  have h1 : conv V1 (y0 + yA) := hP.p2 h01 hV1le
  have h2 := hP.add h1 (hB _ _ hconvB)
  have h3 : conv U (y0 + yA + yB) := hP.p2 h2 hUle
  rwa [hsumy] at h3

theorem join_core {A B : Set ℕ} (hAB : Disjoint A B) {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv)
    (hA : ∀ (F : Filter ℝ) (x : ℝ), subConv A F x → conv F x)
    (hB : ∀ (F : Filter ℝ) (x : ℝ), subConv B F x → conv F x)
    (F : Filter ℝ) (x : ℝ) (hF : subConv (A ∪ B) F x) : conv F x := by
  by_cases hne : F.NeBot
  · refine hP.p3 F x (fun U hUF => join_ultra hAB hP hA hB U x ⟨hUF.trans hF.1, ?_⟩)
    obtain ⟨J, hJF, hJI⟩ := hF.2
    exact ⟨J, hUF hJF, hJI⟩
  · have hbot : F = ⊥ := Filter.not_neBot.1 hne
    subst hbot
    exact hA ⊥ x ⟨bot_le, ∅, Filter.mem_bot, (IA_isIdeal A).empty_mem⟩

/-- **Theorem 8.65.** `ξ_{A ∪ B}` is the finest PVG coarser than `ξ_A` and `ξ_B`. -/
theorem join_least {A B : Set ℕ} {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv)
    (hA : ∀ (F : Filter ℝ) (x : ℝ), subConv A F x → conv F x)
    (hB : ∀ (F : Filter ℝ) (x : ℝ), subConv B F x → conv F x)
    (F : Filter ℝ) (x : ℝ) (hF : subConv (A ∪ B) F x) : conv F x := by
  have hA' : ∀ (F : Filter ℝ) (x : ℝ), subConv (A \ B) F x → conv F x := fun F x h =>
    hA F x ⟨h.1, by
      obtain ⟨J, hJF, hJI⟩ := h.2
      exact ⟨J, hJF, IA_mono Set.diff_subset hJI⟩⟩
  have hdisj : Disjoint (A \ B) B := Set.disjoint_sdiff_left
  rw [← Set.diff_union_self] at hF
  exact join_core hdisj hP hA' hB F x hF

/-- `ξ_{A ∪ B}` is a PVG that contains `ξ_A` and `ξ_B`, and is the least such. -/
theorem subConv_union_isLeast (A B : Set ℕ) :
    IsPVG (subConv (A ∪ B)) ∧ (∀ (F : Filter ℝ) (x : ℝ), subConv A F x → subConv (A ∪ B) F x) ∧
      (∀ (F : Filter ℝ) (x : ℝ), subConv B F x → subConv (A ∪ B) F x) ∧
      ∀ conv : Filter ℝ → ℝ → Prop, IsPVG conv → (∀ F x, subConv A F x → conv F x) →
        (∀ F x, subConv B F x → conv F x) → ∀ F x, subConv (A ∪ B) F x → conv F x :=
  ⟨subConv_isPVG _,
    fun F x h => conv_sub_of_diff_finite (by rw [Set.diff_eq_empty.2 Set.subset_union_left]; exact Set.finite_empty) h,
    fun F x h => conv_sub_of_diff_finite (by rw [Set.diff_eq_empty.2 Set.subset_union_right]; exact Set.finite_empty) h,
    fun conv hP hA hB F x hF => join_least hP hA hB F x hF⟩

#print axioms lam_indep
#print axioms join_least
#print axioms subConv_union_isLeast

end Lac
end PVG
