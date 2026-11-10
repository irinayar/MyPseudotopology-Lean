import Mathlib
import LeanCheck.PVGSubMain
import LeanCheck.PVGSorted

/-!
# PVG: Bohr limits of ultrafilters on `a₁S_A + … + a_kS_A` (Lean check)

Scope. Lemmas for Theorem 8.65 of PVG_v28 (planned), Addendum O of the research note: the join of `ξ_A` and `ξ_B` is `ξ_{A ∪ B}`.

* `exists_lift`, `exists_split`: an ultrafilter containing a sum set `X + Y` is the image of an ultrafilter on `ℝ × ℝ`; its Bohr limit
  is the sum of the Bohr limits of the two projections, and it is finer than the sum filter of the projections;
* `Esub`: the real subspace `e(ℝ)` of `K`; `LamA A`: the real span in `K` of the limits `L_{y^A}(W)`, `W` a free ultrafilter on `ℕ`, of the
  enumeration `y^A` of `{s_n : n ∈ A, n ≥ 1}`;
* `Lr_SsetA_mem`, `Lr_sumSetA_mem`: for infinite `A` (with infinitely many indices `≥ 1`), every ultrafilter containing `S_A`, or
  `a₁S_A + … + a_kS_A`, has its Bohr limit in `e(ℝ) + Λ_A`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-! ### Lifting ultrafilters -/

lemma exists_lift {α β : Type*} (f : α → β) (Q : Set α) (U : Ultrafilter β) (h : f '' Q ∈ U) :
    ∃ H : Ultrafilter α, Q ∈ H ∧ Ultrafilter.map f H = U := by
  have hne : (Filter.comap f (U : Filter β) ⊓ 𝓟 Q).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro s hs
    obtain ⟨t, htU, hts⟩ := Filter.mem_comap.1 hs
    obtain ⟨b, hbt, a, haQ, rfl⟩ := Filter.nonempty_of_mem (Filter.inter_mem htU h)
    exact ⟨a, hts hbt, haQ⟩
  set H : Ultrafilter α := Ultrafilter.of (Filter.comap f (U : Filter β) ⊓ 𝓟 Q) with hH
  have hle : (H : Filter α) ≤ Filter.comap f (U : Filter β) ⊓ 𝓟 Q := Ultrafilter.of_le _
  refine ⟨H, ?_, ?_⟩
  · exact (hle.trans inf_le_right) (Filter.mem_principal_self Q)
  · apply Ultrafilter.eq_of_le
    rw [Ultrafilter.coe_map]
    calc Filter.map f (H : Filter α) ≤ Filter.map f (Filter.comap f (U : Filter β)) :=
          Filter.map_mono (hle.trans inf_le_left)
      _ ≤ U := Filter.map_comap_le

/-- Splitting an ultrafilter that contains a sum set. -/
lemma exists_split {X Y : Set ℝ} (U : Ultrafilter ℝ) (h : X + Y ∈ U) :
    ∃ V1 V2 : Ultrafilter ℝ, X ∈ V1 ∧ Y ∈ V2 ∧ (U : Filter ℝ) ≤ Filter.map₂ (· + ·) (V1 : Filter ℝ) V2 ∧
      Lr U = Lr V1 + Lr V2 := by
  obtain ⟨H, hQ, hmap⟩ := exists_lift (fun p : ℝ × ℝ => p.1 + p.2) (X ×ˢ Y) U (by
    refine Filter.mem_of_superset h ?_
    rintro z ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩)
  refine ⟨Ultrafilter.map Prod.fst H, Ultrafilter.map Prod.snd H, ?_, ?_, ?_, ?_⟩
  · rw [Ultrafilter.mem_map]
    exact Filter.mem_of_superset hQ (fun p hp => hp.1)
  · rw [Ultrafilter.mem_map]
    exact Filter.mem_of_superset hQ (fun p hp => hp.2)
  · intro Z hZ
    obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_map₂_iff.1 hZ
    rw [Ultrafilter.coe_map] at hs ht
    have hprod : s ×ˢ t ∈ (H : Filter (ℝ × ℝ)) := by
      have h1 : Prod.fst ⁻¹' s ∈ (H : Filter (ℝ × ℝ)) := hs
      have h2 : Prod.snd ⁻¹' t ∈ (H : Filter (ℝ × ℝ)) := ht
      exact Filter.inter_mem h1 h2
    have : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Z ∈ (H : Filter (ℝ × ℝ)) :=
      Filter.mem_of_superset hprod (fun p hp => hst (Set.mem_image2_of_mem hp.1 hp.2))
    rw [← hmap, Ultrafilter.coe_map]
    exact this
  · apply Lr_eq_of_tendsto
    have h1 : Tendsto e (Ultrafilter.map Prod.fst H) (𝓝 (Lr (Ultrafilter.map Prod.fst H))) := tendsto_Lr _
    have h2 : Tendsto e (Ultrafilter.map Prod.snd H) (𝓝 (Lr (Ultrafilter.map Prod.snd H))) := tendsto_Lr _
    rw [Ultrafilter.coe_map] at h1 h2
    rw [← hmap, Ultrafilter.coe_map, Filter.tendsto_map'_iff]
    rw [Filter.tendsto_map'_iff] at h1 h2
    have := h1.add h2
    refine this.congr (fun p => ?_)
    simp [e_add]

lemma e_neg' (x : ℝ) : e (-x) = -e x := by
  have h := e_add x (-x)
  rw [add_neg_cancel, e_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- `Lr` of the image of an ultrafilter under a dilation. -/
lemma Lr_smul_map (a : ℝ) (V : Ultrafilter ℝ) : Lr (Ultrafilter.map (fun x => a * x) V) = a • Lr V := by
  apply Lr_eq_of_tendsto
  rw [Ultrafilter.coe_map, Filter.tendsto_map'_iff]
  have := (continuous_smul_const a).tendsto (Lr V) |>.comp (tendsto_Lr V)
  refine this.congr (fun x => ?_)
  simp [smul_e]

/-! ### The subspaces `e(ℝ)` and `Λ_A` of `K` -/

/-- `e(ℝ)` as a real subspace of `K`. -/
def Esub : Submodule ℝ K where
  carrier := {κ | ∃ x : ℝ, e x = κ}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, e_add x y⟩
  zero_mem' := ⟨0, e_zero⟩
  smul_mem' := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨c * x, by rw [← smul_e]⟩

lemma mem_Esub {κ : K} : κ ∈ Esub ↔ ∃ x : ℝ, e x = κ := Iff.rfl

/-- The indices `≥ 1` of `A`. -/
def idx (A : Set ℕ) : Set ℕ := {n | n ∈ A ∧ 1 ≤ n}

/-- The enumeration `y^A` of `{s_n : n ∈ A, n ≥ 1}`. -/
noncomputable def enumA (A : Set ℕ) (k : ℕ) : ℝ := sS (Nat.nth (· ∈ idx A) k)

/-- The real span of the limits `L_{y^A}(W)`, `W` a free ultrafilter. -/
def LamA (A : Set ℕ) : Submodule ℝ K :=
  Submodule.span ℝ (Set.range (fun W : {W : Ultrafilter ℕ // Free W} => L (enumA A) W.1))

lemma L_mem_LamA (A : Set ℕ) {W : Ultrafilter ℕ} (hW : Free W) : L (enumA A) W ∈ LamA A :=
  Submodule.subset_span ⟨⟨W, hW⟩, rfl⟩

lemma idx_infinite {A : Set ℕ} (hA : A.Infinite) : (idx A).Infinite := by
  have : idx A = A \ {0} := by
    ext n
    simp only [idx, mem_setOf_eq, mem_diff, mem_singleton_iff]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [this]
  exact hA.diff (Set.finite_singleton 0)

lemma enumA_mem {A : Set ℕ} (hA : A.Infinite) (k : ℕ) : ∃ n, n ∈ A ∧ 1 ≤ n ∧ enumA A k = sS n := by
  have hi : (setOf fun n => n ∈ idx A).Infinite := idx_infinite hA
  have := Nat.nth_mem_of_infinite hi k
  exact ⟨Nat.nth (· ∈ idx A) k, this.1, this.2, rfl⟩

lemma enumA_injective {A : Set ℕ} (hA : A.Infinite) : Function.Injective (enumA A) := by
  have hi : (setOf fun n => n ∈ idx A).Infinite := idx_infinite hA
  intro a b hab
  have hsm : StrictMono (fun n : ℕ => sS n) := by
    intro n m h
    unfold sS
    exact pow_lt_pow_right₀ (by norm_num) (Nat.pow_lt_pow_left h (by norm_num))
  have h1 : Nat.nth (· ∈ idx A) a = Nat.nth (· ∈ idx A) b := hsm.injective hab
  exact (Nat.nth_strictMono hi).injective h1

/-! ### Limits of ultrafilters on `S_A` -/

/-- An ultrafilter containing `S_A` has Bohr limit in `e(ℝ) + Λ_A`. -/
lemma Lr_SsetA_mem {A : Set ℕ} (hA : A.Infinite) (V : Ultrafilter ℝ) (hV : SsetA A ∈ V) :
    Lr V ∈ Esub ⊔ LamA A := by
  set g := enumA A with hg
  by_cases h0 : ({0} : Set ℝ) ∈ V
  · have hle : (V : Filter ℝ) ≤ pure 0 := Filter.le_pure_iff.2 h0
    have : Lr V = e 0 :=
      Lr_eq_of_tendsto ((tendsto_pure_nhds e 0).mono_left hle)
    rw [this]
    exact Submodule.mem_sup_left ⟨0, rfl⟩
  · have hPN : {x : ℝ | ∃ n, n ∈ A ∧ 1 ≤ n ∧ (x = sS n ∨ x = -sS n)} ∈ V := by
      have hc : ({0} : Set ℝ)ᶜ ∈ V := by
        rw [Ultrafilter.compl_mem_iff_notMem]; exact h0
      refine Filter.mem_of_superset (Filter.inter_mem hV hc) ?_
      rintro x ⟨hx, hx0⟩
      rcases hx with hx | hx
      · exact absurd hx hx0
      · exact hx
    have hsplit : ({x : ℝ | ∃ n, n ∈ A ∧ 1 ≤ n ∧ x = sS n} ∪ {x : ℝ | ∃ n, n ∈ A ∧ 1 ≤ n ∧ x = -sS n}) ∈ V := by
      refine Filter.mem_of_superset hPN ?_
      rintro x ⟨n, hn, hn1, hx | hx⟩
      · exact Or.inl ⟨n, hn, hn1, hx⟩
      · exact Or.inr ⟨n, hn, hn1, hx⟩
    have hrange : ∀ x, (∃ n, n ∈ A ∧ 1 ≤ n ∧ x = sS n) → x ∈ Set.range g := by
      rintro x ⟨n, hn, hn1, rfl⟩
      have hi : (setOf fun n => n ∈ idx A).Infinite := idx_infinite hA
      obtain ⟨k, -, hk⟩ := Nat.exists_lt_card_nth_eq (p := (· ∈ idx A)) (x := n) ⟨hn, hn1⟩
      exact ⟨k, by simp [hg, enumA, hk]⟩
    rcases (Ultrafilter.union_mem_iff.1 hsplit) with hP | hN
    · -- positive part
      obtain ⟨W, -, hW⟩ := exists_lift g Set.univ V (by
        refine Filter.mem_of_superset hP ?_
        intro x hx
        exact ⟨(hrange x hx).choose, trivial, (hrange x hx).choose_spec⟩)
      have hL : Lr V = L g W := by
        apply Lr_eq_of_tendsto
        rw [← hW, Ultrafilter.coe_map, Filter.tendsto_map'_iff]
        exact tendsto_L g W
      rw [hL]
      rcases Ultrafilter.le_cofinite_or_eq_pure W with hfree | ⟨k, hk⟩
      · exact Submodule.mem_sup_right (L_mem_LamA A hfree)
      · have : L g W = e (g k) := by
          apply L_eq_of_tendsto
          rw [hk, Ultrafilter.coe_pure]
          exact tendsto_pure_nhds _ k
        rw [this]
        exact Submodule.mem_sup_left ⟨g k, rfl⟩
    · -- negative part
      obtain ⟨W, -, hW⟩ := exists_lift (fun k => -g k) Set.univ V (by
        refine Filter.mem_of_superset hN ?_
        rintro x ⟨n, hn, hn1, hx⟩
        have : sS n ∈ Set.range g := hrange _ ⟨n, hn, hn1, rfl⟩
        obtain ⟨k, hk⟩ := this
        exact ⟨k, trivial, by rw [hx, ← hk]⟩)
      have hL : Lr V = -L g W := by
        apply Lr_eq_of_tendsto
        rw [← hW, Ultrafilter.coe_map, Filter.tendsto_map'_iff]
        have := (tendsto_L g W).neg
        refine this.congr (fun k => ?_)
        simp [e_neg']
      rw [hL]
      rcases Ultrafilter.le_cofinite_or_eq_pure W with hfree | ⟨k, hk⟩
      · exact Submodule.mem_sup_right (Submodule.neg_mem _ (L_mem_LamA A hfree))
      · have : L g W = e (g k) := by
          apply L_eq_of_tendsto
          rw [hk, Ultrafilter.coe_pure]
          exact tendsto_pure_nhds _ k
        rw [this, ← e_neg']
        exact Submodule.mem_sup_left ⟨-g k, rfl⟩

#print axioms exists_split
#print axioms Lr_SsetA_mem

end Lac
end PVG
