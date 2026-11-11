import Mathlib
import LeanCheck.PVGSubTop
import LeanCheck.PVGSeqFU2
import LeanCheck.PVGSemiTop

/-!
# PVG: the topology `τ_{ξ_A}` is not first countable, not locally compact and not a Baire space (Lean check)

Scope. Propositions 8.66 and 8.70 of PVG_v30 (Addenda S1, Z3, Z5 of the research note). For `A ⊆ ℕ` infinite let `tauA A = modTop (subConv A)` be the
topological modification of `ξ_A = ξ_{τ_B, I_A}` (for `A = ℕ` this is `τ_ξ` of Theorem 7.4, with `s_n = 2^(n^2)`).

* `tauA_nhds_zero_unbounded` (Proposition 8.66 (a)): every `tauA A`-open set containing `0` contains arbitrarily large positive numbers;
* `tauA_unbounded_of_nonempty`: every nonempty `tauA A`-open set is unbounded (translation);
* `tauA_not_countablyGenerated` (Proposition 8.66 (b)): the neighbourhood filter of `0` in `tauA A` is not countably generated;
* `tauA_not_locallyCompact` (Proposition 8.70 (b)): `tauA A` is not locally compact;
* `tauA_not_baire` (Proposition 8.70 (a)): `tauA A` is not a Baire space (ℝ is the union of the closed nowhere dense sets `[-n, n]`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- The topological modification `τ_{ξ_A}` of `ξ_A`. -/
abbrev tauA (A : Set ℕ) : TopologicalSpace ℝ := modTop (subConv A)

/-! ### Bohr-open and Bohr-closed sets are `τ_A`-open and `τ_A`-closed -/

theorem bohrOpen_isOpen_tauA (A : Set ℕ) {U : Set ℝ} (hU : @IsOpen ℝ bohrTop U) : @IsOpen ℝ (tauA A) U := by
  intro x hx F hF
  exact hF.1 (@IsOpen.mem_nhds ℝ bohrTop x U hU hx)

theorem bohrClosed_isClosed_tauA (A : Set ℕ) {S : Set ℝ} (hS : @IsClosed ℝ bohrTop S) : @IsClosed ℝ (tauA A) S :=
  @isOpen_compl_iff ℝ S (tauA A) |>.1 (bohrOpen_isOpen_tauA A ((@isOpen_compl_iff ℝ S bohrTop).2 hS))

/-- Euclidean compact intervals are Bohr closed. -/
theorem Icc_bohrClosed (a b : ℝ) : @IsClosed ℝ bohrTop (Icc a b) := by
  have hc : @Continuous ℝ ℝ _ bohrTop id :=
    (@continuous_iff_continuousAt ℝ ℝ _ bohrTop id).2 (fun x => Filter.tendsto_id'.2 (bohr_coarser_euclid x))
  have hK : @IsCompact ℝ bohrTop (Icc a b) := by
    have h : @IsCompact ℝ bohrTop (id '' Icc a b) :=
      @IsCompact.image ℝ ℝ _ bohrTop (Icc a b) id isCompact_Icc hc
    rwa [image_id] at h
  exact @IsCompact.isClosed ℝ bohrTop bohr_t2 _ hK

/-! ### Proposition 8.66 (a): neighbourhoods of `0` are unbounded -/

theorem tauA_nhds_zero_unbounded {A : Set ℕ} (hA : A.Infinite) {U : Set ℝ}
    (hU : @IsOpen ℝ (tauA A) U) (h0 : (0 : ℝ) ∈ U) (R : ℝ) : ∃ x ∈ U, R < x := by
  by_contra hcon
  push Not at hcon
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  have hfin0 : {t | t ∈ Tset ∧ (1 : ℝ) * t ∈ (∅ : Set ℝ)}.Finite := by simp
  have hD : (0 : ℝ) ∈ closure (DsetA A 1 ∅) := zero_mem_closure_DA hA le_rfl hfin0
  have hDI : DsetA A 1 ∅ ∈ IA A := DsetA_mem_IA A 1 ∅
  have hopen := (mem_modTop_iff (I := IA A) U).1 hU _ hDI
  have h0nc : (0 : ℝ) ∉ closure (DsetA A 1 ∅ \ U) := fun hh => by
    have : (0 : ℝ) ∈ closure (DsetA A 1 ∅ \ U) ∩ U := ⟨hh, h0⟩
    rw [hopen] at this
    exact this
  have hsplit : DsetA A 1 ∅ = (DsetA A 1 ∅ ∩ U) ∪ (DsetA A 1 ∅ \ U) := by
    ext x; by_cases hx : x ∈ U <;> simp [hx]
  have hD' : (0 : ℝ) ∈ closure (DsetA A 1 ∅ ∩ U) := by
    rw [hsplit, closure_union] at hD
    exact hD.resolve_right h0nc
  -- `D ∩ U` is finite
  have hJ : Icc (-|R|) |R| ∈ IA ∅ := bounded_mem_IA ∅ (M := |R|) (fun a ha => abs_le.2 ⟨ha.1, ha.2⟩)
  have hfin := DsetA_inter_finite (C := A) (B := ∅) (fun n _ hn => hn) hJ
  have hsub : DsetA A 1 ∅ ∩ U ⊆ Icc (-|R|) |R| ∩ DsetA A 1 ∅ := by
    rintro x ⟨hxD, hxU⟩
    have hxpos := DsetA_pos le_rfl hxD
    have hxR := hcon x hxU
    refine ⟨⟨?_, ?_⟩, hxD⟩
    · linarith [abs_nonneg R]
    · exact hxR.trans (le_abs_self R)
  have hfin2 : (DsetA A 1 ∅ ∩ U).Finite := hfin.subset hsub
  have hcl : closure (DsetA A 1 ∅ ∩ U) = DsetA A 1 ∅ ∩ U := hfin2.isClosed.closure_eq
  rw [hcl] at hD'
  exact lt_irrefl _ (DsetA_pos le_rfl hD'.1)

/-- Every `tauA A`-neighbourhood of `0` contains arbitrarily large positive numbers. -/
theorem tauA_mem_nhds_zero_unbounded {A : Set ℕ} (hA : A.Infinite) {V : Set ℝ}
    (hV : V ∈ @nhds ℝ (tauA A) 0) (R : ℝ) : ∃ x ∈ V, R < x := by
  obtain ⟨U, hUV, hU, h0⟩ := (@mem_nhds_iff ℝ (tauA A) 0 V).1 hV
  obtain ⟨x, hx, hxR⟩ := tauA_nhds_zero_unbounded hA hU h0 R
  exact ⟨x, hUV hx, hxR⟩

/-- Every nonempty `tauA A`-open set is unbounded above. -/
theorem tauA_unbounded_of_nonempty {A : Set ℕ} (hA : A.Infinite) {U : Set ℝ}
    (hU : @IsOpen ℝ (tauA A) U) {x : ℝ} (hx : x ∈ U) (R : ℝ) : ∃ y ∈ U, R < y := by
  have hcont := modTop_continuous_add_const (subConv_isPVG A) x
  have hopen : @IsOpen ℝ (tauA A) ((fun y : ℝ => y + x) ⁻¹' U) := (@continuous_def ℝ ℝ (tauA A) (tauA A) _).1 hcont U hU
  have h0 : (0 : ℝ) ∈ (fun y : ℝ => y + x) ⁻¹' U := by simpa using hx
  obtain ⟨y, hy, hyR⟩ := tauA_nhds_zero_unbounded hA hopen h0 (R - x)
  exact ⟨y + x, hy, by linarith⟩

/-! ### Sequences with ratios at least `5` -/

theorem exists_five_seq {W : ℕ → Set ℝ} (h : ∀ j (R : ℝ), ∃ x ∈ W j, R < x) :
    ∃ z : ℕ → ℝ, (∀ j, z j ∈ W j) ∧ 0 < z 0 ∧ ∀ j, 5 * z j < z (j + 1) := by
  choose f hfW hfR using h
  refine ⟨fun j => Nat.rec (f 0 0) (fun k zk => f (k + 1) (5 * zk)) j, fun j => ?_, hfR 0 0, fun j => hfR (j + 1) _⟩
  cases j with
  | zero => exact hfW 0 0
  | succ k => exact hfW (k + 1) _

theorem five_seq_pos {z : ℕ → ℝ} (h0 : 0 < z 0) (h5 : ∀ j, 5 * z j < z (j + 1)) : ∀ j, 0 < z j := by
  intro j
  induction j with
  | zero => exact h0
  | succ k ih => have := h5 k; linarith

theorem five_seq_le {z : ℕ → ℝ} (hpos : ∀ j, 0 < z j) (h5 : ∀ j, 5 * z j < z (j + 1)) {i j : ℕ} (hij : i < j) :
    5 * z i ≤ z j := by
  induction j, Nat.succ_le_of_lt hij using Nat.le_induction with
  | base => exact (h5 i).le
  | succ k hk ih =>
    have h1 := h5 k
    have h2 := hpos k
    have h4 := ih (Nat.lt_of_succ_le hk)
    linarith

/-- Every subset of `{z_j}` is Bohr closed (Proposition 8.7, applied to subsequences). -/
theorem sub_range_bohrClosed {z : ℕ → ℝ} (hpos : ∀ j, 0 < z j) (h5 : ∀ j, 5 * z j < z (j + 1)) {S : Set ℝ}
    (hS : S ⊆ range z) : @IsClosed ℝ bohrTop S := by
  by_cases hfin : S.Finite
  · exact @Set.Finite.isClosed ℝ bohrTop (@T2Space.t1Space ℝ bohrTop bohr_t2) S hfin
  · set p : ℕ → Prop := fun j => z j ∈ S with hp
    have hinf : (setOf p).Infinite := by
      intro hT
      apply hfin
      refine (hT.image z).subset ?_
      intro x hx
      obtain ⟨j, rfl⟩ := hS hx
      exact ⟨j, hx, rfl⟩
    set g : ℕ → ℕ := Nat.nth p with hg
    have hgm : StrictMono g := Nat.nth_strictMono hinf
    have hgp : ∀ k, p (g k) := fun k => Nat.nth_mem_of_infinite hinf k
    have hrange : S = range (fun k => z (g k)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, rfl⟩ := hS hx
        have hmem : j ∈ range (Nat.nth p) := by rw [Nat.range_nth_of_infinite hinf]; exact hx
        obtain ⟨k, hk⟩ := hmem
        exact ⟨k, by show z (Nat.nth p k) = z j; rw [hk]⟩
      · rintro ⟨k, rfl⟩
        exact hgp k
    rw [hrange]
    refine lacclosed (fun k => z (g k)) (hpos _).ne' (fun k => ?_)
    show 5 * |z (g k)| ≤ |z (g (k + 1))|
    rw [abs_of_pos (hpos _), abs_of_pos (hpos _)]
    exact five_seq_le hpos h5 (hgm (Nat.lt_succ_self k))

/-! ### Generic topological lemmas -/

/-- An infinite sequence all of whose subsets are closed cannot lie in a compact set. -/
theorem infinite_closed_discrete_not_compact {X : Type*} [TopologicalSpace X] {z : ℕ → X}
    (hz : Function.Injective z) (hcl : ∀ S : Set X, S ⊆ range z → IsClosed S) {K : Set X} (hK : IsCompact K)
    (hZK : range z ⊆ K) : False := by
  have hZc : IsClosed (range z) := hcl _ subset_rfl
  have hZcomp : IsCompact (range z) := hK.of_isClosed_subset hZc hZK
  have hO : ∀ j, IsOpen ((range z \ {z j})ᶜ) := fun j => (hcl _ (fun x hx => hx.1)).isOpen_compl
  have hcov : range z ⊆ ⋃ j, (range z \ {z j})ᶜ := by
    rintro _ ⟨j, rfl⟩
    refine mem_iUnion.2 ⟨j, ?_⟩
    intro h
    exact h.2 rfl
  obtain ⟨t, ht⟩ := hZcomp.elim_finite_subcover (fun j => (range z \ {z j})ᶜ) hO hcov
  have hzm : z (t.sup id + 1) ∈ range z := ⟨_, rfl⟩
  have h1 := ht hzm
  simp only [mem_iUnion, exists_prop] at h1
  obtain ⟨i, hi, hzi⟩ := h1
  have heq : z (t.sup id + 1) = z i := by
    by_contra hne
    exact hzi ⟨hzm, hne⟩
  have hij : t.sup id + 1 = i := hz heq
  have hle : i ≤ t.sup id := Finset.le_sup (f := id) hi
  omega

/-! ### Proposition 8.66 (b): not first countable -/

theorem tauA_not_countablyGenerated {A : Set ℕ} (hA : A.Infinite) :
    ¬ (@nhds ℝ (tauA A) 0).IsCountablyGenerated := by
  intro hcg
  obtain ⟨V, hV⟩ := Filter.exists_antitone_basis (@nhds ℝ (tauA A) 0)
  have hVn : ∀ j, V j ∈ @nhds ℝ (tauA A) 0 := fun j => hV.mem j
  obtain ⟨z, hzV, hz0, hz5⟩ := exists_five_seq (W := V) (fun j R => tauA_mem_nhds_zero_unbounded hA (hVn j) R)
  have hpos := five_seq_pos hz0 hz5
  have hclosed : @IsClosed ℝ (tauA A) (range z) :=
    bohrClosed_isClosed_tauA A (sub_range_bohrClosed hpos hz5 (subset_refl _))
  have h0 : (0 : ℝ) ∉ range z := by
    rintro ⟨j, hj⟩
    exact absurd hj (hpos j).ne'
  have hmem : (range z)ᶜ ∈ @nhds ℝ (tauA A) 0 :=
    @IsOpen.mem_nhds ℝ (tauA A) _ _ (@IsClosed.isOpen_compl ℝ (tauA A) _ hclosed) h0
  obtain ⟨j, -, hj⟩ := hV.toHasBasis.mem_iff.1 hmem
  exact hj (hzV j) ⟨j, rfl⟩

/-! ### Proposition 8.70 (b): not locally compact -/

theorem tauA_not_locallyCompact {A : Set ℕ} (hA : A.Infinite) : ¬ @LocallyCompactSpace ℝ (tauA A) := by
  intro hlc
  obtain ⟨K, hKn, -, hKc⟩ := @LocallyCompactSpace.local_compact_nhds ℝ (tauA A) hlc 0 univ univ_mem
  obtain ⟨z, hzK, hz0, hz5⟩ := exists_five_seq (W := fun _ => K) (fun _ R => tauA_mem_nhds_zero_unbounded hA hKn R)
  have hpos := five_seq_pos hz0 hz5
  have hsm : StrictMono z := strictMono_nat_of_lt_succ (fun j => by have := hz5 j; have := hpos j; linarith)
  have hZK : range z ⊆ K := by rintro _ ⟨j, rfl⟩; exact hzK j
  letI : TopologicalSpace ℝ := tauA A
  exact infinite_closed_discrete_not_compact hsm.injective
    (fun S hS => bohrClosed_isClosed_tauA A (sub_range_bohrClosed hpos hz5 hS)) hKc hZK

/-! ### Proposition 8.70 (a): not a Baire space -/

theorem tauA_not_baire {A : Set ℕ} (hA : A.Infinite) : ¬ @BaireSpace ℝ (tauA A) := by
  intro hB
  have hclosed : ∀ n : ℕ, @IsClosed ℝ (tauA A) (Icc (-(n : ℝ)) n) := fun n =>
    bohrClosed_isClosed_tauA A (Icc_bohrClosed _ _)
  have hcover : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  letI : TopologicalSpace ℝ := tauA A
  haveI : BaireSpace ℝ := hB
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨y, hy, hyR⟩ := tauA_unbounded_of_nonempty hA (isOpen_interior : IsOpen (interior (Icc (-(n : ℝ)) n))) hx
    ((n : ℝ) + 1)
  have h2 := (interior_subset hy).2
  linarith

#print axioms bohrOpen_isOpen_tauA
#print axioms tauA_nhds_zero_unbounded
#print axioms tauA_unbounded_of_nonempty
#print axioms sub_range_bohrClosed
#print axioms tauA_not_countablyGenerated
#print axioms tauA_not_locallyCompact
#print axioms tauA_not_baire

end Lac
end PVG
