import LeanCheck.PVGMerged
import LeanCheck.PVGUncountable

/-!
# PVG: Theorem 8.36 with the sorted list of the terms (Lean check)

Scope. Second Lean piece for Theorem 8.36 of `PVG_v18` (independence for finitely many jointly lacunary sequences), in the
concrete setting of `PVGSequences` and `PVGIndependence` (`K = Hom(ℝ, 𝕋)`, `e`, the limits `L y U`). `PVGMerged.independence_merged`
assumes a merged sequence `z`; here the merged sequence is produced from the sorted list of all terms.

* `exists_sort`: if `f : α → β` is injective with finite initial segments `{q | f q < f p}` and `α` is infinite, then there is an
  enumeration `σ : ℕ ≃ α` with `f ∘ σ` strictly increasing (the rank of `p` is the number of smaller values);
* `independence_listing`: Theorem 8.36 with the hypothesis in the form "there is a listing `φ : ℕ ≃ Fin m × ℕ` of the terms
  `(j, k)` along which the consecutive absolute-value ratios `|y^j_k|` tend to infinity";
* `PairSep c`: for every `R` all but finitely many pairs of distinct terms have ratio at least `R` (larger over smaller);
  `listing_of_sep`: if `c > 0` has finite sublevel sets, `PairSep c` gives a listing (ties broken by an encoding of the
  index) with consecutive ratios tending to infinity;
* `independence_sep`: Theorem 8.36 for `y : Fin m → ℕ → ℝ` with nonzero terms, finite sublevel sets of `|y|` and `PairSep |y|`
  (the sorted list of the terms has consecutive ratios tending to infinity: this is the paper's hypothesis, stated pairwise).

* `JointSep`, `disjoint_span_L_family`, `prop_uncountable_family`, `exists_retraction_of_joint_family`: Proposition 8.38 and
  Corollary 8.39 for a family of base sequences every finite subfamily of which satisfies the hypothesis of Theorem 8.36;
* `exists_pre_ultra`, `lemma_separation` (Lemma 8.40): the set `B'` is built by the recursive choice `k_t`, and the merged list
  of the terms of `y` along `B` and of `y'` along `B'` is checked pairwise (`jointSep_two`, `ratio_sep`);
* `Depth`, `depth_admissible` (Proposition 8.41): sequences of finite depth, by induction on the depth, in the form with
  thinnings `c` and finite-to-one maps `σ` into `B`;
* `corollary_indepB` (Corollary 8.35): thinning a lacunary sequence to a sparse set.

Not formalized: Proposition 8.37 (finitely and countably many sequences: the orthonormal decomposition in `ℝ^m`), the
simultaneous choice in Question 9.5, and the example of Remark 8.42 (an algebraic identity, checked by hand).
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-! ### Sorting -/

/-- **Sorting by rank.** -/
lemma exists_sort {α β : Type*} [LinearOrder β] [Infinite α] (f : α → β) (hf : Function.Injective f)
    (hfin : ∀ p, {q | f q < f p}.Finite) : ∃ σ : ℕ ≃ α, StrictMono (f ∘ σ) := by
  classical
  let r : α → ℕ := fun p => ({q | f q < f p}).ncard
  have hr : ∀ p p', f p < f p' → r p < r p' := by
    intro p p' h
    apply Set.ncard_lt_ncard _ (hfin p')
    refine ⟨fun q hq => lt_trans hq h, fun hsup => ?_⟩
    have : p ∈ {q | f q < f p} := hsup h
    exact lt_irrefl _ this
  have hinj : Function.Injective r := by
    intro p p' hpp
    by_contra hne
    have hfne : f p ≠ f p' := fun h => hne (hf h)
    rcases lt_or_gt_of_ne hfne with h | h
    · exact absurd hpp (hr p p' h).ne
    · exact absurd hpp (hr p' p h).ne'
  haveI : Infinite (Set.range r) := (Set.infinite_range_of_injective hinj).to_subtype
  let e₁ : ℕ ≃o Set.range r := Nat.Subtype.orderIsoOfNat (Set.range r)
  let e₂ : α ≃ Set.range r := Equiv.ofInjective r hinj
  refine ⟨e₁.toEquiv.trans e₂.symm, ?_⟩
  have hrσ : ∀ n, r ((e₁.toEquiv.trans e₂.symm) n) = (e₁ n : ℕ) := by
    intro n
    exact Equiv.apply_ofInjective_symm hinj (e₁ n)
  intro n n' hnn'
  have h1 : (e₁ n : ℕ) < (e₁ n' : ℕ) := e₁.strictMono hnn'
  show f ((e₁.toEquiv.trans e₂.symm) n) < f ((e₁.toEquiv.trans e₂.symm) n')
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with h | h
  · have := hr _ _ h
    rw [hrσ, hrσ] at this
    omega
  · have := (e₁.toEquiv.trans e₂.symm).injective (hf h.symm)
    exact absurd this (ne_of_lt hnn')

/-! ### Theorem 8.36 for a listing of the terms -/

/-- **Theorem 8.36, listing form.** -/
theorem independence_listing {m n : ℕ} (y : Fin m → ℕ → ℝ) (hy0 : ∀ j k, y j k ≠ 0) (φ : ℕ ≃ Fin m × ℕ)
    (hlac : Tendsto (fun i => |y (φ (i + 1)).1 (φ (i + 1)).2| / |y (φ i).1 (φ i).2|) atTop atTop)
    (W : Fin n → Ultrafilter ℕ) (hWi : Function.Injective W) (hWf : ∀ l, Free (W l)) (γ : Fin m → Fin n → ℝ)
    (hγ : ∃ j l, γ j l ≠ 0) (x : ℝ) : ∑ j, ∑ l, γ j l • L (y j) (W l) ≠ e x := by
  refine independence_merged y (fun i => y (φ i).1 (φ i).2) (fun i => hy0 _ _) hlac
    (fun j k => φ.symm (j, k)) ?_ ?_ ?_ W hWi hWf γ hγ x
  · intro j a b hab
    have := φ.symm.injective hab
    exact (Prod.mk.inj this).2
  · intro j j' k k' h
    have := φ.symm.injective h
    exact (Prod.mk.inj this).1
  · intro j k
    simp

/-! ### The pairwise separation form -/

/-- For every `R`, all but finitely many pairs of distinct terms have ratio (larger over smaller) at least `R`. -/
def PairSep {α : Type*} (c : α → ℝ) : Prop :=
  ∀ R : ℝ, ∃ F : Set α, F.Finite ∧ ∀ p, p ∉ F → ∀ q, q ∉ F → p ≠ q → R * c p ≤ c q ∨ R * c q ≤ c p

/-- A positive function with finite sublevel sets and `PairSep` has a listing with consecutive ratios tending to infinity. -/
lemma listing_of_sep {α : Type*} [Encodable α] [Infinite α] (c : α → ℝ) (hc : ∀ p, 0 < c p)
    (hfin : ∀ t, {p | c p ≤ t}.Finite) (hsep : PairSep c) :
    ∃ σ : ℕ ≃ α, Tendsto (fun i => c (σ (i + 1)) / c (σ i)) atTop atTop := by
  classical
  let f : α → ℝ ×ₗ ℕ := fun p => toLex (c p, Encodable.encode p)
  have hf : Function.Injective f := by
    intro p q h
    have := toLex_inj.mp h
    exact Encodable.encode_injective (Prod.mk.inj this).2
  have hfin' : ∀ p, {q | f q < f p}.Finite := by
    intro p
    refine (hfin (c p)).subset ?_
    intro q hq
    have hq' : f q < f p := hq
    simp only [f, Prod.Lex.toLex_lt_toLex] at hq'
    rcases hq' with h | h
    · exact h.le
    · exact h.1.le
  obtain ⟨σ, hσ⟩ := exists_sort f hf hfin'
  have hmono : ∀ i j, i < j → c (σ i) ≤ c (σ j) := by
    intro i j hij
    have := hσ hij
    simp only [Function.comp, f, Prod.Lex.toLex_lt_toLex] at this
    rcases this with h | h
    · exact h.le
    · exact h.1.le
  refine ⟨σ, ?_⟩
  rw [tendsto_atTop]
  intro R
  obtain ⟨F, hF, hFsep⟩ := hsep (max R 2)
  have hpre : (σ ⁻¹' F).Finite := hF.preimage σ.injective.injOn
  have hev : ∀ᶠ i in atTop, i ∉ σ ⁻¹' F := by
    rw [← Nat.cofinite_eq_atTop]
    exact hpre.eventually_cofinite_notMem
  filter_upwards [hev, (tendsto_add_atTop_nat 1).eventually hev] with i hi hi1
  have hne : σ i ≠ σ (i + 1) := fun h => by have := σ.injective h; omega
  have hci := hc (σ i)
  have hci1 := hc (σ (i + 1))
  have hle := hmono i (i + 1) (by omega)
  rw [le_div_iff₀ hci]
  rcases hFsep (σ i) hi (σ (i + 1)) hi1 hne with h | h
  · calc R * c (σ i) ≤ max R 2 * c (σ i) := mul_le_mul_of_nonneg_right (le_max_left _ _) hci.le
      _ ≤ c (σ (i + 1)) := h
  · exfalso
    have h2 : 2 * c (σ (i + 1)) ≤ max R 2 * c (σ (i + 1)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hci1.le
    linarith

/-- **Theorem 8.36 in the pairwise form** (the sorted list of the terms has consecutive ratios tending to infinity). -/
theorem independence_sep {m n : ℕ} (y : Fin m → ℕ → ℝ) (hy0 : ∀ j k, y j k ≠ 0)
    (hfin : ∀ t, {p : Fin m × ℕ | |y p.1 p.2| ≤ t}.Finite) (hsep : PairSep (fun p : Fin m × ℕ => |y p.1 p.2|))
    (W : Fin n → Ultrafilter ℕ) (hWi : Function.Injective W) (hWf : ∀ l, Free (W l)) (γ : Fin m → Fin n → ℝ)
    (hγ : ∃ j l, γ j l ≠ 0) (x : ℝ) : ∑ j, ∑ l, γ j l • L (y j) (W l) ≠ e x := by
  obtain ⟨j0, _, _⟩ := id hγ
  haveI : Nonempty (Fin m) := ⟨j0⟩
  haveI : Infinite (Fin m × ℕ) := Infinite.of_injective (fun k : ℕ => (j0, k)) (fun a b h => (Prod.mk.inj h).2)
  obtain ⟨σ, hσ⟩ := listing_of_sep (fun p : Fin m × ℕ => |y p.1 p.2|) (fun p => abs_pos.mpr (hy0 _ _)) hfin hsep
  exact independence_listing y hy0 σ hσ W hWi hWf γ hγ x

/-! ### A family of jointly lacunary base sequences -/

/-- `y 0, …, y (m-1)` satisfy the hypothesis of Theorem 8.36: nonzero terms, finitely many terms below any bound, and the sorted
list of the terms has consecutive ratios tending to infinity (stated pairwise). -/
def JointSep {m : ℕ} (y : Fin m → ℕ → ℝ) : Prop :=
  (∀ j k, y j k ≠ 0) ∧ (∀ t, {p : Fin m × ℕ | |y p.1 p.2| ≤ t}.Finite) ∧
    PairSep (fun p : Fin m × ℕ => |y p.1 p.2|)

lemma sum_equivFin {α M : Type*} [AddCommMonoid M] (s : Finset α) (h : α → M) :
    ∑ a : Fin s.card, h (s.equivFin.symm a).1 = ∑ x ∈ s, h x := by
  rw [Equiv.sum_comp s.equivFin.symm (fun x : s => h x.1)]
  exact Finset.sum_coe_sort s h

/-- **The limits along free ultrafilters of a family of base sequences, every finite subfamily of which is jointly lacunary,
span a subspace meeting `ℝ e(1)` only in `0`** (the hypothesis `hind` of `prop_uncountable_gen`). -/
theorem disjoint_span_L_family {I : Type*} (y0 : I → ℕ → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin m → I), Function.Injective i → JointSep (fun j => y0 (i j))) :
    Disjoint (Submodule.span ℝ {v : K | ∃ (i : I) (U : Ultrafilter ℕ), Free U ∧ v = L (y0 i) U}) (ℝ ∙ e 1) := by
  classical
  rw [Submodule.disjoint_def]
  intro x hx hx1
  have hx' : x ∈ Submodule.span ℝ
      (Set.range (fun p : {p : I × Ultrafilter ℕ // Free p.2} => L (y0 p.1.1) p.1.2)) := by
    refine Submodule.span_mono ?_ hx
    rintro v ⟨i, U, hU, rfl⟩
    exact ⟨⟨(i, U), hU⟩, rfl⟩
  obtain ⟨g, hg⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx'
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx1
  have hxe : x = e b := by rw [← hb, e_eq_smul b]
  obtain ⟨G, hG⟩ : ∃ G : I × Ultrafilter ℕ → ℝ, ∀ q, G q = if h : Free q.2 then g ⟨q, h⟩ else 0 :=
    ⟨fun q => if h : Free q.2 then g ⟨q, h⟩ else 0, fun q => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (I × Ultrafilter ℕ),
      S = g.support.map (Function.Embedding.subtype (fun p : I × Ultrafilter ℕ => Free p.2)) := ⟨_, rfl⟩
  have hSfree : ∀ q ∈ S, Free q.2 := by
    intro q hq
    rw [hS] at hq
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hq
    exact u.2
  have hGoff : ∀ q, q ∉ S → G q = 0 := by
    intro q hq
    by_cases h : Free q.2
    · rw [hG q, dif_pos h]
      by_contra hne
      exact hq (hS ▸ Finset.mem_map.2 ⟨⟨q, h⟩, Finsupp.mem_support_iff.2 hne, rfl⟩)
    · rw [hG q, dif_neg h]
  have hGS : ∀ u : {p : I × Ultrafilter ℕ // Free p.2}, G u.1 = g u := by
    intro u
    rw [hG, dif_pos u.2]
  have hsum : ∑ q ∈ S, G q • L (y0 q.1) q.2 = e b := by
    rw [hS, Finset.sum_map, ← hxe, ← hg, Finsupp.sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Function.Embedding.subtype_apply]
    rw [hGS u]
  set Jset : Finset I := S.image Prod.fst with hJ
  set Wset : Finset (Ultrafilter ℕ) := S.image Prod.snd with hW
  let iJ : Fin Jset.card → I := fun a => (Jset.equivFin.symm a).1
  let Wf : Fin Wset.card → Ultrafilter ℕ := fun a => (Wset.equivFin.symm a).1
  have hiJ : Function.Injective iJ := fun a a' h => Jset.equivFin.symm.injective (Subtype.ext h)
  have hWi : Function.Injective Wf := fun a a' h => Wset.equivFin.symm.injective (Subtype.ext h)
  have hWfree : ∀ l, Free (Wf l) := by
    intro l
    obtain ⟨q, hq, hq2⟩ := Finset.mem_image.1 (Wset.equivFin.symm l).2
    have : Wf l = q.2 := hq2.symm
    rw [this]
    exact hSfree q hq
  have hconv : ∑ j : Fin Jset.card, ∑ l : Fin Wset.card, G (iJ j, Wf l) • L (y0 (iJ j)) (Wf l) =
      ∑ q ∈ S, G q • L (y0 q.1) q.2 := by
    have h1 : ∑ j : Fin Jset.card, ∑ l : Fin Wset.card, G (iJ j, Wf l) • L (y0 (iJ j)) (Wf l) =
        ∑ a ∈ Jset, ∑ w ∈ Wset, G (a, w) • L (y0 a) w := by
      rw [← sum_equivFin Jset (fun a => ∑ w ∈ Wset, G (a, w) • L (y0 a) w)]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact sum_equivFin Wset (fun w => G (iJ j, w) • L (y0 (iJ j)) w)
    have h2 : ∑ a ∈ Jset, ∑ w ∈ Wset, G (a, w) • L (y0 a) w =
        ∑ q ∈ Jset ×ˢ Wset, G q • L (y0 q.1) q.2 := by rw [Finset.sum_product]
    have hsub : S ⊆ Jset ×ˢ Wset := by
      intro q hq
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
    have h3 : ∑ q ∈ S, G q • L (y0 q.1) q.2 = ∑ q ∈ Jset ×ˢ Wset, G q • L (y0 q.1) q.2 :=
      Finset.sum_subset hsub (fun q _ hq => by rw [hGoff q hq]; exact zero_smul ℝ (L (y0 q.1) q.2))
    rw [h1, h2, ← h3]
  have hall : ∀ q ∈ S, G q = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q0, hq0, hne⟩ := hcon
    have hj0 : q0.1 ∈ Jset := Finset.mem_image_of_mem _ hq0
    have hl0 : q0.2 ∈ Wset := Finset.mem_image_of_mem _ hq0
    refine independence_sep (fun j => y0 (iJ j)) (hfam _ iJ hiJ).1 (hfam _ iJ hiJ).2.1 (hfam _ iJ hiJ).2.2 Wf hWi hWfree
      (fun j l => G (iJ j, Wf l)) ⟨Jset.equivFin ⟨q0.1, hj0⟩, Wset.equivFin ⟨q0.2, hl0⟩, ?_⟩ b ?_
    · simp only [iJ, Wf, Equiv.symm_apply_apply]
      exact hne
    · rw [hconv, hsum]
  have hg0 : g = 0 := by
    ext u
    by_cases hu : u ∈ g.support
    · have h1 : u.1 ∈ S := hS ▸ Finset.mem_map.2 ⟨u, hu, rfl⟩
      have := hall u.1 h1
      rw [hGS u] at this
      simpa using this
    · simpa using Finsupp.notMem_support_iff.1 hu
  rw [← hg, hg0]
  simp

/-- **Proposition 8.38 for a family of jointly lacunary base sequences.** -/
theorem prop_uncountable_family {I ι : Type*} (y0 : I → ℕ → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin m → I), Function.Injective i → JointSep (fun j => y0 (i j)))
    (m : ι → ℕ) (c : (i : ι) → Fin (m i) → I) (r : (i : ι) → Fin (m i) → ℝ)
    (σ : (i : ι) → Fin (m i) → ℕ → ℕ) (hσ : ∀ i j, FiniteToOne (σ i j))
    (z : ι → ℕ → ℝ) (a : ι → ℝ) (B : ι → Set ℕ)
    (hz : ∀ i, ∀ ε > 0, ∃ N, ∀ k ∈ B i, N ≤ k → |z i k - a i| < ε) (yy : ι → ℕ → ℝ)
    (hyy : ∀ i k, yy i k = ∑ j, r i j * y0 (c i j) (σ i j k) + z i k) :
    Disjoint (Submodule.span ℝ {v : K | ∃ i, ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ B i ∈ U ∧ B i ∈ V ∧
      v = L (yy i) U - L (yy i) V}) (ℝ ∙ e 1) :=
  prop_uncountable_gen y0 (disjoint_span_L_family y0 hfam) m c r σ hσ z a B hz yy hyy

/-- **Corollary 8.39 for a family of jointly lacunary base sequences.** -/
theorem exists_retraction_of_joint_family {I ι : Type*} (y0 : I → ℕ → ℝ)
    (hfam : ∀ (m : ℕ) (i : Fin m → I), Function.Injective i → JointSep (fun j => y0 (i j)))
    (m : ι → ℕ) (c : (i : ι) → Fin (m i) → I) (r : (i : ι) → Fin (m i) → ℝ)
    (σ : (i : ι) → Fin (m i) → ℕ → ℕ) (hσ : ∀ i j, FiniteToOne (σ i j))
    (z : ι → ℕ → ℝ) (a : ι → ℝ) (B : ι → Set ℕ) (hBinf : ∀ i, (B i).Infinite)
    (hz : ∀ i, ∀ ε > 0, ∃ N, ∀ k ∈ B i, N ≤ k → |z i k - a i| < ε) (y : ι → ℕ → ℝ)
    (hy : ∀ i k, y i k = ∑ j, r i j * y0 (c i j) (σ i j k) + z i k) :
    ∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ ∀ i, SC π (y i) :=
  exists_retraction_of_family y0 (disjoint_span_L_family y0 hfam) m c r σ hσ z a B hBinf hz y hy

/-! ### Lemma 8.40 (separation) -/

lemma jointSep_comp {m m' : ℕ} {Y : Fin m → ℕ → ℝ} (h : JointSep Y) (i : Fin m' → Fin m)
    (hi : Function.Injective i) : JointSep (fun j => Y (i j)) := by
  have hinj : Function.Injective (Prod.map i (id : ℕ → ℕ)) := hi.prodMap Function.injective_id
  refine ⟨fun j k => h.1 _ _, fun t => ?_, fun R => ?_⟩
  · refine ((h.2.1 t).preimage hinj.injOn).subset ?_
    intro p hp
    exact hp
  · obtain ⟨F, hF, hFs⟩ := h.2.2 R
    refine ⟨Prod.map i id ⁻¹' F, hF.preimage hinj.injOn, fun p hp q hq hpq => ?_⟩
    exact hFs _ hp _ hq (fun h' => hpq (hinj h'))

/-- Sparse sequences: if the ratios eventually exceed every bound, then all later terms exceed `R` times an earlier one. -/
lemma ratio_sep (f : ℕ → ℝ) (hf : ∀ t, 0 < f t) (hr : ∀ R : ℝ, ∃ N, ∀ t, N ≤ t → R * f t ≤ f (t + 1)) (R : ℝ) :
    ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * f s ≤ f t := by
  obtain ⟨N, hN⟩ := hr (max R 1)
  refine ⟨N, fun s hs t hst => ?_⟩
  induction t, hst using Nat.le_induction with
  | base => exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hf s).le) (hN s hs)
  | succ t hst ih =>
    have h1 := hN t (by omega)
    have h2 : f t ≤ max R 1 * f t := by
      have := mul_le_mul_of_nonneg_right (le_max_right R 1) (hf t).le
      linarith
    linarith

lemma sublevel_finite (w : ℕ → ℝ) (hw0 : ∀ t, w t ≠ 0)
    (hw : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * |w s| ≤ |w t|) (T : ℝ) : {t | |w t| ≤ T}.Finite := by
  obtain ⟨N1, hN1⟩ := hw 1
  have hpos : 0 < |w N1| := abs_pos.mpr (hw0 N1)
  obtain ⟨N2, hN2⟩ := hw ((|T| + 1) / |w N1|)
  refine (Set.finite_Iic (max N1 N2)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  simp only [Set.mem_Iic]
  by_contra hlt
  push Not at hlt
  have hs : N2 ≤ max N1 N2 := le_max_right _ _
  have h1 := hN2 (max N1 N2) hs t hlt
  have h2 : |w N1| ≤ |w (max N1 N2)| := by
    rcases (le_max_left N1 N2).eq_or_lt with h | h
    · rw [← h]
    · have := hN1 N1 le_rfl _ h
      linarith
  have h3 : |T| + 1 ≤ (|T| + 1) / |w N1| * |w (max N1 N2)| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have := le_abs_self T
  linarith

lemma jointSep_two (u v : ℕ → ℝ) (hu0 : ∀ t, u t ≠ 0) (hv0 : ∀ t, v t ≠ 0)
    (hu : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * |u s| ≤ |u t|)
    (hv : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * |v s| ≤ |v t|)
    (hc : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, N ≤ t → R * |u s| ≤ |v t| ∨ R * |v t| ≤ |u s|) :
    JointSep ![u, v] := by
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    fin_cases j
    · exact hu0 k
    · exact hv0 k
  · intro T
    have hA := sublevel_finite u hu0 hu T
    have hB := sublevel_finite v hv0 hv T
    refine ((hA.image (fun s => ((0 : Fin 2), s))).union (hB.image (fun s => ((1 : Fin 2), s)))).subset ?_
    rintro ⟨j, s⟩ hp
    fin_cases j
    · left; exact ⟨s, hp, rfl⟩
    · right; exact ⟨s, hp, rfl⟩
  · intro R
    obtain ⟨Nu, hNu⟩ := hu R
    obtain ⟨Nv, hNv⟩ := hv R
    obtain ⟨Nc, hNc⟩ := hc R
    refine ⟨{p : Fin 2 × ℕ | p.2 < max (max Nu Nv) Nc}, ?_, ?_⟩
    · exact (Set.finite_univ.prod (Set.finite_Iio (max (max Nu Nv) Nc))).subset (fun p hp => ⟨Set.mem_univ _, hp⟩)
    · rintro ⟨j, s⟩ hp ⟨j', t⟩ hq hne
      have hs : max (max Nu Nv) Nc ≤ s := by simpa using hp
      have ht : max (max Nu Nv) Nc ≤ t := by simpa using hq
      have h1 : Nu ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
      have h2 : Nv ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
      have h3 : Nc ≤ s := le_trans (le_max_right _ _) hs
      have h1' : Nu ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
      have h2' : Nv ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
      have h3' : Nc ≤ t := le_trans (le_max_right _ _) ht
      fin_cases j <;> fin_cases j'
      · have hst : s ≠ t := fun h => hne (by rw [h])
        rcases lt_or_gt_of_ne hst with h | h
        · left; exact hNu s h1 t h
        · right; exact hNu t h1' s h
      · exact hNc s h3 t h3'
      · rcases hNc t h3' s h3 with h | h
        · right; exact h
        · left; exact h
      · have hst : s ≠ t := fun h => hne (by rw [h])
        rcases lt_or_gt_of_ne hst with h | h
        · left; exact hNv s h2 t h
        · right; exact hNv t h2' s h

lemma exists_pre_ultra {b : ℕ → ℕ} (hb : Function.Injective b) {U : Ultrafilter ℕ} (hU : Free U)
    (hr : Set.range b ∈ U) : ∃ W : Ultrafilter ℕ, Free W ∧ U = W.map b := by
  refine ⟨U.comap hb hr, ?_, ?_⟩
  · intro s hs
    rw [Ultrafilter.mem_coe, Ultrafilter.mem_comap]
    have hfin : sᶜ.Finite := Filter.mem_cofinite.mp hs
    have hc : (b '' sᶜ)ᶜ ∈ U := hU (Filter.mem_cofinite.mpr (by rw [compl_compl]; exact hfin.image b))
    refine Filter.mem_of_superset (Filter.inter_mem hr hc) ?_
    rintro x ⟨⟨a, rfl⟩, hxc⟩
    refine ⟨a, ?_, rfl⟩
    by_contra has
    exact hxc ⟨a, has, rfl⟩
  · apply Ultrafilter.coe_injective
    ext s
    rw [Ultrafilter.mem_coe, Ultrafilter.coe_map, Filter.mem_map]
    show s ∈ U ↔ b ⁻¹' s ∈ U.comap hb hr
    rw [Ultrafilter.mem_comap, Set.image_preimage_eq_inter_range]
    exact ⟨fun h => Filter.inter_mem h hr, fun h => Filter.mem_of_superset h Set.inter_subset_left⟩

/-- **Lemma 8.40 (separation).** `b` enumerates the infinite set `B` (consecutive ratios of `y` along `B` tend to infinity);
`y'` tends to infinity in absolute value and for every `C > 1` infinitely many terms of `y'` lie outside all windows
`[|y_j|/C, C|y_j|]`, `j ∈ B`. Then there is an infinite `B'` such that the real span of the differences of the limits of `y`
along `B*` and of `y'` along `B'*` meets `ℝ e(1)` only in `0`. -/
theorem lemma_separation (y y' : ℕ → ℝ) (hy0 : ∀ k, y k ≠ 0) (b : ℕ → ℕ) (hb : StrictMono b)
    (hratio : Tendsto (fun t => |y (b (t + 1))| / |y (b t)|) atTop atTop)
    (hy' : Tendsto (fun k => |y' k|) atTop atTop)
    (hwin : ∀ C : ℝ, 1 < C →
      {k | ∀ t, ¬ (|y (b t)| / C ≤ |y' k| ∧ |y' k| ≤ C * |y (b t)|)}.Infinite) :
    ∃ B' : Set ℕ, B'.Infinite ∧ Disjoint (Submodule.span ℝ
      ({v : K | ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ Set.range b ∈ U ∧ Set.range b ∈ V ∧
          v = L y U - L y V} ∪
       {v : K | ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ B' ∈ U ∧ B' ∈ V ∧ v = L y' U - L y' V})) (ℝ ∙ e 1) := by
  classical
  have hstep : ∀ (t : ℕ) (k0 : ℕ), ∃ k, k0 < k ∧
      (∀ j, ¬ (|y (b j)| / ((t : ℝ) + 3) ≤ |y' k| ∧ |y' k| ≤ ((t : ℝ) + 3) * |y (b j)|)) ∧
      y' k ≠ 0 ∧ ((t : ℝ) + 1) * |y' k0| ≤ |y' k| := by
    intro t k0
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hinf := hwin ((t : ℝ) + 3) (by linarith)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hy' (((t : ℝ) + 1) * |y' k0| + 1))
    obtain ⟨k, hk, hkgt⟩ := hinf.exists_gt (max k0 N)
    have hkN : ((t : ℝ) + 1) * |y' k0| + 1 ≤ |y' k| := hN k (le_trans (le_max_right _ _) hkgt.le)
    have h0 : 0 ≤ ((t : ℝ) + 1) * |y' k0| := by positivity
    refine ⟨k, lt_of_le_of_lt (le_max_left _ _) hkgt, hk, ?_, by linarith⟩
    intro h
    have : |y' k| = 0 := by simpa using h
    linarith
  choose f hf using hstep
  obtain ⟨kk, hkk0, hkkS⟩ : ∃ kk : ℕ → ℕ, kk 0 = f 0 0 ∧ ∀ t, kk (t + 1) = f (t + 1) (kk t) :=
    ⟨fun t => Nat.rec (f 0 0) (fun t kt => f (t + 1) kt) t, rfl, fun t => rfl⟩
  have hwinK : ∀ (t : ℕ) (j : ℕ), ¬ (|y (b j)| / ((t : ℝ) + 3) ≤ |y' (kk t)| ∧ |y' (kk t)| ≤ ((t : ℝ) + 3) * |y (b j)|) := by
    intro t j
    cases t with
    | zero => rw [hkk0]; exact (hf 0 0).2.1 j
    | succ t => rw [hkkS]; exact (hf (t + 1) (kk t)).2.1 j
  have hne0 : ∀ t, y' (kk t) ≠ 0 := by
    intro t
    cases t with
    | zero => rw [hkk0]; exact (hf 0 0).2.2.1
    | succ t => rw [hkkS]; exact (hf (t + 1) (kk t)).2.2.1
  have hgrow : ∀ t : ℕ, ((t : ℝ) + 2) * |y' (kk t)| ≤ |y' (kk (t + 1))| := by
    intro t
    rw [hkkS]
    have := (hf (t + 1) (kk t)).2.2.2
    push_cast at this
    linarith
  have hmono : ∀ t, kk t < kk (t + 1) := by
    intro t
    rw [hkkS]
    exact (hf (t + 1) (kk t)).1
  have kStrict : StrictMono kk := strictMono_nat_of_lt_succ hmono
  set u : ℕ → ℝ := fun t => y (b t) with hu_def
  set v : ℕ → ℝ := fun t => y' (kk t) with hv_def
  have hu0 : ∀ t, u t ≠ 0 := fun t => hy0 _
  have hv0 : ∀ t, v t ≠ 0 := fun t => hne0 t
  have hupos : ∀ t, 0 < |u t| := fun t => abs_pos.mpr (hu0 t)
  have hvpos : ∀ t, 0 < |v t| := fun t => abs_pos.mpr (hv0 t)
  have hu : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * |u s| ≤ |u t| := by
    intro R
    refine ratio_sep (fun t => |u t|) hupos (fun R' => ?_) R
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hratio R')
    refine ⟨N, fun t ht => ?_⟩
    have := hN t ht
    rwa [le_div_iff₀ (hupos t)] at this
  have hv : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, s < t → R * |v s| ≤ |v t| := by
    intro R
    refine ratio_sep (fun t => |v t|) hvpos (fun R' => ?_) R
    refine ⟨⌈R'⌉₊, fun t ht => ?_⟩
    have h1 : R' ≤ (t : ℝ) := le_trans (Nat.le_ceil R') (by exact_mod_cast ht)
    have h2 := hgrow t
    have h3 : R' * |v t| ≤ ((t : ℝ) + 2) * |v t| := mul_le_mul_of_nonneg_right (by linarith) (hvpos t).le
    exact le_trans h3 h2
  have hc : ∀ R : ℝ, ∃ N, ∀ s, N ≤ s → ∀ t, N ≤ t → R * |u s| ≤ |v t| ∨ R * |v t| ≤ |u s| := by
    intro R
    refine ⟨⌈R⌉₊, fun s _ t ht => ?_⟩
    have h1 : R ≤ (t : ℝ) + 3 := by
      have : R ≤ (t : ℝ) := le_trans (Nat.le_ceil R) (by exact_mod_cast ht)
      linarith
    have ht3 : (0 : ℝ) < (t : ℝ) + 3 := by positivity
    have hw := hwinK t s
    rw [not_and_or, not_le, not_le] at hw
    rcases hw with h | h
    · right
      rw [lt_div_iff₀ ht3] at h
      have : R * |v t| ≤ ((t : ℝ) + 3) * |v t| := mul_le_mul_of_nonneg_right h1 (hvpos t).le
      show R * |y' (kk t)| ≤ |y (b s)|
      linarith
    · left
      have : R * |u s| ≤ ((t : ℝ) + 3) * |u s| := mul_le_mul_of_nonneg_right h1 (hupos s).le
      show R * |y (b s)| ≤ |y' (kk t)|
      linarith
  have hJ : JointSep ![u, v] := jointSep_two u v hu0 hv0 hu hv hc
  have hdis := disjoint_span_L_family (![u, v] : Fin 2 → ℕ → ℝ) (fun m i hi => jointSep_comp hJ i hi)
  refine ⟨Set.range kk, Set.infinite_range_of_injective kStrict.injective, hdis.mono_left ?_⟩
  apply Submodule.span_le.2
  rintro w (⟨U, V, hU, hV, hbU, hbV, rfl⟩ | ⟨U, V, hU, hV, hkU, hkV, rfl⟩)
  · obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra hb.injective hU hbU
    obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra hb.injective hV hbV
    rw [← L_comp y b WU, ← L_comp y b WV]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, WU, hWU, rfl⟩) (Submodule.subset_span ⟨0, WV, hWV, rfl⟩)
  · obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra kStrict.injective hU hkU
    obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra kStrict.injective hV hkV
    rw [← L_comp y' kk WU, ← L_comp y' kk WV]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨1, WU, hWU, rfl⟩) (Submodule.subset_span ⟨1, WV, hWV, rfl⟩)

/-! ### Proposition 8.41 (sequences of finite depth) -/

/-- The generators `L y U - L y V`, `U, V` free containing the infinite set `B`. -/
def Gen (y : ℕ → ℝ) (B : Set ℕ) : Set K :=
  {v : K | ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ B ∈ U ∧ B ∈ V ∧ v = L y U - L y V}

lemma L_of_tendsto {f : ℕ → ℝ} {a : ℝ} (hf : Tendsto f atTop (𝓝 a)) {W : Ultrafilter ℕ} (hW : Free W) :
    L f W = e a := by
  apply L_eq_of_tendsto
  have h1 : Tendsto f (W : Filter ℕ) (𝓝 a) :=
    hf.mono_left (by rw [← Nat.cofinite_eq_atTop]; exact hW)
  exact (continuous_e.tendsto a).comp h1

/-- The generators of the base sequence along `range b` lie in the span of the limits of `y ∘ b`. -/
lemma genY_subset {y : ℕ → ℝ} {b : ℕ → ℕ} (hb : Function.Injective b) :
    Gen y (Set.range b) ⊆
      (Submodule.span ℝ {v : K | ∃ (_ : Unit) (U : Ultrafilter ℕ), Free U ∧ v = L (fun t => y (b t)) U} : Set K) := by
  rintro w ⟨U, V, hU, hV, hbU, hbV, rfl⟩
  obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra hb hU hbU
  obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra hb hV hbV
  rw [← L_comp y b WU, ← L_comp y b WV]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨(), WU, hWU, rfl⟩) (Submodule.subset_span ⟨(), WV, hWV, rfl⟩)

/-- The classes of Proposition 8.41 (after thinning): depth `0` is a bounded sequence or a sequence satisfying the hypothesis of
Lemma 8.40; a sequence has depth `d + 1` if after a thinning `c` and the subtraction of `r · (y ∘ σ)` with `σ` finite-to-one
into `B = range b` it has depth `d`. -/
inductive Depth (y : ℕ → ℝ) (b : ℕ → ℕ) : ℕ → (ℕ → ℝ) → Prop
  | bounded (ρ : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |ρ k| ≤ M) : Depth y b 0 ρ
  | sep (ρ : ℕ → ℝ) (hρ : Tendsto (fun k => |ρ k|) atTop atTop)
      (hwin : ∀ C : ℝ, 1 < C →
        {k | ∀ t, ¬ (|y (b t)| / C ≤ |ρ k| ∧ |ρ k| ≤ C * |y (b t)|)}.Infinite) : Depth y b 0 ρ
  | step (d : ℕ) (ρ : ℕ → ℝ) (c : ℕ → ℕ) (hc : StrictMono c) (σ : ℕ → ℕ) (hσ : FiniteToOne σ)
      (hσB : ∀ k, σ k ∈ Set.range b) (r : ℝ)
      (h : Depth y b d (fun k => ρ (c k) - r * y (σ k))) : Depth y b (d + 1) ρ

/-- **Proposition 8.41.** A sequence of finite depth over `(y, B)` admits an infinite `B'` such that the real span of the
differences of the limits of `y` along `B*` and of `ρ` along `B'*` meets `ℝ e(1)` only in `0`. -/
theorem depth_admissible (y : ℕ → ℝ) (hy0 : ∀ k, y k ≠ 0) (b : ℕ → ℕ) (hb : StrictMono b)
    (hratio : Tendsto (fun t => |y (b (t + 1))| / |y (b t)|) atTop atTop) :
    ∀ (d : ℕ) (ρ : ℕ → ℝ), Depth y b d ρ → ∃ B' : Set ℕ, B'.Infinite ∧
      Disjoint (Submodule.span ℝ (Gen y (Set.range b) ∪ Gen ρ B')) (ℝ ∙ e 1) := by
  have hdisY : Disjoint (Submodule.span ℝ (Gen y (Set.range b))) (ℝ ∙ e 1) := by
    refine (disjoint_span_L (fun t => y (b t)) (fun t => hy0 _) hratio).mono_left ?_
    exact Submodule.span_le.2 (genY_subset hb.injective)
  intro d ρ hD
  induction hD with
  | bounded ρ M hM =>
    obtain ⟨a, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-M) M)
      (x := ρ) (fun k => by simpa [abs_le] using (abs_le.mp (hM k)))
    refine ⟨Set.range φ, Set.infinite_range_of_injective hφ.injective, hdisY.mono_left ?_⟩
    refine Submodule.span_le.2 (Set.union_subset Submodule.subset_span ?_)
    rintro w ⟨U, V, hU, hV, hbU, hbV, rfl⟩
    obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra hφ.injective hU hbU
    obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra hφ.injective hV hbV
    rw [← L_comp ρ φ WU, ← L_comp ρ φ WV, L_of_tendsto (f := fun k => ρ (φ k)) hlim hWU, L_of_tendsto (f := fun k => ρ (φ k)) hlim hWV, sub_self]
    exact Submodule.zero_mem _
  | sep ρ hρ hwin =>
    obtain ⟨B', hB', hdis⟩ := lemma_separation y ρ hy0 b hb hratio hρ hwin
    exact ⟨B', hB', hdis⟩
  | step d ρ c hc σ hσ hσB r h ih =>
    obtain ⟨B₁, hB₁, hdis⟩ := ih
    refine ⟨c '' B₁, hB₁.image hc.injective.injOn, hdis.mono_left ?_⟩
    refine Submodule.span_le.2 (Set.union_subset (fun w hw => Submodule.subset_span (Or.inl hw)) ?_)
    rintro w ⟨U, V, hU, hV, hbU, hbV, rfl⟩
    have hrU : Set.range c ∈ U := Filter.mem_of_superset hbU (Set.image_subset_range _ _)
    have hrV : Set.range c ∈ V := Filter.mem_of_superset hbV (Set.image_subset_range _ _)
    obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra hc.injective hU hrU
    obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra hc.injective hV hrV
    have hB₁U : B₁ ∈ WU := by
      rw [Ultrafilter.mem_map] at hbU
      rwa [Set.preimage_image_eq _ hc.injective] at hbU
    have hB₁V : B₁ ∈ WV := by
      rw [Ultrafilter.mem_map] at hbV
      rwa [Set.preimage_image_eq _ hc.injective] at hbV
    have hdec : ∀ W : Ultrafilter ℕ, Free W → B₁ ∈ W →
        L ρ (W.map c) = L (fun k => ρ (c k) - r * y (σ k)) W + r • L y (W.map σ) := by
      intro W hW _
      rw [← L_comp ρ c W]
      have : (fun k => ρ (c k)) = (fun k => ρ (c k) - r * y (σ k)) + r • (fun k => y (σ k)) := by
        funext k; simp
      rw [this, L_add, L_smul, L_comp]
    have hrb : ∀ W : Ultrafilter ℕ, Set.range b ∈ W.map σ := fun W =>
      Ultrafilter.mem_map.2 (Filter.mem_of_superset Filter.univ_mem (fun k _ => hσB k))
    rw [hdec WU hWU hB₁U, hdec WV hWV hB₁V]
    have h2 : L (fun k => ρ (c k) - r * y (σ k)) WU + r • L y (WU.map σ) -
        (L (fun k => ρ (c k) - r * y (σ k)) WV + r • L y (WV.map σ)) =
        (L (fun k => ρ (c k) - r * y (σ k)) WU - L (fun k => ρ (c k) - r * y (σ k)) WV) +
          r • (L y (WU.map σ) - L y (WV.map σ)) := by
      rw [smul_sub]; abel
    rw [h2]
    refine Submodule.add_mem _ (Submodule.subset_span (Or.inr ⟨WU, WV, hWU, hWV, hB₁U, hB₁V, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl
        ⟨WU.map σ, WV.map σ, free_map_fto hσ hWU, free_map_fto hσ hWV, hrb WU, hrb WV, rfl⟩)))

/-! ### Corollary 8.35 (one lacunary sequence, thinning to a sparse set) -/

lemma abs_ge_pow (y : ℕ → ℝ) (hy : ∀ k, 4 * |y k| ≤ |y (k + 1)|) (k m : ℕ) : (4 : ℝ) ^ m * |y k| ≤ |y (k + m)| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hy (k + m)
    calc (4 : ℝ) ^ (m + 1) * |y k| = 4 * ((4 : ℝ) ^ m * |y k|) := by ring
      _ ≤ 4 * |y (k + m)| := by linarith
      _ ≤ |y (k + m + 1)| := h

/-- **Corollary 8.35.** For a lacunary sequence `y` (`y 0 ≠ 0`, `4 |y k| ≤ |y (k+1)|`) and an infinite `C ⊆ ℕ` there is an infinite
`B ⊆ C` such that the real span of the limits `L y U`, `U` free containing `B`, meets `ℝ e(1)` only in `0`. -/
theorem corollary_indepB (y : ℕ → ℝ) (hy0 : y 0 ≠ 0) (hy : ∀ k, 4 * |y k| ≤ |y (k + 1)|) (C : Set ℕ)
    (hC : C.Infinite) : ∃ B : Set ℕ, B ⊆ C ∧ B.Infinite ∧
      Disjoint (Submodule.span ℝ {v : K | ∃ U : Ultrafilter ℕ, Free U ∧ B ∈ U ∧ v = L y U}) (ℝ ∙ e 1) := by
  have hpos : ∀ k, 0 < |y k| := by
    intro k
    induction k with
    | zero => exact abs_pos.mpr hy0
    | succ k ih => linarith [hy k]
  have hy0' : ∀ k, y k ≠ 0 := fun k => abs_pos.mp (hpos k)
  have hstep : ∀ (j k0 : ℕ), ∃ k ∈ C, k0 + j + 1 ≤ k := fun j k0 => by
    obtain ⟨k, hk, hlt⟩ := hC.exists_gt (k0 + j)
    exact ⟨k, hk, hlt⟩
  choose f hfC hfge using hstep
  obtain ⟨b, hb0, hbS⟩ : ∃ b : ℕ → ℕ, b 0 ∈ C ∧ ∀ j, b (j + 1) = f j (b j) :=
    ⟨fun t => Nat.rec (Classical.choose (hC.nonempty)) (fun j bj => f j bj) t, Classical.choose_spec hC.nonempty,
      fun j => rfl⟩
  have hbC : ∀ j, b j ∈ C := by
    intro j
    cases j with
    | zero => exact hb0
    | succ j => rw [hbS]; exact hfC _ _
  have hbgap : ∀ j, b j + j + 1 ≤ b (j + 1) := by
    intro j; rw [hbS]; exact hfge _ _
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ (fun j => by have := hbgap j; omega)
  have hratio : Tendsto (fun t => |y (b (t + 1))| / |y (b t)|) atTop atTop := by
    rw [tendsto_atTop]
    intro R
    refine Filter.eventually_atTop.2 ⟨⌈Real.logb 4 (max R 1)⌉₊ + 1, fun t ht => ?_⟩
    have h1 := abs_ge_pow y hy (b t) (b (t + 1) - b t)
    have hlt : b t < b (t + 1) := hbmono (Nat.lt_succ_self t)
    have h2 : b t + (b (t + 1) - b t) = b (t + 1) := by omega
    rw [h2] at h1
    have h3 : t + 1 ≤ b (t + 1) - b t := by have := hbgap t; omega
    have h4 : (4 : ℝ) ^ (t + 1) ≤ (4 : ℝ) ^ (b (t + 1) - b t) := pow_le_pow_right₀ (by norm_num) h3
    have h5 : max R 1 ≤ (4 : ℝ) ^ (t + 1) := by
      have hm : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      have h6 : Real.logb 4 (max R 1) ≤ ((t + 1 : ℕ) : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈Real.logb 4 (max R 1)⌉₊ ≤ t + 1))
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) h6
      rw [Real.rpow_logb (by norm_num) (by norm_num) hm, Real.rpow_natCast] at this
      exact this
    rw [le_div_iff₀ (hpos (b t))]
    have h7 : (4 : ℝ) ^ (t + 1) * |y (b t)| ≤ |y (b (t + 1))| :=
      le_trans (mul_le_mul_of_nonneg_right h4 (hpos _).le) h1
    have h8 : R * |y (b t)| ≤ max R 1 * |y (b t)| := mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _).le
    have h9 : max R 1 * |y (b t)| ≤ (4 : ℝ) ^ (t + 1) * |y (b t)| := mul_le_mul_of_nonneg_right h5 (hpos _).le
    linarith
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨j, rfl⟩; exact hbC j
  · refine (disjoint_span_L (fun t => y (b t)) (fun t => hy0' _) hratio).mono_left ?_
    apply Submodule.span_le.2
    rintro w ⟨U, hU, hbU, rfl⟩
    obtain ⟨W, hW, rfl⟩ := exists_pre_ultra hbmono.injective hU hbU
    rw [← L_comp y b W]
    exact Submodule.subset_span ⟨(), W, hW, rfl⟩

#print axioms exists_sort
#print axioms independence_listing
#print axioms listing_of_sep
#print axioms independence_sep
#print axioms disjoint_span_L_family
#print axioms prop_uncountable_family
#print axioms exists_retraction_of_joint_family
#print axioms lemma_separation
#print axioms depth_admissible
#print axioms corollary_indepB

end Q95
end PVG
