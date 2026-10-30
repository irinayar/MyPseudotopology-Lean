import LeanCheck.ChainL1

/-!
# Reduction to metrizable topologies
(HamelCharactersTVG_v18 Theorem 21.1 `thm:metric-pair-v8`)

If two members of `𝒬_Γ` have an incompatible join then two metrizable members of `𝒬_Γ` do, with the same extra character.
-/

namespace LeanCheck

open Filter Topology

section SeqBasis

/-- The group filter basis of a decreasing sequence of symmetric sets with `W_{n+1} + W_{n+1} ⊆ W_n`. -/
def seqBasis (W : ℕ → Set ℚ) (h0 : ∀ n, (0 : ℚ) ∈ W n) (hanti : ∀ n, W (n + 1) ⊆ W n)
    (hadd : ∀ n, ∀ x ∈ W (n + 1), ∀ y ∈ W (n + 1), x + y ∈ W n) (hneg : ∀ n, ∀ x ∈ W n, -x ∈ W n) :
    AddGroupFilterBasis ℚ where
  sets := Set.range W
  nonempty := ⟨W 0, 0, rfl⟩
  inter_sets := by
    have hmono : ∀ {n m : ℕ}, n ≤ m → W m ⊆ W n := by
      intro n m hnm
      induction hnm with
      | refl => exact subset_rfl
      | step h ih => exact (hanti _).trans ih
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨W (max a b), ⟨max a b, rfl⟩, Set.subset_inter (hmono (le_max_left _ _)) (hmono (le_max_right _ _))⟩
  zero' := by
    rintro _ ⟨n, rfl⟩
    exact h0 n
  add' := by
    rintro _ ⟨n, rfl⟩
    refine ⟨W (n + 1), ⟨n + 1, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hadd n x hx y hy
  neg' := by
    rintro _ ⟨n, rfl⟩
    refine ⟨W n, ⟨n, rfl⟩, ?_⟩
    intro x hx
    exact hneg n x hx
  conj' := by
    intro x₀ U hU
    refine ⟨U, hU, ?_⟩
    intro x hx
    simpa using hx

lemma seqBasis_hasBasis (W : ℕ → Set ℚ) (h0 : ∀ n, (0 : ℚ) ∈ W n) (hanti : ∀ n, W (n + 1) ⊆ W n)
    (hadd : ∀ n, ∀ x ∈ W (n + 1), ∀ y ∈ W (n + 1), x + y ∈ W n) (hneg : ∀ n, ∀ x ∈ W n, -x ∈ W n) :
    (@nhds ℚ (seqBasis W h0 hanti hadd hneg).topology 0).HasBasis (fun _ : ℕ => True) W := by
  have h := (seqBasis W h0 hanti hadd hneg).nhds_zero_hasBasis
  refine (Filter.hasBasis_iff).2 fun s => ?_
  rw [h.mem_iff]
  constructor
  · rintro ⟨t, ⟨n, rfl⟩, hts⟩
    exact ⟨n, trivial, hts⟩
  · rintro ⟨n, -, hn⟩
    exact ⟨W n, ⟨n, rfl⟩, hn⟩

end SeqBasis

section Step

/-- An enumeration of `ℚ`. -/
noncomputable def qEnum (k : ℕ) : ℚ := (Denumerable.eqv ℚ).symm k

lemma qEnum_surj (r : ℚ) : ∃ k, qEnum k = r := ⟨Denumerable.eqv ℚ r, by simp [qEnum]⟩

lemma qc_symm_inter {τ : TopologicalSpace ℚ} {U : Set ℚ} (hU : QuasiConvex τ U) :
    QuasiConvex τ (U ∩ (fun x => -x) ⁻¹' U) := by
  intro x hx
  by_cases hxU : x ∈ U
  · have hnx : -x ∉ U := fun h => hx ⟨hxU, h⟩
    obtain ⟨χ, hc, h1, h2⟩ := hU (-x) hnx
    refine ⟨χ, hc, fun y hy => h1 y hy.1, ?_⟩
    rwa [map_neg, norm_neg] at h2
  · obtain ⟨χ, hc, h1, h2⟩ := hU x hxU
    exact ⟨χ, hc, fun y hy => h1 y hy.1, h2⟩

/-- One step of the recursive construction of Theorem 21.1. -/
lemma next_step (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (W : Set ℚ) (hW : W ∈ @nhds ℚ δ 0) (n : ℕ) :
    ∃ W' : Set ℚ, W' ∈ @nhds ℚ δ 0 ∧ W' ⊆ W ∧ (∀ x ∈ W', -x ∈ W') ∧ (∀ x ∈ W', ∀ y ∈ W', x + y ∈ W) ∧
      (∀ k ≤ n, ∀ q ∈ W', ‖rchar (qEnum k) q‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ j ≤ n, ∀ q ∈ W', qEnum j * q ∈ W) ∧ QuasiConvex δ W' := by
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := hδ.1.1
  have hcontχ : ∀ r : ℚ, Continuous (rchar r) := fun r => (hδ.1.2.2.2 _).2 (rchar_mem r)
  have hcs : ∀ s : ℚ, Continuous (fun x : ℚ => s * x) := hδ.2
  have hA1 : ∀ k : ℕ, {q : ℚ | ‖rchar (qEnum k) q‖ < 1 / ((n : ℝ) + 1)} ∈ 𝓝 (0 : ℚ) := by
    intro k
    refine (isOpen_lt (continuous_norm.comp (hcontχ (qEnum k))) continuous_const).mem_nhds ?_
    simp only [Set.mem_setOf_eq, Function.comp_apply, map_zero, norm_zero]
    exact one_div_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hA2 : ∀ j : ℕ, {q : ℚ | qEnum j * q ∈ W} ∈ 𝓝 (0 : ℚ) := by
    intro j
    exact (hcs (qEnum j)).continuousAt.preimage_mem_nhds (by simpa using hW)
  set A : Set ℚ := W ∩ (⋂ k ∈ Finset.range (n + 1), {q : ℚ | ‖rchar (qEnum k) q‖ < 1 / ((n : ℝ) + 1)}) ∩
    (⋂ j ∈ Finset.range (n + 1), {q : ℚ | qEnum j * q ∈ W}) with hAdef
  have hA : A ∈ 𝓝 (0 : ℚ) := by
    refine Filter.inter_mem (Filter.inter_mem hW ?_) ?_
    · exact (Filter.biInter_finset_mem _).2 (fun k _ => hA1 k)
    · exact (Filter.biInter_finset_mem _).2 (fun j _ => hA2 j)
  obtain ⟨V, hV, hVA⟩ := exists_nhds_zero_half hA
  have hVs : V ∩ (fun x => -x) ⁻¹' V ∈ 𝓝 (0 : ℚ) :=
    Filter.inter_mem hV ((continuous_neg.continuousAt).preimage_mem_nhds (by simpa using hV))
  obtain ⟨U, hU, hUV, hUqc⟩ := hδ.1.2.2.1 _ hVs
  refine ⟨U ∩ (fun x => -x) ⁻¹' U, Filter.inter_mem hU ((continuous_neg.continuousAt).preimage_mem_nhds (by simpa using hU)),
    ?_, ?_, ?_, ?_, ?_, qc_symm_inter hUqc⟩
  · intro x hx
    have hxV : x ∈ V := (hUV hx.1).1
    have hxV' : -x ∈ V := (hUV hx.1).2
    have h0 := hVA x hxV 0 (mem_of_mem_nhds hV)
    have h1 : x + 0 ∈ W := (hAdef ▸ h0).1.1
    simpa using h1
  · intro x hx
    exact ⟨hx.2, by simpa using hx.1⟩
  · intro x hx y hy
    have := hVA x (hUV hx.1).1 y (hUV hy.1).1
    exact (hAdef ▸ this).1.1
  · intro k hk q hq
    have hqV : q ∈ V := (hUV hq.1).1
    have hq0 : q + 0 ∈ A := hVA q hqV 0 (mem_of_mem_nhds hV)
    have h1 := (hAdef ▸ hq0).1.2
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_setOf_eq] at h1
    simpa using h1 k (Nat.lt_succ_of_le hk)
  · intro j hj q hq
    have hqV : q ∈ V := (hUV hq.1).1
    have hq0 : q + 0 ∈ A := hVA q hqV 0 (mem_of_mem_nhds hV)
    have h1 := (hAdef ▸ hq0).2
    simp only [Set.mem_iInter, Finset.mem_range, Set.mem_setOf_eq] at h1
    simpa using h1 j (Nat.lt_succ_of_le hj)

/-- The specification of one step. -/
def StepSpec (δ : TopologicalSpace ℚ) (W : Set ℚ) (n : ℕ) (W' : Set ℚ) : Prop :=
  W' ∈ @nhds ℚ δ 0 ∧ W' ⊆ W ∧ (∀ x ∈ W', -x ∈ W') ∧ (∀ x ∈ W', ∀ y ∈ W', x + y ∈ W) ∧
    (∀ k ≤ n, ∀ q ∈ W', ‖rchar (qEnum k) q‖ < 1 / ((n : ℝ) + 1)) ∧
    (∀ j ≤ n, ∀ q ∈ W', qEnum j * q ∈ W) ∧ QuasiConvex δ W'

open Classical in
noncomputable def nextW (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (W : Set ℚ) (n : ℕ) : Set ℚ :=
  if h : W ∈ @nhds ℚ δ 0 then (next_step δ hδ W h n).choose else W

lemma nextW_spec (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (W : Set ℚ) (hW : W ∈ @nhds ℚ δ 0) (n : ℕ) :
    StepSpec δ W n (nextW δ hδ W n) := by
  unfold nextW
  rw [dif_pos hW]
  exact (next_step δ hδ W hW n).choose_spec

/-- The recursive sequence of neighbourhoods. -/
noncomputable def Wseq (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) : ℕ → Set ℚ
  | 0 => nextW δ hδ U 0
  | n + 1 => nextW δ hδ (Wseq δ hδ U n) (n + 1)

lemma Wseq_nhds (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) (hU : U ∈ @nhds ℚ δ 0) (n : ℕ) :
    Wseq δ hδ U n ∈ @nhds ℚ δ 0 := by
  induction n with
  | zero => exact (nextW_spec δ hδ U hU 0).1
  | succ n ih => exact (nextW_spec δ hδ _ ih (n + 1)).1

lemma Wseq_zero_spec (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) (hU : U ∈ @nhds ℚ δ 0) :
    StepSpec δ U 0 (Wseq δ hδ U 0) := nextW_spec δ hδ U hU 0

lemma Wseq_succ_spec (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) (hU : U ∈ @nhds ℚ δ 0) (n : ℕ) :
    StepSpec δ (Wseq δ hδ U n) (n + 1) (Wseq δ hδ U (n + 1)) :=
  nextW_spec δ hδ _ (Wseq_nhds δ hδ U hU n) (n + 1)

end Step

section Assembly

lemma t2_of_rchar (t : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ t _)
    (hc : ∀ r : ℚ, @Continuous ℚ Circ t circTop (rchar r)) : @T2Space ℚ t := by
  letI : TopologicalSpace ℚ := t
  haveI : IsTopologicalAddGroup ℚ := hg
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  have hN : ({0} : Set ℚ) = ⋂ r : ℚ, (rchar r) ⁻¹' {0} := by
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro rfl r; exact map_zero _
    · intro h
      by_contra hq
      have h1 := h (1 / (2 * q))
      rw [rchar_apply, circ_zero_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have : (((1 / (2 * q) * q : ℚ)) : ℝ) = 1 / 2 := by
        have : (1 / (2 * q) * q : ℚ) = 1 / 2 := by field_simp
        rw [this]; push_cast; ring
      rw [this] at hn
      have h2 : (2 : ℝ) * n = 1 := by linarith
      have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
      omega
  rw [hN]
  exact isClosed_iInter fun r => isClosed_singleton.preimage (show Continuous (rchar r) from hc r)

lemma qc_transfer {τ τ' : TopologicalSpace ℚ} (h : ∀ χ : ℚ →+ Circ, @Continuous ℚ Circ τ circTop χ ↔ @Continuous ℚ Circ τ' circTop χ)
    {U : Set ℚ} (hU : QuasiConvex τ U) : QuasiConvex τ' U := by
  intro x hx
  obtain ⟨χ, hc, h1, h2⟩ := hU x hx
  exact ⟨χ, (h χ).1 hc, h1, h2⟩

lemma Gam_eq_rchar {χ : ℚ →+ Circ} (h : χ ∈ Gam) : ∃ r : ℚ, χ = rchar r := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, AddMonoidHom.ext fun s => by rw [hr s, rchar_apply]⟩

end Assembly

section Main

variable (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) (hU : U ∈ @nhds ℚ δ 0)

include hU in
lemma Wseq_anti : ∀ n, Wseq δ hδ U (n + 1) ⊆ Wseq δ hδ U n := fun n => (Wseq_succ_spec δ hδ U hU n).2.1

include hU in
lemma Wseq_add : ∀ n, ∀ x ∈ Wseq δ hδ U (n + 1), ∀ y ∈ Wseq δ hδ U (n + 1), x + y ∈ Wseq δ hδ U n :=
  fun n => (Wseq_succ_spec δ hδ U hU n).2.2.2.1

include hU in
lemma Wseq_neg : ∀ n, ∀ x ∈ Wseq δ hδ U n, -x ∈ Wseq δ hδ U n := by
  intro n
  cases n with
  | zero => exact (Wseq_zero_spec δ hδ U hU).2.2.1
  | succ n => exact (Wseq_succ_spec δ hδ U hU n).2.2.1

include hU in
lemma Wseq_zero_mem : ∀ n, (0 : ℚ) ∈ Wseq δ hδ U n := fun n => mem_of_mem_nhds (Wseq_nhds δ hδ U hU n)

include hU in
lemma Wseq_mono {n m : ℕ} (h : n ≤ m) : Wseq δ hδ U m ⊆ Wseq δ hδ U n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (Wseq_anti δ hδ U hU _).trans ih

include hU in
lemma Wseq_qc : ∀ n, QuasiConvex δ (Wseq δ hδ U n) := by
  intro n
  cases n with
  | zero => exact (Wseq_zero_spec δ hδ U hU).2.2.2.2.2.2
  | succ n => exact (Wseq_succ_spec δ hδ U hU n).2.2.2.2.2.2

/-- The topology `ζ` generated by the sequence `W_n`. -/
noncomputable def zetaTop : TopologicalSpace ℚ :=
  (seqBasis (Wseq δ hδ U) (Wseq_zero_mem δ hδ U hU) (Wseq_anti δ hδ U hU) (Wseq_add δ hδ U hU)
    (Wseq_neg δ hδ U hU)).topology

lemma zeta_group : @IsTopologicalAddGroup ℚ (zetaTop δ hδ U hU) _ :=
  (seqBasis (Wseq δ hδ U) (Wseq_zero_mem δ hδ U hU) (Wseq_anti δ hδ U hU) (Wseq_add δ hδ U hU)
    (Wseq_neg δ hδ U hU)).isTopologicalAddGroup

lemma zeta_basis : (@nhds ℚ (zetaTop δ hδ U hU) 0).HasBasis (fun _ : ℕ => True) (Wseq δ hδ U) :=
  seqBasis_hasBasis _ (Wseq_zero_mem δ hδ U hU) (Wseq_anti δ hδ U hU) (Wseq_add δ hδ U hU) (Wseq_neg δ hδ U hU)

lemma zeta_rchar (r : ℚ) : @Continuous ℚ Circ (zetaTop δ hδ U hU) circTop (rchar r) := by
  letI : TopologicalSpace ℚ := zetaTop δ hδ U hU
  haveI : IsTopologicalAddGroup ℚ := zeta_group δ hδ U hU
  obtain ⟨k, hk⟩ := qEnum_surj r
  have hW : Wseq δ hδ U (k + 3) ∈ 𝓝 (0 : ℚ) := (zeta_basis δ hδ U hU).mem_of_mem trivial
  refine continuous_of_quarter_gen (rchar r) hW ?_
  intro q hq
  have h := (Wseq_succ_spec δ hδ U hU (k + 2)).2.2.2.2.1 k (by omega) q hq
  rw [hk] at h
  refine lt_of_lt_of_le h ?_
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma zeta_cont_id : @Continuous ℚ ℚ δ (zetaTop δ hδ U hU) id := by
  have hg := hδ.1.1
  have hz := zeta_group δ hδ U hU
  have hlim : Tendsto (fun x : ℚ => x) (@nhds ℚ δ 0) (@nhds ℚ (zetaTop δ hδ U hU) 0) := by
    rw [(zeta_basis δ hδ U hU).tendsto_right_iff]
    intro n _
    exact Wseq_nhds δ hδ U hU n
  have hca : @ContinuousAt ℚ ℚ δ (zetaTop δ hδ U hU) (⇑(AddMonoidHom.id ℚ)) 0 := hlim
  exact @continuous_of_continuousAt_zero ℚ δ _ hg ℚ (ℚ →+ ℚ) _ (zetaTop δ hδ U hU) hz.toContinuousAdd _ _
    (AddMonoidHom.id ℚ) hca

lemma zeta_dual (χ : ℚ →+ Circ) :
    @Continuous ℚ Circ (zetaTop δ hδ U hU) circTop χ ↔ χ ∈ Gam := by
  constructor
  · intro hχ
    have hle : δ ≤ zetaTop δ hδ U hU := continuous_id_iff_le.1 (zeta_cont_id δ hδ U hU)
    exact (hδ.1.2.2.2 χ).1 (continuous_le_dom hle hχ)
  · intro hχ
    obtain ⟨r, rfl⟩ := Gam_eq_rchar hχ
    exact zeta_rchar δ hδ U hU r

lemma zeta_scalar (q : ℚ) : Continuous[zetaTop δ hδ U hU, zetaTop δ hδ U hU] (fun x : ℚ => q * x) := by
  have hz := zeta_group δ hδ U hU
  have hb := zeta_basis δ hδ U hU
  obtain ⟨j, hj⟩ := qEnum_surj q
  have hlim : Tendsto (fun x : ℚ => q * x) (@nhds ℚ (zetaTop δ hδ U hU) 0) (@nhds ℚ (zetaTop δ hδ U hU) 0) := by
    rw [hb.tendsto_right_iff]
    intro n _
    have hW : Wseq δ hδ U (max (n + 1) j) ∈ @nhds ℚ (zetaTop δ hδ U hU) 0 := hb.mem_of_mem trivial
    refine Filter.mem_of_superset hW ?_
    intro x hx
    have hm : max (n + 1) j = (max (n + 1) j - 1) + 1 := by omega
    have hjm : j ≤ (max (n + 1) j - 1) + 1 := by omega
    have h1 := (Wseq_succ_spec δ hδ U hU (max (n + 1) j - 1)).2.2.2.2.2.1 j hjm x (by rwa [← hm])
    rw [hj] at h1
    exact Wseq_mono δ hδ U hU (by omega : n ≤ max (n + 1) j - 1) h1
  have hca : @ContinuousAt ℚ ℚ (zetaTop δ hδ U hU) (zetaTop δ hδ U hU) (⇑(AddMonoidHom.mulLeft q)) 0 := by
    show Tendsto (fun x : ℚ => q * x) _ (@nhds ℚ (zetaTop δ hδ U hU) (q * 0))
    rw [mul_zero]; exact hlim
  exact @continuous_of_continuousAt_zero ℚ (zetaTop δ hδ U hU) _ hz ℚ (ℚ →+ ℚ) _ (zetaTop δ hδ U hU) hz.toContinuousAdd _ _
    (AddMonoidHom.mulLeft q) hca

/-- **Core of Theorem 21.1.**  Every member of `𝒬_Γ` and each of its zero-neighbourhoods `U` admits a metrizable member of `𝒬_Γ`
that is coarser than it and still has `U` as a zero-neighbourhood. -/
theorem exists_metrizable_between (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) (U : Set ℚ) (hU : U ∈ @nhds ℚ δ 0) :
    ∃ ζ : TopologicalSpace ℚ, ζ ∈ Ccls Gam ∧ @TopologicalSpace.MetrizableSpace ℚ ζ ∧ U ∈ @nhds ℚ ζ 0 ∧ ∃ W : Set ℚ,
      W ∈ @nhds ℚ ζ 0 ∧ W ⊆ U := by
  have hz := zeta_group δ hδ U hU
  have hb := zeta_basis δ hδ U hU
  have ht2 : @T2Space ℚ (zetaTop δ hδ U hU) := t2_of_rchar _ hz (zeta_rchar δ hδ U hU)
  have hW0 : Wseq δ hδ U 0 ∈ @nhds ℚ (zetaTop δ hδ U hU) 0 := hb.mem_of_mem trivial
  have hsub : Wseq δ hδ U 0 ⊆ U := (Wseq_zero_spec δ hδ U hU).2.1
  have hdual := zeta_dual δ hδ U hU
  refine ⟨zetaTop δ hδ U hU, ⟨⟨hz, ht2, ?_, fun χ => (hdual χ)⟩, zeta_scalar δ hδ U hU⟩,
    metrizable_rat _ hz ht2 _ hb, Filter.mem_of_superset hW0 hsub, Wseq δ hδ U 0, hW0, hsub⟩
  intro V hV
  obtain ⟨n, -, hn⟩ := hb.mem_iff.1 hV
  refine ⟨Wseq δ hδ U n, hb.mem_of_mem trivial, hn, ?_⟩
  exact qc_transfer (fun χ => (hδ.1.2.2.2 χ).trans (hdual χ).symm) (Wseq_qc δ hδ U hU n)

end Main

/-- **Theorem 21.1.**  If two members of `𝒬_Γ` have a join with a continuous character `ψ ∉ Γ`, then there are two metrizable members of
`𝒬_Γ` whose join has the same continuous character `ψ`. -/
theorem reduction_to_metrizable (δ₁ δ₂ : TopologicalSpace ℚ) (h₁ : δ₁ ∈ Ccls Gam) (h₂ : δ₂ ∈ Ccls Gam)
    (ψ : ℚ →+ Circ) (hψ : @Continuous ℚ Circ (δ₁ ⊓ δ₂) circTop ψ) (hψne : ψ ∉ Gam) :
    ∃ ζ₁ ζ₂ : TopologicalSpace ℚ, ζ₁ ∈ Ccls Gam ∧ ζ₂ ∈ Ccls Gam ∧ @TopologicalSpace.MetrizableSpace ℚ ζ₁ ∧
      @TopologicalSpace.MetrizableSpace ℚ ζ₂ ∧ @Continuous ℚ Circ (ζ₁ ⊓ ζ₂) circTop ψ ∧ ψ ∉ Gam := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (ψ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℚ (δ₁ ⊓ δ₂) 0 :=
    (@Continuous.continuousAt ℚ Circ (δ₁ ⊓ δ₂) circTop ψ 0 hψ) hS
  rw [@nhds_inf ℚ δ₁ δ₂ 0] at hpre
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hpre
  obtain ⟨ζ₁, hζ₁, hm₁, -, W₁, hW₁, hW₁U⟩ := exists_metrizable_between δ₁ h₁ U₁ hU₁
  obtain ⟨ζ₂, hζ₂, hm₂, -, W₂, hW₂, hW₂U⟩ := exists_metrizable_between δ₂ h₂ U₂ hU₂
  refine ⟨ζ₁, ζ₂, hζ₁, hζ₂, hm₁, hm₂, ?_, hψne⟩
  letI : TopologicalSpace ℚ := ζ₁ ⊓ ζ₂
  haveI : IsTopologicalAddGroup ℚ := isTopologicalAddGroup_inf hζ₁.1.1 hζ₂.1.1
  refine continuous_of_quarter_gen ψ (W := W₁ ∩ W₂) ?_ ?_
  · rw [@nhds_inf ℚ ζ₁ ζ₂ 0]
    exact Filter.inter_mem_inf hW₁ hW₂
  · intro q hq
    have : q ∈ ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} := hsub ⟨hW₁U hq.1, hW₂U hq.2⟩
    exact this

end LeanCheck
