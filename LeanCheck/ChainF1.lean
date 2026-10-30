import LeanCheck.ChainE7

/-!
# The number of precompact TVG topologies
(HamelCharactersTVG_v18 Theorem 15.3 `thm:precompact-count`)

The group `𝒜 = Hom(ℝ, 𝕋)` of characters is a real vector space under `(a • χ)(x) = χ(a x)`.  Its real dimension is `2^𝔠`; there are
exactly `2^(2^𝔠)` separating real subspaces, hence (classification 15.1) exactly `2^(2^𝔠)` Hausdorff precompact TVG topologies, and
exactly `2^𝔠` real lines, hence (15.2) exactly `2^𝔠` minimal Hausdorff TVG topologies.
-/

namespace LeanCheck

open Cardinal Filter Topology

section CharSpace

noncomputable instance charsSMul : SMul ℝ Chars := ⟨fun a χ => χ.comp (AddMonoidHom.mulLeft a)⟩

lemma chars_smul_apply (a : ℝ) (χ : Chars) (x : ℝ) : (a • χ) x = χ (a * x) := rfl

noncomputable instance charsModule : Module ℝ Chars where
  one_smul χ := by ext x; rw [chars_smul_apply, one_mul]
  mul_smul a b χ := by ext x; rw [chars_smul_apply, chars_smul_apply, chars_smul_apply, mul_comm a b, mul_assoc]
  smul_zero a := by ext x; rw [chars_smul_apply]; rfl
  smul_add a χ ψ := by ext x; rw [chars_smul_apply]; rfl
  add_smul a b χ := by ext x; rw [chars_smul_apply]; simp [chars_smul_apply, add_mul, map_add]
  zero_smul χ := by ext x; rw [chars_smul_apply, zero_mul]; simp

end CharSpace

section Cardinality

lemma card_Circ_le : #Circ ≤ 𝔠 := by
  have : #ℝ = 𝔠 := mk_real
  rw [← this]
  exact mk_le_of_surjective (f := fun x : ℝ => (x : Circ)) (QuotientAddGroup.mk_surjective)

lemma card_Chars : #Chars = 2 ^ 𝔠 := by
  apply le_antisymm
  · calc #Chars ≤ #(ℝ → Circ) := mk_le_of_injective DFunLike.coe_injective
      _ = #Circ ^ 𝔠 := by rw [mk_arrow, lift_id, lift_id, mk_real]
      _ ≤ 𝔠 ^ 𝔠 := power_le_power_right card_Circ_le
      _ = 2 ^ 𝔠 := power_self_eq aleph0_le_continuum
  · rw [← card_addHom]
    refine mk_le_of_injective
      (f := fun f : ℝ →+ ℚ => (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
        ((Rat.castHom ℝ).toAddMonoidHom.comp f)) ?_
    intro f g h
    have hfg : ∀ x : ℝ, ((((f x : ℚ) : ℝ) : ℝ) : Circ) = ((((g x : ℚ) : ℝ) : ℝ) : Circ) := fun x => by
      simpa using congrArg (fun m : ℝ →+ Circ => m x) h
    have := lift_unique ((Rat.castHom ℝ).toAddMonoidHom.comp f) ((Rat.castHom ℝ).toAddMonoidHom.comp g) hfg
    ext x
    have := congrArg (fun m : ℝ →+ ℝ => m x) this
    simpa using this

/-- The real dimension of the space of characters is `2^𝔠`. -/
lemma card_chooseBasisIndex : #(Module.Free.ChooseBasisIndex ℝ Chars) = 2 ^ 𝔠 := by
  have hlt : lift.{0} #ℝ < lift.{0} #Chars := by
    rw [lift_id, lift_id, card_Chars, mk_real]; exact cantor 𝔠
  have := Module.Free.rank_eq_mk_of_infinite_lt (R := ℝ) (M := Chars) hlt
  rw [Module.Free.rank_eq_card_chooseBasisIndex] at this
  rw [this, card_Chars]

end Cardinality

section Count

abbrev ι0 : Type := Module.Free.ChooseBasisIndex ℝ Chars

noncomputable def bC : Module.Basis ι0 ℝ Chars := Module.Free.chooseBasis ℝ Chars

/-- The finite support of `scalChar 1` in the basis. -/
noncomputable def Jset : Finset ι0 := (bC.repr (scalChar 1)).support

/-- The real subspace spanned by the basis vectors indexed by `S` together with `scalChar 1`. -/
noncomputable def HS (S : Set ι0) : Submodule ℝ Chars := Submodule.span ℝ (bC '' (S ∪ (Jset : Set ι0)))

lemma scalChar_mem_HS (S : Set ι0) : scalChar 1 ∈ HS S := by
  unfold HS
  rw [Module.Basis.mem_span_image]
  exact Set.subset_union_right

lemma HS_separates (S : Set ι0) : Separates ((HS S).toAddSubgroup : Set Chars) := by
  intro x hx
  refine ⟨(1 / (2 * x)) • scalChar 1, Submodule.smul_mem _ _ (scalChar_mem_HS S), ?_⟩
  rw [chars_smul_apply, scalChar_apply]
  have : (1 * (1 / (2 * x) * x) : ℝ) = 1 / 2 := by field_simp
  rw [this]
  exact half_ne_zero_circ

lemma HS_realInv (S : Set ι0) : RealInv ((HS S).toAddSubgroup : Set Chars) := by
  intro χ hχ a
  exact Submodule.smul_mem (HS S) a hχ

lemma HS_injective {S T : Set ι0} (hS : S ⊆ (Jset : Set ι0)ᶜ) (hT : T ⊆ (Jset : Set ι0)ᶜ)
    (h : HS S = HS T) : S = T := by
  have key : ∀ {S T : Set ι0}, S ⊆ (Jset : Set ι0)ᶜ → HS S = HS T → S ⊆ T := by
    intro S T hS h i hi
    have h1 : bC i ∈ HS S := Submodule.subset_span ⟨i, Or.inl hi, rfl⟩
    rw [h] at h1
    unfold HS at h1
    rw [Module.Basis.mem_span_image, Module.Basis.repr_self,
      Finsupp.support_single_ne_zero _ one_ne_zero] at h1
    have : i ∈ T ∪ (Jset : Set ι0) := h1 (by simp)
    rcases this with hiT | hiJ
    · exact hiT
    · exact absurd hiJ (hS hi)
  exact Set.Subset.antisymm (key hS h) (key hT h.symm)

lemma card_compl_Jset : #((Jset : Set ι0)ᶜ : Set ι0) = 2 ^ 𝔠 := by
  haveI : Infinite ι0 := by
    apply Cardinal.infinite_iff.2
    rw [card_chooseBasisIndex]
    exact aleph0_le_continuum.trans (cantor 𝔠).le
  have h1 : #(Jset : Set ι0) < #ι0 := by
    calc #(Jset : Set ι0) < ℵ₀ := Cardinal.lt_aleph0_of_finite _
      _ ≤ #ι0 := Cardinal.infinite_iff.1 inferInstance
  rw [mk_compl_of_infinite _ h1, card_chooseBasisIndex]

/-- The subtype of Hausdorff precompact TVG topologies. -/
abbrev PT : Type := {τ : TopologicalSpace ℝ // PTVG τ}

/-- **Theorem 15.3, first count.**  There are exactly `2^(2^𝔠)` Hausdorff precompact TVG topologies on `ℝ`. -/
theorem card_precompact_TVG : #PT = (2 : Cardinal) ^ ((2 : Cardinal) ^ 𝔠) := by
  obtain ⟨hclass, hrep, hinj, -⟩ := classification_TVG_unc
  apply le_antisymm
  · -- upper bound: injection into the power set of the character group
    let H : PT → AddSubgroup Chars := fun τ => Classical.choose (hrep τ.1 τ.2)
    have hspec : ∀ τ : PT, Separates (H τ : Set Chars) ∧ RealInv (H τ : Set Chars) ∧ τ.1 = theta (H τ : Set Chars) :=
      fun τ => Classical.choose_spec (hrep τ.1 τ.2)
    calc #PT ≤ #(Set Chars) := by
          refine mk_le_of_injective (f := fun τ : PT => ((H τ : AddSubgroup Chars) : Set Chars)) ?_
          intro τ τ' h
          have hH : H τ = H τ' := SetLike.coe_injective h
          exact Subtype.ext (by rw [(hspec τ).2.2, (hspec τ').2.2, hH])
      _ = (2 : Cardinal) ^ ((2 : Cardinal) ^ 𝔠) := by rw [mk_set, card_Chars]
  · -- lower bound: subspaces spanned by basis vectors
    calc (2 : Cardinal) ^ ((2 : Cardinal) ^ 𝔠) = 2 ^ #((Jset : Set ι0)ᶜ : Set ι0) := by rw [card_compl_Jset]
      _ = #(↥(𝒫 ((Jset : Set ι0)ᶜ))) := (mk_powerset _).symm
      _ ≤ #PT := by
          refine mk_le_of_injective
            (f := fun S : ↥(𝒫 ((Jset : Set ι0)ᶜ)) =>
              (⟨theta (((HS S.1).toAddSubgroup : AddSubgroup Chars) : Set Chars),
                hclass _ (HS_separates S.1) (HS_realInv S.1)⟩ : PT)) ?_
          intro S T h
          have h1 : theta (((HS S.1).toAddSubgroup : AddSubgroup Chars) : Set Chars) =
              theta (((HS T.1).toAddSubgroup : AddSubgroup Chars) : Set Chars) := congrArg Subtype.val h
          have h2 := (hinj _ _ (HS_separates S.1) (HS_separates T.1)).1 h1
          have h3 : HS S.1 = HS T.1 := Submodule.toAddSubgroup_injective h2
          exact Subtype.ext (HS_injective S.2 T.2 h3)

/-- Minimal (precompact) Hausdorff TVG topologies: precompact members of the class `TVGcls` with no strictly coarser member. -/
abbrev MT : Type := {τ : TopologicalSpace ℝ // PTVG τ ∧ Maximal (· ∈ TVGcls) τ}

lemma bC_ne_zero (i : ι0) : bC i ≠ 0 := bC.ne_zero i

lemma lineSub_eq_iff {i j : ι0} (h : lineSub (bC i) = lineSub (bC j)) : i = j := by
  by_contra hne
  have hmem : bC i ∈ lineSub (bC i) := ⟨1, by ext x; simp⟩
  rw [h] at hmem
  obtain ⟨a, ha⟩ := hmem
  have h1 : bC i = a • bC j := ha
  have h2 := congrArg (fun v => bC.repr v i) h1
  simp only [Module.Basis.repr_self, map_smul, Finsupp.smul_apply, Finsupp.single_apply] at h2
  simp [hne, Finsupp.single_apply, Ne.symm hne] at h2

/-- **Theorem 15.3, second count.**  Exactly `2^𝔠` of the precompact Hausdorff TVG topologies are minimal
Hausdorff TVG topologies. -/
theorem card_minimal_TVG : #MT = 2 ^ 𝔠 := by
  obtain ⟨hclass, hrep, hinj, -⟩ := classification_TVG_unc
  apply le_antisymm
  · -- each minimal topology is `θ` of a real line `ℝχ₀`
    have hex : ∀ τ : MT, ∃ χ₀ : Chars, χ₀ ≠ 0 ∧ τ.1 = theta ((lineSub χ₀ : AddSubgroup Chars) : Set Chars) := by
      intro τ
      obtain ⟨H, hs, hr, hτ⟩ := hrep τ.1 τ.2.1
      have hmax : Maximal (· ∈ TVGcls) (theta (H : Set Chars)) := hτ ▸ τ.2.2
      obtain ⟨χ₀, hχ₀, hH⟩ := (minimal_iff_line H hs hr).1 hmax
      exact ⟨χ₀, hχ₀, by rw [hτ, hH]⟩
    calc #MT ≤ #Chars := by
          refine mk_le_of_injective (f := fun τ : MT => Classical.choose (hex τ)) ?_
          intro τ τ' h
          have e1 := (Classical.choose_spec (hex τ)).2
          have e2 := (Classical.choose_spec (hex τ')).2
          have h' : Classical.choose (hex τ) = Classical.choose (hex τ') := h
          exact Subtype.ext (by rw [e1, e2, h'])
      _ = 2 ^ 𝔠 := card_Chars
  · rw [← card_chooseBasisIndex]
    refine mk_le_of_injective
      (f := fun i : ι0 => (⟨theta ((lineSub (bC i) : AddSubgroup Chars) : Set Chars),
        hclass _ (lineSub_separates (bC_ne_zero i)) (lineSub_realInv _),
        (minimal_iff_line _ (lineSub_separates (bC_ne_zero i)) (lineSub_realInv _)).2 ⟨bC i, bC_ne_zero i, rfl⟩⟩ : MT)) ?_
    intro i j h
    have h1 : theta ((lineSub (bC i) : AddSubgroup Chars) : Set Chars) =
        theta ((lineSub (bC j) : AddSubgroup Chars) : Set Chars) := congrArg Subtype.val h
    exact lineSub_eq_iff ((hinj _ _ (lineSub_separates (bC_ne_zero i)) (lineSub_separates (bC_ne_zero j))).1 h1)

/-- **Theorem 15.3.** -/
theorem precompact_count :
    #PT = (2 : Cardinal) ^ ((2 : Cardinal) ^ 𝔠) ∧ #MT = (2 : Cardinal) ^ 𝔠 :=
  ⟨card_precompact_TVG, card_minimal_TVG⟩

end Count

end LeanCheck
