import LeanCheck.ChainD6

/-!
# Ultrafilter tests for compatible joins, and the irrational-witness proposition
(HamelCharactersTVG_v18 Proposition 20.1 `prop:ultralimit-v8`, Theorem 20.2 `thm:ultrafilter-v8`,
 Proposition 23.1 `prop:conditional-v8`)
-/

namespace LeanCheck

open Filter Topology

section JoinQuarter

variable {G : Type*} [AddCommGroup G]

/-- If `‖t‖ ≤ 1/4` and `‖t + t‖ ≤ 1/4` then `‖t‖ < 1/4`. (Same as `norm_lt_quarter_of_double`.) -/
lemma cont_join_closed_quarter (η₁ η₂ : TopologicalSpace G) (h₁ : @IsTopologicalAddGroup G η₁ _)
    (h₂ : @IsTopologicalAddGroup G η₂ _) (ψ : G →+ Circ) (U₁ U₂ : Set G)
    (hU₁ : U₁ ∈ @nhds G η₁ 0) (hU₂ : U₂ ∈ @nhds G η₂ 0) (hsmall : ∀ x ∈ U₁ ∩ U₂, ‖ψ x‖ ≤ 1 / 4) :
    @Continuous G Circ (η₁ ⊓ η₂) circTop ψ := by
  letI : TopologicalSpace G := η₁ ⊓ η₂
  haveI : IsTopologicalAddGroup G := isTopologicalAddGroup_inf h₁ h₂
  have hW : U₁ ∩ U₂ ∈ 𝓝 (0 : G) := by
    have hn : (𝓝 (0 : G)) = @nhds G η₁ 0 ⊓ @nhds G η₂ 0 := @nhds_inf G η₁ η₂ 0
    rw [hn]
    exact Filter.inter_mem_inf hU₁ hU₂
  have hdbl : Continuous (fun x : G => x + x) := continuous_id.add continuous_id
  have hV : (fun x : G => x + x) ⁻¹' (U₁ ∩ U₂) ∩ (U₁ ∩ U₂) ∈ 𝓝 (0 : G) := by
    refine Filter.inter_mem ?_ hW
    refine hdbl.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  refine continuous_of_quarter_gen ψ hV (fun x hx => ?_)
  refine norm_lt_quarter_of_double (hsmall x hx.2) ?_
  have := hsmall (x + x) hx.1
  rw [map_add] at this
  exact this

end JoinQuarter

section Conditional

/-- `psiQ c ∉ Γ` for irrational `c`. -/
lemma psiQ_not_Gam {c : ℝ} (hc : Irrational c) : psiQ c ∉ Gam := by
  rintro ⟨r, hr⟩
  have h1 := hr 1
  rw [psiQ_apply] at h1
  simp only [Rat.cast_one, mul_one, mul_one] at h1
  have h2 : ((c - (r : ℝ) : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_sub, h1]
    simp
  obtain ⟨n, hn⟩ := (circ_zero_iff _).1 h2
  exact hc ⟨r + n, by push_cast; linarith⟩

/-- **Proposition 23.1.**  Let `f` be a coefficient function (`f u = 1`).  If an irrational `c`, a positive integer `d`
and `ε > 0` satisfy `‖c q‖ ≤ 1/4` whenever `max(P_{2,d}(q), P_{3,d}(q)) < ε`, then `𝒞_f` has no greatest member. -/
theorem conditional_witness (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (c : ℝ) (hc : Irrational c)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ∀ q ∈ xiSet (Cp 2) d ε ∩ xiSet (Cp 3) d ε, ‖psiQ c q‖ ≤ 1 / 4) :
    ¬ ∃ μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ := by
  rintro ⟨μ, hμ, hgr⟩
  have hg2 := gamma_p_mem 2 le_rfl
  have hg3 := gamma_p_mem 3 (by norm_num)
  have hT2 := Tf_mem_Kcls f _ hg2
  have hT3 := Tf_mem_Kcls f _ hg3
  have hcont : @Continuous ℚ Circ (xi (Cp 2) ⊓ xi (Cp 3)) circTop (psiQ c) :=
    cont_join_closed_quarter (xi (Cp 2)) (xi (Cp 3)) hg2.1.1 hg3.1.1 (psiQ c)
      (xiSet (Cp 2) d ε) (xiSet (Cp 3) d ε)
      ((xi_nhds_hasBasis (Cp 2)).mem_of_mem (xiSet_mem (Cp 2) d hd ε hε))
      ((xi_nhds_hasBasis (Cp 3)).mem_of_mem (xiSet_mem (Cp 3) d hd ε hε)) hsmall
  have hne : ∀ r : ℚ, ∃ s : ℚ, psiQ c s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
    intro r
    by_contra hall
    push Not at hall
    exact psiQ_not_Gam hc ⟨r, hall⟩
  obtain ⟨φ, hφ, hφne⟩ := transfer_obstruction f u hu (xi (Cp 2)) (xi (Cp 3)) (psiQ c) hcont hne
  have hle : μ ≤ Tf f (xi (Cp 2)) ⊓ Tf f (xi (Cp 3)) := le_inf (hgr _ hT2) (hgr _ hT3)
  have hcμ : @Continuous ℝ Circ μ circTop φ := continuous_le_dom hle hφ
  obtain ⟨c', a, -, h⟩ := (hμ.2.2.2.1 φ).1 hcμ
  exact hφne ⟨c', a, h⟩

end Conditional

section Ultra

variable {I : Type*}

lemma exists_ulim (𝒰 : Ultrafilter I) (r : I → ℚ) (q : ℚ) :
    ∃ y : Circ, Tendsto (fun i => rchar (r i) q) 𝒰 (𝓝 y) := by
  obtain ⟨y, -, hy⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circ)).ultrafilter_le_nhds
    (𝒰.map (fun i => rchar (r i) q)) (by simp)
  exact ⟨y, hy⟩

/-- The ultralimit `ψ(q) = lim_{i → 𝒰} p(r_i q)` as a character of `ℚ`. -/
noncomputable def ulimChar (𝒰 : Ultrafilter I) (r : I → ℚ) : ℚ →+ Circ where
  toFun q := Classical.choose (exists_ulim 𝒰 r q)
  map_zero' := by
    have h := Classical.choose_spec (exists_ulim 𝒰 r 0)
    have h0 : Tendsto (fun i => rchar (r i) 0) 𝒰 (𝓝 0) := by
      simp only [map_zero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h h0
  map_add' a b := by
    have ha := Classical.choose_spec (exists_ulim 𝒰 r a)
    have hb := Classical.choose_spec (exists_ulim 𝒰 r b)
    have hab := Classical.choose_spec (exists_ulim 𝒰 r (a + b))
    have hsum : Tendsto (fun i => rchar (r i) (a + b)) 𝒰
        (𝓝 (Classical.choose (exists_ulim 𝒰 r a) + Classical.choose (exists_ulim 𝒰 r b))) := by
      simp only [map_add]; exact ha.add hb
    exact tendsto_nhds_unique hab hsum

lemma ulimChar_tendsto (𝒰 : Ultrafilter I) (r : I → ℚ) (q : ℚ) :
    Tendsto (fun i => rchar (r i) q) 𝒰 (𝓝 (ulimChar 𝒰 r q)) :=
  Classical.choose_spec (exists_ulim 𝒰 r q)

/-- **Proposition 20.1, first part.**  The ultralimit character is continuous for the join as soon as the closed
quarter-arc bound holds on a joint neighbourhood. -/
theorem ultralimit_test (δ₁ δ₂ : TopologicalSpace ℚ) (h₁ : @IsTopologicalAddGroup ℚ δ₁ _)
    (h₂ : @IsTopologicalAddGroup ℚ δ₂ _) (𝒰 : Ultrafilter I) (r : I → ℚ)
    (U₁ U₂ : Set ℚ) (hU₁ : U₁ ∈ @nhds ℚ δ₁ 0) (hU₂ : U₂ ∈ @nhds ℚ δ₂ 0)
    (hsmall : ∀ q ∈ U₁ ∩ U₂, ∀ i, ‖rchar (r i) q‖ ≤ 1 / 4) :
    @Continuous ℚ Circ (δ₁ ⊓ δ₂) circTop (ulimChar 𝒰 r) := by
  refine cont_join_closed_quarter δ₁ δ₂ h₁ h₂ _ U₁ U₂ hU₁ hU₂ (fun q hq => ?_)
  have hcl : IsClosed {y : Circ | ‖y‖ ≤ 1 / 4} := isClosed_le continuous_norm continuous_const
  exact hcl.mem_of_tendsto (ulimChar_tendsto 𝒰 r q) (Eventually.of_forall (fun i => hsmall q hq i))

/-- **Proposition 20.1, consequence.**  If the ultralimit character is not in `Γ`, the join has an extra character. -/
theorem ultralimit_incompatible (δ₁ δ₂ : TopologicalSpace ℚ) (h₁ : @IsTopologicalAddGroup ℚ δ₁ _)
    (h₂ : @IsTopologicalAddGroup ℚ δ₂ _) (𝒰 : Ultrafilter I) (r : I → ℚ)
    (U₁ U₂ : Set ℚ) (hU₁ : U₁ ∈ @nhds ℚ δ₁ 0) (hU₂ : U₂ ∈ @nhds ℚ δ₂ 0)
    (hsmall : ∀ q ∈ U₁ ∩ U₂, ∀ i, ‖rchar (r i) q‖ ≤ 1 / 4) (hnot : ulimChar 𝒰 r ∉ Gam) :
    ¬ ∀ χ : ℚ →+ Circ, @Continuous ℚ Circ (δ₁ ⊓ δ₂) circTop χ → χ ∈ Gam :=
  fun h => hnot (h _ (ultralimit_test δ₁ δ₂ h₁ h₂ 𝒰 r U₁ U₂ hU₁ hU₂ hsmall))

/-- **Proposition 20.1, last sentence.**  If `r_n → c` usually with `c` irrational, every free ultrafilter on `ℕ`
gives `ψ(q) = p(c q) ∉ Γ`. -/
theorem ulimChar_of_tendsto (r : ℕ → ℚ) (c : ℝ) (hr : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 c))
    (hc : Irrational c) (𝒰 : Ultrafilter ℕ) (hfree : (𝒰 : Filter ℕ) ≤ atTop) :
    (∀ q : ℚ, ulimChar 𝒰 r q = ((c * (q : ℝ) : ℝ) : Circ)) ∧ ulimChar 𝒰 r ∉ Gam := by
  have hval : ∀ q : ℚ, ulimChar 𝒰 r q = ((c * (q : ℝ) : ℝ) : Circ) := by
    intro q
    have h1 : Tendsto (fun n => rchar (r n) q) atTop (𝓝 ((c * (q : ℝ) : ℝ) : Circ)) := by
      have : Tendsto (fun n => (((r n : ℝ) * (q : ℝ) : ℝ) : Circ)) atTop (𝓝 (((c * (q : ℝ) : ℝ)) : Circ)) :=
        (continuous_coe_circ.tendsto _).comp (hr.mul_const (q : ℝ))
      refine this.congr (fun n => ?_)
      rw [rchar_apply]; push_cast; rfl
    have h2 := h1.mono_left hfree
    exact tendsto_nhds_unique (ulimChar_tendsto 𝒰 r q) h2
  refine ⟨hval, ?_⟩
  have : ulimChar 𝒰 r = psiQ c := by
    ext q; rw [hval q, psiQ_apply]
  rw [this]
  exact psiQ_not_Gam hc

/-- **Theorem 20.2 (exact ultrafilter criterion).**  For group topologies `δ₁, δ₂` on `ℚ`, the join is compatible with
`Γ` (it has no continuous character outside `Γ`) iff every `ψ ∉ Γ` admits an ultrafilter on `ℚ` converging to `0` in
both topologies and containing `A_ψ = {q : ‖ψ q‖ > 1/4}`. -/
theorem ultrafilter_criterion (δ₁ δ₂ : TopologicalSpace ℚ) (h₁ : @IsTopologicalAddGroup ℚ δ₁ _)
    (h₂ : @IsTopologicalAddGroup ℚ δ₂ _) :
    (∀ χ : ℚ →+ Circ, @Continuous ℚ Circ (δ₁ ⊓ δ₂) circTop χ → χ ∈ Gam) ↔
      ∀ ψ : ℚ →+ Circ, ψ ∉ Gam → ∃ F : Ultrafilter ℚ, (F : Filter ℚ) ≤ @nhds ℚ δ₁ 0 ∧
        (F : Filter ℚ) ≤ @nhds ℚ δ₂ 0 ∧ {q : ℚ | 1 / 4 < ‖ψ q‖} ∈ F := by
  constructor
  · intro hcompat ψ hψ
    -- the filter `𝓝₁ ⊓ 𝓝₂ ⊓ 𝓟 A_ψ` is proper, else `ψ` would be continuous for the join
    have hne : (@nhds ℚ δ₁ 0 ⊓ @nhds ℚ δ₂ 0 ⊓ 𝓟 {q : ℚ | 1 / 4 < ‖ψ q‖}).NeBot := by
      rw [Filter.inf_principal_neBot_iff]
      intro S hS
      rw [Filter.mem_inf_iff] at hS
      obtain ⟨U₁, hU₁, U₂, hU₂, rfl⟩ := hS
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hψ
      apply hcompat
      refine cont_join_closed_quarter δ₁ δ₂ h₁ h₂ ψ U₁ U₂ hU₁ hU₂ (fun x hx => ?_)
      by_contra hxn
      push Not at hxn
      have : x ∈ (U₁ ∩ U₂) ∩ {q : ℚ | 1 / 4 < ‖ψ q‖} := ⟨hx, hxn⟩
      rw [hempty] at this
      exact this
    refine ⟨Ultrafilter.of (@nhds ℚ δ₁ 0 ⊓ @nhds ℚ δ₂ 0 ⊓ 𝓟 {q : ℚ | 1 / 4 < ‖ψ q‖}), ?_, ?_, ?_⟩
    · exact (Ultrafilter.of_le _).trans (inf_le_left.trans inf_le_left)
    · exact (Ultrafilter.of_le _).trans (inf_le_left.trans inf_le_right)
    · have := (Ultrafilter.of_le (@nhds ℚ δ₁ 0 ⊓ @nhds ℚ δ₂ 0 ⊓ 𝓟 {q : ℚ | 1 / 4 < ‖ψ q‖})).trans
        (inf_le_right : @nhds ℚ δ₁ 0 ⊓ @nhds ℚ δ₂ 0 ⊓ 𝓟 {q : ℚ | 1 / 4 < ‖ψ q‖} ≤ 𝓟 _)
      exact Filter.le_principal_iff.1 this
  · intro h χ hχ
    by_contra hnot
    obtain ⟨F, hF1, hF2, hA⟩ := h χ hnot
    -- `F → 0` for the join, so `χ(F) → 0`, contradicting `A_χ ∈ F`
    have hF : (F : Filter ℚ) ≤ @nhds ℚ (δ₁ ⊓ δ₂) 0 := by
      rw [@nhds_inf ℚ δ₁ δ₂ 0]; exact le_inf hF1 hF2
    have hT : Tendsto χ (F : Filter ℚ) (𝓝 (χ 0)) :=
      ((@Continuous.tendsto ℚ Circ (δ₁ ⊓ δ₂) _ χ hχ 0)).mono_left hF
    rw [map_zero] at hT
    have hopen : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (0 : Circ) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    have hS : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ (F : Filter ℚ) := hT hopen
    have hinter := (F : Filter ℚ).inter_mem hS hA
    obtain ⟨x, hx1, hx2⟩ := (F : Filter ℚ).nonempty_of_mem hinter
    have h1 : ‖χ x‖ < 1 / 4 := hx1
    have h2 : 1 / 4 < ‖χ x‖ := hx2
    linarith

end Ultra

end LeanCheck
