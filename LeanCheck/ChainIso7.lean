import LeanCheck.ChainIso6

/-!
# Isomorphism classification, part 7: exactly `2^𝔠` isomorphism types
(TVGQ-v7 Corollary `cor:isomorphism-v3` and Corollary `tauiso:types`, counting parts)

Each of the families `{β_{f,ℚ} : f ≠ 0}`, `{σ_{f,ℚ} : f ≠ 0}`, `{τ_{f,ℚ} : f ≠ 0}` contains exactly `2^𝔠`
additive topological group isomorphism types.  There are `2^𝔠` nonzero rational-linear functionals,
and for fixed `f` the relation `g(cx) = r f(x)` leaves at most `𝔠` choices of `g`.
-/

namespace LeanCheck

open Cardinal

/-! ### Isomorphism is an equivalence relation -/

lemma isoTop_refl (η : TopologicalSpace ℝ) : IsoTop η η :=
  ⟨AddEquiv.refl ℝ, @continuous_id ℝ η, @continuous_id ℝ η⟩

lemma isoTop_symm {η₁ η₂ : TopologicalSpace ℝ} (h : IsoTop η₁ η₂) : IsoTop η₂ η₁ := by
  obtain ⟨L, h1, h2⟩ := h
  exact ⟨L.symm, h2, by simpa using h1⟩

lemma isoTop_trans {η₁ η₂ η₃ : TopologicalSpace ℝ} (h : IsoTop η₁ η₂) (h' : IsoTop η₂ η₃) :
    IsoTop η₁ η₃ := by
  obtain ⟨L₁, h1, h2⟩ := h
  obtain ⟨L₂, h1', h2'⟩ := h'
  refine ⟨L₁.trans L₂, ?_, ?_⟩
  · exact @Continuous.comp ℝ ℝ ℝ η₁ η₂ η₃ (L₁ : ℝ → ℝ) (L₂ : ℝ → ℝ) h1' h1
  · exact @Continuous.comp ℝ ℝ ℝ η₃ η₂ η₁ (L₂.symm : ℝ → ℝ) (L₁.symm : ℝ → ℝ) h2 h2'

/-- The setoid of additive topological group isomorphism on an indexed family of topologies. -/
def isoSetoid {X : Type} (η : X → TopologicalSpace ℝ) : Setoid X where
  r x y := IsoTop (η x) (η y)
  iseqv := ⟨fun x => isoTop_refl _, fun h => isoTop_symm h, fun h h' => isoTop_trans h h'⟩

/-! ### An abstract counting principle -/

theorem count_types {X : Type} (η : X → TopologicalSpace ℝ) (hX : #X = 2 ^ 𝔠)
    (hcl : ∀ x, #{y : X // IsoTop (η x) (η y)} ≤ 𝔠) :
    #(Quotient (isoSetoid η)) = 2 ^ 𝔠 := by
  classical
  have hsurj : Function.Surjective (Quotient.mk (isoSetoid η)) :=
    fun q => Quotient.inductionOn q (fun x => ⟨x, rfl⟩)
  apply le_antisymm
  · rw [← hX]; exact mk_le_of_surjective hsurj
  · by_contra hlt
    rw [not_le] at hlt
    have hfib : ∀ q : Quotient (isoSetoid η),
        #{x : X // Quotient.mk (isoSetoid η) x = q} ≤ 𝔠 := by
      intro q
      refine le_trans (mk_le_of_injective (f := fun x : {x : X // Quotient.mk (isoSetoid η) x = q} =>
        (⟨x.1, ?_⟩ : {y : X // IsoTop (η q.out) (η y)})) ?_) (hcl q.out)
      · have := Quotient.mk_out (s := isoSetoid η) x.1
        rw [x.2] at this
        exact this
      · intro x x' h
        exact Subtype.ext (congrArg (fun y : {y : X // IsoTop (η q.out) (η y)} => y.1) h)
    have hsum : #X ≤ #(Quotient (isoSetoid η)) * 𝔠 := by
      rw [← mk_congr (Equiv.sigmaFiberEquiv (Quotient.mk (isoSetoid η))), mk_sigma,
        ← sum_const' (Quotient (isoSetoid η)) 𝔠]
      exact sum_le_sum _ _ hfib
    have hlt2 : #(Quotient (isoSetoid η)) * 𝔠 < 2 ^ 𝔠 :=
      mul_lt_of_lt (aleph0_le_continuum.trans (cantor 𝔠).le) hlt (cantor 𝔠)
    rw [hX] at hsum
    exact absurd hsum (not_le.2 hlt2)

/-! ### Cardinality of the space of functionals -/

theorem card_addHom : #(ℝ →+ ℚ) = 2 ^ 𝔠 := by
  have hB : #(Module.Free.ChooseBasisIndex ℚ ℝ) = 𝔠 := by
    rw [← Module.Free.rank_eq_card_chooseBasisIndex, Real.rank_rat_real]
  have hpow : (ℵ₀ : Cardinal) ^ 𝔠 = 2 ^ 𝔠 :=
    power_eq_two_power aleph0_le_continuum (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 2)).le)
      aleph0_le_continuum
  have hQ : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
  apply le_antisymm
  · calc #(ℝ →+ ℚ) ≤ #(ℝ → ℚ) := mk_le_of_injective DFunLike.coe_injective
      _ = ℵ₀ ^ 𝔠 := by rw [mk_arrow, lift_id, lift_id, mk_real, hQ]
      _ = 2 ^ 𝔠 := hpow
  · calc 2 ^ 𝔠 = ℵ₀ ^ 𝔠 := hpow.symm
      _ = #(Module.Free.ChooseBasisIndex ℚ ℝ → ℚ) := by
          rw [mk_arrow, lift_id, lift_id, hB, hQ]
      _ ≤ #(ℝ →+ ℚ) := by
          refine mk_le_of_injective
            (f := fun v => ((Module.Free.chooseBasis ℚ ℝ).constr ℚ v : ℝ →ₗ[ℚ] ℚ).toAddMonoidHom) ?_
          intro v w h
          apply ((Module.Free.chooseBasis ℚ ℝ).constr ℚ).injective
          apply LinearMap.ext
          intro x
          exact DFunLike.congr_fun h x

theorem card_nonzero_addHom : #{f : ℝ →+ ℚ // f ≠ 0} = 2 ^ 𝔠 := by
  have hbig : ℵ₀ ≤ 2 ^ 𝔠 := aleph0_le_continuum.trans (cantor 𝔠).le
  haveI : Infinite (ℝ →+ ℚ) := Cardinal.infinite_iff.2 (card_addHom ▸ hbig)
  have h1 : #(({0} : Set (ℝ →+ ℚ))ᶜ : Set (ℝ →+ ℚ)) = #(ℝ →+ ℚ) := by
    apply mk_compl_of_infinite
    rw [mk_singleton, card_addHom]
    exact lt_of_lt_of_le one_lt_aleph0 hbig
  rw [← card_addHom, ← h1]
  exact mk_congr (Equiv.subtypeEquivRight (fun f => by simp))

/-! ### Each isomorphism class is small -/

/-- The criterion of the paper: `g(cx) = r f(x)` with `c ≠ 0`, `r ∈ ℚ \ {0}`. -/
def Crit (f g : ℝ →+ ℚ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ ∃ r : ℚ, r ≠ 0 ∧ ∀ x : ℝ, g (c * x) = r * f x

theorem class_le (f : ℝ →+ ℚ) : #{g : ℝ →+ ℚ // Crit f g} ≤ 𝔠 := by
  classical
  let P : {g : ℝ →+ ℚ // Crit f g} → ℝ × ℚ → Prop :=
    fun g p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ ∀ x, g.1 (p.1 * x) = p.2 * f x
  have hex : ∀ g, ∃ p, P g p := fun g => by
    obtain ⟨c, hc, r, hr, h⟩ := g.2
    exact ⟨(c, r), hc, hr, h⟩
  have inj : Function.Injective (fun g => Classical.choose (hex g)) := by
    intro g g' h
    have h1 := Classical.choose_spec (hex g)
    have h2 := Classical.choose_spec (hex g')
    simp only at h
    rw [← h] at h2
    apply Subtype.ext
    ext x
    have e1 := h1.2.2 (x / (Classical.choose (hex g)).1)
    have e2 := h2.2.2 (x / (Classical.choose (hex g)).1)
    rw [mul_div_cancel₀ _ h1.1] at e1 e2
    rw [e1, e2]
  calc #{g : ℝ →+ ℚ // Crit f g} ≤ #(ℝ × ℚ) := mk_le_of_injective inj
    _ = 𝔠 := by
        rw [mk_prod, lift_id, lift_id, mk_real, mk_eq_aleph0 ℚ]
        exact mul_aleph0_eq aleph0_le_continuum

/-- Generic assembly: if isomorphism of the family is exactly the criterion, there are `2^𝔠` types. -/
theorem count_types_of_crit (η : {f : ℝ →+ ℚ // f ≠ 0} → TopologicalSpace ℝ)
    (hiso : ∀ f g : {f : ℝ →+ ℚ // f ≠ 0}, IsoTop (η f) (η g) → Crit f.1 g.1) :
    #(Quotient (isoSetoid η)) = 2 ^ 𝔠 := by
  refine count_types η card_nonzero_addHom (fun f => ?_)
  refine le_trans (mk_le_of_injective
    (f := fun g : {y : {f : ℝ →+ ℚ // f ≠ 0} // IsoTop (η f) (η y)} =>
      (⟨g.1.1, hiso f g.1 g.2⟩ : {g' : ℝ →+ ℚ // Crit f.1 g'})) ?_) (class_le f.1)
  intro g g' h
  exact Subtype.ext (Subtype.ext (congrArg (fun y : {g' : ℝ →+ ℚ // Crit f.1 g'} => y.1) h))

/-- **Exactly `2^𝔠` isomorphism types in `{β_{f,ℚ} : f ≠ 0}`.** -/
theorem count_beta_types :
    #(Quotient (isoSetoid (fun f : {f : ℝ →+ ℚ // f ≠ 0} => betaT f.1 ratSub))) = 2 ^ 𝔠 :=
  count_types_of_crit _ (fun f g h => (iso_Q_beta f.1 g.1 f.2).1 h)

/-- **Exactly `2^𝔠` isomorphism types in `{σ_{f,ℚ} : f ≠ 0}`.** -/
theorem count_sigma_types :
    #(Quotient (isoSetoid (fun f : {f : ℝ →+ ℚ // f ≠ 0} => sigmaT f.1 ratSub))) = 2 ^ 𝔠 :=
  count_types_of_crit _ (fun f g h => (iso_Q_sigma f.1 g.1 f.2).1 h)

/-- **Exactly `2^𝔠` isomorphism types in `{τ_{f,ℚ} : f ≠ 0}`.** -/
theorem count_tau_types :
    #(Quotient (isoSetoid (fun f : {f : ℝ →+ ℚ // f ≠ 0} => tauT f.1 ratSub))) = 2 ^ 𝔠 :=
  count_types_of_crit _ (fun f g h => (iso_Q_tau f.1 g.1 f.2).1 h)

end LeanCheck
