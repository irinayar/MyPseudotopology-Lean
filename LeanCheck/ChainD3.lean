import LeanCheck.ChainD2

/-!
# Real dilations, continued
(HamelCharactersTVG_v18 Lemma 26.1 second part, Proposition 26.3, Corollary 26.4)
-/

namespace LeanCheck

open Filter Topology

section RealDilations2

/-- The ordinary character `x ↦ p(s x)`. -/
noncomputable def scalChar (s : ℝ) : Chars :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (AddMonoidHom.mulLeft s)

lemma scalChar_apply (s x : ℝ) : scalChar s x = ((s * x : ℝ) : Circ) := rfl

lemma scalChar_mem (f : ℝ →+ ℚ) (s : ℝ) : scalChar s ∈ (Hset f ⊤ : Set Chars) :=
  ⟨s, 0, trivial, fun x => by simp [scalChar_apply, chiH]⟩

/-- **Lemma 26.1, second part.**  An additive bijection `φ` of `ℝ` with `χ ∘ φ ∈ H_f` for all `χ ∈ H_f` is a real
scalar multiplication. -/
theorem aut_converse (f : ℝ →+ ℚ) (φ : ℝ →+ ℝ) (hφ : Function.Bijective φ)
    (h : ∀ χ ∈ (Hset f ⊤ : Set Chars), ∃ c a : ℝ, ∀ x : ℝ, χ (φ x) = chiH f c a x) :
    ∃ d : ℝ, d ≠ 0 ∧ ∀ x : ℝ, φ x = d * x := by
  -- for each real `s`, `s φ = c_s id + f_{a_s}`
  have key : ∀ s : ℝ, ∃ c a : ℝ, ∀ x : ℝ, s * φ x = c * x + ((f (a * x) : ℚ) : ℝ) := by
    intro s
    obtain ⟨c, a, hca⟩ := h (scalChar s) (scalChar_mem f s)
    refine ⟨c, a, ?_⟩
    let g : ℝ →+ ℝ := (AddMonoidHom.mulLeft s).comp φ
    let hh : ℝ →+ ℝ := (AddMonoidHom.mulLeft c) + faR f a
    have hgh : ∀ x : ℝ, ((g x : ℝ) : Circ) = ((hh x : ℝ) : Circ) := by
      intro x
      have := hca x
      rw [scalChar_apply] at this
      unfold chiH at this
      simpa [g, hh, faR_apply] using this
    have := lift_unique g hh hgh
    intro x
    have := congrArg (fun m : ℝ →+ ℝ => m x) this
    simpa [g, hh, faR_apply] using this
  obtain ⟨d, a, hda⟩ := key 1
  obtain ⟨e, b, heb⟩ := key (Real.sqrt 2)
  have hφx : ∀ x, φ x = d * x + ((f (a * x) : ℚ) : ℝ) := fun x => by simpa using hda x
  have hrel : ∀ x : ℝ, (Real.sqrt 2 * d - e) * x =
      ((f (b * x) : ℚ) : ℝ) - Real.sqrt 2 * ((f (a * x) : ℚ) : ℝ) := by
    intro x
    have h1 := heb x
    rw [hφx x] at h1
    linarith
  have hk : Real.sqrt 2 * d - e = 0 := by
    by_contra hk
    have hcount : (Set.univ : Set ℝ).Countable := by
      have : (Set.univ : Set ℝ) ⊆ Set.range (fun p : ℚ × ℚ => (p.1 : ℝ) - Real.sqrt 2 * (p.2 : ℝ)) := by
        intro y _
        refine ⟨(f (b * (y / (Real.sqrt 2 * d - e))), f (a * (y / (Real.sqrt 2 * d - e)))), ?_⟩
        have := hrel (y / (Real.sqrt 2 * d - e))
        rw [mul_div_cancel₀ _ hk] at this
        simp only
        exact this.symm
      exact (Set.countable_range _).mono this
    exact Cardinal.not_countable_real hcount
  have hfa : ∀ x : ℝ, f (a * x) = 0 := by
    intro x
    by_contra hne
    have h0 := hrel x
    rw [hk, zero_mul] at h0
    have hq : Real.sqrt 2 = (((f (b * x)) / (f (a * x)) : ℚ) : ℝ) := by
      have hne' : ((f (a * x) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
      rw [Rat.cast_div, eq_div_iff hne']
      linarith
    exact irrational_sqrt_two ⟨_, hq.symm⟩
  have hdφ : ∀ x, φ x = d * x := fun x => by rw [hφx x, hfa x]; simp
  refine ⟨d, ?_, hdφ⟩
  rintro rfl
  have : φ 1 = φ 0 := by rw [hdφ 1, hdφ 0]; simp
  have := hφ.1 this
  norm_num at this

/-- The continuous scalar ring `C_η`. -/
def Ceta (η : TopologicalSpace ℝ) : Set ℝ := {r | Continuous[η, η] (fun x : ℝ => r * x)}

lemma zero_mem_Ceta (η : TopologicalSpace ℝ) : (0 : ℝ) ∈ Ceta η := by
  show Continuous[η, η] (fun x : ℝ => 0 * x)
  simp only [zero_mul]
  exact continuous_const

lemma one_mem_Ceta (η : TopologicalSpace ℝ) : (1 : ℝ) ∈ Ceta η := by
  show Continuous[η, η] (fun x : ℝ => 1 * x)
  simp only [one_mul]
  exact continuous_id

lemma mul_mem_Ceta {η : TopologicalSpace ℝ} {r s : ℝ} (hr : r ∈ Ceta η) (hs : s ∈ Ceta η) : r * s ∈ Ceta η := by
  show Continuous[η, η] (fun x : ℝ => r * s * x)
  have e : (fun x : ℝ => r * s * x) = (fun x : ℝ => r * x) ∘ (fun x : ℝ => s * x) := by
    funext x; simp only [Function.comp]; ring
  rw [e]
  exact @Continuous.comp ℝ ℝ ℝ η η η _ _ hr hs

/-- **Proposition 26.3, first part**: `ρ_r(η) ⊆ ρ_t(η)` (i.e. `ρ_t ≤ ρ_r`) iff `r/t ∈ C_η`. -/
theorem rho_le_iff (r t : ℝ) (hr : r ≠ 0) (ht : t ≠ 0) (η : TopologicalSpace ℝ) :
    rho t η ≤ rho r η ↔ r / t ∈ Ceta η := by
  show _ ↔ Continuous[η, η] (fun x : ℝ => r / t * x)
  rw [continuous_iff_le_induced]
  constructor
  · intro h
    have := induced_mono (g := fun x : ℝ => t⁻¹ * x) h
    unfold rho at this
    rw [induced_compose, induced_compose] at this
    have e1 : ((fun x : ℝ => t * x) ∘ fun x : ℝ => t⁻¹ * x) = id := by
      funext x; show t * (t⁻¹ * x) = x; field_simp
    have e2 : ((fun x : ℝ => r * x) ∘ fun x : ℝ => t⁻¹ * x) = fun x : ℝ => r / t * x := by
      funext x; show r * (t⁻¹ * x) = r / t * x; ring
    rw [e1, e2, induced_id] at this
    exact this
  · intro h
    have := induced_mono (g := fun x : ℝ => t * x) h
    unfold rho
    rw [induced_compose] at this
    have e : ((fun x : ℝ => r / t * x) ∘ fun x : ℝ => t * x) = fun x : ℝ => r * x := by
      funext x; show r / t * (t * x) = r * x; field_simp
    rw [e] at this
    exact this

/-- `Frac(C_η) = ℝ`: every real is a quotient of two elements of `C_η`. -/
def FracAll (η : TopologicalSpace ℝ) : Prop :=
  ∀ x : ℝ, ∃ a b : ℝ, a ∈ Ceta η ∧ b ∈ Ceta η ∧ b ≠ 0 ∧ x = a / b

/-- **Proposition 26.3, second part**: the family `{ρ_r(η)}` is directed iff the fraction field of `C_η` is `ℝ`. -/
theorem rho_directed_iff (η : TopologicalSpace ℝ) :
    Directed (· ≥ ·) (fun r : {r : ℝ // r ≠ 0} => rho r.1 η) ↔ FracAll η := by
  constructor
  · intro hdir x
    by_cases hx : x = 0
    · exact ⟨0, 1, zero_mem_Ceta η, one_mem_Ceta η, one_ne_zero, by simp [hx]⟩
    · obtain ⟨t, h1, h2⟩ := hdir ⟨x, hx⟩ ⟨1, one_ne_zero⟩
      have ht := t.2
      have h1' : x / t.1 ∈ Ceta η := (rho_le_iff x t.1 hx ht η).1 h1
      have h2' : 1 / t.1 ∈ Ceta η := (rho_le_iff 1 t.1 one_ne_zero ht η).1 h2
      refine ⟨x / t.1, 1 / t.1, h1', h2', one_div_ne_zero ht, ?_⟩
      field_simp
  · intro hfrac r s
    obtain ⟨a, b, ha, hb, hb0, hr⟩ := hfrac r.1
    obtain ⟨c, d, hc, hd, hd0, hs⟩ := hfrac s.1
    have hr0 := r.2
    have hs0 := s.2
    have ha0 : a ≠ 0 := by
      rintro rfl; apply hr0; rw [hr]; simp
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hs0; rw [hs]; simp
    have ht0 : (1 / (b * d)) ≠ 0 := one_div_ne_zero (mul_ne_zero hb0 hd0)
    refine ⟨⟨1 / (b * d), ht0⟩, ?_, ?_⟩
    · refine (rho_le_iff r.1 (1 / (b * d)) hr0 ht0 η).2 ?_
      have : r.1 / (1 / (b * d)) = a * d := by rw [hr]; field_simp
      rw [this]; exact mul_mem_Ceta ha hd
    · refine (rho_le_iff s.1 (1 / (b * d)) hs0 ht0 η).2 ?_
      have : s.1 / (1 / (b * d)) = c * b := by rw [hs]; field_simp
      rw [this]; exact mul_mem_Ceta hc hb

/-- **Corollary 26.4 (real saturation).**  If `η ∈ ℒ_f` and `Frac(C_η) = ℝ`, then `η^[ℝ] = ⋁_{r ≠ 0} ρ_r(η)` lies in
`𝒞_f`, is contained in `η`, and is the least TVG topology containing `η`. -/
theorem real_saturation {H : Set (ℝ →+ Circ)} (hH : DilInv H) (η : TopologicalSpace ℝ)
    (hη : η ∈ Kcls H ∅) (hfrac : FracAll η) :
    (⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η) ∈ Kcls H realDil ∧ (⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η) ≤ η ∧
      ∀ τ : TopologicalSpace ℝ, (∀ a : ℝ, Continuous[τ, τ] (fun x : ℝ => a * x)) → τ ≤ η →
        τ ≤ ⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η := by
  haveI : Nonempty {r : ℝ // r ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hjoin := directed_join_mem H ∅ (ι := {r : ℝ // r ≠ 0}) (fun r => rho r.1 η)
    ((rho_directed_iff η).2 hfrac) (fun r => rho_mem hH r.1 r.2 η hη)
  have hdil : ∀ s ∈ realDil, Continuous[⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η, ⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η] s := by
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = 0
    · subst ha
      simp only [zero_mul]
      exact @continuous_const ℝ ℝ (⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η) (⨅ r : {r : ℝ // r ≠ 0}, rho r.1 η) 0
    · rw [continuous_iff_le_induced, induced_iInf]
      refine le_iInf fun t => ?_
      have e : TopologicalSpace.induced (fun x : ℝ => a * x) (rho t.1 η) = rho (t.1 * a) η := by
        unfold rho
        rw [induced_compose]
        congr 1
        funext x
        simp only [Function.comp]
        ring
      rw [e]
      exact iInf_le (fun r : {r : ℝ // r ≠ 0} => rho r.1 η) ⟨t.1 * a, mul_ne_zero t.2 ha⟩
  refine ⟨⟨hjoin.1, hjoin.2.1, hjoin.2.2.1, hjoin.2.2.2.1, hdil⟩, ?_, ?_⟩
  · have := iInf_le (fun r : {r : ℝ // r ≠ 0} => rho r.1 η) ⟨1, one_ne_zero⟩
    rwa [rho_one] at this
  · intro τ hτ hle
    refine le_iInf fun r => ?_
    unfold rho
    exact (continuous_iff_le_induced.1 (hτ r.1)).trans (induced_mono hle)

/-- **Corollary 26.6, first implication.**  If the unrestricted class `ℒ_f` has a greatest member, so does the TVG
class `𝒞_f` (and they coincide). -/
theorem mackey_implies_conjecture (f : ℝ →+ ℚ) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Kcls (Hset f ⊤ : Set Chars) ∅) (hgr : ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) ∅, μ ≤ τ) :
    μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil ∧ ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ :=
  automatic_tvg (Hf_dilInv f) μ hμ hgr

end RealDilations2

end LeanCheck
