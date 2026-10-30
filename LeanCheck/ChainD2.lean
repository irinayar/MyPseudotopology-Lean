import LeanCheck.ChainD1

/-!
# Real dilations and the Mackey problem for the Hamel pair
(HamelCharactersTVG_v18 §26: Lemma 26.1 `lem:aut-v13`, Proposition 26.2 `prop:automatic-tvg-v13`,
 Proposition 26.3 `prop:order-v13`, Corollary 26.4 `cor:real-saturation-v13`)

`H_f = Hset f ⊤` is the set of characters `x ↦ p(c x + f(a x))`.  For a group topology `η` on `ℝ` and a real `r ≠ 0`
put `ρ_r(η) = {m_r⁻¹(U) : U ∈ η}` (`rho r η`, the topology induced by `m_r : x ↦ r x`).

* `Hf_dilInv`, `aut_converse`  : `{χ ∘ m_r} = H_f`, and an additive bijection preserving `H_f` is a real scalar;
* `automatic_tvg`              : a greatest member of `ℒ_f` is a TVG topology and the greatest member of `𝒞_f`;
* `rho_order`, `rho_directed_iff` : `ρ_r(η) ⊆ ρ_t(η)` iff `r/t ∈ C_η`; the family is directed iff `Frac(C_η) = ℝ`;
* `real_saturation`            : if `Frac(C_η) = ℝ` then `⋁_r ρ_r(η) ∈ 𝒞_f` is the least TVG topology containing `η`.
-/

namespace LeanCheck

open Filter Topology

section RealDilations

/-- The set of real scalar maps `x ↦ a x`. -/
def realDil : Set (ℝ → ℝ) := Set.range (fun a : ℝ => fun x : ℝ => a * x)

/-- The topology induced by `m_r : x ↦ r x`. -/
def rho (r : ℝ) (η : TopologicalSpace ℝ) : TopologicalSpace ℝ :=
  TopologicalSpace.induced (fun x : ℝ => r * x) η

/-- `H` is invariant under composition with every nonzero dilation. -/
def DilInv (H : Set (ℝ →+ Circ)) : Prop :=
  ∀ r : ℝ, r ≠ 0 → ∀ χ : ℝ →+ Circ, χ ∈ H ↔ χ.comp (AddMonoidHom.mulLeft r) ∈ H

lemma rho_one (η : TopologicalSpace ℝ) : rho 1 η = η := by
  unfold rho
  simp only [one_mul]
  exact induced_id

lemma rho_rho (r t : ℝ) (η : TopologicalSpace ℝ) : rho r (rho t η) = rho (t * r) η := by
  unfold rho
  rw [induced_compose]
  congr 1
  funext x
  simp only [Function.comp]
  ring

/-- `χ` is `ρ_r(η)`-continuous iff `χ ∘ m_{1/r}` is `η`-continuous. -/
lemma cont_rho_iff (r : ℝ) (hr : r ≠ 0) (η : TopologicalSpace ℝ) (χ : ℝ →+ Circ) :
    @Continuous ℝ Circ (rho r η) circTop χ ↔
      @Continuous ℝ Circ η circTop (χ.comp (AddMonoidHom.mulLeft r⁻¹)) := by
  have e1 : (fun x : ℝ => r⁻¹ * (r * x)) = id := by funext x; show r⁻¹ * (r * x) = x; field_simp
  have e2 : (fun x : ℝ => r * (r⁻¹ * x)) = id := by funext x; show r * (r⁻¹ * x) = x; field_simp
  constructor
  · intro h
    rw [continuous_iff_le_induced] at h ⊢
    have := induced_mono (g := fun x : ℝ => r⁻¹ * x) h
    unfold rho at this
    rw [induced_compose, induced_compose] at this
    have e3 : ((fun x : ℝ => r * x) ∘ fun x : ℝ => r⁻¹ * x) = id := by funext x; show r * (r⁻¹ * x) = x; field_simp
    rw [e3, induced_id] at this
    exact this
  · intro h
    rw [continuous_iff_le_induced] at h ⊢
    have := induced_mono (g := fun x : ℝ => r * x) h
    rw [induced_compose] at this
    have e4 : ((χ.comp (AddMonoidHom.mulLeft r⁻¹) : ℝ → Circ) ∘ fun x : ℝ => r * x) = χ := by
      funext x
      simp only [Function.comp, AddMonoidHom.coe_comp, AddMonoidHom.coe_mulLeft]
      rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul] <;> rfl
    rw [e4] at this
    exact this

lemma Hf_dilInv (f : ℝ →+ ℚ) : DilInv (Hset f ⊤ : Set Chars) := by
  have key : ∀ r : ℝ, ∀ χ : ℝ →+ Circ, χ ∈ (Hset f ⊤ : Set Chars) →
      χ.comp (AddMonoidHom.mulLeft r) ∈ (Hset f ⊤ : Set Chars) := by
    rintro r χ ⟨c, a, -, h⟩
    refine ⟨r * c, r * a, trivial, fun x => ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp, AddMonoidHom.coe_mulLeft]
    rw [h]
    unfold chiH
    congr 1
    rw [show a * (r * x) = r * a * x by ring]
    push_cast
    ring
  intro r hr χ
  constructor
  · exact key r χ
  · intro h
    have := key r⁻¹ _ h
    have e : (χ.comp (AddMonoidHom.mulLeft r)).comp (AddMonoidHom.mulLeft r⁻¹) = χ := by
      ext x
      simp only [AddMonoidHom.coe_comp, Function.comp, AddMonoidHom.coe_mulLeft]
      rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
    rwa [e] at this

lemma rho_mem {H : Set (ℝ →+ Circ)} (hH : DilInv H) (r : ℝ) (hr : r ≠ 0) (η : TopologicalSpace ℝ)
    (hη : η ∈ Kcls H ∅) : rho r η ∈ Kcls H ∅ := by
  refine ⟨?_, ?_, ?_, ?_, fun s hs => absurd hs (Set.notMem_empty s)⟩
  · letI := η; haveI := hη.1
    exact isTopologicalAddGroup_induced (AddMonoidHom.mulLeft r)
  · letI := η; haveI := hη.2.1
    have hemb : @Topology.IsEmbedding ℝ ℝ (rho r η) η (fun x : ℝ => r * x) :=
      @Topology.IsEmbedding.mk ℝ ℝ (rho r η) η (fun x : ℝ => r * x)
        (@Topology.IsInducing.mk ℝ ℝ (rho r η) η (fun x : ℝ => r * x) rfl)
        (fun a b hab => mul_left_cancel₀ hr hab)
    exact @Topology.IsEmbedding.t2Space ℝ ℝ (rho r η) η hη.2.1 (fun x : ℝ => r * x) hemb
  · exact lqc_induced (AddMonoidHom.mulLeft r) η hη.2.2.1
  · intro χ
    rw [cont_rho_iff r hr η χ, hη.2.2.2.1]
    have := hH r⁻¹ (inv_ne_zero hr) χ
    exact this.symm

/-- **Proposition 26.2.**  If `ℒ_f` has a greatest member `μ`, then `μ` is a TVG topology (so lies in `𝒞_f`) and is
the greatest member of `𝒞_f`. -/
theorem automatic_tvg {H : Set (ℝ →+ Circ)} (hH : DilInv H) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Kcls H ∅) (hgr : ∀ τ ∈ Kcls H ∅, μ ≤ τ) :
    μ ∈ Kcls H realDil ∧ ∀ τ ∈ Kcls H realDil, μ ≤ τ := by
  have hdil : ∀ s ∈ realDil, Continuous[μ, μ] s := by
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = 0
    · subst ha
      simp only [zero_mul]
      exact continuous_const
    · have := hgr (rho a μ) (rho_mem hH a ha μ hμ)
      rw [continuous_iff_le_induced]
      exact this
  refine ⟨⟨hμ.1, hμ.2.1, hμ.2.2.1, hμ.2.2.2.1, hdil⟩, fun τ hτ => hgr τ ⟨hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2.1,
    fun s hs => absurd hs (Set.notMem_empty s)⟩⟩

end RealDilations

end LeanCheck
