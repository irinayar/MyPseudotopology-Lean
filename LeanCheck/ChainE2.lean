import LeanCheck.ChainE1

/-!
# Least compatible topologies, and a necessary condition for a greatest member
(HamelCharactersTVG_v18 Proposition 16.1 `prop:compatible`, Proposition 26.5 `prop:necessary-v13`)

* `lqc_circ`, `lqc_betaT`, `lqc_sigmaT` : local quasi-convexity of the circle and of `β_f`, `σ_f`;
* `sigma_mem_Kcls`                      : `σ_f ∈ 𝒞_f`;
* `beta_least`, `sigma_least`           : `β_f` is the least (coarsest) Hausdorff group topology with character group `H_f`;
  `σ_f` is the least one also containing the usual topology;
* `additive_dual`                       : for a compatible `η`, every continuous additive `η → ℝ_usual` is `x ↦ c x`, and
  a nonzero one exists iff `tu ⊆ η`;
* `necessary_condition`                 : if `𝒞_f` has a greatest member `μ`, then `tu ⊆ μ`, and for every `η ∈ 𝒞_f` the
  joins `η ∨ tu` and `η ∨ σ_f` coincide and have character group exactly `H_f`.
-/

namespace LeanCheck

open Filter Topology

section LQCCircle

/-- The circle with its usual topology is locally quasi-convex. -/
lemma lqc_circ : LocQC circTop := by
  intro V hV
  have hV' : V ∈ 𝓝 (0 : Circ) := hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV'
  obtain ⟨n, hn1, hnε⟩ := exists_R ε hε
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨{y : Circ | ∀ j : ℕ, j ≤ n → ‖j • y‖ ≤ 1 / 4}, ?_, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((NormedAddGroup.nhds_zero_basis_norm_lt).mem_of_mem (show 0 < 1 / (4 * (n : ℝ)) by positivity)) ?_
    intro y hy j hj
    have h1 : ‖y‖ < 1 / (4 * (n : ℝ)) := hy
    calc ‖j • y‖ ≤ j * ‖y‖ := norm_nsmul_le
      _ ≤ n * (1 / (4 * (n : ℝ))) := mul_le_mul (by exact_mod_cast hj) h1.le (norm_nonneg _) (Nat.cast_nonneg n)
      _ = 1 / 4 := by field_simp
  · intro y hy
    apply hεV
    rw [Metric.mem_ball, dist_zero_right]
    have := mult_le y n hy
    have h2 : ‖y‖ ≤ 1 / (4 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact lt_of_le_of_lt h2 hnε
  · intro x hx
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hx
    obtain ⟨j, hj, hlt⟩ := hx
    let χ : Circ →+ Circ := j • AddMonoidHom.id Circ
    refine ⟨χ, ?_, fun y hy => hy j hj, hlt⟩
    show Continuous (fun y : Circ => j • y)
    exact continuous_nsmul j

lemma lqc_betaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : LocQC (betaT f S) := by
  unfold betaT
  exact lqc_inf _ _ (lqc_iInf _ (fun b => lqc_induced (cmulHom b) circTop lqc_circ))
    (lqc_iInf _ (fun a : S => lqc_induced (pfHom f (a : ℝ)) circTop lqc_circ))

lemma lqc_sigmaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : LocQC (sigmaT f S) := by
  rw [sigmaT_eq]
  exact lqc_inf _ _ lqc_uR (lqc_betaT f S)

end LQCCircle

lemma cmul_cont_uR (r : ℝ) : @Continuous ℝ Circ uR circTop (cmulHom r) := by
  unfold uR
  exact continuous_coe_circ.comp (continuous_const.mul continuous_id)

section Compatible

variable (f : ℝ →+ ℚ)

lemma cmulHom_memF (b : ℝ) : cmulHom b ∈ (Hset f ⊤ : Set Chars) :=
  ⟨b, 0, trivial, fun x => by simp [chiH, cmulHom_apply]⟩

/-- `σ_f ∈ 𝒞_f`. -/
theorem sigma_mem_Kcls (u : ℝ) (hu : f u = 1) :
    sigmaT f ⊤ ∈ Kcls (Hset f ⊤ : Set Chars) realDil := by
  refine ⟨sigmaT_group f ⊤, TfS_t2 f ⊤ gamma0, lqc_sigmaT f ⊤, fun χ => dual_sigma f ⊤ χ, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (scalar_sigma f u hu ⊤ a).2 (fun b _ => Submodule.mem_top)

/-- **Proposition 16.1 (first part).**  `β_f` is the least Hausdorff group topology with character group `H_f`:
any group topology `η` whose characters include `H_f` is finer than `β_f`. -/
theorem beta_least (η : TopologicalSpace ℝ)
    (hcont : ∀ χ ∈ (Hset f ⊤ : Set Chars), @Continuous ℝ Circ η circTop χ) : η ≤ betaT f ⊤ := by
  unfold betaT
  refine le_inf (le_iInf fun b => ?_) (le_iInf fun a => ?_)
  · exact continuous_iff_le_induced.1 (hcont _ (cmulHom_memF f b))
  · exact continuous_iff_le_induced.1 (hcont (pfHom f (a : ℝ)) ⟨0, (a : ℝ), trivial, fun x => by simp [pfHom_apply, chiH]⟩)

/-- **Proposition 16.1 (second part).**  `σ_f` is the least such topology that also contains `tu`. -/
theorem sigma_least (η : TopologicalSpace ℝ)
    (hcont : ∀ χ ∈ (Hset f ⊤ : Set Chars), @Continuous ℝ Circ η circTop χ)
    (huη : η ≤ uR) : η ≤ sigmaT f ⊤ := by
  rw [sigmaT_eq]
  exact le_inf huη (beta_least f η hcont)

/-- **Proposition 16.1 (third part).**  For `η` with character group `H_f`, every continuous additive map
`(ℝ, η) → ℝ_usual` is `x ↦ c x`; a nonzero one exists iff `tu ⊆ η` (i.e. `η ≤ uR`). -/
theorem additive_dual (η : TopologicalSpace ℝ)
    (hdual : ∀ χ : Chars, @Continuous ℝ Circ η circTop χ ↔ χ ∈ (Hset f ⊤ : Set Chars)) :
    (∀ L : ℝ →+ ℝ, Continuous[η, uR] L → ∃ c : ℝ, ∀ x, L x = c * x) ∧
    ((∃ L : ℝ →+ ℝ, L ≠ 0 ∧ Continuous[η, uR] L) ↔
      η ≤ uR) := by
  have hrig : ∀ L : ℝ →+ ℝ, Continuous[η, uR] L →
      ∃ c : ℝ, ∀ x, L x = c * x := by
    intro L hL
    refine rigidity_abstract f f ⊤ ⊤ η uR (fun χ => ?_) (fun r => ?_) L hL
    · exact (hdual χ).trans Iff.rfl
    · exact cmul_cont_uR r
  refine ⟨hrig, ⟨?_, fun hle => ?_⟩⟩
  · rintro ⟨L, hL0, hL⟩
    obtain ⟨c, hc⟩ := hrig L hL
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hL0 (AddMonoidHom.ext fun x => by simp [hc x])
    have hLfun : (L : ℝ → ℝ) = fun x => c * x := funext hc
    rw [hLfun] at hL
    have : Continuous[η, uR] (id : ℝ → ℝ) := by
      have e : (id : ℝ → ℝ) = (fun y => c⁻¹ * y) ∘ (fun x => c * x) := by
        funext x; simp only [Function.comp, id]; field_simp
      rw [e]
      exact @Continuous.comp ℝ ℝ ℝ η uR uR _ _ (uR_dil c⁻¹) hL
    have h2 := continuous_iff_le_induced.1 this
    rwa [@induced_id ℝ uR] at h2
  · refine ⟨AddMonoidHom.id ℝ, fun h => ?_, ?_⟩
    · have := congrArg (fun m : ℝ →+ ℝ => m 1) h
      simp at this
    · exact continuous_id_of_le hle

/-- **Proposition 26.5.**  Suppose `𝒞_f` has a greatest member `μ`.  Then `tu ⊆ μ`, and for every `η ∈ 𝒞_f` the joins
`η ∨ tu` and `η ∨ σ_f` coincide and have character group exactly `H_f`. -/
theorem necessary_condition (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil)
    (hgr : ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ) :
    μ ≤ uR ∧ ∀ η ∈ Kcls (Hset f ⊤ : Set Chars) realDil, η ⊓ uR = η ⊓ sigmaT f ⊤ ∧
      ∀ χ : Chars, @Continuous ℝ Circ (η ⊓ uR) circTop χ ↔ χ ∈ (Hset f ⊤ : Set Chars) := by
  have hσ := sigma_mem_Kcls f u hu
  have hμσ : μ ≤ sigmaT f ⊤ := hgr _ hσ
  have hμu : μ ≤ uR := hμσ.trans (sigmaT_le_usual f ⊤)
  refine ⟨hμu, fun η hη => ⟨?_, fun χ => ?_⟩⟩
  · have hηβ : η ≤ betaT f ⊤ := beta_least f η (fun χ hχ => (hη.2.2.2.1 χ).2 hχ)
    have e : sigmaT f ⊤ = uR ⊓ betaT f ⊤ := sigmaT_eq f ⊤
    rw [e, ← inf_assoc, inf_comm η uR, inf_assoc, inf_eq_left.2 hηβ]
  · constructor
    · intro hc
      exact (hμ.2.2.2.1 χ).1 (continuous_le_dom (le_inf (hgr _ hη) hμu) hc)
    · intro hχ
      exact continuous_le_dom inf_le_left ((hη.2.2.2.1 χ).2 hχ)

end Compatible

end LeanCheck
