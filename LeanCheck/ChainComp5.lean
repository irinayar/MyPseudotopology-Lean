import LeanCheck.ChainComp4
import LeanCheck.ChainDuality

/-!
# The rational case: metrizability (TVGQ-v7 Corollary `cor:rational`)

For `S = ℚ`, `σ_{f,ℚ}` and `τ_{f,ℚ}` are metrizable while `β_{f,ℚ}` is not.  Metrizability of `σ` and
`τ` follows from the completion embeddings into `ℝ × K_ℚ` and `ℝ × ℝ`.  Non-metrizability of `β` is proved
here for every parameter space `S`: `β_{f,S} = θ_{H_{f,S}}`, and a countable neighbourhood base at `0` would
make `θ_H` equal to `θ_{H₀}` for a countable subgroup `H₀`, whose dual (by the duality fact F1,
`dual_theta_iff`) is `H₀`; but the dual is the uncountable group `H_{f,S}`.
-/

namespace LeanCheck

open Filter Topology

lemma countable_span_int {G : Type} [AddCommGroup G] (s : Set G) (hs : s.Countable) :
    ((Submodule.span ℤ s : Submodule ℤ G) : Set G).Countable := by
  haveI : Countable s := hs.to_subtype
  have : ((Submodule.span ℤ s : Submodule ℤ G) : Set G) ⊆
      Set.range (fun l : s →₀ ℤ => Finsupp.linearCombination ℤ (fun x : s => (x : G)) l) := by
    intro x hx
    have : x ∈ Submodule.span ℤ (Set.range (fun x : s => (x : G))) := by simpa using hx
    obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 this
    exact ⟨l, by simpa [Finsupp.linearCombination_apply] using hl⟩
  exact (Set.countable_range _).mono this

/-- **`β_{f,S}` is not first countable** (hence not metrizable), for every parameter space `S`. -/
theorem beta_not_firstCountable (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    ¬ @FirstCountableTopology ℝ (betaT f S) := by
  intro hfc
  obtain ⟨u, hu⟩ := exists_unit f hf
  have hnhds := @FirstCountableTopology.nhds_generated_countable ℝ (betaT f S) hfc 0
  obtain ⟨B, hB⟩ := @Filter.exists_antitone_basis ℝ (@nhds ℝ (betaT f S) 0) hnhds
  let H : Set Chars := (Hset f S : Set Chars)
  have hβ : betaT f S = theta H := betaT_eq_theta f S
  have hdata : ∀ n, ∃ (I : Finset H) (W : H → Set Circ), (∀ i, W i ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | ∀ i ∈ I, (i : Chars) x ∈ W i} ⊆ B n := by
    intro n
    refine theta_nhds_sub H (B n) ?_
    rw [← hβ]
    exact hB.mem n
  choose I W hW hsub using hdata
  let G0 : Set Chars := ⋃ n, (fun i : H => (i : Chars)) '' (I n : Set H)
  have hG0 : G0.Countable :=
    Set.countable_iUnion fun n => ((I n).finite_toSet.image _).countable
  let H0 : AddSubgroup Chars := (Submodule.span ℤ G0).toAddSubgroup
  have hH0 : (H0 : Set Chars).Countable := countable_span_int G0 hG0
  have hG0H0 : G0 ⊆ (H0 : Set Chars) := fun x hx => Submodule.subset_span hx
  -- every character of `H` is `θ_{H₀}`-continuous
  have hcont : ∀ χ ∈ H, @Continuous ℝ Circ (theta (H0 : Set Chars)) circTop χ := by
    intro χ hχ
    have hχβ : @Continuous ℝ Circ (betaT f S) circTop χ := by
      rw [hβ]; exact theta_cont_of_mem H χ hχ
    haveI := theta_group (H0 : Set Chars)
    have hat : @ContinuousAt ℝ Circ (theta (H0 : Set Chars)) circTop χ 0 := by
      intro V hV
      have h1 : χ ⁻¹' V ∈ @nhds ℝ (betaT f S) 0 :=
        (@Continuous.continuousAt ℝ Circ (betaT f S) circTop χ 0 hχβ) hV
      obtain ⟨n, -, hn⟩ := hB.toHasBasis.mem_iff.1 h1
      have hcyl : {x : ℝ | ∀ i ∈ I n, (i : Chars) x ∈ W n i} ∈ @nhds ℝ (theta (H0 : Set Chars)) 0 := by
        have : {x : ℝ | ∀ i ∈ I n, (i : Chars) x ∈ W n i} =
            ⋂ i ∈ I n, ((i : Chars) : ℝ → Circ) ⁻¹' (W n i) := by
          ext x; simp
        rw [this]
        refine (Filter.biInter_finset_mem (I n)).2 (fun i hi => ?_)
        have hiH0 : (i : Chars) ∈ (H0 : Set Chars) :=
          hG0H0 (Set.mem_iUnion.2 ⟨n, ⟨i, hi, rfl⟩⟩)
        have hc := theta_cont_of_mem (H0 : Set Chars) (i : Chars) hiH0
        have : ((i : Chars) : ℝ → Circ) ⁻¹' (W n i) ∈ @nhds ℝ (theta (H0 : Set Chars)) 0 :=
          (@Continuous.continuousAt ℝ Circ (theta (H0 : Set Chars)) circTop (i : Chars) 0 hc)
            (by rw [map_zero]; exact hW n i)
        exact this
      show χ ⁻¹' V ∈ @nhds ℝ (theta (H0 : Set Chars)) 0
      exact Filter.mem_of_superset hcyl ((hsub n).trans hn)
    exact @continuous_of_continuousAt_zero ℝ (theta (H0 : Set Chars)) _ (theta_group _) Circ Chars _
      circTop' _ _ _ χ hat
  have hmemH0 : ∀ χ ∈ H, χ ∈ H0 := fun χ hχ => (dual_theta_iff H0 χ).1 (hcont χ hχ)
  -- the characters `p(b ·)` form an uncountable subfamily of `H`
  let chiB : ℝ → Chars := fun b => cmulHom b
  have hchiH : ∀ b, chiB b ∈ H := by
    intro b
    refine ⟨b, 0, S.zero_mem, fun x => ?_⟩
    simp [chiB, cmulHom_apply, chiH]
  have hinj : Function.Injective chiB := by
    intro b b' h
    have := mixed_zero f u hu (b - b') 0 (fun x => by
      have hx := congrArg (fun χ : Chars => χ x) h
      simp only [chiB, cmulHom_apply] at hx
      simp only [chiH, zero_mul, map_zero, Rat.cast_zero, add_zero, sub_mul]
      rw [AddCircle.coe_sub (𝕜 := ℝ) (p := (1 : ℝ)), hx, sub_self])
    exact sub_eq_zero.1 this.1
  haveI : Countable (H0 : Set Chars) := hH0.to_subtype
  let g : ℝ → (H0 : Set Chars) := fun b => ⟨chiB b, hmemH0 _ (hchiH b)⟩
  have hg : Function.Injective g := fun b b' h => hinj (congrArg Subtype.val h)
  haveI : Countable ℝ := hg.countable
  exact Cardinal.not_countable_real Set.countable_univ

theorem beta_not_metrizable (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    ¬ @TopologicalSpace.MetrizableSpace ℝ (betaT f S) := by
  intro h
  apply beta_not_firstCountable f hf S
  letI : TopologicalSpace ℝ := betaT f S
  haveI : TopologicalSpace.MetrizableSpace ℝ := h
  infer_instance

/-! ### Metrizability of `σ_{f,ℚ}` and `τ_{f,ℚ}` -/

instance ratSub_countable : Countable ratSub := by
  have : Function.Surjective (fun q : ℚ => (⟨(q : ℝ), (mem_ratSub _).2 ⟨q, rfl⟩⟩ : ratSub)) := by
    intro a
    obtain ⟨q, hq⟩ := (mem_ratSub a.1).1 a.2
    exact ⟨q, Subtype.ext hq.symm⟩
  exact this.countable

instance PD_metrizable (A : Type) [AddCommGroup A] [Countable A] :
    TopologicalSpace.MetrizableSpace (PD A) :=
  (Topology.IsEmbedding.mk (pd_isInducing A) (pd_injective A)).metrizableSpace

theorem sigma_metrizable_Q (f : ℝ →+ ℚ) :
    @TopologicalSpace.MetrizableSpace ℝ (sigmaT f ratSub) := by
  have hemb : @Topology.IsEmbedding ℝ (ℝ × PD ratSub) (sigmaT f ratSub) _ (ISigma f ratSub) :=
    @Topology.IsEmbedding.mk ℝ (ℝ × PD ratSub) (sigmaT f ratSub) _ _ (ISigma_inducing f ratSub)
      (fun x y h => congrArg Prod.fst h)
  exact @Topology.IsEmbedding.metrizableSpace ℝ (ℝ × PD ratSub) (sigmaT f ratSub) _ _ _ hemb

theorem tau_metrizable_Q (f : ℝ →+ ℚ) :
    @TopologicalSpace.MetrizableSpace ℝ (tauT f ratSub) := by
  have hS : Submodule.span ℚ (Set.range (fun _ : Unit => (1 : ℝ))) = ratSub := by
    rw [Set.range_const]; rfl
  have hemb : @Topology.IsEmbedding ℝ (ℝ × (Unit → ℝ)) (tauT f ratSub) _
      (GTau f (fun _ : Unit => (1 : ℝ))) :=
    @Topology.IsEmbedding.mk ℝ (ℝ × (Unit → ℝ)) (tauT f ratSub) _ _ (GTau_inducing f ratSub _ hS)
      (fun x y h => congrArg Prod.fst h)
  exact @Topology.IsEmbedding.metrizableSpace ℝ (ℝ × (Unit → ℝ)) (tauT f ratSub) _ _ _ hemb

/-! ### The rational case, assembled -/

theorem completion_rational (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    (@IsInducing ℝ (PD ℝ × PD ratSub) (betaT f ratSub) _ (JBeta f ratSub) ∧
        DenseRange (JBeta f ratSub) ∧ CompleteSpace (PD ℝ × PD ratSub)) ∧
    (@IsInducing ℝ (ℝ × PD ratSub) (sigmaT f ratSub) _ (ISigma f ratSub) ∧
        DenseRange (ISigma f ratSub) ∧ CompleteSpace (ℝ × PD ratSub)) ∧
    (@IsInducing ℝ (ℝ × (Unit → ℝ)) (tauT f ratSub) _ (GTau f (fun _ : Unit => (1 : ℝ))) ∧
        DenseRange (GTau f (fun _ : Unit => (1 : ℝ))) ∧ CompleteSpace (ℝ × (Unit → ℝ))) ∧
    @TopologicalSpace.MetrizableSpace ℝ (sigmaT f ratSub) ∧
    @TopologicalSpace.MetrizableSpace ℝ (tauT f ratSub) ∧
    ¬ @TopologicalSpace.MetrizableSpace ℝ (betaT f ratSub) := by
  have hS : Submodule.span ℚ (Set.range (fun _ : Unit => (1 : ℝ))) = ratSub := by
    rw [Set.range_const]; rfl
  obtain ⟨h1, h2, h3, -, -⟩ := completion_beta f hf ratSub
  obtain ⟨k1, k2, k3, -, -⟩ := completion_sigma f hf ratSub
  have hli : LinearIndependent ℚ (fun _ : Unit => (1 : ℝ)) :=
    LinearIndependent.of_subsingleton () one_ne_zero
  obtain ⟨t1, t2, t3⟩ := completion_tau f hf ratSub (fun _ : Unit => (1 : ℝ)) hli hS
  exact ⟨⟨h1, h2, inferInstance⟩, ⟨k1, k2, k3⟩, ⟨t1, t2, t3⟩, sigma_metrizable_Q f,
    tau_metrizable_Q f, beta_not_metrizable f hf ratSub⟩

end LeanCheck
