import LeanCheck.ChainComp1

/-!
# Completions of `σ_{f,S}` and `β_{f,S}` (TVGQ-v7 Theorem `thm:completion`)

`I_S : (ℝ, σ_{f,S}) → ℝ × K_S` and `J_S : (ℝ, β_{f,S}) → K_ℝ × K_S` are topological embeddings with dense
range into locally compact Hausdorff (hence complete) abelian groups, so these are the completions.
Density is Kronecker's theorem (`kronecker_range`) combined with the independence of the mixed characters
`p(c x + f(a x))` (`mixed_zero`), plus density of the joint kernel for the real coordinate.
-/

namespace LeanCheck

open Filter Topology

lemma pd_basic_open {A : Type} [AddCommGroup A] (φ : PD A) (U : Set (PD A)) (hU : IsOpen U)
    (hφ : φ ∈ U) :
    ∃ (F : Finset A) (t : A → Set Circ), (∀ a ∈ F, IsOpen (t a) ∧ φ a ∈ t a) ∧
      ∀ ψ : PD A, (∀ a ∈ F, ψ a ∈ t a) → ψ ∈ U := by
  obtain ⟨V, hV, rfl⟩ := (pd_isInducing A).isOpen_iff.1 hU
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hV (pdFun φ) hφ
  refine ⟨I, u, hu, fun ψ hψ => hsub ?_⟩
  intro a ha
  exact hψ a ha

lemma skT_sum {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (k : ι₁ ⊕ ι₂ → ℤ) (v : ι₁ → Circ)
    (w : ι₂ → Circ) :
    skT k (Sum.elim v w) = ∑ b, k (Sum.inl b) • v b + ∑ a, k (Sum.inr a) • w a := by
  simp [skT, Fintype.sum_sum_type]

/-- Simultaneous approximation of a character `ψ` of `ℝ_d` and a character `φ` of `S_d` by the orbit of `x`. -/
theorem approx_chars (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ)
    (F : Finset ℝ) (F' : Finset S) (ψ : PD ℝ) (φ : PD S) (t : ℝ → Set Circ) (t' : S → Set Circ)
    (ht : ∀ b ∈ F, IsOpen (t b) ∧ ψ b ∈ t b) (ht' : ∀ a ∈ F', IsOpen (t' a) ∧ φ a ∈ t' a) :
    ∃ x : ℝ, (∀ b ∈ F, eHom x b ∈ t b) ∧ (∀ a ∈ F', jHom f S x a ∈ t' a) := by
  classical
  let Ψ : ℝ →+ (({b // b ∈ F} ⊕ {a // a ∈ F'}) → Circ) :=
    { toFun := fun x =>
        Sum.elim (fun b : {b // b ∈ F} => eHom x b.1) (fun a : {a // a ∈ F'} => jHom f S x a.1)
      map_zero' := by funext i; rcases i with i | i <;> simp
      map_add' := by intro x y; funext i; rcases i with i | i <;> simp }
  let s0 : ({b // b ∈ F} ⊕ {a // a ∈ F'}) → Circ :=
    Sum.elim (fun b : {b // b ∈ F} => ψ b.1) (fun a : {a // a ∈ F'} => φ a.1)
  have hs0 : ∀ k : ({b // b ∈ F} ⊕ {a // a ∈ F'}) → ℤ, (∀ x, skT k (Ψ x) = 0) → skT k s0 = 0 := by
    intro k hk
    let c : ℝ := ∑ b : {b // b ∈ F}, k (Sum.inl b) • b.1
    let a' : S := ∑ a : {a // a ∈ F'}, k (Sum.inr a) • a.1
    have hΨ : ∀ x, skT k (Ψ x) = eHom x c + jHom f S x a' := by
      intro x
      show skT k (Sum.elim (fun b : {b // b ∈ F} => eHom x b.1)
        (fun a : {a // a ∈ F'} => jHom f S x a.1)) = _
      rw [skT_sum]
      simp only [c, a', map_sum, map_zsmul]
    have hchi : ∀ x, chiH f c (a' : ℝ) x = 0 := by
      intro x
      have := hk x
      rw [hΨ] at this
      rw [← this, eHom_apply, jHom_apply, chiH]
      exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _
    obtain ⟨hc0, ha0⟩ := mixed_zero f u hu c (a' : ℝ) hchi
    have ha0' : a' = 0 := Subtype.ext ha0
    show skT k (Sum.elim (fun b : {b // b ∈ F} => ψ b.1) (fun a : {a // a ∈ F'} => φ a.1)) = 0
    rw [skT_sum]
    have e1 : ∑ b : {b // b ∈ F}, k (Sum.inl b) • ψ b.1 = ψ c := by
      simp only [c, map_sum, map_zsmul]
    have e2 : ∑ a : {a // a ∈ F'}, k (Sum.inr a) • φ a.1 = φ a' := by
      simp only [a', map_sum, map_zsmul]
    rw [e1, e2, hc0, ha0', map_zero, map_zero, add_zero]
  have hcl : s0 ∈ closure (Set.range Ψ) := kronecker_range Ψ s0 hs0
  let O : Set (({b // b ∈ F} ⊕ {a // a ∈ F'}) → Circ) :=
    Set.pi Set.univ (fun i => Sum.elim (fun b : {b // b ∈ F} => t b.1) (fun a : {a // a ∈ F'} => t' a.1) i)
  have hO : IsOpen O := by
    refine isOpen_set_pi Set.finite_univ (fun i _ => ?_)
    rcases i with i | i
    · exact (ht i.1 i.2).1
    · exact (ht' i.1 i.2).1
  have hs0O : s0 ∈ O := by
    intro i _
    rcases i with i | i
    · exact (ht i.1 i.2).2
    · exact (ht' i.1 i.2).2
  obtain ⟨y, hyO, x, rfl⟩ := mem_closure_iff.1 hcl O hO hs0O
  refine ⟨x, fun b hb => ?_, fun a ha => ?_⟩
  · exact hyO (Sum.inl ⟨b, hb⟩) (Set.mem_univ _)
  · exact hyO (Sum.inr ⟨a, ha⟩) (Set.mem_univ _)

end LeanCheck
