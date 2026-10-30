import LeanCheck.ChainPW1

/-!
# Peter–Weyl, part 2: integral operators with continuous kernel are compact

The span of the tensors `a(x) b(y)` is a point-separating star subalgebra of `C(K × K, ℂ)`, hence dense
(Stone–Weierstrass); the operators with tensor kernels have rank one, and the set of kernels with compact
operator is closed because `k ↦ T_k` is bounded.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LeanCheck
namespace PW

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- The span of the tensors. -/
noncomputable def tensorSpan (K : Type) [TopologicalSpace K] [CompactSpace K] : Submodule ℂ C(K × K, ℂ) :=
  Submodule.span ℂ (Set.range (fun p : C(K, ℂ) × C(K, ℂ) => tensor p.1 p.2))

lemma tensor_mul (a b a' b' : C(K, ℂ)) : tensor a b * tensor a' b' = tensor (a * a') (b * b') := by
  ext p; simp [tensor_apply]; ring

lemma tensor_star (a b : C(K, ℂ)) : star (tensor a b) = tensor (star a) (star b) := by
  ext p; simp [tensor_apply]

lemma tensor_one : (tensor (1 : C(K, ℂ)) 1) = 1 := by
  ext p; simp [tensor_apply]

theorem tensorSpan_dense [NormalSpace K] :
    ∀ k : C(K × K, ℂ), k ∈ closure (tensorSpan K : Set C(K × K, ℂ)) := by
  let S := tensorSpan K
  have S_mul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a1, b1⟩, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨a2, b2⟩, rfl⟩ := hy
        simp only
        rw [tensor_mul]; exact Submodule.subset_span ⟨(a1 * a2, b1 * b2), rfl⟩
      | zero => simp
      | add y y' _ _ ihy ihy' => rw [mul_add]; exact S.add_mem ihy ihy'
      | smul c y _ ihy => rw [mul_smul_comm]; exact S.smul_mem c ihy
    | zero => simp
    | add x x' _ _ ihx ihx' => rw [add_mul]; exact S.add_mem ihx ihx'
    | smul c x _ ihx => rw [smul_mul_assoc]; exact S.smul_mem c ihx
  have S_star : ∀ a ∈ S, star a ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a1, b1⟩, rfl⟩ := hx
      simp only
      rw [tensor_star]; exact Submodule.subset_span ⟨(star a1, star b1), rfl⟩
    | zero => simp
    | add x x' _ _ ihx ihx' => rw [star_add]; exact S.add_mem ihx ihx'
    | smul c x _ ihx => rw [star_smul]; exact S.smul_mem _ ihx
  have S_one : (1 : C(K × K, ℂ)) ∈ S := by
    rw [← tensor_one]; exact Submodule.subset_span ⟨(1, 1), rfl⟩
  let D : StarSubalgebra ℂ C(K × K, ℂ) :=
    { carrier := (S : Set C(K × K, ℂ))
      mul_mem' := fun {a b} ha hb => S_mul a ha b hb
      one_mem' := S_one
      add_mem' := fun {a b} ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        have : algebraMap ℂ C(K × K, ℂ) c = c • (1 : C(K × K, ℂ)) := by
          ext p; simp [Algebra.algebraMap_eq_smul_one]
        rw [this]; exact S.smul_mem c S_one
      star_mem' := fun {a} ha => S_star a ha }
  -- separating points
  have hsepK : ∀ x x' : K, x ≠ x' → ∃ a : C(K, ℂ), a x ≠ a x' := by
    intro x x' hne
    obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x)) (isClosed_singleton (x := x'))
      (Set.disjoint_singleton.2 hne)
    refine ⟨⟨fun z => ((g z : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩, ?_⟩
    simp only [ContinuousMap.coe_mk]
    rw [hg0 (Set.mem_singleton x), hg1 (Set.mem_singleton x')]
    simp
  have hDsep : D.SeparatesPoints := by
    intro p q hpq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      obtain ⟨a, ha⟩ := hsepK _ _ h2
      refine ⟨tensor 1 a, ⟨tensor 1 a, Submodule.subset_span ⟨(1, a), rfl⟩, rfl⟩, ?_⟩
      simpa [tensor_apply] using ha
    · obtain ⟨a, ha⟩ := hsepK _ _ h1
      refine ⟨tensor a 1, ⟨tensor a 1, Submodule.subset_span ⟨(a, 1), rfl⟩, rfl⟩, ?_⟩
      simpa [tensor_apply] using ha
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints D hDsep
  intro k
  have : k ∈ D.topologicalClosure := by rw [htop]; trivial
  exact this

/-- **Every integral operator with continuous kernel on `L²(μ)` is compact.** -/
theorem Tk_compact [NormalSpace K] (k : C(K × K, ℂ)) : IsCompactOperator (Tk μ k) := by
  have hclosed : IsClosed {k : C(K × K, ℂ) | IsCompactOperator (Theta μ k)} :=
    (isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ)
      (M₁ := Lp ℂ 2 μ) (M₂ := Lp ℂ 2 μ)).preimage (Theta μ).continuous
  have hsub : (tensorSpan K : Set C(K × K, ℂ)) ⊆ {k | IsCompactOperator (Theta μ k)} := by
    intro k hk
    induction hk using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      exact isCompact_Tk_tensor μ a b
    | zero => simpa using isCompactOperator_zero
    | add x y _ _ hx hy => simpa [map_add] using hx.add hy
    | smul c x _ hx => simpa [map_smul] using hx.smul c
  have := hclosed.closure_subset_iff.2 hsub (tensorSpan_dense k)
  exact this

end PW
end LeanCheck
