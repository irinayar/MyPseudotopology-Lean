import Mathlib
import LeanCheck.PVGBetaHalf
import LeanCheck.PVGBetaDelete

/-!
# PVG: one stage of the construction (Lean check, with Kronecker's theorem as a hypothesis)

Scope. "Claim A" of the proof of Theorem `thm:betaexists` of PVG_v22. Let `x₁, …, x_N` be algebraically independent over `ℚ`, `n ≥ 1` and
`ε > 0`. Then there are finitely many vectors `c⁽¹⁾, …, c⁽ᵠ⁾` of the box `[-n, n]ⁿ`, with half-integers `t_q = k_q + 1/2` and sets `E_q`
of at most `n` indices, such that every `c` of the box lies in the open set `U_q` of the `q`-th witness, where `‖c_i t_q x_j‖ < ε` for all
`i ≤ n` and `j ∉ E_q`. In the formal statement the open sets `U_q` are replaced by the condition "`‖c_i t_q x_j‖ < ε` for all `c` of the box
that the `q`-th witness serves", that is: for every `c` in the box there is a witness in the finite family that works for `c`.

* `witness_pointwise`: for one `c` there are `k ∈ ℤ` and `E` with at most `n` elements such that `‖c_i (k + 1/2) x_j‖ < ε` for `j ∉ E`
  (deletion lemma and half-integer lemma);
* `finite_witnesses`: a finite family of witnesses serves every `c` of the box (compactness).

Kronecker's density theorem is the explicit hypothesis `KroneckerDensity` of `PVGBetaHalf`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Beta

theorem witness_pointwise (hK : KroneckerDensity) {N n : ℕ} (x : Fin N → ℝ)
    (hx : AlgebraicIndependent ℚ x) (c : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (E : Finset (Fin N)) (k : ℤ), E.card ≤ n ∧
      ∀ (i : Fin n) (j : Fin N), j ∉ E →
        ‖((c i * ((k : ℝ) + 1 / 2) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  obtain ⟨T, hT, hspan⟩ := deletion x hx c
  let ι := Fin n × T
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let y : Fin (Fintype.card ι) → ℝ := fun l => c (e.symm l).1 * x (e.symm l).2
  have hrange : Set.range y = Set.range (fun p : Fin n × T => c p.1 * x p.2) := by
    ext z
    constructor
    · rintro ⟨l, rfl⟩; exact ⟨e.symm l, rfl⟩
    · rintro ⟨p, rfl⟩; exact ⟨e p, by simp [y]⟩
  have h1 : (1 : ℝ) ∉ Submodule.span ℚ (Set.range y) := by rw [hrange]; exact hspan
  obtain ⟨k, hk⟩ := half_integer_witness hK y h1 ε hε
  refine ⟨Finset.univ \ T, k, ?_, ?_⟩
  · rw [Finset.card_univ_sdiff]; simp only [Fintype.card_fin]; omega
  · intro i j hj
    have hjT : j ∈ T := by simpa using hj
    have := hk (e (i, ⟨j, hjT⟩))
    simp only [y, Equiv.symm_apply_apply] at this
    have e2 : (((k : ℝ) + 1 / 2) * (c i * x j)) = c i * ((k : ℝ) + 1 / 2) * x j := by ring
    rw [e2] at this
    exact this

/-- A finite family of witnesses serves every vector of the box `[-n, n]^n`. -/
theorem finite_witnesses (hK : KroneckerDensity) {N n : ℕ} (x : Fin N → ℝ)
    (hx : AlgebraicIndependent ℚ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset (Fin n → ℝ)) (k : (Fin n → ℝ) → ℤ) (E : (Fin n → ℝ) → Finset (Fin N)),
      (∀ c ∈ S, (E c).card ≤ n) ∧
      ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) →
        ∃ c₀ ∈ S, ∀ (i : Fin n) (j : Fin N), j ∉ E c₀ →
          ‖((c i * ((k c₀ : ℝ) + 1 / 2) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  -- a witness for every vector
  have hw : ∀ c : Fin n → ℝ, ∃ (E : Finset (Fin N)) (k : ℤ), E.card ≤ n ∧
      ∀ (i : Fin n) (j : Fin N), j ∉ E →
        ‖((c i * ((k : ℝ) + 1 / 2) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε / 2 + ε / 2 :=
    fun c => by
      obtain ⟨E, k, hE, hk⟩ := witness_pointwise hK x hx c (by positivity : 0 < ε / 2)
      exact ⟨E, k, hE, fun i j hj => by linarith [hk i j hj]⟩
  choose E k hE hk using hw
  -- the set of vectors served by the witness of `c`
  let U : (Fin n → ℝ) → Set (Fin n → ℝ) := fun c =>
    {c' | ∀ (i : Fin n) (j : Fin N), j ∉ E c →
      ‖((c' i * ((k c : ℝ) + 1 / 2) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε}
  have hUopen : ∀ c, IsOpen (U c) := by
    intro c
    have : U c = ⋂ i : Fin n, ⋂ j : {j : Fin N // j ∉ E c},
        {c' : Fin n → ℝ | ‖((c' i * ((k c : ℝ) + 1 / 2) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε} := by
      ext c'; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => ?_))
    refine isOpen_lt (continuous_norm.comp ?_) continuous_const
    exact (AddCircle.continuous_mk' 1).comp
      (((continuous_apply i).mul continuous_const).mul continuous_const)
  have hcU : ∀ c, c ∈ U c := by
    intro c i j hj
    have := hk c i j hj
    linarith
  -- compactness of the box
  have hcomp : IsCompact {c : Fin n → ℝ | ∀ i, |c i| ≤ n} := by
    have : {c : Fin n → ℝ | ∀ i, |c i| ≤ n} = Set.pi Set.univ (fun _ => Set.Icc (-(n : ℝ)) n) := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]
    rw [this]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S, -, hS⟩ := hcomp.elim_nhds_subcover U (fun c _ => (hUopen c).mem_nhds (hcU c))
  refine ⟨S, k, E, fun c _ => hE c, ?_⟩
  intro c hc
  have := hS hc
  rw [Set.mem_iUnion₂] at this
  obtain ⟨c₀, hc₀, hcc₀⟩ := this
  exact ⟨c₀, hc₀, hcc₀⟩

end Beta
end PVG
