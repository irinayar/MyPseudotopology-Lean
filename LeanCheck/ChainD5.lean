import LeanCheck.ChainD4

/-!
# Properties of the topologies `ξ_C` on `ℚ`
(TVGQ-v7 §"Rational observation topologies"; HamelCharactersTVG_v18 Theorem 22.1 `thm:prime-v8`)

For a nonempty set `C` of positive integers the group topology `ξ_C` on `ℚ` (neighbourhood base
`{q : ∀ c ∈ C, ‖q/(d c)‖ < ε}`) is Hausdorff, locally quasi-convex, and admits every fixed rational multiplication
continuously.  If moreover its dual is `Γ` it lies in `𝒬_Γ = Ccls Gam`.  For the chain `p^{n²}` the dual is `Γ`
by Theorem F, so `γ_p = ξ_{{p^{n²}}}` belongs to `𝒬_Γ`.
-/

namespace LeanCheck

open Filter Topology

section XiProps

/-- The rational character `q ↦ p(r q)`. -/
noncomputable def rchar (r : ℚ) : ℚ →+ Circ := psi0.comp (AddMonoidHom.mulLeft r)

lemma rchar_apply (r q : ℚ) : rchar r q = (((r * q : ℚ) : ℝ) : Circ) := by
  simp [rchar, psi0_apply]

lemma rchar_mem (r : ℚ) : rchar r ∈ Gam := ⟨r, fun s => rchar_apply r s⟩

/-- The observation `p(q / (d c))` of `ξ_C`. -/
noncomputable def xt (q : ℚ) (d c : ℕ) : Circ := ((((q / ((d : ℚ) * (c : ℚ))) : ℚ) : ℝ) : Circ)

variable (C : Set ℕ) (hC : ∀ c ∈ C, 0 < c) (hne : C.Nonempty)

include hC hne in
lemma xi_rchar_cont (r : ℚ) : @Continuous ℚ Circ (xi C) circTop (rchar r) :=
  xi_Gam_cont C hC hne _ (rchar_mem r)

include hC hne in
/-- `ξ_C` is Hausdorff. -/
theorem xi_t2 : @T2Space ℚ (xi C) := by
  letI : TopologicalSpace ℚ := xi C
  haveI : IsTopologicalAddGroup ℚ := xi_group C
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  have hN : ({0} : Set ℚ) = ⋂ r : ℚ, (rchar r) ⁻¹' {0} := by
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro rfl r; exact map_zero _
    · intro h
      by_contra hq
      have h1 := h (1 / (2 * q))
      rw [rchar_apply, circ_zero_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have : (((1 / (2 * q) * q : ℚ)) : ℝ) = 1 / 2 := by
        have : (1 / (2 * q) * q : ℚ) = 1 / 2 := by field_simp
        rw [this]; push_cast; ring
      rw [this] at hn
      have h2 : (2 : ℝ) * n = 1 := by linarith
      have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
      omega
  rw [hN]
  exact isClosed_iInter fun r => isClosed_singleton.preimage (show Continuous (rchar r) from xi_rchar_cont C hC hne r)

include hC hne in
/-- Every fixed rational multiplication is `ξ_C`-continuous. -/
theorem xi_scalar (s : ℚ) : Continuous[xi C, xi C] (fun x : ℚ => s * x) := by
  letI : TopologicalSpace ℚ := xi C
  haveI : IsTopologicalAddGroup ℚ := xi_group C
  have hmul : (fun x : ℚ => s * x) = ⇑(AddMonoidHom.mulLeft s) := rfl
  rw [hmul]
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  rw [(xi_nhds_hasBasis C).tendsto_iff (xi_nhds_hasBasis C)]
  rintro V ⟨d, hd, ε, hε, rfl⟩
  set a : ℤ := s.num
  set b : ℕ := s.den
  have hbpos : 0 < b := s.den_pos
  refine ⟨xiSet C (b * d) (ε / (|(a : ℝ)| + 1)), xiSet_mem C (b * d) (Nat.mul_pos hbpos hd) _ (by positivity),
    fun x hx c hc => ?_⟩
  have h1 := hx c hc
  have e : ((((s * x) / ((d : ℚ) * c) : ℚ) : ℝ) : Circ) =
      a • ((((x / (((b * d : ℕ) : ℚ) * c) : ℚ) : ℝ) : Circ)) := by
    have hs : s = a / b := (Rat.num_div_den s).symm
    have eq : (s * x) / ((d : ℚ) * c) = (a : ℚ) * (x / (((b * d : ℕ) : ℚ) * c)) := by
      rw [hs]; push_cast
      rw [div_mul_eq_mul_div, div_div, mul_assoc, mul_div_assoc]
    rw [eq, zsmul_coe_circ]
    push_cast
    rfl
  show ‖(((((s * x) / ((d : ℚ) * c) : ℚ) : ℝ)) : Circ)‖ < ε
  rw [e]
  refine lt_of_le_of_lt (norm_zsmul_le _ _) ?_
  rw [Int.norm_eq_abs]
  calc |(a : ℝ)| * ‖(((x / (((b * d : ℕ) : ℚ) * c) : ℚ) : ℝ) : Circ)‖ ≤ |(a : ℝ)| * (ε / (|(a : ℝ)| + 1)) := by
        gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (a : ℝ)]

include hC hne in
/-- `ξ_C` is locally quasi-convex. -/
theorem xi_lqc : LocQC (xi C) := by
  intro V hV
  obtain ⟨s, ⟨d, hd, ε, hε, rfl⟩, hs⟩ := ((xi_nhds_hasBasis C).mem_iff).mp hV
  obtain ⟨n, hn1, hnε⟩ := exists_R ε hε
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨{q : ℚ | ∀ c ∈ C, ∀ m : ℕ, m ≤ n → ‖m • xt q d c‖ ≤ 1 / 4}, ?_, ?_, ?_⟩
  · refine Filter.mem_of_superset
      ((xi_nhds_hasBasis C).mem_of_mem (xiSet_mem C d hd (1 / (4 * (n : ℝ))) (by positivity))) ?_
    intro q hq c hc m hm
    have h1 : ‖xt q d c‖ < 1 / (4 * (n : ℝ)) := hq c hc
    calc ‖m • xt q d c‖ ≤ m * ‖xt q d c‖ := norm_nsmul_le
      _ ≤ n * (1 / (4 * (n : ℝ))) :=
        mul_le_mul (by exact_mod_cast hm) h1.le (norm_nonneg _) (Nat.cast_nonneg n)
      _ = 1 / 4 := by field_simp
  · intro q hq
    apply hs
    intro c hc
    have hall : ∀ j : ℕ, j ≤ n → ‖j • xt q d c‖ ≤ 1 / 4 :=
      fun j hj => hq c hc j hj
    have := mult_le _ n hall
    have h2 : ‖xt q d c‖ ≤ 1 / (4 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact lt_of_le_of_lt h2 hnε
  · intro x hx
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hx
    obtain ⟨c, hc, m, hm, hlt⟩ := hx
    refine ⟨rchar ((m : ℚ) / ((d : ℚ) * c)), xi_rchar_cont C hC hne _, fun y hy => ?_, ?_⟩
    · have e : rchar ((m : ℚ) / ((d : ℚ) * c)) y = m • xt y d c := by
        rw [rchar_apply, xt, nsmul_coe_circ]
        congr 1
        push_cast
        ring
      rw [e]; exact hy c hc m hm
    · have e : rchar ((m : ℚ) / ((d : ℚ) * c)) x = m • xt x d c := by
        rw [rchar_apply, xt, nsmul_coe_circ]
        congr 1
        push_cast
        ring
      rw [e]; exact hlt

include hC hne in
/-- If the dual of `ξ_C` is `Γ`, then `ξ_C ∈ 𝒬_Γ`. -/
theorem xi_mem_Ccls (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi C) circTop ψ ↔ ψ ∈ Gam) :
    xi C ∈ Ccls Gam := by
  refine ⟨⟨xi_group C, xi_t2 C hC hne, xi_lqc C hC hne, hdual⟩, fun q => ?_⟩
  have e : (mq q : ℚ → ℚ) = fun x : ℚ => q * x := by funext x; simp [mq_apply]
  rw [e]
  exact xi_scalar C hC hne q

end XiProps

end LeanCheck
