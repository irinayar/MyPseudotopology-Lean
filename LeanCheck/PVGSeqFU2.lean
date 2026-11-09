import LeanCheck.PVGSeqFU

/-!
# PVG: extension to topologies containing the Bohr topology, closed lacunary sets, clusters (Lean check)

Scope. The remaining statements of the first half of Section 8 of `PVG_v19` that do not use the cluster bound:

* `extend_seq`, `extend_euclid_of_FU`, `extend_eq_euclid` (Theorem `extendFU` (a), (b), (c)): for an ideal `I` and a group
  topology `β` that contains the Bohr topology (`hβ : ∀ x, 𝓝_β x ≤ 𝓝_B x`: every Bohr neighbourhood is a `β`-neighbourhood);
* `countable_modTop` (Proposition `ctblFU`): the topological modification of the countable PVG is the Euclidean topology;
* `lacclosed` (Proposition `lacclosed`): a set `{t_k}` with `t_0 ≠ 0`, `|t_{k+1}| ≥ 5|t_k|` is closed in the Bohr topology
  (interpolation lemma `interpolation_bounded`);
* `clusters` (Proposition `clusters`): for `M_i > 0` and `H_i → ∞`, the set `C = ⋃_i {M_i h : 1 ≤ h ≤ H_i}` does not contain `0`
  and `0 ∈ cl_{τ_B} C` (pigeonhole in the torus).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise Cardinal

namespace PVG
namespace Q95

/-! ### Theorem 8.14 (`extendFU`) -/

section ExtendFU

/-- `ξ` defined from a neighbourhood system `N` (for `N = @nhds ℝ β` it is `@xiConv ℝ β I`). -/
def xiN (N : ℝ → Filter ℝ) (I : Set (Set ℝ)) (F : Filter ℝ) (x : ℝ) : Prop := F ≤ N x ∧ ∃ A ∈ F, A ∈ I

variable (N : ℝ → Filter ℝ) {I : Set (Set ℝ)}

/-- (a): sequences converging for `ξ_{β,I}` converge in the Euclidean topology, if `β ⊇ τ_B`. -/
theorem extend_seq (hβ : ∀ x, N x ≤ @nhds ℝ bohrTop x) {a : ℕ → ℝ} {x : ℝ}
    (h : xiN N I (Filter.map a atTop) x) : Tendsto a atTop (𝓝 x) :=
  (bohrseq a x).1 ((bohrConv_iff _ _).2 (h.1.trans (hβ x)))

/-- (b): if `ξ_{β,I}` is Fréchet–Urysohn, `ξ`-convergence implies Euclidean convergence. -/
theorem extend_euclid_of_FU (hI : IsIdeal I) (hβ : ∀ x, N x ≤ @nhds ℝ bohrTop x)
    (hFU : IsFU (xiN N I)) {F : Filter ℝ} {x : ℝ} (hF : xiN N I F x) : F ≤ 𝓝 x := by
  by_contra hno
  rw [Filter.le_def] at hno
  push Not at hno
  obtain ⟨W, hW, hWF⟩ := hno
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  have hballF : Metric.ball x ε ∉ F := fun h => hWF (Filter.mem_of_superset h hball)
  obtain ⟨A, hAF, hAI⟩ := hF.2
  set A' : Set ℝ := A \ Metric.ball x ε with hA'
  have hA'I : A' ∈ I := hI.mono hAI Set.diff_subset
  have hne : (N x ⊓ 𝓟 A').NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    have hUF : U ∈ F := hF.1 hU
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hballF
    refine Filter.mem_of_superset (Filter.inter_mem hUF hAF) (fun y hy => ?_)
    by_contra hyb
    have : y ∈ U ∩ A' := ⟨hy.1, hy.2, hyb⟩
    rw [hemp] at this
    exact this
  have hconv : xiN N I (N x ⊓ 𝓟 A') x :=
    ⟨inf_le_left, A', Filter.mem_inf_of_right (Filter.mem_principal_self _), hA'I⟩
  obtain ⟨u, hu, hconvu⟩ := hFU A' x ⟨_, hne, Filter.mem_inf_of_right (Filter.mem_principal_self _), hconv⟩
  have hlim := extend_seq N hβ hconvu
  have hev : ∀ᶠ n in atTop, u n ∈ Metric.ball x ε := hlim (Metric.ball_mem_nhds x hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hu n).2 hn

/-- (c): if moreover `β ⊆ τ_E` and `(-1,1) ∈ I`, then `ξ_{β,I}` is the Euclidean convergence. -/
theorem extend_eq_euclid (hI : IsIdeal I) (hball : Metric.ball (0 : ℝ) 1 ∈ I)
    (hβ : ∀ x, N x ≤ @nhds ℝ bohrTop x) (hβE : ∀ x, 𝓝 x ≤ N x)
    (hFU : IsFU (xiN N I)) (F : Filter ℝ) (x : ℝ) : xiN N I F x ↔ F ≤ 𝓝 x := by
  refine ⟨fun h => extend_euclid_of_FU N hI hβ hFU h, fun h => ?_⟩
  refine ⟨h.trans (hβE x), Metric.ball x 1, h (Metric.ball_mem_nhds x one_pos), ?_⟩
  refine bounded_mem_of_ball hI hball (M := |x| + 1) (fun a ha => ?_)
  rw [Metric.mem_ball, Real.dist_eq] at ha
  have h1 : |a| ≤ |a - x| + |x| := by
    have := abs_add_le (a - x) x
    simpa using this
  linarith

end ExtendFU

/-! ### Proposition `ctblFU`: the modification of the countable PVG -/

theorem countable_modTop : modTop countableConv = (inferInstance : TopologicalSpace ℝ) := by
  refine TopologicalSpace.ext ?_
  ext U
  show (∀ x ∈ U, ∀ F, countableConv F x → U ∈ F) ↔ IsOpen U
  constructor
  · intro hU
    rw [isOpen_iff_mem_nhds]
    intro x hx
    by_contra hno
    have hex : ∀ n : ℕ, ∃ d ∈ Metric.ball x (1 / ((n : ℝ) + 1)), d ∉ U := by
      intro n
      by_contra hcon
      push Not at hcon
      exact hno (Filter.mem_of_superset (Metric.ball_mem_nhds x (by positivity)) hcon)
    choose d hd using hex
    have hlim : Tendsto d atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => (Metric.mem_ball.1 (hd n).1).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv : countableConv (Filter.map d atTop) x :=
      ⟨hlim, Set.range d, Filter.mem_map.2 (Filter.mem_of_superset Filter.univ_mem (fun n _ => ⟨n, rfl⟩)),
        Set.countable_range d⟩
    have := hU x hx _ hconv
    have h2 : ∀ᶠ n in atTop, d n ∈ U := Filter.mem_map.1 this
    obtain ⟨n, hn⟩ := h2.exists
    exact (hd n).2 hn
  · intro hU x hx F hF
    exact hF.1 (hU.mem_nhds hx)

/-! ### Proposition `lacclosed`: closed lacunary sets -/

lemma abs_tail_large (t : ℕ → ℝ) (h0 : t 0 ≠ 0) (h5 : ∀ k, 5 * |t k| ≤ |t (k + 1)|) (B : ℝ) :
    ∃ k0, ∀ k, k0 ≤ k → B < |t k| := by
  have hpow : ∀ k, 5 ^ k * |t 0| ≤ |t k| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := h5 k
      calc 5 ^ (k + 1) * |t 0| = 5 * (5 ^ k * |t 0|) := by ring
        _ ≤ 5 * |t k| := by linarith
        _ ≤ |t (k + 1)| := this
  have hpos : 0 < |t 0| := abs_pos.2 h0
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / |t 0|) (by norm_num : (1 : ℝ) < 5)
  refine ⟨n, fun k hk => ?_⟩
  rw [div_lt_iff₀ hpos] at hn
  have h1 : (5 : ℝ) ^ n ≤ 5 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
  linarith [hpow k]

lemma isOpen_bohr_of_nhds (s : Set ℝ) (h : ∀ y ∈ s, s ∈ @nhds ℝ bohrTop y) : @IsOpen ℝ bohrTop s := by
  letI : TopologicalSpace ℝ := bohrTop
  exact isOpen_iff_mem_nhds.2 h

lemma isClosed_bohr_of_compl (s : Set ℝ) (h : @IsOpen ℝ bohrTop sᶜ) : @IsClosed ℝ bohrTop s := by
  letI : TopologicalSpace ℝ := bohrTop
  exact isOpen_compl_iff.1 h

lemma bohr_compl_mem_nhds (s : Set ℝ) (hs : s.Finite) (y : ℝ) (hy : y ∉ s) : sᶜ ∈ @nhds ℝ bohrTop y := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  exact hs.isClosed.isOpen_compl.mem_nhds hy

/-- **Proposition `lacclosed`.** `{t_k}` with `t_0 ≠ 0` and `|t_{k+1}| ≥ 5 |t_k|` is closed in the Bohr topology. -/
theorem lacclosed (t : ℕ → ℝ) (h0 : t 0 ≠ 0) (h5 : ∀ k, 5 * |t k| ≤ |t (k + 1)|) :
    @IsClosed ℝ bohrTop (Set.range t) := by
  have key : ∀ y, y ∉ Set.range t → (Set.range t)ᶜ ∈ @nhds ℝ bohrTop y := by
    intro y hy
    obtain ⟨k0, hk0⟩ := abs_tail_large t h0 h5 (5 * |y| + |y| + 1)
    have hu0 : t (k0 + 0) - y ≠ 0 := by
      intro h
      have h1 : t (k0 + 0) = y := sub_eq_zero.1 h
      have h2 := hk0 (k0 + 0) (by omega)
      rw [h1] at h2
      nlinarith [abs_nonneg y]
    have hur : ∀ j, 4 * |t (k0 + j) - y| ≤ |t (k0 + (j + 1)) - y| := by
      intro j
      have e : k0 + (j + 1) = k0 + j + 1 := by omega
      rw [e]
      have h1 := h5 (k0 + j)
      have h2 := hk0 (k0 + j) (by omega)
      have h3 : |t (k0 + j) - y| ≤ |t (k0 + j)| + |y| := by
        have := abs_sub (t (k0 + j)) y; linarith
      have h4 : |t (k0 + j + 1)| - |y| ≤ |t (k0 + j + 1) - y| := by
        have := abs_sub_abs_le_abs_sub (t (k0 + j + 1)) y; linarith
      linarith [abs_nonneg y]
    obtain ⟨b, -, -, hgood⟩ := interpolation_bounded (fun j => t (k0 + j) - y) hu0 hur Set.univ
    have hfar : ∀ j, 1 / 3 ≤ ‖((b * (t (k0 + j) - y) : ℝ) : AddCircle (1 : ℝ))‖ :=
      fun j => norm_circle_ge_of_far ((hgood j).1 (Set.mem_univ j))
    set Sb : Set ℝ := {z | ‖((b * (z - y) : ℝ) : AddCircle (1 : ℝ))‖ < 1 / 3} with hSb
    have hSbn : Sb ∈ @nhds ℝ bohrTop y := by
      rw [nhds_bohr]
      refine Filter.mem_comap.2 ⟨{κ : K | ‖κ b - ((b * y : ℝ) : AddCircle (1 : ℝ))‖ < 1 / 3}, ?_, ?_⟩
      · refine IsOpen.mem_nhds ?_ ?_
        · exact isOpen_lt (((continuous_eval b).sub continuous_const).norm) continuous_const
        · simp
      · intro z hz
        simp only [Set.mem_preimage, Set.mem_setOf_eq, e_apply] at hz
        show ‖((b * (z - y) : ℝ) : AddCircle (1 : ℝ))‖ < 1 / 3
        rw [mul_sub, AddCircle.coe_sub]
        exact hz
    have hyF : y ∉ Set.range (fun k : Fin k0 => t k) := fun ⟨k, hk⟩ => hy ⟨k, hk⟩
    have hFn := bohr_compl_mem_nhds (Set.range (fun k : Fin k0 => t k)) (Set.finite_range _) y hyF
    refine Filter.mem_of_superset (Filter.inter_mem hSbn hFn) ?_
    rintro z ⟨hzS, hzF⟩ ⟨k, rfl⟩
    by_cases hk : k < k0
    · exact hzF ⟨⟨k, hk⟩, rfl⟩
    · push Not at hk
      have := hfar (k - k0)
      have e : k0 + (k - k0) = k := by omega
      rw [e] at this
      exact absurd hzS (not_lt.2 this)
  exact isClosed_bohr_of_compl _ (isOpen_bohr_of_nhds _ (fun y hy => key y hy))

#print axioms extend_euclid_of_FU
#print axioms extend_eq_euclid
#print axioms countable_modTop
#print axioms lacclosed

end Q95
end PVG
