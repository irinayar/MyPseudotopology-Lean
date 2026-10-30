import LeanCheck.ChainV3

/-!
# Two failed constructions
(HamelCharactersTVG_v18 Proposition A.1 `prop:blocks-v8`, Proposition B.3 `prop:odd-segments-v12`)

* `alternating_blocks`: for the alternating dyadic blocks `B_k = [k², (k+1)² - 1]`, `I = ⋃ B_{2j}`, `J = ⋃ B_{2j+1}`
  both `ξ_I` and `ξ_J` have an irrational continuous character (so neither is compatible with `Γ`), while their
  join is the usual topology.
* `odd_segments_not_T2`, `odd_segments_character_discontinuous`: the raw odd-indexed half `C_odd = {k!·2^j : j odd}`
  generates a non-Hausdorff topology on `ℚ/ℤ`, and the profinite-series character `ψ(x) = ∑_{k ≥ 1} k! x` is not
  continuous for it (checked with the true continuity predicate, using the quarter-arc equivalence).
-/

namespace LeanCheck

open Filter Topology

section Blocks

/-- The block `B_k = {k², …, (k+1)² - 1}`. -/
def blockB (k : ℕ) : Set ℕ := {n | k ^ 2 ≤ n ∧ n < (k + 1) ^ 2}

/-- `I = ⋃ B_{2j}`. -/
def blockI : Set ℕ := {n | ∃ j, n ∈ blockB (2 * j)}

/-- `J = ⋃ B_{2j+1}`. -/
def blockJ : Set ℕ := {n | ∃ j, n ∈ blockB (2 * j + 1)}

lemma blockI_long : LongBlocks blockI := by
  intro L
  refine ⟨(2 * L) ^ 2, fun n h1 h2 => ⟨L, ?_, ?_⟩⟩
  · simpa using h1
  · show n < (2 * L + 1) ^ 2
    nlinarith

lemma blockJ_long : LongBlocks blockJ := by
  intro L
  refine ⟨(2 * L + 1) ^ 2, fun n h1 h2 => ⟨L, ?_, ?_⟩⟩
  · exact h1
  · show n < (2 * L + 1 + 1) ^ 2
    nlinarith

lemma blockIJ_univ : blockI ∪ blockJ = Set.univ := by
  ext n
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  -- `n` lies in `B_k` with `k = ⌊√n⌋`
  set k : ℕ := Nat.sqrt n with hk
  have h1 : k ^ 2 ≤ n := by rw [hk, pow_two]; exact Nat.sqrt_le n
  have h2 : n < (k + 1) ^ 2 := by rw [pow_two]; exact Nat.lt_succ_sqrt n
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · left; exact ⟨j, by rw [← hj]; exact ⟨h1, h2⟩⟩
  · right; exact ⟨j, by rw [← hj]; exact ⟨h1, h2⟩⟩

/-- **Why the alternating block attempt fails** (Proposition A.1). -/
theorem alternating_blocks :
    (∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (dyad '' blockI)) circTop (psiQ γ)) ∧
    (∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (dyad '' blockJ)) circTop (psiQ γ)) ∧
    xi (dyad '' blockI) ⊓ xi (dyad '' blockJ) = (inferInstance : TopologicalSpace ℚ) := by
  refine ⟨dyadic_long_blocks _ blockI_long, dyadic_long_blocks _ blockJ_long, ?_⟩
  rw [xi_inf_union, ← Set.image_union, blockIJ_univ]
  apply dyadic_bounded_gaps
  exact ⟨0, 0, fun k _ => ⟨k, Set.mem_univ _, le_rfl, by omega⟩⟩

end Blocks

section OddSegments

/-- The raw odd-indexed observations `k!·2^j`, `k ≥ 1`, `j` odd. -/
def COdd : Set ℕ := {c | ∃ k j : ℕ, 1 ≤ k ∧ j % 2 = 1 ∧ c = k.factorial * 2 ^ j}

lemma facM_null : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ facM n := fun N hN =>
  ⟨N, fun n hn => Nat.dvd_factorial hN (by omega)⟩

/-- The element `1/2 + ℤ`. -/
noncomputable def xHalf : TorsA := piHom (1 / 2)

lemma xHalf_coe : ((xHalf : TorsA) : Circ) = ((1 / 2 : ℝ) : Circ) := by
  rw [xHalf, piHom_coe]; push_cast; rfl

lemma even_smul_xHalf {c : ℕ} (hc : c % 2 = 0) : c • (xHalf : Circ) = 0 := by
  rw [xHalf_coe, nsmul_coe_circ, circ_zero_iff]
  obtain ⟨m, hm⟩ : ∃ m, c = 2 * m := ⟨c / 2, by omega⟩
  exact ⟨m, by rw [hm]; push_cast; ring⟩

lemma xHalf_mem_obs {δ : ℝ} (hδ : 0 < δ) : xHalf ∈ obs COdd δ := by
  rintro c ⟨k, j, hk, hj, rfl⟩
  have : (k.factorial * 2 ^ j) % 2 = 0 := by
    have hd : 2 ∣ k.factorial * 2 ^ j := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    exact Nat.mod_eq_zero_of_dvd hd
  rw [even_smul_xHalf this, norm_zero]
  exact hδ

/-- **The raw odd-indexed half is not Hausdorff** (Proposition B.3, first sentence). -/
theorem odd_segments_not_T2 : ¬ @T2Space TorsA (basisOf COdd).topology := by
  intro hT2
  have hne : xHalf ≠ 0 := by
    intro h
    have : ((xHalf : TorsA) : Circ) = 0 := by rw [h]; rfl
    rw [xHalf_coe, circ_zero_iff] at this
    obtain ⟨n, hn⟩ := this
    have h2 : (2 : ℝ) * n = 1 := by linarith
    have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
    omega
  obtain ⟨U, V, hU, hV, h0, hx, hdisj⟩ := @t2_separation TorsA (basisOf COdd).topology hT2 0 xHalf (Ne.symm hne)
  have hUn : U ∈ @nhds TorsA (basisOf COdd).topology 0 :=
    @IsOpen.mem_nhds TorsA (basisOf COdd).topology 0 U hU h0
  obtain ⟨W, ⟨δ, hδ, rfl⟩, hW⟩ := ((basisOf COdd).nhds_zero_hasBasis).mem_iff.1 hUn
  have hxU : xHalf ∈ U := hW (xHalf_mem_obs hδ)
  exact Set.disjoint_left.1 hdisj hxU hx

/-- The profinite-series character `ψ(x) = ∑_{k ≥ 1} k! x` of `ℚ/ℤ`. -/
noncomputable def psiSeries : TorsA →+ Circ :=
  zetaSum facM_chain facM_null id strictMono_id

lemma psiSeries_xHalf : psiSeries xHalf = ((1 / 2 : ℝ) : Circ) := by
  unfold psiSeries
  rw [zetaSum_apply facM_chain facM_null id strictMono_id xHalf 1 (fun n hn => by
    show facM n • (xHalf : Circ) = 0
    refine even_smul_xHalf ?_
    show (n + 1).factorial % 2 = 0
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_factorial (by norm_num) (by omega)))]
  simp only [Finset.range_one, Finset.sum_singleton, id]
  show facM 0 • (xHalf : Circ) = _
  rw [show facM 0 = 1 from rfl, one_smul, xHalf_coe]

/-- **The series character is not continuous for the raw odd half** (Proposition B.3, second sentence). -/
theorem odd_segments_character_discontinuous :
    ¬ @Continuous TorsA Circ (basisOf COdd).topology circTop psiSeries := by
  intro h
  obtain ⟨δ, hδ, hq⟩ := quarter_of_continuous COdd psiSeries h
  have := hq xHalf (xHalf_mem_obs hδ)
  rw [psiSeries_xHalf, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by norm_num)] at this
  norm_num at this

end OddSegments

end LeanCheck
