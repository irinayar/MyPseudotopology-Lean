import Mathlib
import LeanCheck.PVGModStrict

/-!
# PVG: an `I_S`-thin cluster set that accumulates at `0` in the Bohr topology (Lean check)

Scope. Addendum I7 of the research note and the new proposition of `PVG_v24`. For `M_i = (i+1) s_{i+1}` let
`Ct = ⋃_i {M_i h : 1 ≤ h ≤ i}`. The elements of the `i`-th cluster lie between `j s_j` and `j² s_j` with `j = i+1`, in the gap between the
bands `[c₀ s_T / 4, 3 c₁ s_T]` in which the large elements of a member of `I_S` must lie.

* `thin_Ct`: `J ∩ Ct` is finite for every `J ∈ I_S` (the proof uses `rep_of_mem_sumSet` and `lower_bound` of `PVGLacCount`);
* `thin_cluster_modstrict`: `0 ∉ Ct`, `0 ∈ cl_{τ_B} Ct` (`clusters` of `PVGClusters`), `ℝ ∖ Ct` is `τ_ξ`-open (`finite_closed` of `PVGSeqFU`)
  and not `τ_B`-open; so `τ_B ⊊ τ_ξ` is witnessed by a set that meets every member of `I_S` in a finite set.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- The centers `M_i = (i+1) s_{i+1}`. -/
noncomputable def Mt (i : ℕ) : ℝ := ((i : ℝ) + 1) * sS (i + 1)

lemma Mt_pos (i : ℕ) : 0 < Mt i := mul_pos (by positivity) (sS_pos _)

/-- The cluster set `⋃_i {M_i h : 1 ≤ h ≤ i}`. -/
def Ct : Set ℝ := {x | ∃ i h : ℕ, 1 ≤ h ∧ h ≤ i ∧ x = Mt i * h}

/-- The key estimate: no element of the `(j-1)`-st cluster lies in `[-m,m] + ∑ d_n s_n` when `j` is large. -/
lemma not_mem_of_large {m c0 c1 : ℝ} (hm : 0 ≤ m) (hc0 : 0 < c0) (hc1 : 1 ≤ c1) (N0 : ℕ) (hN0 : 1 ≤ N0)
    (hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1)) (j : ℕ) (hj1 : 2 * c1 + m + 1 ≤ j)
    (hjN0 : N0 ≤ j) (hjbig : (j : ℝ) ^ 2 + m < c0 * 2 ^ (2 * j))
    (d : ℕ → ℝ) (hd : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1)) (N : ℕ) (hN : ∀ n, N ≤ n → d n = 0)
    (e : ℝ) (he : |e| ≤ m) (z : ℝ) (hz : z = e + ∑ n ∈ Finset.range N, d n * sS n)
    (hlo : (j : ℝ) * sS j ≤ |z|) (hhi : |z| ≤ (j : ℝ) ^ 2 * sS j) : False := by
  have hsj1 : 1 ≤ sS j := one_le_sS j
  have hcd : ∀ n, |d n| ≤ c1 := by
    intro n
    rcases hd n with h | h
    · rw [h, abs_zero]; linarith
    · exact h.2
  by_cases hA : ∀ n, j < n → d n = 0
  · -- the top index is at most `j`
    set σ : ℝ := ∑ n ∈ Finset.range N, d n * sS n with hσ
    have hg : ∀ n, 0 ≤ |d n| * sS n := fun n => mul_nonneg (abs_nonneg _) (sS_pos n).le
    have h1 : ∑ n ∈ Finset.range N, |d n| * sS n = ∑ n ∈ Finset.range (N + j + 1), |d n| * sS n := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) (fun x hx hxn => ?_)
      have : N ≤ x := by simpa using hxn
      rw [hN x this]; simp
    have h2 : ∑ n ∈ Finset.range (j + 1), |d n| * sS n = ∑ n ∈ Finset.range (N + j + 1), |d n| * sS n := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) (fun x hx hxn => ?_)
      have : j + 1 ≤ x := by simpa using hxn
      rw [hA x (by omega)]; simp
    have h3 : ∑ n ∈ Finset.range (j + 1), |d n| * sS n ≤ ∑ n ∈ Finset.range (j + 1), c1 * sS n :=
      Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hcd n) (sS_pos n).le)
    have h4 : ∑ n ∈ Finset.range (j + 1), c1 * sS n ≤ c1 * (2 * sS j) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (geom_sS j) (by linarith)
    have h5 : |σ| ≤ ∑ n ∈ Finset.range N, |d n| * sS n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [abs_mul, abs_of_pos (sS_pos n)]
    have hσb : |σ| ≤ 2 * c1 * sS j := by
      calc |σ| ≤ ∑ n ∈ Finset.range N, |d n| * sS n := h5
        _ = ∑ n ∈ Finset.range (j + 1), |d n| * sS n := by rw [h1, h2]
        _ ≤ c1 * (2 * sS j) := h3.trans h4
        _ = 2 * c1 * sS j := by ring
    have hzb : |z| ≤ m + 2 * c1 * sS j := by
      rw [hz]
      exact (abs_add_le _ _).trans (add_le_add he hσb)
    nlinarith [mul_le_mul_of_nonneg_right hj1 (sS_pos j).le]
  · push Not at hA
    obtain ⟨n1, hn1j, hn1⟩ := hA
    have hn1N : n1 < N := by
      by_contra hcon
      exact hn1 (hN n1 (not_lt.1 hcon))
    set S : Finset ℕ := (Finset.range N).filter (fun n => d n ≠ 0) with hS
    have hne : S.Nonempty := ⟨n1, by simp [hS, hn1N, hn1]⟩
    set T := S.max' hne with hT
    have hTS : T ∈ S := Finset.max'_mem S hne
    have hTN : T < N := by simpa [hS] using (Finset.mem_filter.1 hTS).1
    have hdT : d T ≠ 0 := (Finset.mem_filter.1 hTS).2
    have hT1 : n1 ≤ T := Finset.le_max' S n1 (by simp [hS, hn1N, hn1])
    have hup : ∀ n, T < n → d n = 0 := by
      intro n hn
      by_contra hdn
      have hnN : n < N := by
        by_contra hcon
        exact hdn (hN n (not_lt.1 hcon))
      have : n ∈ S := by simp [hS, hnN, hdn]
      have := Finset.le_max' S n this
      omega
    have hTj : j + 1 ≤ T := by omega
    have hlb := lower_bound hc0 (by linarith) N0 hN0 hN0big d hd T (by omega) hdT hup N hTN
    have hsT : sS (j + 1) ≤ sS T := sS_mono hTj
    have hsj : sS (j + 1) = sS j * 2 ^ (2 * j + 1) := sS_succ j
    have hz' : |z| ≥ |∑ n ∈ Finset.range N, d n * sS n| - m := by
      have := abs_sub_abs_le_abs_sub (∑ n ∈ Finset.range N, d n * sS n) (-e)
      rw [hz]
      have h2 := abs_add_le e (∑ n ∈ Finset.range N, d n * sS n)
      have h3 : |∑ n ∈ Finset.range N, d n * sS n| ≤ |e + ∑ n ∈ Finset.range N, d n * sS n| + |e| := by
        have := abs_sub (e + ∑ n ∈ Finset.range N, d n * sS n) e
        simpa using this
      linarith
    have hpow : (2 : ℝ) ^ (2 * j + 1) = 2 * 2 ^ (2 * j) := by rw [pow_succ]; ring
    have hcore : c0 * 2 ^ (2 * j) * sS j - m ≤ |z| := by
      have : c0 * sS T / 2 ≥ c0 * (sS j * 2 ^ (2 * j + 1)) / 2 := by
        rw [← hsj]; nlinarith
      rw [hpow] at this
      nlinarith
    have hfin : c0 * 2 ^ (2 * j) * sS j - m ≤ (j : ℝ) ^ 2 * sS j := hcore.trans hhi
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt (sub_pos.2 hjbig)) (sS_pos j).le, mul_le_mul_of_nonneg_left hsj1 hm]

/-- **`Ct` is `I_S`-thin**: every member of `I_S` meets it in a finite set. -/
theorem thin_Ct {J : Set ℝ} (hJ : J ∈ IS) : (J ∩ Ct).Finite := by
  obtain ⟨m, l, h⟩ := mem_IS_iff.1 hJ
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts (Cset l)
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  set N0 : ℕ := n0 + 1 with hN0def
  have hN0 : 1 ≤ N0 := by omega
  have hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1) := by
    intro T hT
    have h1 : (2 : ℝ) ^ n0 ≤ 2 ^ (2 * T - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : 4 * c1 / c0 < 2 ^ (2 * T - 1) := lt_of_lt_of_le hn0 h1
    rw [div_lt_iff₀ hc0] at h2
    linarith
  set m' : ℝ := |m| with hm'
  have hm'0 : 0 ≤ m' := abs_nonneg _
  -- the eventual conditions on `j`
  have e1 : ∀ᶠ j : ℕ in atTop, 2 * c1 + m' + 1 ≤ (j : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have e2 : ∀ᶠ j : ℕ in atTop, N0 ≤ j := eventually_ge_atTop N0
  have e3 : ∀ᶠ j : ℕ in atTop, (j : ℝ) ^ 2 + m' < c0 * 2 ^ (2 * j) := by
    have ht1 : Tendsto (fun j : ℕ => (j : ℝ) ^ 2 / 4 ^ j) atTop (𝓝 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 4)
    have ht2 : Tendsto (fun j : ℕ => m' / 4 ^ j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))
    have ht := ht1.add ht2
    rw [add_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds hc0)] with j hj
    have h4 : (0 : ℝ) < 4 ^ j := by positivity
    have : ((j : ℝ) ^ 2 + m') / 4 ^ j < c0 := by
      rw [add_div]; exact hj
    rw [div_lt_iff₀ h4] at this
    have e4 : (2 : ℝ) ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
    rw [e4]; exact this
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 (e1.and (e2.and e3))
  refine Set.Finite.subset
    ((Set.finite_Iio J0).biUnion (fun i _ => ((Set.finite_Icc 1 i).image (fun h : ℕ => Mt i * (h : ℝ))))) ?_
  rintro z ⟨hzJ, i, hh, hh1, hhi, rfl⟩
  by_contra hnot
  have hiJ0 : J0 ≤ i + 1 := by
    by_contra hcon
    apply hnot
    simp only [Set.mem_iUnion]
    exact ⟨i, by simp; omega, hh, ⟨hh1, hhi⟩, rfl⟩
  obtain ⟨hj1, hjN0, hjbig⟩ := hJ0 (i + 1) hiJ0
  obtain ⟨y, σ, hy, hσ, hzeq⟩ := h _ hzJ
  obtain ⟨N, d, hdmem, hdN, hσeq⟩ := rep_of_mem_sumSet l σ hσ
  have hd : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1) := by
    intro n
    by_cases h0 : d n = 0
    · exact Or.inl h0
    · exact Or.inr ⟨hlow _ (hdmem n) h0, hup _ (hdmem n)⟩
  have hpos : 0 < Mt i * (hh : ℝ) := mul_pos (Mt_pos i) (by exact_mod_cast hh1)
  have hMt : Mt i = ((i + 1 : ℕ) : ℝ) * sS (i + 1) := by simp [Mt]
  have hlo : ((i + 1 : ℕ) : ℝ) * sS (i + 1) ≤ |Mt i * (hh : ℝ)| := by
    rw [abs_of_pos hpos, hMt]
    have : (1 : ℝ) ≤ hh := by exact_mod_cast hh1
    have hs := mul_pos (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ)) (sS_pos (i + 1))
    nlinarith
  have hhi' : |Mt i * (hh : ℝ)| ≤ ((i + 1 : ℕ) : ℝ) ^ 2 * sS (i + 1) := by
    rw [abs_of_pos hpos, hMt]
    have : (hh : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : hh ≤ i + 1)
    have hs := mul_pos (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ)) (sS_pos (i + 1))
    nlinarith
  have hj1' : 2 * c1 + m' + 1 ≤ ((i + 1 : ℕ) : ℝ) := hj1
  exact not_mem_of_large hm'0 hc0 hc1 N0 hN0 hN0big (i + 1) hj1' hjN0 hjbig d hd N hdN y
    (hy.trans (le_abs_self m)) _ (by rw [hzeq, hσeq]) hlo hhi'

/-- **The thin cluster set.** `Ct` meets every member of `I_S` in a finite set, `0 ∉ Ct`, `0 ∈ cl_{τ_B} Ct`, and `ℝ ∖ Ct` is `τ_ξ`-open
but not `τ_B`-open. -/
theorem thin_cluster_modstrict :
    (∀ J ∈ IS, (J ∩ Ct).Finite) ∧ (0 : ℝ) ∉ Ct ∧ (0 : ℝ) ∈ @closure ℝ bohrTop Ct ∧
    @IsOpen ℝ (modTop lacConv) Ctᶜ ∧ ¬ @IsOpen ℝ bohrTop Ctᶜ := by
  have hcl := clusters Mt Mt_pos (fun i => i) tendsto_id
  have hCt : Ct = {x : ℝ | ∃ i h : ℕ, 1 ≤ h ∧ h ≤ (fun i : ℕ => i) i ∧ x = Mt i * h} := rfl
  refine ⟨fun J hJ => thin_Ct hJ, ?_, ?_, ?_, ?_⟩
  · rw [hCt]; exact hcl.1
  · rw [hCt]; exact hcl.2
  · letI : TopologicalSpace ℝ := bohrTop
    haveI := bohr_t2
    haveI := bohr_isTopologicalAddGroup
    haveI := bohr_constSMul
    exact finite_closed (I := IS) (fun J hJ => thin_Ct hJ)
  · intro hopen
    have h0 : (0 : ℝ) ∈ Ctᶜ := by rw [hCt]; exact hcl.1
    have hmem : Ctᶜ ∈ @nhds ℝ bohrTop 0 := @IsOpen.mem_nhds ℝ bohrTop 0 _ hopen h0
    have := (@mem_closure_iff_nhds ℝ bohrTop 0 Ct).1 (by rw [hCt]; exact hcl.2) _ hmem
    obtain ⟨x, hx1, hx2⟩ := this
    exact hx1 hx2

#print axioms thin_Ct
#print axioms thin_cluster_modstrict

end Lac
end PVG
