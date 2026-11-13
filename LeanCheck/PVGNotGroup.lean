import Mathlib
import LeanCheck.PVGNotGroupClosure
import LeanCheck.PVGNTrace

/-!
# PVG: Lemma 8.78(d) and Theorem 8.79 of PVG_v34: `τ_ξ` is not a group topology (Lean check)

Scope. `ξ = ξ_{τ_B, I_S}` is the PVG of the lacunary ideal (`lacConv = xiConv IS`), `τ_ξ = modTop lacConv` its topological modification
(`mem_modTop_iff`: `U` is open iff `cl_{τ_B}(J \ U) ∩ U = ∅` for all `J ∈ I_S`). With the set `E = Eall = ⋃_{i ≥ 2} E_i` of `PVGNotGroupArith`:

* `Eall_compl_open` : `ℝ \ E` is `τ_ξ`-open (Lemma 8.78(d); uses `Ei_not_mem_piece` and `closure_Ei`);
* `zero_notMem_Eall` : `0 ∉ E` (Lemma 8.78(a));
* `modTop_not_continuousAdd`, `modTop_not_topAddGroup` : **Theorem 8.79**: addition is not continuous at `(0, 0)` for `τ_ξ`; so `τ_ξ` is not a group
  topology (Question 9.2 of PVG_v33 has a negative answer). The proof is the one of the article: for a `τ_ξ`-open `V ∋ 0` with `V + V ⊆ ℝ \ E`
  there are Bohr neighbourhoods `O₀`, `O_i` of `0` with `O₀ ∩ J₀ ⊆ V`, `O_i ∩ J_i ⊆ V` (`J_c = {c (s_a - s_b)} ∈ I_S`); a free ultrafilter `W₀` gives
  `k ≠ l` with `L(W₀ - k) - L(W₀ - l)` in the open set of `K` defining `O₀` (compactness), and the iterated limit along `W₀ ⊗ W₀` (carried out as an
  iterated choice of `n` and then `m`) gives `u + w ∈ E_i`, `u = s_{n-k} - s_{m-l} ∈ V`, `w = c_i (s_n - s_m) ∈ V`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set Pointwise
open scoped Classical

namespace PVG
namespace Lac
open Q95

lemma Sset_mem_pos {a : ℕ} (ha : 1 ≤ a) : sS a ∈ Sset := Or.inr ⟨a, ha, Or.inl rfl⟩

/-- `J_c = {c (s_a - s_b) : a, b ≥ 1}`. -/
def Jc (c : ℝ) : Set ℝ := {z | ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ z = c * (sS a - sS b)}

lemma Jc_mem_IS (c : ℝ) : Jc c ∈ IS := by
  refine ⟨0, [c, -c], ?_⟩
  rintro z ⟨a, b, ha, hb, rfl⟩
  refine ⟨0, ⟨by simp, by simp⟩, c * sS a + ((-c) * sS b + 0), ?_, by ring⟩
  refine ⟨c * sS a, ⟨sS a, Sset_mem_pos ha, rfl⟩, (-c) * sS b + 0, ?_, rfl⟩
  exact ⟨(-c) * sS b, ⟨sS b, Sset_mem_pos hb, rfl⟩, 0, rfl, rfl⟩

lemma zero_notMem_Eall : (0 : ℝ) ∉ Eall := by
  rintro ⟨i, hi, hy⟩
  exact Ei_ne_zero (by omega) hy rfl

lemma closure_J_Eall {J : Set ℝ} (hJ : J ∈ IS) :
    @closure ℝ bohrTop (J \ Eallᶜ) ⊆ Eall := by
  letI : TopologicalSpace ℝ := bohrTop
  obtain ⟨m0, l, hJsub⟩ := hJ
  obtain ⟨i0, hi0⟩ := Ei_not_mem_piece m0 l
  have hsub : J \ Eallᶜ ⊆ ⋃ j : Fin i0, Ei (j.1 + 2) := by
    rintro y ⟨hyJ, hyE⟩
    have hyE' : y ∈ Eall := by simpa using hyE
    obtain ⟨i, hi2, hyi⟩ := hyE'
    have hlt : i < i0 := by
      by_contra hge
      exact hi0 i (not_lt.1 hge) y hyi (hJsub hyJ)
    refine mem_iUnion.2 ⟨⟨i - 2, by omega⟩, ?_⟩
    have : i - 2 + 2 = i := by omega
    simpa [this] using hyi
  intro x hx
  have h1 : closure (J \ Eallᶜ) ⊆ ⋃ j : Fin i0, Ei (j.1 + 2) := by
    calc closure (J \ Eallᶜ) ⊆ closure (⋃ j : Fin i0, Ei (j.1 + 2)) := closure_mono hsub
      _ = ⋃ j : Fin i0, closure (Ei (j.1 + 2)) := closure_iUnion_of_finite _
      _ ⊆ ⋃ j : Fin i0, Ei (j.1 + 2) := iUnion_mono fun j y hy => closure_Ei (by omega) hy
  obtain ⟨j, hj⟩ := mem_iUnion.1 (h1 hx)
  exact ⟨j.1 + 2, by omega, hj⟩

/-- **Lemma 8.78(d)**: `ℝ \ E` is `τ_ξ`-open. -/
theorem Eall_compl_open : @IsOpen ℝ (modTop lacConv) Eallᶜ := by
  have hmem := @mem_modTop_iff ℝ _ _ bohrTop bohr_isTopologicalAddGroup bohr_constSMul IS Eallᶜ
  refine hmem.2 ?_
  intro J hJ
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  exact hx2 (closure_J_Eall hJ hx1)

lemma bohr_open_pre {O : Set ℝ} (hO : @IsOpen ℝ bohrTop O) : ∃ Y : Set K, IsOpen Y ∧ e ⁻¹' Y = O :=
  isOpen_induced_iff.1 hO

lemma e_mul_sub (c a b : ℝ) : e (c * (a - b)) = c • e a - c • e b := by
  rw [mul_sub, e_sub, ← smul_e, ← smul_e]

/-- Local Bohr neighbourhoods inside a `τ_ξ`-neighbourhood of `0`. -/
lemma local_bohr {V : Set ℝ} (hV : @IsOpen ℝ (modTop lacConv) V) (h0 : (0 : ℝ) ∈ V) {J : Set ℝ}
    (hJ : J ∈ IS) : ∃ Y : Set K, IsOpen Y ∧ e 0 ∈ Y ∧ ∀ z ∈ J, e z ∈ Y → z ∈ V := by
  have hmem := @mem_modTop_iff ℝ _ _ bohrTop bohr_isTopologicalAddGroup bohr_constSMul IS V
  have hcl := hmem.1 hV J hJ
  have hOopen : @IsOpen ℝ bohrTop (@closure ℝ bohrTop (J \ V))ᶜ :=
    (@isOpen_compl_iff ℝ (@closure ℝ bohrTop (J \ V)) bohrTop).2 (@isClosed_closure ℝ bohrTop _)
  obtain ⟨Y, hY, hYO⟩ := bohr_open_pre hOopen
  have h0O : (0 : ℝ) ∈ (@closure ℝ bohrTop (J \ V))ᶜ := by
    intro h
    have : (0 : ℝ) ∈ @closure ℝ bohrTop (J \ V) ∩ V := ⟨h, h0⟩
    rw [hcl] at this
    exact this
  refine ⟨Y, hY, ?_, ?_⟩
  · rw [← hYO] at h0O
    exact h0O
  · intro z hzJ hzY
    by_contra hzV
    have hzO : z ∈ (@closure ℝ bohrTop (J \ V))ᶜ := by rw [← hYO]; exact hzY
    exact hzO (@subset_closure ℝ bohrTop (J \ V) z ⟨hzJ, hzV⟩)

/-- **Theorem 8.79**: addition is not continuous for `τ_ξ`. -/
theorem modTop_not_continuousAdd : ¬ @ContinuousAdd ℝ (modTop lacConv) _ := by
  intro hca
  letI τ : TopologicalSpace ℝ := modTop lacConv
  have hU : IsOpen Eallᶜ := Eall_compl_open
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := hca.continuous_add
  have hpre := hcont.isOpen_preimage Eallᶜ hU
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Eallᶜ := by
    simpa using zero_notMem_Eall
  obtain ⟨V1, V2, hV1, hV2, h01, h02, hsub⟩ := isOpen_prod_iff.1 hpre 0 0 h00
  set V : Set ℝ := V1 ∩ V2 with hVdef
  have hVopen : IsOpen V := hV1.inter hV2
  have h0V : (0 : ℝ) ∈ V := ⟨h01, h02⟩
  have hVV : ∀ u ∈ V, ∀ w ∈ V, u + w ∈ Eallᶜ := fun u hu w hw => hsub (Set.mk_mem_prod hu.1 hw.2)
  -- a free ultrafilter and the points `L(W₀ - k)`
  obtain ⟨W0, hW0⟩ : ∃ W0 : Ultrafilter ℕ, Free W0 := ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le _⟩
  set p : ℕ → K := fun k => L sS (shiftU k W0) with hp
  -- the Bohr neighbourhood for `J₀ = J_1`
  obtain ⟨Y0, hY0, h0Y0, hY0V⟩ := local_bohr hVopen h0V (Jc_mem_IS 1)
  obtain ⟨κ, hκ⟩ := exists_clusterPt_of_compactSpace (Filter.map p atTop)
  have hsub0 : ∃ V1 ∈ 𝓝 κ, ∀ a ∈ V1, ∀ c ∈ V1, a - c ∈ Y0 := by
    have h1 : Tendsto (fun q : K × K => q.1 - q.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
      continuous_sub.tendsto (κ, κ)
    rw [sub_self] at h1
    have h2 := h1 (hY0.mem_nhds (by simpa [e_zero] using h0Y0))
    rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2
    obtain ⟨V1, hV1, hV1sub⟩ := h2
    exact ⟨V1, hV1, fun a ha c hc => hV1sub (Set.mk_mem_prod ha hc)⟩
  obtain ⟨Vk, hVk, hVkY⟩ := hsub0
  have hfreq : ∃ᶠ j in atTop, p j ∈ Vk := (mapClusterPt_iff_frequently.1 hκ) Vk hVk
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨k, hk1, hkV⟩ := hfreq 1
  obtain ⟨l, hl, hlV⟩ := hfreq (k + 1)
  have hl1 : 1 ≤ l := by omega
  have hkl : k ≠ l := by omega
  have hpkl : p k - p l ∈ Y0 := hVkY _ hkV _ hlV
  -- the index `i` and the Bohr neighbourhood for `J_{c_i}`
  set i : ℕ := max (max k l) 2 with hi
  have hi2 : 2 ≤ i := le_max_right _ _
  have hki : k ≤ i := le_trans (le_max_left _ _) (le_max_left _ _)
  have hli : l ≤ i := le_trans (le_max_right _ _) (le_max_left _ _)
  set c : ℝ := cc i with hc
  obtain ⟨Yi, hYi, h0Yi, hYiV⟩ := local_bohr hVopen h0V (Jc_mem_IS c)
  have h0Yi' : (0 : K) ∈ Yi := by simpa [e_zero] using h0Yi
  have h0Y0' : (0 : K) ∈ Y0 := by simpa [e_zero] using h0Y0
  -- convergence along `W₀`
  have hpl : ∀ l' : ℕ, Tendsto (fun m => e (sS (m - l'))) (W0 : Filter ℕ) (𝓝 (p l')) :=
    fun l' => tendsto_e_comp sS W0 (fun m => m - l')
  have hL3 : Tendsto (fun m => e (sS m)) (W0 : Filter ℕ) (𝓝 (L sS W0)) := tendsto_L sS W0
  have hsm : ∀ κ : K, Tendsto (fun κ' : K => c • κ') (𝓝 κ) (𝓝 (c • κ)) :=
    fun κ => (continuous_smul_const c).tendsto κ
  -- first coordinate `n`
  have hB1 : ∀ᶠ n in (W0 : Filter ℕ), e (sS (n - k)) - p l ∈ Y0 := by
    have := (hpl k).sub_const (p l)
    exact this.eventually (hY0.mem_nhds hpkl)
  have hB2 : ∀ᶠ n in (W0 : Filter ℕ), c • e (sS n) - c • L sS W0 ∈ Yi := by
    have h1 := ((hsm _).comp hL3).sub_const (c • L sS W0)
    rw [sub_self] at h1
    exact h1.eventually (hYi.mem_nhds h0Yi')
  have hB3 : ∀ᶠ n in (W0 : Filter ℕ), MM i ≤ n := by
    refine hW0 (Filter.mem_cofinite.2 ((Set.finite_Iio (MM i)).subset ?_))
    intro n hn
    simpa using hn
  obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n, e (sS (n - k)) - p l ∈ Y0 ∧ c • e (sS n) - c • L sS W0 ∈ Yi ∧
      MM i ≤ n := ((hB1.and hB2).and hB3).exists.imp fun n h => ⟨h.1.1, h.1.2, h.2⟩
  -- second coordinate `m`
  have hC1 : ∀ᶠ m in (W0 : Filter ℕ), e (sS (n - k)) - e (sS (m - l)) ∈ Y0 := by
    have := (tendsto_const_nhds (x := e (sS (n - k)))).sub (hpl l)
    exact this.eventually (hY0.mem_nhds hn1)
  have hC2 : ∀ᶠ m in (W0 : Filter ℕ), c • e (sS n) - c • e (sS m) ∈ Yi := by
    have := (tendsto_const_nhds (x := c • e (sS n))).sub ((hsm _).comp hL3)
    exact this.eventually (hYi.mem_nhds hn2)
  have hC3 : ∀ᶠ m in (W0 : Filter ℕ), n < m := by
    refine hW0 (Filter.mem_cofinite.2 ((Set.finite_Iic n).subset ?_))
    intro m hm
    simpa using hm
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m, e (sS (n - k)) - e (sS (m - l)) ∈ Y0 ∧
      c • e (sS n) - c • e (sS m) ∈ Yi ∧ n < m :=
    ((hC1.and hC2).and hC3).exists.imp fun m h => ⟨h.1.1, h.1.2, h.2⟩
  have hMM : MM i = 3 * i + 4 := rfl
  have hn1' : 1 ≤ n - k := by omega
  have hm1' : 1 ≤ m - l := by omega
  have hnpos : 1 ≤ n := by omega
  have hmpos : 1 ≤ m := by omega
  -- `u` and `w` lie in `V`
  have hu : sS (n - k) - sS (m - l) ∈ V := by
    have h1 : (1 : ℝ) * (sS (n - k) - sS (m - l)) ∈ Jc 1 := ⟨n - k, m - l, hn1', hm1', rfl⟩
    have h2 : e ((1 : ℝ) * (sS (n - k) - sS (m - l))) ∈ Y0 := by
      rw [one_mul, e_sub]; exact hm1
    simpa using hY0V _ h1 h2
  have hw : c * (sS n - sS m) ∈ V := by
    have h1 : c * (sS n - sS m) ∈ Jc c := ⟨n, m, hnpos, hmpos, rfl⟩
    have h2 : e (c * (sS n - sS m)) ∈ Yi := by
      rw [e_mul_sub]; exact hm2
    exact hYiV _ h1 h2
  have hyE : sS (n - k) - sS (m - l) + c * (sS n - sS m) ∈ Eall :=
    ⟨i, hi2, ⟨k, l, n, m, hk1, hki, hl1, hli, hkl, hn3, hm3, rfl⟩⟩
  exact hVV _ hu _ hw hyE

/-- `τ_ξ` is not a group topology. -/
theorem modTop_not_topAddGroup : ¬ @IsTopologicalAddGroup ℝ (modTop lacConv) _ := by
  intro h
  exact modTop_not_continuousAdd (@IsTopologicalAddGroup.toContinuousAdd ℝ (modTop lacConv) _ h)

end Lac
end PVG
