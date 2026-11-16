import Mathlib
import LeanCheck.PVGNotGroup

/-!
# PVG: a necessary condition on every witness of condition (N) (Lean check)

Scope. Proposition (necessary condition) of `PVG_v47`, Section "A necessary condition for the group property". Let `γ` be *any* group
topology on `ℝ` such that every `γ`-neighbourhood of `0` contains a Bohr-trace neighbourhood of `0` on the two pieces `J_1 = S - S` and
`J_{c_i} = c_i S - c_i S` (`i ≥ 2`, `c_i = 3^i`, `s_n = 2^(n^2)`). Then every `γ`-neighbourhood of `0` meets the set `E = ⋃_{i ≥ 2} E_i` of
Lemma 8.78 (`Eall`).

* `TraceNhd γ J` : every `γ`-neighbourhood `V` of `0` contains `{z ∈ J : e z ∈ Y}` for an open set `Y` of `K = Hom(ℝ,𝕋)` containing `e 0`
  (the trace of `γ` on `J` is contained in the Bohr trace at `0`);
* `traceNhd_of_induced_eq` : this holds if `γ` and the Bohr topology induce the same topology on `J` (with `0 ∈ J`);
* `exists_Eall_mem_nhds` : the statement above (no inclusion between `γ`, `τ_B` and `τ_E` is used);
* `condN_nhds_meets_Eall` : in particular, for every witness `γ` of condition (N) (a group topology with the Bohr trace on every member of `I_S`)
  every `γ`-neighbourhood of `0` meets `E`.

The proof is the one of Theorem 8.79 (`modTop_not_continuousAdd`) with the `τ_ξ`-open set `V` replaced by a `γ`-neighbourhood `V` with `V + V ⊆ W`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set Pointwise
open scoped Classical

namespace PVG
namespace Lac
open Q95

/-- Every `γ`-neighbourhood of `0` contains the Bohr trace `{z ∈ J : e z ∈ Y}` of a neighbourhood `Y` of `e 0` in `K`. -/
def TraceNhd (γ : TopologicalSpace ℝ) (J : Set ℝ) : Prop :=
  ∀ V ∈ @nhds ℝ γ 0, ∃ Y : Set K, IsOpen Y ∧ e 0 ∈ Y ∧ ∀ z ∈ J, e z ∈ Y → z ∈ V

/-- If `γ` and the Bohr topology induce the same topology on `J ∋ 0`, then `TraceNhd γ J`. -/
theorem traceNhd_of_induced_eq (γ : TopologicalSpace ℝ) {J : Set ℝ} (h0 : (0 : ℝ) ∈ J)
    (h : TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop) : TraceNhd γ J := by
  intro V hV
  have h1 : (Subtype.val ⁻¹' V : Set J) ∈ @nhds J (TopologicalSpace.induced (Subtype.val : J → ℝ) γ) ⟨0, h0⟩ := by
    rw [@nhds_induced ℝ J γ Subtype.val ⟨0, h0⟩]
    exact Filter.preimage_mem_comap hV
  rw [h, @nhds_induced ℝ J bohrTop Subtype.val ⟨0, h0⟩] at h1
  obtain ⟨B, hB, hBV⟩ := Filter.mem_comap.1 h1
  obtain ⟨O, hOB, hOopen, h0O⟩ := (@mem_nhds_iff ℝ bohrTop 0 B).1 hB
  obtain ⟨Y, hY, hYO⟩ := bohr_open_pre hOopen
  refine ⟨Y, hY, ?_, ?_⟩
  · have : (0 : ℝ) ∈ e ⁻¹' Y := by rw [hYO]; exact h0O
    exact this
  · intro z hzJ hzY
    have hzO : z ∈ O := by rw [← hYO]; exact hzY
    have : (⟨z, hzJ⟩ : J) ∈ Subtype.val ⁻¹' B := hOB hzO
    exact hBV this

lemma zero_mem_Jc (c : ℝ) : (0 : ℝ) ∈ Jc c := ⟨1, 1, le_rfl, le_rfl, by ring⟩

/-- **Necessary condition.** If a group topology `γ` has the Bohr trace (in the weak form `TraceNhd`) on `J_1` and on `J_{c_i}` for `i ≥ 2`,
every `γ`-neighbourhood of `0` meets `E`. -/
theorem exists_Eall_mem_nhds (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (h1 : TraceNhd γ (Jc 1)) (h2 : ∀ i : ℕ, 2 ≤ i → TraceNhd γ (Jc (cc i))) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ y ∈ Eall, y ∈ W := by
  intro W hW
  letI τ : TopologicalSpace ℝ := γ
  haveI : @IsTopologicalAddGroup ℝ γ _ := hγ
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
  -- a free ultrafilter and the points `L(W₀ - k)`
  obtain ⟨W0, hW0⟩ : ∃ W0 : Ultrafilter ℕ, Free W0 := ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le _⟩
  set p : ℕ → K := fun k => L sS (shiftU k W0) with hp
  -- the Bohr neighbourhood for `J₀ = J_1`
  obtain ⟨Y0, hY0, h0Y0, hY0V⟩ := h1 V hV
  obtain ⟨κ, hκ⟩ := exists_clusterPt_of_compactSpace (Filter.map p atTop)
  have hsub0 : ∃ V1 ∈ 𝓝 κ, ∀ a ∈ V1, ∀ c ∈ V1, a - c ∈ Y0 := by
    have h1' : Tendsto (fun q : K × K => q.1 - q.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
      continuous_sub.tendsto (κ, κ)
    rw [sub_self] at h1'
    have h2' := h1' (hY0.mem_nhds (by simpa [e_zero] using h0Y0))
    rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2'
    obtain ⟨V1, hV1, hV1sub⟩ := h2'
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
  obtain ⟨Yi, hYi, h0Yi, hYiV⟩ := h2 i hi2 V hV
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
    have h1'' := ((hsm _).comp hL3).sub_const (c • L sS W0)
    rw [sub_self] at h1''
    exact h1''.eventually (hYi.mem_nhds h0Yi')
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
    have h1a : (1 : ℝ) * (sS (n - k) - sS (m - l)) ∈ Jc 1 := ⟨n - k, m - l, hn1', hm1', rfl⟩
    have h2a : e ((1 : ℝ) * (sS (n - k) - sS (m - l))) ∈ Y0 := by
      rw [one_mul, e_sub]; exact hm1
    simpa using hY0V _ h1a h2a
  have hw : c * (sS n - sS m) ∈ V := by
    have h1a : c * (sS n - sS m) ∈ Jc c := ⟨n, m, hnpos, hmpos, rfl⟩
    have h2a : e (c * (sS n - sS m)) ∈ Yi := by
      rw [e_mul_sub]; exact hm2
    exact hYiV _ h1a h2a
  have hyE : sS (n - k) - sS (m - l) + c * (sS n - sS m) ∈ Eall :=
    ⟨i, hi2, ⟨k, l, n, m, hk1, hki, hl1, hli, hkl, hn3, hm3, rfl⟩⟩
  exact ⟨_, hyE, hVV _ hu _ hw⟩

/-- **Every witness of condition (N) has `0` in the `γ`-closure of `E`**: for a group topology `γ` that induces the Bohr topology on every
member of `I_S` (in particular on `J_1` and on the `J_{c_i}`), every `γ`-neighbourhood of `0` meets `E`. -/
theorem condN_nhds_meets_Eall (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (htr : ∀ J ∈ IS, TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ y ∈ Eall, y ∈ W :=
  exists_Eall_mem_nhds γ hγ
    (traceNhd_of_induced_eq γ (zero_mem_Jc 1) (htr _ (Jc_mem_IS 1)))
    (fun i _ => traceNhd_of_induced_eq γ (zero_mem_Jc (cc i)) (htr _ (Jc_mem_IS (cc i))))

#print axioms exists_Eall_mem_nhds
#print axioms condN_nhds_meets_Eall

end Lac
end PVG
