import Mathlib
import LeanCheck.PVGNotGroupArith
import LeanCheck.PVGNotGroupShift
import LeanCheck.PVGIndependence
import LeanCheck.PVGBohr

/-!
# PVG: Lemma 8.78(c) of PVG_v34: the Bohr closure of `E_i` is `E_i` (Lean check)

Scope. `closure_Ei` : `cl_{τ_B}(E_i) ⊆ E_i` (`Ei i` of `PVGNotGroupArith`) for `i ≥ 2`. The proof follows the article: a point of the closure of
`e(E_i)` in `K` is a limit of `e(y)` along an ultrafilter `V'` on the index set (quadruples `(k, l, n, m)`); `k`, `l` are constant along `V'`; if
`V'` is principal the point is `e(y)`, `y ∈ E_i`; otherwise `Z₂ = m_* V'` is free and the limit is a real combination of the limits
`L(Z₁ - k)`, `L(Z₂ - l)`, `L(Z₁)`, `L(Z₂)` (`Z₁ = n_* V'`, `Z₁` principal or free) that is not in `e(ℝ)` by the independence theorem
(`PVGIndependence`), after merging coincident ultrafilters (`indep4`), using that shifts do not fix free ultrafilters (`PVGNotGroupShift`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Classical

namespace PVG
namespace Lac
open Q95

lemma sS_ratio : Tendsto (fun k : ℕ => |sS (k + 1)| / |sS k|) atTop atTop := by
  have h : (fun k : ℕ => |sS (k + 1)| / |sS k|) = fun k : ℕ => (2 : ℝ) ^ (2 * k + 1) := by
    funext k
    rw [abs_of_pos (sS_pos _), abs_of_pos (sS_pos _), sS_succ]
    have := (sS_pos k).ne'
    field_simp
  rw [h]
  refine (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp ?_
  exact tendsto_atTop_mono (fun k => by simp only [id]; omega) tendsto_id

/-- A relation among four limits along free ultrafilters: the merged coefficients vanish. -/
lemma indep4 (A B C D : Ultrafilter ℕ) (hA : Free A) (hB : Free B) (hC : Free C) (hD : Free D)
    (a b c d r : ℝ) (h : a • L sS A + b • L sS B + c • L sS C + d • L sS D = e r) :
    ∀ U ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)),
      (if U = A then a else 0) + (if U = B then b else 0) + (if U = C then c else 0) +
        (if U = D then d else 0) = 0 := by
  have hfree : ∀ U ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)), Free U := by
    intro U hU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl <;> assumption
  refine independence_finset sS (fun k => (sS_pos k).ne') sS_ratio _ hfree
    (fun U => (if U = A then a else 0) + (if U = B then b else 0) + (if U = C then c else 0) +
      (if U = D then d else 0)) r ?_
  beta_reduce
  have add_smul' : ∀ (a b : ℝ) (x : K), (a + b) • x = a • x + b • x := fun a b x => add_smul a b x
  have zero_smul' : ∀ x : K, (0 : ℝ) • x = 0 := fun x => zero_smul ℝ x
  simp only [add_smul', ite_smul, zero_smul', Finset.sum_add_distrib, ite_self]
  have hAm : A ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)) := by simp
  have hBm : B ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)) := by simp
  have hCm : C ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)) := by simp
  have hDm : D ∈ ({A, B, C, D} : Finset (Ultrafilter ℕ)) := by simp
  rw [Finset.sum_ite_eq' _ A, Finset.sum_ite_eq' _ B, Finset.sum_ite_eq' _ C,
    Finset.sum_ite_eq' _ D]
  simpa [hAm, hBm, hCm, hDm] using h

lemma L_pure (y : ℕ → ℝ) (a : ℕ) : L y (pure a) = e (y a) :=
  L_eq_of_tendsto (tendsto_pure_left.2 (fun s hs => mem_of_mem_nhds hs))

lemma not_free_iff {Z : Ultrafilter ℕ} (h : ¬ Free Z) : ∃ a, Z = pure a := by
  unfold Free at h
  rw [Filter.le_def] at h
  push_neg at h
  obtain ⟨s, hs, hsZ⟩ := h
  have hfin : sᶜ.Finite := Filter.mem_cofinite.1 hs
  have hmem : sᶜ ∈ (Z : Filter ℕ) := Ultrafilter.compl_mem_iff_notMem.2 hsZ
  obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem hfin hmem
  exact ⟨a, ha⟩

/-- The index tuples `(k, l, n, m)` of `E_i`. -/
def Pidx (i : ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Prop :=
  1 ≤ q.1 ∧ q.1 ≤ i ∧ 1 ≤ q.2.1 ∧ q.2.1 ≤ i ∧ q.1 ≠ q.2.1 ∧ MM i ≤ q.2.2.1 ∧ q.2.2.1 < q.2.2.2

/-- The element of `E_i` with index tuple `q`. -/
def Ff (i : ℕ) (q : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  sS (q.2.2.1 - q.1) - sS (q.2.2.2 - q.2.1) + cc i * (sS q.2.2.1 - sS q.2.2.2)

lemma Ei_eq_image (i : ℕ) : Ei i = Ff i '' {q | Pidx i q} := by
  ext y
  constructor
  · rintro ⟨k, l, n, m, h1, h2, h3, h4, h5, h6, h7, rfl⟩
    exact ⟨(k, l, n, m), ⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩
  · rintro ⟨⟨k, l, n, m⟩, ⟨h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩
    exact ⟨k, l, n, m, h1, h2, h3, h4, h5, h6, h7, rfl⟩

lemma e_Ff (i : ℕ) (q : ℕ × ℕ × ℕ × ℕ) :
    e (Ff i q) = e (sS (q.2.2.1 - q.1)) - e (sS (q.2.2.2 - q.2.1)) + cc i • e (sS q.2.2.1) -
      cc i • e (sS q.2.2.2) := by
  unfold Ff
  rw [smul_e, smul_e]
  have h1 := eHom.map_add (sS (q.2.2.1 - q.1) - sS (q.2.2.2 - q.2.1)) (cc i * (sS q.2.2.1 - sS q.2.2.2))
  have h2 := eHom.map_sub (sS (q.2.2.1 - q.1)) (sS (q.2.2.2 - q.2.1))
  have h3 := eHom.map_sub (cc i * sS q.2.2.1) (cc i * sS q.2.2.2)
  have h4 : cc i * (sS q.2.2.1 - sS q.2.2.2) = cc i * sS q.2.2.1 - cc i * sS q.2.2.2 := by ring
  simp only [eHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1 h2 h3
  rw [h1, h2, h4, h3]
  abel

lemma shiftU_map {ι : Type*} (V : Ultrafilter ι) (f : ι → ℕ) (d : ℕ) :
    shiftU d (V.map f) = V.map (fun q => f q - d) := by
  unfold shiftU
  rw [Ultrafilter.map_map]
  rfl

lemma e_comb (a b x c : ℝ) : e (a + c * b - x) = e a + c • e b - e x := by
  have h1 := eHom.map_sub (a + c * b) x
  have h2 := eHom.map_add a (c * b)
  simp only [eHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1 h2
  rw [h1, h2, smul_e]

lemma const_of_bdd {ι : Type*} (V : Ultrafilter ι) (f : ι → ℕ) (B : ℕ)
    (h : ∀ᶠ q in (V : Filter ι), f q ≤ B) : ∃ a, ∀ᶠ q in (V : Filter ι), f q = a := by
  have hmem : Set.Iic B ∈ ((V.map f : Ultrafilter ℕ) : Filter ℕ) := by
    rw [Ultrafilter.coe_map, Filter.mem_map]
    exact h
  obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem (Set.finite_Iic B) hmem
  refine ⟨a, ?_⟩
  have h1 : ({a} : Set ℕ) ∈ ((V.map f : Ultrafilter ℕ) : Filter ℕ) := by
    rw [ha]; exact Filter.mem_pure.2 rfl
  rw [Ultrafilter.coe_map, Filter.mem_map] at h1
  exact h1

/-- **Lemma 8.78(c)**: the Bohr closure of `E_i` is `E_i`. -/
theorem closure_Ei {i : ℕ} (hi : 2 ≤ i) {x : ℝ} (hx : x ∈ @closure ℝ bohrTop (Ei i)) : x ∈ Ei i := by
  classical
  letI : TopologicalSpace ℝ := bohrTop
  have hind : Topology.IsInducing e := ⟨rfl⟩
  have hx' : e x ∈ closure (e '' Ei i) := by
    have := hind.closure_eq_preimage_closure_image (Ei i)
    rw [this] at hx
    exact hx
  obtain ⟨U, hUmem, hUle⟩ := mem_closure_iff_ultrafilter.1 hx'
  set g : ℕ × ℕ × ℕ × ℕ → K := fun q => e (Ff i q) with hg
  set s0 : Set (ℕ × ℕ × ℕ × ℕ) := {q | Pidx i q} with hs0
  have hne : (Filter.comap g (U : Filter K) ⊓ 𝓟 s0).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro W hW
    obtain ⟨t, ht, htW⟩ := Filter.mem_comap.1 hW
    have hmem : t ∩ e '' Ei i ∈ (U : Filter K) := Filter.inter_mem ht hUmem
    obtain ⟨z, hzt, y, hyE, rfl⟩ := Filter.nonempty_of_mem hmem
    rw [Ei_eq_image] at hyE
    obtain ⟨q, hq, rfl⟩ := hyE
    exact ⟨q, htW hzt, hq⟩
  set V : Ultrafilter (ℕ × ℕ × ℕ × ℕ) := Ultrafilter.of (Filter.comap g (U : Filter K) ⊓ 𝓟 s0) with hV
  have hVle : (V : Filter (ℕ × ℕ × ℕ × ℕ)) ≤ Filter.comap g (U : Filter K) ⊓ 𝓟 s0 := Ultrafilter.of_le _
  have hPmem : s0 ∈ (V : Filter (ℕ × ℕ × ℕ × ℕ)) := hVle (Filter.mem_inf_of_right (Filter.mem_principal_self _))
  have htend : Tendsto g (V : Filter (ℕ × ℕ × ℕ × ℕ)) (𝓝 (e x)) :=
    (Filter.tendsto_iff_comap.2 (hVle.trans inf_le_left)).mono_right hUle
  have hP : ∀ᶠ q in (V : Filter (ℕ × ℕ × ℕ × ℕ)), Pidx i q := hPmem
  -- the principal case
  have hExt : ∀ q₀, V = pure q₀ → x ∈ Ei i := by
    intro q₀ hq₀
    have hP0 : Pidx i q₀ := by
      have : s0 ∈ ((pure q₀ : Ultrafilter _) : Filter _) := hq₀ ▸ hPmem
      simpa [hs0] using this
    rw [hq₀, Ultrafilter.coe_pure] at htend
    have h1 : g q₀ = e x :=
      tendsto_nhds_unique ((tendsto_pure_pure g q₀).mono_right (pure_le_nhds _)) htend
    have h2 : Ff i q₀ = x := e_injective' h1
    rw [Ei_eq_image]
    exact ⟨q₀, hP0, h2⟩
  -- k and l are constant
  obtain ⟨k₀, hk⟩ := const_of_bdd V (fun q => q.1) i (hP.mono fun q hq => hq.2.1)
  obtain ⟨l₀, hl⟩ := const_of_bdd V (fun q => q.2.1) i (hP.mono fun q hq => hq.2.2.2.1)
  obtain ⟨q1, ⟨hq1k, hq1l⟩, hq1P⟩ := ((hk.and hl).and hP).exists
  obtain ⟨hk1, hki, hl1, hli, hkl, hMn, hnm⟩ := hq1P
  have hk1' : 1 ≤ k₀ := by rw [← hq1k]; exact hk1
  have hl1' : 1 ≤ l₀ := by rw [← hq1l]; exact hl1
  have hkl' : k₀ ≠ l₀ := by rw [← hq1k, ← hq1l]; exact hkl
  set Z1 : Ultrafilter ℕ := V.map (fun q => q.2.2.1) with hZ1
  set Z2 : Ultrafilter ℕ := V.map (fun q => q.2.2.2) with hZ2
  by_cases hZ2f : Free Z2
  swap
  · -- `Z₂` principal: `V` is principal
    obtain ⟨m₀, hm₀⟩ := not_free_iff hZ2f
    have hm : ∀ᶠ q in (V : Filter (ℕ × ℕ × ℕ × ℕ)), q.2.2.2 = m₀ := by
      have h1 : ({m₀} : Set ℕ) ∈ ((Z2 : Ultrafilter ℕ) : Filter ℕ) := by
        rw [hm₀]; exact Filter.mem_pure.2 rfl
      rw [hZ2, Ultrafilter.coe_map, Filter.mem_map] at h1
      exact h1
    set T : Set (ℕ × ℕ × ℕ × ℕ) := (fun n => (k₀, l₀, n, m₀)) '' Set.Iic m₀ with hT
    have hTmem : T ∈ (V : Filter (ℕ × ℕ × ℕ × ℕ)) := by
      filter_upwards [hk, hl, hm, hP] with q h1 h2 h3 h4
      refine ⟨q.2.2.1, ?_, ?_⟩
      · simp only [Set.mem_Iic]
        have := h4.2.2.2.2.2.2
        omega
      · show (k₀, l₀, q.2.2.1, m₀) = q
        rw [← h1, ← h2, ← h3]
    obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem ((Set.finite_Iic m₀).image _) hTmem
    exact hExt a ha
  -- `Z₂` free
  set c : ℝ := cc i with hc
  have hc3 : 3 ≤ c := three_le_cc (by omega)
  have hEq : ∀ᶠ q in (V : Filter (ℕ × ℕ × ℕ × ℕ)), g q = e (sS (q.2.2.1 - k₀)) - e (sS (q.2.2.2 - l₀)) +
      c • e (sS q.2.2.1) - c • e (sS q.2.2.2) := by
    filter_upwards [hk, hl] with q h1 h2
    show e (Ff i q) = _
    rw [e_Ff, h1, h2]
  have T1 := tendsto_e_comp sS V (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1 - k₀)
  have T2 := tendsto_e_comp sS V (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.2 - l₀)
  have T3 := tendsto_e_comp sS V (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1)
  have T4 := tendsto_e_comp sS V (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.2)
  have hsm : ∀ κ : K, Tendsto (fun κ' : K => c • κ') (𝓝 κ) (𝓝 (c • κ)) :=
    fun κ => (continuous_smul_const c).tendsto κ
  have Tlim := ((T1.sub T2).add ((hsm _).comp T3)).sub ((hsm _).comp T4)
  have huniq := tendsto_nhds_unique (htend.congr' hEq) Tlim
  have hL1 : V.map (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1 - k₀) = shiftU k₀ Z1 :=
    (shiftU_map V (fun q => q.2.2.1) k₀).symm
  have hL2 : V.map (fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.2 - l₀) = shiftU l₀ Z2 :=
    (shiftU_map V (fun q => q.2.2.2) l₀).symm
  rw [hL1, hL2] at huniq
  have huniq' : e x = L sS (shiftU k₀ Z1) - L sS (shiftU l₀ Z2) + c • L sS Z1 - c • L sS Z2 :=
    huniq
  by_cases hZ1f : Free Z1
  · exfalso
    have hA : Free (shiftU k₀ Z1) := shiftU_free hZ1f k₀
    have hB : Free (shiftU l₀ Z2) := shiftU_free hZ2f l₀
    have h4 : (1 : ℝ) • L sS (shiftU k₀ Z1) + (-1 : ℝ) • L sS (shiftU l₀ Z2) + c • L sS Z1 +
        (-c) • L sS Z2 = e x := by
      rw [huniq']
      have one_smul' : ∀ y : K, (1 : ℝ) • y = y := fun y => one_smul ℝ y
      have neg_smul' : ∀ (a : ℝ) (y : K), (-a) • y = -(a • y) := fun a y => neg_smul a y
      simp only [one_smul', neg_smul']
      abel
    have h5 := indep4 _ _ _ _ hA hB hZ1f hZ2f 1 (-1) c (-c) x h4
    have hAC : shiftU k₀ Z1 ≠ Z1 := shiftU_ne hZ1f hk1'
    by_cases hCD : Z1 = Z2
    · have hAB : shiftU k₀ Z1 ≠ shiftU l₀ Z2 := by rw [← hCD]; exact shiftU_inj hZ1f hkl'
      have hAD : shiftU k₀ Z1 ≠ Z2 := by rw [← hCD]; exact hAC
      have := h5 (shiftU k₀ Z1) (by simp)
      rw [if_pos rfl, if_neg hAB, if_neg hAC, if_neg hAD] at this
      norm_num at this
    · have := h5 Z1 (by simp)
      rw [if_neg hAC.symm, if_pos rfl, if_neg hCD] at this
      by_cases hCB : Z1 = shiftU l₀ Z2
      · rw [if_pos hCB] at this
        linarith
      · rw [if_neg hCB] at this
        linarith
  · exfalso
    obtain ⟨n₀, hn₀⟩ := not_free_iff hZ1f
    have hL1' : L sS (shiftU k₀ Z1) = e (sS (n₀ - k₀)) := by
      rw [hn₀]
      unfold shiftU
      rw [Ultrafilter.map_pure, L_pure]
    have hL3' : L sS Z1 = e (sS n₀) := by rw [hn₀, L_pure]
    rw [hL1', hL3'] at huniq'
    have key : L sS (shiftU l₀ Z2) + c • L sS Z2 = e (sS (n₀ - k₀) + c * sS n₀ - x) := by
      rw [e_comb, huniq']
      abel
    have hne : shiftU l₀ Z2 ≠ Z2 := shiftU_ne hZ2f hl1'
    have hWi : Function.Injective (![shiftU l₀ Z2, Z2] : Fin 2 → Ultrafilter ℕ) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
      · exact absurd hab hne
      · exact absurd hab.symm hne
    have hWf : ∀ j, Free ((![shiftU l₀ Z2, Z2] : Fin 2 → Ultrafilter ℕ) j) := by
      intro j
      fin_cases j
      · exact shiftU_free hZ2f l₀
      · exact hZ2f
    exact independence sS (fun k => (sS_pos k).ne') sS_ratio ![shiftU l₀ Z2, Z2] hWi hWf ![1, c]
      ⟨0, by simp⟩ (sS (n₀ - k₀) + c * sS n₀ - x) (by simpa [Fin.sum_univ_two] using key)

end Lac
end PVG
