import Mathlib
import LeanCheck.PVGTwoFinest

/-!
# PVGtwo: the singleton parity lemma and the number of serving topologies (Lean check)

The statements are those of ChatGPT's audit of Section 7.6.

* `odd_points_gen` : for integers `L k` with `L (k+1) - L k → ∞` and any strictly increasing `e`, every neighbourhood of
  `0` for the topology of `δ_k = 2^(-L k)` contains a point at which exactly one of the integers nearest to `δ_k x` is odd,
  and that one has its index in the range of `e`;
* `many_embed` : for the sparse sequence the sets of branches `H` of the binary tree give serving topologies `Gam H`,
  finer than `γ_δ`, with `H ⊆ H'` exactly when `Gam H'` is finer than `Gam H`;
* `many_card` : there are exactly `2 ^ continuum` group topologies that serve `A(δ)` and are finer than `γ_δ`.

Order of topologies as in Mathlib: `γ₁ ≤ γ₂` means that `γ₁` is finer. Sequences are indexed from `0`.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise Cardinal

namespace PVG
namespace Two
open Q95 Lac

theorem odd_points_gen (L : ℕ → ℕ) (hL : ∀ G : ℕ, ∃ K, ∀ k, K ≤ k → L k + G ≤ L (k + 1))
    (e : ℕ → ℕ) (he : StrictMono e) (F : Finset ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∃ x : ℝ, x ∈ bset F η' ∧ (∀ k, dint (x / 2 ^ L k) ≤ η) ∧ ∃ i0 : ℕ, (∃ j, e j = i0) ∧
      (∀ k, k ≠ i0 → Even (round (x / 2 ^ L k))) ∧ Odd (round (x / 2 ^ L i0)) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((2 : ℝ) ^ m)⁻¹ * 2 ≤ min η (1 / 8) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (x := min η (1 / 8) / 2) (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
    rw [one_div, inv_pow] at hm
    exact ⟨m, by linarith⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at hm
      have := hm.trans (min_le_right _ _)
      norm_num at this
    · exact h
  set N := 2 ^ m with hN
  have hNr : (N : ℝ) = 2 ^ m := by rw [hN]; push_cast; rfl
  have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
  set G := m + 1 with hG
  obtain ⟨K0, hK0⟩ := hL G
  have hstep : ∀ a b : ℕ, K0 ≤ a → a ≤ b → L a + (b - a) * G ≤ L b := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h1 := hK0 b (ha.trans hab)
      have e1 : b + 1 - a = (b - a) + 1 := by omega
      rw [e1, add_mul, one_mul]
      omega
  have hgap : ∀ a b : ℕ, K0 ≤ a → a < b → L a + G ≤ L b := by
    intro a b ha hab
    have h1 := hstep a b ha hab.le
    have h2 : G ≤ (b - a) * G := Nat.le_mul_of_pos_left G (by omega)
    omega
  set B0 := ∑ k ∈ Finset.range K0, L k with hB0
  set T := K0 + B0 + m + 1 with hT
  have hlarge : ∀ i, T ≤ i → ∀ k, k < i → L k + G ≤ L i := by
    intro i hi k hk
    by_cases hkK : k < K0
    · have h1 : L k ≤ B0 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hkK)
      have h2 := hstep K0 i le_rfl (by omega)
      have h3 : B0 + G ≤ (i - K0) * G := by
        have h4 : (B0 + m + 1) * G ≤ (i - K0) * G := Nat.mul_le_mul_right G (by omega)
        refine le_trans ?_ h4
        have h5 : B0 ≤ B0 * G := Nat.le_mul_of_pos_right B0 (by omega)
        have e2 : (B0 + m + 1) * G = B0 * G + (m + 1) * G := by ring
        have h6 : G ≤ (m + 1) * G := Nat.le_mul_of_pos_left G (by omega)
        omega
      omega
    · exact hgap k i (not_lt.1 hkK) hk
  have habove : ∀ i, T ≤ i → ∀ k, i < k → L i + G ≤ L k := fun i hi k hk => hgap i k (by omega) hk
  set u : ℕ → (F → AddCircle (1 : ℝ)) := fun n c => (((c : ℝ) * 2 ^ (L (e n) - m) : ℝ) : AddCircle (1 : ℝ)) with hu
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  obtain ⟨lim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  set ρ := η' / (4 * N) with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨M0, hM0⟩ := Metric.tendsto_atTop.1 hlim ρ hρ0
  set M := M0 + T with hM
  set i : ℕ → ℕ := fun j => e (φ (M + j)) with hi
  have hinc : StrictMono i := fun a b hab => he (hφ (by omega))
  have hige : ∀ j, T ≤ i j := fun j =>
    le_trans (by omega) ((show M + j ≤ φ (M + j) from hφ.id_le (M + j)).trans (he.id_le (φ (M + j))))
  have hmL : ∀ j, m ≤ L (i j) := by
    intro j
    have h1 := hlarge (i j) (hige j) 0 (by have := hige j; omega)
    omega
  have hclose : ∀ j (c : F), dist (u (φ (M + j)) c) (lim c) < ρ := by
    intro j c
    exact lt_of_le_of_lt (dist_le_pi_dist _ _ c) (hM0 (M + j) (by omega))
  set x : ℝ := (∑ j ∈ Finset.range N, (2 : ℝ) ^ (L (i (j + 1)) - m)) - 2 ^ L (i 0) with hx
  set A : ℕ → ℕ → ℤ := fun k j => if L k + m ≤ L (i (j + 1)) then 2 ^ (L (i (j + 1)) - m - L k) else 0 with hA
  set As : ℕ → ℕ → ℝ := fun k j =>
    if L k + m ≤ L (i (j + 1)) then 0 else 2 ^ (L (i (j + 1)) - m) / 2 ^ L k with hAs
  set B : ℕ → ℤ := fun k => if L k ≤ L (i 0) then 2 ^ (L (i 0) - L k) else 0 with hB
  set Bs : ℕ → ℝ := fun k => if L k ≤ L (i 0) then 0 else 2 ^ L (i 0) / 2 ^ L k with hBs
  set n : ℕ → ℤ := fun k => (∑ j ∈ Finset.range N, A k j) - B k with hn
  set s : ℕ → ℝ := fun k => (∑ j ∈ Finset.range N, As k j) - Bs k with hs
  have hsplit : ∀ k, x / 2 ^ L k = (n k : ℝ) + s k := by
    intro k
    have hp : (0 : ℝ) < 2 ^ L k := by positivity
    have t1 : ∀ j, (2 : ℝ) ^ (L (i (j + 1)) - m) / 2 ^ L k = (A k j : ℝ) + As k j := by
      intro j
      simp only [hA, hAs]
      split_ifs with h
      · have e1 : L (i (j + 1)) - m = (L (i (j + 1)) - m - L k) + L k := by omega
        rw [add_zero]
        push_cast
        rw [div_eq_iff hp.ne', ← pow_add, ← e1]
      · simp
    have t2 : (2 : ℝ) ^ L (i 0) / 2 ^ L k = (B k : ℝ) + Bs k := by
      simp only [hB, hBs]
      split_ifs with h
      · have e1 : L (i 0) = (L (i 0) - L k) + L k := by omega
        rw [add_zero]
        push_cast
        rw [div_eq_iff hp.ne', ← pow_add, ← e1]
      · simp
    have e0 : x / 2 ^ L k = (∑ j ∈ Finset.range N, (2 : ℝ) ^ (L (i (j + 1)) - m) / 2 ^ L k) -
        2 ^ L (i 0) / 2 ^ L k := by
      rw [hx, sub_div, Finset.sum_div]
    rw [e0, t2, Finset.sum_congr rfl fun j _ => t1 j, Finset.sum_add_distrib]
    simp only [hn, hs]
    push_cast
    ring
  have hsmall : ∀ k, |s k| ≤ ((2 : ℝ) ^ m)⁻¹ * 2 := by
    intro k
    have hAs0 : ∀ j, 0 ≤ As k j := by
      intro j; simp only [hAs]; split_ifs
      · exact le_rfl
      · positivity
    have hBs0 : 0 ≤ Bs k := by
      simp only [hBs]; split_ifs
      · exact le_rfl
      · positivity
    have hlt : ∀ a : ℕ, i a < k → (2 : ℝ) ^ L (i a) / 2 ^ L k ≤ ((2 : ℝ) ^ G)⁻¹ := by
      intro a ha
      have h1 := habove (i a) (hige a) k ha
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ one_le_two h1
    have hterm : ∀ j ∈ Finset.range N, As k j ≤
        (if i (j + 1) = k then ((2 : ℝ) ^ m)⁻¹ else 0) + ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ G)⁻¹ := by
      intro j _
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ G)⁻¹ := by positivity
      simp only [hAs]
      split_ifs with h h' h'
      · exfalso
        rw [h'] at h
        omega
      · simpa using h0
      · have e1 : (2 : ℝ) ^ (L (i (j + 1)) - m) / 2 ^ L k = ((2 : ℝ) ^ m)⁻¹ := by
          rw [h', pow_sub₀ _ two_ne_zero (by rw [← h']; exact hmL _)]
          field_simp
        rw [e1]
        exact le_add_of_nonneg_right h0
      · have hlt' : i (j + 1) < k := by
          rcases lt_trichotomy (i (j + 1)) k with hh | hh | hh
          · exact hh
          · exact absurd hh h'
          · have := hlarge (i (j + 1)) (hige _) k hh
            exact absurd (show L k + m ≤ L (i (j + 1)) by omega) h
        have e1 : (2 : ℝ) ^ (L (i (j + 1)) - m) / 2 ^ L k =
            ((2 : ℝ) ^ m)⁻¹ * (2 ^ L (i (j + 1)) / 2 ^ L k) := by
          rw [pow_sub₀ _ two_ne_zero (hmL _)]
          ring
        rw [e1, zero_add]
        exact mul_le_mul_of_nonneg_left (hlt _ hlt') (by positivity)
    have hsum : ∑ j ∈ Finset.range N, As k j ≤ ((2 : ℝ) ^ m)⁻¹ + ((2 : ℝ) ^ G)⁻¹ := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNr,
        mul_inv_cancel_left₀ (by positivity : (2 : ℝ) ^ m ≠ 0)]
      refine add_le_add ?_ le_rfl
      have h1 : ((Finset.range N).filter fun j => i (j + 1) = k).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        have h2 := (Finset.mem_filter.1 ha).2
        have h3 := (Finset.mem_filter.1 hb).2
        have := hinc.injective (h2.trans h3.symm)
        omega
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast h1)
    have hBsle : Bs k ≤ ((2 : ℝ) ^ G)⁻¹ := by
      simp only [hBs]
      split_ifs with h
      · positivity
      · refine hlt 0 ?_
        rcases lt_trichotomy (i 0) k with hh | hh | hh
        · exact hh
        · exact absurd (le_of_eq (congrArg L hh.symm)) h
        · have := hlarge (i 0) (hige 0) k hh
          exact absurd (show L k ≤ L (i 0) by omega) h
    have hGm : ((2 : ℝ) ^ G)⁻¹ * 2 = ((2 : ℝ) ^ m)⁻¹ := by
      rw [hG, pow_succ]; field_simp
    have h0 : 0 ≤ ∑ j ∈ Finset.range N, As k j := Finset.sum_nonneg fun j _ => hAs0 j
    have hGpos : 0 ≤ ((2 : ℝ) ^ G)⁻¹ := by positivity
    simp only [hs]
    rw [abs_le]
    constructor <;> linarith
  have hs8 : ∀ k, |s k| ≤ 1 / 8 := fun k => (hsmall k).trans (hm.trans (min_le_right _ _))
  have hround : ∀ k, round (x / 2 ^ L k) = n k := by
    intro k
    refine round_near _ _ ?_
    rw [hsplit k, add_sub_cancel_left]
    exact lt_of_le_of_lt (hs8 k) (by norm_num)
  have hAeven : ∀ k j, Even (A k j) := by
    intro k j
    simp only [hA]
    split_ifs with h
    · refine (even_two).pow_of_ne_zero ?_
      have hlt : k < i (j + 1) := by
        rcases lt_trichotomy k (i (j + 1)) with hh | hh | hh
        · exact hh
        · rw [hh] at h; omega
        · have := habove (i (j + 1)) (hige _) k hh
          omega
      have h1 := hlarge (i (j + 1)) (hige _) k hlt
      omega
    · exact Even.zero
  have hsumeven : ∀ k, Even (∑ j ∈ Finset.range N, A k j) := fun k =>
    Finset.even_sum _ fun j _ => hAeven k j
  have hneven : ∀ k, k ≠ i 0 → Even (n k) := by
    intro k hk
    refine (hsumeven k).sub ?_
    simp only [hB]
    split_ifs with h
    · refine (even_two).pow_of_ne_zero ?_
      have hlt : k < i 0 := by
        rcases lt_trichotomy k (i 0) with hh | hh | hh
        · exact hh
        · exact absurd hh hk
        · have := habove (i 0) (hige 0) k hh
          omega
      have := hlarge (i 0) (hige 0) k hlt
      omega
    · exact Even.zero
  have hnodd : Odd (n (i 0)) := by
    refine (hsumeven (i 0)).sub_odd ?_
    simp only [hB, if_pos le_rfl, Nat.sub_self, pow_zero]
    exact odd_one
  refine ⟨x, ?_, ?_, i 0, ⟨φ (M + 0), rfl⟩, fun k hk => by rw [hround]; exact hneven k hk,
    by rw [hround]; exact hnodd⟩
  · intro c hc
    set c' : F := ⟨c, hc⟩ with hc'
    have e1 : ((c * x : ℝ) : AddCircle (1 : ℝ)) =
        ∑ j ∈ Finset.range N, (u (φ (M + (j + 1))) c' - u (φ (M + 0)) c') := by
      have e2 : c * x = (∑ j ∈ Finset.range N, c * 2 ^ (L (i (j + 1)) - m)) - N • (c * 2 ^ (L (i 0) - m)) := by
        rw [hx, mul_sub, Finset.mul_sum, nsmul_eq_mul, hNr]
        congr 1
        have e3 : (2 : ℝ) ^ L (i 0) = 2 ^ m * 2 ^ (L (i 0) - m) := by
          rw [← pow_add]; congr 1; have := hmL 0; omega
        rw [e3]; ring
      rw [e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      rw [AddCircle.coe_sub, AddCircle.coe_nsmul]
      congr 1
      exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
    show ‖((c * x : ℝ) : AddCircle (1 : ℝ))‖ < η'
    rw [e1]
    have h1 : ∀ j ∈ Finset.range N, ‖u (φ (M + (j + 1))) c' - u (φ (M + 0)) c'‖ ≤ ρ + ρ := by
      intro j _
      rw [← dist_eq_norm]
      have h2 := hclose (j + 1) c'
      have h3 := hclose 0 c'
      have := dist_triangle_right (u (φ (M + (j + 1))) c') (u (φ (M + 0)) c') (lim c')
      linarith
    refine lt_of_le_of_lt ((norm_sum_le _ _).trans (Finset.sum_le_sum h1)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e4 : (N : ℝ) * (ρ + ρ) = η' / 2 := by
      rw [hρ]; field_simp; ring
    rw [e4]
    exact half_lt_self hη'
  · intro k
    rw [hsplit k, add_comm, show s k + (n k : ℝ) = s k - ((-n k : ℤ) : ℝ) by push_cast; ring, dint_sub_int]
    exact (dint_le_abs _).trans ((hsmall k).trans (hm.trans (min_le_left _ _)))

/-! ## Many serving topologies -/

lemma Lv_gaps : ∀ G : ℕ, ∃ K, ∀ k, K ≤ k → Lv k + G ≤ Lv (k + 1) := by
  intro G
  refine ⟨G, fun k hk => ?_⟩
  have h := Lv_gap (Nat.lt_succ_self k)
  rw [Nat.succ_eq_add_one] at h
  omega

noncomputable def thJ (J : Set ℕ) : ℕ → AddCircle (1 : ℝ) :=
  fun k => open Classical in if k ∈ J then ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else 0

noncomputable def tauJ (J : Set ℕ) : TopologicalSpace ℝ :=
  Classical.choose (exists_par dlt2 dlt2_tendsto (thJ J))

lemma tauJ_spec (J : Set ℕ) : @IsTopologicalAddGroup ℝ (tauJ J) _ ∧
    (@nhds ℝ (tauJ J) 0).HasBasis (fun p : ℝ × ℝ => 0 < p.1 ∧ p.1 ≤ 1 / 5 ∧ 0 < p.2)
      (fun p => Nset dlt2 (thJ J) p.1 p.2) :=
  Classical.choose_spec (exists_par dlt2 dlt2_tendsto (thJ J))

/-- `γ_{δ,θ}` for `θ = 1/2` on `J` and `0` elsewhere. -/
noncomputable def gamJ (J : Set ℕ) : TopologicalSpace ℝ := tauJ J ⊓ bohrTop

lemma gamJ_nhds (J : Set ℕ) : @nhds ℝ (gamJ J) 0 = @nhds ℝ (tauJ J) 0 ⊓ @nhds ℝ bohrTop 0 :=
  @nhds_inf ℝ (tauJ J) bohrTop 0

lemma gamJ_group (J : Set ℕ) : @IsTopologicalAddGroup ℝ (gamJ J) _ :=
  isTopologicalAddGroup_inf (tauJ_spec J).1 bohr_group

lemma usual_le_tauJ (J : Set ℕ) : euclidNhds 0 ≤ @nhds ℝ (tauJ J) 0 := by
  intro W hW
  obtain ⟨⟨ε, η⟩, ⟨hε, hε5, hη⟩, hsub⟩ := (tauJ_spec J).2.mem_iff.1 hW
  simp only at hε hε5 hη hsub
  have hball : Metric.ball (0 : ℝ) ε ∈ euclidNhds 0 := Metric.ball_mem_nhds _ hε
  refine Filter.mem_of_superset hball fun x hx => hsub ?_
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
  have hk : ∀ k, |dlt2 k * x| < ε := by
    intro k
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg x) (dlt2_le_one k)) hx
  refine ⟨fun k => (dint_le_abs _).trans (hk k).le, ?_⟩
  have hz : Phit dlt2 (thJ J) x = 0 := by
    unfold Phit
    have : (fun k => round (dlt2 k * x) • thJ J k) = fun _ => 0 := by
      funext k
      have : round (dlt2 k * x) = 0 := by
        refine round_near _ 0 ?_
        rw [Int.cast_zero, sub_zero]
        exact lt_of_lt_of_le (hk k) (hε5.trans (by norm_num))
      rw [this, zero_smul]
    rw [this, finsum_zero]
  show ‖Phit dlt2 (thJ J) x‖ ≤ η
  rw [hz, norm_zero]
  exact hη.le

lemma gamJ_le_gam (J : Set ℕ) : gamJ J ≤ gamTop dlt2 := by
  refine le_of_nhds_zero _ _ (gamJ_group J) (gam_group dlt2) fun W hW => ?_
  obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam dlt2 W).1 hW
  have hε : 0 < min η (1 / 5 : ℝ) := lt_min hη (by norm_num)
  rw [gamJ_nhds]
  have h1 : Nset dlt2 (thJ J) (min η (1 / 5)) 1 ∈ @nhds ℝ (tauJ J) 0 :=
    (tauJ_spec J).2.mem_of_mem (i := (min η (1 / 5), 1)) ⟨hε, min_le_right _ _, one_pos⟩
  refine Filter.mem_of_superset (Filter.inter_mem_inf h1 hB) fun x hx => ?_
  exact hBW x hx.2 fun k => (hx.1.1 k).trans (min_le_left _ _)

lemma gamJ_serves (J : Set ℕ) : Serves (gamJ J) A2 := by
  refine ⟨gamJ_group J, (gamJ_le_gam J).trans (gam_le_bohr _), ?_, ?_, fun a ha => ?_⟩
  · intro h
    have h1 : bohrTop ≤ gamTop dlt2 := h ▸ gamJ_le_gam J
    exact serves_dlt2.2.2.1 (le_antisymm (gam_le_bohr _) h1)
  · rw [gamJ_nhds]
    exact le_inf (usual_le_tauJ J) (nhds_mono continuous_e.le_induced)
  · refine tb_join (tauJ J) bohrTop (tauJ_spec J).1 bohr_group _
      (par_tb dlt2 dlt2_tendsto (thJ J) _ (tauJ_spec J).2 a ha) ?_
    intro W hW
    obtain ⟨F, hF⟩ := pre_bohr W hW
    exact ⟨F, fun y _ => hF y⟩

/-- The code of the first `n` entries of a binary sequence. -/
def code (t : ℕ → Bool) (n : ℕ) : ℕ := 2 ^ n + ∑ i ∈ Finset.range n, if t i then 2 ^ i else 0

lemma code_lt (t : ℕ → Bool) (n : ℕ) : ∑ i ∈ Finset.range n, (if t i then 2 ^ i else 0) < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    split_ifs <;> omega

lemma code_range (t : ℕ → Bool) (n : ℕ) : 2 ^ n ≤ code t n ∧ code t n < 2 ^ (n + 1) := by
  have := code_lt t n
  unfold code
  rw [pow_succ]
  omega

lemma code_strict (t : ℕ → Bool) : StrictMono (code t) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact lt_of_lt_of_le (code_range t n).2 (code_range t (n + 1)).1

lemma code_eq {t s : ℕ → Bool} {n m : ℕ} (h : code t n = code s m) : n = m ∧ ∀ i < n, t i = s i := by
  have hnm : n = m := by
    have h1 := code_range t n
    have h2 := code_range s m
    rw [h] at h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : 2 ^ (n + 1) ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hlt
      omega
    · have : 2 ^ (m + 1) ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hlt
      omega
  subst hnm
  refine ⟨rfl, ?_⟩
  have key : ∀ k, ∑ i ∈ Finset.range k, (if t i then 2 ^ i else 0) =
      ∑ i ∈ Finset.range k, (if s i then 2 ^ i else 0) → ∀ i < k, t i = s i := by
    intro k
    induction k with
    | zero => intro _ i hi; omega
    | succ k ih =>
      intro hk i hi
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hk
      have h1 := code_lt t k
      have h2 := code_lt s k
      have hbit : t k = s k := by
        cases ht : t k <;> cases hs : s k <;> simp [ht, hs] at hk ⊢ <;> omega
      have hrest : ∑ i ∈ Finset.range k, (if t i then 2 ^ i else 0) =
          ∑ i ∈ Finset.range k, (if s i then 2 ^ i else 0) := by
        rw [hbit] at hk; exact Nat.add_right_cancel hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h3 | h3
      · exact ih hrest i h3
      · rw [h3]; exact hbit
  refine key n ?_
  unfold code at h
  omega

def Jt' (t : ℕ → Bool) : Set ℕ := range (code t)

/-- Away from finitely many other branches. -/
lemma code_avoid (t : ℕ → Bool) (F : Finset (ℕ → Bool)) (hF : t ∉ F) :
    ∃ N0, ∀ n, N0 ≤ n → ∀ s ∈ F, code t n ∉ Jt' s := by
  classical
  have h : ∀ s : ℕ → Bool, s ≠ t → ∃ i, t i ≠ s i := fun s hs => by
    by_contra hc
    push Not at hc
    exact hs (funext fun i => (hc i).symm)
  choose! d hd using h
  refine ⟨F.sup d + 1, fun n hn s hs => ?_⟩
  rintro ⟨m, hm⟩
  have hst : s ≠ t := fun h => hF (h ▸ hs)
  obtain ⟨h1, h2⟩ := code_eq hm.symm
  have h3 : d s < n := lt_of_le_of_lt (Finset.le_sup (f := d) hs) (by omega)
  exact hd s hst (h2 _ h3)

noncomputable def Gam (H : Set (ℕ → Bool)) : TopologicalSpace ℝ :=
  gamTop dlt2 ⊓ ⨅ t ∈ H, gamJ (Jt' t)

lemma Gam_le (H : Set (ℕ → Bool)) : Gam H ≤ gamTop dlt2 := inf_le_left

lemma Gam_nhds (H : Set (ℕ → Bool)) :
    @nhds ℝ (Gam H) 0 = @nhds ℝ (gamTop dlt2) 0 ⊓ ⨅ t ∈ H, @nhds ℝ (gamJ (Jt' t)) 0 := by
  refine (@nhds_inf ℝ (gamTop dlt2) (⨅ t ∈ H, gamJ (Jt' t)) 0).trans
    (congrArg (fun F => @nhds ℝ (gamTop dlt2) 0 ⊓ F) ?_)
  rw [nhds_iInf]
  exact iInf_congr fun t => nhds_iInf

/-- A topology between one serving topology and the finest one serves. -/
lemma serves_between (g g1 g2 : TopologicalSpace ℝ) (A : Set ℝ) (h1 : Serves g1 A) (h2 : Serves g2 A)
    (hg : @IsTopologicalAddGroup ℝ g _) (hlow : g1 ≤ g) (hup : g ≤ g2) : Serves g A := by
  refine ⟨hg, hup.trans h2.2.1, ?_, h1.2.2.2.1.trans (nhds_mono hlow), fun a ha W hW =>
    h1.2.2.2.2 a ha W (nhds_mono hlow hW)⟩
  intro h
  refine h2.2.2.1 (le_antisymm h2.2.1 ?_)
  rw [← h]
  exact hup

attribute [local irreducible] gamTop gamJ Jt' dlt2 Lv in
lemma Gam_group (H : Set (ℕ → Bool)) : @IsTopologicalAddGroup ℝ (Gam H) _ := by
  have h2 : @IsTopologicalAddGroup ℝ (⨅ t ∈ H, gamJ (Jt' t)) _ := by
    refine isTopologicalAddGroup_iInf fun t => ?_
    refine isTopologicalAddGroup_iInf fun _ => ?_
    exact gamJ_group (Jt' t)
  unfold Gam
  exact isTopologicalAddGroup_inf (gam_group dlt2) h2

lemma Gam_serves (H : Set (ℕ → Bool)) : Serves (Gam H) A2 := by
  have key : ∀ γ : TopologicalSpace ℝ, Serves γ A2 → (∀ γ' : TopologicalSpace ℝ, Serves γ' A2 → γ ≤ γ') →
      γ ≤ Gam H := fun γ _ hfin =>
    le_inf (hfin _ serves_dlt2) (le_iInf₂ fun t _ => hfin _ (gamJ_serves (Jt' t)))
  obtain ⟨γ, hγ, hfin⟩ := exists_finest A2 ⟨_, serves_dlt2⟩
  exact serves_between (Gam H) γ (gamTop dlt2) A2 hγ serves_dlt2 (Gam_group H) (key γ hγ hfin) (Gam_le H)

lemma Phit_thJ (J : Set ℕ) (x : ℝ) (i0 : ℕ) (heven : ∀ k, k ≠ i0 → Even (round (x / 2 ^ Lv k)))
    (hodd : Odd (round (x / 2 ^ Lv i0))) :
    open Classical in Phit dlt2 (thJ J) x = if i0 ∈ J then ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else 0 := by
  classical
  have hr : ∀ k, round (dlt2 k * x) = round (x / 2 ^ Lv k) := fun k => by
    rw [show dlt2 k * x = x / 2 ^ Lv k by unfold dlt2; rw [inv_mul_eq_div]]
  unfold Phit
  rw [finsum_eq_single _ i0]
  · rw [hr]
    unfold thJ
    split_ifs
    · exact half_smul_odd _ hodd
    · rw [smul_zero]
  · intro k hk
    rw [hr]
    unfold thJ
    split_ifs
    · exact half_smul_even _ (heven k hk)
    · rw [smul_zero]

lemma Gam_not_le {H H' : Set (ℕ → Bool)} {t : ℕ → Bool} (ht : t ∈ H) (ht' : t ∉ H') : ¬ Gam H' ≤ Gam H := by
  classical
  intro hle
  set U := Nset dlt2 (thJ (Jt' t)) (1 / 5) (1 / 4) with hU
  have hUH : U ∈ @nhds ℝ (Gam H) 0 := by
    have h1 : Gam H ≤ gamJ (Jt' t) := inf_le_right.trans (iInf₂_le t ht)
    refine nhds_mono h1 ?_
    rw [gamJ_nhds]
    exact mem_inf_of_left ((tauJ_spec _).2.mem_of_mem (i := (1 / 5, 1 / 4)) ⟨by norm_num, le_rfl, by norm_num⟩)
  have hUH' : U ∈ @nhds ℝ (Gam H') 0 := nhds_mono hle hUH
  -- a filter below the neighbourhoods of `0` for `Gam H'` that misses `U`
  set Z : Finset (ℕ → Bool) → Set ℝ := fun F =>
    {x | Phit dlt2 (thJ (Jt' t)) x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ∧ ∀ s ∈ F, ↑s ∈ H' →
      Phit dlt2 (thJ (Jt' s)) x = 0} with hZ
  set Fl : Filter ℝ := @nhds ℝ (gamTop dlt2) 0 ⊓ ⨅ F : Finset (ℕ → Bool), 𝓟 (Z F) with hFl
  have hZanti : ∀ F G : Finset (ℕ → Bool), F ⊆ G → Z G ⊆ Z F := fun F G hFG x hx =>
    ⟨hx.1, fun s hs hsH => hx.2 s (hFG hs) hsH⟩
  have hbasis : (⨅ F : Finset (ℕ → Bool), 𝓟 (Z F)).HasBasis (fun _ => True) Z := by
    refine hasBasis_iInf_principal ?_
    intro F G
    exact ⟨F ∪ G, hZanti F _ Finset.subset_union_left, hZanti G _ Finset.subset_union_right⟩
  have hne : Fl.NeBot := by
    refine inf_neBot_iff.2 fun {W} hW {Y} hY => ?_
    obtain ⟨F, -, hFY⟩ := hbasis.mem_iff.1 hY
    set F' := F.filter fun s => s ∈ H' with hF'
    have htF : t ∉ F' := fun h => ht' (Finset.mem_filter.1 h).2
    obtain ⟨N0, hN0⟩ := code_avoid t F' htF
    obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam dlt2 W).1 hW
    obtain ⟨Fb, η', hη', hFb⟩ := exists_bset_subset hB
    obtain ⟨x, hxF, hxd, i0, ⟨j, hj⟩, heven, hodd⟩ := odd_points_gen Lv Lv_gaps (fun n => code t (N0 + n))
      (fun a b hab => code_strict t (by omega)) Fb hη hη'
    have hxW : x ∈ W := hBW x (hFb hxF) fun k => by
      rw [show dlt2 k * x = x / 2 ^ Lv k by unfold dlt2; rw [inv_mul_eq_div]]
      exact hxd k
    refine ⟨x, hxW, hFY ⟨?_, fun s hs hsH => ?_⟩⟩
    · have hmem : i0 ∈ Jt' t := ⟨N0 + j, hj⟩
      rw [Phit_thJ _ x i0 heven hodd, if_pos hmem]
    · have hmem : i0 ∉ Jt' s := by
        rw [← hj]
        exact hN0 (N0 + j) (Nat.le_add_right _ _) s (Finset.mem_filter.2 ⟨hs, hsH⟩)
      rw [Phit_thJ _ x i0 heven hodd, if_neg hmem]
  have hFle : Fl ≤ @nhds ℝ (Gam H') 0 := by
    rw [Gam_nhds]
    refine le_inf inf_le_left (le_iInf₂ fun s hs => ?_)
    rw [gamJ_nhds]
    refine le_inf ?_ (inf_le_left.trans (nhds_mono (gam_le_bohr _)))
    intro V hV
    obtain ⟨⟨ε, η⟩, ⟨hε, hε5, hη⟩, hsub⟩ := (tauJ_spec _).2.mem_iff.1 hV
    simp only at hε hε5 hη hsub
    have h1 : {x : ℝ | ∀ k, dint (dlt2 k * x) ≤ ε} ∈ @nhds ℝ (gamTop dlt2) 0 :=
      (mem_nhds_gam dlt2 _).2 ⟨univ, univ_mem, ε, hε, fun x _ hx => hx⟩
    have h2 : Z {s} ∈ ⨅ F : Finset (ℕ → Bool), 𝓟 (Z F) := mem_iInf_of_mem {s} (mem_principal_self _)
    refine Filter.mem_of_superset (Filter.inter_mem_inf h1 h2) fun x hx => hsub ⟨hx.1, ?_⟩
    show ‖Phit dlt2 (thJ (Jt' s)) x‖ ≤ η
    rw [hx.2.2 s (Finset.mem_singleton_self s) hs, norm_zero]
    exact hη.le
  have hUF : U ∈ Fl := hFle hUH'
  have hZF : Z ∅ ∈ Fl := mem_inf_of_right (mem_iInf_of_mem ∅ (mem_principal_self _))
  obtain ⟨x, hxU, hxZ⟩ := hne.nonempty_of_mem (Filter.inter_mem hUF hZF)
  have h1 : ‖Phit dlt2 (thJ (Jt' t)) x‖ ≤ 1 / 4 := hxU.2
  rw [hxZ.1] at h1
  have h2 : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = 1 / 2 := dint_half
  rw [h2] at h1
  norm_num at h1

/-- The serving topologies `Gam H` are ordered as the sets `H`. -/
theorem many_embed (H H' : Set (ℕ → Bool)) : H ⊆ H' ↔ Gam H' ≤ Gam H := by
  constructor
  · intro h
    exact inf_le_inf_left _ (le_iInf₂ fun t ht => iInf₂_le t (h ht))
  · intro h t ht
    by_contra ht'
    exact Gam_not_le ht ht' h

/-- The usual topology, named so that it can be used next to a variable one. -/
abbrev usualTop : TopologicalSpace ℝ := inferInstance

lemma usualTop_group : @IsTopologicalAddGroup ℝ usualTop _ := inferInstance

lemma card_opens : #{s : Set ℝ // IsOpen s} ≤ 𝔠 := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis ℝ
  have h : Function.Injective (fun s : {s : Set ℝ // IsOpen s} => ({u : b | (u : Set ℝ) ⊆ s.1} : Set b)) := by
    intro s t hst
    refine Subtype.ext ?_
    have key : ∀ s t : {s : Set ℝ // IsOpen s}, ({u : b | (u : Set ℝ) ⊆ s.1} : Set b) = {u : b | (u : Set ℝ) ⊆ t.1} →
        s.1 ⊆ t.1 := by
      intro s t hst x hx
      obtain ⟨u, hu, hxu, hus⟩ := hb.exists_subset_of_mem_open hx s.2
      have h1 : (⟨u, hu⟩ : b) ∈ ({u : b | (u : Set ℝ) ⊆ t.1} : Set b) := hst ▸ hus
      exact h1 hxu
    exact Set.Subset.antisymm (key s t hst) (key t s hst.symm)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [Cardinal.mk_set, ← Cardinal.two_power_aleph0]
  exact Cardinal.power_le_power_left two_ne_zero (Cardinal.le_aleph0_iff_set_countable.2 hbc)

/-- **There are exactly `2 ^ continuum` serving topologies finer than `γ_δ`.** -/
theorem many_card : #{γ : TopologicalSpace ℝ // Serves γ A2 ∧ γ ≤ gamTop dlt2} = 2 ^ 𝔠 := by
  refine le_antisymm ?_ ?_
  · have husual : ∀ γ : TopologicalSpace ℝ, Serves γ A2 → ∀ s : Set ℝ, IsOpen[γ] s → IsOpen[usualTop] s := by
      intro γ hs
      have h1 : usualTop ≤ γ := le_of_nhds_zero _ _ usualTop_group hs.1 hs.2.2.2.1
      exact fun s hs => h1 s hs
    let f : {γ : TopologicalSpace ℝ // Serves γ A2 ∧ γ ≤ gamTop dlt2} → Set {s : Set ℝ // IsOpen s} :=
      fun γ => {s | IsOpen[γ.1] s.1}
    have hf : Function.Injective f := by
      intro γ1 γ2 h
      refine Subtype.ext (TopologicalSpace.ext (funext fun s => propext ⟨fun hs => ?_, fun hs => ?_⟩))
      · have hu := husual γ1.1 γ1.2.1 s hs
        have : (⟨s, hu⟩ : {s : Set ℝ // IsOpen s}) ∈ f γ1 := hs
        rw [h] at this
        exact this
      · have hu := husual γ2.1 γ2.2.1 s hs
        have : (⟨s, hu⟩ : {s : Set ℝ // IsOpen s}) ∈ f γ2 := hs
        rw [← h] at this
        exact this
    refine (Cardinal.mk_le_of_injective hf).trans ?_
    rw [Cardinal.mk_set]
    exact Cardinal.power_le_power_left two_ne_zero card_opens
  · have hinj : Function.Injective (fun H : Set (ℕ → Bool) =>
        (⟨Gam H, Gam_serves H, Gam_le H⟩ : {γ : TopologicalSpace ℝ // Serves γ A2 ∧ γ ≤ gamTop dlt2})) := by
      intro H H' h
      have e : Gam H = Gam H' := congrArg Subtype.val h
      exact Set.Subset.antisymm ((many_embed H H').2 e.symm.le) ((many_embed H' H).2 e.le)
    refine le_trans (le_of_eq ?_) (Cardinal.mk_le_of_injective hinj)
    rw [Cardinal.mk_set]
    have : #(ℕ → Bool) = 𝔠 := by
      rw [Cardinal.mk_arrow]
      simp [Cardinal.two_power_aleph0]
    rw [this]

end Two
end PVG
