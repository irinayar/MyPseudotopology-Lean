import LeanCheck.PVGSorted

/-!
# PVG: Proposition 8.37, finitely and countably many sequences (Lean check)

Scope. Formal counterpart of Proposition 8.37 of `PVG_v18` in the concrete setting of `PVGSequences` (`K = Hom(ℝ, 𝕋)`, `e`,
the limits `L y U`). The proof of the article is formalized in three stages:

* `decomp` (stage A): a sequence `x` in a finite-dimensional real inner product space `V` has a subsequence `x ∘ φ` of the form
  `∑ i, f i • v i + ρ` with unit vectors `v i`, `ρ` convergent, `|f i| → ∞` and `|f i'| / |f i| → 0` for `i < i'` (the orthonormal
  decomposition of the article; the induction is on the dimension of the subspace containing the sequence, the termination
  uses only that the orthogonal part lies in a strictly smaller subspace);
* `exists_retraction_countable`, `exists_retraction_finite`: Corollary 8.39 for finitely and countably many sequences (`countable_family`, `finite_family` with the retraction construction `R4`);
* thinning (stage B): the coefficient sequences can be thinned to a sequence `b` along which the numbers `|f i (b t)|` are
  jointly separated (`JointSep`, so Theorem 8.36 applies);
* stage C: the finite case, stage D: the countable case by the diagonal argument.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

section Decomp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Stage A: the decomposition.** -/
theorem decomp (x : ℕ → V) : ∀ (n : ℕ) (W : Submodule ℝ V), Module.finrank ℝ W = n → (∀ k, x k ∈ W) →
    ∃ (φ : ℕ → ℕ) (r : ℕ) (f : Fin r → ℕ → ℝ) (v : Fin r → V) (ρ : ℕ → V) (ρlim : V),
      StrictMono φ ∧ (∀ k, x (φ k) = ∑ i, f i k • v i + ρ k) ∧ Tendsto ρ atTop (𝓝 ρlim) ∧
      (∀ i, Tendsto (fun k => |f i k|) atTop atTop) ∧
      (∀ i i', i < i' → Tendsto (fun k => |f i' k| / |f i k|) atTop (𝓝 0)) ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ h : 0 < r, ∀ k, |f ⟨0, h⟩ k| ≤ ‖x (φ k)‖) := by
  intro n
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  intro W hW hxW
  by_cases hT : Tendsto (fun k => ‖x k‖) atTop atTop
  · -- unbounded: split off the leading direction
    obtain ⟨N, hN⟩ : ∃ N, ∀ k, N ≤ k → 0 < ‖x k‖ := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hT 1)
      exact ⟨N, fun k hk => lt_of_lt_of_le one_pos (hN k hk)⟩
    have hKc : IsCompact (Metric.sphere (0 : V) 1 ∩ (W : Set V)) :=
      (isCompact_sphere (0 : V) 1).inter_right (Submodule.closed_of_finiteDimensional W)
    have hu : ∀ k, (‖x (N + k)‖)⁻¹ • x (N + k) ∈ Metric.sphere (0 : V) 1 ∩ (W : Set V) := by
      intro k
      have hpos := hN (N + k) (by omega)
      refine ⟨?_, W.smul_mem _ (hxW _)⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    obtain ⟨v, hvK, ψ, hψ, hlim⟩ := hKc.tendsto_subseq (x := fun k => (‖x (N + k)‖)⁻¹ • x (N + k)) hu
    have hv1 : ‖v‖ = 1 := by simpa using hvK.1
    have hvW : v ∈ W := hvK.2
    obtain ⟨φ₁, hφ₁def⟩ : ∃ φ₁ : ℕ → ℕ, ∀ k, φ₁ k = N + ψ k := ⟨fun k => N + ψ k, fun k => rfl⟩
    have hφ₁ : StrictMono φ₁ := fun a b h => by rw [hφ₁def, hφ₁def]; have := hψ h; omega
    obtain ⟨y, hy⟩ : ∃ y : ℕ → V, ∀ k, y k = x (φ₁ k) := ⟨fun k => x (φ₁ k), fun k => rfl⟩
    have hyW : ∀ k, y k ∈ W := fun k => by rw [hy]; exact hxW _
    have hyn : ∀ k, 0 < ‖y k‖ := fun k => by rw [hy, hφ₁def]; exact hN _ (by omega)
    obtain ⟨f1, hf1⟩ : ∃ f1 : ℕ → ℝ, ∀ k, f1 k = inner ℝ (y k) v := ⟨fun k => inner ℝ (y k) v, fun k => rfl⟩
    obtain ⟨ρ1, hρ1⟩ : ∃ ρ1 : ℕ → V, ∀ k, ρ1 k = y k - f1 k • v := ⟨fun k => y k - f1 k • v, fun k => rfl⟩
    have hu' : Tendsto (fun k => (‖y k‖)⁻¹ • y k) atTop (𝓝 v) := by
      refine hlim.congr (fun k => ?_)
      simp only [Function.comp, hy, hφ₁def]
    have hyT : Tendsto (fun k => ‖y k‖) atTop atTop := by
      have : Tendsto φ₁ atTop atTop := hφ₁.tendsto_atTop
      exact (hT.comp this).congr (fun k => by simp only [Function.comp, hy])
    have hratio : Tendsto (fun k => f1 k / ‖y k‖) atTop (𝓝 1) := by
      have h1 := Filter.Tendsto.inner (𝕜 := ℝ) hu' (tendsto_const_nhds (x := v))
      have h2 : inner ℝ v v = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv1]; norm_num
      rw [h2] at h1
      refine h1.congr (fun k => ?_)
      rw [real_inner_smul_left, hf1, div_eq_inv_mul]
    have hsmall : Tendsto (fun k => ‖ρ1 k‖ / ‖y k‖) atTop (𝓝 0) := by
      have h1 := (hu'.sub (hratio.smul_const v)).norm
      have h0 : ‖v - (1 : ℝ) • v‖ = 0 := by simp
      rw [h0] at h1
      refine h1.congr (fun k => ?_)
      have : (‖y k‖)⁻¹ • y k - (f1 k / ‖y k‖) • v = (‖y k‖)⁻¹ • ρ1 k := by
        rw [hρ1, smul_sub, smul_smul, div_eq_inv_mul]
      rw [this, norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
    have hrat1 : Tendsto (fun k => |f1 k| / ‖y k‖) atTop (𝓝 1) := by
      have := hratio.abs
      simp only [abs_one] at this
      refine this.congr (fun k => ?_)
      rw [abs_div, abs_of_pos (hyn k)]
    have hf1T : Tendsto (fun k => |f1 k|) atTop atTop := by
      have hev : ∀ᶠ k in atTop, (1 / 2 : ℝ) < |f1 k| / ‖y k‖ :=
        hrat1.eventually (lt_mem_nhds (by norm_num))
      refine tendsto_atTop_mono' atTop ?_ (hyT.atTop_div_const (by norm_num : (0 : ℝ) < 2))
      filter_upwards [hev] with k hk
      have := hyn k
      rw [lt_div_iff₀ this] at hk
      linarith
    have hq : Tendsto (fun k => ‖ρ1 k‖ / |f1 k|) atTop (𝓝 0) := by
      have h1 := hsmall.mul (hrat1.inv₀ one_ne_zero)
      simp only [inv_one, mul_one, zero_mul] at h1
      refine h1.congr (fun k => ?_)
      have hyk := (hyn k).ne'
      rcases eq_or_ne (|f1 k|) 0 with h0 | h0
      · simp [h0]
      · rw [inv_div]; field_simp
    set W' : Submodule ℝ V := W ⊓ (ℝ ∙ v)ᗮ with hW'
    have hvv : inner ℝ v v = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv1]; norm_num
    have hρW : ∀ k, ρ1 k ∈ W' := by
      intro k
      refine ⟨?_, ?_⟩
      · rw [hρ1]; exact W.sub_mem (hyW k) (W.smul_mem _ hvW)
      · show ρ1 k ∈ (ℝ ∙ v)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hρ1, inner_sub_left, real_inner_smul_left, hf1, hvv]
        ring
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left (fun h => ?_)
      have hv' : v ∈ W' := by rw [h]; exact hvW
      have := Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv'.2
      rw [hvv] at this
      norm_num at this
    have hfr' : Module.finrank ℝ W' < n := hW ▸ Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨φ₂, r', f', v', ρ', ρlim', hφ₂, hdec, hρ', hfT, hfr, hv', hbound⟩ := ih _ hfr' ρ1 W' rfl hρW
    have hbd : ∀ j : Fin r', ∀ᶠ k in atTop, |f' j k| ≤ ‖ρ1 (φ₂ k)‖ := by
      intro j
      have h0 : 0 < r' := Fin.pos j
      by_cases hj : j = ⟨0, h0⟩
      · subst hj; exact Filter.Eventually.of_forall (hbound h0)
      · have hlt0 : (⟨0, h0⟩ : Fin r') < j := by
          rw [Fin.lt_def]
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          show 0 < j.val
          omega
        have e1 := (hfr ⟨0, h0⟩ j hlt0).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
        have e2 := (hfT ⟨0, h0⟩).eventually_gt_atTop 0
        filter_upwards [e1, e2] with k h1 h2
        rw [div_lt_one h2] at h1
        exact h1.le.trans (hbound h0 k)
    refine ⟨φ₁ ∘ φ₂, r' + 1, (Fin.cons (fun k => f1 (φ₂ k)) f' : Fin (r' + 1) → ℕ → ℝ),
      (Fin.cons v v' : Fin (r' + 1) → V), ρ', ρlim', hφ₁.comp hφ₂, ?_, hρ', ?_, ?_, ?_, ?_⟩
    · intro k
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have h1 := hdec k
      rw [hρ1, hy] at h1
      rw [add_assoc, ← h1]
      simp only [Function.comp]
      abel
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · show Tendsto (fun k => |f1 (φ₂ k)|) atTop atTop
        exact hf1T.comp hφ₂.tendsto_atTop
      · simpa using hfT j
    · intro i i'
      refine Fin.cases ?_ (fun j => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) i'
      · intro h; exact absurd h (lt_irrefl _)
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        refine squeeze_zero' (Filter.Eventually.of_forall (fun k => by positivity)) ?_
          (hq.comp hφ₂.tendsto_atTop)
        filter_upwards [hbd j'] with k hk
        exact div_le_div_of_nonneg_right hk (abs_nonneg _)
      · intro h; exact absurd h (Fin.not_lt_zero _)
      · intro h
        simp only [Fin.cons_succ]
        exact hfr j j' (Fin.succ_lt_succ_iff.1 h)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hv1
      · simpa using hv' j
    · intro h k
      have e0 : (⟨0, h⟩ : Fin (r' + 1)) = 0 := rfl
      rw [e0]
      simp only [Fin.cons_zero]
      rw [hf1]
      calc |inner ℝ (y (φ₂ k)) v| ≤ ‖y (φ₂ k)‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖x ((φ₁ ∘ φ₂) k)‖ := by rw [hv1, mul_one, hy]; rfl
  · -- a bounded subsequence
    obtain ⟨b, hb⟩ : ∃ b : ℝ, ∃ᶠ k in atTop, ‖x k‖ < b := by
      by_contra hcon
      push Not at hcon
      apply hT
      rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hcon b)
      exact ⟨N, fun a ha => hN a ha⟩
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop hb
    obtain ⟨a, _, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : V) b).tendsto_subseq
      (x := fun k => x (φ k)) (fun k => by simpa using (hφb k).le)
    refine ⟨φ ∘ ψ, 0, fun i => i.elim0, fun i => i.elim0, fun k => x (φ (ψ k)), a, hφ.comp hψ, ?_, hlim, ?_, ?_, ?_, ?_⟩
    · intro k; simp
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro h; omega

end Decomp

/-! ### Stage B: thinning to jointly separated coefficients -/

/-- **A finite family is `JointSep` if each sequence is eventually sparse and distinct sequences are eventually separated.** -/
lemma jointSep_fin {m : ℕ} (y : Fin m → ℕ → ℝ) (hy0 : ∀ i t, y i t ≠ 0)
    (hs : ∀ R : ℝ, ∃ N, ∀ i, ∀ s, N ≤ s → ∀ t, s < t → R * |y i s| ≤ |y i t|)
    (hc : ∀ R : ℝ, ∃ N, ∀ i i', i ≠ i' → ∀ s, N ≤ s → ∀ t, N ≤ t → R * |y i s| ≤ |y i' t| ∨ R * |y i' t| ≤ |y i s|) :
    JointSep y := by
  refine ⟨hy0, fun T => ?_, fun R => ?_⟩
  · have hfin : ∀ i : Fin m, {t | |y i t| ≤ T}.Finite := fun i =>
      sublevel_finite (y i) (hy0 i) (fun R => by
        obtain ⟨N, hN⟩ := hs R
        exact ⟨N, fun s hs' t hst => hN i s hs' t hst⟩) T
    refine (Set.finite_iUnion (fun i : Fin m => (hfin i).image (fun s => (i, s)))).subset ?_
    rintro ⟨i, s⟩ hp
    exact Set.mem_iUnion.2 ⟨i, s, hp, rfl⟩
  · obtain ⟨N1, hN1⟩ := hs R
    obtain ⟨N2, hN2⟩ := hc R
    refine ⟨{p : Fin m × ℕ | p.2 < max N1 N2}, ?_, ?_⟩
    · exact (Set.finite_univ.prod (Set.finite_Iio (max N1 N2))).subset (fun p hp => ⟨Set.mem_univ _, hp⟩)
    · rintro ⟨i, s⟩ hp ⟨i', t⟩ hq hne
      have hs' : max N1 N2 ≤ s := by simpa using hp
      have ht' : max N1 N2 ≤ t := by simpa using hq
      by_cases hii : i = i'
      · subst hii
        have hst : s ≠ t := fun h => hne (by rw [h])
        rcases lt_or_gt_of_ne hst with h | h
        · left; exact hN1 i s (le_trans (le_max_left _ _) hs') t h
        · right; exact hN1 i t (le_trans (le_max_left _ _) ht') s h
      · exact hN2 i i' hii s (le_trans (le_max_right _ _) hs') t (le_trans (le_max_right _ _) ht')

/-- **Thinning.** If `|f i| → ∞` and `|f i'| / |f i| → 0` for `i < i'`, then along a suitable subsequence `b` all the numbers
`|f i (b t)|` are jointly separated (the hypothesis of Theorem 8.36). -/
theorem thin_joint {r : ℕ} (f : Fin r → ℕ → ℝ) (hT : ∀ i, Tendsto (fun k => |f i k|) atTop atTop)
    (hr : ∀ i i', i < i' → Tendsto (fun k => |f i' k| / |f i k|) atTop (𝓝 0)) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ JointSep (fun i => fun t => f i (b t)) := by
  classical
  have hstep : ∀ (t : ℕ) (k0 : ℕ), ∃ k, k0 < k ∧ (∀ i, f i k ≠ 0) ∧
      (∀ i i', i < i' → ((t : ℝ) + 1) * |f i' k| ≤ |f i k|) ∧
      (∀ i, ((t : ℝ) + 1) * (∑ i', |f i' k0|) ≤ |f i k|) := by
    intro t k0
    have hev : ∀ᶠ k in atTop, k0 < k ∧ (∀ i, f i k ≠ 0) ∧
        (∀ i i', i < i' → ((t : ℝ) + 1) * |f i' k| ≤ |f i k|) ∧
        (∀ i, ((t : ℝ) + 1) * (∑ i', |f i' k0|) ≤ |f i k|) := by
      refine (Filter.eventually_gt_atTop k0).and ((Filter.eventually_all.2 fun i => ?_).and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => ?_).and
          (Filter.eventually_all.2 fun i => ?_)))
      · filter_upwards [(hT i).eventually_gt_atTop 0] with k hk
        exact fun h => by rw [h] at hk; simp at hk
      · by_cases hii : i < i'
        · have e1 := (hr i i' hii).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((t : ℝ) + 1)))
          filter_upwards [e1, (hT i).eventually_gt_atTop 0] with k h1 h2 _
          rw [div_lt_iff₀ h2] at h1
          have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
          have := mul_lt_mul_of_pos_left h1 ht
          have e : ((t : ℝ) + 1) * (1 / ((t : ℝ) + 1) * |f i k|) = |f i k| := by field_simp
          rw [e] at this
          linarith
        · exact Filter.Eventually.of_forall (fun k h => absurd h hii)
      · exact (hT i).eventually_ge_atTop _
    obtain ⟨k, hk⟩ := hev.exists
    exact ⟨k, hk⟩
  choose g hg using hstep
  obtain ⟨kk, hkk0, hkkS⟩ : ∃ kk : ℕ → ℕ, kk 0 = g 0 0 ∧ ∀ t, kk (t + 1) = g (t + 1) (kk t) :=
    ⟨fun t => Nat.rec (g 0 0) (fun t kt => g (t + 1) kt) t, rfl, fun t => rfl⟩
  have hmono : ∀ t, kk t < kk (t + 1) := fun t => by rw [hkkS]; exact (hg (t + 1) (kk t)).1
  have hkS : StrictMono kk := strictMono_nat_of_lt_succ hmono
  have hne0 : ∀ i t, f i (kk t) ≠ 0 := by
    intro i t
    cases t with
    | zero => rw [hkk0]; exact (hg 0 0).2.1 i
    | succ t => rw [hkkS]; exact (hg (t + 1) (kk t)).2.1 i
  have hblock : ∀ (t : ℕ) (i i' : Fin r), i < i' → ((t : ℝ) + 1) * |f i' (kk t)| ≤ |f i (kk t)| := by
    intro t i i' h
    cases t with
    | zero => rw [hkk0]; simpa using (hg 0 0).2.2.1 i i' h
    | succ t => rw [hkkS]; have := (hg (t + 1) (kk t)).2.2.1 i i' h; push_cast at this ⊢; linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℝ, ∀ t, M t = ∑ i', |f i' (kk t)| := ⟨fun t => ∑ i', |f i' (kk t)|, fun t => rfl⟩
  have hMnn : ∀ t, 0 ≤ M t := fun t => by rw [hM]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hle_M : ∀ t i, |f i (kk t)| ≤ M t := fun t i => by
    rw [hM]
    exact Finset.single_le_sum (f := fun i' => |f i' (kk t)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hgrow : ∀ (t : ℕ) (i : Fin r), ((t : ℝ) + 2) * M t ≤ |f i (kk (t + 1))| := by
    intro t i
    rw [hkkS, hM]
    have := (hg (t + 1) (kk t)).2.2.2 i
    push_cast at this
    have e : ((t : ℝ) + 1 + 1) = (t : ℝ) + 2 := by ring
    rw [e] at this
    exact this
  have hMsucc : ∀ t, M t ≤ M (t + 1) := by
    intro t
    rcases isEmpty_or_nonempty (Fin r) with he | hn
    · rw [hM, hM]; simp
    · obtain ⟨i0⟩ := hn
      have h1 := hgrow t i0
      have h2 := hle_M (t + 1) i0
      have h3 : M t ≤ ((t : ℝ) + 2) * M t := by nlinarith [hMnn t, (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      linarith
  have hMmono : ∀ (s t : ℕ), s ≤ t → M s ≤ M t := fun s t hst => by
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih => exact le_trans ih (hMsucc t)
  have hcross : ∀ (s t : ℕ), s < t → ∀ i i' : Fin r, ((t : ℝ) + 1) * |f i (kk s)| ≤ |f i' (kk t)| := by
    intro s t hst i i'
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    have h1 := hgrow u i'
    have h2 : M s ≤ M u := hMmono s u (by omega)
    have h3 := mul_le_mul_of_nonneg_left ((hle_M s i).trans h2) (by positivity : (0 : ℝ) ≤ (u : ℝ) + 2)
    push_cast
    linarith
  have hmonoY : ∀ i, Monotone (fun t => |f i (kk t)|) := fun i =>
    monotone_nat_of_le_succ (fun t => by
      have h1 := hgrow t i
      have h2 := hle_M t i
      have h3 : M t ≤ ((t : ℝ) + 2) * M t := by nlinarith [hMnn t, (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      linarith)
  refine ⟨kk, hkS, jointSep_fin (fun i t => f i (kk t)) hne0 ?_ ?_⟩
  · intro R
    refine ⟨⌈R⌉₊, fun i s hs t hst => ?_⟩
    have hRs : R ≤ (s : ℝ) := le_trans (Nat.le_ceil R) (by exact_mod_cast hs)
    have h1 := hgrow s i
    have h2 := hle_M s i
    have h4 : |f i (kk (s + 1))| ≤ |f i (kk t)| := hmonoY i hst
    have h5 : R * |f i (kk s)| ≤ ((s : ℝ) + 2) * M s := by
      have := mul_le_mul_of_nonneg_left h2 (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)] : (0 : ℝ) ≤ (s : ℝ) + 2)
      have h6 : R * |f i (kk s)| ≤ ((s : ℝ) + 2) * |f i (kk s)| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      linarith
    linarith
  · intro R
    refine ⟨⌈R⌉₊, fun i i' hii s hs t ht => ?_⟩
    have hRs : R ≤ (s : ℝ) + 1 := by
      have := le_trans (Nat.le_ceil R) (by exact_mod_cast hs : (⌈R⌉₊ : ℝ) ≤ s); linarith
    have hRt : R ≤ (t : ℝ) + 1 := by
      have := le_trans (Nat.le_ceil R) (by exact_mod_cast ht : (⌈R⌉₊ : ℝ) ≤ t); linarith
    rcases lt_trichotomy s t with h | h | h
    · left
      have := hcross s t h i i'
      have h7 := mul_le_mul_of_nonneg_right hRt (abs_nonneg (f i (kk s)))
      linarith
    · subst h
      rcases lt_or_gt_of_ne hii with h' | h'
      · right
        have := hblock s i i' h'
        have h7 := mul_le_mul_of_nonneg_right hRs (abs_nonneg (f i' (kk s)))
        linarith
      · left
        have := hblock s i' i h'
        have h7 := mul_le_mul_of_nonneg_right hRs (abs_nonneg (f i (kk s)))
        linarith
    · right
      have := hcross t s h i' i
      have h7 := mul_le_mul_of_nonneg_right hRs (abs_nonneg (f i' (kk t)))
      linarith

/-! ### Stage C: finitely many sequences -/

/-- **Proposition 8.37, finite case.** For finitely many real sequences and an infinite `C` there is an infinite `B ⊆ C` such
that the real span of all the differences `L (y j) U - L (y j) V`, `U, V` free containing `B`, meets `ℝ e(1)` only in `0`. -/
theorem finite_family {m : ℕ} (y : Fin m → ℕ → ℝ) (C : Set ℕ) (hC : C.Infinite) :
    ∃ B : Set ℕ, B ⊆ C ∧ B.Infinite ∧ Disjoint (Submodule.span ℝ (⋃ j, Gen (y j) B)) (ℝ ∙ e 1) := by
  classical
  have hCinf : (setOf (· ∈ C)).Infinite := hC
  obtain ⟨c, hcS, hcC⟩ : ∃ c : ℕ → ℕ, StrictMono c ∧ ∀ k, c k ∈ C :=
    ⟨Nat.nth (· ∈ C), Nat.nth_strictMono hCinf, Nat.nth_mem_of_infinite hCinf⟩
  let x : ℕ → EuclideanSpace ℝ (Fin m) := fun k => (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => y j (c k))
  obtain ⟨φ, r, f, v, ρ, ρlim, hφ, hdec, hρ, hfT, hfr, hv, hbound⟩ :=
    decomp x _ ⊤ rfl (fun k => Submodule.mem_top)
  obtain ⟨b, hb, hjs⟩ := thin_joint f hfT hfr
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℕ, ∀ t, Φ t = c (φ (b t)) := ⟨fun t => c (φ (b t)), fun t => rfl⟩
  have hΦS : StrictMono Φ := fun a a' h => by rw [hΦ, hΦ]; exact hcS (hφ (hb h))
  have hdis : Disjoint (Submodule.span ℝ {w : K | ∃ (i : Fin r) (U : Ultrafilter ℕ), Free U ∧
      w = L (fun t => f i (b t)) U}) (ℝ ∙ e 1) :=
    disjoint_span_L_family (fun i t => f i (b t)) (fun m' i hi => jointSep_comp hjs i hi)
  refine ⟨Set.range Φ, ?_, Set.infinite_range_of_injective hΦS.injective, hdis.mono_left ?_⟩
  · rintro _ ⟨t, rfl⟩; rw [hΦ]; exact hcC _
  apply Submodule.span_le.2
  intro w hw
  obtain ⟨j, hwj⟩ := Set.mem_iUnion.1 hw
  obtain ⟨U, V', hU, hV, hBU, hBV, rfl⟩ := hwj
  obtain ⟨WU, hWU, rfl⟩ := exists_pre_ultra hΦS.injective hU hBU
  obtain ⟨WV, hWV, rfl⟩ := exists_pre_ultra hΦS.injective hV hBV
  have hcoord : ∀ t, y j (Φ t) = ∑ i, v i j * f i (b t) + ρ (b t) j := by
    intro t
    have := congrArg (fun w : EuclideanSpace ℝ (Fin m) => w j) (hdec (b t))
    rw [hΦ]
    simpa [x, mul_comm] using this
  have hρj : Tendsto (fun t => ρ (b t) j) atTop (𝓝 (ρlim j)) := by
    have h1 : Tendsto (fun t => ρ (b t)) atTop (𝓝 ρlim) := hρ.comp hb.tendsto_atTop
    exact ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).continuous.tendsto _).comp h1
  have hz : ∀ ε > 0, ∃ N, ∀ k ∈ (Set.univ : Set ℕ), N ≤ k → |ρ (b k) j - ρlim j| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Metric.tendsto_nhds.1 hρj) ε hε)
    exact ⟨N, fun k _ hk => by simpa [Real.dist_eq] using hN k hk⟩
  have hLrep : ∀ W : Ultrafilter ℕ, Free W →
      L (y j) (W.map Φ) = ∑ i, v i j • L (fun t => f i (b t)) W + e (ρlim j) := by
    intro W hW
    rw [← L_comp (y j) Φ W]
    have := L_rep (fun i t => f i (b t)) (m := r) (fun i => i) (fun i => v i j) (fun _ => id)
      (fun _ n => by simp [Set.preimage]) (fun t => ρ (b t) j) (ρlim j) Set.univ hz (fun t => y j (Φ t))
      (fun t => by simpa using hcoord t) hW (Filter.univ_mem)
    simpa using this
  rw [hLrep WU hWU, hLrep WV hWV]
  have h2 : ∑ i, v i j • L (fun t => f i (b t)) WU + e (ρlim j) -
      (∑ i, v i j • L (fun t => f i (b t)) WV + e (ρlim j)) =
      ∑ i, v i j • (L (fun t => f i (b t)) WU - L (fun t => f i (b t)) WV) := by
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
  rw [h2]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact Submodule.subset_span ⟨i, WU, hWU, rfl⟩
  · exact Submodule.subset_span ⟨i, WV, hWV, rfl⟩

/-! ### Stage D: countably many sequences -/

/-- **Proposition 8.37.** For a countable family `y : ℕ → ℕ → ℝ` of real sequences and an infinite `C` there is an infinite
`B ⊆ C` such that the real span of all the differences `L (y n) U - L (y n) V`, `U, V` free containing `B`, meets `ℝ e(1)` only
in `0`. (A finite family is `finite_family`.) -/
theorem countable_family (y : ℕ → ℕ → ℝ) (C : Set ℕ) (hC : C.Infinite) :
    ∃ B : Set ℕ, B ⊆ C ∧ B.Infinite ∧ Disjoint (Submodule.span ℝ (⋃ n, Gen (y n) B)) (ℝ ∙ e 1) := by
  classical
  have hstep : ∀ (n : ℕ) (D : {s : Set ℕ // s.Infinite}), ∃ D' : {s : Set ℕ // s.Infinite}, D'.1 ⊆ D.1 ∧
      Disjoint (Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) D'.1)) (ℝ ∙ e 1) := by
    intro n D
    obtain ⟨B', hB'D, hB'inf, hB'dis⟩ := finite_family (fun j : Fin (n + 1) => y j) D.1 D.2
    exact ⟨⟨B', hB'inf⟩, hB'D, hB'dis⟩
  choose nxt hnxt using hstep
  obtain ⟨Bs, hBs0, hBsS⟩ : ∃ Bs : ℕ → {s : Set ℕ // s.Infinite}, Bs 0 = ⟨C, hC⟩ ∧ ∀ n, Bs (n + 1) = nxt n (Bs n) :=
    ⟨fun n => Nat.rec ⟨C, hC⟩ (fun n D => nxt n D) n, rfl, fun n => rfl⟩
  have hanti : ∀ n, (Bs (n + 1)).1 ⊆ (Bs n).1 := fun n => by rw [hBsS]; exact (hnxt n (Bs n)).1
  have hdisS : ∀ n, Disjoint (Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) (Bs (n + 1)).1)) (ℝ ∙ e 1) :=
    fun n => by rw [hBsS]; exact (hnxt n (Bs n)).2
  have hsub : ∀ n k, n ≤ k → (Bs k).1 ⊆ (Bs n).1 := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact subset_rfl
    | succ k _ ih => exact (hanti k).trans ih
  -- the diagonal sequence
  have hex : ∀ (n a : ℕ), ∃ k ∈ (Bs (n + 1)).1, a < k := fun n a => (Bs (n + 1)).2.exists_gt a
  choose pick hpickB hpickgt using hex
  obtain ⟨b, hb0, hbS⟩ : ∃ b : ℕ → ℕ, b 0 ∈ (Bs 0).1 ∧ ∀ n, b (n + 1) = pick n (b n) :=
    ⟨fun n => Nat.rec (Classical.choose (Bs 0).2.nonempty) (fun n bn => pick n bn) n,
      Classical.choose_spec (Bs 0).2.nonempty, fun n => rfl⟩
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ (fun n => by rw [hbS]; exact hpickgt n (b n))
  have hbB : ∀ n, b n ∈ (Bs n).1 := by
    intro n
    cases n with
    | zero => exact hb0
    | succ n => rw [hbS]; exact hpickB n (b n)
  have hbC : ∀ n, b n ∈ C := fun n => by
    have := hsub 0 n (Nat.zero_le n) (hbB n)
    rwa [hBs0] at this
  -- B is almost contained in every B_n
  have hmem : ∀ n, ∀ U : Ultrafilter ℕ, Free U → Set.range b ∈ U → (Bs n).1 ∈ U := by
    intro n U hU hBU
    have hfin : (b '' Set.Iio n).Finite := (Set.finite_Iio n).image b
    have hcof : (b '' Set.Iio n)ᶜ ∈ U := hU (Filter.mem_cofinite.mpr (by rw [compl_compl]; exact hfin))
    refine Filter.mem_of_superset (Filter.inter_mem hBU hcof) ?_
    rintro _ ⟨⟨m, rfl⟩, hm⟩
    have hnm : n ≤ m := by
      by_contra h
      exact hm ⟨m, by simpa using (not_le.mp h), rfl⟩
    exact hsub n m hnm (hbB m)
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact hbC n
  -- the span
  have hSn : ∀ n, Disjoint (Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) (Set.range b))) (ℝ ∙ e 1) := by
    intro n
    refine (hdisS n).mono_left (Submodule.span_mono ?_)
    refine Set.iUnion_mono (fun j => ?_)
    rintro w ⟨U, V', hU, hV, hBU, hBV, rfl⟩
    exact ⟨U, V', hU, hV, hmem (n + 1) U hU hBU, hmem (n + 1) V' hV hBV, rfl⟩
  rw [Submodule.disjoint_def]
  intro w hw hw1
  have hdir : Monotone (fun n : ℕ => Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) (Set.range b))) := by
    intro n n' hnn'
    refine Submodule.span_mono ?_
    rintro w ⟨_, ⟨j, rfl⟩, hwj⟩
    exact Set.mem_iUnion.2 ⟨⟨j.1, by omega⟩, hwj⟩
  have hle : Submodule.span ℝ (⋃ n, Gen (y n) (Set.range b)) ≤
      ⨆ n : ℕ, Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) (Set.range b)) := by
    refine Submodule.span_le.2 (Set.iUnion_subset fun n w hw => ?_)
    refine (le_iSup (fun n : ℕ => Submodule.span ℝ (⋃ j : Fin (n + 1), Gen (y j) (Set.range b))) n)
      (Submodule.subset_span ?_)
    exact Set.mem_iUnion.2 ⟨⟨n, Nat.lt_succ_self n⟩, hw⟩
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir.directed_le).1 (hle hw)
  exact (Submodule.disjoint_def.1 (hSn n)) w hn hw1

/-! ### Corollary 8.39 for finitely and countably many sequences -/

/-- **Corollary 8.39 for a countable family of real sequences**: one real linear `π` with `π (e 1) = 1` is good for every member
(the combination of `countable_family` with the retraction construction `R4`). -/
theorem exists_retraction_countable (y : ℕ → ℕ → ℝ) :
    ∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ ∀ n, SC π (y n) := by
  classical
  obtain ⟨B, -, hBinf, hdis⟩ := countable_family y Set.univ Set.infinite_univ
  let Lac : Set (ℕ → ℝ) := Set.range y
  have hR4 := (R4 (e 1) e_one_ne_zero Lac L Free).2 ⟨fun _ => B, ?_, ?_⟩
  · obtain ⟨π, h1, hπ⟩ := hR4
    exact ⟨π, h1, fun n => hπ (y n) ⟨n, rfl⟩⟩
  · intro w _; exact hBinf
  · refine Disjoint.mono_left ?_ hdis
    apply Submodule.span_mono
    rintro v ⟨w, ⟨n, rfl⟩, U, V, hU, hV, hBU, hBV, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, U, V, hU, hV, hBU, hBV, rfl⟩

/-- **Corollary 8.39 for finitely many real sequences.** -/
theorem exists_retraction_finite {m : ℕ} (y : Fin m → ℕ → ℝ) :
    ∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ ∀ j, SC π (y j) := by
  classical
  obtain ⟨B, -, hBinf, hdis⟩ := finite_family y Set.univ Set.infinite_univ
  let Lac : Set (ℕ → ℝ) := Set.range y
  have hR4 := (R4 (e 1) e_one_ne_zero Lac L Free).2 ⟨fun _ => B, ?_, ?_⟩
  · obtain ⟨π, h1, hπ⟩ := hR4
    exact ⟨π, h1, fun j => hπ (y j) ⟨j, rfl⟩⟩
  · intro w _; exact hBinf
  · refine Disjoint.mono_left ?_ hdis
    apply Submodule.span_mono
    rintro v ⟨w, ⟨j, rfl⟩, U, V, hU, hV, hBU, hBV, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, U, V, hU, hV, hBU, hBV, rfl⟩

#print axioms decomp
#print axioms thin_joint
#print axioms finite_family
#print axioms countable_family
#print axioms exists_retraction_countable
#print axioms exists_retraction_finite

end Q95
end PVG
