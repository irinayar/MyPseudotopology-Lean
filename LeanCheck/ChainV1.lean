import LeanCheck.ChainW2

/-!
# Irrational scalar probes for the rational Hamel pair
(TVGQ-v7 Propositions 17.8 `chains:irrational`, 17.9 `chains:probe`; HamelCharactersTVG_v18 Propositions D.8, D.9)

`f : ℝ →+ ℚ` is a nonzero additive function, `ψ_r(x) = p(f(r x))` (`pfHom f r`), and
`H_{f,ℚ} = {x ↦ p(c x + q f(x))}` (`Hq f`).  The rational line `ℚ ⊆ ℝ` is `ratLine`, so that
`β_{f,ℚ}, σ_{f,ℚ}, τ_{f,ℚ}` are `betaT f ratLine`, `sigmaT f ratLine`, `tauT f ratLine`.

* `psiR_not_mem`        : for irrational `r`, `ψ_r ∉ H_{f,ℚ}`;
* `scalar_ring_rat`     : in a topology whose dual is `H_{f,ℚ}`, a real multiplication is continuous iff the
                          multiplier is rational;
* `irrational_witness`  : a sequence `x_n → 0` with `f(x_n) = 0`, `f(r x_n) = 1/2`;
* `irrational_probe_sequences` : it tends to zero in `β, σ, τ` but `(r x_n)` tends to zero in none of them;
* `irrational_join_test` : (17.9) the quarter-arc join test.
-/

namespace LeanCheck

open Filter Topology

section Irrational

/-- The rational line `ℚ ⊆ ℝ` as a `ℚ`-subspace. -/
noncomputable def ratLine : Submodule ℚ ℝ := Submodule.span ℚ {(1 : ℝ)}

lemma mem_ratLine {a : ℝ} : a ∈ ratLine ↔ ∃ q : ℚ, (q : ℝ) = a := by
  unfold ratLine
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa [Rat.smul_def] using hq⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa [Rat.smul_def] using hq⟩

lemma f_natmul (f : ℝ →+ ℚ) (N : ℕ) (z : ℝ) : f ((N : ℝ) * z) = N * f z := by
  have := f_ratmul f (N : ℚ) z
  simpa using this

/-- A function that is `ℕ`-homogeneous and integer valued is zero. -/
lemma zero_of_int_valued (G : ℝ → ℝ) (hG : ∀ (N : ℕ) y, G ((N : ℝ) * y) = N * G y)
    (hint : ∀ x, ∃ n : ℤ, G x = n) : ∀ x, G x = 0 := by
  intro x
  by_contra hne
  obtain ⟨N, hN⟩ := exists_nat_gt (|G x|)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (abs_nonneg _) hN
  obtain ⟨m, hm⟩ := hint (x / N)
  have h1 := hG N (x / N)
  rw [mul_div_cancel₀ _ hNpos.ne', hm] at h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa using h1
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : 1 ≤ |m| := Int.one_le_abs hm0
    exact_mod_cast this
  have h2 : |G x| = N * |(m : ℝ)| := by
    rw [h1, abs_mul, abs_of_pos hNpos]
  nlinarith

/-- **Excluded scalars** (17.8, first sentence).  For irrational `r`, `ψ_r ∉ H_{f,ℚ}`. -/
theorem psiR_not_mem (f : ℝ →+ ℚ) (hf : f ≠ 0) (r : ℝ) (hr : Irrational r) : pfHom f r ∉ Hq f := by
  rintro ⟨c, q, h⟩
  set G : ℝ → ℝ := fun x => ((f (r * x) : ℚ) : ℝ) - c * x - ((f ((q : ℝ) * x) : ℚ) : ℝ) with hG
  have hint : ∀ x, ∃ n : ℤ, G x = n := fun x => by
    have h1 := h x
    rw [pfHom_apply] at h1
    unfold chiH at h1
    have h2 : ((G x : ℝ) : Circ) = 0 := by
      have : G x = ((f (r * x) : ℚ) : ℝ) - (c * x + ((f ((q : ℝ) * x) : ℚ) : ℝ)) := by
        simp only [hG]; ring
      rw [this, AddCircle.coe_sub, h1, sub_self]
    exact (circ_zero_iff _).1 h2
  have hmul : ∀ (N : ℕ) y, G ((N : ℝ) * y) = N * G y := by
    intro N y
    simp only [hG]
    have e1 : r * ((N : ℝ) * y) = (N : ℝ) * (r * y) := by ring
    have e2 : (q : ℝ) * ((N : ℝ) * y) = (N : ℝ) * ((q : ℝ) * y) := by ring
    rw [e1, e2, f_natmul, f_natmul]
    push_cast
    ring
  have hG0 := zero_of_int_valued G hmul hint
  have hrel : ∀ x, ((f (r * x) : ℚ) : ℝ) - ((f ((q : ℝ) * x) : ℚ) : ℝ) = c * x := fun x => by
    have := hG0 x
    simp only [hG] at this
    linarith
  have hc0 : c = 0 := by
    by_contra hc
    apply hr
    refine ⟨f (r * (r / c)) - f ((q : ℝ) * (r / c)), ?_⟩
    push_cast
    rw [hrel (r / c)]
    field_simp
  have hf0 : ∀ y, f y = 0 := by
    intro y
    have hne : r - q ≠ 0 := by
      intro h0
      exact hr ⟨q, by linarith⟩
    have h1 := hrel (y / (r - q))
    rw [hc0, zero_mul] at h1
    have h2 : f (r * (y / (r - q))) = f ((q : ℝ) * (y / (r - q))) := by
      exact_mod_cast sub_eq_zero.1 h1
    have h3 : y = r * (y / (r - q)) - (q : ℝ) * (y / (r - q)) := by
      field_simp
    rw [h3, map_sub, h2, sub_self]
  exact hf (AddMonoidHom.ext hf0)

/-- **Continuous scalar ring** (17.8, second sentence).  In a topology whose characters are exactly `H_{f,ℚ}`,
multiplication by `r` is continuous iff `r` is rational (rational multiplications being continuous by hypothesis). -/
theorem scalar_ring_rat (f : ℝ →+ ℚ) (hf : f ≠ 0) (τ : TopologicalSpace ℝ)
    (hdual : ∀ χ : ℝ →+ Circ, @Continuous ℝ Circ τ circTop χ ↔ χ ∈ Hq f)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (fun x : ℝ => (q : ℝ) * x)) (r : ℝ) :
    Continuous[τ, τ] (fun x : ℝ => r * x) ↔ ∃ q : ℚ, r = q := by
  constructor
  · intro hr
    by_contra hnot
    have hirr : Irrational r := fun ⟨q, hq'⟩ => hnot ⟨q, hq'.symm⟩
    have h1 : @Continuous ℝ Circ τ circTop (pfHom f 1) := (hdual _).2 (by
      have := pfHom_mem f (1 : ℚ)
      simpa using this)
    have h2 : @Continuous ℝ Circ τ circTop (pfHom f r) := by
      have : (pfHom f r : ℝ → Circ) = (pfHom f 1 : ℝ → Circ) ∘ (fun x : ℝ => r * x) := by
        funext x
        simp [pfHom_apply]
      rw [this]
      exact @Continuous.comp ℝ ℝ Circ τ τ circTop _ _ h1 hr
    exact psiR_not_mem f hf r hirr ((hdual _).1 h2)
  · rintro ⟨q, rfl⟩
    exact hq q

/-- `ψ_r(x) = 1/2` never tends to `0`. -/
lemma not_tendsto_of_const {X : Type*} {t : TopologicalSpace X} (ψ : X → Circ)
    (hψ : @Continuous X Circ t circTop ψ) (x0 : X) (hx0 : ψ x0 = 0)
    (z : ℕ → X) (hz : ∀ n, ψ (z n) = ((1 / 2 : ℝ) : Circ)) : ¬ Tendsto z atTop (@nhds X t x0) := by
  intro h
  have hψ' : @Continuous X Circ t _ ψ := hψ
  have h1 : Tendsto (fun n => ψ (z n)) atTop (𝓝 (ψ x0)) :=
    (@Continuous.tendsto X Circ t _ ψ hψ' x0).comp h
  rw [hx0] at h1
  have h2 : Tendsto (fun n => ψ (z n)) atTop (𝓝 ((1 / 2 : ℝ) : Circ)) := by
    simp only [hz]
    exact tendsto_const_nhds
  have h3 := tendsto_nhds_unique h1 h2
  have h4 : (((1 / 2 : ℝ)) : Circ) = 0 := h3.symm
  obtain ⟨n, hn⟩ := (circ_zero_iff _).1 h4
  have : (2 : ℝ) * n = 1 := by linarith
  have h5 : (2 : ℤ) * n = 1 := by exact_mod_cast this
  omega

lemma exists_f_one (f : ℝ →+ ℚ) (hf : f ≠ 0) : ∃ u : ℝ, f u = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (AddMonoidHom.ext h)
  refine ⟨(((f x)⁻¹ : ℚ) : ℝ) * x, ?_⟩
  rw [f_ratmul]
  field_simp

/-- **Sequence witnesses** (17.8, third sentence, first half): for irrational `r` and nonzero `f` there is
`x_n → 0` (usual) with `f(x_n) = 0` and `f(r x_n) = 1/2`. -/
theorem irrational_witness (f : ℝ →+ ℚ) (hf : f ≠ 0) (r : ℝ) (hr : Irrational r) :
    ∃ x : ℕ → ℝ, (∀ n, |x n| < 1 / ((n : ℝ) + 1)) ∧ (∀ n, f (x n) = 0) ∧
      (∀ n, f (r * x n) = 1 / 2) := by
  obtain ⟨u, hu⟩ := exists_f_one f hf
  have hrq : ∀ q : ℚ, r ≠ q := fun q h => hr ⟨q, h.symm⟩
  -- a vector `y0` with `f y0 = 0` and `f (r y0) ≠ 0`
  obtain ⟨y0, hy0, hy0'⟩ : ∃ y, f y = 0 ∧ f (r * y) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    set c : ℚ := f (r * u) with hc
    have h1 : ∀ y, f (r * y) = c * f y := fun y => by
      have hy : f (y - ((f y : ℚ) : ℝ) * u) = 0 := by
        rw [map_sub, f_ratmul, hu]; ring
      have h2 := hcon _ hy
      have e : r * (y - ((f y : ℚ) : ℝ) * u) = r * y - ((f y : ℚ) : ℝ) * (r * u) := by ring
      rw [e, map_sub, f_ratmul] at h2
      rw [hc]
      linarith
    have hf0 : ∀ y, f y = 0 := by
      intro y
      have hne : r - c ≠ 0 := sub_ne_zero.2 (hrq c)
      have e : y = r * (y / (r - c)) - (c : ℝ) * (y / (r - c)) := by field_simp
      rw [e, map_sub, h1, f_ratmul]
      ring
    exact hf (AddMonoidHom.ext hf0)
  set t : ℚ := f (r * y0) with ht
  have ht0 : t ≠ 0 := hy0'
  set y : ℝ := (((1 / (2 * t) : ℚ)) : ℝ) * y0 with hy
  have hy1 : f y = 0 := by rw [hy, f_ratmul, hy0, mul_zero]
  have hy2 : f (r * y) = 1 / 2 := by
    have e : r * y = (((1 / (2 * t) : ℚ)) : ℝ) * (r * y0) := by rw [hy]; ring
    rw [e, f_ratmul]
    field_simp
    rfl
  -- a nonzero element `k` killed by both `f` and `f ∘ (r ·)`
  obtain ⟨k, hk0, hk1, hk2⟩ : ∃ k : ℝ, k ≠ 0 ∧ f k = 0 ∧ f (r * k) = 0 := by
    by_contra hno
    push_neg at hno
    have hinj : Function.Injective (fun x : ℝ => (f x, f (r * x))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      by_contra hne
      have hne' : a - b ≠ 0 := sub_ne_zero.2 hne
      refine hno (a - b) hne' (by rw [map_sub, hab.1, sub_self]) ?_
      rw [mul_sub, map_sub, hab.2, sub_self]
    haveI : Countable ℝ := hinj.countable
    exact Cardinal.not_countable_real Set.countable_univ
  have hq : ∀ n : ℕ, ∃ q : ℚ, |y + (q : ℝ) * k| < 1 / ((n : ℝ) + 1) := fun n => by
    have hk' : 0 < |k| := abs_pos.2 hk0
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set δ : ℝ := 1 / (((n : ℝ) + 1) * |k|) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show -y / k < -y / k + δ by linarith)
    refine ⟨q, ?_⟩
    have e : y + (q : ℝ) * k = k * ((q : ℝ) + y / k) := by field_simp; ring
    have h3 : |(q : ℝ) + y / k| < δ := by
      rw [abs_lt]
      constructor
      · have : -y / k = -(y / k) := by ring
        linarith
      · have : -y / k = -(y / k) := by ring
        linarith
    rw [e, abs_mul]
    calc |k| * |(q : ℝ) + y / k| < |k| * δ := mul_lt_mul_of_pos_left h3 hk'
      _ = 1 / ((n : ℝ) + 1) := by rw [hδ]; field_simp
  choose q hq using hq
  refine ⟨fun n => y + (q n : ℝ) * k, hq, fun n => ?_, fun n => ?_⟩
  · rw [map_add, hy1, f_ratmul, hk1]; ring
  · have e : r * (y + (q n : ℝ) * k) = r * y + (q n : ℝ) * (r * k) := by ring
    rw [e, map_add, hy2, f_ratmul, hk2]; ring

/-- **Sequence witnesses** (17.8, third sentence): the sequence tends to zero in `β_{f,ℚ}`, `σ_{f,ℚ}`, `τ_{f,ℚ}`,
while `(r x_n)` tends to zero in none of them. -/
theorem irrational_probe_sequences (f : ℝ →+ ℚ) (hf : f ≠ 0) (r : ℝ) (hr : Irrational r) :
    ∃ x : ℕ → ℝ, (∀ n, |x n| < 1 / ((n : ℝ) + 1)) ∧ (∀ n, f (x n) = 0) ∧ (∀ n, f (r * x n) = 1 / 2) ∧
      (Tendsto x atTop (@nhds ℝ (betaT f ratLine) 0) ∧ Tendsto x atTop (@nhds ℝ (sigmaT f ratLine) 0) ∧
        Tendsto x atTop (@nhds ℝ (tauT f ratLine) 0)) ∧
      (¬ Tendsto (fun n => r * x n) atTop (@nhds ℝ (betaT f ratLine) 0) ∧
        ¬ Tendsto (fun n => r * x n) atTop (@nhds ℝ (sigmaT f ratLine) 0) ∧
        ¬ Tendsto (fun n => r * x n) atTop (@nhds ℝ (tauT f ratLine) 0)) := by
  obtain ⟨x, hx1, hx2, hx3⟩ := irrational_witness f hf r hr
  have hx0 : Tendsto x atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]
    exact (hx1 n).le
  have htau : Tendsto x atTop (@nhds ℝ (tauT f ratLine) 0) := by
    rw [tendsto_tau_iff]
    refine ⟨hx0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := mem_ratLine.1 a.2
    have : ∀ n, f ((a : ℝ) * x n) = 0 := fun n => by
      rw [← hq, f_ratmul, hx2 n, mul_zero]
    simp only [this, Rat.cast_zero]
    exact tendsto_const_nhds
  have hsig : Tendsto x atTop (@nhds ℝ (sigmaT f ratLine) 0) :=
    htau.mono_right (nhds_mono (tauT_le_sigmaT f ratLine))
  have hbeta : Tendsto x atTop (@nhds ℝ (betaT f ratLine) 0) :=
    hsig.mono_right (nhds_mono (sigmaT_le_betaT f ratLine))
  have h1 : (1 : ℝ) ∈ ratLine := mem_ratLine.2 ⟨1, by simp⟩
  have hcb : @Continuous ℝ Circ (betaT f ratLine) circTop (pfHom f 1) := by
    simpa using pfHom_cont_beta f ratLine ⟨1, h1⟩
  have hcs : @Continuous ℝ Circ (sigmaT f ratLine) circTop (pfHom f 1) :=
    continuous_iff_le_induced.2 ((sigmaT_le_betaT f ratLine).trans (continuous_iff_le_induced.1 hcb))
  have hct : @Continuous ℝ Circ (tauT f ratLine) circTop (pfHom f 1) :=
    continuous_iff_le_induced.2 ((tauT_le_sigmaT f ratLine).trans (continuous_iff_le_induced.1 hcs))
  have hz : ∀ n, pfHom f 1 (r * x n) = ((1 / 2 : ℝ) : Circ) := fun n => by
    rw [pfHom_apply, one_mul, hx3 n]
    push_cast
    rfl
  exact ⟨x, hx1, hx2, hx3, ⟨hbeta, hsig, htau⟩,
    not_tendsto_of_const _ hcb 0 (map_zero _) _ hz, not_tendsto_of_const _ hcs 0 (map_zero _) _ hz,
    not_tendsto_of_const _ hct 0 (map_zero _) _ hz⟩

end Irrational

section JoinTest

/-- If `‖t‖ ≤ 1/4` and `‖t + t‖ ≤ 1/4` then `‖t‖ < 1/4`. -/
lemma norm_lt_quarter_of_double {t : Circ} (h1 : ‖t‖ ≤ 1 / 4) (h2 : ‖t + t‖ ≤ 1 / 4) : ‖t‖ < 1 / 4 := by
  obtain ⟨θ, rfl, hθ, hn⟩ := exists_centered t
  rw [hn] at h1 ⊢
  have habs : |θ| ≤ 1 / 4 := h1
  have hd : |2 * θ| ≤ 1 / 2 := by
    rw [abs_mul]; norm_num; linarith
  have e : ((θ : ℝ) : Circ) + (θ : Circ) = ((2 * θ : ℝ) : Circ) := by
    rw [← AddCircle.coe_add]; ring_nf
  rw [e, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using hd)] at h2
  rw [abs_mul] at h2
  norm_num at h2
  linarith

/-- **A fixed irrational character as a join test** (17.9).  If `η₁, η₂` are group topologies on `ℝ` with
zero-neighbourhoods `U₁, U₂` such that `ψ_r(U₁ ∩ U₂) ⊆ [-1/4, 1/4] + ℤ`, then `ψ_r` is continuous for the join
`η₁ ∨ η₂` (Mathlib's `⊓`) although `ψ_r ∉ H_{f,ℚ}`; so the join is not compatible with `H_{f,ℚ}`. -/
theorem irrational_join_test (f : ℝ →+ ℚ) (hf : f ≠ 0) (r : ℝ) (hr : Irrational r)
    (η₁ η₂ : TopologicalSpace ℝ) (h₁ : @IsTopologicalAddGroup ℝ η₁ _) (h₂ : @IsTopologicalAddGroup ℝ η₂ _)
    (U₁ U₂ : Set ℝ) (hU₁ : U₁ ∈ @nhds ℝ η₁ 0) (hU₂ : U₂ ∈ @nhds ℝ η₂ 0)
    (hsmall : ∀ x ∈ U₁ ∩ U₂, ‖pfHom f r x‖ ≤ 1 / 4) :
    @Continuous ℝ Circ (η₁ ⊓ η₂) circTop (pfHom f r) ∧ pfHom f r ∉ Hq f := by
  refine ⟨?_, psiR_not_mem f hf r hr⟩
  letI : TopologicalSpace ℝ := η₁ ⊓ η₂
  haveI : IsTopologicalAddGroup ℝ := isTopologicalAddGroup_inf h₁ h₂
  have hW : U₁ ∩ U₂ ∈ 𝓝 (0 : ℝ) := by
    have hn : (𝓝 (0 : ℝ)) = @nhds ℝ η₁ 0 ⊓ @nhds ℝ η₂ 0 := @nhds_inf ℝ η₁ η₂ 0
    rw [hn]
    exact Filter.inter_mem_inf hU₁ hU₂
  have hdbl : Continuous (fun x : ℝ => x + x) := continuous_id.add continuous_id
  have hV : (fun x : ℝ => x + x) ⁻¹' (U₁ ∩ U₂) ∩ (U₁ ∩ U₂) ∈ 𝓝 (0 : ℝ) := by
    refine Filter.inter_mem ?_ hW
    refine hdbl.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  refine continuous_of_quarter_gen (pfHom f r) hV (fun x hx => ?_)
  refine norm_lt_quarter_of_double (hsmall x hx.2) ?_
  have := hsmall (x + x) hx.1
  rw [map_add] at this
  exact this

end JoinTest

end LeanCheck
