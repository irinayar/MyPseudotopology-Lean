import LeanCheck.ChainNecessaryMackey
import LeanCheck.ChainIso7

/-!
# Basic facts about TVGQ topologies and the exact scalar rings
(TVGQ-v7 Proposition 2.2 `division`, Proposition 2.4 `ring`, the homeomorphism sentence of Theorem 7.1,
Corollary 7.3 `transcendental example`)

* `tvgq_division_equiv` : the TVGQ condition (all rational dilations continuous) is equivalent to continuity of
  `x ↦ x/n` for every `n ≥ 1`, and to each `x ↦ n x` being a homeomorphism;
* `scalarCont_subring` : the continuous scalar ring is a unital subring of `ℝ` containing `ℚ`;
  `isHomeomorph_mul_iff` : a nonzero `a` acts by a homeomorphism iff `a` and `a⁻¹` are continuous scalars;
* `homeo_iff_scalar_beta/sigma/tau` : multiplication by `r` is a homeomorphism of `β/σ/τ_{f,S}` iff `r S = S`;
* `transcendental_example` : for transcendental `t` and `S = ℚ[t]` multiplication by `t` is a continuous bijection
  with discontinuous inverse in each of the three topologies.
-/

namespace LeanCheck

open Filter Topology

section Basics

lemma natmul_cont' (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) (n : ℕ) :
    Continuous[τ, τ] (fun x : ℝ => (n : ℝ) * x) := by
  letI := τ
  haveI := hτ
  have : (fun x : ℝ => (n : ℝ) * x) = fun x => n • x := by funext x; simp [nsmul_eq_mul]
  rw [this]; exact continuous_nsmul n

lemma intmul_cont' (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) (z : ℤ) :
    Continuous[τ, τ] (fun x : ℝ => (z : ℝ) * x) := by
  letI := τ
  haveI := hτ
  have : (fun x : ℝ => (z : ℝ) * x) = fun x => z • x := by funext x; simp [zsmul_eq_mul]
  rw [this]; exact continuous_zsmul z

/-- **Proposition 2.2 (`division`).**  For an additive group topology on `ℝ`, the TVGQ condition is equivalent to
continuity of `x ↦ x/n` for every positive integer `n`, and also to each `x ↦ n x` (`n ≥ 1`) being a
homeomorphism. -/
theorem tvgq_division_equiv (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) :
    List.TFAE
      [ ∀ q : ℚ, Continuous[τ, τ] (fun x : ℝ => (q : ℝ) * x),
        ∀ n : ℕ, 0 < n → Continuous[τ, τ] (fun x : ℝ => x / (n : ℝ)),
        ∀ n : ℕ, 0 < n → @IsHomeomorph ℝ ℝ τ τ (fun x : ℝ => (n : ℝ) * x) ] := by
  tfae_have 1 → 2 := by
    intro h n hn
    have e : (fun x : ℝ => x / (n : ℝ)) = fun x : ℝ => (((1 : ℚ) / n : ℚ) : ℝ) * x := by
      funext x; push_cast; ring
    rw [e]; exact h _
  tfae_have 2 → 1 := by
    intro h q
    have e : (fun x : ℝ => (q : ℝ) * x) =
        (fun y : ℝ => (q.num : ℝ) * y) ∘ (fun x : ℝ => x / (q.den : ℝ)) := by
      funext x
      simp only [Function.comp]
      have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
      have : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
      rw [this]; field_simp
    rw [e]
    exact @Continuous.comp ℝ ℝ ℝ τ τ τ _ _ (intmul_cont' τ hτ q.num) (h q.den q.den_pos)
  tfae_have 2 → 3 := by
    intro h n hn
    rw [isHomeomorph_iff_exists_inverse]
    refine ⟨natmul_cont' τ hτ n, fun x => x / (n : ℝ), ?_, ?_, h n hn⟩
    · intro x
      have hd : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only; field_simp
    · intro x
      have hd : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only; field_simp
  tfae_have 3 → 2 := by
    intro h n hn
    obtain ⟨-, g, hl, -, hg⟩ := (isHomeomorph_iff_exists_inverse).1 (h n hn)
    have hd : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : (fun x : ℝ => x / (n : ℝ)) = g := by
      funext x
      have := hl (x / (n : ℝ))
      simp only at this
      rw [mul_div_cancel₀ _ hd] at this
      exact this.symm
    rw [this]; exact hg
  tfae_finish

/-- The continuous scalar ring of a topology on `ℝ`. -/
theorem scalarCont_subring (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (fun x : ℝ => (q : ℝ) * x)) :
    ∃ R : Subring ℝ, (R : Set ℝ) = scalarCont τ ∧ ∀ q : ℚ, (q : ℝ) ∈ R := by
  letI := τ
  haveI := hτ
  refine ⟨{ carrier := scalarCont τ
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, rfl, fun q => hq q⟩
  · intro a b ha hb
    show Continuous[τ, τ] (fun x : ℝ => (a * b) * x)
    have e : (fun x : ℝ => (a * b) * x) = (fun y : ℝ => a * y) ∘ (fun x : ℝ => b * x) := by
      funext x; simp [mul_assoc]
    rw [e]
    exact @Continuous.comp ℝ ℝ ℝ τ τ τ _ _ ha hb
  · show Continuous[τ, τ] (fun x : ℝ => (1 : ℝ) * x)
    simp only [one_mul]; exact continuous_id
  · intro a b ha hb
    show Continuous[τ, τ] (fun x : ℝ => (a + b) * x)
    have e : (fun x : ℝ => (a + b) * x) = fun x => a * x + b * x := by funext x; ring
    rw [e]
    exact ha.add hb
  · show Continuous[τ, τ] (fun x : ℝ => (0 : ℝ) * x)
    simp only [zero_mul]; exact continuous_const
  · intro a ha
    show Continuous[τ, τ] (fun x : ℝ => (-a) * x)
    have e : (fun x : ℝ => (-a) * x) = fun x => -(a * x) := by funext x; ring
    rw [e]
    exact ha.neg

/-- **Proposition 2.4 (`ring`), second sentence.**  A nonzero scalar acts by a homeomorphism exactly when
both `a` and `a⁻¹` are continuous scalars. -/
theorem isHomeomorph_mul_iff (τ : TopologicalSpace ℝ) (a : ℝ) (ha : a ≠ 0) :
    @IsHomeomorph ℝ ℝ τ τ (fun x : ℝ => a * x) ↔ a ∈ scalarCont τ ∧ a⁻¹ ∈ scalarCont τ := by
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · rintro ⟨h1, g, hl, -, hg⟩
    refine ⟨h1, ?_⟩
    have : (fun x : ℝ => a⁻¹ * x) = g := by
      funext x
      have := hl (a⁻¹ * x)
      simp only at this
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul] at this
      exact this.symm
    show Continuous[τ, τ] (fun x : ℝ => a⁻¹ * x)
    rw [this]; exact hg
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x => a⁻¹ * x, ?_, ?_, h2⟩
    · intro x; simp only; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    · intro x; simp only; rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- `r S = S` (as sets) is the same as `r` and `r⁻¹` both lying in `M(S)`. -/
theorem scalarRing_inv_iff (S : Submodule ℚ ℝ) (r : ℝ) (hr : r ≠ 0) :
    ((fun a : ℝ => a * r) '' (S : Set ℝ) = S) ↔ r ∈ scalarRing S ∧ r⁻¹ ∈ scalarRing S := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have : a * r ∈ (fun a : ℝ => a * r) '' (S : Set ℝ) := ⟨a, ha, rfl⟩
      rw [h] at this; exact this
    · have ha' : a ∈ (fun a : ℝ => a * r) '' (S : Set ℝ) := by rw [h]; exact ha
      obtain ⟨s, hs, rfl⟩ := ha'
      simpa [mul_assoc, mul_inv_cancel₀ hr] using hs
  · rintro ⟨h1, h2⟩
    ext a
    constructor
    · rintro ⟨s, hs, rfl⟩; exact h1 s hs
    · intro ha
      exact ⟨a * r⁻¹, h2 a ha, by simp [mul_assoc, inv_mul_cancel₀ hr]⟩

/-- **Theorem 7.1, homeomorphism sentence (`β`).** -/
theorem homeo_iff_scalar_beta (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) (hr : r ≠ 0) :
    @IsHomeomorph ℝ ℝ (betaT f S) (betaT f S) (fun x : ℝ => r * x) ↔
      ((fun a : ℝ => a * r) '' (S : Set ℝ) = S) := by
  rw [isHomeomorph_mul_iff _ r hr, scalarRing_inv_iff S r hr]
  show Continuous[betaT f S, betaT f S] (fun x : ℝ => r * x) ∧ Continuous[betaT f S, betaT f S] (fun x : ℝ => r⁻¹ * x) ↔ _
  rw [scalar_beta f u hu S r, scalar_beta f u hu S r⁻¹]

theorem homeo_iff_scalar_sigma (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) (hr : r ≠ 0) :
    @IsHomeomorph ℝ ℝ (sigmaT f S) (sigmaT f S) (fun x : ℝ => r * x) ↔
      ((fun a : ℝ => a * r) '' (S : Set ℝ) = S) := by
  rw [isHomeomorph_mul_iff _ r hr, scalarRing_inv_iff S r hr]
  show Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => r * x) ∧ Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => r⁻¹ * x) ↔ _
  rw [scalar_sigma f u hu S r, scalar_sigma f u hu S r⁻¹]

theorem homeo_iff_scalar_tau (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) (hr : r ≠ 0) :
    @IsHomeomorph ℝ ℝ (tauT f S) (tauT f S) (fun x : ℝ => r * x) ↔
      ((fun a : ℝ => a * r) '' (S : Set ℝ) = S) := by
  rw [isHomeomorph_mul_iff _ r hr, scalarRing_inv_iff S r hr]
  show Continuous[tauT f S, tauT f S] (fun x : ℝ => r * x) ∧ Continuous[tauT f S, tauT f S] (fun x : ℝ => r⁻¹ * x) ↔ _
  rw [scalar_tau f u hu S r, scalar_tau f u hu S r⁻¹]

/-! ### Corollary 7.3: a continuous bijection with discontinuous inverse -/

lemma inv_not_mem_adjoin (t : ℝ) (ht : Transcendental ℚ t) :
    t⁻¹ ∉ (Algebra.adjoin ℚ {t} : Subalgebra ℚ ℝ) := by
  intro h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by
      refine ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩)
  have hq : Polynomial.aeval t (Polynomial.X * p - 1) = 0 := by
    simp only [map_sub, map_mul, Polynomial.aeval_X, map_one]
    rw [show Polynomial.aeval t p = t⁻¹ from hp, mul_inv_cancel₀ ht0, sub_self]
  have h0 : (Polynomial.X * p - 1 : Polynomial ℚ) = 0 := by
    by_contra hne
    exact ht ⟨_, hne, hq⟩
  have := congrArg (fun q : Polynomial ℚ => q.coeff 0) h0
  simp at this

/-- **Corollary 7.3.**  For transcendental `t` and `S = ℚ[t]`, in each of `β`, `σ`, `τ`:
multiplication by `t` is continuous and bijective, but its inverse is not continuous. -/
theorem transcendental_example (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (t : ℝ) (ht : Transcendental ℚ t) :
    let S : Submodule ℚ ℝ := Subalgebra.toSubmodule (Algebra.adjoin ℚ {t})
    (Continuous[betaT f S, betaT f S] (fun x : ℝ => t * x) ∧ Function.Bijective (fun x : ℝ => t * x) ∧
      ¬ Continuous[betaT f S, betaT f S] (fun x : ℝ => t⁻¹ * x)) ∧
    (Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => t * x) ∧ Function.Bijective (fun x : ℝ => t * x) ∧
      ¬ Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => t⁻¹ * x)) ∧
    (Continuous[tauT f S, tauT f S] (fun x : ℝ => t * x) ∧ Function.Bijective (fun x : ℝ => t * x) ∧
      ¬ Continuous[tauT f S, tauT f S] (fun x : ℝ => t⁻¹ * x)) := by
  intro S
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by refine ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩)
  have hS1 : (1 : ℝ) ∈ S := (Algebra.adjoin ℚ {t}).one_mem
  have htS : t ∈ scalarRing S := by
    intro a ha
    have hA : a ∈ (Algebra.adjoin ℚ {t} : Subalgebra ℚ ℝ) := ha
    exact (Algebra.adjoin ℚ {t}).mul_mem hA (Algebra.self_mem_adjoin_singleton ℚ t)
  have hinv : t⁻¹ ∉ scalarRing S := by
    intro h
    have := h 1 hS1
    rw [one_mul] at this
    exact inv_not_mem_adjoin t ht this
  have hbij : Function.Bijective (fun x : ℝ => t * x) := by
    constructor
    · intro x y h; exact mul_left_cancel₀ ht0 h
    · intro y; exact ⟨t⁻¹ * y, by simp [← mul_assoc, mul_inv_cancel₀ ht0]⟩
  refine ⟨⟨?_, hbij, ?_⟩, ⟨?_, hbij, ?_⟩, ⟨?_, hbij, ?_⟩⟩
  · exact (scalar_beta f u hu S t).2 htS
  · intro h; exact hinv ((scalar_beta f u hu S t⁻¹).1 h)
  · exact (scalar_sigma f u hu S t).2 htS
  · intro h; exact hinv ((scalar_sigma f u hu S t⁻¹).1 h)
  · exact (scalar_tau f u hu S t).2 htS
  · intro h; exact hinv ((scalar_tau f u hu S t⁻¹).1 h)

end Basics

end LeanCheck
