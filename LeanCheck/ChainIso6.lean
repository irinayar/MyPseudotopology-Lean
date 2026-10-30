import LeanCheck.ChainIso5

/-!
# Isomorphism classification, part 6: automorphisms and shears
(TVGQ-v7 Corollary `tauiso:auto`)

The automorphisms of `(ℝ, τ_{f,ℚ})` are exactly `L_{c,s} x = c x + s f(x)` with `c ∈ ℚ \ {0}` and
`c + f(s) ≠ 0`; composition and inverse formulas; the shear subgroup `M_s = L_{1,s}`.
-/

namespace LeanCheck

open Filter Topology

/-! ### The maps `L_{c,s}` -/

/-- `L_{c,s} x = c x + s f(x)`. -/
noncomputable def Lcs (f : ℝ →+ ℚ) (c : ℚ) (s : ℝ) : ℝ →+ ℝ where
  toFun x := (c : ℝ) * x + s * ((f x : ℚ) : ℝ)
  map_zero' := by simp
  map_add' x y := by push_cast [map_add]; ring

lemma Lcs_apply (f : ℝ →+ ℚ) (c : ℚ) (s x : ℝ) :
    Lcs f c s x = (c : ℝ) * x + s * ((f x : ℚ) : ℝ) := rfl

lemma f_real_ratmul (f : ℝ →+ ℚ) (s : ℝ) (q : ℚ) : f (s * (q : ℝ)) = q * f s := by
  rw [mul_comm, f_ratmul]

lemma f_div_rat (f : ℝ →+ ℚ) (y : ℝ) (c : ℚ) (hc : c ≠ 0) : f (y / (c : ℝ)) = f y / c := by
  have : y / (c : ℝ) = ((c⁻¹ : ℚ) : ℝ) * y := by
    have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    push_cast; field_simp
  rw [this, f_ratmul]; field_simp

/-- **Composition**: `L_{c,s} ∘ L_{c',s'} = L_{cc', c s' + c' s + s f(s')}`. -/
theorem Lcs_comp (f : ℝ →+ ℚ) (c c' : ℚ) (s s' x : ℝ) :
    Lcs f c s (Lcs f c' s' x) = Lcs f (c * c') ((c : ℝ) * s' + (c' : ℝ) * s + s * ((f s' : ℚ) : ℝ)) x := by
  simp only [Lcs_apply]
  have : f ((c' : ℝ) * x + s' * ((f x : ℚ) : ℝ)) = c' * f x + f x * f s' := by
    rw [map_add, f_ratmul, f_real_ratmul]
  rw [this]
  push_cast
  ring

/-- The inverse `y ↦ y/c − s f(y) / (c (c + f s))`. -/
noncomputable def Linv (f : ℝ →+ ℚ) (c : ℚ) (s : ℝ) (y : ℝ) : ℝ :=
  y / (c : ℝ) - s * (((f y : ℚ) / (c * (c + f s)) : ℚ) : ℝ)

theorem Lcs_Linv (f : ℝ →+ ℚ) (c : ℚ) (s : ℝ) (hc : c ≠ 0) (hK : c + f s ≠ 0) (y : ℝ) :
    Lcs f c s (Linv f c s y) = y := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hKR : (c : ℝ) + ((f s : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hK
  simp only [Lcs_apply, Linv]
  have : f (y / (c : ℝ) - s * (((f y : ℚ) / (c * (c + f s)) : ℚ) : ℝ)) =
      f y / c - (f y / (c * (c + f s))) * f s := by
    rw [map_sub, f_div_rat f y c hc, f_real_ratmul]
  rw [this]
  push_cast
  field_simp
  ring

theorem Linv_Lcs (f : ℝ →+ ℚ) (c : ℚ) (s : ℝ) (hc : c ≠ 0) (hK : c + f s ≠ 0) (x : ℝ) :
    Linv f c s (Lcs f c s x) = x := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hKR : (c : ℝ) + ((f s : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hK
  have h1 : f (Lcs f c s x) = f x * (c + f s) := by
    rw [Lcs_apply, map_add, f_ratmul, f_real_ratmul]; ring
  simp only [Linv]
  rw [h1]
  simp only [Lcs_apply]
  push_cast
  field_simp
  ring

/-! ### Invertibility of `A` in the one-term case -/

lemma Wsp_unit (σ0 : ℝ) : Wsp (fun _ : Unit => σ0) = Submodule.span ℚ {σ0} := by
  unfold Wsp
  rw [Set.range_const]

lemma Lam_unit (f : ℝ →+ ℚ) (σ0 x : ℝ) :
    LamHom f (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => σ0) x = σ0 * ((f x : ℚ) : ℝ) := by
  simp [LamHom_apply]

lemma A_unit (f : ℝ →+ ℚ) (σ0 : ℝ) (q : ℚ) :
    ((q : ℝ) * σ0) + LamHom f (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => σ0) ((q : ℝ) * σ0) =
      (((q * (1 + f σ0) : ℚ)) : ℝ) * σ0 := by
  rw [Lam_unit, f_ratmul]
  push_cast
  ring

/-- `A` is invertible iff `1 + f(σ₀) ≠ 0`. -/
theorem ainv_unit_iff (f : ℝ →+ ℚ) (σ0 : ℝ) :
    AInv f (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => σ0) ↔ (1 + f σ0 : ℚ) ≠ 0 := by
  have hW : ∀ w, w ∈ Wsp (fun _ : Unit => σ0) ↔ ∃ q : ℚ, w = (q : ℝ) * σ0 := by
    intro w
    rw [Wsp_unit, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩
    · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩
  constructor
  · rintro ⟨hinj, -⟩ hρ
    have h1 : ((1 : ℚ) : ℝ) * σ0 ∈ Wsp (fun _ : Unit => σ0) := (hW _).2 ⟨1, rfl⟩
    have h2 := A_unit f σ0 1
    rw [one_mul, hρ] at h2
    simp only [Rat.cast_one, one_mul, Rat.cast_zero, zero_mul] at h2 h1
    have h0 : σ0 = 0 := hinj σ0 h1 h2
    rw [h0, map_zero] at hρ
    simp at hρ
  · intro hρ
    refine ⟨fun w hw hw0 => ?_, fun w hw => ?_⟩
    · obtain ⟨q, rfl⟩ := (hW w).1 hw
      rw [A_unit] at hw0
      rcases mul_eq_zero.1 hw0 with h | h
      · have : q * (1 + f σ0) = 0 := by exact_mod_cast h
        rcases mul_eq_zero.1 this with h' | h'
        · rw [h']; simp
        · exact absurd h' hρ
      · rw [h]; simp
    · obtain ⟨q, rfl⟩ := (hW w).1 hw
      refine ⟨((q / (1 + f σ0) : ℚ) : ℝ) * σ0, (hW _).2 ⟨_, rfl⟩, ?_⟩
      rw [A_unit]
      congr 2
      field_simp

/-! ### The automorphism group of `(ℝ, τ_{f,ℚ})` -/

/-- **Automorphisms** (TVGQ-v7 Corollary `tauiso:auto`): the topological group automorphisms of
`(ℝ, τ_{f,ℚ})` are exactly the maps `L_{c,s}` with `c ∈ ℚ \ {0}` and `c + f(s) ≠ 0`. -/
theorem tau_auto_iff (f : ℝ →+ ℚ) (hf : f ≠ 0) (L : ℝ →+ ℝ) :
    (∃ e : ℝ ≃+ ℝ, (∀ x, e x = L x) ∧ Continuous[tauT f ratSub, tauT f ratSub] e ∧
        Continuous[tauT f ratSub, tauT f ratSub] e.symm) ↔
      ∃ (c : ℚ) (s : ℝ), c ≠ 0 ∧ c + f s ≠ 0 ∧ ∀ x, L x = Lcs f c s x := by
  constructor
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨c, κ, hκ, b, σ, hc, hb, hL⟩ := tau_iso_rep f f ratSub ratSub e h1
    -- collapse the finite sum to one term
    choose r hr using fun j => (mem_ratSub (b j)).1 (hb j)
    set s0 : ℝ := ∑ j, σ j * (r j : ℝ) with hs0
    have hLam : ∀ x, LamHom f b σ x = s0 * ((f x : ℚ) : ℝ) := by
      intro x
      rw [LamHom_apply, hs0, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hr j, f_ratmul]
      push_cast; ring
    have hL1 : ∀ x, L x = c * (x + LamHom f (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => s0) x) := by
      intro x
      rw [Lam_unit, ← hLam, ← he, hL]
    obtain ⟨hA, heq⟩ := (tau_iso_criterion f f ratSub ratSub c hc (fun _ : Unit => (1 : ℝ))
      (fun _ : Unit => s0) (fun _ => (mem_ratSub 1).2 ⟨1, by simp⟩) L hL1).1 ⟨e, he, h1, h2⟩
    obtain ⟨r0, hr0, hfr⟩ := (fscaled_Q_iff f f hf c).1 heq
    have hcr : c = (r0 : ℝ) := by
      apply fa_inj f hf
      ext x
      simp only [fa_apply]
      rw [hfr x, f_ratmul]
    have hρ := (ainv_unit_iff f s0).1 hA
    refine ⟨r0, c * s0, hr0, ?_, fun x => ?_⟩
    · have : f (c * s0) = r0 * f s0 := by rw [hcr]; exact f_ratmul f r0 s0
      rw [this]
      have : r0 * (1 + f s0) ≠ 0 := mul_ne_zero hr0 hρ
      intro h; apply this; linarith
    · rw [Lcs_apply, ← he, hL x, hLam, hcr]
      ring
  · rintro ⟨c, s, hc, hK, hL⟩
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    set σ0 : ℝ := ((c⁻¹ : ℚ) : ℝ) * s with hσ0
    have hρ : (1 + f σ0 : ℚ) ≠ 0 := by
      have : f σ0 = c⁻¹ * f s := by rw [hσ0, f_ratmul]
      rw [this]
      intro h
      apply hK
      have : c * (1 + c⁻¹ * f s) = c + f s := by field_simp
      rw [← this, h, mul_zero]
    have hL1 : ∀ x, L x = (c : ℝ) * (x + LamHom f (fun _ : Unit => (1 : ℝ))
        (fun _ : Unit => σ0) x) := by
      intro x
      rw [hL x, Lcs_apply, Lam_unit, hσ0]
      push_cast
      field_simp
    have heq : FsetScaled f (c : ℝ) ratSub = Fset f ratSub :=
      (fscaled_Q_iff f f hf (c : ℝ)).2 ⟨c, hc, fun x => f_ratmul f c x⟩
    exact (tau_iso_criterion f f ratSub ratSub (c : ℝ) hcR (fun _ : Unit => (1 : ℝ))
      (fun _ : Unit => σ0) (fun _ => (mem_ratSub 1).2 ⟨1, by simp⟩) L hL1).2
      ⟨(ainv_unit_iff f σ0).2 hρ, heq⟩

/-! ### Shears -/

/-- The shear `M_s = L_{1,s}`. -/
noncomputable abbrev Mshear (f : ℝ →+ ℚ) (s : ℝ) : ℝ →+ ℝ := Lcs f 1 s

theorem Mshear_comp (f : ℝ →+ ℚ) (s s' x : ℝ) :
    Mshear f s (Mshear f s' x) = Mshear f (s' + s + s * ((f s' : ℚ) : ℝ)) x := by
  rw [Lcs_comp]
  simp

/-- The homomorphism `M_s ↦ 1 + f(s)` onto `ℚˣ`: multiplicative for the shear composition law. -/
theorem shear_hom (f : ℝ →+ ℚ) (s s' : ℝ) :
    1 + f (s' + s + s * ((f s' : ℚ) : ℝ)) = (1 + f s) * (1 + f s') := by
  rw [map_add, map_add, f_real_ratmul]
  ring

/-- Splitting: `q ↦ M_{(q-1)u}` is a multiplicative section when `f u = 1`. -/
theorem shear_section (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (q : ℚ) :
    1 + f (((q - 1 : ℚ) : ℝ) * u) = q := by
  rw [f_ratmul, hu]; ring

theorem shear_section_mul (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (q q' : ℚ) :
    (((q' - 1 : ℚ) : ℝ) * u) + (((q - 1 : ℚ) : ℝ) * u) +
        (((q - 1 : ℚ) : ℝ) * u) * ((f (((q' - 1 : ℚ) : ℝ) * u) : ℚ) : ℝ) =
      (((q * q' - 1 : ℚ) : ℝ) * u) := by
  rw [f_ratmul, hu]
  push_cast
  ring

/-- Kernel: shears with `f k = 0` compose additively. -/
theorem shear_kernel (f : ℝ →+ ℚ) (k k' : ℝ) (hk : f k' = 0) :
    k' + k + k * ((f k' : ℚ) : ℝ) = k + k' := by
  rw [hk]; simp; ring

/-- `M_u M_k = M_{u+k}` for `k ∈ ker f`. -/
theorem shear_comm_left (f : ℝ →+ ℚ) (u k : ℝ) (hk : f k = 0) (x : ℝ) :
    Mshear f u (Mshear f k x) = Mshear f (u + k) x := by
  rw [Mshear_comp, hk]; simp [add_comm]

/-- `M_k M_u = M_{u+2k}` when `f u = 1`. -/
theorem shear_comm_right (f : ℝ →+ ℚ) (u k : ℝ) (hu : f u = 1) (x : ℝ) :
    Mshear f k (Mshear f u x) = Mshear f (u + 2 * k) x := by
  rw [Mshear_comp, hu]; simp; ring_nf

/-- The shear group is nonabelian: `M_u M_k ≠ M_k M_u` for nonzero `k ∈ ker f`. -/
theorem shear_nonabelian (f : ℝ →+ ℚ) (u k : ℝ) (hu : f u = 1) (hk : f k = 0) (hk0 : k ≠ 0) :
    ∃ x, Mshear f u (Mshear f k x) ≠ Mshear f k (Mshear f u x) := by
  refine ⟨u, fun h => hk0 ?_⟩
  rw [shear_comm_left f u k hk, shear_comm_right f u k hu] at h
  simp only [Lcs_apply, hu] at h
  push_cast at h
  linarith

/-- If `1 ∈ S` and `1 + f(s) ≠ 0` then `M_s` is an automorphism of `(ℝ, τ_{f,S})`. -/
theorem shear_auto (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (h1 : (1 : ℝ) ∈ S) (s : ℝ)
    (hs : (1 + f s : ℚ) ≠ 0) :
    ∃ e : ℝ ≃+ ℝ, (∀ x, e x = Mshear f s x) ∧ Continuous[tauT f S, tauT f S] e ∧
      Continuous[tauT f S, tauT f S] e.symm := by
  have hL : ∀ x, Mshear f s x = (1 : ℝ) * (x + LamHom f (fun _ : Unit => (1 : ℝ))
      (fun _ : Unit => s) x) := by
    intro x
    rw [Lam_unit, Lcs_apply]; push_cast; ring
  have heq : FsetScaled f (1 : ℝ) S = Fset f S := by
    ext m
    simp [FsetScaled, Fset]
  exact (tau_iso_criterion f f S S 1 one_ne_zero (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => s)
    (fun _ => h1) (Mshear f s) hL).2 ⟨(ainv_unit_iff f s).2 hs, heq⟩

end LeanCheck
