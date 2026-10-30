import Mathlib

/-!
# Product formula for the averaged central mass: abstract core (Claude 09:45 note, Codex 11:03 audit)

Checked here (all with hypotheses stated explicitly; nothing about the cascade itself is assumed beyond them):

* `farfield`, `farfield_geom`: the far-field recursion without counting words.  The functions `h k`
  are normalised convolutions with `0 ≤ h ≤ 1`, `h L = 0` outside radius `ε`, and the one-step
  inequality `h k y ≤ ∑_d w_{k+1}(d) h_{k+1}(y+d)`.  Conclusion: for `‖y‖ ≥ u`, `ε ≤ 3u/4`,
  `h k y ≤ ∑_{m<n} B^m * (tail mass of level k+m+1 beyond norm u/2^(m+3))`.
* `center_max`: a function with nonnegative cosine coefficients is maximal at `0`.
* `telescope`: the exact product identity from the one-step ratios.
* `two_term_ne`: the two-term displacement `r/P + s/Q` is not an integer when `P,Q` are coprime and
  `0 < |r| < P` (the non-vanishing used before the three-logarithm bound).
* `autocorr`, `kernel_fourier_nonneg`: the finite identity `∑_r |W(r)|² e(rt/Q) = Q ∑_x w(x) w(x+t)`
  on `ZMod Q`, hence nonnegativity of the integer Fourier coefficients of the discrete window kernel.

Not checked here: the tail bound for
the kernel, the growth lemma for merged levels, the Matveev lower bound, and the reduction to JA.
-/

namespace LeanCheck
namespace MixedPrimeProduct

section farfield

variable {G : Type*} [SeminormedAddCommGroup G]

/-- Mass of the level-`j` kernel at displacements of norm larger than `v`. -/
noncomputable def tailMass (S : ℕ → Finset G) (w : ℕ → G → ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  ∑ d ∈ S j, if v < ‖d‖ then w j d else 0

lemma tailMass_nonneg (S : ℕ → Finset G) (w : ℕ → G → ℝ) (hw : ∀ j d, 0 ≤ w j d) (j : ℕ)
    (v : ℝ) : 0 ≤ tailMass S w j v := by
  unfold tailMass
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact hw j d
  · exact le_rfl

theorem farfield (S : ℕ → Finset G) (w : ℕ → G → ℝ) (hw : ∀ j d, 0 ≤ w j d)
    (B : ℝ) (hmass : ∀ j, ∑ d ∈ S j, w j d ≤ B)
    (h : ℕ → G → ℝ) (h0 : ∀ k y, 0 ≤ h k y) (h1 : ∀ k y, h k y ≤ 1)
    (L : ℕ) (ε : ℝ)
    (hrec : ∀ k, k < L → ∀ y, h k y ≤ ∑ d ∈ S (k + 1), w (k + 1) d * h (k + 1) (y + d))
    (hL : ∀ y, ε ≤ ‖y‖ → h L y = 0) :
    ∀ (n k : ℕ), k + n = L → ∀ (c : ℕ → ℝ) (y : G),
      ε + ∑ m ∈ Finset.range n, c (m + 1) ≤ ‖y‖ →
      h k y ≤ ∑ m ∈ Finset.range n, B ^ m * tailMass S w (k + m + 1) (c (m + 1)) := by
  have hB : 0 ≤ B := le_trans (Finset.sum_nonneg (fun d _ => hw 0 d)) (hmass 0)
  intro n
  induction n with
  | zero =>
    intro k hk c y hy
    have hkL : k = L := by omega
    subst hkL
    simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hy ⊢
    rw [hL y hy]
  | succ n ih =>
    intro k hk c y hy
    have hkL : k < L := by omega
    set R : ℝ := ∑ m ∈ Finset.range n, B ^ m * tailMass S w (k + 1 + m + 1) (c (m + 1 + 1)) with hR
    have hRnn : 0 ≤ R := by
      apply Finset.sum_nonneg
      intro m _
      exact mul_nonneg (pow_nonneg hB m) (tailMass_nonneg S w hw _ _)
    have hsum : ∑ m ∈ Finset.range (n + 1), c (m + 1)
        = ∑ m ∈ Finset.range n, c (m + 1 + 1) + c (0 + 1) := Finset.sum_range_succ' _ _
    have hIH : ∀ d : G, ‖d‖ ≤ c 1 → h (k + 1) (y + d) ≤ R := by
      intro d hd
      have hnorm : ‖y‖ ≤ ‖y + d‖ + ‖d‖ := by
        have := norm_sub_le (y + d) d
        simpa using this
      have := ih (k + 1) (by omega) (fun m => c (m + 1)) (y + d) (by
        show ε + ∑ m ∈ Finset.range n, c (m + 1 + 1) ≤ ‖y + d‖
        have h2 : c (0 + 1) = c 1 := rfl
        linarith)
      simpa [hR] using this
    refine le_trans (hrec k hkL y) ?_
    have hpt : ∀ d ∈ S (k + 1), w (k + 1) d * h (k + 1) (y + d)
        ≤ (if c 1 < ‖d‖ then w (k + 1) d else 0) + w (k + 1) d * R := by
      intro d _
      by_cases hd : c 1 < ‖d‖
      · rw [if_pos hd]
        have := h1 (k + 1) (y + d)
        have := hw (k + 1) d
        have : 0 ≤ w (k + 1) d * R := mul_nonneg (hw _ _) hRnn
        nlinarith
      · rw [if_neg hd]
        have := hIH d (not_lt.mp hd)
        have := hw (k + 1) d
        nlinarith
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hBR : (∑ d ∈ S (k + 1), w (k + 1) d) * R ≤ B * R :=
      mul_le_mul_of_nonneg_right (hmass _) hRnn
    have heq : ∑ m ∈ Finset.range (n + 1), B ^ m * tailMass S w (k + m + 1) (c (m + 1))
        = tailMass S w (k + 1) (c 1) + B * R := by
      rw [Finset.sum_range_succ', hR, Finset.mul_sum]
      have : ∑ m ∈ Finset.range n, B ^ (m + 1) * tailMass S w (k + (m + 1) + 1) (c (m + 1 + 1))
          = ∑ m ∈ Finset.range n, B * (B ^ m * tailMass S w (k + 1 + m + 1) (c (m + 1 + 1))) := by
        apply Finset.sum_congr rfl
        intro m _
        have e : k + (m + 1) + 1 = k + 1 + m + 1 := by omega
        rw [e, pow_succ]
        ring
      rw [this]
      simp [tailMass]
      ring
    rw [heq]
    unfold tailMass
    linarith

/-- Geometric radii `u / 2^(m+3)`: total displacement at most `u/4`. -/
theorem farfield_geom (S : ℕ → Finset G) (w : ℕ → G → ℝ) (hw : ∀ j d, 0 ≤ w j d)
    (B : ℝ) (hmass : ∀ j, ∑ d ∈ S j, w j d ≤ B)
    (h : ℕ → G → ℝ) (h0 : ∀ k y, 0 ≤ h k y) (h1 : ∀ k y, h k y ≤ 1)
    (L : ℕ) (ε : ℝ)
    (hrec : ∀ k, k < L → ∀ y, h k y ≤ ∑ d ∈ S (k + 1), w (k + 1) d * h (k + 1) (y + d))
    (hL : ∀ y, ε ≤ ‖y‖ → h L y = 0) (u : ℝ) (hu0 : 0 ≤ u) (hu : ε ≤ 3 * u / 4)
    (n k : ℕ) (hk : k + n = L) (y : G) (hy : u ≤ ‖y‖) :
    h k y ≤ ∑ m ∈ Finset.range n, B ^ m * tailMass S w (k + m + 1) (u / 2 ^ (m + 3)) := by
  have key := farfield S w hw B hmass h h0 h1 L ε hrec hL n k hk (fun m => u / 2 ^ (m + 2)) y
  have hgeom : ∑ m ∈ Finset.range n, u / 2 ^ (m + 1 + 2) ≤ u / 4 := by
    have e : ∀ m : ℕ, u / 2 ^ (m + 1 + 2) = u / 8 * (1 / 2 : ℝ) ^ m := by
      intro m
      rw [one_div, inv_pow, pow_add, pow_succ]
      field_simp
      ring
    simp_rw [e]
    rw [← Finset.mul_sum]
    have := sum_geometric_two_le n
    nlinarith
  have := key (by
    show ε + ∑ m ∈ Finset.range n, u / 2 ^ (m + 1 + 2) ≤ ‖y‖
    linarith)
  simpa [pow_succ, add_assoc] using this

end farfield

/-- A function with nonnegative cosine coefficients is maximal at the origin. -/
theorem center_max {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (x : ℝ) :
    ∑ i ∈ s, a i * Real.cos (θ i * x) ≤ ∑ i ∈ s, a i * Real.cos (θ i * 0) := by
  apply Finset.sum_le_sum
  intro i _
  simp only [mul_zero, Real.cos_zero]
  have := Real.cos_le_one (θ i * x)
  have := ha i
  nlinarith

/-- Exact telescoping of the normalised ratios: if `H (i-1) 0 = f i * H i 0` with `H L 0 = 1`
then `H 0 0 = ∏ f i`. -/
theorem telescope (H : ℕ → ℝ) (f : ℕ → ℝ) (L : ℕ) (hL : H L = 1)
    (hf : ∀ i, 1 ≤ i → i ≤ L → H (i - 1) = f i * H i) :
    H 0 = ∏ i ∈ Finset.Icc 1 L, f i := by
  have : ∀ n, n ≤ L → H (L - n) = (∏ i ∈ Finset.Icc (L - n + 1) L, f i) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using hL
    | succ n ih =>
      intro hn
      have h1 : H (L - n - 1) = f (L - n) * H (L - n) := hf (L - n) (by omega) (by omega)
      have e : L - (n + 1) = L - n - 1 := by omega
      rw [e, h1, ih (by omega)]
      have : Finset.Icc (L - n - 1 + 1) L = insert (L - n) (Finset.Icc (L - n + 1) L) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [this, Finset.prod_insert (by simp)]
  simpa using this L le_rfl

/-- The two-term displacement `(r Q + s P) / (P Q)` is never an integer when `P, Q` are coprime and
`0 < |r| < P`. -/
theorem two_term_ne (P Q : ℕ) (hPQ : Nat.Coprime P Q) (r s k : ℤ) (hr0 : r ≠ 0)
    (hr : |r| < (P : ℤ)) : r * Q + s * P ≠ k * (P * Q) := by
  intro h
  have hdvd : (P : ℤ) ∣ r * Q := by
    have : r * Q = P * (k * Q - s) := by linarith
    exact ⟨_, this⟩
  have hcop : IsCoprime (P : ℤ) (Q : ℤ) := Nat.isCoprime_iff_coprime.mpr hPQ
  have hr' : (P : ℤ) ∣ r := hcop.dvd_of_dvd_mul_right hdvd
  exact hr0 (Int.eq_zero_of_abs_lt_dvd hr' hr)

/-- Finite autocorrelation identity: `∑_r |W(r)|² e(rt/Q) = Q ∑_x w(x) w(x+t)`, with
`W(r) = ∑_x w(x) e(rx/Q)` and `e(a/Q) = ZMod.stdAddChar a`. -/
theorem autocorr (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (t : ZMod Q) :
    ∑ r : ZMod Q, ((∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) *
        (∑ y, (w y : ℂ) * ZMod.stdAddChar (-(r * y)))) * ZMod.stdAddChar (r * t)
      = (Q : ℂ) * ∑ x, (w x : ℂ) * (w (x + t) : ℂ) := by
  have key : ∀ r : ZMod Q, ((∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) *
        (∑ y, (w y : ℂ) * ZMod.stdAddChar (-(r * y)))) * ZMod.stdAddChar (r * t)
      = ∑ x, ∑ y, ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t)) := by
    intro r
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    have : (ZMod.stdAddChar (r * (x - y + t)) : ℂ)
        = ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) * ZMod.stdAddChar (r * t) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [this]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have hprim : (ZMod.stdAddChar : AddChar (ZMod Q) ℂ).IsPrimitive := ZMod.isPrimitive_stdAddChar Q
  have hsum : ∀ x y : ZMod Q, ∑ r : ZMod Q, ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t))
      = if x - y + t = 0 then ((w x : ℂ) * (w y : ℂ)) * (Q : ℂ) else 0 := by
    intro x y
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ hprim]
    split_ifs <;> simp [ZMod.card]
  have h1 : ∀ x : ZMod Q, ∑ y : ZMod Q, ∑ r : ZMod Q,
      ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t))
      = (w x : ℂ) * (w (x + t) : ℂ) * (Q : ℂ) := by
    intro x
    rw [show (∑ y : ZMod Q, ∑ r : ZMod Q, ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t)))
        = ∑ y : ZMod Q, (if x - y + t = 0 then ((w x : ℂ) * (w y : ℂ)) * (Q : ℂ) else 0) from
        Finset.sum_congr rfl (fun y _ => hsum x y)]
    have : ∀ y : ZMod Q, (x - y + t = 0) ↔ (x + t = y) := by
      intro y; constructor <;> intro h <;> [skip; skip] <;> [linear_combination h; linear_combination h]
    simp_rw [this]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ r : ZMod Q,
      ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t))
      = ∑ x : ZMod Q, (w x : ℂ) * (w (x + t) : ℂ) * (Q : ℂ) :=
    Finset.sum_congr rfl (fun x _ => h1 x)
  have h3 : ∑ x : ZMod Q, ∑ r : ZMod Q, ∑ y : ZMod Q, ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t))
      = ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ r : ZMod Q, ((w x : ℂ) * (w y : ℂ)) * ZMod.stdAddChar (r * (x - y + t)) :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
  rw [h3, h2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring


/-- Nonnegativity of the integer Fourier coefficients of the kernel: for a nonnegative window `w`
on `ZMod Q`, the real part of `∑_r |W(r)|² e(rt/Q)` is `Q ∑_x w(x) w(x+t) ≥ 0`.  (The imaginary
part vanishes as well; only the real part enters the cosine coefficients.) -/
theorem kernel_fourier_nonneg (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (hw : ∀ x, 0 ≤ w x)
    (t : ZMod Q) :
    0 ≤ (∑ r : ZMod Q, ((∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) *
        (∑ y, (w y : ℂ) * ZMod.stdAddChar (-(r * y)))) * ZMod.stdAddChar (r * t)).re := by
  rw [autocorr Q w t]
  have : (Q : ℂ) * ∑ x, (w x : ℂ) * (w (x + t) : ℂ)
      = (((Q : ℝ) * ∑ x, w x * w (x + t) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  apply mul_nonneg (Nat.cast_nonneg Q)
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (hw (x + t)))


end MixedPrimeProduct
end LeanCheck
