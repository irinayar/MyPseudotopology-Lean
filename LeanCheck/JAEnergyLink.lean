import Mathlib
import LeanCheck.JATransfer

/-!
# From the spectral window to the weighted energy (end of component 16)

Lemma `lem:weighted-spectral` of `TVGaddmore_v27`.  Let `f_2, f_3` be nonnegative periodic weights, of periods `q_2, q_3`,
restricted to `[0, X]`; write `α_p(h) = ∑_{x=0}^{X-h} f_p(x) f_p(x+h)` (pairs in `[0, X]`) and
`E = α_3(0) α_2(0) + 2 ∑_{h=1}^{X} α_3(h) α_2(h)`  (the weighted collision energy, `= ∑_h α_3(h) α_2(h)`).

Checked here (no axiom, no `sorry`):

* the *seed is positive-definite*: the spectral measure `|f̂_p|^2` of any nonnegative periodic weight is a `PD` measure
  (it is `kern`, `JATransfer.kern_PD`), with explicit coefficient `q_p ∑_{x<q_p} f_p(x) f_p(x+h)` (`coef_cos`);
* `alpha_le`: `α_p(h) ≤ (L - h)/q_p ∑_{x<q_p} f_p(x) f_p(x+h)` for `L ≥ X + 1 + q_p` (incomplete periods);
* `total_ge`: `∑_{x ≤ X} f_p(x) ≥ (X + 1 - q_p)/q_p ∑_{x<q_p} f_p(x)` (complete periods);
* `energy_le_psi`: `E ≤ (q_2 q_3)^{-2} ∑_x ν(x) Ψ_L(x)` with `ν = |f̂_3|^2 * |f̂_2|^2` on `ZMod N`;
* `energy_le_arc`: `E ≤ 3 L^3 ν(arc (m-1)) / (q_2 q_3)^2` (via `JABlocks.spectral_window`);
* `energy_normalized`: `E ≤ K (T_2 T_3)^2` with `T_p = ∑_{x ≤ X} f_p(x)` and
  `K = 3 L^3 ν(arc(m-1)) / ((X+1-q_2)^2 (X+1-q_3)^2 (S_2 S_3)^2)`, `S_p = ∑_{x<q_p} f_p(x)`.

Not checked here: the exact identity `∑_d R(d)^2 = E` between the representation-function energy and `E` (done in
`JAEnergyIdentity`), the expectation over the random translations, and the uniform central bound for `ν`.
-/

namespace LeanCheck
namespace JAEnergyLink

open Finset JALocalize JABlocks JATransfer

/-! ### Periodic sums -/

lemma per_iter (g : ℕ → ℝ) (q : ℕ) (hper : ∀ x, g (x + q) = g x) (n x : ℕ) :
    g (n * q + x) = g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (n + 1) * q + x = (n * q + x) + q := by ring
    rw [this, hper, ih]

lemma sum_blocks (g : ℕ → ℝ) (q : ℕ) (hper : ∀ x, g (x + q) = g x) (n : ℕ) :
    ∑ x ∈ range (n * q), g x = n * ∑ x ∈ range q, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih]
    have : ∑ x ∈ range q, g (n * q + x) = ∑ x ∈ range q, g x :=
      Finset.sum_congr rfl (fun x _ => per_iter g q hper n x)
    rw [this]
    push_cast
    ring

lemma sum_range_le (g : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (hg0 : ∀ x, 0 ≤ g x)
    (hper : ∀ x, g (x + q) = g x) (M : ℕ) :
    ∑ x ∈ range M, g x ≤ ((M : ℝ) + q) / q * ∑ x ∈ range q, g x := by
  have hS : 0 ≤ ∑ x ∈ range q, g x := Finset.sum_nonneg (fun x _ => hg0 x)
  have h1 : M / q * q ≤ M := Nat.div_mul_le_self M q
  have h2 : M < M / q * q + q := Nat.lt_div_mul_add hq
  set n := M / q + 1 with hn
  have hnq : n * q = M / q * q + q := by rw [hn, add_mul, one_mul]
  have hMq : M ≤ n * q := by omega
  have hsub : range M ⊆ range (n * q) := Finset.range_subset_range.mpr hMq
  calc ∑ x ∈ range M, g x ≤ ∑ x ∈ range (n * q), g x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)
    _ = n * ∑ x ∈ range q, g x := sum_blocks g q hper n
    _ ≤ ((M : ℝ) + q) / q * ∑ x ∈ range q, g x := by
        apply mul_le_mul_of_nonneg_right _ hS
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
        rw [le_div_iff₀ hq0]
        have : n * q ≤ M + q := by omega
        exact_mod_cast this

lemma sum_range_ge (g : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (hg0 : ∀ x, 0 ≤ g x)
    (hper : ∀ x, g (x + q) = g x) (M : ℕ) :
    ((M : ℝ) - q) / q * ∑ x ∈ range q, g x ≤ ∑ x ∈ range M, g x := by
  have hS : 0 ≤ ∑ x ∈ range q, g x := Finset.sum_nonneg (fun x _ => hg0 x)
  have h1 : M / q * q ≤ M := Nat.div_mul_le_self M q
  have h2 : M < M / q * q + q := Nat.lt_div_mul_add hq
  set n := M / q with hn
  have hsub : range (n * q) ⊆ range M := Finset.range_subset_range.mpr h1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc ((M : ℝ) - q) / q * ∑ x ∈ range q, g x ≤ n * ∑ x ∈ range q, g x := by
        apply mul_le_mul_of_nonneg_right _ hS
        rw [div_le_iff₀ hq0]
        have : (M : ℝ) < n * q + q := by exact_mod_cast h2
        linarith
    _ = ∑ x ∈ range (n * q), g x := (sum_blocks g q hper n).symm
    _ ≤ ∑ x ∈ range M, g x := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)

/-- Restricted autocorrelation is bounded by the period autocorrelation times the number of periods. -/
lemma alpha_le (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (hf0 : ∀ x, 0 ≤ f x) (hper : ∀ x, f (x + q) = f x)
    (X h : ℕ) (hh : h ≤ X) :
    ∑ x ∈ range (X + 1 - h), f x * f (x + h) ≤
      ((X : ℝ) + 1 - h + q) / q * ∑ x ∈ range q, f x * f (x + h) := by
  have := sum_range_le (fun x => f x * f (x + h)) q hq (fun x => mul_nonneg (hf0 x) (hf0 _))
    (fun x => by
      show f (x + q) * f (x + q + h) = f x * f (x + h)
      rw [hper x, show x + q + h = (x + h) + q by ring, hper (x + h)]) (X + 1 - h)
  have hc : ((X + 1 - h : ℕ) : ℝ) = (X : ℝ) + 1 - h := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at this
  exact this

lemma total_ge (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (hf0 : ∀ x, 0 ≤ f x) (hper : ∀ x, f (x + q) = f x)
    (X : ℕ) :
    (((X : ℝ) + 1) - q) / q * ∑ x ∈ range q, f x ≤ ∑ x ∈ range (X + 1), f x := by
  have := sum_range_ge f q hq hf0 hper (X + 1)
  push_cast at this
  exact this


/-! ### Periodic weights from `ZMod q` and the Fourier coefficients of their spectral measures -/

section fourier

variable {q : ℕ} [NeZero q]

/-- The `ℕ`-indexed periodic weight attached to `fz : ZMod q → ℝ`. -/
def fn (fz : ZMod q → ℝ) (x : ℕ) : ℝ := fz (x : ZMod q)

lemma fn_per (fz : ZMod q → ℝ) (x : ℕ) : fn fz (x + q) = fn fz x := by
  unfold fn
  push_cast
  rw [ZMod.natCast_self, add_zero]

/-- Autocorrelation over one period. -/
def pi (fz : ZMod q → ℝ) (h : ℕ) : ℝ := ∑ x ∈ range q, fn fz x * fn fz (x + h)

lemma pi_nonneg (fz : ZMod q → ℝ) (hf : ∀ y, 0 ≤ fz y) (h : ℕ) : 0 ≤ pi fz h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hf _) (hf _))

lemma sum_zmod (u : ZMod q → ℝ) : ∑ y : ZMod q, u y = ∑ x ∈ range q, u (x : ZMod q) := by
  symm
  refine Finset.sum_bij (fun x _ => (x : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb h
    rw [Finset.mem_range] at ha hb
    exact cast_inj_lt (N := q) (m := q) le_rfl ha hb h
  · intro y _
    exact ⟨y.val, Finset.mem_range.mpr (ZMod.val_lt y), ZMod.natCast_zmod_val y⟩

lemma acorr_cast (fz : ZMod q → ℝ) (h : ℕ) : acorr fz (h : ZMod q) = pi fz h := by
  unfold acorr pi
  rw [sum_zmod]
  apply Finset.sum_congr rfl
  intro x _
  unfold fn
  push_cast
  rfl

lemma val_cast_mod {N d : ℕ} [NeZero N] (hN : N = q * d) (h : ℕ) :
    (((h : ZMod N).val : ℕ) : ZMod q) = (h : ZMod q) := by
  rw [ZMod.val_natCast]
  have hN0 : ((N : ℕ) : ZMod q) = 0 := by
    rw [hN]; push_cast; simp [ZMod.natCast_self]
  conv_rhs => rw [← Nat.mod_add_div h N]
  push_cast
  rw [hN0]
  simp

/-- The Fourier coefficient of the kernel (spectral) measure at the integer `h`. -/
lemma coef_pi {N d : ℕ} [NeZero N] (hN : N = q * d) (fz : ZMod q → ℝ) (h : ℕ) :
    ∑ y : ZMod N, (kern N q d fz y : ℂ) * ZMod.stdAddChar ((h : ZMod N) * y) =
      (((q : ℝ) * pi fz h : ℝ) : ℂ) := by
  rw [kern_coef hN, val_cast_mod hN, acorr_cast]

end fourier

/-! ### The weighted energy and the spectral window -/

section energy

variable {q₂ q₃ N d₂ d₃ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero N]

/-- Restricted autocorrelation (pairs `x, x + h` in `[0, X]`). -/
def alpha {q : ℕ} [NeZero q] (fz : ZMod q → ℝ) (X h : ℕ) : ℝ :=
  ∑ x ∈ range (X + 1 - h), fn fz x * fn fz (x + h)

/-- The weighted collision energy `E = ∑_h α_3(h) α_2(h)`, written with the symmetry `α(-h) = α(h)`. -/
def energyE (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (X : ℕ) : ℝ :=
  alpha f₃ X 0 * alpha f₂ X 0 + 2 * ∑ h ∈ Ico 1 (X + 1), alpha f₃ X h * alpha f₂ X h

/-- The spectral measure `ν = |f̂_2|^2 * |f̂_3|^2` on `ZMod N`. -/
noncomputable def nuM (N q₂ q₃ d₂ d₃ : ℕ) [NeZero N] [NeZero q₂] [NeZero q₃]
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) : ZMod N → ℝ :=
  conv (kern N q₂ d₂ f₂) (kern N q₃ d₃ f₃)

lemma nuM_PD (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) : PD (nuM N q₂ q₃ d₂ d₃ f₂ f₃) :=
  (kern_PD hN₂ f₂ hf₂).conv (kern_PD hN₃ f₃ hf₃)

/-- Cosine coefficients of `ν`: the product of the two period autocorrelations. -/
lemma nu_cos (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (h : ℕ) :
    ∑ x, nuM N q₂ q₃ d₂ d₃ f₂ f₃ x * Real.cos (h * ang N x) =
      ((q₂ : ℝ) * pi f₂ h) * ((q₃ : ℝ) * pi f₃ h) := by
  have h1 := fourier_conv (kern N q₂ d₂ f₂) (kern N q₃ d₃ f₃) (h : ZMod N)
  rw [coef_pi hN₂, coef_pi hN₃] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re] at h2
  rw [← h2]
  apply Finset.sum_congr rfl
  intro x _
  unfold nuM
  rw [Complex.re_ofReal_mul, stdAddChar_re]

lemma alpha_le_pi (f : ZMod q₂ → ℝ) (hf : ∀ y, 0 ≤ f y) (X h : ℕ) (hh : h ≤ X) :
    alpha f X h ≤ ((X : ℝ) + 1 - h + q₂) / q₂ * pi f h := by
  unfold alpha pi
  exact alpha_le (fn f) q₂ (Nat.pos_of_ne_zero (NeZero.ne q₂)) (fun x => hf _) (fn_per f) X h hh

lemma alpha_nonneg {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (hf : ∀ y, 0 ≤ f y) (X h : ℕ) :
    0 ≤ alpha f X h := Finset.sum_nonneg (fun x _ => mul_nonneg (hf _) (hf _))

/-- **The weighted energy is bounded by the spectral window.** -/
theorem energy_le_psi (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (X : ℕ) :
    energyE f₂ f₃ X ≤ 1 / ((q₂ : ℝ) * q₃) ^ 2 *
      ∑ x, nuM N q₂ q₃ d₂ d₃ f₂ f₃ x * JASpectral.Psi (X + 1 + q₂ + q₃) (ang N x) := by
  set L : ℕ := X + 1 + q₂ + q₃ with hL
  have hq₂ : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
  have hq₃ : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
  set c : ℕ → ℝ := fun h => ((q₂ : ℝ) * pi f₂ h) * ((q₃ : ℝ) * pi f₃ h) with hc
  have hc0 : ∀ h, 0 ≤ c h := fun h =>
    mul_nonneg (mul_nonneg hq₂.le (pi_nonneg f₂ hf₂ h)) (mul_nonneg hq₃.le (pi_nonneg f₃ hf₃ h))
  -- expansion of the spectral sum
  have hexp : ∑ x, nuM N q₂ q₃ d₂ d₃ f₂ f₃ x * JASpectral.Psi L (ang N x) =
      (L : ℝ) ^ 2 * c 0 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * c h := by
    unfold JASpectral.Psi
    rw [JASpectral.expand_sum Finset.univ (nuM N q₂ q₃ d₂ d₃ f₂ f₃) (ang N) L
      (fun h => ((L : ℝ) - h) ^ 2) ((L : ℝ) ^ 2)]
    have h0 := nu_cos hN₂ hN₃ f₂ f₃ 0
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] at h0
    rw [h0]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    rw [nu_cos hN₂ hN₃ f₂ f₃ h]
  rw [hexp]
  -- termwise bound for h ≤ X
  have hterm : ∀ h : ℕ, h ≤ X → alpha f₃ X h * alpha f₂ X h ≤
      1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) := by
    intro h hh
    have a2 := alpha_le_pi f₂ hf₂ X h hh
    have a3 : alpha f₃ X h ≤ ((X : ℝ) + 1 - h + q₃) / q₃ * pi f₃ h :=
      alpha_le_pi (q₂ := q₃) f₃ hf₃ X h hh
    have hhR : (h : ℝ) ≤ X := by exact_mod_cast hh
    have hLR : (L : ℝ) = X + 1 + q₂ + q₃ := by rw [hL]; push_cast; ring
    have b2 : ((X : ℝ) + 1 - h + q₂) / q₂ * pi f₂ h ≤ ((L : ℝ) - h) / q₂ * pi f₂ h := by
      apply mul_le_mul_of_nonneg_right _ (pi_nonneg f₂ hf₂ h)
      apply div_le_div_of_nonneg_right _ hq₂.le
      rw [hLR]; linarith
    have b3 : ((X : ℝ) + 1 - h + q₃) / q₃ * pi f₃ h ≤ ((L : ℝ) - h) / q₃ * pi f₃ h := by
      apply mul_le_mul_of_nonneg_right _ (pi_nonneg f₃ hf₃ h)
      apply div_le_div_of_nonneg_right _ hq₃.le
      rw [hLR]; linarith
    have hprod : alpha f₃ X h * alpha f₂ X h ≤
        (((L : ℝ) - h) / q₃ * pi f₃ h) * (((L : ℝ) - h) / q₂ * pi f₂ h) :=
      mul_le_mul (a3.trans b3) (a2.trans b2) (alpha_nonneg f₂ hf₂ X h)
        (mul_nonneg (div_nonneg (by rw [hLR]; linarith) hq₃.le) (pi_nonneg f₃ hf₃ h))
    refine hprod.trans (le_of_eq ?_)
    simp only [hc]
    field_simp
  -- assemble
  unfold energyE
  have hs : ∑ h ∈ Ico 1 (X + 1), alpha f₃ X h * alpha f₂ X h ≤
      ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) :=
    Finset.sum_le_sum (fun h hh => hterm h (by rw [Finset.mem_Ico] at hh; omega))
  have hs2 : ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) ≤
      ∑ h ∈ Ico 1 L, 1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      rw [Finset.mem_Ico] at hh ⊢
      omega
    · intro h _ _
      positivity [hc0 h]
  have h0 := hterm 0 (Nat.zero_le X)
  have hs4 : ∑ h ∈ Ico 1 L, 1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) =
      1 / ((q₂ : ℝ) * q₃) ^ 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * c h := by
    rw [Finset.mul_sum]
  rw [Nat.cast_zero, sub_zero] at h0
  have : 1 / ((q₂ : ℝ) * q₃) ^ 2 * ((L : ℝ) ^ 2 * c 0 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * c h) =
      1 / ((q₂ : ℝ) * q₃) ^ 2 * ((L : ℝ) ^ 2 * c 0) +
        2 * (1 / ((q₂ : ℝ) * q₃) ^ 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * c h) := by ring
  rw [this]
  have hs3 : ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃) ^ 2 * (((L : ℝ) - h) ^ 2 * c h) =
      1 / ((q₂ : ℝ) * q₃) ^ 2 * ∑ h ∈ Ico 1 (X + 1), ((L : ℝ) - h) ^ 2 * c h := by
    rw [Finset.mul_sum]
  linarith

/-- **Weighted energy ≤ spectral window at the central arc.** -/
theorem energy_le_arc (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hLm : N ≤ (X + 1 + q₂ + q₃) * m) :
    energyE f₂ f₃ X ≤ 3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 *
      (∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t) / ((q₂ : ℝ) * q₃) ^ 2 := by
  have h1 := energy_le_psi hN₂ hN₃ f₂ f₃ hf₂ hf₃ X
  have h2 := spectral_window (X + 1 + q₂ + q₃) m hm hmN hLm (nuM N q₂ q₃ d₂ d₃ f₂ f₃)
    (nuM_PD hN₂ hN₃ f₂ f₃ hf₂ hf₃).nonneg (nuM_PD hN₂ hN₃ f₂ f₃ hf₂ hf₃).coef
  have hq : (0 : ℝ) < ((q₂ : ℝ) * q₃) ^ 2 := by
    have : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
    have : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
    positivity
  calc energyE f₂ f₃ X ≤ 1 / ((q₂ : ℝ) * q₃) ^ 2 *
        ∑ x, nuM N q₂ q₃ d₂ d₃ f₂ f₃ x * JASpectral.Psi (X + 1 + q₂ + q₃) (ang N x) := h1
    _ ≤ 1 / ((q₂ : ℝ) * q₃) ^ 2 * (3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 *
        ∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

end energy


section normalized

variable {q₂ q₃ N d₂ d₃ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero N]

/-- **Normalized weighted energy.**  With `S_p = ∑_{x<q_p} f_p(x)` (one period) and `T_p = ∑_{x ≤ X} f_p(x)`
(the total weight on `[0, X]`),
`E ≤ K (T_2 T_3)^2` where `K = 3 L^3 ν(arc(m-1)) / ((X+1-q_2)^2 (X+1-q_3)^2 (S_2 S_3)^2)`. -/
theorem energy_normalized (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ)
    (f₃ : ZMod q₃ → ℝ) (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hLm : N ≤ (X + 1 + q₂ + q₃) * m) (hX₂ : q₂ < X + 1) (hX₃ : q₃ < X + 1)
    (hS₂ : 0 < ∑ x ∈ range q₂, fn f₂ x) (hS₃ : 0 < ∑ x ∈ range q₃, fn f₃ x) :
    energyE f₂ f₃ X ≤
      (3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t) /
        ((((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) *
          ((∑ x ∈ range q₂, fn f₂ x) * (∑ x ∈ range q₃, fn f₃ x))) ^ 2)) *
      ((∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x)) ^ 2 := by
  have hE := energy_le_arc hN₂ hN₃ f₂ f₃ hf₂ hf₃ X m hm hmN hLm
  have hq₂ : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
  have hq₃ : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
  set S₂ := ∑ x ∈ range q₂, fn f₂ x with hS₂d
  set S₃ := ∑ x ∈ range q₃, fn f₃ x with hS₃d
  set T₂ := ∑ x ∈ range (X + 1), fn f₂ x with hT₂d
  set T₃ := ∑ x ∈ range (X + 1), fn f₃ x with hT₃d
  set B := ∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun t _ => (nuM_PD hN₂ hN₃ f₂ f₃ hf₂ hf₃).nonneg t)
  have hX₂R : (0 : ℝ) < (X : ℝ) + 1 - q₂ := by
    have : (q₂ : ℝ) < X + 1 := by exact_mod_cast hX₂
    linarith
  have hX₃R : (0 : ℝ) < (X : ℝ) + 1 - q₃ := by
    have : (q₃ : ℝ) < X + 1 := by exact_mod_cast hX₃
    linarith
  have t₂ := total_ge (fn f₂) q₂ (Nat.pos_of_ne_zero (NeZero.ne q₂)) (fun x => hf₂ _) (fn_per f₂) X
  have t₃ := total_ge (fn f₃) q₃ (Nat.pos_of_ne_zero (NeZero.ne q₃)) (fun x => hf₃ _) (fn_per f₃) X
  set P : ℝ := ((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * (S₂ * S₃) / ((q₂ : ℝ) * q₃) with hP
  have hP0 : 0 < P := by positivity
  have hPT : P ≤ T₂ * T₃ := by
    have e : P = (((X : ℝ) + 1 - q₂) / q₂ * S₂) * (((X : ℝ) + 1 - q₃) / q₃ * S₃) := by
      rw [hP]; field_simp
    rw [e]
    exact mul_le_mul t₂ t₃ (by positivity) (le_trans (by positivity) t₂)
  have hPT2 : P ^ 2 ≤ (T₂ * T₃) ^ 2 := pow_le_pow_left₀ hP0.le hPT 2
  have hD : 0 < (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * (S₂ * S₃)) ^ 2 := by positivity
  have hK : 0 ≤ 3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * B /
      (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * (S₂ * S₃)) ^ 2 := by positivity
  have hEq : 3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * B / ((q₂ : ℝ) * q₃) ^ 2 =
      (3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * B /
        (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * (S₂ * S₃)) ^ 2) * P ^ 2 := by
    rw [hP]; field_simp
  calc energyE f₂ f₃ X ≤ 3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * B / ((q₂ : ℝ) * q₃) ^ 2 := hE
    _ = _ := hEq
    _ ≤ _ := mul_le_mul_of_nonneg_left hPT2 hK

end normalized

#print axioms coef_pi
#print axioms nu_cos
#print axioms energy_le_psi
#print axioms energy_le_arc
#print axioms energy_normalized

end JAEnergyLink
end LeanCheck
