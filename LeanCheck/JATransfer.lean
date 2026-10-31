import Mathlib
import LeanCheck.JABlocks

/-!
# Transfer of the expected spectral measure to `ZMod N` (end of component 16)

In `TVGaddmore_v27` the expected spectral measure is `μ_X = μ_0 * K_{Q_1} * ... * K_{Q_k}` where
`K_Q = ∑_{r mod Q} κ_Q(r) δ_{r/Q}`, `κ_Q(r) = |Ŵ(r)|^2 / (Q m_Q)^2` and `W` is a nonnegative window of period `Q`.
All the measures live on the finite group `(1/N)ℤ/ℤ ≅ ZMod N` once every `Q_i` divides `N`.

Checked here (no axiom, no `sorry`):

* `PD ν`: `ν ≥ 0` and every Fourier coefficient `∑_x ν(x) e(s x)` is a real number `≥ 0` (the hypothesis of
  `JABlocks.spectral_window`);
* `PD.conv`: `PD` is preserved by convolution (the Fourier transform is multiplicative);
* `kern_PD`: the kernel measure `K_w(y) = ∑_{r : ZMod Q} |Ŵ(r)|^2 [y = r·(N/Q)]` of any nonnegative window `w` on
  `ZMod Q`, `Q ∣ N`, is `PD` (its Fourier coefficient at `s` is `Q ∑_x w(x) w(x+s)`, by the autocorrelation identity);
  positive multiples (the normalization `1/(Q m_Q)^2`) preserve `PD` (`PD.smul`);
* `spectral_window_conv`: for a `PD` seed and a list of `PD` factors, `ν = seed * K_1 * ... * K_k` satisfies the
  spectral window bound `∑ ν Ψ_L ≤ 3 L^3 ν(arc (m-1))`, uniformly in the number of factors.

Not checked here: that the seed measure of the construction is `PD`, and the passage from this bound to the weighted
energy (`lem:weighted-spectral`).
-/

namespace LeanCheck
namespace JATransfer

open Finset JALocalize JABlocks

variable {N : ℕ} [NeZero N]

/-- A nonnegative function on `ZMod N` all of whose Fourier coefficients are real and nonnegative. -/
structure PD (ν : ZMod N → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  coef : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ)

/-- Convolution on `ZMod N`. -/
def conv (ν₁ ν₂ : ZMod N → ℝ) (x : ZMod N) : ℝ := ∑ y, ν₁ y * ν₂ (x - y)

lemma fourier_conv (ν₁ ν₂ : ZMod N → ℝ) (s : ZMod N) :
    ∑ x, (conv ν₁ ν₂ x : ℂ) * ZMod.stdAddChar (s * x) =
      (∑ y, (ν₁ y : ℂ) * ZMod.stdAddChar (s * y)) * (∑ z, (ν₂ z : ℂ) * ZMod.stdAddChar (s * z)) := by
  unfold conv
  rw [Finset.sum_mul_sum]
  have h1 : ∀ x : ZMod N, ((∑ y, ν₁ y * ν₂ (x - y) : ℝ) : ℂ) * ZMod.stdAddChar (s * x) =
      ∑ y, ((ν₁ y : ℂ) * (ν₂ (x - y) : ℂ)) * ZMod.stdAddChar (s * x) := by
    intro x
    push_cast
    rw [Finset.sum_mul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Equiv.sum_comp (Equiv.addLeft y)]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  have : (ZMod.stdAddChar (s * (y + z)) : ℂ) =
      ZMod.stdAddChar (s * y) * ZMod.stdAddChar (s * z) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [this]
  ring

lemma PD.conv {ν₁ ν₂ : ZMod N → ℝ} (h₁ : PD ν₁) (h₂ : PD ν₂) : PD (conv ν₁ ν₂) := by
  refine ⟨fun x => Finset.sum_nonneg (fun y _ => mul_nonneg (h₁.nonneg y) (h₂.nonneg _)), fun s => ?_⟩
  obtain ⟨c₁, hc₁, e₁⟩ := h₁.coef s
  obtain ⟨c₂, hc₂, e₂⟩ := h₂.coef s
  refine ⟨c₁ * c₂, mul_nonneg hc₁ hc₂, ?_⟩
  rw [fourier_conv, e₁, e₂]
  push_cast
  ring

lemma PD.smul {ν : ZMod N → ℝ} (h : PD ν) {a : ℝ} (ha : 0 ≤ a) : PD (fun x => a * ν x) := by
  refine ⟨fun x => mul_nonneg ha (h.nonneg x), fun s => ?_⟩
  obtain ⟨c, hc, e⟩ := h.coef s
  refine ⟨a * c, mul_nonneg ha hc, ?_⟩
  have : ∑ x, ((a * ν x : ℝ) : ℂ) * ZMod.stdAddChar (s * x) =
      (a : ℂ) * ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring
  rw [this, e]
  push_cast
  ring

/-- Iterated convolution against a list of factors. -/
def convList (seed : ZMod N → ℝ) : List (ZMod N → ℝ) → (ZMod N → ℝ)
  | [] => seed
  | κ :: ks => convList (conv seed κ) ks

lemma PD.convList {seed : ZMod N → ℝ} (hs : PD seed) :
    ∀ ks : List (ZMod N → ℝ), (∀ κ ∈ ks, PD κ) → PD (convList seed ks)
  | [], _ => hs
  | κ :: ks, h => PD.convList (hs.conv (h κ (by simp))) ks (fun k hk => h k (by simp [hk]))

/-! ### The kernel measure -/

/-- The kernel measure `K_w(y) = ∑_{r : ZMod Q} |Ŵ(r)|^2 [y = r (N/Q)]` on `ZMod N`, where `N = Q d`. -/
noncomputable def kern (N Q d : ℕ) [NeZero N] [NeZero Q] (w : ZMod Q → ℝ) (y : ZMod N) : ℝ :=
  ∑ r : ZMod Q, if y = ((r.val * d : ℕ) : ZMod N) then
    ‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 else 0

lemma std_compat {Q d : ℕ} [NeZero Q] [NeZero N] (hN : N = Q * d) (s : ZMod N) (r : ZMod Q) :
    (ZMod.stdAddChar (s * ((r.val * d : ℕ) : ZMod N)) : ℂ) =
      ZMod.stdAddChar (((s.val : ℕ) : ZMod Q) * r) := by
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hd : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by
      rintro rfl
      simp at hN
      exact NeZero.ne N hN
    exact_mod_cast this
  have e1 : s * ((r.val * d : ℕ) : ZMod N) = (((s.val * r.val * d : ℕ) : ℤ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val s]
    simp
    ring
  have e2 : ((s.val : ℕ) : ZMod Q) * r = (((s.val * r.val : ℕ) : ℤ) : ZMod Q) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val r]
    simp
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hN' : (N : ℂ) = (Q : ℂ) * (d : ℂ) := by exact_mod_cast hN
  rw [hN']
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp

/-- **Exact Fourier coefficient of the kernel measure**: at `s` it equals `Q ∑_x w(x) w(x + s mod Q)`. -/
lemma kern_coef {Q d : ℕ} [NeZero Q] (hN : N = Q * d) (w : ZMod Q → ℝ) (s : ZMod N) :
    ∑ y : ZMod N, (kern N Q d w y : ℂ) * ZMod.stdAddChar (s * y) =
      (((Q : ℝ) * acorr w ((s.val : ℕ) : ZMod Q) : ℝ) : ℂ) := by
  classical
  set t : ZMod Q := ((s.val : ℕ) : ZMod Q) with ht
  have h1 : ∑ y : ZMod N, (kern N Q d w y : ℂ) * ZMod.stdAddChar (s * y) =
      ∑ r : ZMod Q, ((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 : ℝ) : ℂ) *
        ZMod.stdAddChar (s * ((r.val * d : ℕ) : ZMod N)) := by
    have hk : ∀ y : ZMod N, (kern N Q d w y : ℂ) =
        ∑ r : ZMod Q, if y = ((r.val * d : ℕ) : ZMod N) then
          ((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 : ℝ) : ℂ) else 0 := by
      intro y
      unfold kern
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    simp_rw [hk, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_eq_single (((r.val * d : ℕ) : ZMod N))]
    · rw [if_pos rfl]
    · intro y _ hy
      rw [if_neg hy, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have h2 : ∀ r : ZMod Q, ((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 : ℝ) : ℂ) *
        ZMod.stdAddChar (s * ((r.val * d : ℕ) : ZMod N)) =
      ((∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) *
        (∑ z, (w z : ℂ) * ZMod.stdAddChar (-(r * z)))) * ZMod.stdAddChar (r * t) := by
    intro r
    rw [← coef_mul_conj w r, std_compat hN s r, mul_comm t r]
  simp_rw [h2]
  rw [← acorr_eq w t]
  push_cast
  rfl

lemma kern_PD {Q d : ℕ} [NeZero Q] (hN : N = Q * d) (w : ZMod Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    PD (kern N Q d w) := by
  classical
  refine ⟨fun x => Finset.sum_nonneg (fun r _ => by split_ifs <;> positivity), fun s => ?_⟩
  exact ⟨(Q : ℝ) * acorr w ((s.val : ℕ) : ZMod Q), mul_nonneg (Nat.cast_nonneg Q)
    (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (hw _))), kern_coef hN w s⟩

/-- **The expected spectral measure satisfies the spectral window bound**, for any number of kernel factors. -/
theorem spectral_window_conv (seed : ZMod N → ℝ) (hseed : PD seed) (ks : List (ZMod N → ℝ))
    (hks : ∀ κ ∈ ks, PD κ) (L m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ L * m) :
    ∑ x, convList seed ks x * JASpectral.Psi L (ang N x) ≤
      3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1), convList seed ks t := by
  have h := PD.convList hseed ks hks
  exact spectral_window L m hm hmN hLm _ h.nonneg h.coef

#print axioms fourier_conv
#print axioms PD.conv
#print axioms kern_coef
#print axioms kern_PD
#print axioms spectral_window_conv

end JATransfer
end LeanCheck
