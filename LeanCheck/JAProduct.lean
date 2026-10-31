import Mathlib
import LeanCheck.JAMulti2

/-!
# The central bound, step 1: `Mavg` is a scalar times an iterated convolution, and the exact product identity

`CentralBound` (component 13) is the uniform bound of `(Mavg_a ∗ Mavg_b)(arc(m-1))`.  The paper proves it through the
**product identity** `∫ F dμ_X = S_0 ∏ f_i`.  This file formalizes the exact algebraic part on `ZMod N`:

* `conv_assoc`, `convList_smul`;
* `kernList`, `Mavg_eq_convList`: `Mavg_n(s) = (∏_{k<n} q_k^{-2}) · (s ∗ κ_1 ∗ ⋯ ∗ κ_n)` with `κ_k = kernq(q_k, w_k)`;
* `Hs` (the tails `H_i = K_{i+1} ∗ ⋯ ∗ K_L ∗ F`), `conv_convList_right`:
  `((μ ∗ K_1 ∗ ⋯ ∗ K_L) ∗ F)(x) = (μ ∗ H_0)(x)`;
* `Hs_zero_prod`: if all `H_i(0) > 0` then `H_0(0) = F(0) · ∏_i f_i` with `f_i = H_{i-1}(0)/H_i(0)`;
* `product_identity`: `((μ ∗ K_1 ∗ ⋯ ∗ K_L) ∗ F)(0) = S_0 · F(0) · ∏ f_i`, `S_0 = (μ ∗ H_0)(0)/H_0(0)`.

Not done here: the bounds `1 ≤ f_i ≤ B_D`, the far-field estimate, the case analysis and the Matveev input.
-/

namespace LeanCheck
namespace JAProduct

open Finset JATransfer JAMulti

variable {N : ℕ} [NeZero N]

lemma conv_assoc (a b c : ZMod N → ℝ) (x : ZMod N) :
    conv (conv a b) c x = conv a (conv b c) x := by
  calc conv (conv a b) c x = ∑ y, ∑ z, a z * b (y - z) * c (x - y) := by
        unfold conv
        simp_rw [Finset.sum_mul]
    _ = ∑ z, ∑ y, a z * b (y - z) * c (x - y) := Finset.sum_comm
    _ = conv a (conv b c) x := by
        unfold conv
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        refine Fintype.sum_equiv (Equiv.subRight z) _ _ (fun y => ?_)
        simp only [Equiv.subRight_apply]
        have : x - z - (y - z) = x - y := by ring
        rw [this]
        ring

lemma convList_smul (ks : List (ZMod N → ℝ)) :
    ∀ (a : ℝ) (t : ZMod N → ℝ), convList (fun x => a * t x) ks = fun x => a * convList t ks x := by
  induction ks with
  | nil => intro a t; rfl
  | cons κ ks ih =>
    intro a t
    show convList (conv (fun x => a * t x) κ) ks = _
    have h : conv (fun x => a * t x) κ = fun x => a * conv t κ x := funext (fun x => conv_smul_left N a t κ x)
    rw [h, ih]
    rfl

/-- The kernel measures of levels `1, …, n`. -/
noncomputable def kernList (N : ℕ) [NeZero N] (c : Chain) (n : ℕ) : List (ZMod N → ℝ) :=
  (List.range n).map (fun k => kernq N (c.q (k + 1)) (c.w (k + 1)))

lemma kernList_succ (c : Chain) (n : ℕ) :
    kernList N c (n + 1) = kernq N (c.q 1) (c.w 1) :: kernList N c.tail n := by
  unfold kernList
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- **`Mavg` as an iterated convolution.** -/
theorem Mavg_eq_convList :
    ∀ (n : ℕ) (c : Chain) (s : ZMod N → ℝ),
      Mavg N n c s = fun x => (∏ k ∈ range n, 1 / ((c.q k : ℕ) : ℝ) ^ 2) * convList s (kernList N c n) x := by
  intro n
  induction n with
  | zero =>
    intro c s
    funext x
    simp [Mavg, kernList, convList]
  | succ n ih =>
    intro c s
    simp only [Mavg]
    rw [ih c.tail]
    funext x
    rw [convList_smul]
    rw [Finset.prod_range_succ', kernList_succ]
    show (∏ k ∈ range n, 1 / ((c.tail.q k : ℕ) : ℝ) ^ 2) *
        ((1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * convList (conv s (kernq N (c.q 1) (c.w 1))) (kernList N c.tail n) x) =
      ((∏ k ∈ range n, 1 / ((c.q (k + 1) : ℕ) : ℝ) ^ 2) * (1 / ((c.q 0 : ℕ) : ℝ) ^ 2)) *
        convList (conv s (kernq N (c.q 1) (c.w 1))) (kernList N c.tail n) x
    have hq : ∀ k, ((c.tail.q k : ℕ) : ℝ) = ((c.q (k + 1) : ℕ) : ℝ) := fun k => rfl
    simp only [hq]
    ring

/-! ### The tails and the product identity -/

/-- `Hs F [K_{i+1}, …, K_L] = K_{i+1} ∗ ⋯ ∗ K_L ∗ F`. -/
def Hs (F : ZMod N → ℝ) : List (ZMod N → ℝ) → (ZMod N → ℝ)
  | [] => F
  | K :: ks => conv K (Hs F ks)

lemma conv_convList_right (F : ZMod N → ℝ) (ks : List (ZMod N → ℝ)) :
    ∀ (μ : ZMod N → ℝ) (x : ZMod N), conv (convList μ ks) F x = conv μ (Hs F ks) x := by
  induction ks with
  | nil => intro μ x; rfl
  | cons K ks ih =>
    intro μ x
    show conv (convList (conv μ K) ks) F x = conv μ (conv K (Hs F ks)) x
    rw [ih (conv μ K) x, conv_assoc]

/-- Telescoping: `H_0(0) = F(0) ∏ f_i` with `f_i = H_{i-1}(0)/H_i(0)`. -/
lemma Hs_zero_prod (F : ZMod N → ℝ) :
    ∀ (ks : List (ZMod N → ℝ)), (∀ i ≤ ks.length, 0 < Hs F (ks.drop i) 0) →
      Hs F ks 0 = F 0 * ∏ i ∈ range ks.length,
        (Hs F (ks.drop i) 0 / Hs F (ks.drop (i + 1)) 0) := by
  intro ks
  induction ks with
  | nil => intro _; simp [Hs]
  | cons K ks ih =>
    intro hpos
    have hpos' : ∀ i ≤ ks.length, 0 < Hs F (ks.drop i) 0 := by
      intro i hi
      have := hpos (i + 1) (by simp; omega)
      simpa using this
    have h0 : 0 < Hs F ks 0 := by simpa using hpos' 0 (Nat.zero_le _)
    have hK : 0 < Hs F (K :: ks) 0 := by simpa using hpos 0 (Nat.zero_le _)
    rw [List.length_cons, Finset.prod_range_succ']
    have e := ih hpos'
    have key : ∀ P : ℝ, Hs F ks 0 = F 0 * P →
        Hs F (K :: ks) 0 = F 0 * (P * (Hs F (K :: ks) 0 / Hs F ks 0)) := by
      intro P hP
      rw [show F 0 * (P * (Hs F (K :: ks) 0 / Hs F ks 0)) =
        (F 0 * P) * (Hs F (K :: ks) 0 / Hs F ks 0) by ring, ← hP]
      field_simp
    simp only [List.drop_succ_cons, List.drop_zero]
    exact key _ e

/-- **The product identity.** -/
theorem product_identity (μ F : ZMod N → ℝ) (ks : List (ZMod N → ℝ))
    (hpos : ∀ i ≤ ks.length, 0 < Hs F (ks.drop i) 0) :
    conv (convList μ ks) F 0 =
      (conv μ (Hs F ks) 0 / Hs F ks 0) * F 0 * ∏ i ∈ range ks.length,
        (Hs F (ks.drop i) 0 / Hs F (ks.drop (i + 1)) 0) := by
  have h0 : 0 < Hs F ks 0 := by simpa using hpos 0 (Nat.zero_le _)
  rw [conv_convList_right]
  have e := Hs_zero_prod F ks hpos
  rw [mul_assoc, ← e]
  field_simp

#print axioms conv_assoc
#print axioms Mavg_eq_convList
#print axioms conv_convList_right
#print axioms Hs_zero_prod
#print axioms product_identity

end JAProduct
end LeanCheck
