import Mathlib
import LeanCheck.JAProduct

/-!
# The central bound, step 2: the arc mass reduction and the merging of the two kernel lists

For two chains `a`, `b` (seeds `sa`, `sb`; windows with positive sums `Z_k = ∑ w_k`) and `2 m ≤ N`:

* `Ftri`: the triangle test function `F = (1/(2m)) acorr(1_{[0,2m)})` on `ZMod N`; `Ftri_zero : F 0 = 1`,
  `Ftri_symm`, `Ftri_ge_half : F ≥ 1/2` on `arc N (m-1)`;
* `arc_mass_le`: for `ν ≥ 0`, `∑_{t ∈ arc N (m-1)} ν t ≤ 2 (ν ∗ F)(0)`;
* `convList_append`, `conv_convList`, `convList_perm`: the convolution of two kernel-list products is the product over the
  merged list, in ANY order (so the kernels of both primes can be sorted by size);
* `normK`: the unit-atom normalization `K = κ / Z^2` (`normK_zero_ge : K(0) ≥ 1`), `Mavg_eq_norm`:
  `Mavg_n(s) = (∏_k Z_{k+1}^2/q_k^2) · (s ∗ K_1 ∗ ⋯ ∗ K_n)`;
* `Hs_pos`: all tails `H_i(0) ≥ 1` (so the hypothesis of `product_identity` holds automatically);
* `arc_mass_product`: **the arc mass of `Mavg_a ∗ Mavg_b` is at most `2 · Sc · S_0 · ∏ f_i`**, where `Sc` is the explicit
  scalar, `S_0 = (μ ∗ H_0)(0)/H_0(0)`, `f_i = H_{i-1}(0)/H_i(0) ` along any order of the merged normalized kernel list.
-/

namespace LeanCheck
namespace JAProduct2

open Finset JATransfer JAMulti JAProduct JALocalize

variable {N : ℕ} [NeZero N]

/-! ### Conventions on convolution -/

lemma conv_smul_right (v t : ZMod N → ℝ) (a : ℝ) (x : ZMod N) :
    conv v (fun y => a * t y) x = a * conv v t x := by
  unfold conv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma conv_comm_ (u v : ZMod N → ℝ) (x : ZMod N) : conv u v x = conv v u x := conv_comm' N u v x

lemma convList_append (s : ZMod N → ℝ) (ks ls : List (ZMod N → ℝ)) :
    convList s (ks ++ ls) = convList (convList s ks) ls := by
  induction ks generalizing s with
  | nil => rfl
  | cons K ks ih => exact ih (conv s K)

lemma conv_convList_left (b : ZMod N → ℝ) (ks : List (ZMod N → ℝ)) :
    ∀ a : ZMod N → ℝ, conv (convList a ks) b = convList (conv a b) ks := by
  induction ks with
  | nil => intro a; rfl
  | cons K ks ih =>
    intro a
    show conv (convList (conv a K) ks) b = convList (conv (conv a b) K) ks
    rw [ih (conv a K)]
    congr 1
    funext x
    rw [conv_assoc, conv_assoc]
    congr 1
    funext y
    exact conv_comm_ K b y

lemma conv_convList (a : ZMod N → ℝ) (ks : List (ZMod N → ℝ)) (b : ZMod N → ℝ) (ls : List (ZMod N → ℝ)) :
    conv (convList a ks) (convList b ls) = convList (convList (conv a b) ks) ls := by
  induction ls generalizing b with
  | nil =>
    show conv (convList a ks) b = convList (convList (conv a b) ks) []
    exact conv_convList_left b ks a
  | cons L ls ih =>
    show conv (convList a ks) (convList (conv b L) ls) = convList (convList (conv a b) ks) (L :: ls)
    rw [ih (conv b L)]
    show convList (convList (conv a (conv b L)) ks) ls = convList (conv (convList (conv a b) ks) L) ls
    congr 1
    rw [conv_convList_left L ks (conv a b)]
    congr 1
    funext x
    rw [conv_assoc]

lemma convList_perm {ks ks' : List (ZMod N → ℝ)} (h : ks.Perm ks') :
    ∀ s : ZMod N → ℝ, convList s ks = convList s ks' := by
  induction h with
  | nil => intro s; rfl
  | cons K _ ih => intro s; exact ih (conv s K)
  | swap K L ks =>
    intro s
    show convList (conv (conv s L) K) ks = convList (conv (conv s K) L) ks
    congr 1
    funext x
    rw [conv_assoc, conv_assoc]
    congr 1
    funext y
    exact conv_comm_ L K y
  | trans _ _ ih1 ih2 => intro s; exact (ih1 s).trans (ih2 s)

/-! ### The triangle test function and the arc mass -/

/-- The triangle test function `(1/(2m)) acorr(1_{[0,2m)})`. -/
noncomputable def Ftri (N m : ℕ) [NeZero N] : ZMod N → ℝ := fun t => acorr (win N (2 * m)) t / (2 * m : ℝ)

lemma Ftri_nonneg (m : ℕ) (t : ZMod N) : 0 ≤ Ftri N m t :=
  div_nonneg (acorr_nonneg _ _) (by positivity)

lemma Ftri_symm (m : ℕ) (t : ZMod N) : Ftri N m (-t) = Ftri N m t := by
  unfold Ftri acorr
  congr 1
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ (fun x => ?_)
  simp only [Equiv.subRight_apply]
  rw [sub_add_cancel, mul_comm, ← sub_eq_add_neg]

lemma Ftri_ge_half (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) (t : ZMod N) (ht : t ∈ arc N (m - 1)) :
    1 / 2 ≤ Ftri N m t := by
  have h := acorr_ge_arc (2 * m) (m - 1) h2m (by omega) t ht
  have hc : ((2 * m - (m - 1) : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; rw [Nat.cast_sub hm]; push_cast; ring
  rw [hc] at h
  unfold Ftri
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma Ftri_zero (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) : Ftri N m 0 = 1 := by
  have h0 : (0 : ZMod N) ∈ arc N 0 := by
    unfold arc
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩)
  have h1 := acorr_ge_arc (2 * m) 0 h2m (Nat.zero_le _) 0 h0
  have h2 := acorr_le (N := N) (2 * m) 0
  simp only [Nat.sub_zero] at h1
  have hm2 : (0 : ℝ) < 2 * m := by positivity
  unfold Ftri
  have : acorr (win N (2 * m)) 0 = ((2 * m : ℕ) : ℝ) := le_antisymm h2 h1
  rw [this]
  push_cast
  field_simp

/-- **The arc mass is at most twice the integral of the triangle.** -/
lemma arc_mass_le (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) (ν : ZMod N → ℝ) (hν : ∀ x, 0 ≤ ν x) :
    ∑ t ∈ arc N (m - 1), ν t ≤ 2 * conv ν (Ftri N m) 0 := by
  classical
  have e : conv ν (Ftri N m) 0 = ∑ y, ν y * Ftri N m y := by
    unfold conv
    apply Finset.sum_congr rfl
    intro y _
    rw [zero_sub, Ftri_symm]
  rw [e]
  have h1 : ∑ y ∈ arc N (m - 1), ν y * (1 / 2) ≤ ∑ y ∈ arc N (m - 1), ν y * Ftri N m y :=
    Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (Ftri_ge_half m hm h2m y hy) (hν y))
  have h2 : ∑ y ∈ arc N (m - 1), ν y * Ftri N m y ≤ ∑ y, ν y * Ftri N m y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => mul_nonneg (hν y) (Ftri_nonneg m y))
  rw [← Finset.sum_mul] at h1
  linarith

/-! ### Unit-atom normalization of the kernels -/

/-- The unit-atom normalization `K = κ / Z^2`, `Z = ∑ w`. -/
noncomputable def normK (N : ℕ) [NeZero N] (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) : ZMod N → ℝ :=
  fun x => (1 / (∑ y, w y) ^ 2) * kernq N Q w x

lemma normK_nonneg (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (x : ZMod N) : 0 ≤ normK N Q w x :=
  mul_nonneg (by positivity) (JAFinal.kern_nonneg' Q (N / Q) w x)

lemma normK_zero_ge (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (hZ : 0 < ∑ y, w y) : 1 ≤ normK N Q w 0 := by
  have h := JAFinal.kern_zero_ge (N := N) Q (N / Q) w
  unfold normK kernq
  have hz : 0 < (∑ y, w y) ^ 2 := by positivity
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hz]
  linarith

lemma kernq_eq_scale (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (hZ : 0 < ∑ y, w y) :
    kernq N Q w = fun x => (∑ y, w y) ^ 2 * normK N Q w x := by
  funext x
  unfold normK
  field_simp

/-- The normalized kernel measures of levels `1, …, n`. -/
noncomputable def normKernList (N : ℕ) [NeZero N] (c : Chain) (n : ℕ) : List (ZMod N → ℝ) :=
  (List.range n).map (fun k => normK N (c.q (k + 1)) (c.w (k + 1)))

lemma convList_range_scale :
    ∀ (n : ℕ) (c : ℕ → ℝ) (f g : ℕ → (ZMod N → ℝ)), (∀ k, f k = fun x => c k * g k x) →
      ∀ s : ZMod N → ℝ, convList s ((List.range n).map f) =
        fun x => (∏ k ∈ range n, c k) * convList s ((List.range n).map g) x := by
  intro n
  induction n with
  | zero => intro c f g _ s; funext x; simp [convList]
  | succ n ih =>
    intro c f g hfg s
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    show convList (conv s (f 0)) (List.map (f ∘ Nat.succ) (List.range n)) =
      fun x => (∏ k ∈ range (n + 1), c k) *
        convList (conv s (g 0)) (List.map (g ∘ Nat.succ) (List.range n)) x
    have h1 : conv s (f 0) = fun x => c 0 * conv s (g 0) x := by
      rw [hfg 0]
      funext x
      exact conv_smul_right s (g 0) (c 0) x
    rw [h1, convList_smul, ih (fun k => c (k + 1)) (f ∘ Nat.succ) (g ∘ Nat.succ) (fun k => hfg (k + 1))]
    funext x
    rw [Finset.prod_range_succ']
    ring

lemma convList_kern_norm (c : Chain) (n : ℕ) (hZ : ∀ k, 0 < ∑ y, c.w (k + 1) y) (s : ZMod N → ℝ) :
    convList s (kernList N c n) =
      fun x => (∏ k ∈ range n, (∑ y, c.w (k + 1) y) ^ 2) * convList s (normKernList N c n) x :=
  convList_range_scale n (fun k => (∑ y, c.w (k + 1) y) ^ 2) _ _
    (fun k => kernq_eq_scale (c.q (k + 1)) (c.w (k + 1)) (hZ k)) s

/-- **`Mavg` as a scalar times a product of unit-atom kernels.** -/
theorem Mavg_eq_norm (c : Chain) (n : ℕ) (hZ : ∀ k, 0 < ∑ y, c.w (k + 1) y) (s : ZMod N → ℝ) :
    Mavg N n c s = fun x => (∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2)) *
      convList s (normKernList N c n) x := by
  rw [Mavg_eq_convList, convList_kern_norm c n hZ]
  funext x
  rw [← mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  ring

/-! ### Nonnegativity and the tails -/

lemma convList_nonneg (ks : List (ZMod N → ℝ)) (hks : ∀ K ∈ ks, ∀ x, 0 ≤ K x) :
    ∀ s : ZMod N → ℝ, (∀ x, 0 ≤ s x) → ∀ x, 0 ≤ convList s ks x := by
  induction ks with
  | nil => intro s hs; exact hs
  | cons K ks ih =>
    intro s hs
    exact ih (fun K' hK' => hks K' (List.mem_cons_of_mem _ hK')) (conv s K)
      (JAFinal.conv_nonneg' _ _ hs (hks K (List.mem_cons_self)))

lemma Hs_atom (F : ZMod N → ℝ) (hF : ∀ x, 0 ≤ F x) (hF0 : 1 ≤ F 0) :
    ∀ ks : List (ZMod N → ℝ), (∀ K ∈ ks, (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0) →
      (∀ x, 0 ≤ Hs F ks x) ∧ 1 ≤ Hs F ks 0 := by
  intro ks
  induction ks with
  | nil => intro _; exact ⟨hF, hF0⟩
  | cons K ks ih =>
    intro hks
    obtain ⟨h1, h2⟩ := ih (fun K' hK' => hks K' (List.mem_cons_of_mem _ hK'))
    obtain ⟨hK1, hK2⟩ := hks K (List.mem_cons_self)
    refine ⟨fun x => JAFinal.conv_nonneg' _ _ hK1 h1 x, ?_⟩
    show 1 ≤ conv K (Hs F ks) 0
    calc (1 : ℝ) ≤ K 0 * Hs F ks 0 := by nlinarith
      _ ≤ conv K (Hs F ks) 0 := JAFinal.conv_zero_ge _ _ hK1 h1

/-! ### The arc mass of `Mavg_a ∗ Mavg_b` as a product -/

/-- **Arc mass reduction and kernel merging.**  For nonnegative seed measures `A`, `B` and ANY order `ks'` of the merged
list of normalized kernels, the arc mass is at most `2 · Sc · S_0 · ∏ f_i` with the explicit scalar `Sc`. -/
theorem arc_mass_product (ca cb : Chain) (na nb : ℕ) (hZa : ∀ k, 0 < ∑ y, ca.w (k + 1) y)
    (hZb : ∀ k, 0 < ∑ y, cb.w (k + 1) y) (A B : ZMod N → ℝ) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) (ks' : List (ZMod N → ℝ))
    (hperm : ks'.Perm (normKernList N ca na ++ normKernList N cb nb)) :
    ∑ t ∈ arc N (m - 1), conv (Mavg N na ca A) (Mavg N nb cb B) t ≤
      2 * ((∏ k ∈ range na, ((∑ y, ca.w (k + 1) y) ^ 2 / ((ca.q k : ℕ) : ℝ) ^ 2)) *
          (∏ k ∈ range nb, ((∑ y, cb.w (k + 1) y) ^ 2 / ((cb.q k : ℕ) : ℝ) ^ 2))) *
        ((conv (conv A B) (Hs (Ftri N m) ks') 0 / Hs (Ftri N m) ks' 0) *
          ∏ i ∈ range ks'.length,
            (Hs (Ftri N m) (ks'.drop i) 0 / Hs (Ftri N m) (ks'.drop (i + 1)) 0)) := by
  classical
  set F := Ftri N m with hFdef
  set Sa := ∏ k ∈ range na, ((∑ y, ca.w (k + 1) y) ^ 2 / ((ca.q k : ℕ) : ℝ) ^ 2) with hSa
  set Sb := ∏ k ∈ range nb, ((∑ y, cb.w (k + 1) y) ^ 2 / ((cb.q k : ℕ) : ℝ) ^ 2) with hSb
  have hnormk : ∀ (c : Chain) (n : ℕ), (∀ k, 0 < ∑ y, c.w (k + 1) y) →
      ∀ K ∈ normKernList N c n, (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 := by
    intro c n hZ K hK
    unfold normKernList at hK
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hK
    exact ⟨normK_nonneg _ _, normK_zero_ge _ _ (hZ k)⟩
  have hks' : ∀ K ∈ ks', (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 := by
    intro K hK
    rcases List.mem_append.mp (hperm.subset hK) with h | h
    · exact hnormk ca na hZa K h
    · exact hnormk cb nb hZb K h
  have hF0 : F 0 = 1 := Ftri_zero m hm h2m
  have hFnn : ∀ x, 0 ≤ F x := Ftri_nonneg m
  obtain ⟨hHnn, hH1⟩ := Hs_atom F hFnn (by rw [hF0]) ks' hks'
  have hSa0 : 0 ≤ Sa := Finset.prod_nonneg (fun k _ => by positivity)
  have hSb0 : 0 ≤ Sb := Finset.prod_nonneg (fun k _ => by positivity)
  have hν : conv (Mavg N na ca A) (Mavg N nb cb B) =
      fun x => (Sa * Sb) * convList (conv A B) ks' x := by
    rw [Mavg_eq_norm ca na hZa, Mavg_eq_norm cb nb hZb]
    funext x
    rw [JARealization.conv_smul]
    rw [conv_convList, ← convList_append, convList_perm hperm.symm]
  have hksnn : ∀ K ∈ ks', ∀ x, 0 ≤ K x := fun K hK => (hks' K hK).1
  have hconvnn : ∀ x, 0 ≤ convList (conv A B) ks' x :=
    convList_nonneg ks' hksnn _ (fun x => JAFinal.conv_nonneg' _ _ hA hB x)
  have hνnn : ∀ x, 0 ≤ conv (Mavg N na ca A) (Mavg N nb cb B) x := by
    intro x
    rw [hν]
    exact mul_nonneg (mul_nonneg hSa0 hSb0) (hconvnn x)
  have h1 := arc_mass_le m hm h2m _ hνnn
  have h2 : conv (conv (Mavg N na ca A) (Mavg N nb cb B)) F 0 =
      (Sa * Sb) * conv (convList (conv A B) ks') F 0 := by
    rw [hν]
    exact conv_smul_left N (Sa * Sb) (convList (conv A B) ks') F 0
  have hpos : ∀ i ≤ ks'.length, 0 < Hs F (ks'.drop i) 0 := by
    intro i _
    have := Hs_atom F hFnn (by rw [hF0]) (ks'.drop i) (fun K hK => hks' K (List.mem_of_mem_drop hK))
    linarith [this.2]
  have h3 := product_identity (conv A B) F ks' hpos
  rw [hF0, mul_one] at h3
  calc ∑ t ∈ arc N (m - 1), conv (Mavg N na ca A) (Mavg N nb cb B) t
      ≤ 2 * conv (conv (Mavg N na ca A) (Mavg N nb cb B)) F 0 := h1
    _ = 2 * ((Sa * Sb) * conv (convList (conv A B) ks') F 0) := by rw [h2]
    _ = _ := by rw [h3]; ring

#print axioms arc_mass_le
#print axioms conv_convList
#print axioms convList_perm
#print axioms Mavg_eq_norm
#print axioms arc_mass_product

end JAProduct2
end LeanCheck
