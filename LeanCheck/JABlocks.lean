import Mathlib
import LeanCheck.JALocalize
import LeanCheck.JASpectral

/-!
# Block summation: the spectral window bound on a finite cyclic group (component 16)

Lemma `lem:weighted-spectral` of `TVGaddmore_v27` states `∫ Ψ_L dν ≤ 5 L^3 ν{‖t‖ ≤ 1/L}` for a nonnegative measure
`ν` with nonnegative real Fourier coefficients.  Here it is proved for a measure on `ZMod N` (angle `2π x/N`):

* `fej_far`: the Fejér kernel is at most `N^2 / (4 (r+1)^2)` off the arc `{±k : k ≤ r}`;
* `ann_mass`: each annulus `{±k : j m ≤ k ≤ (j+1) m - 1}` has `ν`-mass at most `4 B`, `B = ν(arc (m-1))`
  (two applications of `JALocalize.loc_mass_half` to each of the two sides);
* `fej_block_sum`: `∑ ν F_L ≤ 3 L^2 B` for `m = ⌈N/L⌉` (central arc contributes `L^2 B`, the blocks `j ≥ 1` contribute
  `L^2 B / j^2` each, and `∑ 1/j^2 ≤ 2`);
* `spectral_window`: `∑ ν Ψ_L ≤ 3 L^3 B`, which is `≤ 5 L^3 ν{‖t‖ ≤ 1/L}` since the arc of radius `m - 1` lies inside
  `‖t‖ < 1/L`.

Not checked here: the transfer from the expected spectral measures of the construction to a measure on `ZMod N` with
nonnegative real coefficients, and the passage to the weighted energy.
-/

namespace LeanCheck
namespace JABlocks

open Finset JALocalize JASpectral Real

variable {N : ℕ} [NeZero N]

/-- The angle `2π x / N` of a point of `ZMod N`. -/
noncomputable def ang (N : ℕ) [NeZero N] (x : ZMod N) : ℝ := 2 * π * (x.val : ℝ) / N

lemma mem_arc_iff {r : ℕ} {x : ZMod N} :
    x ∈ arc N r ↔ ∃ k : ℕ, k ≤ r ∧ (x = (k : ZMod N) ∨ x = -(k : ZMod N)) := by
  classical
  unfold arc
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
    · exact ⟨k, by omega, Or.inl h.symm⟩
    · exact ⟨k, by omega, Or.inr h.symm⟩
  · rintro ⟨k, hk, h | h⟩
    · exact Or.inl ⟨k, by omega, h.symm⟩
    · exact Or.inr ⟨k, by omega, h.symm⟩

lemma arc_neg {r : ℕ} {x : ZMod N} (hx : x ∈ arc N r) : -x ∈ arc N r := by
  rw [mem_arc_iff] at hx ⊢
  obtain ⟨k, hk, h | h⟩ := hx
  · exact ⟨k, hk, Or.inr (by rw [h])⟩
  · exact ⟨k, hk, Or.inl (by rw [h, neg_neg])⟩

lemma val_far {r : ℕ} {x : ZMod N} (hx : x ∉ arc N r) : r + 1 ≤ x.val ∧ r + 1 ≤ N - x.val := by
  have hv : x.val < N := ZMod.val_lt x
  constructor
  · by_contra h
    push Not at h
    apply hx
    rw [mem_arc_iff]
    exact ⟨x.val, by omega, Or.inl (ZMod.natCast_zmod_val x).symm⟩
  · by_contra h
    push Not at h
    apply hx
    rw [mem_arc_iff]
    refine ⟨N - x.val, by omega, Or.inr ?_⟩
    rw [Nat.cast_sub hv.le]
    simp [ZMod.natCast_self, ZMod.natCast_zmod_val]

lemma sin_lower_half {w r : ℕ} (hw : 2 * w ≤ N) (hr : r + 1 ≤ w) :
    2 * ((r : ℝ) + 1) / N ≤ Real.sin (π * w / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h2w : (2 * w : ℝ) ≤ N := by exact_mod_cast hw
  have hmain := Real.mul_le_sin (x := π * w / N) (by positivity) (by
    rw [div_le_iff₀ hN]; nlinarith [Real.pi_pos])
  have e : 2 / π * (π * w / N) = 2 * w / N := by field_simp
  rw [e] at hmain
  have hrw : (r : ℝ) + 1 ≤ w := by exact_mod_cast hr
  calc 2 * ((r : ℝ) + 1) / N ≤ 2 * w / N := by gcongr
    _ ≤ _ := hmain

lemma sin_lower {v r : ℕ} (hvN : v < N) (h1 : r + 1 ≤ v) (h2 : r + 1 ≤ N - v) :
    2 * ((r : ℝ) + 1) / N ≤ Real.sin (π * v / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rcases le_total (2 * v) N with h | h
  · exact sin_lower_half h h1
  · have hw : 2 * (N - v) ≤ N := by omega
    have := sin_lower_half (N := N) hw h2
    have e : π * ((N - v : ℕ) : ℝ) / N = π - π * v / N := by
      rw [Nat.cast_sub hvN.le]; field_simp
    rw [e, Real.sin_pi_sub] at this
    exact this

/-- Pointwise Fejér bound away from the origin. -/
lemma fej_far (L r : ℕ) {x : ZMod N} (hx : x ∉ arc N r) :
    Fej L (ang N x) ≤ (N : ℝ) ^ 2 / (4 * ((r : ℝ) + 1) ^ 2) := by
  obtain ⟨h1, h2⟩ := val_far hx
  have hvN := ZMod.val_lt x
  have hs := sin_lower (r := r) hvN h1 h2
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  set s := Real.sin (π * x.val / N) with hsdef
  have hcos : 2 - 2 * Real.cos (ang N x) = 4 * s ^ 2 := by
    have : ang N x = 2 * (π * x.val / N) := by unfold ang; ring
    rw [this, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (π * x.val / N)
    nlinarith
  have hpos : 0 < 2 * ((r : ℝ) + 1) / N := by positivity
  have hs2 : (2 * ((r : ℝ) + 1) / N) ^ 2 ≤ s ^ 2 := by
    apply pow_le_pow_left₀ hpos.le hs
  have hlow : 16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2 ≤ 2 - 2 * Real.cos (ang N x) := by
    rw [hcos]
    have e16 : 16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2 = 4 * (2 * ((r : ℝ) + 1) / N) ^ 2 := by
      rw [div_pow]; ring
    rw [e16]
    linarith [hs2]
  have hF := fej_mul_le_four L (ang N x)
  have hF0 := fej_nonneg L (ang N x)
  have hq : 0 < 16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2 := by positivity
  have h3 : Fej L (ang N x) * (16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) ≤ 4 := by
    calc Fej L (ang N x) * (16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2)
        ≤ Fej L (ang N x) * (2 - 2 * Real.cos (ang N x)) := mul_le_mul_of_nonneg_left hlow hF0
      _ = (2 - 2 * Real.cos (ang N x)) * Fej L (ang N x) := by ring
      _ ≤ 4 := hF
  rw [le_div_iff₀ (by positivity)]
  have e : Fej L (ang N x) * (4 * ((r : ℝ) + 1) ^ 2) =
      Fej L (ang N x) * (16 * ((r : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 / 4) := by
    field_simp
    ring
  rw [e]
  nlinarith [h3, sq_nonneg (N : ℝ)]

lemma near_arc (k c d : ℕ) (h1 : c ≤ k + d) (h2 : k ≤ c + d) :
    (k : ZMod N) - (c : ZMod N) ∈ arc N d := by
  rw [mem_arc_iff]
  rcases le_total c k with h | h
  · refine ⟨k - c, by omega, Or.inl ?_⟩
    rw [Nat.cast_sub h]
  · refine ⟨c - k, by omega, Or.inr ?_⟩
    rw [Nat.cast_sub h]
    ring

/-- The annulus `{±k : j m ≤ k ≤ (j+1) m - 1}`. -/
noncomputable def ann (N m j : ℕ) [NeZero N] : Finset (ZMod N) :=
  open Classical in arc N ((j + 1) * m - 1) \ arc N (j * m - 1)

/-- **Annulus mass**: each annulus (`j ≥ 1`) has `ν`-mass at most `4 B`. -/
theorem ann_mass (m j : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hj : 1 ≤ j) (ν : ZMod N → ℝ)
    (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ)) :
    ∑ x ∈ ann N m j, ν x ≤ 4 * ∑ t ∈ arc N (m - 1), ν t := by
  classical
  set y : ZMod N := ((j * m + m / 2 : ℕ) : ZMod N) with hy
  have hsub : ann N m j ⊆ (arc N (m / 2)).image (fun t => y + t) ∪
      (arc N (m / 2)).image (fun t => -y + t) := by
    intro x hx
    unfold ann at hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_arc_iff] at hx1
    obtain ⟨k, hk, h | h⟩ := hx1
    · have hk2 : j * m ≤ k := by
        by_contra hlt
        push Not at hlt
        apply hx2
        rw [mem_arc_iff]
        exact ⟨k, by omega, Or.inl h⟩
      rw [Finset.mem_union]
      left
      rw [Finset.mem_image]
      refine ⟨x - y, ?_, by ring⟩
      rw [h, hy]
      apply near_arc
      · omega
      · have : (j + 1) * m - 1 = j * m + m - 1 := by rw [add_mul]; omega
        omega
    · have hk2 : j * m ≤ k := by
        by_contra hlt
        push Not at hlt
        apply hx2
        rw [mem_arc_iff]
        exact ⟨k, by omega, Or.inr h⟩
      rw [Finset.mem_union]
      right
      rw [Finset.mem_image]
      refine ⟨x + y, ?_, by ring⟩
      have h3 : x + y = -((k : ZMod N) - (((j * m + m / 2 : ℕ) : ZMod N))) := by rw [h, hy]; ring
      rw [h3]
      apply arc_neg
      apply near_arc
      · omega
      · have : (j + 1) * m - 1 = j * m + m - 1 := by rw [add_mul]; omega
        omega
  have h1 := loc_mass_half m hm hmN ν hν hc y
  have h2 := loc_mass_half m hm hmN ν hν hc (-y)
  have e1 : ∑ x ∈ (arc N (m / 2)).image (fun t => y + t), ν x = ∑ t ∈ arc N (m / 2), ν (y + t) :=
    Finset.sum_image (fun a _ b _ h => add_left_cancel h)
  have e2 : ∑ x ∈ (arc N (m / 2)).image (fun t => -y + t), ν x = ∑ t ∈ arc N (m / 2), ν (-y + t) :=
    Finset.sum_image (fun a _ b _ h => add_left_cancel h)
  calc ∑ x ∈ ann N m j, ν x
      ≤ ∑ x ∈ (arc N (m / 2)).image (fun t => y + t) ∪ (arc N (m / 2)).image (fun t => -y + t), ν x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hν x)
    _ ≤ ∑ x ∈ (arc N (m / 2)).image (fun t => y + t), ν x +
        ∑ x ∈ (arc N (m / 2)).image (fun t => -y + t), ν x := by
        have := Finset.sum_union_inter (s₁ := (arc N (m / 2)).image (fun t => y + t))
          (s₂ := (arc N (m / 2)).image (fun t => -y + t)) (f := ν)
        have h0 : 0 ≤ ∑ x ∈ ((arc N (m / 2)).image (fun t => y + t)) ∩
            ((arc N (m / 2)).image (fun t => -y + t)), ν x :=
          Finset.sum_nonneg (fun x _ => hν x)
        linarith
    _ ≤ 4 * ∑ t ∈ arc N (m - 1), ν t := by rw [e1, e2]; linarith

lemma icc_sq (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have key : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hN0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hN0 hN0, mul_pos (mul_pos hN0 hN0) hN0]
    linarith

lemma sum_inv_sq_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have := icc_sq N h
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- **Block summation for the Fejér kernel.** -/
theorem fej_block_sum (L m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ L * m) (ν : ZMod N → ℝ)
    (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ)) :
    ∑ x, ν x * Fej L (ang N x) ≤ 3 * (L : ℝ) ^ 2 * ∑ t ∈ arc N (m - 1), ν t := by
  classical
  set B := ∑ t ∈ arc N (m - 1), ν t with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun t _ => hν t)
  -- coefficient of the j-th block
  set cj : ℕ → ℝ := fun j => (N : ℝ) ^ 2 / (4 * ((j : ℝ) * m) ^ 2) with hcj
  have hcj_nonneg : ∀ j, 0 ≤ cj j := fun j => by simp only [hcj]; positivity
  -- pointwise majorant
  have hmaj : ∀ x : ZMod N, Fej L (ang N x) ≤
      (L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0) +
      ∑ j ∈ Finset.Icc 1 N, cj j * (if x ∈ ann N m j then 1 else 0) := by
    intro x
    by_cases hx : x ∈ arc N (m - 1)
    · have h1 := fej_le_sq L (ang N x)
      have h2 : 0 ≤ ∑ j ∈ Finset.Icc 1 N, cj j * (if x ∈ ann N m j then 1 else 0) :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hcj_nonneg j) (by split_ifs <;> norm_num))
      rw [if_pos hx]
      linarith
    · -- find the block
      have hex : ∃ j, x ∈ arc N ((j + 1) * m - 1) := by
        refine ⟨N, ?_⟩
        rw [mem_arc_iff]
        refine ⟨x.val, ?_, Or.inl (ZMod.natCast_zmod_val x).symm⟩
        have := ZMod.val_lt x
        have : N + 1 ≤ (N + 1) * m := by nlinarith
        omega
      set j0 := Nat.find hex with hj0
      have hj0mem : x ∈ arc N ((j0 + 1) * m - 1) := Nat.find_spec hex
      have hj0pos : 1 ≤ j0 := by
        by_contra h0
        have hj0eq : j0 = 0 := by omega
        apply hx
        have h' := hj0mem
        rw [hj0eq] at h'
        simpa using h'
      have hj0N : j0 ≤ N := Nat.find_min' hex (by
        rw [mem_arc_iff]
        refine ⟨x.val, ?_, Or.inl (ZMod.natCast_zmod_val x).symm⟩
        have := ZMod.val_lt x
        have : N + 1 ≤ (N + 1) * m := by nlinarith
        omega)
      have hnot : x ∉ arc N (j0 * m - 1) := by
        have := Nat.find_min hex (show j0 - 1 < j0 by omega)
        have e : (j0 - 1 + 1) * m - 1 = j0 * m - 1 := by
          rw [Nat.sub_add_cancel hj0pos]
        rwa [e] at this
      have hfar := fej_far L (j0 * m - 1) hnot
      have hpos : 1 ≤ j0 * m := by nlinarith
      have e2 : (((j0 * m - 1 : ℕ) : ℝ) + 1) = (j0 : ℝ) * m := by
        rw [Nat.cast_sub hpos]; push_cast; ring
      rw [e2] at hfar
      have hxA : x ∈ ann N m j0 := by
        unfold ann
        rw [Finset.mem_sdiff]
        exact ⟨hj0mem, hnot⟩
      have h1 : cj j0 ≤ ∑ j ∈ Finset.Icc 1 N, cj j * (if x ∈ ann N m j then 1 else 0) := by
        have := Finset.single_le_sum (f := fun j => cj j * (if x ∈ ann N m j then 1 else 0))
          (fun j _ => mul_nonneg (hcj_nonneg j) (by split_ifs <;> norm_num))
          (Finset.mem_Icc.mpr ⟨hj0pos, hj0N⟩)
        simpa [hxA] using this
      have h2 : 0 ≤ (L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0) := by
        split_ifs <;> positivity
      calc Fej L (ang N x) ≤ cj j0 := hfar
        _ ≤ _ := by linarith
  -- sum against ν
  have hstep : ∑ x, ν x * Fej L (ang N x) ≤
      ∑ x, ν x * ((L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0) +
        ∑ j ∈ Finset.Icc 1 N, cj j * (if x ∈ ann N m j then 1 else 0)) :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hmaj x) (hν x))
  have hexp : ∑ x, ν x * ((L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0) +
        ∑ j ∈ Finset.Icc 1 N, cj j * (if x ∈ ann N m j then 1 else 0)) =
      (L : ℝ) ^ 2 * B + ∑ j ∈ Finset.Icc 1 N, cj j * ∑ x ∈ ann N m j, ν x := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [hB, Finset.mul_sum]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun x => x ∈ arc N (m - 1))]
      have h1 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ arc N (m - 1)),
          ν x * ((L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0)) =
          ∑ x ∈ Finset.univ.filter (fun x => x ∈ arc N (m - 1)), (L : ℝ) ^ 2 * ν x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [if_pos hx.2]; ring
      have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ arc N (m - 1)),
          ν x * ((L : ℝ) ^ 2 * (if x ∈ arc N (m - 1) then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [if_neg hx.2]; ring
      rw [h1, h2, add_zero]
      congr 1
      ext x
      simp
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have : ∑ x : ZMod N, ν x * (cj j * (if x ∈ ann N m j then 1 else 0)) =
          cj j * ∑ x : ZMod N, (if x ∈ ann N m j then ν x else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      rw [this, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  -- bound each block
  have hblocks : ∑ j ∈ Finset.Icc 1 N, cj j * ∑ x ∈ ann N m j, ν x ≤
      ∑ j ∈ Finset.Icc 1 N, (L : ℝ) ^ 2 * B * (1 / (j : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hmass := ann_mass m j hm hmN hj.1 ν hν hc
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hNL : (N : ℝ) ≤ L * m := by exact_mod_cast hLm
    have hjm : (0 : ℝ) < (j : ℝ) * m := by positivity
    have hcj_le : cj j ≤ (L : ℝ) ^ 2 / (4 * (j : ℝ) ^ 2) := by
      simp only [hcj]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have : (N : ℝ) ^ 2 ≤ ((L : ℝ) * m) ^ 2 := pow_le_pow_left₀ hN0 hNL 2
      nlinarith [sq_nonneg (j : ℝ), sq_nonneg (m : ℝ)]
    have hmass0 : 0 ≤ ∑ x ∈ ann N m j, ν x := Finset.sum_nonneg (fun x _ => hν x)
    calc cj j * ∑ x ∈ ann N m j, ν x ≤ ((L : ℝ) ^ 2 / (4 * (j : ℝ) ^ 2)) * (4 * B) := by
          apply mul_le_mul hcj_le hmass (by exact hmass0) (by positivity)
      _ = (L : ℝ) ^ 2 * B * (1 / (j : ℝ) ^ 2) := by
          field_simp
  have hgeo : ∑ j ∈ Finset.Icc 1 N, (L : ℝ) ^ 2 * B * (1 / (j : ℝ) ^ 2) ≤ 2 * ((L : ℝ) ^ 2 * B) := by
    rw [← Finset.mul_sum]
    have := sum_inv_sq_le N
    have h0 : 0 ≤ (L : ℝ) ^ 2 * B := by positivity
    nlinarith
  calc ∑ x, ν x * Fej L (ang N x) ≤ _ := hstep
    _ = _ := hexp
    _ ≤ (L : ℝ) ^ 2 * B + 2 * ((L : ℝ) ^ 2 * B) := by linarith
    _ = 3 * (L : ℝ) ^ 2 * B := by ring

/-- The real part of the character at `h x` is `cos (h · angle)`. -/
lemma stdAddChar_re (h : ℕ) (x : ZMod N) :
    (ZMod.stdAddChar ((h : ZMod N) * x)).re = Real.cos (h * ang N x) := by
  have e : (h : ZMod N) * x = (((h * x.val : ℕ) : ℤ) : ZMod N) := by
    simp [mul_comm]
  rw [e, ZMod.stdAddChar_coe]
  have e2 : 2 * (π : ℂ) * Complex.I * (((h * x.val : ℕ) : ℤ) : ℂ) / (N : ℂ) =
      ((2 * π * ((h * x.val : ℕ) : ℝ) / N : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e2, Complex.exp_ofReal_mul_I_re]
  congr 1
  unfold ang
  push_cast
  ring

lemma hpd_of_hc (ν : ZMod N → ℝ)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ))
    (h : ℕ) : 0 ≤ ∑ x, ν x * Real.cos (h * ang N x) := by
  obtain ⟨c, hc0, hcs⟩ := hc (h : ZMod N)
  have := congrArg Complex.re hcs
  rw [Complex.re_sum, Complex.ofReal_re] at this
  have h2 : ∑ x, ν x * Real.cos (h * ang N x) = c := by
    rw [← this]
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.re_ofReal_mul, stdAddChar_re]
  rw [h2]; exact hc0

/-- **The spectral window bound.** For `m = ⌈N/L⌉`, i.e. `N ≤ L m`, `∑ ν Ψ_L ≤ 3 L^3 ν(arc (m-1))`. -/
theorem spectral_window (L m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ L * m) (ν : ZMod N → ℝ)
    (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ)) :
    ∑ x, ν x * Psi L (ang N x) ≤ 3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1), ν t := by
  have h1 := spectral_step Finset.univ ν (ang N) hν (hpd_of_hc ν hc) L
  have h2 := fej_block_sum L m hm hmN hLm ν hν hc
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  calc ∑ x, ν x * Psi L (ang N x) ≤ L * ∑ x, ν x * Fej L (ang N x) := h1
    _ ≤ L * (3 * (L : ℝ) ^ 2 * ∑ t ∈ arc N (m - 1), ν t) := mul_le_mul_of_nonneg_left h2 hL0
    _ = 3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1), ν t := by ring

#print axioms fej_far
#print axioms ann_mass
#print axioms fej_block_sum
#print axioms spectral_window

end JABlocks
end LeanCheck
