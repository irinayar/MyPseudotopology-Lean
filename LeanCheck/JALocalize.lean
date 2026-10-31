import Mathlib
import LeanCheck.MixedPrimeProduct

/-!
# Localization of mass for positive-definite measures on a finite cyclic group (component 16)

The paper's argument uses the triangular cutoff on the circle, whose Fourier series is infinite.  For a measure on
the finite group `ZMod N` (which is where the expected spectral measures of the construction live) the cutoff is
replaced by the autocorrelation `a(t) = ∑_x w(x) w(x+t)` of an interval indicator `w`; its Fourier coefficients
`|ŵ(r)|^2` are nonnegative, so no series has to be summed.

Checked here (no axiom, no `sorry`):

* `loc_fourier`: if `ν` has real nonnegative Fourier coefficients (`hc`), then for every real window `w` and every `y`
  `∑_x ν(x) a(x - y) ≤ ∑_x ν(x) a(x)`  (the triangular-cutoff statement "the integral of the translated cutoff is
  largest at the origin");
* `loc_mass`: for the window `w = 1_{[0,m)}`: the `ν`-mass of the arc `y + {±k : k ≤ m/2}` is at most twice the mass
  of the arc `{±k : k < m}`  (radius `1/(2L)` versus `1/L` when `m ≈ N/L`).
-/

namespace LeanCheck
namespace JALocalize

open Finset MixedPrimeProduct

/-- Autocorrelation of a window on `ZMod N`. -/
def acorr {N : ℕ} [NeZero N] (w : ZMod N → ℝ) (t : ZMod N) : ℝ := ∑ x, w x * w (x + t)

section fourier

variable {N : ℕ} [NeZero N]

lemma acorr_eq (w : ZMod N → ℝ) (t : ZMod N) :
    ((N : ℂ) * (acorr w t : ℂ)) =
      ∑ r : ZMod N, ((∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) *
        (∑ z, (w z : ℂ) * ZMod.stdAddChar (-(r * z)))) * ZMod.stdAddChar (r * t) := by
  rw [autocorr N w t]
  unfold acorr
  push_cast
  all_goals rfl

lemma coef_mul_conj (w : ZMod N → ℝ) (r : ZMod N) :
    (∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) * (∑ z, (w z : ℂ) * ZMod.stdAddChar (-(r * z))) =
      (((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖) ^ 2 : ℝ) : ℂ) := by
  have h : (∑ z, (w z : ℂ) * ZMod.stdAddChar (-(r * z))) =
      (starRingEnd ℂ) (∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_mul, Complex.conj_ofReal, AddChar.map_neg_eq_conj]
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The translated cutoff has the largest integral at the origin.** -/
theorem loc_fourier (w ν : ZMod N → ℝ)
    (hc : ∀ r : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (r * x) = (c : ℂ))
    (y : ZMod N) : ∑ x, ν x * acorr w (x - y) ≤ ∑ x, ν x * acorr w x := by
  choose c hc0 hcc using hc
  -- the identity at a general shift
  have key : ∀ y : ZMod N, ((N : ℂ) * ((∑ x, ν x * acorr w (x - y) : ℝ) : ℂ)) =
      ∑ r : ZMod N, (((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖) ^ 2 : ℝ) : ℂ) * (c r : ℂ) *
        ZMod.stdAddChar (-(r * y)) := by
    intro y
    have h1 : ((N : ℂ) * ((∑ x, ν x * acorr w (x - y) : ℝ) : ℂ)) =
        ∑ x, (ν x : ℂ) * ((N : ℂ) * (acorr w (x - y) : ℂ)) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h1]
    have h2 : ∀ x : ZMod N, (ν x : ℂ) * ((N : ℂ) * (acorr w (x - y) : ℂ)) =
        ∑ r : ZMod N, (((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖) ^ 2 : ℝ) : ℂ) *
          ((ν x : ℂ) * ZMod.stdAddChar (r * x)) * ZMod.stdAddChar (-(r * y)) := by
      intro x
      rw [acorr_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [coef_mul_conj]
      have : (ZMod.stdAddChar (r * (x - y)) : ℂ) =
          ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [this]
      ring
    simp_rw [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcc r]
    all_goals ring
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set R : ZMod N → ℝ := fun r => ‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 * c r with hR
  have hR0 : ∀ r, 0 ≤ R r := fun r => mul_nonneg (sq_nonneg _) (hc0 r)
  have key' : ∀ y : ZMod N, ((N : ℂ) * ((∑ x, ν x * acorr w (x - y) : ℝ) : ℂ)) =
      ∑ r : ZMod N, (R r : ℂ) * ZMod.stdAddChar (-(r * y)) := by
    intro y
    rw [key y]
    apply Finset.sum_congr rfl
    intro r _
    rw [hR]
    push_cast
    ring
  have hy : (N : ℝ) * ∑ x, ν x * acorr w (x - y) ≤ ∑ r, R r := by
    have h1 := congrArg Complex.re (key' y)
    have h2 : ((N : ℂ) * ((∑ x, ν x * acorr w (x - y) : ℝ) : ℂ)) =
        (((N : ℝ) * ∑ x, ν x * acorr w (x - y) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.ofReal_re, Complex.re_sum] at h1
    rw [h1]
    apply Finset.sum_le_sum
    intro r _
    rw [Complex.re_ofReal_mul]
    have hn : (ZMod.stdAddChar (-(r * y)) : ℂ).re ≤ 1 := by
      calc (ZMod.stdAddChar (-(r * y)) : ℂ).re ≤ ‖(ZMod.stdAddChar (-(r * y)) : ℂ)‖ :=
            Complex.re_le_norm _
        _ = 1 := AddChar.norm_apply _ _
    nlinarith [hR0 r]
  have h0 : (N : ℝ) * ∑ x, ν x * acorr w (x - 0) = ∑ r, R r := by
    have h1 := key' 0
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one] at h1
    have h2 : ((N : ℂ) * ((∑ x, ν x * acorr w (x - 0) : ℝ) : ℂ)) =
        (((N : ℝ) * ∑ x, ν x * acorr w (x - 0) : ℝ) : ℂ) := by push_cast; ring
    rw [h2] at h1
    have h3 : (∑ r : ZMod N, (R r : ℂ)) = ((∑ r, R r : ℝ) : ℂ) := by push_cast; rfl
    rw [h3] at h1
    exact_mod_cast h1
  simp only [sub_zero] at h0
  have : (N : ℝ) * ∑ x, ν x * acorr w (x - y) ≤ (N : ℝ) * ∑ x, ν x * acorr w x := by
    rw [h0]; exact hy
  exact le_of_mul_le_mul_left this hN

end fourier


section arcs

variable {N : ℕ} [NeZero N]

open Classical in
/-- The window `[0, m)` as a finite subset of `ZMod N`. -/
noncomputable def Jset (N m : ℕ) [NeZero N] : Finset (ZMod N) :=
  (range m).image (fun k : ℕ => (k : ZMod N))

open Classical in
/-- Indicator of `[0, m)`. -/
noncomputable def win (N m : ℕ) [NeZero N] : ZMod N → ℝ := fun x => if x ∈ Jset N m then 1 else 0

open Classical in
/-- The arc `{±k : k ≤ r}`. -/
noncomputable def arc (N r : ℕ) [NeZero N] : Finset (ZMod N) :=
  (range (r + 1)).image (fun k : ℕ => (k : ZMod N)) ∪
    (range (r + 1)).image (fun k : ℕ => -(k : ZMod N))

lemma win_nonneg (m : ℕ) (x : ZMod N) : 0 ≤ win N m x := by
  unfold win; split_ifs <;> norm_num

lemma win_le_one (m : ℕ) (x : ZMod N) : win N m x ≤ 1 := by
  unfold win; split_ifs <;> norm_num

lemma win_nat (m j : ℕ) (hj : j < m) : win N m (j : ZMod N) = 1 := by
  classical
  unfold win
  rw [if_pos]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

lemma acorr_nonneg (m : ℕ) (t : ZMod N) : 0 ≤ acorr (win N m) t :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (win_nonneg m x) (win_nonneg m _))

lemma card_Jset_le (m : ℕ) : (Jset N m).card ≤ m := by
  classical
  unfold Jset
  exact (Finset.card_image_le).trans (by simp)

lemma sum_win (m : ℕ) : ∑ x : ZMod N, win N m x = ((Jset N m).card : ℝ) := by
  classical
  unfold win
  rw [Finset.sum_boole]
  congr 1
  simp

lemma acorr_le (m : ℕ) (t : ZMod N) : acorr (win N m) t ≤ m := by
  unfold acorr
  calc ∑ x, win N m x * win N m (x + t) ≤ ∑ x, win N m x :=
        Finset.sum_le_sum (fun x _ => by
          have := win_nonneg (N := N) m x
          have := win_le_one (N := N) m (x + t)
          nlinarith)
    _ = ((Jset N m).card : ℝ) := sum_win m
    _ ≤ m := by exact_mod_cast card_Jset_le m

/-- The autocorrelation of the window vanishes outside the arc `{±k : k < m}`. -/
lemma acorr_support (m : ℕ) (t : ZMod N) (ht : t ∉ arc N (m - 1)) : acorr (win N m) t = 0 := by
  classical
  unfold acorr
  apply Finset.sum_eq_zero
  intro x _
  by_contra hne
  have h1 : win N m x ≠ 0 := fun h => hne (by rw [h]; ring)
  have h2 : win N m (x + t) ≠ 0 := fun h => hne (by rw [h]; ring)
  unfold win at h1 h2
  have hx : x ∈ Jset N m := by by_contra h; exact h1 (if_neg h)
  have hxt : x + t ∈ Jset N m := by by_contra h; exact h2 (if_neg h)
  unfold Jset at hx hxt
  rw [Finset.mem_image] at hx hxt
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hxt
  rw [Finset.mem_range] at ha hb
  apply ht
  unfold arc
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  have htb : t = (b : ZMod N) - (a : ZMod N) := by rw [hbe]; ring
  rcases le_total a b with hab | hab
  · left
    refine ⟨b - a, Finset.mem_range.mpr (by omega), ?_⟩
    rw [htb, Nat.cast_sub hab]
  · right
    refine ⟨a - b, Finset.mem_range.mpr (by omega), ?_⟩
    rw [htb, Nat.cast_sub hab]
    ring

lemma cast_inj_lt {m : ℕ} (hmN : m ≤ N) {a b : ℕ} (ha : a < m) (hb : b < m)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

/-- Lower bound at a positive shift `k`. -/
lemma acorr_ge_pos (m k : ℕ) (hmN : m ≤ N) (hk : k ≤ m) :
    ((m - k : ℕ) : ℝ) ≤ acorr (win N m) (k : ZMod N) := by
  classical
  unfold acorr
  have hsub : ((range (m - k)).image (fun j : ℕ => (j : ZMod N))) ⊆ (univ : Finset (ZMod N)) :=
    Finset.subset_univ _
  calc ((m - k : ℕ) : ℝ) = ∑ x ∈ (range (m - k)).image (fun j : ℕ => (j : ZMod N)), (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_image_of_injOn, Finset.card_range]
        · simp
        · intro a ha b hb h
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          exact cast_inj_lt hmN (by omega) (by omega) h
    _ ≤ ∑ x ∈ (range (m - k)).image (fun j : ℕ => (j : ZMod N)),
          win N m x * win N m (x + (k : ZMod N)) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [Finset.mem_range] at hj
        rw [win_nat m j (by omega),
          show ((j : ZMod N) + (k : ZMod N)) = ((j + k : ℕ) : ZMod N) by push_cast; ring,
          win_nat m (j + k) (by omega)]
        norm_num
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => mul_nonneg (win_nonneg m x) (win_nonneg m _))

/-- Lower bound at a negative shift `-k`. -/
lemma acorr_ge_neg (m k : ℕ) (hmN : m ≤ N) (hk : k ≤ m) :
    ((m - k : ℕ) : ℝ) ≤ acorr (win N m) (-(k : ZMod N)) := by
  classical
  unfold acorr
  have hsub : ((range (m - k)).image (fun j : ℕ => ((j + k : ℕ) : ZMod N))) ⊆
      (univ : Finset (ZMod N)) := Finset.subset_univ _
  calc ((m - k : ℕ) : ℝ) =
        ∑ x ∈ (range (m - k)).image (fun j : ℕ => ((j + k : ℕ) : ZMod N)), (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_image_of_injOn, Finset.card_range]
        · simp
        · intro a ha b hb h
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          have := cast_inj_lt hmN (a := a + k) (b := b + k) (by omega) (by omega) h
          omega
    _ ≤ ∑ x ∈ (range (m - k)).image (fun j : ℕ => ((j + k : ℕ) : ZMod N)),
          win N m x * win N m (x + -(k : ZMod N)) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [Finset.mem_range] at hj
        rw [win_nat m (j + k) (by omega),
          show (((j + k : ℕ) : ZMod N) + -(k : ZMod N)) = (j : ZMod N) by push_cast; ring,
          win_nat m j (by omega)]
        norm_num
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => mul_nonneg (win_nonneg m x) (win_nonneg m _))

lemma acorr_ge_arc (m r : ℕ) (hmN : m ≤ N) (hr : r ≤ m) (t : ZMod N) (ht : t ∈ arc N r) :
    ((m - r : ℕ) : ℝ) ≤ acorr (win N m) t := by
  classical
  unfold arc at ht
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ht
  rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · rw [Finset.mem_range] at hk
    refine le_trans ?_ (acorr_ge_pos m k hmN (by omega))
    exact_mod_cast Nat.sub_le_sub_left (by omega) m
  · rw [Finset.mem_range] at hk
    refine le_trans ?_ (acorr_ge_neg m k hmN (by omega))
    exact_mod_cast Nat.sub_le_sub_left (by omega) m

/-- **Localization of mass.**  For a nonnegative measure `ν` on `ZMod N` with real nonnegative Fourier
coefficients, the mass of the arc `y + {±k : k ≤ r}` times `m - r` is at most `m` times the mass of the central
arc `{±k : k < m}`. -/
theorem loc_mass (m r : ℕ) (hmN : m ≤ N) (hr : r ≤ m) (ν : ZMod N → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ))
    (y : ZMod N) :
    ((m - r : ℕ) : ℝ) * ∑ t ∈ arc N r, ν (y + t) ≤ (m : ℝ) * ∑ t ∈ arc N (m - 1), ν t := by
  classical
  have hF := loc_fourier (win N m) ν hc y
  have hre : ∑ x, ν x * acorr (win N m) (x - y) = ∑ t, ν (y + t) * acorr (win N m) t := by
    rw [← Equiv.sum_comp (Equiv.addLeft y)]
    apply Finset.sum_congr rfl
    intro t _
    simp
  rw [hre] at hF
  have hlow : ((m - r : ℕ) : ℝ) * ∑ t ∈ arc N r, ν (y + t) ≤
      ∑ t, ν (y + t) * acorr (win N m) t := by
    rw [Finset.mul_sum]
    calc ∑ t ∈ arc N r, ((m - r : ℕ) : ℝ) * ν (y + t)
        ≤ ∑ t ∈ arc N r, ν (y + t) * acorr (win N m) t := by
          apply Finset.sum_le_sum
          intro t ht
          have := acorr_ge_arc m r hmN hr t ht
          nlinarith [hν (y + t)]
      _ ≤ ∑ t, ν (y + t) * acorr (win N m) t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun t _ _ => mul_nonneg (hν _) (acorr_nonneg m t))
  have hup : ∑ x, ν x * acorr (win N m) x ≤ (m : ℝ) * ∑ t ∈ arc N (m - 1), ν t := by
    rw [Finset.mul_sum]
    have hz : ∀ x ∈ (univ : Finset (ZMod N)), x ∉ arc N (m - 1) →
        ν x * acorr (win N m) x = 0 := by
      intro x _ hx
      rw [acorr_support m x hx, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ (arc N (m - 1))) hz]
    apply Finset.sum_le_sum
    intro x _
    have := acorr_le (N := N) m x
    nlinarith [hν x]
  linarith

/-- **The statement used for the spectral window**: radius `m/2` versus radius `m - 1`, with the factor `2`. -/
theorem loc_mass_half (m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (ν : ZMod N → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ))
    (y : ZMod N) :
    ∑ t ∈ arc N (m / 2), ν (y + t) ≤ 2 * ∑ t ∈ arc N (m - 1), ν t := by
  have h := loc_mass m (m / 2) hmN (Nat.div_le_self m 2) ν hν hc y
  have hA : 0 ≤ ∑ t ∈ arc N (m / 2), ν (y + t) := Finset.sum_nonneg (fun t _ => hν _)
  have hB : 0 ≤ ∑ t ∈ arc N (m - 1), ν t := Finset.sum_nonneg (fun t _ => hν _)
  have h2 : (m : ℝ) ≤ 2 * ((m - m / 2 : ℕ) : ℝ) := by
    have : m ≤ 2 * (m - m / 2) := by omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  nlinarith

end arcs

#print axioms loc_fourier
#print axioms loc_mass
#print axioms loc_mass_half

end JALocalize
end LeanCheck
