import LeanCheck.TVGPlusOrderB
import LeanCheck.MixedPrimeColoured

/-!
# TVGplus: the finite collision-energy criterion for shifted targets

Formal counterpart of the criterion of the Codex note of 6 November 2026, 19:03 (audited by Claude
the same day). For nonempty scale sets `Sq`, `Sp ⊆ ℕ`, an integer `X ≥ 0` and `r : ℝ` put

* `A = {a ∈ [0, X] : Pn Sq a < r}` and `B = {b ∈ [0, X] : Pn Sp b < r}`,
* `V = {a - b : a ∈ A, b ∈ B}`, `R t = #{(a, b) ∈ A × B : a - b = t}`, `E = ∑_{t ∈ V} R t ^ 2`,
* `M = 2 X + 1` and `L = ⌈(|A| |B|)² / E⌉`.

`energy_criterion`: every integer `t` with `|t| + M + 1 ≤ 2 L` (that is, `|t| ≤ 2L - M - 1`) has a
signed witness `k` with `|k| ≤ X`, `Pn Sq k < 2 r` and `Pn Sp (k - t) < 2 r`.
`energy_criterion_sq` specializes to the scales `sqScales q`, `sqScales p` of the article.
`energy_arithmetic`: for `X = 10^12` and `L = 1418493632083` the bound is `836987264164`.

The pseudonorms are those of the article, `Pn S k = sup_{q ∈ S} ‖k / q‖`; the proof uses only the
subadditivity `Pn_sub_le`. The energy certificate of the manuscript (`L = 1418493632083` at
`r = 1/20`, `X = 10^12`) is a finite computation that is not part of this file.
-/

namespace LeanCheck
namespace ShiftedEnergy

open LeanCheck.MixedPrime Finset
open scoped Classical

section Criterion

variable (Sq Sp : Set ℕ) (X : ℕ) (r : ℝ)

/-- `A = {a ∈ [0, X] : Pn Sq a < r}`. -/
noncomputable def ballA : Finset ℤ := (Finset.Icc (0 : ℤ) X).filter (fun a => Pn Sq a < r)

/-- `B = {b ∈ [0, X] : Pn Sp b < r}`. -/
noncomputable def ballB : Finset ℤ := (Finset.Icc (0 : ℤ) X).filter (fun b => Pn Sp b < r)

/-- The difference set `V = A - B`. -/
noncomputable def diffV : Finset ℤ :=
  (ballA Sq X r ×ˢ ballB Sp X r).image (fun x => x.1 - x.2)

/-- `R t`, the number of representations of `t` as `a - b`. -/
noncomputable def rep (t : ℤ) : ℕ :=
  ((ballA Sq X r ×ˢ ballB Sp X r).filter (fun x => x.1 - x.2 = t)).card

/-- The energy `E = ∑ R t ^ 2`. -/
noncomputable def energy : ℕ := ∑ t ∈ diffV Sq Sp X r, rep Sq Sp X r t ^ 2

/-- `L = ⌈(|A| |B|)² / E⌉`. -/
noncomputable def Lbound : ℕ :=
  ⌈(((ballA Sq X r).card * (ballB Sp X r).card : ℕ) ^ 2 : ℝ) / (energy Sq Sp X r : ℝ)⌉₊

lemma sum_rep : ∑ t ∈ diffV Sq Sp X r, rep Sq Sp X r t = (ballA Sq X r).card * (ballB Sp X r).card := by
  unfold diffV rep
  rw [← Finset.card_eq_sum_card_image (fun x : ℤ × ℤ => x.1 - x.2), Finset.card_product]

/-- Cauchy–Schwarz: `(|A| |B|)² ≤ |V| E`. -/
lemma cs_bound : ((ballA Sq X r).card * (ballB Sp X r).card) ^ 2 ≤
    (diffV Sq Sp X r).card * energy Sq Sp X r := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (diffV Sq Sp X r) (fun t => (rep Sq Sp X r t : ℝ))
    (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
  have hs : (∑ t ∈ diffV Sq Sp X r, (rep Sq Sp X r t : ℝ)) =
      ((ballA Sq X r).card * (ballB Sp X r).card : ℕ) := by
    rw [← sum_rep Sq Sp X r]; push_cast; rfl
  rw [hs] at h
  unfold energy
  have : (((ballA Sq X r).card * (ballB Sp X r).card : ℕ) : ℝ) ^ 2 ≤
      ((diffV Sq Sp X r).card : ℝ) * ((∑ t ∈ diffV Sq Sp X r, rep Sq Sp X r t ^ 2 : ℕ) : ℝ) := by
    push_cast at h ⊢
    nlinarith [h]
  exact_mod_cast this

/-- `L ≤ |V|`. -/
lemma Lbound_le_card : Lbound Sq Sp X r ≤ (diffV Sq Sp X r).card := by
  unfold Lbound
  rw [Nat.ceil_le]
  by_cases hE : energy Sq Sp X r = 0
  · rw [hE]; simp
  · have hEpos : (0 : ℝ) < energy Sq Sp X r := by exact_mod_cast Nat.pos_of_ne_zero hE
    rw [div_le_iff₀ hEpos]
    have := cs_bound Sq Sp X r
    have : ((((ballA Sq X r).card * (ballB Sp X r).card : ℕ) : ℝ)) ^ 2 ≤
        ((diffV Sq Sp X r).card : ℝ) * (energy Sq Sp X r : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    exact this

lemma diffV_subset : diffV Sq Sp X r ⊆ Finset.Icc (-(X : ℤ)) X := by
  intro v hv
  unfold diffV at hv
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨ha, _⟩ := Finset.mem_filter.1 (Finset.mem_product.1 hab).1
  obtain ⟨hb, _⟩ := Finset.mem_filter.1 (Finset.mem_product.1 hab).2
  rw [Finset.mem_Icc] at ha hb ⊢
  constructor <;> omega

variable {Sq Sp}

/-- **Finite collision-energy criterion.** -/
theorem energy_criterion (hSq : Sq.Nonempty) (hSp : Sp.Nonempty) (t : ℤ)
    (ht : |t| + (2 * (X : ℤ) + 1) + 1 ≤ 2 * (Lbound Sq Sp X r : ℤ)) :
    ∃ k : ℤ, |k| ≤ X ∧ Pn Sq k < 2 * r ∧ Pn Sp (k - t) < 2 * r := by
  set V := diffV Sq Sp X r with hV
  set V' : Finset ℤ := V.image (fun v => v + t) with hV'
  have hcard' : V'.card = V.card :=
    Finset.card_image_of_injective _ (add_left_injective t)
  have hLV : Lbound Sq Sp X r ≤ V.card := Lbound_le_card Sq Sp X r
  -- the two sets meet
  have hmeet : ¬ Disjoint V V' := by
    intro hdis
    have hsub : V ∪ V' ⊆ Finset.Icc (-(X : ℤ) + min 0 t) (X + max 0 t) := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · have := diffV_subset Sq Sp X r h
        rw [Finset.mem_Icc] at this ⊢
        constructor <;> [skip; skip] <;> (have := min_le_left 0 t; have := le_max_left 0 t; omega)
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        have := diffV_subset Sq Sp X r hv
        rw [Finset.mem_Icc] at this ⊢
        have h1 := min_le_right 0 t
        have h2 := le_max_right 0 t
        constructor <;> omega
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, hcard', Int.card_Icc] at hle
    rcases le_total 0 t with h0 | h0
    · have e1 : min 0 t = 0 := min_eq_left h0
      have e2 : max 0 t = t := max_eq_right h0
      rw [e1, e2] at hle
      rw [abs_of_nonneg h0] at ht
      omega
    · have e1 : min 0 t = t := min_eq_right h0
      have e2 : max 0 t = 0 := max_eq_left h0
      rw [e1, e2] at hle
      rw [abs_of_nonpos h0] at ht
      omega
  -- a common point
  obtain ⟨x, hxV, hxV'⟩ : ∃ x, x ∈ V ∧ x ∈ V' := by
    by_contra hcon
    apply hmeet
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 hxV'
  obtain ⟨⟨a', b'⟩, hab', hx⟩ := Finset.mem_image.1 hxV
  obtain ⟨⟨a, b⟩, hab, hv'⟩ := Finset.mem_image.1 hv
  simp only at hx hv'
  have ha' := Finset.mem_filter.1 (Finset.mem_product.1 hab').1
  have hb' := Finset.mem_filter.1 (Finset.mem_product.1 hab').2
  have ha := Finset.mem_filter.1 (Finset.mem_product.1 hab).1
  have hb := Finset.mem_filter.1 (Finset.mem_product.1 hab).2
  rw [Finset.mem_Icc] at ha'  hb' ha hb
  have hk : |a' - a| ≤ X := by rw [abs_le]; constructor <;> omega
  refine ⟨a' - a, by exact_mod_cast hk, ?_, ?_⟩
  · have := Pn_sub_le hSq a' a
    linarith [ha'.2, ha.2]
  · have e : a' - a - t = b' - b := by omega
    rw [e]
    have := Pn_sub_le hSp b' b
    linarith [hb'.2, hb.2]

end Criterion

open Cardinal in
/-- The specialization to the scales `sqScales q`, `sqScales p` of the article. -/
theorem energy_criterion_sq (p q X : ℕ) (r : ℝ) (t : ℤ)
    (ht : |t| + (2 * (X : ℤ) + 1) + 1 ≤ 2 * (Lbound (sqScales q) (sqScales p) X r : ℤ)) :
    ∃ k : ℤ, |k| ≤ X ∧ Pn (sqScales q) k < 2 * r ∧ Pn (sqScales p) (k - t) < 2 * r :=
  energy_criterion X r (LeanCheck.TVGPlus.sq_nonempty q) (LeanCheck.TVGPlus.sq_nonempty p) t ht

/-- The arithmetic of the manuscript's certificate: `2L - M - 1 = 836987264164`. -/
theorem energy_arithmetic :
    2 * (1418493632083 : ℤ) - (2 * (10 ^ 12 : ℤ) + 1) - 1 = 836987264164 := by norm_num

/-- A unit target needs `L ≥ X + 2`. -/
theorem unit_target_iff (L X : ℤ) :
    (1 : ℤ) + (2 * X + 1) + 1 ≤ 2 * L ↔ X + 2 ≤ L := by omega

end ShiftedEnergy
end LeanCheck
