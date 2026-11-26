import Mathlib
import LeanCheck.TwoPrimesFormula
import LeanCheck.TwoPrimesNonresonance

/-!
# Heights `X = M v` with a general number `M` of top clusters

The module `TwoPrimesFormula` treats the height `X = D v`, where `1/D` is the radius.  Here the
number of top clusters is a separate integer `M ≥ 100`.  The lower set `Z` may have any number of
elements (it contains `0`).

* `energy_formula_multiple`: `(1 - 5/M)(4/3) κ_M ≤ C ≤ (1 + 5/M)(4/3) κ_M`.  The lower sets only
  have to satisfy `Wide` (widths `100|y| < u`, `100|z| < v`, `v ≥ 2000 u`).
* `energy_of_kappa_lt`: if `κ_M ≤ K < 69/40` and `M ≥ 200K/(69 - 40K)` then `C ≤ 2.3`.
* `block_transfer`: `H² P_j ≤ (j+H-1)² P_H`, with `P_j = Σ_ξ G(ξ) F_j(ξ v/u)`.
* `kappa_transfer`: `κ_M ≤ (1 + 3h/M + 4h²/M²) P_H/H²`, `h = H - 1`.
* `phi_le_four_kappa`, `kappa_le_thirtytwo`: `P_H/H² ≤ 4 κ_H`, and `κ_M ≤ 32 κ_H` for `H ≤ M`.
* `small_conductor`: the kernel alone bounds the nonzero frequencies of a conductor `Q` prime to
  `v` by `π² Q²/(4 M²)`.
* `exists_far_multiple`: for large `D` one pair of levels serves all `1 ≤ M ≤ D^μ`.

That the balls are the sets `{j u + y}` and `{k v + z}` for the digit sets of two primes is not part
of this module.
-/

namespace TwoPrimesMultiple

open Finset Real TwoPrimesFormula

set_option linter.unusedSectionVars false

/-- The hypotheses: lower digit sets of width `1/100` and `M ≥ 100` top clusters.  No lower bound on
the number of elements of `Z` is assumed; it contains `0`. -/
structure Wide (M u v : ℕ) (Y Z : Finset ℤ) : Prop where
  hv : 2000 * u ≤ v
  hYne : Y.Nonempty
  hY : ∀ y ∈ Y, (100 : ℤ) * |y| < u
  hZ : ∀ z ∈ Z, (100 : ℤ) * |z| < v
  hZ0 : (0 : ℤ) ∈ Z
  hM : 100 ≤ M

/-- A setting of `TwoPrimesFormula` at radius `1/D`, with `M ≥ 100`, satisfies `Wide`. -/
lemma wide_of_setting {D M u v : ℕ} {Y Z : Finset ℤ} (S : Setting D u v Y Z) (hM : 100 ≤ M) :
    Wide M u v Y Z where
  hv := le_trans (Nat.mul_le_mul_right u (Nat.mul_le_mul_left 20 S.hD)) S.hv
  hYne := S.hYne
  hY := by
    intro y hy
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (S.hY y hy)
    exact_mod_cast S.hD
  hZ := by
    intro z hz
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (S.hZ z hz)
    exact_mod_cast S.hD
  hZ0 := S.hZ0
  hM := hM

/-- The hypotheses allow `Z` to consist of one element. -/
theorem wide_singleton : Wide 100 1 2000 {0} {0} where
  hv := by norm_num
  hYne := singleton_nonempty _
  hY := by simp
  hZ := by simp
  hZ0 := mem_singleton_self _
  hM := le_refl _

namespace Wide

variable {M u v : ℕ} {Y Z : Finset ℤ} (W : Wide M u v Y Z)
include W

lemma u_pos : 0 < u := by
  obtain ⟨y, hy⟩ := W.hYne
  have h1 := W.hY y hy
  have h2 := abs_nonneg y
  omega

lemma v_pos : 0 < v := by
  have h1 := W.hZ 0 W.hZ0
  simp only [abs_zero, mul_zero] at h1
  exact_mod_cast h1

lemma uv : 2000 * u ≤ v := W.hv

lemma Y_small : ∀ y ∈ Y, 2 * |y| < (u : ℤ) := by
  intro y hy
  have h1 := W.hY y hy
  have h2 := abs_nonneg y
  omega

lemma Z_small : ∀ z ∈ Z, 2 * |z| < (v : ℤ) := by
  intro z hz
  have h1 := W.hZ z hz
  have h2 := abs_nonneg z
  omega

lemma Y_card_pos : (0 : ℝ) < Y.card := by exact_mod_cast W.hYne.card_pos

lemma Z_card_ge : (1 : ℝ) ≤ Z.card := by
  have h : 0 < Z.card := card_pos.mpr ⟨0, W.hZ0⟩
  exact_mod_cast h

lemma power_eq_G (ξ : ℕ) : power u Y ξ * power u Z ξ
    = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * G u Y Z ξ := by
  have h1 := W.Y_card_pos
  have h2 := W.Z_card_ge
  have h3 : (Z.card : ℝ) ≠ 0 := by linarith
  have h4 : (Y.card : ℝ) ≠ 0 := h1.ne'
  unfold G
  field_simp

lemma sum_power (g : ℕ → ℝ) : ∑ ξ ∈ range u, power u Y ξ * power u Z ξ * g ξ
    = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * ∑ ξ ∈ range u, G u Y Z ξ * g ξ := by
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [W.power_eq_G]
  ring

lemma G_nonneg (ξ : ℕ) : 0 ≤ G u Y Z ξ := by
  unfold G
  exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _)) (by positivity)

lemma G_zero : G u Y Z 0 = 1 := by
  have h1 := W.Y_card_pos
  have h2 := W.Z_card_ge
  have h3 : (Z.card : ℝ) ≠ 0 := by linarith
  have h4 : (Y.card : ℝ) ≠ 0 := h1.ne'
  unfold G
  rw [power_zero, power_zero]
  field_simp

lemma J_ge : 2000 * M ≤ M * v / u := by
  rw [Nat.le_div_iff_mul_le W.u_pos]
  have := Nat.mul_le_mul_left M W.uv
  calc 2000 * M * u = M * (2000 * u) := by ring
    _ ≤ M * v := this

lemma sub_setA : prodSet u (Ico 1 (M * v / u)) Y ⊆ setA M u v Y := by
  intro a ha
  unfold prodSet at ha
  obtain ⟨⟨j, y⟩, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨hj, hy⟩ := mem_product.mp hp
  have hj' := mem_Ico.mp hj
  have hsmall := W.Y_small y hy
  have hy1 := abs_le.mp (le_refl |y|)
  unfold setA
  rw [mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · unfold prodSet
    exact mem_image.mpr ⟨(j, y), mem_product.mpr ⟨mem_range.mpr (by omega), hy⟩, rfl⟩
  · have h1 : (u : ℤ) ≤ (j : ℤ) * u := by
      have : (1 : ℤ) ≤ j := by exact_mod_cast hj'.1
      nlinarith
    have := abs_nonneg y
    simp only
    omega
  · have h1 : ((j : ℤ) + 1) * u ≤ ((M * v / u : ℕ) : ℤ) * u := by
      have : (j : ℤ) + 1 ≤ ((M * v / u : ℕ) : ℤ) := by exact_mod_cast hj'.2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : ((M * v / u : ℕ) : ℤ) * u ≤ (M : ℤ) * v := by
      have := Nat.div_mul_le_self (M * v) u
      exact_mod_cast this
    have e1 : ((j : ℤ) + 1) * u = (j : ℤ) * u + u := by ring
    have := abs_nonneg y
    simp only
    omega

lemma setA_sub : setA M u v Y ⊆ prodSet u (Ico 0 (M * v / u + 2)) Y := by
  unfold setA
  rw [← range_eq_Ico]
  exact filter_subset _ _

lemma sub_setB : prodSet v (Ico 1 M) Z ⊆ setB M v Z := by
  intro b hb
  unfold prodSet at hb
  obtain ⟨⟨k, z⟩, hp, rfl⟩ := mem_image.mp hb
  obtain ⟨hk, hz⟩ := mem_product.mp hp
  have hk' := mem_Ico.mp hk
  have hsmall := W.Z_small z hz
  have hz1 := abs_le.mp (le_refl |z|)
  unfold setB
  rw [mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · unfold prodSet
    exact mem_image.mpr ⟨(k, z), mem_product.mpr ⟨mem_range.mpr (by omega), hz⟩, rfl⟩
  · have h1 : (v : ℤ) ≤ (k : ℤ) * v := by
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk'.1
      nlinarith
    have := abs_nonneg z
    simp only
    omega
  · have h1 : ((k : ℤ) + 1) * v ≤ (M : ℤ) * v := by
      have : (k : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast hk'.2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have e1 : ((k : ℤ) + 1) * v = (k : ℤ) * v + v := by ring
    have := abs_nonneg z
    simp only
    omega

lemma setB_sub : setB M v Z ⊆ prodSet v (Ico 0 (M + 1)) Z := by
  unfold setB
  rw [← range_eq_Ico]
  exact filter_subset _ _

/-- `|B| = M |Z| + 1`. -/
lemma card_setB : (setB M v Z).card = M * Z.card + 1 := by
  have hM := W.hM
  have hv0 := W.v_pos
  have himg : setB M v Z = ((range (M + 1) ×ˢ Z).filter fun p : ℕ × ℤ =>
        0 ≤ (p.1 : ℤ) * v + p.2 ∧ (p.1 : ℤ) * v + p.2 ≤ (M : ℤ) * v).image
        fun p => (p.1 : ℤ) * v + p.2 := by
    unfold setB prodSet
    rw [filter_image]
  rw [himg, card_image_of_injOn ((digit_injOn v _ Z W.Z_small).mono
    (coe_subset.mpr (filter_subset _ _))), card_filter, sum_product]
  obtain ⟨d, hd⟩ : ∃ d, M = d + 1 := ⟨M - 1, by omega⟩
  have hbound : ∀ z ∈ Z, -(v : ℤ) < z ∧ z < v := by
    intro z hz
    have h1 := W.Z_small z hz
    have h2 := abs_le.mp (le_refl |z|)
    have := abs_nonneg z
    omega
  have hfirst : (∑ z ∈ Z, if 0 ≤ ((0 : ℕ) : ℤ) * v + z ∧ ((0 : ℕ) : ℤ) * v + z ≤ (M : ℤ) * v
        then 1 else 0) = (Z.filter fun z => 0 ≤ z).card := by
    rw [card_filter]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (M : ℤ) * v := by
      have : (1 : ℤ) ≤ M := by omega
      nlinarith
    refine if_congr ?_ rfl rfl
    simp only [Nat.cast_zero, zero_mul, zero_add]
    omega
  have hlast : (∑ z ∈ Z, if 0 ≤ ((M : ℕ) : ℤ) * v + z ∧ ((M : ℕ) : ℤ) * v + z ≤ (M : ℤ) * v
        then 1 else 0) = (Z.filter fun z => z ≤ 0).card := by
    rw [card_filter]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (M : ℤ) * v := by
      have : (1 : ℤ) ≤ M := by omega
      nlinarith
    refine if_congr ?_ rfl rfl
    omega
  have hmid : ∀ k ∈ range d, (∑ z ∈ Z,
        if 0 ≤ (((k + 1 : ℕ)) : ℤ) * v + z ∧ (((k + 1 : ℕ)) : ℤ) * v + z ≤ (M : ℤ) * v
        then 1 else 0) = Z.card := by
    intro k hk
    have hk' := mem_range.mp hk
    rw [card_eq_sum_ones]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (((k + 1 : ℕ)) : ℤ) * v := by
      have : (1 : ℤ) ≤ (((k + 1 : ℕ)) : ℤ) := by omega
      nlinarith
    have h3 : ((((k + 1 : ℕ)) : ℤ) + 1) * v ≤ (M : ℤ) * v := by
      have : (((k + 1 : ℕ)) : ℤ) + 1 ≤ M := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have e1 : ((((k + 1 : ℕ)) : ℤ) + 1) * v = (((k + 1 : ℕ)) : ℤ) * v + v := by ring
    rw [if_pos]
    omega
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ range (M + 1), f k
      = (∑ k ∈ range d, f (k + 1)) + f 0 + f M := by
    intro f
    rw [sum_range_succ, hd, sum_range_succ']
  rw [hsplit, sum_congr rfl hmid, hfirst, hlast, sum_const, card_range, smul_eq_mul]
  have hunion : (Z.filter fun z => 0 ≤ z).card + (Z.filter fun z => z ≤ 0).card = Z.card + 1 := by
    have h1 := card_union_add_card_inter (Z.filter fun z => 0 ≤ z) (Z.filter fun z => z ≤ 0)
    have h2 : (Z.filter fun z => 0 ≤ z) ∪ (Z.filter fun z => z ≤ 0) = Z := by
      ext z
      simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        rcases le_total 0 z with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    have h3 : (Z.filter fun z => 0 ≤ z) ∩ (Z.filter fun z => z ≤ 0) = {0} := by
      ext z
      simp only [mem_inter, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨_, h4⟩, ⟨_, h5⟩⟩; omega
      · rintro rfl; exact ⟨⟨W.hZ0, le_refl _⟩, ⟨W.hZ0, le_refl _⟩⟩
    rw [h2, h3, card_singleton] at h1
    exact h1.symm
  have hMZ : M * Z.card = d * Z.card + Z.card := by rw [hd]; ring
  omega

lemma card_setA_lower : (((M * v / u : ℕ) : ℝ) - 1) * Y.card ≤ ((setA M u v Y).card : ℝ) := by
  have h1 := card_le_card W.sub_setA
  rw [card_prodSet u _ Y W.Y_small, Nat.card_Ico] at h1
  have hJ : 1 ≤ M * v / u := by
    have := W.J_ge
    have := W.hM
    omega
  have h3 : (((M * v / u - 1) * Y.card : ℕ) : ℝ) ≤ ((setA M u v Y).card : ℝ) := by exact_mod_cast h1
  rwa [Nat.cast_mul, Nat.cast_sub hJ, Nat.cast_one] at h3

lemma card_setA_upper : ((setA M u v Y).card : ℝ) ≤ (((M * v / u : ℕ) : ℝ) + 2) * Y.card := by
  have h1 := card_le_card W.setA_sub
  rw [card_prodSet u _ Y W.Y_small, Nat.card_Ico, Nat.sub_zero] at h1
  have h3 : ((setA M u v Y).card : ℝ) ≤ (((M * v / u + 2) * Y.card : ℕ) : ℝ) := by exact_mod_cast h1
  rwa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h3

/-- The two weight bounds. -/
lemma weight_bounds (m : ℤ) {y y' z z' : ℤ} (hy : y ∈ Y) (hy' : y' ∈ Y) (hz : z ∈ Z) (hz' : z' ∈ Z)
    (h : (u : ℤ) ∣ m * v + (z - z') - (y - y')) :
    let q := (m * v + (z - z') - (y - y')) / (u : ℤ)
    (v : ℝ) / u * ((M : ℝ) - 3 / 100 - |(m : ℝ)|)
        ≤ ((M * v / u : ℕ) : ℝ) - 1 - (q.natAbs : ℝ) ∧
    (((M * v / u : ℕ) : ℝ) + 2 - (q.natAbs : ℝ)) ≤ (v : ℝ) / u * ((M : ℝ) + 1 - |(m : ℝ)|) := by
  intro q
  have hur : (0 : ℝ) < u := by exact_mod_cast W.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast W.v_pos
  have huv : 2000 * (u : ℝ) ≤ v := by exact_mod_cast W.uv
  have hq : (q : ℝ) * u = (m : ℝ) * v + ((z : ℝ) - z') - ((y : ℝ) - y') := by
    have h1 : q * (u : ℤ) = m * v + (z - z') - (y - y') := Int.ediv_mul_cancel h
    exact_mod_cast h1
  have hnat : (q.natAbs : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hyb : ∀ y ∈ Y, |(y : ℝ)| ≤ u / 100 := by
    intro y hy
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100), mul_comm]
    have h1 := (W.hY y hy).le
    exact_mod_cast h1
  have hzb : ∀ z ∈ Z, |(z : ℝ)| ≤ v / 100 := by
    intro z hz
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100), mul_comm]
    have h1 := (W.hZ z hz).le
    exact_mod_cast h1
  have herr : |((z : ℝ) - z') - ((y : ℝ) - y')| ≤ 2 * (v / 100) + 2 * (u / 100) := by
    have h1 := abs_sub ((z : ℝ) - z') ((y : ℝ) - y')
    have h2 := abs_sub (z : ℝ) z'
    have h3 := abs_sub (y : ℝ) y'
    have h4 := hzb z hz
    have h5 := hzb z' hz'
    have h6 := hyb y hy
    have h7 := hyb y' hy'
    linarith
  have habs : |(|(q : ℝ)| * u - |(m : ℝ)| * v)| ≤ 2 * (v / 100) + 2 * (u / 100) := by
    have h1 : |(q : ℝ)| * u = |(q : ℝ) * u| := by rw [abs_mul, abs_of_pos hur]
    have h2 : |(m : ℝ)| * v = |(m : ℝ) * v| := by rw [abs_mul, abs_of_pos hvr]
    rw [h1, h2]
    refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
    rw [hq, show (m : ℝ) * v + ((z : ℝ) - z') - ((y : ℝ) - y') - (m : ℝ) * v
      = ((z : ℝ) - z') - ((y : ℝ) - y') by ring]
    exact herr
  have hab := abs_le.mp habs
  have hJ1 : ((M * v / u : ℕ) : ℝ) * u ≤ (M : ℝ) * v := by
    have := Nat.div_mul_le_self (M * v) u
    exact_mod_cast this
  have hJ2 : (M : ℝ) * v ≤ (((M * v / u : ℕ) : ℝ) + 1) * u := by
    have h1 := Nat.lt_div_mul_add (a := M * v) W.u_pos
    have h2 : M * v ≤ (M * v / u + 1) * u := by
      have e1 : (M * v / u + 1) * u = M * v / u * u + u := by ring
      omega
    exact_mod_cast h2
  set J : ℝ := ((M * v / u : ℕ) : ℝ) with hJdef
  rw [hnat]
  have hexp : ∀ t : ℝ, (v : ℝ) / u * t * u = v * t := by
    intro t
    field_simp
  constructor
  · refine le_of_mul_le_mul_right ?_ hur
    rw [hexp]
    have e1 : (J - 1 - |(q : ℝ)|) * u = (J + 1) * u - 2 * u - |(q : ℝ)| * u := by ring
    have e2 : (v : ℝ) * ((M : ℝ) - 3 / 100 - |(m : ℝ)|)
        = (M : ℝ) * v - 3 / 100 * v - |(m : ℝ)| * v := by ring
    rw [e1, e2]
    linarith [hab.2]
  · refine le_of_mul_le_mul_right ?_ hur
    rw [hexp]
    have e1 : (J + 2 - |(q : ℝ)|) * u = J * u + 2 * u - |(q : ℝ)| * u := by ring
    have e2 : (v : ℝ) * ((M : ℝ) + 1 - |(m : ℝ)|)
        = (M : ℝ) * v + v - |(m : ℝ)| * v := by ring
    rw [e1, e2]
    linarith [hab.1]

/-- The upper bound for the energy in Fourier form. -/
lemma energy_le : energy (setA M u v Y) (setB M v Z)
    ≤ (v : ℝ) / u * ((1 / (u : ℝ)) * ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
        TwoPrimesFormula.H (M + 1) ((ξ : ℝ) * v / u)) := by
  have hu := W.u_pos
  have hmono := energy_mono W.setA_sub W.setB_sub
  have hIco : Ico 0 (M * v / u + 2) = Ico 0 (0 + (M * v / u + 2)) := by rw [Nat.zero_add]
  rw [hIco, energy_prod u v _ 0 hu _ Y Z W.Y_small W.Z_small, ← range_eq_Ico] at hmono
  refine le_trans hmono ?_
  set Wt : ℤ → ℝ := fun m => (v : ℝ) / u * ((M : ℝ) + 1 - |(m : ℝ)|) with hW
  have hstep : ∀ k ∈ range (M + 1), ∀ k' ∈ range (M + 1),
      (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          count u (M * v / u + 2) (((k : ℤ) - k') * v + (z - z') - (y - y')))
        ≤ Wt ((k : ℤ) - k') * (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))) := by
    intro k hk k' hk'
    have hk1 := mem_range.mp hk
    have hk2 := mem_range.mp hk'
    have hm : |((((k : ℤ) - k' : ℤ)) : ℝ)| ≤ (M : ℝ) := by
      have h1 : |(k : ℤ) - k'| ≤ (M : ℤ) := by rw [abs_le]; omega
      exact_mod_cast h1
    have hW0 : 0 ≤ Wt ((k : ℤ) - k') :=
      mul_nonneg (by positivity) (by linarith)
    simp only [mul_sum]
    refine sum_le_sum fun z hz => sum_le_sum fun z' hz' => sum_le_sum fun y hy =>
      sum_le_sum fun y' hy' => ?_
    unfold count
    by_cases h : (u : ℤ) ∣ ((k : ℤ) - k') * v + (z - z') - (y - y')
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 1 := if_pos h
      rw [hi, one_mul, mul_one]
      have hb := (W.weight_bounds ((k : ℤ) - k') hy hy' hz hz' h).2
      set q := (((k : ℤ) - k') * v + (z - z') - (y - y')) / (u : ℤ)
      by_cases hle : q.natAbs ≤ M * v / u + 2
      · rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_ofNat]
        exact hb
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
        exact hW0
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 0 := if_neg h
      rw [hi, zero_mul, mul_zero]
  refine le_trans (sum_le_sum fun k hk => sum_le_sum fun k' hk' => hstep k hk k' hk') ?_
  rw [fourier u v hu (range (M + 1)) Wt Y Z]
  refine le_of_eq ?_
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [mul_left_comm]
  congr 1
  unfold TwoPrimesFormula.H
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k' _ => ?_
  rw [hW]
  push_cast
  ring

/-- The lower bound for the energy in Fourier form. -/
lemma le_energy :
    (v : ℝ) / u * ((1 / (u : ℝ)) * ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
        (TwoPrimesFormula.H (M - 1) ((ξ : ℝ) * v / u)
          + 97 / 100 * F (M - 1) ((ξ : ℝ) * v / u)))
      ≤ energy (setA M u v Y) (setB M v Z) := by
  have hu := W.u_pos
  have hM := W.hM
  have hJ : 1 ≤ M * v / u := by
    have := W.J_ge
    omega
  have hmono := energy_mono W.sub_setA W.sub_setB
  have hIco : Ico 1 (M * v / u) = Ico 1 (1 + (M * v / u - 1)) := by
    congr 1
    omega
  rw [hIco, energy_prod u v _ 1 hu _ Y Z W.Y_small W.Z_small] at hmono
  refine le_trans ?_ hmono
  set Wt : ℤ → ℝ := fun m => (v : ℝ) / u * ((M : ℝ) - 3 / 100 - |(m : ℝ)|) with hW
  have hstep : ∀ k ∈ Ico 1 M, ∀ k' ∈ Ico 1 M,
      Wt ((k : ℤ) - k') * (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            ind u (((k : ℤ) - k') * v + (z - z') - (y - y')))
        ≤ ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          count u (M * v / u - 1) (((k : ℤ) - k') * v + (z - z') - (y - y')) := by
    intro k _ k' _
    simp only [mul_sum]
    refine sum_le_sum fun z hz => sum_le_sum fun z' hz' => sum_le_sum fun y hy =>
      sum_le_sum fun y' hy' => ?_
    unfold count
    by_cases h : (u : ℤ) ∣ ((k : ℤ) - k') * v + (z - z') - (y - y')
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 1 := if_pos h
      rw [hi, one_mul, mul_one]
      have hb := (W.weight_bounds ((k : ℤ) - k') hy hy' hz hz' h).1
      set q := (((k : ℤ) - k') * v + (z - z') - (y - y')) / (u : ℤ)
      refine le_trans hb ?_
      have h1 : M * v / u - 1 ≤ (M * v / u - 1 - q.natAbs) + q.natAbs := by omega
      have h2 : ((M * v / u - 1 : ℕ) : ℝ) ≤ ((M * v / u - 1 - q.natAbs : ℕ) : ℝ) + (q.natAbs : ℝ) := by
        exact_mod_cast h1
      rw [Nat.cast_sub hJ, Nat.cast_one] at h2
      linarith
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 0 := if_neg h
      rw [hi, zero_mul, mul_zero]
  refine le_trans ?_ (sum_le_sum fun k hk => sum_le_sum fun k' hk' => hstep k hk k' hk')
  rw [fourier u v hu (Ico 1 M) Wt Y Z]
  have hkernel : ∀ θ : ℝ, ∑ k ∈ Ico 1 M, ∑ k' ∈ Ico 1 M, Wt ((k : ℤ) - k') * c θ ((k : ℤ) - k')
      = (v : ℝ) / u * (TwoPrimesFormula.H (M - 1) θ + 97 / 100 * F (M - 1) θ) := by
    intro θ
    have hshift : ∑ k ∈ Ico 1 M, ∑ k' ∈ Ico 1 M, Wt ((k : ℤ) - k') * c θ ((k : ℤ) - k')
        = ∑ k ∈ range (M - 1), ∑ k' ∈ range (M - 1), Wt ((k : ℤ) - k') * c θ ((k : ℤ) - k') := by
      rw [sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k' _ => ?_
      have e1 : (((1 + k : ℕ) : ℤ) - ((1 + k' : ℕ) : ℤ)) = (k : ℤ) - k' := by push_cast; ring
      rw [e1]
    rw [hshift]
    unfold TwoPrimesFormula.H F
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun k' _ => ?_
    simp only [hW, Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    ring
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [hkernel]
  ring

lemma one_le_kappaD : 1 ≤ kappaD M u v Y Z := by
  have hH := H_at_zero_pos M (by have := W.hM; omega)
  have h0 : G u Y Z 0 * (TwoPrimesFormula.H M (((0 : ℕ) : ℝ) * v / u) / TwoPrimesFormula.H M 0) = 1 := by
    rw [W.G_zero, show ((0 : ℕ) : ℝ) * v / u = 0 by simp, div_self hH.ne', mul_one]
  unfold kappaD
  rw [← h0]
  exact single_le_sum
    (f := fun ξ => G u Y Z ξ * (TwoPrimesFormula.H M ((ξ : ℝ) * v / u) / TwoPrimesFormula.H M 0))
    (fun ξ _ => mul_nonneg (W.G_nonneg ξ) (div_nonneg (H_nonneg _ _) hH.le))
    (mem_range.mpr W.u_pos)

lemma sum_H_eq : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u)
    = TwoPrimesFormula.H M 0 * kappaD M u v Y Z := by
  have hH := H_at_zero_pos M (by have := W.hM; omega)
  have hH' := hH.ne'
  unfold kappaD
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  field_simp

lemma C_form (a T b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 * ((M : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))) / ((a * Y.card) * (b * Z.card)) ^ 2
      = (2 * ((M : ℝ) * v) + 1) * v * T / ((u : ℝ) ^ 2 * a ^ 2 * b ^ 2) := by
  have h1 := W.Y_card_pos.ne'
  have h2 : (Z.card : ℝ) ≠ 0 := by have := W.Z_card_ge; linarith
  have h3 : (u : ℝ) ≠ 0 := by have := W.u_pos; positivity
  field_simp

lemma C_upper (T : ℝ) (hT : 0 ≤ T)
    (hE : energy (setA M u v Y) (setB M v Z) ≤ (v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))) :
    C M u v Y Z ≤ (2 + 1 / ((M : ℝ) * v)) * T / ((M : ℝ) ^ 3 * (1 - 2 * u / ((M : ℝ) * v)) ^ 2) := by
  have hur : (0 : ℝ) < u := by exact_mod_cast W.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast W.v_pos
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast W.hM
  have hM0 : (0 : ℝ) < M := by linarith
  have huv : 2000 * (u : ℝ) ≤ v := by exact_mod_cast W.uv
  have hY := W.Y_card_pos
  have hZ := W.Z_card_ge
  set r : ℝ := (M : ℝ) * v / u with hr
  have hr20 : 2000 * (M : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ hur]
    have := mul_le_mul_of_nonneg_left huv hM0.le
    linarith
  have hr2 : 2 < r := by linarith
  have hJ : r - 1 ≤ ((M * v / u : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := M * v) W.u_pos
    have h2 : M * v ≤ (M * v / u + 1) * u := by
      have e1 : (M * v / u + 1) * u = M * v / u * u + u := by ring
      omega
    have h3 : (M : ℝ) * v ≤ (((M * v / u : ℕ) : ℝ) + 1) * u := by exact_mod_cast h2
    rw [hr, sub_le_iff_le_add, div_le_iff₀ hur]
    exact h3
  have hA : (r - 2) * Y.card ≤ ((setA M u v Y).card : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hY.le) W.card_setA_lower
    linarith
  have hB : (M : ℝ) * Z.card ≤ ((setB M v Z).card : ℝ) := by
    rw [W.card_setB]
    push_cast
    linarith
  have hlow : 0 < ((r - 2) * Y.card) * ((M : ℝ) * Z.card) := by
    have : (0 : ℝ) < Z.card := by linarith
    have : 0 < r - 2 := by linarith
    positivity
  have hprod : ((r - 2) * Y.card) * ((M : ℝ) * Z.card)
      ≤ ((setA M u v Y).card : ℝ) * ((setB M v Z).card : ℝ) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have h1 : C M u v Y Z ≤ (2 * ((M : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)))
      / (((r - 2) * Y.card) * ((M : ℝ) * Z.card)) ^ 2 := by
    unfold TwoPrimesFormula.C
    refine div_le_div₀ ?_ (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
      (pow_le_pow_left₀ hlow.le hprod 2)
    have : 0 ≤ (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)) := by
      positivity
    positivity
  refine le_trans h1 (le_of_eq ?_)
  rw [W.C_form (r - 2) T (M : ℝ) (by linarith) hM0.ne']
  have h2 : r - 2 ≠ 0 := by linarith
  have h3 : (M : ℝ) * v - 2 * u ≠ 0 := by
    have : 2 * (u : ℝ) < (M : ℝ) * v := by
      have h4 : r * u = (M : ℝ) * v := by rw [hr]; field_simp
      have h5 := mul_lt_mul_of_pos_right hr2 hur
      linarith
    linarith
  rw [hr]
  field_simp

lemma C_lower (T : ℝ) (hT : 0 ≤ T)
    (hE : (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))
      ≤ energy (setA M u v Y) (setB M v Z)) :
    2 * T / ((M : ℝ) ^ 3 * (1 + 2 * u / ((M : ℝ) * v)) ^ 2 * (1 + 1 / ((M : ℝ) * Z.card)) ^ 2)
      ≤ C M u v Y Z := by
  have hur : (0 : ℝ) < u := by exact_mod_cast W.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast W.v_pos
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast W.hM
  have hM0 : (0 : ℝ) < M := by linarith
  have huv : 2000 * (u : ℝ) ≤ v := by exact_mod_cast W.uv
  have hY := W.Y_card_pos
  have hZ := W.Z_card_ge
  have hZ0 : (0 : ℝ) < Z.card := by linarith
  set r : ℝ := (M : ℝ) * v / u with hr
  have hr20 : 2000 * (M : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ hur]
    have := mul_le_mul_of_nonneg_left huv hM0.le
    linarith
  have hr0 : 0 < r := by linarith
  have hJ : ((M * v / u : ℕ) : ℝ) ≤ r := by
    have h1 := Nat.div_mul_le_self (M * v) u
    have h2 : ((M * v / u : ℕ) : ℝ) * u ≤ (M : ℝ) * v := by exact_mod_cast h1
    rw [hr, le_div_iff₀ hur]
    exact h2
  have hA : ((setA M u v Y).card : ℝ) ≤ (r + 2) * Y.card := by
    refine le_trans W.card_setA_upper (mul_le_mul_of_nonneg_right ?_ hY.le)
    linarith
  have hB : ((setB M v Z).card : ℝ) = ((M : ℝ) + 1 / Z.card) * Z.card := by
    rw [W.card_setB]
    push_cast
    field_simp
  have hApos : (0 : ℝ) < (setA M u v Y).card := by
    have h1 := W.card_setA_lower
    have h2 : (1 : ℝ) < ((M * v / u : ℕ) : ℝ) := by
      have h3 : 2 ≤ M * v / u := by
        have h4 := W.J_ge
        have := W.hM
        omega
      have h7 : (2 : ℝ) ≤ ((M * v / u : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    exact lt_of_lt_of_le (mul_pos (by linarith) hY) h1
  have hBpos : (0 : ℝ) < (setB M v Z).card := by
    rw [hB]
    have : (0 : ℝ) < (M : ℝ) + 1 / Z.card := by positivity
    positivity
  have hprod : ((setA M u v Y).card : ℝ) * ((setB M v Z).card : ℝ)
      ≤ ((r + 2) * Y.card) * (((M : ℝ) + 1 / Z.card) * Z.card) := by
    rw [hB]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  have h1 : (2 * ((M : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)))
      / (((r + 2) * Y.card) * (((M : ℝ) + 1 / Z.card) * Z.card)) ^ 2 ≤ C M u v Y Z := by
    unfold TwoPrimesFormula.C
    refine div_le_div₀ ?_ (mul_le_mul_of_nonneg_left hE (by positivity))
      (pow_pos (mul_pos hApos hBpos) 2)
      (pow_le_pow_left₀ (mul_nonneg hApos.le hBpos.le) hprod 2)
    have : 0 ≤ energy (setA M u v Y) (setB M v Z) := by
      refine le_trans ?_ hE
      positivity
    positivity
  refine le_trans ?_ h1
  have hb : (M : ℝ) + 1 / Z.card ≠ 0 := by
    have : (0 : ℝ) < (M : ℝ) + 1 / Z.card := by positivity
    exact this.ne'
  rw [W.C_form (r + 2) T ((M : ℝ) + 1 / Z.card) (by linarith) hb]
  have e1 : 2 * T / ((M : ℝ) ^ 3 * (1 + 2 * u / ((M : ℝ) * v)) ^ 2 * (1 + 1 / ((M : ℝ) * Z.card)) ^ 2)
      = (2 * ((M : ℝ) * v)) * v * T / ((u : ℝ) ^ 2 * (r + 2) ^ 2 * ((M : ℝ) + 1 / Z.card) ^ 2) := by
    have h2 : (M : ℝ) * v + 2 * u ≠ 0 := by positivity
    have h3 : (M : ℝ) * Z.card + 1 ≠ 0 := by positivity
    rw [hr]
    field_simp
  rw [e1]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hvr.le) hT
  linarith

lemma small_terms :
    1 / ((M : ℝ) * v) ≤ 1 / (M : ℝ) / 2000 ∧ 2 * u / ((M : ℝ) * v) ≤ 1 / (M : ℝ) / 1000
      ∧ 0 ≤ 2 * u / ((M : ℝ) * v) := by
  have hur : (0 : ℝ) < u := by exact_mod_cast W.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast W.v_pos
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast W.u_pos
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast W.hM
  have hM0 : (0 : ℝ) < M := by linarith
  have huv : 2000 * (u : ℝ) ≤ v := by exact_mod_cast W.uv
  refine ⟨?_, ?_, by positivity⟩
  · rw [div_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    linarith
  · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left huv hM0.le
    linarith

end Wide

/-- `(N - 1) F_N ≤ 2 K_N`: one block carries at most this share of the kernel. -/
lemma F_le_H (N : ℕ) (θ : ℝ) (hN : 1 ≤ N) :
    ((N : ℝ) - 1) * F N θ ≤ 2 * TwoPrimesFormula.H N θ := by
  have h2sum : 2 * (∑ j ∈ range N, F j θ) ≤ TwoPrimesFormula.H N θ := by
    rw [H_eq]; have := F_nonneg N θ; linarith
  have h1 : ∑ _a ∈ Ico 1 N, F N θ ≤ ∑ a ∈ Ico 1 N, 2 * (F a θ + F (N - a) θ) := by
    refine sum_le_sum fun a ha => ?_
    have ha' := mem_Ico.mp ha
    have e1 : a + (N - a) = N := by omega
    calc F N θ = F (a + (N - a)) θ := by rw [e1]
      _ ≤ _ := F_add_le _ _ _
  have h3 : ∑ a ∈ Ico 1 N, F (N - a) θ = ∑ a ∈ Ico 1 N, F a θ := by
    refine sum_nbij' (fun a => N - a) (fun a => N - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a _; rfl
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, ← mul_sum, sum_add_distrib, h3,
    Nat.cast_sub hN, Nat.cast_one] at h1
  have h4 : ∑ j ∈ Ico 1 N, F j θ ≤ ∑ j ∈ range N, F j θ :=
    sum_le_sum_of_subset_of_nonneg (fun a ha => mem_range.mpr (mem_Ico.mp ha).2)
      fun j _ _ => F_nonneg j θ
  linarith

namespace Wide
end Wide

variable {M u v : ℕ} {Y Z : Finset ℤ}

set_option maxHeartbeats 2000000 in
/-- **The two-sided formula for `M` top clusters.** -/
theorem energy_formula_multiple (W : Wide M u v Y Z) :
    (1 - 5 / (M : ℝ)) * (4 / 3) * kappaD M u v Y Z ≤ C M u v Y Z ∧
      C M u v Y Z ≤ (1 + 5 / (M : ℝ)) * (4 / 3) * kappaD M u v Y Z := by
  have hur : (0 : ℝ) < u := by exact_mod_cast W.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast W.v_pos
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast W.hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hM3 : 3 ≤ M := by have := W.hM; omega
  have hκ := W.one_le_kappaD
  have hκ0 : 0 ≤ kappaD M u v Y Z := by linarith
  have hH0 := H_at_zero_pos M (by omega)
  obtain ⟨hs1, hs2, hs3⟩ := W.small_terms
  set x : ℝ := 1 / M with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hMr
  have h5M : 5 / (M : ℝ) = 5 * x := by rw [hx]; ring
  have hxx : x ^ 2 ≤ x / 100 := by nlinarith
  have hK : TwoPrimesFormula.H M 0 / (M : ℝ) ^ 3 = 2 / 3 * (1 + x ^ 2 / 2) := by
    rw [H_at_zero, hx]
    field_simp
  set T := TwoPrimesFormula.H M 0 * kappaD M u v Y Z with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hH0.le hκ0
  have hsum : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u) = T := W.sum_H_eq
  have hTD : T / (M : ℝ) ^ 3 = 2 / 3 * (1 + x ^ 2 / 2) * kappaD M u v Y Z := by
    rw [hTdef, mul_div_right_comm, hK]
  constructor
  · -- lower bound
    set a : ℝ := 1 - 21 / 10 * x with ha
    have ha0 : 0 ≤ a := by linarith
    have hker : ∀ θ : ℝ, a * TwoPrimesFormula.H M θ
        ≤ TwoPrimesFormula.H (M - 1) θ + 97 / 100 * F (M - 1) θ := by
      intro θ
      have hs := H_succ (M - 1) θ
      rw [Nat.sub_add_cancel (by omega : 1 ≤ M)] at hs
      have hK0 := H_nonneg M θ
      have hF1 := F_le_H M θ (by omega)
      have hF2 := F_le_H (M - 1) θ (by omega)
      rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one] at hF2
      have hmon : TwoPrimesFormula.H (M - 1) θ ≤ TwoPrimesFormula.H M θ := by
        have h1 := F_nonneg (M - 1) θ
        have h2 := F_nonneg M θ
        linarith
      have hd1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      have hd2 : (0 : ℝ) < (M : ℝ) - 2 := by linarith
      have e1 : F M θ ≤ 2 / ((M : ℝ) - 1) * TwoPrimesFormula.H M θ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hd1, mul_comm (F M θ)]
        exact hF1
      have e2 : F (M - 1) θ ≤ 2 / ((M : ℝ) - 2) * TwoPrimesFormula.H M θ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hd2, mul_comm (F (M - 1) θ)]
        have h3 : (M : ℝ) - 1 - 1 = (M : ℝ) - 2 := by ring
        rw [h3] at hF2
        linarith
      have hnum : 2 / ((M : ℝ) - 1) + 3 / 100 * (2 / ((M : ℝ) - 2)) ≤ 21 / 10 * x := by
        have h4 : 21 / 10 * x = (21 / 10) / (M : ℝ) := by rw [hx]; ring
        have h5 : 2 / ((M : ℝ) - 1) + 3 / 100 * (2 / ((M : ℝ) - 2))
            = (2 * ((M : ℝ) - 2) + 6 / 100 * ((M : ℝ) - 1)) / (((M : ℝ) - 1) * ((M : ℝ) - 2)) := by
          field_simp
          ring
        rw [h4, h5, div_le_div_iff₀ (mul_pos hd1 hd2) hM0]
        nlinarith
      have h6 := mul_le_mul_of_nonneg_right hnum hK0
      have h7 : (2 / ((M : ℝ) - 1) + 3 / 100 * (2 / ((M : ℝ) - 2))) * TwoPrimesFormula.H M θ
          = 2 / ((M : ℝ) - 1) * TwoPrimesFormula.H M θ
            + 3 / 100 * (2 / ((M : ℝ) - 2) * TwoPrimesFormula.H M θ) := by ring
      rw [ha]
      linarith
    have hE : (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (a * T)))
        ≤ energy (setA M u v Y) (setB M v Z) := by
      refine le_trans ?_ W.le_energy
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      rw [W.sum_power]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hsum, mul_sum]
      refine sum_le_sum fun ξ _ => ?_
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hker _) (W.G_nonneg ξ)
    have h1 := W.C_lower (a * T) (mul_nonneg ha0 hT0) hE
    refine le_trans ?_ h1
    have hZ1 := W.Z_card_ge
    set p : ℝ := 1 + 2 * u / ((M : ℝ) * v) with hp
    set q : ℝ := 1 + 1 / ((M : ℝ) * Z.card) with hq
    have hp1 : p ≤ 1 + x / 1000 := by linarith
    have hp0 : 0 < p := by linarith
    have hq1 : q ≤ 1 + x := by
      have h2 : 1 / ((M : ℝ) * Z.card) ≤ x := by
        rw [hx]
        refine one_div_le_one_div_of_le hM0 ?_
        have := mul_le_mul_of_nonneg_left hZ1 hM0.le
        linarith
      linarith
    have hq0 : 0 < q := by
      have : (0 : ℝ) ≤ 1 / ((M : ℝ) * Z.card) := by positivity
      linarith
    have hmain : (1 - 5 * x) * (p ^ 2 * q ^ 2) ≤ a := by
      have h2 : p * q ≤ 1 + 102 / 100 * x := by
        refine le_trans (mul_le_mul hp1 hq1 hq0.le (by linarith)) ?_
        nlinarith
      have h3 : p ^ 2 * q ^ 2 ≤ 1 + 21 / 10 * x := by
        have e1 : p ^ 2 * q ^ 2 = (p * q) ^ 2 := by ring
        rw [e1]
        refine le_trans (pow_le_pow_left₀ (mul_nonneg hp0.le hq0.le) h2 2) ?_
        nlinarith
      have h4 : (0 : ℝ) ≤ 1 - 5 * x := by linarith
      refine le_trans (mul_le_mul_of_nonneg_left h3 h4) ?_
      rw [ha]
      nlinarith
    have hden : (0 : ℝ) < (M : ℝ) ^ 3 * p ^ 2 * q ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    have hTD' : T = 2 / 3 * (1 + x ^ 2 / 2) * kappaD M u v Y Z * (M : ℝ) ^ 3 := by
      rw [← hTD]
      field_simp
    have h6 : (1 - 5 * x) * (p ^ 2 * q ^ 2) * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3)
        ≤ a * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    have h7 : a * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3) ≤ 2 * (a * T) := by
      have h8 : 0 ≤ a * kappaD M u v Y Z * (M : ℝ) ^ 3 * x ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg ha0 hκ0) (by positivity)) (sq_nonneg _)
      have e1 : 2 * (a * T) = a * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3)
          + 2 / 3 * (a * kappaD M u v Y Z * (M : ℝ) ^ 3 * x ^ 2) := by
        rw [hTD']; ring
      linarith
    have e2 : (1 - 5 / (M : ℝ)) * (4 / 3) * kappaD M u v Y Z * ((M : ℝ) ^ 3 * p ^ 2 * q ^ 2)
        = (1 - 5 * x) * (p ^ 2 * q ^ 2) * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3) := by
      rw [h5M]; ring
    rw [e2]
    exact le_trans h6 h7
  · -- upper bound
    set b : ℝ := 1 + 4 / ((M : ℝ) - 2) with hb
    have hd2 : (0 : ℝ) < (M : ℝ) - 2 := by linarith
    have hb0 : 0 ≤ b := by
      have : (0 : ℝ) ≤ 4 / ((M : ℝ) - 2) := div_nonneg (by norm_num) hd2.le
      linarith
    have hE : energy (setA M u v Y) (setB M v Z) ≤ (v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (b * T))) := by
      refine le_trans W.energy_le ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      rw [W.sum_power]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hsum, mul_sum]
      refine sum_le_sum fun ξ _ => ?_
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (H_succ_le M hM3 _) (W.G_nonneg ξ)
    have h1 := W.C_upper (b * T) (mul_nonneg hb0 hT0) hE
    refine le_trans h1 ?_
    set p : ℝ := 1 - 2 * u / ((M : ℝ) * v) with hp
    have hp1 : 1 - x / 1000 ≤ p := by linarith
    have hp0 : 0 < p := by linarith
    have hbval : b ≤ 1 + 409 / 100 * x := by
      have h2 : 4 / ((M : ℝ) - 2) ≤ 409 / 100 * x := by
        have e1 : 409 / 100 * x = (409 / 100) / M := by rw [hx]; ring
        rw [e1, div_le_div_iff₀ hd2 hM0]
        linarith
      linarith
    have hpinv : 1 ≤ (1 + x / 100) * p ^ 2 := by
      have h2 : (1 - x / 1000) ^ 2 ≤ p ^ 2 := by
        refine pow_le_pow_left₀ ?_ hp1 2
        linarith
      have h3 : 1 ≤ (1 + x / 100) * (1 - x / 1000) ^ 2 := by
        have h4 : 1 - x / 500 ≤ (1 - x / 1000) ^ 2 := by nlinarith [sq_nonneg x]
        have h5 : 1 ≤ (1 + x / 100) * (1 - x / 500) := by nlinarith
        exact le_trans h5 (mul_le_mul_of_nonneg_left h4 (by linarith))
      exact le_trans h3 (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hA : 2 + 1 / ((M : ℝ) * v) ≤ 2 * (1 + x / 200) := by linarith
    have hden : (0 : ℝ) < (M : ℝ) ^ 3 * p ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hTD' : T = 2 / 3 * (1 + x ^ 2 / 2) * kappaD M u v Y Z * (M : ℝ) ^ 3 := by
      rw [← hTD]
      field_simp
    have hN := num_upper x hx0 hx1
    have hK2 : 1 + x ^ 2 / 2 ≤ 1 + x / 200 := by linarith
    have h6 : (2 + 1 / ((M : ℝ) * v)) * (b * T)
        ≤ (2 * (1 + x / 200)) * ((1 + 409 / 100 * x)
            * (2 / 3 * (1 + x / 200) * kappaD M u v Y Z * (M : ℝ) ^ 3)) := by
      refine mul_le_mul hA (mul_le_mul hbval ?_ hT0 (by linarith)) (mul_nonneg hb0 hT0)
        (by linarith)
      rw [hTD']
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hκ0) (by positivity)
      linarith
    have h7 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) ≤ (1 + 5 * x) * p ^ 2 := by
      have h8 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * 1
          ≤ (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * ((1 + x / 100) * p ^ 2) :=
        mul_le_mul_of_nonneg_left hpinv (by positivity)
      have h9 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * (1 + x / 100) * p ^ 2
          ≤ (1 + 5 * x) * p ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg _)
      linarith
    have h10 := mul_le_mul_of_nonneg_right h7
      (show 0 ≤ (4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3 by positivity)
    have e2 : (1 + 5 / (M : ℝ)) * (4 / 3) * kappaD M u v Y Z * ((M : ℝ) ^ 3 * p ^ 2)
        = (1 + 5 * x) * p ^ 2 * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3) := by
      rw [h5M]; ring
    have e3 : (2 * (1 + x / 200)) * ((1 + 409 / 100 * x)
          * (2 / 3 * (1 + x / 200) * kappaD M u v Y Z * (M : ℝ) ^ 3))
        = (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x)
          * ((4 / 3) * kappaD M u v Y Z * (M : ℝ) ^ 3) := by ring
    rw [e2]
    rw [e3] at h6
    exact le_trans h6 h10

/-- A fixed bound below `69/40` suffices when `M` is large enough. -/
theorem energy_of_kappa_lt (W : Wide M u v Y Z) (K : ℝ) (h : kappaD M u v Y Z ≤ K)
    (hM : 200 * K ≤ (M : ℝ) * (69 - 40 * K)) : C M u v Y Z ≤ 23 / 10 := by
  have h1 := (energy_formula_multiple W).2
  have h3 := W.one_le_kappaD
  have hMr : (100 : ℝ) ≤ M := by exact_mod_cast W.hM
  have hM0 : (0 : ℝ) < M := by linarith
  have h4 : (0 : ℝ) ≤ 5 / (M : ℝ) := by positivity
  have h5 : (1 + 5 / (M : ℝ)) * (4 / 3) * kappaD M u v Y Z ≤ (1 + 5 / (M : ℝ)) * (4 / 3) * K :=
    mul_le_mul_of_nonneg_left h (mul_nonneg (by linarith) (by norm_num))
  have h6 : (1 + 5 / (M : ℝ)) * (4 / 3) * K ≤ 23 / 10 := by
    have e : (1 + 5 / (M : ℝ)) * (4 / 3) * K = (4 * ((M : ℝ) + 5) * K) / (3 * M) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ## The transfer between block lengths -/

/-- `Σ_{k<j} w(r - k a)`. -/
def blk {u : ℕ} (a : ZMod u) (w : ZMod u → ℝ) (j : ℕ) (r : ZMod u) : ℝ :=
  ∑ k ∈ range j, w (r - (k : ZMod u) * a)

theorem blk_transfer {u : ℕ} [NeZero u] (a : ZMod u) (w : ZMod u → ℝ) (hw : ∀ r, 0 ≤ w r)
    (j H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ) ^ 2 * ∑ r, blk a w j r ^ 2 ≤ ((j + H - 1 : ℕ) : ℝ) ^ 2 * ∑ r, blk a w H r ^ 2 := by
  set n := j + H - 1 with hn
  -- the shifted block starting at `s - (H - 1)`
  set c : ℕ → ZMod u := fun s => ((s : ZMod u) - ((H - 1 : ℕ) : ZMod u)) * a with hc
  have hcover : ∀ r, (H : ℝ) * blk a w j r ≤ ∑ s ∈ range n, blk a w H (r - c s) := by
    intro r
    have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 + (H - 1) - p.2, p.2))
        ((range j ×ˢ range H : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro p hp p' hp' h
      rw [coe_product, Set.mem_prod, mem_coe, mem_coe, mem_range, mem_range] at hp hp'
      simp only [Prod.mk.injEq] at h
      refine Prod.ext ?_ h.2
      omega
    have hsub : (range j ×ˢ range H).image (fun p : ℕ × ℕ => (p.1 + (H - 1) - p.2, p.2))
        ⊆ range n ×ˢ range H := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      rw [mem_product, mem_range, mem_range] at hp ⊢
      refine ⟨?_, hp.2⟩
      simp only
      omega
    have hsum := sum_le_sum_of_subset_of_nonneg
      (f := fun q : ℕ × ℕ => w (r - c q.1 - (q.2 : ZMod u) * a)) hsub (fun q _ _ => hw _)
    rw [sum_image hinj] at hsum
    have hleft : ∑ p ∈ range j ×ˢ range H,
          w (r - c (p.1 + (H - 1) - p.2) - (p.2 : ZMod u) * a)
        = (H : ℝ) * blk a w j r := by
      rw [sum_product]
      unfold blk
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      have hterm : ∀ i ∈ range H, w (r - c (k + (H - 1) - i) - (i : ZMod u) * a)
          = w (r - (k : ZMod u) * a) := by
        intro i hi
        have hi' := mem_range.mp hi
        congr 1
        have hcast : ((k + (H - 1) - i : ℕ) : ZMod u)
            = (k : ZMod u) + ((H - 1 : ℕ) : ZMod u) - (i : ZMod u) := by
          rw [Nat.cast_sub (by omega : i ≤ k + (H - 1)), Nat.cast_add]
        simp only [hc]
        rw [hcast]
        ring
      rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
    rw [hleft] at hsum
    refine le_trans hsum (le_of_eq ?_)
    rw [sum_product]
    rfl
  have hsq : ∀ r, ((H : ℝ) * blk a w j r) ^ 2 ≤ (n : ℝ) * ∑ s ∈ range n, blk a w H (r - c s) ^ 2 := by
    intro r
    have h0 : 0 ≤ (H : ℝ) * blk a w j r :=
      mul_nonneg (by positivity) (sum_nonneg fun k _ => hw _)
    have h1 := pow_le_pow_left₀ h0 (hcover r) 2
    have h2 := sq_sum_le_card_mul_sum_sq (s := range n) (f := fun s => blk a w H (r - c s))
    rw [card_range] at h2
    exact le_trans h1 h2
  have htrans : ∀ s, ∑ r, blk a w H (r - c s) ^ 2 = ∑ r, blk a w H r ^ 2 := by
    intro s
    exact Equiv.sum_comp (Equiv.subRight (c s)) (fun r => blk a w H r ^ 2)
  have h := sum_le_sum (s := univ) fun r (_ : r ∈ univ) => hsq r
  have e1 : ∑ r, ((H : ℝ) * blk a w j r) ^ 2 = (H : ℝ) ^ 2 * ∑ r, blk a w j r ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have e2 : ∑ r, (n : ℝ) * ∑ s ∈ range n, blk a w H (r - c s) ^ 2
      = (n : ℝ) ^ 2 * ∑ r, blk a w H r ^ 2 := by
    rw [← mul_sum, sum_comm, sum_congr rfl fun s _ => htrans s, sum_const, card_range,
      nsmul_eq_mul]
    ring
  rw [e1, e2] at h
  exact h

/-- The number of pairs `(y, z)` with `z - y ≡ r`. -/
def wt (u : ℕ) (Y Z : Finset ℤ) (r : ZMod u) : ℝ :=
  ∑ y ∈ Y, ∑ z ∈ Z, if ((z - y : ℤ) : ZMod u) = r then 1 else 0

/-- `P_j = Σ_ξ G(ξ) F_j(ξ v / u)`. -/
noncomputable def P (u v : ℕ) (Y Z : Finset ℤ) (j : ℕ) : ℝ :=
  ∑ ξ ∈ range u, G u Y Z ξ * F j ((ξ : ℝ) * v / u)

lemma sum_blk_sq (u v : ℕ) [NeZero u] (Y Z : Finset ℤ) (j : ℕ) :
    ∑ r, blk (v : ZMod u) (wt u Y Z) j r ^ 2
      = ∑ k ∈ range j, ∑ k' ∈ range j, ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) := by
  set I : Finset (ℕ × ℤ × ℤ) := range j ×ˢ Y ×ˢ Z with hI
  set val : ℕ × ℤ × ℤ → ZMod u := fun p => (((p.1 : ℤ) * v + p.2.2 - p.2.1 : ℤ) : ZMod u) with hval
  have hblk : ∀ r, blk (v : ZMod u) (wt u Y Z) j r = ∑ p ∈ I, if val p = r then (1 : ℝ) else 0 := by
    intro r
    rw [hI, sum_product]
    unfold blk wt
    refine sum_congr rfl fun k _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    refine if_congr ?_ rfl rfl
    simp only [hval]
    constructor
    · intro h
      push_cast at h ⊢
      linear_combination h
    · intro h
      push_cast at h ⊢
      linear_combination h
  have hsq : ∑ r, blk (v : ZMod u) (wt u Y Z) j r ^ 2
      = ∑ p ∈ I, ∑ p' ∈ I, if val p = val p' then (1 : ℝ) else 0 := by
    have h1 : ∀ r, blk (v : ZMod u) (wt u Y Z) j r ^ 2
        = ∑ p ∈ I, ∑ p' ∈ I, (if val p = r then (1 : ℝ) else 0) * (if val p' = r then 1 else 0) := by
      intro r
      rw [hblk, sq, sum_mul_sum]
    rw [sum_congr rfl fun r _ => h1 r, sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun p' _ => ?_
    rw [sum_eq_single (val p)]
    · rw [if_pos rfl, one_mul]
      exact if_congr eq_comm rfl rfl
    · intro r _ hr
      rw [if_neg (Ne.symm hr), zero_mul]
    · intro h
      exact absurd (mem_univ _) h
  have hind : ∀ p p' : ℕ × ℤ × ℤ, (if val p = val p' then (1 : ℝ) else 0)
      = ind u (((p.1 : ℤ) - p'.1) * v + (p.2.2 - p'.2.2) - (p.2.1 - p'.2.1)) := by
    intro p p'
    unfold ind
    refine if_congr ?_ rfl rfl
    simp only [hval]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← sub_eq_zero]
    constructor
    · intro h
      push_cast at h ⊢
      linear_combination h
    · intro h
      push_cast at h ⊢
      linear_combination h
  rw [hsq]
  simp only [hind]
  rw [hI, sum_product]
  refine sum_congr rfl fun k _ => ?_
  simp only [sum_product]
  have step : ∀ y ∈ Y, ∑ z ∈ Z, ∑ k' ∈ range j, ∑ y' ∈ Y, ∑ z' ∈ Z,
        ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))
      = ∑ k' ∈ range j, ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y' ∈ Y,
        ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) := by
    intro y _
    rw [sum_comm]
    refine sum_congr rfl fun k' _ => sum_congr rfl fun z _ => ?_
    rw [sum_comm]
  rw [sum_congr rfl step, sum_comm]
  refine sum_congr rfl fun k' _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_comm]

/-- The Fourier form of `Σ_r blk²`. -/
lemma sum_blk_fourier (u v : ℕ) [NeZero u] (Y Z : Finset ℤ) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (j : ℕ) :
    ∑ r, blk (v : ZMod u) (wt u Y Z) j r ^ 2
      = (1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * P u v Y Z j) := by
  have hu : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  rw [sum_blk_sq]
  have h := fourier u v hu (range j) (fun _ => (1 : ℝ)) Y Z
  simp only [one_mul] at h
  rw [h]
  congr 1
  unfold P
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  have hYc : (Y.card : ℝ) ≠ 0 := by
    have := hY.card_pos
    positivity
  have hZc : (Z.card : ℝ) ≠ 0 := by
    have := hZ.card_pos
    positivity
  have hG : power u Y ξ * power u Z ξ = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * G u Y Z ξ := by
    unfold G
    field_simp
  rw [hG]
  unfold F
  ring

/-- **Transfer between block lengths.** -/
theorem block_transfer (u v : ℕ) (hu : 0 < u) (Y Z : Finset ℤ) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (j H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ) ^ 2 * P u v Y Z j ≤ ((j + H - 1 : ℕ) : ℝ) ^ 2 * P u v Y Z H := by
  haveI : NeZero u := ⟨hu.ne'⟩
  have hw : ∀ r : ZMod u, 0 ≤ wt u Y Z r := by
    intro r
    unfold wt
    refine sum_nonneg fun y _ => sum_nonneg fun z _ => ?_
    split <;> norm_num
  have h := blk_transfer (v : ZMod u) (wt u Y Z) hw j H hH
  rw [sum_blk_fourier u v Y Z hY hZ, sum_blk_fourier u v Y Z hY hZ] at h
  have hc : (0 : ℝ) < (1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2) := by
    have h1 := hY.card_pos
    have h2 := hZ.card_pos
    positivity
  refine le_of_mul_le_mul_left ?_ hc
  have e1 : (1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2) * ((H : ℝ) ^ 2 * P u v Y Z j)
      = (H : ℝ) ^ 2 * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * P u v Y Z j)) := by
    ring
  have e2 : (1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2)
        * (((j + H - 1 : ℕ) : ℝ) ^ 2 * P u v Y Z H)
      = ((j + H - 1 : ℕ) : ℝ) ^ 2
        * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * P u v Y Z H)) := by
    ring
  rw [e1, e2]
  exact h

lemma sum_shift_sq (M h : ℕ) :
    2 * (∑ j ∈ range M, ((j : ℝ) + h) ^ 2) + ((M : ℝ) + h) ^ 2
      = TwoPrimesFormula.H M 0 + 2 * h * (M : ℝ) ^ 2 + (h : ℝ) ^ 2 * (2 * M + 1) := by
  rw [H_at_zero]
  induction M with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih

/-- **`κ_M` is controlled by any block length `H`.** -/
theorem kappa_transfer (u v : ℕ) (hu : 0 < u) (Y Z : Finset ℤ) (hY : Y.Nonempty) (hZ : Z.Nonempty)
    (M H : ℕ) (hM : 1 ≤ M) (hH : 1 ≤ H) :
    kappaD M u v Y Z ≤ (1 + 3 * ((H : ℝ) - 1) / M + 4 * ((H : ℝ) - 1) ^ 2 / (M : ℝ) ^ 2)
      * (P u v Y Z H / (H : ℝ) ^ 2) := by
  obtain ⟨h, hh⟩ : ∃ h, H = h + 1 := ⟨H - 1, by omega⟩
  have hHr : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hh' : (H : ℝ) - 1 = h := by rw [hh]; push_cast; ring
  set Q : ℝ := P u v Y Z H / (H : ℝ) ^ 2 with hQ
  have hGnn : ∀ ξ, 0 ≤ G u Y Z ξ := by
    intro ξ
    unfold G
    exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _)) (by positivity)
  have hQ0 : 0 ≤ Q := by
    refine div_nonneg ?_ (by positivity)
    exact sum_nonneg fun ξ _ => mul_nonneg (hGnn ξ) (F_nonneg _ _)
  have hPj : ∀ j : ℕ, P u v Y Z j ≤ ((j : ℝ) + h) ^ 2 * Q := by
    intro j
    have h1 := block_transfer u v hu Y Z hY hZ j H hH
    have e : ((j + H - 1 : ℕ) : ℝ) = (j : ℝ) + h := by
      rw [show j + H - 1 = j + h by omega]
      push_cast
      ring
    rw [e] at h1
    rw [hQ, mul_div_assoc', le_div_iff₀ (by positivity), mul_comm]
    exact h1
  have hH0 := H_at_zero_pos M hM
  have hsum : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u)
      = 2 * (∑ j ∈ range M, P u v Y Z j) + P u v Y Z M := by
    unfold P
    simp only [H_eq]
    have e : ∀ ξ ∈ range u, G u Y Z ξ * (2 * (∑ j ∈ range M, F j ((ξ : ℝ) * v / u))
          + F M ((ξ : ℝ) * v / u))
        = (∑ j ∈ range M, 2 * (G u Y Z ξ * F j ((ξ : ℝ) * v / u)))
          + G u Y Z ξ * F M ((ξ : ℝ) * v / u) := by
      intro ξ _
      rw [mul_add, mul_sum, mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl e, sum_add_distrib]
    congr 1
    rw [sum_comm, mul_sum]
    exact sum_congr rfl fun j _ => by rw [mul_sum]
  have hbound : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u)
      ≤ (TwoPrimesFormula.H M 0 + 2 * h * (M : ℝ) ^ 2 + (h : ℝ) ^ 2 * (2 * M + 1)) * Q := by
    rw [hsum, ← sum_shift_sq M h]
    have h1 : ∑ j ∈ range M, P u v Y Z j ≤ (∑ j ∈ range M, ((j : ℝ) + h) ^ 2) * Q := by
      rw [sum_mul]
      exact sum_le_sum fun j _ => hPj j
    have h2 := hPj M
    have e : (2 * (∑ j ∈ range M, ((j : ℝ) + h) ^ 2) + ((M : ℝ) + h) ^ 2) * Q
        = 2 * ((∑ j ∈ range M, ((j : ℝ) + h) ^ 2) * Q) + ((M : ℝ) + h) ^ 2 * Q := by ring
    rw [e]
    linarith
  have hK : TwoPrimesFormula.H M 0 + 2 * h * (M : ℝ) ^ 2 + (h : ℝ) ^ 2 * (2 * M + 1)
      ≤ TwoPrimesFormula.H M 0
        * (1 + 3 * (h : ℝ) / M + 4 * (h : ℝ) ^ 2 / (M : ℝ) ^ 2) := by
    have hh0 : (0 : ℝ) ≤ h := by positivity
    rw [H_at_zero]
    have e : (M : ℝ) * (2 * (M : ℝ) ^ 2 + 1) / 3 * (1 + 3 * (h : ℝ) / M + 4 * (h : ℝ) ^ 2 / (M : ℝ) ^ 2)
        = (M : ℝ) * (2 * (M : ℝ) ^ 2 + 1) / 3 + (2 * h * (M : ℝ) ^ 2 + h)
          + 4 * (h : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2 + 1) / (3 * M) := by
      field_simp
    rw [e]
    have h3 : (h : ℝ) ^ 2 * (2 * M + 1) ≤ 4 * (h : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2 + 1) / (3 * M) := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : (2 * (M : ℝ) + 1) * (3 * M) ≤ 4 * (2 * (M : ℝ) ^ 2 + 1) := by
        nlinarith [sq_nonneg (4 * (M : ℝ) - 3)]
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (h : ℝ))
      linear_combination h5
    linarith
  have hfin : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u)
      ≤ TwoPrimesFormula.H M 0 * ((1 + 3 * (h : ℝ) / M + 4 * (h : ℝ) ^ 2 / (M : ℝ) ^ 2) * Q) := by
    rw [← mul_assoc]
    exact le_trans hbound (mul_le_mul_of_nonneg_right hK hQ0)
  rw [hh']
  have e : kappaD M u v Y Z
      = (∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H M ((ξ : ℝ) * v / u)) / TwoPrimesFormula.H M 0 := by
    unfold kappaD
    rw [sum_div]
    exact sum_congr rfl fun ξ _ => by ring
  rw [e, div_le_iff₀ hH0, mul_comm _ (TwoPrimesFormula.H M 0)]
  exact hfin

/-- Proposition: every shorter block average is at least a quarter of the longer one, hence
`Φ_H = P_H / H² ≤ 4 κ_H`. -/
theorem phi_le_four_kappa (u v : ℕ) (hu : 0 < u) (Y Z : Finset ℤ) (hY : Y.Nonempty)
    (hZ : Z.Nonempty) (H : ℕ) (hH : 1 ≤ H) :
    P u v Y Z H / (H : ℝ) ^ 2 ≤ 4 * kappaD H u v Y Z := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  set Φ : ℝ := P u v Y Z H / (H : ℝ) ^ 2 with hΦ
  have hPH : P u v Y Z H = (H : ℝ) ^ 2 * Φ := by rw [hΦ]; field_simp
  have hGnn : ∀ ξ, 0 ≤ G u Y Z ξ := by
    intro ξ
    unfold G
    exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _)) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hPnn : ∀ j, 0 ≤ P u v Y Z j := fun j =>
    sum_nonneg fun ξ _ => mul_nonneg (hGnn ξ) (F_nonneg _ _)
  have hΦ0 : 0 ≤ Φ := div_nonneg (hPnn _) (by positivity)
  have hlow : ∀ j, j ≤ H → (j : ℝ) ^ 2 * Φ ≤ 4 * P u v Y Z j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have := hPnn 0
      simp only [Nat.cast_zero]
      linarith
    have h1 := block_transfer u v hu Y Z hY hZ H j h0
    have h2 : ((H + j - 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
      have : H + j - 1 ≤ 2 * H := by omega
      exact_mod_cast this
    have h3 : ((H + j - 1 : ℕ) : ℝ) ^ 2 * P u v Y Z j ≤ (2 * (H : ℝ)) ^ 2 * P u v Y Z j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2) (hPnn j)
    have h4 := le_trans h1 h3
    rw [hPH] at h4
    refine le_of_mul_le_mul_left ?_ (pow_pos hHr 2)
    have e1 : (H : ℝ) ^ 2 * ((j : ℝ) ^ 2 * Φ) = (j : ℝ) ^ 2 * ((H : ℝ) ^ 2 * Φ) := by ring
    have e2 : (H : ℝ) ^ 2 * (4 * P u v Y Z j) = (2 * (H : ℝ)) ^ 2 * P u v Y Z j := by ring
    rw [e1, e2]
    exact h4
  have hH0 := H_at_zero_pos H hH
  have hsum : ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H H ((ξ : ℝ) * v / u)
      = 2 * (∑ j ∈ range H, P u v Y Z j) + P u v Y Z H := by
    unfold P
    simp only [H_eq]
    have e : ∀ ξ ∈ range u, G u Y Z ξ * (2 * (∑ j ∈ range H, F j ((ξ : ℝ) * v / u))
          + F H ((ξ : ℝ) * v / u))
        = (∑ j ∈ range H, 2 * (G u Y Z ξ * F j ((ξ : ℝ) * v / u)))
          + G u Y Z ξ * F H ((ξ : ℝ) * v / u) := by
      intro ξ _
      rw [mul_add, mul_sum, mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl e, sum_add_distrib]
    congr 1
    rw [sum_comm, mul_sum]
    exact sum_congr rfl fun j _ => by rw [mul_sum]
  have hK : TwoPrimesFormula.H H 0 = 2 * (∑ j ∈ range H, (j : ℝ) ^ 2) + (H : ℝ) ^ 2 := by
    have h := sum_shift_sq H 0
    have e1 : ∑ j ∈ range H, ((j : ℝ) + ((0 : ℕ) : ℝ)) ^ 2 = ∑ j ∈ range H, (j : ℝ) ^ 2 :=
      sum_congr rfl fun j _ => by rw [Nat.cast_zero, add_zero]
    rw [e1, Nat.cast_zero] at h
    linear_combination -h
  have hmain : TwoPrimesFormula.H H 0 * Φ
      ≤ 4 * ∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H H ((ξ : ℝ) * v / u) := by
    have h1 : (∑ j ∈ range H, (j : ℝ) ^ 2) * Φ ≤ 4 * ∑ j ∈ range H, P u v Y Z j := by
      rw [sum_mul, mul_sum]
      exact sum_le_sum fun j hj => hlow j (mem_range.mp hj).le
    have h2 := hlow H le_rfl
    rw [hsum, hK]
    have e : (2 * (∑ j ∈ range H, (j : ℝ) ^ 2) + (H : ℝ) ^ 2) * Φ
        = 2 * ((∑ j ∈ range H, (j : ℝ) ^ 2) * Φ) + (H : ℝ) ^ 2 * Φ := by ring
    rw [e]
    linarith
  have e : kappaD H u v Y Z
      = (∑ ξ ∈ range u, G u Y Z ξ * TwoPrimesFormula.H H ((ξ : ℝ) * v / u))
        / TwoPrimesFormula.H H 0 := by
    unfold kappaD
    rw [sum_div]
    exact sum_congr rfl fun ξ _ => by ring
  rw [e, mul_div_assoc', le_div_iff₀ hH0, mul_comm Φ]
  exact hmain

/-- **`κ_M ≤ 32 κ_H` for `H ≤ M`.** -/
theorem kappa_le_thirtytwo (u v : ℕ) (hu : 0 < u) (Y Z : Finset ℤ) (hY : Y.Nonempty)
    (hZ : Z.Nonempty) (M H : ℕ) (hH : 1 ≤ H) (hHM : H ≤ M) :
    kappaD M u v Y Z ≤ 32 * kappaD H u v Y Z := by
  have hM : 1 ≤ M := le_trans hH hHM
  have h1 := kappa_transfer u v hu Y Z hY hZ M H hM hH
  have h2 := phi_le_four_kappa u v hu Y Z hY hZ H hH
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHMr : (H : ℝ) ≤ M := by exact_mod_cast hHM
  have hh0 : (0 : ℝ) ≤ (H : ℝ) - 1 := by linarith
  have hhM : (H : ℝ) - 1 ≤ M := by linarith
  have ha : 3 * ((H : ℝ) - 1) / M ≤ 3 := by
    rw [div_le_iff₀ hM0]; linarith
  have hb : 4 * ((H : ℝ) - 1) ^ 2 / (M : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ hh0 hhM 2
    linarith
  have hGnn : ∀ ξ, 0 ≤ G u Y Z ξ := by
    intro ξ
    unfold G
    exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _)) (by positivity)
  have hΦ0 : 0 ≤ P u v Y Z H / (H : ℝ) ^ 2 :=
    div_nonneg (sum_nonneg fun ξ _ => mul_nonneg (hGnn ξ) (F_nonneg _ _)) (by positivity)
  have h3 : kappaD M u v Y Z ≤ 8 * (P u v Y Z H / (H : ℝ) ^ 2) :=
    le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) hΦ0)
  linarith

/-! ## Small conductors -/

lemma sum_inv_sq_le (Q : ℕ) : ∑ r ∈ Ico 1 Q, (1 : ℝ) / (r : ℝ) ^ 2 ≤ π ^ 2 / 6 :=
  sum_le_hasSum (Ico 1 Q) (fun r _ => by positivity) hasSum_zeta_two

/-- The kernel alone bounds the nonzero frequencies of a conductor `Q` prime to `v`. -/
theorem small_conductor (M Q v : ℕ) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hco : Nat.Coprime v Q) :
    ∑ b ∈ Ico 1 Q, TwoPrimesFormula.H M ((b : ℝ) * v / Q) / TwoPrimesFormula.H M 0
      ≤ π ^ 2 * (Q : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set σ : ℕ → ℕ := fun b => (b * v) % Q with hσ
  have hmem : ∀ b ∈ Ico 1 Q, σ b ∈ Ico 1 Q := by
    intro b hb
    have hb' := mem_Ico.mp hb
    rw [mem_Ico]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    rcases Nat.eq_zero_or_pos (σ b) with h | h
    · have h1 : Q ∣ b * v := Nat.dvd_of_mod_eq_zero h
      have h2 : Q ∣ b := (Nat.Coprime.symm hco).dvd_of_dvd_mul_right h1
      have h3 := Nat.le_of_dvd (by omega) h2
      omega
    · exact h
  have hinj : Set.InjOn σ (Ico 1 Q : Finset ℕ) := by
    intro b hb b' hb' h
    have h1 := mem_Ico.mp (mem_coe.mp hb)
    have h2 := mem_Ico.mp (mem_coe.mp hb')
    have h3 : b * v ≡ b' * v [MOD Q] := h
    have h4 : b ≡ b' [MOD Q] :=
      Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm hco) h3
    exact Nat.ModEq.eq_of_lt_of_lt h4 h1.2 h2.2
  have himg : (Ico 1 Q).image σ = Ico 1 Q := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
      exact hmem b hb
    · rw [card_image_of_injOn hinj]
  set g : ℕ → ℝ := fun r => 3 * (Q : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2)
    * (1 / (r : ℝ) ^ 2 + 1 / ((Q - r : ℕ) : ℝ) ^ 2) with hg
  have hterm : ∀ b ∈ Ico 1 Q,
      TwoPrimesFormula.H M ((b : ℝ) * v / Q) / TwoPrimesFormula.H M 0 ≤ g (σ b) := by
    intro b hb
    have hr := mem_Ico.mp (hmem b hb)
    set r := σ b with hrdef
    set k : ℕ := b * v / Q with hk
    have hdiv : (b : ℝ) * v / Q = (k : ℝ) + (r : ℝ) / Q := by
      have h1 : b * v = Q * k + r := (Nat.div_add_mod (b * v) Q).symm
      have h2 : (b : ℝ) * v = (Q : ℝ) * k + r := by exact_mod_cast h1
      rw [h2]
      field_simp
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.1
    have hrQ : (r : ℝ) < Q := by exact_mod_cast hr.2
    have hsub : ((Q - r : ℕ) : ℝ) = (Q : ℝ) - r := by rw [Nat.cast_sub hr.2.le]
    have hfar : ∀ (n : ℤ) (d : ℝ), 0 < d → d ≤ (Q : ℝ) / 2 → |(b : ℝ) * v / Q - n| = d / Q →
        TwoPrimesFormula.H M ((b : ℝ) * v / Q) / TwoPrimesFormula.H M 0
          ≤ 3 * (Q : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2) * (1 / d ^ 2) := by
      intro n d hd hd2 heq
      have h0 : 0 < |(b : ℝ) * v / Q - n| := by rw [heq]; exact div_pos hd hQr
      have h1 : |(b : ℝ) * v / Q - n| ≤ 1 / 2 := by
        rw [heq, div_le_iff₀ hQr]
        linarith
      refine le_trans (weight_le_far M hM _ n h0 h1) (le_of_eq ?_)
      rw [heq]
      field_simp
    have hc : 0 ≤ 3 * (Q : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2) := by positivity
    have ha : (0 : ℝ) ≤ 1 / (r : ℝ) ^ 2 := by positivity
    have hb2 : (0 : ℝ) ≤ 1 / ((Q - r : ℕ) : ℝ) ^ 2 := by positivity
    rcases le_total ((r : ℝ)) ((Q : ℝ) / 2) with h | h
    · refine le_trans (hfar (k : ℤ) r hr0 h ?_) ?_
      · rw [hdiv, Int.cast_natCast, add_sub_cancel_left, abs_of_pos (div_pos hr0 hQr)]
      · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb2) hc
    · have hd : (0 : ℝ) < (Q : ℝ) - r := by linarith
      refine le_trans (hfar ((k : ℤ) + 1) ((Q : ℝ) - r) hd (by linarith) ?_) ?_
      · have e : (b : ℝ) * v / Q - (((k : ℤ) + 1 : ℤ) : ℝ) = -(((Q : ℝ) - r) / Q) := by
          rw [hdiv]
          push_cast
          field_simp
          ring
        rw [e, abs_neg, abs_of_pos (div_pos hd hQr)]
      · rw [← hsub]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) hc
  refine le_trans (sum_le_sum hterm) ?_
  rw [← sum_image hinj, himg]
  simp only [hg]
  rw [← mul_sum, sum_add_distrib]
  have hrefl : ∑ r ∈ Ico 1 Q, (1 : ℝ) / ((Q - r : ℕ) : ℝ) ^ 2
      = ∑ r ∈ Ico 1 Q, (1 : ℝ) / (r : ℝ) ^ 2 := by
    refine sum_nbij' (fun r => Q - r) (fun r => Q - r) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      have := mem_Ico.mp hr
      rw [mem_Ico]
      omega
    · intro r hr
      have := mem_Ico.mp hr
      rw [mem_Ico]
      omega
    · intro r hr
      have := mem_Ico.mp hr
      omega
    · intro r hr
      have := mem_Ico.mp hr
      omega
    · intro r _
      rfl
  rw [hrefl]
  have h := sum_inv_sq_le Q
  have hc : 0 ≤ 3 * (Q : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add h h) hc) (le_of_eq ?_)
  field_simp
  ring

/-! ## Existence of levels serving a range of multiples -/

open TwoPrimesNonresonance in
set_option maxHeartbeats 1000000 in
/-- For large `D` one pair of levels serves every number `M ≤ D ^ μ` of top clusters. -/
theorem exists_far_multiple {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {x0 x2 μ : ℝ}
    (hμ : 0 ≤ μ) (h1 : (μ + 1) ^ 2 < 4 * (x0 * Real.log p))
    (h2 : (μ + 2) ^ 2 < 4 * (x0 * Real.log q)) (h02 : x0 < x2)
    {K : ℕ} (hK : 1 ≤ K) :
    ∃ L0 : ℝ, ∀ D : ℕ, 0 < D → L0 ≤ Real.log D → ∃ s t : ℕ,
      K * D * q ^ (s ^ 2) ≤ p ^ (t ^ 2) ∧
      ∀ M : ℕ, 1 ≤ M → Real.log M ≤ μ * Real.log D →
        D * M * p ^ (t ^ 2) < q ^ ((s + 1) ^ 2) ∧
        D * M * p ^ (t ^ 2) < p ^ ((t + 1) ^ 2) ∧
        x0 * (Real.log D) ^ 2 ≤ Real.log (M * p ^ (t ^ 2) : ℕ) ∧
        Real.log (M * p ^ (t ^ 2) : ℕ) ≤ x2 * (Real.log D) ^ 2
:= by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Real.log p := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = Real.log q := ⟨_, rfl⟩
  have hα0 : 0 < α := hα ▸ Real.log_pos (by exact_mod_cast hp.one_lt)
  have hβ0 : 0 < β := hβ ▸ Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (x0 + x2) / 2 := ⟨_, rfl⟩
  have hx00 : 0 < x0 := by
    rw [← hα] at h1
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hα0.le
    have := sq_nonneg (μ + 1)
    linarith
  have hx0x : x0 < x := by rw [hx]; linarith
  have hxx2 : x < x2 := by rw [hx]; linarith
  have hx0' : 0 < x := lt_trans hx00 hx0x
  have hxα : (μ + 1) ^ 2 < 4 * (x * α) := by
    rw [← hα] at h1
    exact lt_trans h1 (by have := mul_lt_mul_of_pos_right hx0x hα0; linarith)
  have hxβ : (μ + 2) ^ 2 < 4 * (x * β) := by
    rw [← hβ] at h2
    exact lt_trans h2 (by have := mul_lt_mul_of_pos_right hx0x hβ0; linarith)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = √(β / α) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := hγ ▸ Real.sqrt_pos.mpr (div_pos hβ0 hα0)
  have hγirr : Irrational γ := by rw [hγ, hα, hβ]; exact irrational_ratio hp hq hpq
  have hγ2 : γ ^ 2 * α = β := by
    rw [hγ, Real.sq_sqrt (div_nonneg hβ0.le hα0.le)]; field_simp
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = √(x * α) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = √(x / β) := ⟨_, rfl⟩
  have hw0 : 0 < w := hw ▸ Real.sqrt_pos.mpr (mul_pos hx0' hα0)
  have hσ0 : 0 < σ := hσ ▸ Real.sqrt_pos.mpr (div_pos hx0' hβ0)
  have hw2 : w ^ 2 = x * α := by rw [hw, Real.sq_sqrt (mul_nonneg hx0'.le hα0.le)]
  have hσ2 : σ ^ 2 * β = x := by
    rw [hσ, Real.sq_sqrt (div_nonneg hx0'.le hβ0.le)]; field_simp
  -- the identities between the square roots
  have hσγ : σ * (γ * α) = w := by
    have h3 : (σ * (γ * α)) ^ 2 = w ^ 2 := by
      have e : (σ * (γ * α)) ^ 2 = σ ^ 2 * (γ ^ 2 * α) * α := by ring
      rw [e, hγ2, hσ2, hw2]
    exact (pow_left_inj₀ (by positivity) hw0.le two_ne_zero).mp h3
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = σ * β := ⟨_, rfl⟩
  have hz2 : z ^ 2 = x * β := by
    have e : z ^ 2 = σ ^ 2 * β * β := by rw [hz]; ring
    rw [e, hσ2]
  have hz0 : 0 < z := hz ▸ mul_pos hσ0 hβ0
  have hz32 : (μ + 2) / 2 < z := by
    have h3 : ((μ + 2) / 2) ^ 2 < z ^ 2 := by
      rw [hz2, div_pow, div_lt_iff₀ (by norm_num)]; linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) hz0.le two_ne_zero).mp h3
  have hwγ : w * γ = z := by
    have h3 : (w * γ) ^ 2 = z ^ 2 := by
      have e : (w * γ) ^ 2 = x * (γ ^ 2 * α) := by rw [mul_pow, hw2]; ring
      rw [e, hγ2, hz2]
    exact (pow_left_inj₀ (by positivity) hz0.le two_ne_zero).mp h3
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * w) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hwa : 2 * w * a = 1 := by rw [ha]; field_simp
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = γ - (μ + 2) / (2 * w) := ⟨_, rfl⟩
  have hwl : w * l = z - (μ + 2) / 2 := by
    rw [hl, mul_sub, hwγ]; field_simp
  have hl0 : 0 < l := by
    have : 0 < w * l := by rw [hwl]; linarith
    exact pos_of_mul_pos_right this hw0.le
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min l 1 / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; have := lt_min hl0 one_pos; linarith
  have hεl : 4 * ε ≤ l := by rw [hε]; have := min_le_left l 1; linarith
  have hε14 : ε ≤ 1 / 4 := by rw [hε]; have := min_le_right l 1; linarith
  obtain ⟨K0, hK0⟩ := rotation (γ := -γ) hγirr.neg hε0 (by linarith)
  obtain ⟨Bmax, hBmax⟩ : ∃ B : ℝ, B = 2 * (K0 + 1) * (γ * α) * (a + 1) + α * (a + 1) ^ 2 :=
    ⟨_, rfl⟩
  have hBmax0 : 0 ≤ Bmax := by rw [hBmax]; positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = Real.log K / (2 * w * ε) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2 : ℝ, L2 = (Bmax + 2) / (z - (μ + 2) / 2) := ⟨_, rfl⟩
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = (K0 : ℝ) + 2 := ⟨_, rfl⟩
  obtain ⟨L3, hL3⟩ : ∃ L3 : ℝ, L3 = (2 * σ * Mc * β + Mc ^ 2 * β) / (x2 - x) := ⟨_, rfl⟩
  refine ⟨max 1 (max L1 (max L2 L3)), fun D hD hLD => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log D := ⟨_, rfl⟩
  rw [← hL] at hLD ⊢
  have hL1' : 1 ≤ L := le_trans (le_max_left _ _) hLD
  have hLL1 : L1 ≤ L := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hLD
  have hLL2 : L2 ≤ L :=
    le_trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hLD
  have hLL3 : L3 ≤ L :=
    le_trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hLD
  have hL0 : 0 < L := by linarith
  -- choose s and t
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, s0 = ⌈L * σ⌉₊ := ⟨_, rfl⟩
  obtain ⟨j, hj, hfr⟩ := hK0 (s0 * γ + (a + ε))
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = s0 + j := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = s * γ + (a + ε) := ⟨_, rfl⟩
  have hfr' : Int.fract (-y) < ε := by
    have : (j : ℝ) * -γ - (s0 * γ + (a + ε)) = -y := by rw [hy, hs]; push_cast; ring
    rwa [this] at hfr
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈y⌉₊ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε + Int.fract (-y) := ⟨_, rfl⟩
  have hte : (t : ℝ) = s * γ + (a + e) := by
    have h3 : ((⌈y⌉₊ : ℕ) : ℝ) = (⌈y⌉ : ℝ) := by
      have h4 : (0 : ℤ) ≤ ⌈y⌉ := Int.ceil_nonneg hy0
      have h5 : ((⌈y⌉₊ : ℕ) : ℤ) = ⌈y⌉ := by
        rw [← Int.ceil_toNat]; exact Int.toNat_of_nonneg h4
      exact_mod_cast h5
    have h6 : Int.fract (-y) = (⌈y⌉ : ℝ) - y := by
      unfold Int.fract
      rw [Int.floor_neg]; push_cast; ring
    rw [ht, h3, he, h6, hy]; ring
  have he0 : ε ≤ e := by rw [he]; have := Int.fract_nonneg (-y); linarith
  have he1 : e ≤ 2 * ε := by rw [he]; linarith
  have hepos : 0 ≤ e := le_trans hε0.le he0
  have heone : e ≤ 1 := by linarith
  -- the size of s
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = s - L * σ := ⟨_, rfl⟩
  have hsθ : (s : ℝ) = L * σ + θ := by rw [hθ]; ring
  have hθ0 : 0 ≤ θ := by
    have h3 : L * σ ≤ (s0 : ℝ) := hs0 ▸ Nat.le_ceil _
    have h4 : (s0 : ℝ) ≤ s := by rw [hs]; push_cast; have := Nat.cast_nonneg (α := ℝ) j; linarith
    rw [hθ]; linarith
  have hθ1 : θ ≤ K0 + 1 := by
    have h3 : (s0 : ℝ) < L * σ + 1 := hs0 ▸ Nat.ceil_lt_add_one (by positivity)
    have h4 : (s : ℝ) ≤ s0 + K0 := by
      rw [hs]; push_cast; have : (j : ℝ) ≤ K0 := by exact_mod_cast hj
      linarith
    rw [hθ]; linarith
  -- r = t²α - s²β
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * θ * (γ * α) * (a + e) + α * (a + e) ^ 2 := ⟨_, rfl⟩
  have hr : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β = L + 2 * L * w * e + B := by
    have e1 : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β
        = 2 * (s : ℝ) * (γ * α) * (a + e) + α * (a + e) ^ 2 := by
      rw [hte, ← hγ2]; ring
    have e2 : 2 * (s : ℝ) * (γ * α) * (a + e)
        = 2 * L * (σ * (γ * α)) * (a + e) + 2 * θ * (γ * α) * (a + e) := by
      rw [hsθ]; ring
    have e3 : 2 * L * (σ * (γ * α)) * (a + e) = L * (2 * w * a) + 2 * L * w * e := by
      rw [hσγ]; ring
    rw [e1, e2, e3, hwa, hB]; ring
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h3 : 0 ≤ 2 * θ * (γ * α) * (a + e) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
    have h4 : 0 ≤ α * (a + e) ^ 2 := mul_nonneg hα0.le (sq_nonneg _)
    linarith
  have hBle : B ≤ Bmax := by
    rw [hB, hBmax]
    have h3 : a + e ≤ a + 1 := by linarith
    have h4 : 2 * θ * (γ * α) * (a + e) ≤ 2 * (K0 + 1) * (γ * α) * (a + 1) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) h3
        (by linarith) (by positivity)
    have h5 : α * (a + e) ^ 2 ≤ α * (a + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 2) hα0.le
    linarith
  have hlow : L + Real.log K ≤ (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β := by
    rw [hr]
    have h3 : Real.log K ≤ L * (2 * w * ε) := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * w * ε)).mp (hL1 ▸ hLL1)
      linarith
    have h4 : 2 * L * w * ε ≤ 2 * L * w * e :=
      mul_le_mul_of_nonneg_left he0 (by positivity)
    have h5 : L * (2 * w * ε) = 2 * L * w * ε := by ring
    linarith
  have hup : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β ≤ (2 * s + 1) * β - (1 + μ) * L - 2 := by
    rw [hr]
    have h3 : 2 * w * e ≤ z - (μ + 2) / 2 := by
      have h4 : 2 * e ≤ l := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hw0.le
      linarith [hwl]
    have h6 : 2 * L * w * e ≤ L * (z - (μ + 2) / 2) := by
      have := mul_le_mul_of_nonneg_left h3 hL0.le
      linarith
    have h7 : Bmax + 2 ≤ L * (z - (μ + 2) / 2) :=
      (div_le_iff₀ (by linarith : (0:ℝ) < z - (μ + 2) / 2)).mp (hL2 ▸ hLL2)
    have h8 : 2 * L * z ≤ 2 * (s : ℝ) * β := by
      have h9 : L * σ ≤ s := by rw [hsθ]; linarith
      have := mul_le_mul_of_nonneg_right h9 hβ0.le
      rw [hz]; linarith
    linarith [hBle, hβ0.le]
  have hbig : (1 + μ) * L < (2 * (t : ℝ) + 1) * α := by
    have h3 : (s : ℝ) * γ ≤ t := by rw [hte]; linarith
    have h4 : L * σ * γ ≤ (s : ℝ) * γ :=
      mul_le_mul_of_nonneg_right (by rw [hsθ]; linarith) hγ0.le
    have h5 : L * w ≤ (t : ℝ) * α := by
      have h6 := mul_le_mul_of_nonneg_right (h4.trans h3) hα0.le
      have e1 : L * σ * γ * α = L * (σ * (γ * α)) := by ring
      rw [e1, hσγ] at h6
      exact h6
    have h7 : μ + 1 < 2 * w := by
      have h8 : (μ + 1) ^ 2 < (2 * w) ^ 2 := by rw [mul_pow, hw2]; linarith
      exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h8
    have h9 : L * (μ + 1) ≤ L * (2 * w) := mul_le_mul_of_nonneg_left h7.le hL0.le
    linarith
  -- translate to integers
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have lpow : ∀ (b : ℕ) (k : ℕ), (0 : ℝ) < b → Real.log ((b : ℝ) ^ k) = k * Real.log b :=
    fun b k _ => Real.log_pow _ _
  refine ⟨s, t, ?_, fun M hM1 hMD => ?_⟩
  · have h3 : ((K * D * q ^ (s ^ 2) : ℕ) : ℝ) ≤ ((p ^ (t ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_le_log_iff (mul_pos (mul_pos hKr hDr) (pow_pos hqr _)) (pow_pos hpr _),
        Real.log_mul (mul_pos hKr hDr).ne' (pow_pos hqr _).ne',
        Real.log_mul hKr.ne' hDr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα, ← hβ]
      push_cast; linarith
    exact_mod_cast h3
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hμL : (1 + μ) * L = L + μ * L := by ring
  have hXlog : Real.log (M * p ^ (t ^ 2) : ℕ) = Real.log M + (t : ℝ) ^ 2 * α := by
    push_cast
    rw [Real.log_mul hMr.ne' (pow_pos hpr _).ne', Real.log_pow, ← hα]
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h3 : ((D * M * p ^ (t ^ 2) : ℕ) : ℝ) < ((q ^ ((s + 1) ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_lt_log_iff (mul_pos (mul_pos hDr hMr) (pow_pos hpr _)) (pow_pos hqr _),
        Real.log_mul (mul_pos hDr hMr).ne' (pow_pos hpr _).ne',
        Real.log_mul hDr.ne' hMr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα, ← hβ]
      push_cast
      have e1 : ((s : ℝ) + 1) ^ 2 * β = (s : ℝ) ^ 2 * β + (2 * s + 1) * β := by ring
      rw [e1]; linarith
    exact_mod_cast h3
  · have h3 : ((D * M * p ^ (t ^ 2) : ℕ) : ℝ) < ((p ^ ((t + 1) ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_lt_log_iff (mul_pos (mul_pos hDr hMr) (pow_pos hpr _)) (pow_pos hpr _),
        Real.log_mul (mul_pos hDr hMr).ne' (pow_pos hpr _).ne',
        Real.log_mul hDr.ne' hMr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα]
      push_cast
      have e1 : ((t : ℝ) + 1) ^ 2 * α = (t : ℝ) ^ 2 * α + (2 * t + 1) * α := by ring
      rw [e1]; linarith
    exact_mod_cast h3
  · rw [hXlog]
    have h3 : x0 * L ^ 2 ≤ x * L ^ 2 := mul_le_mul_of_nonneg_right hx0x.le (sq_nonneg _)
    have h4 : x * L ^ 2 ≤ (s : ℝ) ^ 2 * β := by
      have h5 : (L * σ) ^ 2 ≤ (s : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by rw [hsθ]; linarith) 2
      have h6 := mul_le_mul_of_nonneg_right h5 hβ0.le
      have e1 : (L * σ) ^ 2 * β = (σ ^ 2 * β) * L ^ 2 := by ring
      rw [e1, hσ2] at h6
      exact h6
    linarith
  · rw [hXlog]
    have h3 : Real.log M + (t : ℝ) ^ 2 * α ≤ ((s : ℝ) + 1) ^ 2 * β := by
      have e1 : ((s : ℝ) + 1) ^ 2 * β = (s : ℝ) ^ 2 * β + (2 * s + 1) * β := by ring
      rw [e1]; linarith
    have h4 : (s : ℝ) + 1 ≤ L * σ + Mc := by rw [hsθ, hMc]; linarith
    have h5 : ((s : ℝ) + 1) ^ 2 * β ≤ (L * σ + Mc) ^ 2 * β :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4 2) hβ0.le
    have h6 : (L * σ + Mc) ^ 2 * β = x * L ^ 2 + (2 * σ * Mc * β) * L + Mc ^ 2 * β := by
      rw [← hσ2]; ring
    have h7 : 2 * σ * Mc * β + Mc ^ 2 * β ≤ L * (x2 - x) :=
      (div_le_iff₀ (by linarith : (0:ℝ) < x2 - x)).mp (hL3 ▸ hLL3)
    have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
    have h8 : Mc ^ 2 * β * 1 ≤ Mc ^ 2 * β * L :=
      mul_le_mul_of_nonneg_left hL1' (mul_nonneg (sq_nonneg _) hβ0.le)
    have h9 := mul_le_mul_of_nonneg_right h7 hL0.le
    linarith only [h3, h5, h6, h8, h9]


end TwoPrimesMultiple
