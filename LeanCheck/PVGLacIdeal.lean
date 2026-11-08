import LeanCheck.PVGLacCount
import LeanCheck.PVGBohr

/-!
# PVG: the lacunary ideal `I_S` (Lean check)

Scope. Lemma 7.2 of `PVG_v19`: the family `I_S` of subsets `A ⊆ ℝ` with `A ⊆ [-m,m] + a₁S + … + a_kS` satisfies (I1) to (I5) and
contains the bounded sets. The proof of (I3) (`ℝ ∉ I_S`) uses Lebesgue measure and the counting lemma (`PVGLacCount.count_bound`).

* `IS`: the ideal; `IS_isIdeal`: (I1) to (I5) in the form of `IsIdeal` (`PVGIdeal`); `bounded_mem_IS`: bounded sets belong to `IS`;
* `volume_cover_le`: a set covered by the intervals `[σ - m, σ + m]`, `σ ∈ Y`, has measure at most `|Y| · 2m`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Set Pointwise MeasureTheory Filter
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-! ### Elementary closure properties of `sumSet` -/

lemma mem_sumSet_cons {a : ℝ} {l : List ℝ} {x : ℝ} :
    x ∈ sumSet (a :: l) ↔ ∃ c ∈ Sset, ∃ y ∈ sumSet l, x = a * c + y := by
  constructor
  · rintro ⟨u, ⟨c, hc, rfl⟩, y, hy, rfl⟩
    exact ⟨c, hc, y, hy, by simp [smul_eq_mul]⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨a * c, ⟨c, hc, by simp [smul_eq_mul]⟩, y, hy, rfl⟩

lemma sumSet_append_add : ∀ (l l' : List ℝ) (x y : ℝ), x ∈ sumSet l → y ∈ sumSet l' → x + y ∈ sumSet (l ++ l')
  | [], l', x, y, hx, hy => by
    have : x = 0 := hx
    subst this; simpa using hy
  | a :: l, l', x, y, hx, hy => by
    obtain ⟨c, hc, z, hz, rfl⟩ := mem_sumSet_cons.1 hx
    refine mem_sumSet_cons.2 ⟨c, hc, z + y, sumSet_append_add l l' z y hz hy, by ring⟩

lemma sumSet_append_left (l l' : List ℝ) {x : ℝ} (hx : x ∈ sumSet l) : x ∈ sumSet (l ++ l') := by
  simpa using sumSet_append_add l l' x 0 hx (zero_mem_sumSet l')

lemma sumSet_append_right (l l' : List ℝ) {y : ℝ} (hy : y ∈ sumSet l') : y ∈ sumSet (l ++ l') := by
  simpa using sumSet_append_add l l' 0 y (zero_mem_sumSet l) hy

lemma sumSet_smul_mem (c : ℝ) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSet l → c * x ∈ sumSet (l.map (fun a => c * a))
  | [], x, hx => by
    have : x = 0 := hx
    subst this; simp [sumSet]
  | a :: l, x, hx => by
    obtain ⟨c', hc', y, hy, rfl⟩ := mem_sumSet_cons.1 hx
    refine mem_sumSet_cons.2 ⟨c', hc', c * y, sumSet_smul_mem c l y hy, by ring⟩

/-! ### The ideal -/

/-- `I_S`: the sets contained in `[-m,m] + a₁S + … + a_kS`. -/
def IS : Set (Set ℝ) := {A | ∃ (m : ℝ) (l : List ℝ), A ⊆ Icc (-m) m + sumSet l}

lemma mem_IS_iff {A : Set ℝ} : A ∈ IS ↔ ∃ (m : ℝ) (l : List ℝ), ∀ z ∈ A, ∃ y σ : ℝ, |y| ≤ m ∧ σ ∈ sumSet l ∧ z = y + σ := by
  constructor
  · rintro ⟨m, l, h⟩
    refine ⟨m, l, fun z hz => ?_⟩
    obtain ⟨y, hy, σ, hσ, rfl⟩ := h hz
    exact ⟨y, σ, abs_le.2 ⟨hy.1, hy.2⟩, hσ, rfl⟩
  · rintro ⟨m, l, h⟩
    refine ⟨m, l, fun z hz => ?_⟩
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h z hz
    exact ⟨y, ⟨(abs_le.1 hy).1, (abs_le.1 hy).2⟩, σ, hσ, rfl⟩

/-- Bounded sets belong to `I_S`. -/
lemma bounded_mem_IS {A : Set ℝ} {M : ℝ} (h : ∀ a ∈ A, |a| ≤ M) : A ∈ IS := by
  rw [mem_IS_iff]
  exact ⟨M, [], fun z hz => ⟨z, 0, h z hz, rfl, by simp⟩⟩

/-! ### Measure of a cover by short intervals -/

lemma volume_cover_le (Y : Finset ℝ) {m : ℝ} (hm : 0 ≤ m) {A : Set ℝ}
    (hA : A ⊆ ⋃ σ ∈ Y, Icc (σ - m) (σ + m)) : volume A ≤ ENNReal.ofReal (Y.card * (2 * m)) := by
  refine (measure_mono hA).trans ((measure_biUnion_finset_le Y _).trans ?_)
  have : ∀ σ ∈ Y, volume (Icc (σ - m) (σ + m)) = ENNReal.ofReal (2 * m) := by
    intro σ _; rw [Real.volume_Icc]; congr 1; ring
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simp

/-! ### (I3): `ℝ` is not in `I_S` -/

lemma sS_unbounded (B : ℝ) : ∃ L : ℕ, B < sS L := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  unfold sS
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le n])

theorem univ_not_mem_IS : (Set.univ : Set ℝ) ∉ IS := by
  rintro ⟨m, l, h⟩
  set m' : ℝ := |m| with hm'
  have hm'0 : 0 ≤ m' := abs_nonneg m
  obtain ⟨K, hK, hcount⟩ := count_bound l 2 (by norm_num)
  obtain ⟨L, hL⟩ := sS_unbounded (max m' (m' ^ 2 * K))
  have hLm : m' < sS L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLK : m' ^ 2 * K < sS L := lt_of_le_of_lt (le_max_right _ _) hL
  obtain ⟨hfin, hnc⟩ := hcount L
  set Y := sumSet l ∩ Icc (-(2 * sS L)) (2 * sS L) with hY
  have hcover : Icc (-(sS L)) (sS L) ⊆ ⋃ σ ∈ hfin.toFinset, Icc (σ - m') (σ + m') := by
    intro u hu
    obtain ⟨y, hy, σ, hσ, rfl⟩ := h (Set.mem_univ u)
    have hy' : |y| ≤ m' := (abs_le.2 ⟨hy.1, hy.2⟩).trans (le_abs_self m)
    have hyb := abs_le.1 hy'
    have hσI : σ ∈ Icc (-(2 * sS L)) (2 * sS L) := by
      constructor <;> linarith [hu.1, hu.2]
    simp only [Set.mem_iUnion]
    refine ⟨σ, (hfin.mem_toFinset).2 ⟨hσ, hσI⟩, ?_, ?_⟩ <;> linarith [hyb.1, hyb.2]
  have hvol := volume_cover_le hfin.toFinset hm'0 hcover
  rw [Real.volume_Icc] at hvol
  have hcard : (hfin.toFinset.card : ℝ) = (Y.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card Y hfin]
  rw [hcard] at hvol
  have hsL := sS_pos L
  have hq : 0 ≤ (Y.ncard : ℝ) * (2 * m') := by positivity
  have hle := (ENNReal.ofReal_le_ofReal_iff hq).1 hvol
  have h1 : sS L ≤ (Y.ncard : ℝ) * m' := by linarith
  have h2 : (sS L) ^ 2 ≤ ((Y.ncard : ℝ) * m') ^ 2 := pow_le_pow_left₀ hsL.le h1 2
  have h3 : ((Y.ncard : ℝ) * m') ^ 2 = (Y.ncard : ℝ) ^ 2 * m' ^ 2 := by ring
  have h4 : (sS L) ^ 2 ≤ K * sS L * m' ^ 2 := by
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hnc (sq_nonneg m'))
  have h5 : sS L ≤ K * m' ^ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  nlinarith

/-- **Lemma 7.2.** `I_S` satisfies (I1) to (I5). -/
theorem IS_isIdeal : IsIdeal IS where
  mono := fun {A B} hA hBA => by
    obtain ⟨m, l, h⟩ := hA
    exact ⟨m, l, hBA.trans h⟩
  union := fun {A B} hA hB => by
    rw [mem_IS_iff] at *
    obtain ⟨m, l, h⟩ := hA
    obtain ⟨m', l', h'⟩ := hB
    refine ⟨max m m', l ++ l', fun z hz => ?_⟩
    rcases hz with hz | hz
    · obtain ⟨y, σ, hy, hσ, rfl⟩ := h z hz
      exact ⟨y, σ, hy.trans (le_max_left _ _), sumSet_append_left l l' hσ, rfl⟩
    · obtain ⟨y, σ, hy, hσ, rfl⟩ := h' z hz
      exact ⟨y, σ, hy.trans (le_max_right _ _), sumSet_append_right l l' hσ, rfl⟩
  single := fun x => bounded_mem_IS (M := |x|) (fun a ha => by rw [Set.mem_singleton_iff.1 ha])
  ne_univ := univ_not_mem_IS
  add := fun {A B} hA hB => by
    rw [mem_IS_iff] at *
    obtain ⟨m, l, h⟩ := hA
    obtain ⟨m', l', h'⟩ := hB
    refine ⟨m + m', l ++ l', fun z hz => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h a ha
    obtain ⟨y', σ', hy', hσ', rfl⟩ := h' b hb
    exact ⟨y + y', σ + σ', (abs_add_le y y').trans (add_le_add hy hy'),
      sumSet_append_add l l' σ σ' hσ hσ', by ring⟩
  smul := fun a {A} hA => by
    rw [mem_IS_iff] at *
    obtain ⟨m, l, h⟩ := hA
    refine ⟨|a| * m, l.map (fun c => a * c), fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.1 hz
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h w hw
    refine ⟨a * y, a * σ, ?_, sumSet_smul_mem a l σ hσ, by simp [smul_eq_mul]; ring⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)

#print axioms univ_not_mem_IS
#print axioms IS_isIdeal

end Lac
end PVG
