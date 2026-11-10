import Mathlib
import LeanCheck.PVGLacMain

/-!
# PVG: the ideals `I_A` of the lacunary subfamilies (Lean check)

Scope. Addendum N2 of the research note, formal counterpart of the first part of Theorem 8.61 of PVG_v27 (planned). For `A ⊆ ℕ` let
`S_A = {0} ∪ {±s_n : n ∈ A, n ≥ 1}` (`SsetA A`, so `S_ℕ = S` up to the index `0`), `a₁S_A + … + a_kS_A` (`sumSetA A l`) and `I_A` (`IA A`) the
family of sets contained in `[-m,m] + a₁S_A + … + a_kS_A`.

* `IA_isIdeal`: `I_A` satisfies (I1) to (I5) (`IsIdeal`); `ne_univ` follows from `I_A ⊆ I_S` (`IA_sub_IS`, `univ_not_mem_IS`);
* `IA_mono`: `A ⊆ B` implies `I_A ⊆ I_B`; `IA_mono_of_diff_finite`: `A \ B` finite implies `I_A ⊆ I_B`;
* `bounded_mem_IA`: bounded sets belong to `I_A`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- `S_A = {0} ∪ {±s_n : n ∈ A, n ≥ 1}`. -/
def SsetA (A : Set ℕ) : Set ℝ := {x | x = 0 ∨ ∃ n : ℕ, n ∈ A ∧ 1 ≤ n ∧ (x = sS n ∨ x = -sS n)}

lemma zero_mem_SsetA (A : Set ℕ) : (0 : ℝ) ∈ SsetA A := Or.inl rfl

lemma SsetA_sub (A : Set ℕ) : SsetA A ⊆ Sset := by
  intro x hx
  rcases hx with h | ⟨n, -, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨n, h1, h2⟩

lemma SsetA_mono {A B : Set ℕ} (h : A ⊆ B) : SsetA A ⊆ SsetA B := by
  intro x hx
  rcases hx with h0 | ⟨n, hn, h1, h2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨n, h hn, h1, h2⟩

/-- `a₁S_A + … + a_kS_A`. -/
def sumSetA (A : Set ℕ) : List ℝ → Set ℝ
  | [] => {0}
  | a :: l => a • SsetA A + sumSetA A l

lemma zero_mem_sumSetA (A : Set ℕ) : ∀ l : List ℝ, (0 : ℝ) ∈ sumSetA A l
  | [] => rfl
  | a :: l => ⟨0, ⟨0, zero_mem_SsetA A, by simp⟩, 0, zero_mem_sumSetA A l, by simp⟩

lemma mem_sumSetA_cons {A : Set ℕ} {a : ℝ} {l : List ℝ} {x : ℝ} :
    x ∈ sumSetA A (a :: l) ↔ ∃ c ∈ SsetA A, ∃ y ∈ sumSetA A l, x = a * c + y := by
  constructor
  · rintro ⟨u, ⟨c, hc, rfl⟩, y, hy, rfl⟩
    exact ⟨c, hc, y, hy, by simp [smul_eq_mul]⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨a * c, ⟨c, hc, by simp [smul_eq_mul]⟩, y, hy, rfl⟩

lemma sumSetA_sub (A : Set ℕ) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l → x ∈ sumSet l
  | [], x, hx => hx
  | a :: l, x, hx => by
    obtain ⟨c, hc, y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    exact mem_sumSet_cons.2 ⟨c, SsetA_sub A hc, y, sumSetA_sub A l y hy, rfl⟩

lemma sumSetA_mono {A B : Set ℕ} (h : A ⊆ B) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l → x ∈ sumSetA B l
  | [], x, hx => hx
  | a :: l, x, hx => by
    obtain ⟨c, hc, y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    exact mem_sumSetA_cons.2 ⟨c, SsetA_mono h hc, y, sumSetA_mono h l y hy, rfl⟩

lemma sumSetA_append_add (A : Set ℕ) :
    ∀ (l l' : List ℝ) (x y : ℝ), x ∈ sumSetA A l → y ∈ sumSetA A l' → x + y ∈ sumSetA A (l ++ l')
  | [], l', x, y, hx, hy => by
    have : x = 0 := hx
    subst this; simpa using hy
  | a :: l, l', x, y, hx, hy => by
    obtain ⟨c, hc, z, hz, rfl⟩ := mem_sumSetA_cons.1 hx
    exact mem_sumSetA_cons.2 ⟨c, hc, z + y, sumSetA_append_add A l l' z y hz hy, by ring⟩

lemma sumSetA_append_left (A : Set ℕ) (l l' : List ℝ) {x : ℝ} (hx : x ∈ sumSetA A l) : x ∈ sumSetA A (l ++ l') := by
  simpa using sumSetA_append_add A l l' x 0 hx (zero_mem_sumSetA A l')

lemma sumSetA_append_right (A : Set ℕ) (l l' : List ℝ) {y : ℝ} (hy : y ∈ sumSetA A l') : y ∈ sumSetA A (l ++ l') := by
  simpa using sumSetA_append_add A l l' 0 y (zero_mem_sumSetA A l) hy

lemma sumSetA_smul_mem (A : Set ℕ) (c : ℝ) :
    ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l → c * x ∈ sumSetA A (l.map (fun a => c * a))
  | [], x, hx => by
    have : x = 0 := hx
    subst this; simp [sumSetA]
  | a :: l, x, hx => by
    obtain ⟨c', hc', y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    exact mem_sumSetA_cons.2 ⟨c', hc', c * y, sumSetA_smul_mem A c l y hy, by ring⟩

/-- `I_A`: the sets contained in `[-m,m] + a₁S_A + … + a_kS_A`. -/
def IA (A : Set ℕ) : Set (Set ℝ) := {J | ∃ (m : ℝ) (l : List ℝ), J ⊆ Icc (-m) m + sumSetA A l}

lemma mem_IA_iff {A : Set ℕ} {J : Set ℝ} :
    J ∈ IA A ↔ ∃ (m : ℝ) (l : List ℝ), ∀ z ∈ J, ∃ y σ : ℝ, |y| ≤ m ∧ σ ∈ sumSetA A l ∧ z = y + σ := by
  constructor
  · rintro ⟨m, l, h⟩
    refine ⟨m, l, fun z hz => ?_⟩
    obtain ⟨y, hy, σ, hσ, rfl⟩ := h hz
    exact ⟨y, σ, abs_le.2 ⟨hy.1, hy.2⟩, hσ, rfl⟩
  · rintro ⟨m, l, h⟩
    refine ⟨m, l, fun z hz => ?_⟩
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h z hz
    exact ⟨y, ⟨(abs_le.1 hy).1, (abs_le.1 hy).2⟩, σ, hσ, rfl⟩

lemma bounded_mem_IA (A : Set ℕ) {J : Set ℝ} {M : ℝ} (h : ∀ a ∈ J, |a| ≤ M) : J ∈ IA A := by
  rw [mem_IA_iff]
  exact ⟨M, [], fun z hz => ⟨z, 0, h z hz, rfl, by simp⟩⟩

/-- `I_A ⊆ I_S`. -/
lemma IA_sub_IS (A : Set ℕ) {J : Set ℝ} (hJ : J ∈ IA A) : J ∈ IS := by
  obtain ⟨m, l, h⟩ := mem_IA_iff.1 hJ
  rw [mem_IS_iff]
  exact ⟨m, l, fun z hz => by
    obtain ⟨y, σ, hy, hσ, hz'⟩ := h z hz
    exact ⟨y, σ, hy, sumSetA_sub A l σ hσ, hz'⟩⟩

/-- `A ⊆ B` implies `I_A ⊆ I_B`. -/
lemma IA_mono {A B : Set ℕ} (h : A ⊆ B) {J : Set ℝ} (hJ : J ∈ IA A) : J ∈ IA B := by
  obtain ⟨m, l, hJ'⟩ := mem_IA_iff.1 hJ
  rw [mem_IA_iff]
  exact ⟨m, l, fun z hz => by
    obtain ⟨y, σ, hy, hσ, hz'⟩ := hJ' z hz
    exact ⟨y, σ, hy, sumSetA_mono h l σ hσ, hz'⟩⟩


/-- Replacing the elements `s_n` with `n ∈ A`, `n ∉ B` by `0` changes an element of `a₁S_A + … + a_kS_A` by at most `Mb ∑ |a_i|`. -/
lemma sumSetA_approx {A B : Set ℕ} {Mb : ℝ} (hMb0 : 0 ≤ Mb) (hMb : ∀ n ∈ A, n ∉ B → sS n ≤ Mb) :
    ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l →
      ∃ y ∈ sumSetA B l, |x - y| ≤ Mb * (l.map (fun a => |a|)).sum
  | [], x, hx => by
    have : x = 0 := hx
    subst this
    exact ⟨0, rfl, by simp⟩
  | a :: l, x, hx => by
    obtain ⟨c, hc, z, hz, rfl⟩ := mem_sumSetA_cons.1 hx
    obtain ⟨y, hy, hzy⟩ := sumSetA_approx hMb0 hMb l z hz
    by_cases hcB : c ∈ SsetA B
    · refine ⟨a * c + y, mem_sumSetA_cons.2 ⟨c, hcB, y, hy, rfl⟩, ?_⟩
      have h1 : a * c + z - (a * c + y) = z - y := by ring
      rw [h1]
      simp only [List.map_cons, List.sum_cons]
      have := mul_nonneg hMb0 (abs_nonneg a)
      linarith
    · refine ⟨y, mem_sumSetA_cons.2 ⟨0, zero_mem_SsetA B, y, hy, by ring⟩, ?_⟩
      have hcb : |c| ≤ Mb := by
        rcases hc with h0 | ⟨n, hnA, hn1, hcn⟩
        · exact absurd (h0 ▸ zero_mem_SsetA B) hcB
        · have hnB : n ∉ B := fun hnB => hcB (Or.inr ⟨n, hnB, hn1, hcn⟩)
          have := hMb n hnA hnB
          rcases hcn with rfl | rfl
          · rwa [abs_of_pos (sS_pos n)]
          · rwa [abs_neg, abs_of_pos (sS_pos n)]
      simp only [List.map_cons, List.sum_cons]
      have h2 : |a * c + z - y| ≤ |a * c| + |z - y| := by
        have := abs_add_le (a * c) (z - y)
        rwa [show a * c + (z - y) = a * c + z - y by ring] at this
      have h3 : |a * c| ≤ |a| * Mb := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcb (abs_nonneg a)
      nlinarith

/-- `A \ B` finite implies `I_A ⊆ I_B`. -/
lemma IA_mono_of_diff_finite {A B : Set ℕ} (h : (A \ B).Finite) {J : Set ℝ} (hJ : J ∈ IA A) : J ∈ IA B := by
  obtain ⟨m, l, hJ'⟩ := mem_IA_iff.1 hJ
  obtain ⟨Mb0, hMb0⟩ := (h.image sS).bddAbove
  have hMb : ∀ n ∈ A, n ∉ B → sS n ≤ max Mb0 0 := fun n hn hnB =>
    le_trans (hMb0 ⟨n, ⟨hn, hnB⟩, rfl⟩) (le_max_left _ _)
  rw [mem_IA_iff]
  refine ⟨m + max Mb0 0 * (l.map (fun a => |a|)).sum, l, fun z hz => ?_⟩
  obtain ⟨y, σ, hy, hσ, rfl⟩ := hJ' z hz
  obtain ⟨σ', hσ', hd⟩ := sumSetA_approx (le_max_right _ _) hMb l σ hσ
  refine ⟨y + (σ - σ'), σ', ?_, hσ', by ring⟩
  exact (abs_add_le y (σ - σ')).trans (add_le_add hy hd)

/-- **(I1) to (I5) for `I_A`.** -/
theorem IA_isIdeal (A : Set ℕ) : IsIdeal (IA A) where
  mono := fun {J J'} hJ hJ' => by
    obtain ⟨m, l, h⟩ := hJ
    exact ⟨m, l, hJ'.trans h⟩
  union := fun {J J'} hJ hJ' => by
    rw [mem_IA_iff] at *
    obtain ⟨m, l, h⟩ := hJ
    obtain ⟨m', l', h'⟩ := hJ'
    refine ⟨max m m', l ++ l', fun z hz => ?_⟩
    rcases hz with hz | hz
    · obtain ⟨y, σ, hy, hσ, rfl⟩ := h z hz
      exact ⟨y, σ, hy.trans (le_max_left _ _), sumSetA_append_left A l l' hσ, rfl⟩
    · obtain ⟨y, σ, hy, hσ, rfl⟩ := h' z hz
      exact ⟨y, σ, hy.trans (le_max_right _ _), sumSetA_append_right A l l' hσ, rfl⟩
  single := fun x => bounded_mem_IA A (M := |x|) (fun a ha => by rw [Set.mem_singleton_iff.1 ha])
  ne_univ := fun h => univ_not_mem_IS (IA_sub_IS A h)
  add := fun {J J'} hJ hJ' => by
    rw [mem_IA_iff] at *
    obtain ⟨m, l, h⟩ := hJ
    obtain ⟨m', l', h'⟩ := hJ'
    refine ⟨m + m', l ++ l', fun z hz => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h a ha
    obtain ⟨y', σ', hy', hσ', rfl⟩ := h' b hb
    exact ⟨y + y', σ + σ', (abs_add_le y y').trans (add_le_add hy hy'),
      sumSetA_append_add A l l' σ σ' hσ hσ', by ring⟩
  smul := fun a {J} hJ => by
    rw [mem_IA_iff] at *
    obtain ⟨m, l, h⟩ := hJ
    refine ⟨|a| * m, l.map (fun c => a * c), fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.1 hz
    obtain ⟨y, σ, hy, hσ, rfl⟩ := h w hw
    refine ⟨a * y, a * σ, ?_, sumSetA_smul_mem A a l σ hσ, by simp [smul_eq_mul]; ring⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)

#print axioms IA_isIdeal
#print axioms IA_mono_of_diff_finite

end Lac
end PVG
