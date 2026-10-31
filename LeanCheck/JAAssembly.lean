import LeanCheck.JAEnergy
import LeanCheck.MixedPrimeAnalytic
import LeanCheck.MixedPrimeRadii
import LeanCheck.MixedPrimeColoured

/-!
# Assembly of the joint-approximation argument (components 10, 17 and the Stage A statement)

This module formalizes the combinatorial skeleton of the proof of `thm:joint-approximation` in `TVGaddmore_v27`
(last two paragraphs of its proof) and the logical reduction to the two inputs that are not in Mathlib.

Checked here (no axiom, no `sorry`; all hypotheses explicit):

* `card_V_ge`: weighted Cauchy-Schwarz.  If a weighted collision energy on `[-X, X]` is at most `K` times the
  normalized value `(Σf Σg)^2 / (2X+1)`, then the difference set `V = A_3 - A_2` has at least `(2X+1)/K` elements
  (the step "weighted Cauchy-Schwarz gives `|V_X| ≥ c_D (2X+1)`").
* `syndetic_of_dense_difference`: if for arbitrarily large `X` there are supports `A_2, A_3 ⊆ [0, X]` with
  `A_p - A_p ⊆ U_p` and `|A_3 - A_2| ≥ c (2X+1)`, then `W = U_3 - U_2` is syndetic (translates of `V` are disjoint
  when the shifts are `W`-separated, they fit in an interval of length `2X` plus a constant, so a `W`-separated
  family has at most `2/c` members; a maximal one is a finite cover; `finite_cover_of_bounded_packing`).
* `JA_of_dense_differences` (Stage A): the joint-approximation property `JAProp` follows from the density input
  `hdense` at every precision and the compact-quotient criterion, which is carried as the explicit hypothesis
  `CompactQuotientCriterion` (Corollary "bounded-gap criterion", direction "syndetic implies JA"; it needs completeness
  and character separation on a compact abelian group, which are not in Mathlib).

Not checked here: `hdense` itself (it is the output of the normalized-product argument, i.e. the Matveev two-term
separation, the window kernels and the random-translation averaging), and `CompactQuotientCriterion`.
-/

namespace LeanCheck
namespace JAAssembly

open MixedPrime JAEnergy MixedPrimeAnalytic

/-- `V = A_3 - A_2` as a finite set. -/
def Vset (A3 A2 : Finset ℤ) : Finset ℤ := (A3 ×ˢ A2).image (fun p => p.1 - p.2)

lemma mem_Vset {A3 A2 : Finset ℤ} {v : ℤ} : v ∈ Vset A3 A2 ↔ ∃ a ∈ A3, ∃ b ∈ A2, a - b = v := by
  unfold Vset
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩; exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨a, b, ⟨ha, hb⟩, h⟩

/-- **Weighted Cauchy-Schwarz**: a normalized energy bound forces a large difference set. -/
theorem card_V_ge (X : ℕ) (A3 A2 : Finset ℤ) (f g : ℤ → ℝ)
    (h3 : ∀ a ∈ A3, 0 ≤ a ∧ a ≤ X) (h2 : ∀ b ∈ A2, 0 ≤ b ∧ b ≤ X)
    (hm : 0 < (∑ a ∈ A3, f a) * (∑ b ∈ A2, g b)) (K : ℝ) (hK : 0 < K)
    (hE : ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep A3 A2 f g d) ^ 2 ≤
      K * ((∑ a ∈ A3, f a) * (∑ b ∈ A2, g b)) ^ 2 / (2 * (X : ℝ) + 1)) :
    (2 * (X : ℝ) + 1) / K ≤ ((Vset A3 A2).card : ℝ) := by
  set m := (∑ a ∈ A3, f a) * (∑ b ∈ A2, g b) with hmdef
  have hT : ∀ a ∈ A3, ∀ b ∈ A2, a - b ∈ Vset A3 A2 := fun a ha b hb => mem_Vset.mpr ⟨a, ha, b, hb, rfl⟩
  have hcs := cs_difference A3 A2 f g (Vset A3 A2) hT
  have hVsub : Vset A3 A2 ⊆ Finset.Icc (-(X : ℤ)) X := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_Vset.mp hv
    rw [Finset.mem_Icc]
    have := h3 a ha; have := h2 b hb
    constructor <;> omega
  have hle : ∑ d ∈ Vset A3 A2, (rep A3 A2 f g d) ^ 2 ≤ ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep A3 A2 f g d) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hVsub (fun _ _ _ => sq_nonneg _)
  have hX : (0 : ℝ) < 2 * (X : ℝ) + 1 := by positivity
  have hm2 : 0 < m ^ 2 := by positivity
  have hVc : (0 : ℝ) ≤ ((Vset A3 A2).card : ℝ) := Nat.cast_nonneg _
  -- m^2 ≤ |V| * E ≤ |V| * K m^2 / (2X+1)
  have h1 : m ^ 2 ≤ ((Vset A3 A2).card : ℝ) * (K * m ^ 2 / (2 * (X : ℝ) + 1)) :=
    hcs.trans (mul_le_mul_of_nonneg_left (hle.trans hE) hVc)
  rw [div_le_iff₀ hK]
  have h2' : m ^ 2 * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ) * (K * m ^ 2) := by
    have := mul_le_mul_of_nonneg_right h1 hX.le
    calc m ^ 2 * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ) * (K * m ^ 2 / (2 * (X : ℝ) + 1)) *
        (2 * (X : ℝ) + 1) := this
      _ = ((Vset A3 A2).card : ℝ) * (K * m ^ 2) := by field_simp
  nlinarith

/-- The set of attainable differences `W = U_3 - U_2`. -/
def DiffSet (U3 U2 : Set ℤ) : Set ℤ := {w | ∃ a ∈ U3, ∃ b ∈ U2, w = a - b}

/-- **Large difference sets give a syndetic set** (the packing argument of the proof of JA). -/
theorem syndetic_of_dense_difference (U2 U3 : Set ℤ) (h2 : (0 : ℤ) ∈ U2) (h3 : (0 : ℤ) ∈ U3)
    (hs2 : ∀ k ∈ U2, -k ∈ U2) (hs3 : ∀ k ∈ U3, -k ∈ U3) (c : ℝ) (hc : 0 < c)
    (hV : ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ ∃ A2 A3 : Finset ℤ,
      (∀ a ∈ A2, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ A3, 0 ≤ a ∧ a ≤ X) ∧
      (∀ a ∈ A3, ∀ a' ∈ A3, a - a' ∈ U3) ∧ (∀ b ∈ A2, ∀ b' ∈ A2, b - b' ∈ U2) ∧
      c * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ)) :
    ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, z - f ∈ DiffSet U3 U2 := by
  classical
  set W := DiffSet U3 U2 with hW
  have h0W : (0 : ℤ) ∈ W := ⟨0, h3, 0, h2, by simp⟩
  have hsymW : ∀ w ∈ W, -w ∈ W := by
    rintro w ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, hs3 a ha, -b, hs2 b hb, by ring⟩
  have hbound : ∀ s : Finset ℤ, (s : Set ℤ).Pairwise (fun x y => x - y ∉ W) → s.card ≤ ⌈2 / c⌉₊ := by
    intro s hs
    set M : ℕ := s.sup Int.natAbs with hMdef
    obtain ⟨X, hMX, A2, A3, hA2, hA3, hd3, hd2, hcard⟩ := hV M
    set V := Vset A3 A2 with hVdef
    have hVsub : ∀ v ∈ V, -(X : ℤ) ≤ v ∧ v ≤ X := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_Vset.mp hv
      have := hA3 a ha; have := hA2 b hb
      constructor <;> omega
    have hVV : ∀ v ∈ V, ∀ v' ∈ V, v' - v ∈ W := by
      intro v hv v' hv'
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_Vset.mp hv
      obtain ⟨a', ha', b', hb', rfl⟩ := mem_Vset.mp hv'
      exact ⟨a' - a, hd3 a' ha' a ha, b' - b, hd2 b' hb' b hb, by ring⟩
    have hdisj : ∀ f ∈ s, ∀ f' ∈ s, f ≠ f' →
        Disjoint (V.image (fun v => v + f)) (V.image (fun v => v + f')) := by
      intro f hf f' hf' hne
      apply disjoint_translates_of_not_mem
      intro v hv v' hv' heq
      exact hs hf hf' hne (heq ▸ hVV v hv v' hv')
    set I := Finset.Icc (-(X : ℤ) - (M : ℤ)) ((X : ℤ) + (M : ℤ)) with hI
    have hsub : ∀ f ∈ s, V.image (fun v => v + f) ⊆ I := by
      intro f hf x hx
      rw [Finset.mem_image] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      have h1 := hVsub v hv
      have h2 : f.natAbs ≤ M := Finset.le_sup (f := Int.natAbs) hf
      rw [hI, Finset.mem_Icc]
      constructor <;> omega
    have hpack := packing_card_le V s I hdisj hsub
    have hIcard : I.card = 2 * X + 2 * M + 1 := by
      rw [hI, Int.card_Icc]; omega
    have hMX' : (M : ℝ) ≤ X := by exact_mod_cast hMX
    have hpackR : (s.card : ℝ) * (V.card : ℝ) ≤ 2 * (2 * (X : ℝ) + 1) := by
      have h1 : ((s.card * V.card : ℕ) : ℝ) ≤ ((I.card : ℕ) : ℝ) := by exact_mod_cast hpack
      rw [hIcard] at h1
      push_cast at h1
      nlinarith
    have hX : (0 : ℝ) < 2 * (X : ℝ) + 1 := by positivity
    have hsc : (s.card : ℝ) * c ≤ 2 := by
      have : (s.card : ℝ) * (c * (2 * (X : ℝ) + 1)) ≤ 2 * (2 * (X : ℝ) + 1) :=
        le_trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) hpackR
      nlinarith
    have : (s.card : ℝ) ≤ 2 / c := by rw [le_div_iff₀ hc]; exact hsc
    exact_mod_cast this.trans (Nat.le_ceil _)
  obtain ⟨s, hs⟩ := finite_cover_of_bounded_packing (fun x y : ℤ => x - y ∉ W)
    (fun a b hab hba => hab (by simpa using hsymW _ hba))
    (fun x hx => hx (by simpa using h0W)) ⌈2 / c⌉₊ hbound
  exact ⟨s, fun z => by
    obtain ⟨y, hy, hn⟩ := hs z
    exact ⟨y, hy, not_not.mp hn⟩⟩

/-! ### Stage A: joint approximation from the density input and the compact-quotient criterion -/

/-- `U_{p,r} = {k : P_p(k) < r}`. -/
def Uset (p : ℕ) (r : ℝ) : Set ℤ := {k | Pn (sqScales p) k < r}

/-- Joint approximation: `P_3(k) < δ` and `P_2(k-1) < δ` for some integer `k`, for every `δ > 0`. -/
def JAProp : Prop := ∀ δ : ℝ, 0 < δ → ∃ k : ℤ, Pn (sqScales 3) k < δ ∧ Pn (sqScales 2) (k - 1) < δ

/-- `W_ε = U_{3,ε} - U_{2,ε}` is syndetic for every `ε > 0`. -/
def SyndeticW : Prop := ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, z - f ∈ DiffSet (Uset 3 ε) (Uset 2 ε)

/-- **Hypothesis (not proved here)**: the compact-quotient criterion of Corollary "bounded-gap criterion",
direction "syndetic implies JA" (completion, total boundedness, trivial dual, character separation). -/
def CompactQuotientCriterion : Prop := SyndeticW → JAProp

/-- The density input at precision `ε`: arbitrarily large supports with small self-differences and many differences. -/
def DenseDifferences (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ ∃ A2 A3 : Finset ℤ,
    (∀ a ∈ A2, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ A3, 0 ≤ a ∧ a ≤ X) ∧
    (∀ a ∈ A3, ∀ a' ∈ A3, Pn (sqScales 3) (a - a') < ε) ∧
    (∀ b ∈ A2, ∀ b' ∈ A2, Pn (sqScales 2) (b - b') < ε) ∧
    c * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ)

theorem syndeticW_of_dense (h : ∀ ε : ℝ, 0 < ε → DenseDifferences ε) : SyndeticW := by
  intro ε hε
  obtain ⟨c, hc, hV⟩ := h ε hε
  refine syndetic_of_dense_difference (Uset 2 ε) (Uset 3 ε) ?_ ?_ ?_ ?_ c hc hV
  · show Pn (sqScales 2) 0 < ε
    rw [Pn_zero]; exact hε
  · show Pn (sqScales 3) 0 < ε
    rw [Pn_zero]; exact hε
  · intro k hk; show Pn (sqScales 2) (-k) < ε; rw [Pn_neg]; exact hk
  · intro k hk; show Pn (sqScales 3) (-k) < ε; rw [Pn_neg]; exact hk

/-- **Stage A.**  The density input at every precision, together with the compact-quotient criterion, gives JA. -/
theorem JA_of_dense_differences (hQ : CompactQuotientCriterion)
    (h : ∀ ε : ℝ, 0 < ε → DenseDifferences ε) : JAProp :=
  hQ (syndeticW_of_dense h)

#print axioms card_V_ge
#print axioms syndetic_of_dense_difference
#print axioms syndeticW_of_dense
#print axioms JA_of_dense_differences

end JAAssembly
end LeanCheck
