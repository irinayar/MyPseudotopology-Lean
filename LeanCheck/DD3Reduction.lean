import Mathlib
import LeanCheck.MixedPrimeAnalytic
import LeanCheck.JAMerged
import LeanCheck.JAEnergyIdentity

/-!
# Diagonal density for three primes: the reduction layer (Lean check)

Scope. These are the three-prime counterparts of the combinatorial and algebraic steps of the proof of joint
approximation (`JAAssembly`, `JAMerged`, `JAEnergyIdentity`, `JAWeilE`) that change when a third chain of prime
squares is added (research note `TVGplus_conditional_DD235_2026-11-07.md`, items 1, 5, 6, 7). They are
proved here for arbitrary finite sets and weights; nothing here uses the pseudonorms `P_p` themselves.

* `three_parts_zero` (item 7): if `m₂ a₂ = m₃ a₃ = m₅ a₅ = 0` for pairwise coprime `m_i` and `a₂ + a₃ + a₅ = 0`
  in an abelian group, then all `a_i = 0` (the `p`-primary parts of `ℚ/ℤ` are independent).
* `card_V3_ge`, `sum_rep3` (item 5): for finite `A, B, C ⊆ ℤ` and weights `f, g, h`, with
  `R(u,v) = ∑_{x - y = u, y - z = v} f(x) g(y) h(z)`: `(∑f ∑g ∑h)² ≤ |T| ∑_{w ∈ T} R(w)²`
  for every finite `T ⊆ ℤ²` containing all `(x - y, y - z)`.
* `energy3_eq_acf` (item 5): `∑_{w} R(w)²` (written as the collision sum over pairs of triples) equals
  `∑_d acf_A f(d) acf_B g(d) acf_C h(d)`, the product of three autocorrelations, for any finite `D ⊇ A - A`.
* `syndetic_of_dense_difference3` (item 6): if `W ⊆ ℤ²` is symmetric, contains `0`, and for arbitrarily large `X` there
  is a finite `V ⊆ [-X,X]²` with `|V| ≥ c (2X+1)²` and `V - V ⊆ W`, then `ℤ² = F + W` for a finite `F`.
* `merged_gap4`, `merged_gap_seq3`, `merged_growth_exp3`, `window_card_le_three` (item 1): among four increasing periods
  `b^(n²)`, `b ∈ {2,3,5}`, two share a base, so the span is at least `sqrt (lp)` of the smallest; hence
  `log Q_{i+3j} - log Q_i ≥ j sqrt (log Q_i)`, and a logarithmic window of width at most `sqrt u` holds at most three
  periods.

Not formalized: the cluster estimate with the third level (item 3), the central bound for three chains, the Weil
step for `ℤ²`, and the hypothesis `H(2,3,5)` itself. A Lean proof verifies its formal statement under its hypotheses;
the correspondence with the research note requires mathematical review.
-/

open Finset

namespace LeanCheck
namespace DD3

/-! ### A. Independence of prime-power torsion -/

lemma smul_mul_zero {G : Type*} [AddCommGroup G] {m : ℕ} {a : G} (h : m • a = 0) (k : ℕ) :
    (m * k) • a = 0 := by
  rw [mul_comm, mul_smul, h, smul_zero]

lemma eq_zero_of_coprime_smul {G : Type*} [AddCommGroup G] {m n : ℕ} (h : Nat.Coprime m n) {a : G}
    (hm : m • a = 0) (hn : n • a = 0) : a = 0 := by
  obtain ⟨u, v, huv⟩ : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have : a = (u * (m : ℤ) + v * (n : ℤ)) • a := by rw [huv, one_smul]
  rw [this, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hm, hn]
  simp

lemma part_zero {G : Type*} [AddCommGroup G] {ma mb mc : ℕ} (hab : Nat.Coprime ma mb)
    (hac : Nat.Coprime ma mc) {a b c : G} (ha : ma • a = 0) (hb : mb • b = 0) (hc : mc • c = 0)
    (hs : a + b + c = 0) : a = 0 := by
  have e : a = -(b + c) := by rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact hs
  have h1 : (mb * mc) • a = 0 := by
    rw [e, smul_neg, smul_add, smul_mul_zero hb mc, mul_comm, smul_mul_zero hc mb]
    simp
  exact eq_zero_of_coprime_smul (Nat.Coprime.mul_right hab hac) ha h1

/-- **Item 7.** If three elements of an abelian group are torsion of pairwise coprime orders and sum to zero,
each is zero. -/
theorem three_parts_zero {G : Type*} [AddCommGroup G] {m₂ m₃ m₅ : ℕ} (h23 : Nat.Coprime m₂ m₃)
    (h25 : Nat.Coprime m₂ m₅) (h35 : Nat.Coprime m₃ m₅) {a₂ a₃ a₅ : G} (h2 : m₂ • a₂ = 0)
    (h3 : m₃ • a₃ = 0) (h5 : m₅ • a₅ = 0) (hs : a₂ + a₃ + a₅ = 0) :
    a₂ = 0 ∧ a₃ = 0 ∧ a₅ = 0 := by
  refine ⟨part_zero h23 h25 h2 h3 h5 hs, ?_, ?_⟩
  · exact part_zero h23.symm h35 h3 h2 h5 (by rw [show a₃ + a₂ + a₅ = a₂ + a₃ + a₅ by abel]; exact hs)
  · exact part_zero h25.symm h35.symm h5 h2 h3
      (by rw [show a₅ + a₂ + a₃ = a₂ + a₃ + a₅ by abel]; exact hs)

/-! ### B. The three-fold collision energy -/

section Energy

/-- `(x, (y, z)) ↦ (x - y, y - z)`. -/
def phi (p : ℤ × (ℤ × ℤ)) : ℤ × ℤ := (p.1 - p.2.1, p.2.1 - p.2.2)

/-- The weight `f x * g y * h z` of a triple. -/
noncomputable def wt (f g h : ℤ → ℝ) (p : ℤ × (ℤ × ℤ)) : ℝ := f p.1 * g p.2.1 * h p.2.2

/-- Weighted representation function of the pair of differences `(x - y, y - z)`. -/
noncomputable def rep3 (A B C : Finset ℤ) (f g h : ℤ → ℝ) (w : ℤ × ℤ) : ℝ :=
  ∑ p ∈ A ×ˢ (B ×ˢ C), if phi p = w then wt f g h p else 0

lemma sum_fiber_sq {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (φ : ι → κ) (T : Finset κ)
    (F : ι → ℝ) (hφ : ∀ i ∈ S, φ i ∈ T) :
    ∑ k ∈ T, (∑ i ∈ S, if φ i = k then F i else 0) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, if φ i = φ j then F i * F j else 0 := by
  have h1 : ∀ k, (∑ i ∈ S, if φ i = k then F i else 0) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, (if φ i = k then F i else 0) * (if φ j = k then F j else 0) := by
    intro k; rw [sq, Finset.sum_mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h2 : ∀ k, (if φ i = k then F i else 0) * (if φ j = k then F j else 0) =
      if φ i = k then (if φ j = φ i then F i * F j else 0) else 0 := by
    intro k
    by_cases hk : φ i = k
    · subst hk; simp [mul_ite]
    · simp [hk]
  simp_rw [h2]
  rw [Finset.sum_ite_eq]
  simp only [hφ i hi, ↓reduceIte]
  by_cases h : φ i = φ j
  · simp [h]
  · simp [h, Ne.symm h]

/-- A product of three sums as one sum over a triple product. -/
lemma triple_prod_sum {α β γ : Type*} (P : Finset α) (Q : Finset β) (R : Finset γ)
    (a : α → ℝ) (b : β → ℝ) (c : γ → ℝ) :
    (∑ u ∈ P, a u) * (∑ v ∈ Q, b v) * (∑ w ∈ R, c w) =
      ∑ x ∈ P ×ˢ (Q ×ˢ R), a x.1 * b x.2.1 * c x.2.2 := by
  simp only [Finset.sum_product]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]

variable {A B C : Finset ℤ}

theorem sum_rep3 (f g h : ℤ → ℝ) (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ A ×ˢ (B ×ˢ C), phi p ∈ T) :
    ∑ w ∈ T, rep3 A B C f g h w = (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c) := by
  unfold rep3
  rw [Finset.sum_comm]
  have : ∀ p ∈ A ×ˢ (B ×ˢ C), (∑ w ∈ T, if phi p = w then wt f g h p else 0) = wt f g h p := by
    intro p hp
    rw [Finset.sum_ite_eq]
    simp only [hT p hp, ↓reduceIte]
  rw [Finset.sum_congr rfl this, triple_prod_sum]
  rfl

/-- **Item 5, Cauchy–Schwarz.** -/
theorem card_V3_ge (f g h : ℤ → ℝ) (T : Finset (ℤ × ℤ)) (hT : ∀ p ∈ A ×ˢ (B ×ˢ C), phi p ∈ T) :
    ((∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c)) ^ 2 ≤
      (T.card : ℝ) * ∑ w ∈ T, (rep3 A B C f g h w) ^ 2 := by
  rw [← sum_rep3 f g h T hT]
  have := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun w => rep3 A B C f g h w)
  simpa using this

/-- The sum of squares of the representation function is the collision sum over pairs of triples. -/
theorem sum_sq_rep3 (f g h : ℤ → ℝ) (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ A ×ˢ (B ×ˢ C), phi p ∈ T) :
    ∑ w ∈ T, (rep3 A B C f g h w) ^ 2 =
      ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        if phi p = phi q then wt f g h p * wt f g h q else 0 :=
  sum_fiber_sq (A ×ˢ (B ×ˢ C)) phi T (wt f g h) hT

lemma collapse (D : Finset ℤ) (a b c : ℤ) (α β γ : ℝ) (ha : a ∈ D) :
    ∑ d ∈ D, (if a = d then α else 0) * (if b = d then β else 0) * (if c = d then γ else 0) =
      if b = a ∧ c = a then α * β * γ else 0 := by
  rw [Finset.sum_eq_single a]
  · by_cases hb : b = a <;> by_cases hc : c = a <;> simp [hb, hc]
  · intro d _ hd
    simp [Ne.symm hd]
  · intro h; exact absurd ha h

/-- **Item 5, correlation form.** The collision sum equals `∑_d acf f(d) acf g(d) acf h(d)`. -/
theorem energy3_eq_acf (f g h : ℤ → ℝ) (D : Finset ℤ) (hD : ∀ a ∈ A, ∀ a' ∈ A, a' - a ∈ D) :
    ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if phi p = phi q then wt f g h p * wt f g h q else 0) =
      ∑ d ∈ D, JAEnergyIdentity.acf A f d * JAEnergyIdentity.acf B g d * JAEnergyIdentity.acf C h d := by
  classical
  have hacf : ∀ (E : Finset ℤ) (F : ℤ → ℝ) (d : ℤ), JAEnergyIdentity.acf E F d =
      ∑ u ∈ E ×ˢ E, if u.2 - u.1 = d then F u.1 * F u.2 else 0 := by
    intro E F d
    unfold JAEnergyIdentity.acf
    rw [Finset.sum_product]
  have hR : ∀ d, JAEnergyIdentity.acf A f d * JAEnergyIdentity.acf B g d *
        JAEnergyIdentity.acf C h d =
      ∑ x ∈ (A ×ˢ A) ×ˢ ((B ×ˢ B) ×ˢ (C ×ˢ C)),
        (if x.1.2 - x.1.1 = d then f x.1.1 * f x.1.2 else 0) *
        (if x.2.1.2 - x.2.1.1 = d then g x.2.1.1 * g x.2.1.2 else 0) *
        (if x.2.2.2 - x.2.2.1 = d then h x.2.2.1 * h x.2.2.2 else 0) := by
    intro d
    rw [hacf, hacf, hacf, triple_prod_sum]
  simp_rw [hR]
  conv_rhs => rw [Finset.sum_comm]
  refine (Finset.sum_product' (A ×ˢ (B ×ˢ C)) (A ×ˢ (B ×ˢ C))
    (fun p q => if phi p = phi q then wt f g h p * wt f g h q else 0)).symm.trans ?_
  refine Finset.sum_nbij'
    (fun z => ((z.1.1, z.2.1), ((z.1.2.1, z.2.2.1), (z.1.2.2, z.2.2.2))))
    (fun u => ((u.1.1, (u.2.1.1, u.2.2.1)), (u.1.2, (u.2.1.2, u.2.2.2))))
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_product] at hz ⊢
    tauto
  · intro u hu
    simp only [Finset.mem_product] at hu ⊢
    tauto
  · intro z _; rfl
  · intro u _; rfl
  · intro z hz
    simp only [Finset.mem_product] at hz
    rw [collapse D _ _ _ _ _ _ (hD _ hz.1.1 _ hz.2.1)]
    simp only [phi, wt, Prod.mk.injEq]
    by_cases hc : (z.1.1 - z.1.2.1 = z.2.1 - z.2.2.1 ∧ z.1.2.1 - z.1.2.2 = z.2.2.1 - z.2.2.2)
    · have h1 : z.2.2.1 - z.1.2.1 = z.2.1 - z.1.1 := by omega
      have h2 : z.2.2.2 - z.1.2.2 = z.2.1 - z.1.1 := by omega
      simp only [hc, h1, h2, and_self, ↓reduceIte]
      ring
    · have hn : ¬ (z.2.2.1 - z.1.2.1 = z.2.1 - z.1.1 ∧ z.2.2.2 - z.1.2.2 = z.2.1 - z.1.1) := by
        rintro ⟨h1, h2⟩
        exact hc ⟨by omega, by omega⟩
      simp only [hc, hn, ↓reduceIte]

end Energy

/-! ### C. Syndeticity in `ℤ²` from large difference sets -/

section Syndetic

theorem packing_card_le_gen {G : Type*} [AddCommGroup G] [DecidableEq G] (V F I : Finset G)
    (hdisj : ∀ f ∈ F, ∀ f' ∈ F, f ≠ f' →
      Disjoint (V.image (fun v => v + f)) (V.image (fun v => v + f')))
    (hsub : ∀ f ∈ F, V.image (fun v => v + f) ⊆ I) :
    F.card * V.card ≤ I.card := by
  have hpw : (F : Set G).PairwiseDisjoint (fun f => V.image (fun v => v + f)) := by
    intro f hf f' hf' hne
    exact hdisj f hf f' hf' hne
  have hcard : (F.biUnion (fun f => V.image (fun v => v + f))).card
      = ∑ f ∈ F, (V.image (fun v => v + f)).card := Finset.card_biUnion hpw
  have hinj : ∀ f : G, (V.image (fun v => v + f)).card = V.card := by
    intro f
    exact Finset.card_image_of_injective _ (add_left_injective f)
  have hsubU : F.biUnion (fun f => V.image (fun v => v + f)) ⊆ I := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨f, hf, hx⟩ := hx
    exact hsub f hf hx
  have := Finset.card_le_card hsubU
  rw [hcard] at this
  simp only [hinj, Finset.sum_const, smul_eq_mul] at this
  exact this

/-- **Item 6.** Large difference sets in a box give a syndetic set in `ℤ²`. -/
theorem syndetic_of_dense_difference3 (W : Set (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ W)
    (hsymm : ∀ w ∈ W, -w ∈ W) (c : ℝ) (hc : 0 < c)
    (hV : ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ ∃ V : Finset (ℤ × ℤ),
      (∀ v ∈ V, |v.1| ≤ X ∧ |v.2| ≤ X) ∧ (∀ v ∈ V, ∀ v' ∈ V, v' - v ∈ W) ∧
      c * (2 * (X : ℝ) + 1) ^ 2 ≤ (V.card : ℝ)) :
    ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, z - f ∈ W := by
  classical
  have hbound : ∀ s : Finset (ℤ × ℤ), (s : Set (ℤ × ℤ)).Pairwise (fun x y => x - y ∉ W) →
      s.card ≤ ⌈4 / c⌉₊ := by
    intro s hs
    set M : ℕ := s.sup (fun p => p.1.natAbs + p.2.natAbs) with hMdef
    obtain ⟨X, hMX, V, hVb, hVV, hcard⟩ := hV M
    have hdisj : ∀ f ∈ s, ∀ f' ∈ s, f ≠ f' →
        Disjoint (V.image (fun v => v + f)) (V.image (fun v => v + f')) := by
      intro f hf f' hf' hne
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_image] at hx hx'
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨v', hv', hvv⟩ := hx'
      apply hs hf hf' hne
      have : f - f' = v' - v := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm]
        exact hvv.symm
      rw [this]
      exact hVV v hv v' hv'
    set I : Finset (ℤ × ℤ) := Finset.Icc (-(X : ℤ) - M) ((X : ℤ) + M) ×ˢ
      Finset.Icc (-(X : ℤ) - M) ((X : ℤ) + M) with hI
    have hsub : ∀ f ∈ s, V.image (fun v => v + f) ⊆ I := by
      intro f hf x hx
      rw [Finset.mem_image] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      have h1 := abs_le.1 (hVb v hv).1
      have h2 := abs_le.1 (hVb v hv).2
      have h3 : f.1.natAbs + f.2.natAbs ≤ M :=
        Finset.le_sup (f := fun p : ℤ × ℤ => p.1.natAbs + p.2.natAbs) hf
      rw [hI, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      simp only [Prod.fst_add, Prod.snd_add]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
    have hpack := packing_card_le_gen V s I hdisj hsub
    have hIcard : I.card = (2 * X + 2 * M + 1) * (2 * X + 2 * M + 1) := by
      have e : ((X : ℤ) + M + 1 - (-(X : ℤ) - M)).toNat = 2 * X + 2 * M + 1 := by omega
      rw [hI, Finset.card_product, Int.card_Icc, e]
    rw [hIcard] at hpack
    have hMX' : (M : ℝ) ≤ X := by exact_mod_cast hMX
    have hpackR : (s.card : ℝ) * (V.card : ℝ) ≤ 4 * (2 * (X : ℝ) + 1) ^ 2 := by
      have h1 : ((s.card * V.card : ℕ) : ℝ) ≤
          (((2 * X + 2 * M + 1) * (2 * X + 2 * M + 1) : ℕ) : ℝ) := by exact_mod_cast hpack
      push_cast at h1
      nlinarith [Nat.cast_nonneg (α := ℝ) X, Nat.cast_nonneg (α := ℝ) M]
    have hX : (0 : ℝ) < (2 * (X : ℝ) + 1) ^ 2 := by positivity
    have hsc : (s.card : ℝ) * c ≤ 4 := by
      have : (s.card : ℝ) * (c * (2 * (X : ℝ) + 1) ^ 2) ≤ 4 * (2 * (X : ℝ) + 1) ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) hpackR
      nlinarith
    have : (s.card : ℝ) ≤ 4 / c := by rw [le_div_iff₀ hc]; exact hsc
    exact_mod_cast this.trans (Nat.le_ceil _)
  obtain ⟨s, hs⟩ := MixedPrimeAnalytic.finite_cover_of_bounded_packing
    (fun x y : ℤ × ℤ => x - y ∉ W)
    (fun a b hab hba => hab (by simpa using hsymm _ hba))
    (fun x hx => hx (by simpa using h0)) ⌈4 / c⌉₊ hbound
  exact ⟨s, fun z => by
    obtain ⟨y, hy, hn⟩ := hs z
    exact ⟨y, hy, not_not.mp hn⟩⟩

end Syndetic

/-! ### D. Merged growth of three chains -/

section Merged

open JAMerged

/-- **Item 1.** Among four increasing periods `b^(n^2)`, `b ∈ {2,3,5}`, two share a base, so the span is at least
`sqrt (lp)` of the smallest. -/
theorem merged_gap4 (b n : Fin 4 → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : StrictMono (fun i => lp (b i) (n i))) :
    Real.sqrt (lp (b 0) (n 0)) ≤ lp (b 3) (n 3) - lp (b 0) (n 0) := by
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hcard : ({2, 3, 5} : Finset ℕ).card < (Finset.univ : Finset (Fin 4)).card := by decide
  obtain ⟨x, -, y, -, hxy, hbxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin 4))) (t := ({2, 3, 5} : Finset ℕ)) hcard (f := b)
    (fun i _ => by rcases hb i with h | h | h <;> simp [h])
  have key : ∀ i j : Fin 4, i < j → b i = b j →
      Real.sqrt (lp (b 0) (n 0)) ≤ lp (b 3) (n 3) - lp (b 0) (n 0) := by
    intro i j hij hbij
    have hlt : lp (b i) (n i) < lp (b j) (n j) := hmono hij
    rw [← hbij] at hlt
    have hnm : n i < n j := lp_strict (hb2 i) hlt
    have hgap := same_chain_gap (hb2 i) hnm
    have hle0 : lp (b 0) (n 0) ≤ lp (b i) (n i) := hmono.monotone (Fin.zero_le i)
    have hle3 : lp (b j) (n j) ≤ lp (b 3) (n 3) := hmono.monotone (Fin.le_last j)
    have hs : Real.sqrt (lp (b 0) (n 0)) ≤ Real.sqrt (lp (b i) (n i)) := Real.sqrt_le_sqrt hle0
    have hbj : lp (b i) (n j) = lp (b j) (n j) := by rw [hbij]
    rw [hbj] at hgap
    linarith
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hbxy
  · exact key y x h hbxy.symm

/-- Merged growth: `log Q_{i+3j} - log Q_i ≥ j sqrt (log Q_i)` for every increasing selection. -/
theorem merged_gap_seq3 (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i j : ℕ) :
    (j : ℝ) * Real.sqrt (lp (b i) (n i)) ≤
      lp (b (i + 3 * j)) (n (i + 3 * j)) - lp (b i) (n i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : Real.sqrt (lp (b (i + 3 * j)) (n (i + 3 * j))) ≤
        lp (b (i + 3 * j + 3)) (n (i + 3 * j + 3)) - lp (b (i + 3 * j)) (n (i + 3 * j)) :=
      merged_gap4 (fun k : Fin 4 => b (i + 3 * j + k)) (fun k : Fin 4 => n (i + 3 * j + k))
        (fun k => hb _) (fun a a' haa => hmono (Nat.add_lt_add_left (Fin.lt_def.1 haa) _))
    have hge : Real.sqrt (lp (b i) (n i)) ≤ Real.sqrt (lp (b (i + 3 * j)) (n (i + 3 * j))) :=
      Real.sqrt_le_sqrt (hmono.monotone (by omega))
    have e : i + 3 * (j + 1) = i + 3 * j + 3 := by ring
    rw [e]
    push_cast
    nlinarith

/-- The same, for an arbitrary offset `m` (the exponent is `⌊m/3⌋`). -/
theorem merged_gap_seq_odd3 (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i m : ℕ) :
    ((m / 3 : ℕ) : ℝ) * Real.sqrt (lp (b i) (n i)) ≤
      lp (b (i + m)) (n (i + m)) - lp (b i) (n i) := by
  have h1 := merged_gap_seq3 b n hb hmono i (m / 3)
  have h2 : lp (b (i + 3 * (m / 3))) (n (i + 3 * (m / 3))) ≤ lp (b (i + m)) (n (i + m)) :=
    hmono.monotone (by omega)
  linarith

/-- Exponential form: `Q_{i+m} ≥ Q_i * exp (t_i ⌊m/3⌋)`, `t_i = sqrt (log Q_i)`. -/
theorem merged_growth_exp3 (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i m : ℕ) :
    Real.exp (lp (b i) (n i)) * Real.exp (Real.sqrt (lp (b i) (n i)) * ((m / 3 : ℕ) : ℝ)) ≤
      Real.exp (lp (b (i + m)) (n (i + m))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := merged_gap_seq_odd3 b n hb hmono i m
  linarith

/-- **At most three periods in a window** `[u, v]` with `v - u ≤ sqrt u`. -/
theorem window_card_le_three (s : Finset (ℕ × ℕ)) (u v : ℝ) (hw : v - u ≤ Real.sqrt u)
    (hs : ∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5) ∧ u ≤ lp p.1 p.2 ∧ lp p.1 p.2 ≤ v) :
    s.card ≤ 3 := by
  have hcard : s.card ≤ ({2, 3, 5} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have := (hs p hp).1
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact this
    · intro p hp q hq hpq
      have hp' := hs p hp
      have hq' := hs q hq
      have hb2 : 2 ≤ p.1 := by rcases hp'.1 with h | h | h <;> omega
      by_contra hne
      have hn : p.2 ≠ q.2 := fun h => hne (Prod.ext hpq h)
      rcases lt_or_gt_of_ne hn with h | h
      · have := chain_window_one (b := p.1) (n := p.2) (m := q.2) hb2 u v hp'.2.1
          (by rw [hpq]; exact hq'.2.2) h
        linarith
      · have := chain_window_one (b := q.1) (n := q.2) (m := p.2) (by rw [← hpq]; exact hb2) u v
          hq'.2.1 (by rw [← hpq]; exact hp'.2.2) h
        linarith
  have h3 : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
  omega

end Merged

end DD3
end LeanCheck
