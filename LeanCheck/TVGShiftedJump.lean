import LeanCheck.TVGPlusOrderB

/-!
# TVGplus: the jump argument and the unconditional limsup lower bound for the shifted height

Formal counterpart of the argument of the Codex note of 6 November 2026, 15:13 (audited by Claude
the same day). Two disjoint finite sets `S1`, `S2` of primes; the shifted ball at radius `δ` is
`W δ = {k | P_p(k - 1) < δ for p ∈ S1, P_q(k) < δ for q ∈ S2}` (`InBall S1 δ (k-1) ∧ InBall S2 δ k`),
`D_n = D_{S1}(e^{-n}) D_{S2}(e^{-n})`, `height n` is the least `|k|` with `k ∈ W (e^{-n})`.

* `exists_jump`, `jump_abstract`: abstract form. For an antitone family `W n` of nonempty sets of
  integers with empty intersection, there are arbitrarily large `n` with `height n < height (n+1)`,
  and then `D_n ≤ 2 · height (n+1)` whenever two different members of `W n` differ by at least `D_n`.
* `Dvis_unbounded`: `D_S(e^{-n})` is unbounded for a nonempty set `S` of primes.
* `shifted_jump`: the jump inequality `D_n ≤ 2 · height (n+1)` for the shifted problem.
* `shifted_limsup_lower`: if every `W (e^{-n})` is nonempty, then for every `0 ≤ b < c_{S1} + c_{S2}`
  and every `N` there is `m ≥ N` with `exp (b m²) ≤ height m`, that is,
  `limsup log height / n² ≥ c_{S1} + c_{S2}`.

The existence hypothesis (witnesses at every radius) is an assumption here; it is not proved.
-/

namespace LeanCheck
namespace ShiftedJump

open LeanCheck.MixedPrime LeanCheck.TVGPlus

section Abstract

/-- The least absolute value of an element of `W n`. -/
noncomputable def height (W : ℕ → Set ℤ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k ∈ W n, k.natAbs = m}

lemma height_spec {W : ℕ → Set ℤ} {n : ℕ} (h : (W n).Nonempty) :
    ∃ k ∈ W n, k.natAbs = height W n := by
  have : {m : ℕ | ∃ k ∈ W n, k.natAbs = m}.Nonempty := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k.natAbs, k, hk, rfl⟩
  exact Nat.sInf_mem this

lemma height_le {W : ℕ → Set ℤ} {n : ℕ} {k : ℤ} (hk : k ∈ W n) : height W n ≤ k.natAbs :=
  Nat.sInf_le ⟨k, hk, rfl⟩

lemma height_mono {W : ℕ → Set ℤ} (hanti : Antitone W) {n : ℕ} (h : (W (n + 1)).Nonempty) :
    height W n ≤ height W (n + 1) := by
  obtain ⟨k, hk, hkh⟩ := height_spec h
  rw [← hkh]
  exact height_le (hanti (Nat.le_succ n) hk)

/-- The heights of an antitone family of nonempty sets with empty intersection jump infinitely often. -/
theorem exists_jump {W : ℕ → Set ℤ} (hanti : Antitone W) (hne : ∀ n, (W n).Nonempty)
    (hempty : ∀ k : ℤ, ∃ n, k ∉ W n) (N : ℕ) : ∃ n ≥ N, height W n < height W (n + 1) := by
  by_contra hcon
  have hle : ∀ n ≥ N, height W (n + 1) ≤ height W n := by
    intro n hn
    by_contra h
    exact hcon ⟨n, hn, not_le.1 h⟩
  have hconst : ∀ n ≥ N, height W n = height W N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [le_antisymm (hle n hn) (height_mono hanti (hne (n + 1))), ih]
  set H := height W N with hH
  by_cases hall : ∀ n ≥ N, (H : ℤ) ∈ W n
  · obtain ⟨n, hn⟩ := hempty H
    by_cases hnN : n ≥ N
    · exact hn (hall n hnN)
    · exact hn (hanti (by omega : n ≤ N) (hall N le_rfl))
  · obtain ⟨n1, hn1'⟩ := Classical.not_forall.1 hall
    obtain ⟨hn1, hn1H⟩ := Classical.not_forall.1 hn1'
    have hneg : ∀ n ≥ N, (-(H : ℤ)) ∈ W n := by
      intro n hn
      obtain ⟨a, ha, hah⟩ := height_spec (hne (max n n1))
      have hh : height W (max n n1) = H := hconst _ (le_trans hn (le_max_left _ _))
      have ha1 : a ∈ W n1 := hanti (le_max_right _ _) ha
      have haH : a.natAbs = H := by rw [hah, hh]
      rcases Int.natAbs_eq a with h | h
      · exfalso
        apply hn1H
        rw [h, haH] at ha1
        exact ha1
      · have : a = -(H : ℤ) := by rw [h, haH]
        rw [← this]
        exact hanti (le_max_left _ _) ha
    obtain ⟨n, hn⟩ := hempty (-(H : ℤ))
    by_cases hnN : n ≥ N
    · exact hn (hneg n hnN)
    · exact hn (hanti (by omega : n ≤ N) (hneg N le_rfl))

/-- Jump inequality, abstract form. -/
theorem jump_abstract {W : ℕ → Set ℤ} (Dn : ℕ → ℕ) (hanti : Antitone W)
    (hne : ∀ n, (W n).Nonempty) (hempty : ∀ k : ℤ, ∃ n, k ∉ W n)
    (hdiv : ∀ n, ∀ a ∈ W n, ∀ b ∈ W n, a ≠ b → (Dn n : ℤ) ≤ |a - b|) (N : ℕ) :
    ∃ n ≥ N, height W n < height W (n + 1) ∧ Dn n ≤ 2 * height W (n + 1) := by
  obtain ⟨n, hn, hlt⟩ := exists_jump hanti hne hempty N
  refine ⟨n, hn, hlt, ?_⟩
  obtain ⟨a, ha, hah⟩ := height_spec (hne (n + 1))
  obtain ⟨b, hb, hbh⟩ := height_spec (hne n)
  have ha' : a ∈ W n := hanti (Nat.le_succ n) ha
  have hab : a ≠ b := by
    intro h
    subst h
    omega
  have h1 := hdiv n a ha' b hb hab
  have h2 : |a - b| ≤ |a| + |b| := abs_sub a b
  have hA : |a| = (a.natAbs : ℤ) := Int.abs_eq_natAbs a
  have hB : |b| = (b.natAbs : ℤ) := Int.abs_eq_natAbs b
  rw [hA, hB] at h2
  have h3 : (Dn n : ℤ) ≤ (a.natAbs : ℤ) + (b.natAbs : ℤ) := le_trans h1 h2
  have h4 : Dn n ≤ a.natAbs + b.natAbs := by exact_mod_cast h3
  omega

end Abstract

section Shifted

variable (S1 S2 : Finset ℕ)

/-- Shifted ball: `P_p(k - 1) < δ` for `p ∈ S1` and `P_q(k) < δ` for `q ∈ S2`. -/
def Wsh (δ : ℝ) : Set ℤ := {k | InBall S1 δ (k - 1) ∧ InBall S2 δ k}

/-- The radii `e^{-n}`. -/
noncomputable def rad (n : ℕ) : ℝ := Real.exp (-(n : ℝ))

lemma rad_pos (n : ℕ) : 0 < rad n := Real.exp_pos _

lemma rad_anti {m n : ℕ} (h : m ≤ n) : rad n ≤ rad m := by
  unfold rad
  exact Real.exp_le_exp.2 (by have : (m : ℝ) ≤ n := by exact_mod_cast h
                              linarith)

lemma inBall_mono {S : Finset ℕ} {δ δ' : ℝ} (h : δ' ≤ δ) {k : ℤ} (hk : InBall S δ' k) :
    InBall S δ k := fun p hp => lt_of_lt_of_le (hk p hp) h

/-- The family `W n = Wsh (e^{-n})`. -/
def Wn (n : ℕ) : Set ℤ := Wsh S1 S2 (rad n)

/-- The product of the two universal divisors at radius `e^{-n}`. -/
noncomputable def Dn (n : ℕ) : ℕ := Dvis S1 (rad n) * Dvis S2 (rad n)

lemma Wn_anti : Antitone (Wn S1 S2) := by
  intro m n h k hk
  exact ⟨inBall_mono (rad_anti h) hk.1, inBall_mono (rad_anti h) hk.2⟩

variable {S1 S2}

lemma coprime_Dvis (hS1 : ∀ p ∈ S1, p.Prime) (hS2 : ∀ p ∈ S2, p.Prime) (hd : Disjoint S1 S2)
    (δ : ℝ) : Nat.Coprime (Dvis S1 δ) (Dvis S2 δ) := by
  unfold Dvis
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (hS1 p hp) (hS2 q hq)).2 (fun h => by
    subst h
    exact Finset.disjoint_left.1 hd hp hq)

lemma Wn_div (hS1 : ∀ p ∈ S1, p.Prime) (hS2 : ∀ p ∈ S2, p.Prime) (hd : Disjoint S1 S2) (n : ℕ) :
    ∀ a ∈ Wn S1 S2 n, ∀ b ∈ Wn S1 S2 n, a ≠ b → (Dn S1 S2 n : ℤ) ≤ |a - b| := by
  intro a ha b hb hab
  have h1a := forced hS1 (rad_pos n) ha.1
  have h1b := forced hS1 (rad_pos n) hb.1
  have h2a := forced hS2 (rad_pos n) ha.2
  have h2b := forced hS2 (rad_pos n) hb.2
  have hd1 : (Dvis S1 (rad n) : ℤ) ∣ a - b := by
    have := dvd_sub h1a h1b
    have e : a - 1 - (b - 1) = a - b := by ring
    rwa [e] at this
  have hd2 : (Dvis S2 (rad n) : ℤ) ∣ a - b := dvd_sub h2a h2b
  have hcop : IsCoprime (Dvis S1 (rad n) : ℤ) (Dvis S2 (rad n) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (coprime_Dvis hS1 hS2 hd (rad n))
  have hmul := hcop.mul_dvd hd1 hd2
  have hne : a - b ≠ 0 := sub_ne_zero.2 hab
  have : ((Dvis S1 (rad n) * Dvis S2 (rad n) : ℕ) : ℤ) ∣ |a - b| := by
    push_cast
    exact (dvd_abs _ _).2 hmul
  exact Int.le_of_dvd (abs_pos.2 hne) this

lemma cS_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) : 0 < cS S := by
  unfold cS
  apply Finset.sum_pos _ hne
  intro p hp
  have : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hS p hp).one_lt)
  positivity

lemma log_rad (n : ℕ) : Real.log (1 / rad n) = n := by
  unfold rad
  rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

lemma Dvis_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (δ : ℝ) : 0 < Dvis S δ := by
  unfold Dvis
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hS p hp).pos _

/-- `exp (c n² - |S| n / 2) ≤ D_S(e^{-n})` once `n ≥ log p` for all `p ∈ S`. -/
lemma exp_le_Dvis {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {n : ℕ}
    (hn : ∀ p ∈ S, Real.log p ≤ n) :
    Real.exp ((n : ℝ) ^ 2 * cS S - S.card * ((n : ℝ) / 2)) ≤ (Dvis S (rad n) : ℝ) := by
  have hge := log_Dvis_ge S hS (rad_pos n) (by
    intro p hp
    rw [log_rad]
    exact hn p hp)
  rw [log_rad] at hge
  have hpos : (0 : ℝ) < Dvis S (rad n) := by exact_mod_cast Dvis_pos hS (rad n)
  calc Real.exp ((n : ℝ) ^ 2 * cS S - S.card * ((n : ℝ) / 2))
      ≤ Real.exp (Real.log (Dvis S (rad n) : ℝ)) := Real.exp_le_exp.2 hge
    _ = (Dvis S (rad n) : ℝ) := Real.exp_log hpos

/-- `D_S(e^{-n})` is unbounded for a nonempty set of primes. -/
lemma Dvis_unbounded {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (H : ℕ) :
    ∃ n : ℕ, H < Dvis S (rad n) := by
  have hc := cS_pos hS hne
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max 1 (∑ p ∈ S, Real.log p))
    ((S.card / 2 + H) / cS S))
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hlog : ∀ p ∈ S, Real.log p ≤ n := by
    intro p hp
    have h0 : ∀ q ∈ S, 0 ≤ Real.log q := fun q hq =>
      (Real.log_pos (by exact_mod_cast (hS q hq).one_lt)).le
    have : Real.log p ≤ ∑ q ∈ S, Real.log q :=
      Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ)) h0 hp
    exact le_trans this (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  refine ⟨n, ?_⟩
  have hexp := exp_le_Dvis hS hlog
  have hn2 : (S.card / 2 + H) / cS S ≤ n := le_trans (le_max_right _ _) hn
  have h3 : (S.card / 2 + H : ℝ) ≤ n * cS S := by
    rwa [div_le_iff₀ hc] at hn2
  have h4 : (H : ℝ) ≤ (n : ℝ) ^ 2 * cS S - S.card * ((n : ℝ) / 2) := by
    have h5 : (S.card : ℝ) / 2 * n + H ≤ n * (n * cS S) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) H, Nat.cast_nonneg (α := ℝ) S.card]
    nlinarith
  have h6 := Real.add_one_le_exp ((n : ℝ) ^ 2 * cS S - S.card * ((n : ℝ) / 2))
  have : (H : ℝ) < Dvis S (rad n) := by linarith
  exact_mod_cast this

lemma Wn_empty (hS1 : ∀ p ∈ S1, p.Prime) (hS2 : ∀ p ∈ S2, p.Prime)
    (hne1 : S1.Nonempty) (hne2 : S2.Nonempty) (k : ℤ) : ∃ n, k ∉ Wn S1 S2 n := by
  by_contra hcon0
  have hcon : ∀ n, k ∈ Wn S1 S2 n := fun n => by
    by_contra h
    exact hcon0 ⟨n, h⟩
  by_cases hk1 : k - 1 = 0
  · -- then k = 1, and `D_{S2}(e^{-n}) ∣ 1` for every n
    obtain ⟨n, hn⟩ := Dvis_unbounded hS2 hne2 1
    have hdv := forced hS2 (rad_pos n) (hcon n).2
    have hk : k = 1 := by omega
    rw [hk] at hdv
    have := Int.le_of_dvd one_pos hdv
    have : (Dvis S2 (rad n) : ℤ) ≤ 1 := this
    omega
  · obtain ⟨n, hn⟩ := Dvis_unbounded hS1 hne1 (k - 1).natAbs
    have hdv := forced hS1 (rad_pos n) (hcon n).1
    have := Int.natAbs_le_of_dvd_ne_zero hdv hk1
    have h2 : Dvis S1 (rad n) ≤ (k - 1).natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hdv
      exact Nat.le_of_dvd (Int.natAbs_pos.2 hk1) (by simpa using this)
    omega

/-- Jump inequality for the shifted problem: if every shifted ball is nonempty, then for every `N`
there is `n ≥ N` with `D_n ≤ 2 · height (n+1)` (and `height n < height (n+1)`). -/
theorem shifted_jump (hS1 : ∀ p ∈ S1, p.Prime) (hS2 : ∀ p ∈ S2, p.Prime) (hd : Disjoint S1 S2)
    (hne1 : S1.Nonempty) (hne2 : S2.Nonempty) (hne : ∀ n, (Wn S1 S2 n).Nonempty) (N : ℕ) :
    ∃ n ≥ N, height (Wn S1 S2) n < height (Wn S1 S2) (n + 1) ∧
      Dn S1 S2 n ≤ 2 * height (Wn S1 S2) (n + 1) :=
  jump_abstract (Dn S1 S2) (Wn_anti S1 S2) hne (Wn_empty hS1 hS2 hne1 hne2)
    (Wn_div hS1 hS2 hd) N

/-- **Unconditional limsup lower bound** (given witnesses at every radius): for every
`0 ≤ b < c_{S1} + c_{S2}` and every `N` there is `m ≥ N` with `exp (b m²) ≤ height m`. -/
theorem shifted_limsup_lower (hS1 : ∀ p ∈ S1, p.Prime) (hS2 : ∀ p ∈ S2, p.Prime)
    (hd : Disjoint S1 S2) (hne1 : S1.Nonempty) (hne2 : S2.Nonempty)
    (hne : ∀ n, (Wn S1 S2 n).Nonempty) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < cS S1 + cS S2) (N : ℕ) :
    ∃ m ≥ N, Real.exp (b * (m : ℝ) ^ 2) ≤ (height (Wn S1 S2) m : ℝ) := by
  set c := cS S1 + cS S2 with hc
  set s : ℝ := S1.card + S2.card with hs
  have hcb : 0 < c - b := by linarith
  have hs0 : 0 ≤ s := by positivity
  -- threshold `n₁`
  obtain ⟨n1, hn1⟩ := exists_nat_ge (max (max 1 ((∑ p ∈ S1, Real.log p) + ∑ p ∈ S2, Real.log p))
    ((2 * b + s / 2 + b + Real.log 2 + 1) / (c - b) + 1))
  have hn1one : (1 : ℝ) ≤ n1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn1
  have hlogsum : (∑ p ∈ S1, Real.log p) + ∑ p ∈ S2, Real.log p ≤ n1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn1
  have hn1b : (2 * b + s / 2 + b + Real.log 2 + 1) / (c - b) + 1 ≤ n1 := le_trans (le_max_right _ _) hn1
  obtain ⟨n, hn, _, hD⟩ := shifted_jump hS1 hS2 hd hne1 hne2 hne (max N n1)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnn1 : n1 ≤ n := le_trans (le_max_right _ _) hn
  have hnr : (n1 : ℝ) ≤ n := by exact_mod_cast hnn1
  have hlog0 : ∀ q ∈ S1 ∪ S2, 0 ≤ Real.log q := by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact (Real.log_pos (by exact_mod_cast (hS1 q h).one_lt)).le
    · exact (Real.log_pos (by exact_mod_cast (hS2 q h).one_lt)).le
  have hlogS1 : ∀ p ∈ S1, Real.log p ≤ n := by
    intro p hp
    have h0 : ∀ q ∈ S1, 0 ≤ Real.log q := fun q hq => hlog0 q (Finset.mem_union_left _ hq)
    have h1 : Real.log p ≤ ∑ q ∈ S1, Real.log q := Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ)) h0 hp
    have h2 : 0 ≤ ∑ q ∈ S2, Real.log q :=
      Finset.sum_nonneg (fun q hq => hlog0 q (Finset.mem_union_right _ hq))
    linarith
  have hlogS2 : ∀ p ∈ S2, Real.log p ≤ n := by
    intro p hp
    have h0 : ∀ q ∈ S2, 0 ≤ Real.log q := fun q hq => hlog0 q (Finset.mem_union_right _ hq)
    have h1 : Real.log p ≤ ∑ q ∈ S2, Real.log q := Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ)) h0 hp
    have h2 : 0 ≤ ∑ q ∈ S1, Real.log q :=
      Finset.sum_nonneg (fun q hq => hlog0 q (Finset.mem_union_left _ hq))
    linarith
  have e1 := exp_le_Dvis hS1 hlogS1
  have e2 := exp_le_Dvis hS2 hlogS2
  have hprod : Real.exp ((n : ℝ) ^ 2 * c - s * ((n : ℝ) / 2)) ≤ (Dn S1 S2 n : ℝ) := by
    have : Real.exp ((n : ℝ) ^ 2 * c - s * ((n : ℝ) / 2)) =
        Real.exp ((n : ℝ) ^ 2 * cS S1 - S1.card * ((n : ℝ) / 2)) *
        Real.exp ((n : ℝ) ^ 2 * cS S2 - S2.card * ((n : ℝ) / 2)) := by
      rw [← Real.exp_add]; congr 1; rw [hc, hs]; ring
    rw [this]
    unfold Dn
    push_cast
    exact mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
  have hDr : (Dn S1 S2 n : ℝ) ≤ 2 * (height (Wn S1 S2) (n + 1) : ℝ) := by exact_mod_cast hD
  -- the quadratic inequality
  have hq : b * ((n + 1 : ℕ) : ℝ) ^ 2 + Real.log 2 ≤ (n : ℝ) ^ 2 * c - s * ((n : ℝ) / 2) := by
    have hnb : (2 * b + s / 2 + b + Real.log 2 + 1) / (c - b) + 1 ≤ n := le_trans hn1b hnr
    have h1 : (2 * b + s / 2 + b + Real.log 2 + 1) ≤ (n - 1) * (c - b) := by
      have := (div_le_iff₀ hcb).1 (by linarith : (2 * b + s / 2 + b + Real.log 2 + 1) / (c - b) ≤ n - 1)
      exact this
    have hn1' : (1 : ℝ) ≤ n := le_trans hn1one hnr
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    push_cast
    nlinarith [mul_nonneg hcb.le (sub_nonneg.2 hn1'), mul_nonneg (sub_nonneg.2 hn1') hcb.le]
  refine ⟨n + 1, by omega, ?_⟩
  have h2 : Real.exp (b * ((n + 1 : ℕ) : ℝ) ^ 2) * 2 ≤ Real.exp ((n : ℝ) ^ 2 * c - s * ((n : ℝ) / 2)) := by
    have e2' : Real.exp (b * ((n + 1 : ℕ) : ℝ) ^ 2) * 2 =
        Real.exp (b * ((n + 1 : ℕ) : ℝ) ^ 2 + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    rw [e2']
    exact Real.exp_le_exp.2 hq
  have h3 : Real.exp (b * ((n + 1 : ℕ) : ℝ) ^ 2) * 2 ≤ 2 * (height (Wn S1 S2) (n + 1) : ℝ) := by
    linarith
  linarith

end Shifted

end ShiftedJump
end LeanCheck
