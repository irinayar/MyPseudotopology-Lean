import Mathlib

/-!
# CRT solvability for the two-chain construction (Theorem H of `ChainSubsetTheorem_note.md`)

Given the difference chain `G = {g_n}` (`g_n ∣ g_{n+1}`, `g_n > 0`) and divisors `W_{n+1} ∣ g_{n+1}`
(the factorial parts `t!` of `g_{n+1}`), we construct `M_n` with

* `M_0 = 1`, `M_n ∣ M_{n+1}`,  `W_{n+1} ∣ M_{n+1}`,
* `E_n := M_n + g_n` satisfies `E_n ∣ E_{n+1}`,
* `R_n M_n ≤ M_{n+1}` (ratios tend to infinity) and `g_{n+1} ≤ M_{n+1}`.

The heart is the one-step system `M ∣ X, W ∣ X, (M + g) ∣ X + g'`, solvable because
`gcd (lcm M W) (M + g) ∣ g'`.
-/

namespace LeanCheck

/-- Solvability of `L ∣ X`, `E ∣ X + g` with `X` as large as we like, when `gcd L E ∣ g`. -/
lemma crt_solvable (L E g : ℤ) (hL : 0 < L) (hE : 0 < E) (h : (Int.gcd L E : ℤ) ∣ g) (B : ℤ) :
    ∃ X : ℤ, B ≤ X ∧ L ∣ X ∧ E ∣ X + g := by
  obtain ⟨g', hg'⟩ := h
  have hb := Int.gcd_eq_gcd_ab L E
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = Int.gcdA L E := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = Int.gcdB L E := ⟨_, rfl⟩
  rw [← hA, ← hC] at hb
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℤ, X0 = -(L * A * g') := ⟨_, rfl⟩
  have hX0E : X0 + g = E * (C * g') := by
    rw [hX0, hg']
    linear_combination g' * hb
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (B - X0).toNat := ⟨_, rfl⟩
  refine ⟨X0 + L * E * k, ?_, ?_, ?_⟩
  · have h1 : B - X0 ≤ k := by rw [hk]; exact Int.self_le_toNat _
    have h2 : (k : ℤ) ≤ L * E * k := by
      have : (1 : ℤ) ≤ L * E := by nlinarith
      have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
      nlinarith
    linarith
  · exact ⟨-(A * g') + E * k, by rw [hX0]; ring⟩
  · exact ⟨C * g' + L * k, by
      have : X0 + L * E * k + g = (X0 + g) + L * E * k := by ring
      rw [this, hX0E]; ring⟩

/-- `gcd (lcm a b) c` divides `lcm (gcd a c) (gcd b c)`. -/
lemma gcd_lcm_dvd (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd (Nat.lcm a b) c ∣ Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  have hg1 : Nat.gcd a c ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)).ne'
  have hg2 : Nat.gcd b c ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hb)).ne'
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hg3 : Nat.gcd (Nat.lcm a b) c ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hl)).ne'
  have hl2 : Nat.lcm (Nat.gcd a c) (Nat.gcd b c) ≠ 0 := Nat.lcm_ne_zero hg1 hg2
  rw [← Nat.factorization_le_iff_dvd hg3 hl2, Nat.factorization_gcd hl hc,
    Nat.factorization_lcm ha hb, Nat.factorization_lcm hg1 hg2, Nat.factorization_gcd ha hc,
    Nat.factorization_gcd hb hc]
  rw [Finsupp.le_def]
  intro p
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

/-- One step of the construction. -/
lemma crt_step (M g g' W B : ℕ) (hM : 0 < M) (hW : 0 < W) (hg : 0 < g) (hgg : g ∣ g')
    (hWg : W ∣ g') : ∃ M' : ℕ, B ≤ M' ∧ M ∣ M' ∧ W ∣ M' ∧ (M + g) ∣ (M' + g') := by
  have hE : 0 < M + g := by omega
  have hL : 0 < Nat.lcm M W := Nat.lcm_pos hM hW
  have hd : Nat.gcd (Nat.lcm M W) (M + g) ∣ g' := by
    have h1 := gcd_lcm_dvd M W (M + g) hM.ne' hW.ne' hE.ne'
    refine h1.trans (Nat.lcm_dvd ?_ ?_)
    · refine dvd_trans ?_ hgg
      have a1 := Nat.gcd_dvd_left M (M + g)
      have a2 := Nat.gcd_dvd_right M (M + g)
      exact (Nat.dvd_add_right a1).mp a2
    · exact (Nat.gcd_dvd_left W (M + g)).trans hWg
  have hdZ : (Int.gcd (Nat.lcm M W : ℤ) ((M + g : ℕ) : ℤ) : ℤ) ∣ (g' : ℤ) := by
    rw [Int.gcd_natCast_natCast]
    exact Int.natCast_dvd_natCast.mpr hd
  obtain ⟨X, hX1, hX2, hX3⟩ := crt_solvable (Nat.lcm M W : ℤ) ((M + g : ℕ) : ℤ) (g' : ℤ)
    (by exact_mod_cast hL) (by exact_mod_cast hE) hdZ (B : ℤ)
  have hX0 : 0 ≤ X := le_trans (Int.natCast_nonneg B) hX1
  obtain ⟨M', rfl⟩ : ∃ M' : ℕ, X = M' := ⟨X.toNat, (Int.toNat_of_nonneg hX0).symm⟩
  have h2 : Nat.lcm M W ∣ M' := Int.natCast_dvd_natCast.mp hX2
  have h3 : (M + g) ∣ (M' + g') := by exact_mod_cast hX3
  exact ⟨M', by exact_mod_cast hX1, (Nat.dvd_lcm_left M W).trans h2,
    (Nat.dvd_lcm_right M W).trans h2, h3⟩

/-- The whole construction: sequences `M_n` with the divisibilities and growth required in Theorem H. -/
theorem two_chains_exists (g W R : ℕ → ℕ) (hg0 : g 0 = 1) (hg : ∀ n, 0 < g n)
    (hgd : ∀ n, g n ∣ g (n + 1)) (hW0 : ∀ n, 0 < W n) (hWg : ∀ n, W (n + 1) ∣ g (n + 1)) :
    ∃ M : ℕ → ℕ, M 0 = 1 ∧ (∀ n, 0 < M n) ∧ (∀ n, M n ∣ M (n + 1)) ∧
      (∀ n, W (n + 1) ∣ M (n + 1)) ∧ (∀ n, (M n + g n) ∣ (M (n + 1) + g (n + 1))) ∧
      (∀ n, R n * M n ≤ M (n + 1)) ∧ (∀ n, g (n + 1) ≤ M (n + 1)) := by
  have step : ∀ (M gn gn' Wn Bn : ℕ), 0 < M → 0 < gn → ∃ M' : ℕ,
      (0 < Wn → gn ∣ gn' → Wn ∣ gn' → Bn ≤ M' ∧ M ∣ M' ∧ Wn ∣ M' ∧ (M + gn) ∣ (M' + gn')) := by
    intro M gn gn' Wn Bn hM hgn
    by_cases h : 0 < Wn ∧ gn ∣ gn' ∧ Wn ∣ gn'
    · obtain ⟨M', hM'⟩ := crt_step M gn gn' Wn Bn hM h.1 hgn h.2.1 h.2.2
      exact ⟨M', fun _ _ _ => hM'⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose! F hF using step
  let Mseq' : ℕ → ℕ := fun n => Nat.rec 1 (fun k Mk => F Mk (g k) (g (k + 1)) (W (k + 1))
    (max (R k * Mk) (g (k + 1) + 1)) ) n
  have hM0 : Mseq' 0 = 1 := rfl
  have hMs : ∀ k, Mseq' (k + 1) = F (Mseq' k) (g k) (g (k + 1)) (W (k + 1))
      (max (R k * Mseq' k) (g (k + 1) + 1)) := fun k => rfl
  have hpos : ∀ n, 0 < Mseq' n := by
    intro n
    induction n with
    | zero => simp [hM0]
    | succ k ih =>
      have := hF (Mseq' k) (g k) (g (k + 1)) (W (k + 1)) (max (R k * Mseq' k) (g (k + 1) + 1))
        ih (hg k) (hW0 _) (hgd k) (hWg k)
      rw [hMs]
      have h2 := this.1
      have h3 : g (k + 1) + 1 ≤ max (R k * Mseq' k) (g (k + 1) + 1) := le_max_right _ _
      omega
  have key : ∀ k, (max (R k * Mseq' k) (g (k + 1) + 1) ≤ Mseq' (k + 1)) ∧ Mseq' k ∣ Mseq' (k + 1)
      ∧ W (k + 1) ∣ Mseq' (k + 1) ∧ (Mseq' k + g k) ∣ (Mseq' (k + 1) + g (k + 1)) := by
    intro k
    rw [hMs]
    exact hF (Mseq' k) (g k) (g (k + 1)) (W (k + 1)) (max (R k * Mseq' k) (g (k + 1) + 1))
      (hpos k) (hg k) (hW0 _) (hgd k) (hWg k)
  refine ⟨Mseq', hM0, hpos, fun n => (key n).2.1, fun n => (key n).2.2.1,
    fun n => (key n).2.2.2, fun n => ?_, fun n => ?_⟩
  · exact le_trans (le_max_left _ _) (key n).1
  · have := le_trans (le_max_right _ _) (key n).1
    omega

end LeanCheck
