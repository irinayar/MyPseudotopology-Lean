import LeanCheck.ChainJoin

/-!
# `ζ_G = ∑_s g_{a_s}` is not an integer of the profinite completion

`ζ_G` is the profinite integer whose residue modulo `N` is the (eventually constant) partial sum
`P_S = ∑_{s<S} g_{a_s}` (`N ∣ g_{a_s}` for large `s` by the profinite nullness of `G`).
We prove: no integer `u` satisfies `ζ_G ≡ u (mod N)` for all `N`.  The idea: modulo `g_{a_s}` and modulo
`2 g_{a_s}` the partial sum `P_s` and `P_{s+1} = P_s + g_{a_s}` are both `≡ u`, which forces
`(P_s - u)/g_{a_s}` to be odd; but `0 ≤ P_s ≤ g_{a_s}/2`, so `|u| ≥ g_{a_s}/2 ≥ 2^{s-1}`, impossible for large `s`.
-/

namespace LeanCheck

open Finset

/-- Partial sums of `ζ_G`. -/
def Psum (s : ℕ) : ℕ := ∑ t ∈ range s, gG (aG t)

lemma aG_strictMono : StrictMono aG := by
  intro s t h; unfold aG; nlinarith

lemma aG_ge (s : ℕ) : s ≤ aG s := by unfold aG; nlinarith

lemma gG_dvd_of_le {n m : ℕ} (h : n ≤ m) : gG n ∣ gG m := by
  induction m, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m _ ih => exact ih.trans (gG_dvd m)

lemma gG_mono {n m : ℕ} (h : n ≤ m) : gG n ≤ gG m :=
  Nat.le_of_dvd (gG_pos m) (gG_dvd_of_le h)

lemma gG_pow (s : ℕ) : ∀ j ≤ s + 1, gG (aG s + j) = 2 ^ j * gG (aG s) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h := gG_run_aG s j (by omega)
    have h' : gG (aG s + (j + 1)) = 2 * gG (aG s + j) := h
    rw [h', ih (by omega), pow_succ]
    ring

lemma q_double (s : ℕ) : 2 ^ (s + 1) * gG (aG s) ≤ gG (aG (s + 1)) := by
  have h1 := gG_pow s (s + 1) le_rfl
  have h2 : aG s + (s + 1) ≤ aG (s + 1) := by unfold aG; nlinarith
  calc 2 ^ (s + 1) * gG (aG s) = gG (aG s + (s + 1)) := h1.symm
    _ ≤ gG (aG (s + 1)) := gG_mono h2

lemma q_ge (s : ℕ) : 2 ^ s ≤ gG (aG s) := by
  induction s with
  | zero => have h := gG_pos (aG 0); norm_num; omega
  | succ s ih =>
    have h := q_double s
    have hp := gG_pos (aG s)
    calc 2 ^ (s + 1) = 2 ^ (s + 1) * 1 := by ring
      _ ≤ 2 ^ (s + 1) * gG (aG s) := Nat.mul_le_mul_left _ hp
      _ ≤ gG (aG (s + 1)) := h

lemma Psum_le : ∀ s, 1 ≤ s → 2 * Psum s ≤ gG (aG s) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    have := q_double 0
    simp only [Psum, Finset.sum_range_one]
    simpa [pow_one] using this
  | succ s hs ih =>
    have h := q_double s
    have h4 : 4 ≤ 2 ^ (s + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 4 * gG (aG s) ≤ 2 ^ (s + 1) * gG (aG s) := Nat.mul_le_mul_right _ h4
    have hP : Psum (s + 1) = Psum s + gG (aG s) := by simp [Psum, Finset.sum_range_succ]
    rw [hP]
    omega

lemma tail_dvd {d s S : ℕ} (hsS : s ≤ S) (h : ∀ t, s ≤ t → d ∣ gG (aG t)) :
    (d : ℤ) ∣ (Psum S : ℤ) - Psum s := by
  have e : Psum S = Psum s + ∑ t ∈ Ico s S, gG (aG t) := by
    unfold Psum; exact (Finset.sum_range_add_sum_Ico _ hsS).symm
  have e2 : (Psum S : ℤ) - Psum s = ((∑ t ∈ Ico s S, gG (aG t) : ℕ) : ℤ) := by
    rw [e]; push_cast; ring
  rw [e2]
  exact Int.natCast_dvd_natCast.mpr (Finset.dvd_sum (fun t ht => h t (Finset.mem_Ico.mp ht).1))

/-- `ζ_G` is not (the image of) an integer: no `u` with `ζ_G ≡ u` modulo every `N`. -/
theorem zetaG_not_integer :
    ¬ ∃ u : ℤ, ∀ N : ℕ, 0 < N → ∃ S0 : ℕ, ∀ S ≥ S0, (N : ℤ) ∣ (Psum S : ℤ) - u := by
  rintro ⟨u, hu⟩
  obtain ⟨s, hs⟩ : ∃ s, s = u.natAbs + 1 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by omega
  obtain ⟨S1, hS1⟩ := hu (gG (aG s)) (gG_pos _)
  obtain ⟨S2, hS2⟩ := hu (gG (aG s + 1)) (gG_pos _)
  obtain ⟨S, hS⟩ : ∃ S, S = max (max S1 S2) (s + 1) := ⟨_, rfl⟩
  have hSs : s + 1 ≤ S := by rw [hS]; exact le_max_right _ _
  have hSS1 : S1 ≤ S := by rw [hS]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hSS2 : S2 ≤ S := by rw [hS]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h2q : gG (aG s + 1) = 2 * gG (aG s) := by simpa using gG_run_aG s 0 (by omega)
  have hq := gG_pos (aG s)
  -- modulo `q = g_{a_s}`
  have d1 : (gG (aG s) : ℤ) ∣ (Psum s : ℤ) - u := by
    have a1 := hS1 S hSS1
    have a2 := tail_dvd (d := gG (aG s)) (s := s) (S := S) (by omega)
      (fun t ht => gG_dvd_of_le (aG_strictMono.monotone ht))
    have := dvd_sub a1 a2
    simpa using this
  -- modulo `2q = g_{a_s + 1}`
  have d2 : ((2 * gG (aG s) : ℕ) : ℤ) ∣ (Psum (s + 1) : ℤ) - u := by
    rw [← h2q]
    have a1 := hS2 S hSS2
    have a2 := tail_dvd (d := gG (aG s + 1)) (s := s + 1) (S := S) hSs (fun t ht => by
      apply gG_dvd_of_le
      have : aG (s + 1) ≤ aG t := aG_strictMono.monotone ht
      have : aG s < aG (s + 1) := aG_strictMono (by omega)
      omega)
    have := dvd_sub a1 a2
    simpa using this
  obtain ⟨c, hc⟩ := d1
  obtain ⟨e, he⟩ := d2
  have hP : (Psum (s + 1) : ℤ) = Psum s + gG (aG s) := by
    simp [Psum, Finset.sum_range_succ]
  have hqZ : (0 : ℤ) < gG (aG s) := by exact_mod_cast hq
  have hce : c + 1 = 2 * e := by
    have : (gG (aG s) : ℤ) * (c + 1) = (gG (aG s) : ℤ) * (2 * e) := by
      push_cast at he
      rw [hP] at he
      linarith
    exact mul_left_cancel₀ (ne_of_gt hqZ) this
  have hP2 : 2 * (Psum s : ℤ) ≤ gG (aG s) := by exact_mod_cast Psum_le s hs1
  have hP0 : (0 : ℤ) ≤ Psum s := Int.natCast_nonneg _
  have hpow : 2 * u.natAbs < 2 ^ s := by
    have := Nat.lt_two_pow_self (n := u.natAbs)
    rw [hs, pow_succ]
    omega
  have hqpow : (2 ^ s : ℤ) ≤ gG (aG s) := by exact_mod_cast q_ge s
  have hpowZ : (2 * u.natAbs : ℤ) < 2 ^ s := by exact_mod_cast hpow
  have hc0 : c ≤ -1 ∨ 1 ≤ c := by omega
  rcases hc0 with hc1 | hc1
  · have : (gG (aG s) : ℤ) * c ≤ -(gG (aG s) : ℤ) := by nlinarith
    omega
  · have : (gG (aG s) : ℤ) ≤ (gG (aG s) : ℤ) * c := by nlinarith
    omega

/-- Residues of `ζ_G` modulo a profinitely null divisibility chain `M` exist and are compatible. -/
theorem zetaG_residues_exist (M : ℕ → ℕ) (hMpos : ∀ n, 0 < M n) (hMdvd : ∀ n, M n ∣ M (n + 1)) :
    ∃ z : ℕ → ℤ, (∀ k, (M k : ℤ) ∣ z (k + 1) - z k) ∧
      ∀ k, ∃ S0, ∀ S ≥ S0, (M k : ℤ) ∣ (Psum S : ℤ) - z k := by
  classical
  have hex : ∀ k, ∃ T, ∀ t ≥ T, M k ∣ gG (aG t) := by
    intro k
    obtain ⟨n0, hn0⟩ := gG_null (hMpos k)
    exact ⟨n0, fun t ht => hn0 (aG t) (le_trans ht (aG_ge t))⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℕ, ∀ k, S k = Nat.find (hex k) := ⟨fun k => Nat.find (hex k), fun _ => rfl⟩
  have hSspec : ∀ k, ∀ t ≥ S k, M k ∣ gG (aG t) := fun k => by rw [hS]; exact Nat.find_spec (hex k)
  have hSmono : ∀ k, S k ≤ S (k + 1) := by
    intro k
    rw [hS k, hS (k + 1)]
    apply Nat.find_min'
    intro t ht
    have := Nat.find_spec (hex (k + 1))
    exact (hMdvd k).trans (this t ht)
  refine ⟨fun k => (Psum (S k) : ℤ), fun k => ?_, fun k => ⟨S k, fun T hT => ?_⟩⟩
  · exact tail_dvd (d := M k) (s := S k) (S := S (k + 1)) (hSmono k) (fun t ht => hSspec k t ht)
  · exact tail_dvd (d := M k) (s := S k) (S := T) hT (fun t ht => hSspec k t ht)

/-- Integrality in the sense of `case_dichotomy` is impossible for `ζ_G`. -/
theorem zetaG_not_M_integer (M : ℕ → ℕ) (hMnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (z : ℕ → ℤ) (hzP : ∀ k, ∃ S0, ∀ S ≥ S0, (M k : ℤ) ∣ (Psum S : ℤ) - z k) :
    ¬ ∃ (u : ℤ) (i1 : ℕ), ∀ i ≥ i1, (M (i + 1) : ℤ) ∣ z (i + 1) - u := by
  rintro ⟨u, i1, h⟩
  apply zetaG_not_integer
  refine ⟨u, fun N hN => ?_⟩
  obtain ⟨n0, hn0⟩ := hMnull N hN
  obtain ⟨S0, hS0⟩ := hzP (max i1 n0 + 1)
  refine ⟨S0, fun S hS => ?_⟩
  have h1 := hS0 S hS
  have h2 := h (max i1 n0) (le_max_left _ _)
  have h3 : (M (max i1 n0 + 1) : ℤ) ∣ (Psum S : ℤ) - u := by
    have := dvd_add h1 h2
    simpa using this
  have h4 : (N : ℤ) ∣ (M (max i1 n0 + 1) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hn0 _ (by omega))
  exact h4.trans h3

end LeanCheck
