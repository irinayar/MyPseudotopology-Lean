import LeanCheck.ChainCRT

/-!
# A concrete difference chain `G` and the full data of Theorem H

`G` has ratios `r_k = s + 1` when `k = s²` (`s ≥ 1`) and `r_k = 2` otherwise, so
`g_n = ∏_{k<n} r_k`.  Between `s²` and `(s+1)²` there are `2s` consecutive ratio-2 steps
(arbitrarily long bounded-ratio runs), and `(S+1)! ∣ g_n` for `n > S²` (profinitely null).
Combined with `two_chains_exists` this gives the two chains `F₁ = {M_n}`, `F₂ = {1} ∪ {M_n + g_n}`.
-/

namespace LeanCheck

/-- Ratio sequence of the difference chain. -/
def rG (k : ℕ) : ℕ :=
  if 1 ≤ Nat.sqrt k ∧ Nat.sqrt k * Nat.sqrt k = k then Nat.sqrt k + 1 else 2

/-- The difference chain `g_n = ∏_{k<n} r_k`. -/
def gG (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, rG k

lemma rG_ge (k : ℕ) : 2 ≤ rG k := by
  unfold rG
  split_ifs with h
  · omega
  · exact le_refl _

lemma gG_zero : gG 0 = 1 := by simp [gG]

lemma gG_succ (n : ℕ) : gG (n + 1) = gG n * rG n := by
  simp [gG, Finset.prod_range_succ]

lemma gG_pos (n : ℕ) : 0 < gG n := by
  induction n with
  | zero => simp [gG_zero]
  | succ n ih => rw [gG_succ]; exact Nat.mul_pos ih (lt_of_lt_of_le (by norm_num) (rG_ge n))

lemma gG_dvd (n : ℕ) : gG n ∣ gG (n + 1) := by
  rw [gG_succ]; exact Dvd.intro _ rfl

lemma rG_square (s : ℕ) : rG ((s + 1) * (s + 1)) = s + 2 := by
  unfold rG
  have h : Nat.sqrt ((s + 1) * (s + 1)) = s + 1 := Nat.sqrt_eq (s + 1)
  rw [h]
  simp

lemma rG_two {s k : ℕ} (h1 : s * s < k) (h2 : k < (s + 1) * (s + 1)) : rG k = 2 := by
  unfold rG
  have hs : Nat.sqrt k = s := by
    apply le_antisymm
    · have := (Nat.sqrt_lt (m := k) (n := s + 1)).mpr h2
      omega
    · exact Nat.le_sqrt.mpr (le_of_lt h1)
  rw [hs]
  have : s * s ≠ k := ne_of_lt h1
  simp [this]

/-- Arbitrarily long runs of ratio-2 steps. -/
lemma gG_runs (L : ℕ) : ∃ n, ∀ j < L, gG (n + j + 1) = 2 * gG (n + j) := by
  refine ⟨L * L + 1, fun j hj => ?_⟩
  rw [gG_succ, mul_comm, rG_two (s := L)]
  · omega
  · nlinarith

/-- The explicit run bottoms `a_s = (s+1)² + 1`; the run starting at `a_s` has `s+1` ratio-2 steps. -/
def aG (s : ℕ) : ℕ := (s + 1) * (s + 1) + 1

lemma gG_run_aG (s j : ℕ) (hj : j < s + 1) : gG (aG s + j + 1) = 2 * gG (aG s + j) := by
  unfold aG
  rw [gG_succ, mul_comm, rG_two (s := s + 1)]
  · omega
  · nlinarith

lemma factorial_eq_prod (S : ℕ) : (S + 1).factorial = ∏ s ∈ Finset.range S, (s + 2) := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ (S + 1)]
    ring

/-- `(S+1)! ∣ g_n` once `n > S²`. -/
lemma factorial_dvd_gG {S n : ℕ} (h : S * S < n) : (S + 1).factorial ∣ gG n := by
  rw [factorial_eq_prod]
  have hinj : Set.InjOn (fun s : ℕ => (s + 1) * (s + 1)) (Finset.range S : Set ℕ) := by
    intro a _ b _ hab
    have : (a + 1) * (a + 1) = (b + 1) * (b + 1) := hab
    have := Nat.mul_self_inj.mp this
    omega
  have himg : ∏ s ∈ Finset.range S, (s + 2) =
      ∏ k ∈ (Finset.range S).image (fun s : ℕ => (s + 1) * (s + 1)), rG k := by
    rw [Finset.prod_image hinj]
    apply Finset.prod_congr rfl
    intro s _
    rw [rG_square]
  rw [himg]
  unfold gG
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
  have hs' : s < S := Finset.mem_range.mp hs
  rw [Finset.mem_range]
  nlinarith

/-- Profinite nullness of `G`: every positive integer divides `g_n` for large `n`. -/
lemma gG_null {N : ℕ} (hN : 0 < N) : ∃ n0, ∀ n ≥ n0, N ∣ gG n := by
  refine ⟨N * N + 1, fun n hn => ?_⟩
  exact (Nat.dvd_factorial hN (Nat.le_succ N)).trans (factorial_dvd_gG (by omega))

/-- The factorial parts `W_n = (⌊√(n-1)⌋)!` dividing `g_n`. -/
def WG (n : ℕ) : ℕ := (Nat.sqrt (n - 1)).factorial

lemma WG_pos (n : ℕ) : 0 < WG n := Nat.factorial_pos _

lemma WG_dvd (n : ℕ) : WG (n + 1) ∣ gG (n + 1) := by
  unfold WG
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨S, hS⟩ : ∃ S, Nat.sqrt n = S + 1 := ⟨Nat.sqrt n - 1, by omega⟩
    rw [hS]
    apply factorial_dvd_gG
    have := Nat.sqrt_le n
    rw [hS] at this
    nlinarith

lemma WG_null {N : ℕ} (hN : 0 < N) : ∃ n0, ∀ n ≥ n0, N ∣ WG n := by
  refine ⟨N * N + 1, fun n hn => ?_⟩
  unfold WG
  have hle : N ≤ Nat.sqrt (n - 1) := Nat.le_sqrt.mpr (by omega)
  exact (Nat.dvd_factorial hN le_rfl).trans (Nat.factorial_dvd_factorial hle)

/-- The full data of Theorem H for this `G`. -/
theorem theoremH_data :
    ∃ M : ℕ → ℕ, M 0 = 1 ∧ (∀ n, 0 < M n) ∧ (∀ n, M n ∣ M (n + 1)) ∧
      (∀ n, (M n + gG n) ∣ (M (n + 1) + gG (n + 1))) ∧
      (∀ n, (n + 2) * M n ≤ M (n + 1)) ∧
      (∀ n, (n + 2) * (M n + gG n) ≤ 2 * (M (n + 1) + gG (n + 1))) ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n ∧ N ∣ M n + gG n ∧ N ∣ gG n) := by
  obtain ⟨M, h0, hpos, hdvd, hW, hE, hR, hgle⟩ :=
    two_chains_exists gG WG (fun n => n + 2) gG_zero gG_pos gG_dvd WG_pos WG_dvd
  refine ⟨M, h0, hpos, hdvd, hE, hR, ?_, ?_⟩
  · intro n
    have hg : gG n ≤ M n := by
      cases n with
      | zero => simp [gG_zero, h0]
      | succ k => exact hgle k
    have h1 := hR n
    have h2 : (n + 2) * (M n + gG n) ≤ 2 * ((n + 2) * M n) := by nlinarith
    have h3 : M (n + 1) ≤ M (n + 1) + gG (n + 1) := Nat.le_add_right _ _
    omega
  · intro N hN
    obtain ⟨n1, h1⟩ := gG_null hN
    obtain ⟨n2, h2⟩ := WG_null hN
    refine ⟨max (max n1 n2) 1 + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hkn1 : k + 1 ≥ n1 := by omega
    have hkn2 : k + 1 ≥ n2 := by omega
    have hNM : N ∣ M (k + 1) := (h2 (k + 1) hkn2).trans (hW k)
    have hNg : N ∣ gG (k + 1) := h1 (k + 1) hkn1
    exact ⟨hNM, dvd_add hNM hNg, hNg⟩

end LeanCheck
