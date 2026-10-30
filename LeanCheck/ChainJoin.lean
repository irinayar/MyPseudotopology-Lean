import LeanCheck.ChainG
import LeanCheck.ChainLemmas

/-!
# The join argument of Theorem H: the difference ball and the character `ζ_G`

For two families of observations `M_n` and `E_n = M_n + g_n`, if `M_n x` and `E_n x` are within `δ` of an integer
for all `n`, then (triangle inequality) `g_n x = E_n x - M_n x` is within `2δ` of an integer.  Along a run of
ratio-2 steps `g_{a+j+1} = 2 g_{a+j}` the contraction lemma then makes `g_a x` within `2δ / 2^L` of an integer, and
summing over runs of lengths `≥ s+1` shows that every finite partial sum of `ζ_G = ∑_s g_{a_s}` is within `1/4`
of an integer: the quarter-arc form of "`ζ_G` is continuous for the join".
-/

namespace LeanCheck

/-- Bottom of a ratio-2 run: if `g_n x` is within `δ'` of an integer for all `n`, then `g_a x` is within `δ'/2^L`. -/
lemma run_near {g : ℕ → ℕ} {a L : ℕ} (hrun : ∀ j < L, g (a + j + 1) = 2 * g (a + j))
    {δ' : ℝ} (hδ' : δ' * 3 < 1) (x : ℝ)
    (hg : ∀ n, ∃ k : ℤ, |(g n : ℝ) * x - k| < δ') :
    ∃ k : ℤ, |(g a : ℝ) * x - k| < δ' / 2 ^ L := by
  choose c hc using hg
  have hw : ∀ i ≤ L, |(g (a + i) : ℝ) * x - c (a + i)| < δ' := fun i _ => hc (a + i)
  have hint : ∀ i < L, ∃ n : ℤ,
      ((g (a + (i + 1)) : ℝ) * x - c (a + (i + 1))) - ((fun _ => 2 : ℕ → ℕ) i : ℝ)
        * ((g (a + i) : ℝ) * x - c (a + i)) = n := by
    intro i hi
    refine ⟨2 * c (a + i) - c (a + (i + 1)), ?_⟩
    have h := hrun i hi
    have h' : (g (a + (i + 1)) : ℝ) = 2 * g (a + i) := by exact_mod_cast h
    rw [h']
    push_cast
    ring
  have := run_bottom_small (δ := δ') (A := 2) (by nlinarith) (fun _ => 2) (fun _ => le_refl 2)
    (fun _ => by norm_num) (fun i => (g (a + i) : ℝ) * x - c (a + i)) L hw hint
  exact ⟨c (a + 0), by simpa using this⟩

/-- Every finite partial sum of `ζ_G` is within `1/4` of an integer on the join ball. -/
theorem join_cont {g M : ℕ → ℕ} (a L : ℕ → ℕ)
    (hrun : ∀ s j, j < L s → g (a s + j + 1) = 2 * g (a s + j))
    (hL : ∀ s, s + 1 ≤ L s) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 16) (x : ℝ)
    (h1 : ∀ n, ∃ k : ℤ, |(M n : ℝ) * x - k| < δ)
    (h2 : ∀ n, ∃ k : ℤ, |((M n + g n : ℕ) : ℝ) * x - k| < δ) :
    ∀ S, ∃ N : ℤ, |∑ s ∈ Finset.range S, (g (a s) : ℝ) * x - N| < 1 / 4 := by
  -- triangle inequality: `g_n x` is within `2δ` of an integer
  have hg : ∀ n, ∃ k : ℤ, |(g n : ℝ) * x - k| < 2 * δ := by
    intro n
    obtain ⟨k1, hk1⟩ := h1 n
    obtain ⟨k2, hk2⟩ := h2 n
    refine ⟨k2 - k1, ?_⟩
    have e : (g n : ℝ) * x - ((k2 - k1 : ℤ) : ℝ)
        = (((M n + g n : ℕ) : ℝ) * x - k2) - ((M n : ℝ) * x - k1) := by push_cast; ring
    rw [e]
    calc |(((M n + g n : ℕ) : ℝ) * x - k2) - ((M n : ℝ) * x - k1)|
        ≤ |((M n + g n : ℕ) : ℝ) * x - k2| + |(M n : ℝ) * x - k1| := abs_sub _ _
      _ < 2 * δ := by linarith
  -- bottoms of the runs
  have hs : ∀ s, ∃ k : ℤ, |(g (a s) : ℝ) * x - k| < 2 * δ / 2 ^ (s + 1) := by
    intro s
    obtain ⟨k, hk⟩ := run_near (hrun s) (by linarith) x hg
    refine ⟨k, lt_of_lt_of_le hk ?_⟩
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (hL s)
  choose kk hkk using hs
  intro S
  have key : ∀ S, ∃ N : ℤ,
      |∑ s ∈ Finset.range S, (g (a s) : ℝ) * x - N| ≤ 2 * δ * (1 - (1 / 2) ^ S) := by
    intro S
    induction S with
    | zero => exact ⟨0, by simp⟩
    | succ S ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + kk S, ?_⟩
      rw [Finset.sum_range_succ]
      have h := hkk S
      have e : ∑ s ∈ Finset.range S, (g (a s) : ℝ) * x + (g (a S) : ℝ) * x - ((N + kk S : ℤ) : ℝ)
          = (∑ s ∈ Finset.range S, (g (a s) : ℝ) * x - N) + ((g (a S) : ℝ) * x - kk S) := by
        push_cast; ring
      rw [e]
      have hpow : 2 * δ / 2 ^ (S + 1) = 2 * δ * ((1 / 2) ^ S - (1 / 2) ^ (S + 1)) := by
        simp only [one_div, inv_pow]; rw [pow_succ]; field_simp; ring
      calc |(∑ s ∈ Finset.range S, (g (a s) : ℝ) * x - N) + ((g (a S) : ℝ) * x - kk S)|
          ≤ |∑ s ∈ Finset.range S, (g (a s) : ℝ) * x - N| + |(g (a S) : ℝ) * x - kk S| :=
            abs_add_le _ _
        _ ≤ 2 * δ * (1 - (1 / 2) ^ S) + 2 * δ / 2 ^ (S + 1) := by linarith
        _ = 2 * δ * (1 - (1 / 2) ^ (S + 1)) := by rw [hpow]; ring
  obtain ⟨N, hN⟩ := key S
  refine ⟨N, lt_of_le_of_lt hN ?_⟩
  have : (0 : ℝ) < (1 / 2) ^ S := by positivity
  nlinarith [mul_pos hδ0 this]

/-- The core of Theorem H, all in one statement. -/
theorem counterexample_core :
    ∃ (M a : ℕ → ℕ), M 0 = 1 ∧ (∀ n, 0 < M n) ∧ (∀ n, M n ∣ M (n + 1)) ∧
      (∀ n, (M n + gG n) ∣ (M (n + 1) + gG (n + 1))) ∧ (∀ n, (n + 2) * M n ≤ M (n + 1)) ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n ∧ N ∣ M n + gG n ∧ N ∣ gG n) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 16 → ∀ x : ℝ,
        (∀ n, ∃ k : ℤ, |(M n : ℝ) * x - k| < δ) →
        (∀ n, ∃ k : ℤ, |((M n + gG n : ℕ) : ℝ) * x - k| < δ) →
        ∀ S, ∃ N : ℤ, |∑ s ∈ Finset.range S, (gG (a s) : ℝ) * x - N| < 1 / 4) := by
  obtain ⟨M, h0, hpos, hdvd, hE, hR, _, hnull⟩ := theoremH_data
  refine ⟨M, aG, h0, hpos, hdvd, hE, hR, hnull, ?_⟩
  intro δ hδ0 hδ x h1 h2
  exact join_cont (g := gG) (M := M) aG (fun s => s + 1) (fun s j hj => gG_run_aG s j hj)
    (fun s => le_refl _) hδ0 hδ x h1 h2

end LeanCheck
