import LeanCheck.ChainNonInt
import LeanCheck.ChainDichotomy

/-!
# Capstone: the two explicit chains, finite-level statement of Theorem H

For the explicit chains `F₁ = {M_n}` and `F₂ = {1} ∪ {M_n + g_n}` built in `ChainG`, with ratios
`α¹_n = M_{n+1}/M_n` and `α²_n = M²_{n+1}/M²_n`:

* both ratio sequences are `≥ 2` and tend to infinity (so `case_dichotomy` applies);
* the profinite integer `ζ_G = ∑_s g_{a_s}` has compatible residue systems modulo both chains;
* `ζ_G` is **not** quarter-arc continuous for either chain (`case_dichotomy` + `zetaG_not_M_integer`);
* on the join ball (`M_n x` and `M²_n x` within `δ < 1/16` of integers) every finite partial sum of `ζ_G` at `x`
  is within `1/4` of an integer (`join_cont`).

The modelling assumptions are those of `case_dichotomy` (quarter-arc form of continuity, the formula for `ζ` on digit
strings, `Ẑ = lim ℤ/M_k`); the translation to genuine topological continuity and Theorem 24.3 are not formalized.
-/

namespace LeanCheck

/-- `z` is a compatible residue system for the chain with ratios `α`. -/
def Compat (α : ℕ → ℕ) (z : ℕ → ℤ) : Prop := ∀ k, (Mseq α k : ℤ) ∣ z (k + 1) - z k

/-- `z` represents `ζ_G`: `z_k` is the residue of `ζ_G` modulo `M_k`. -/
def Represents (α : ℕ → ℕ) (z : ℕ → ℤ) : Prop :=
  ∀ k, ∃ S0, ∀ S ≥ S0, (Mseq α k : ℤ) ∣ (Psum S : ℤ) - z k

lemma Mseq_of_chain {M : ℕ → ℕ} (h0 : M 0 = 1) (hdvd : ∀ n, M n ∣ M (n + 1)) :
    Mseq (fun n => M (n + 1) / M n) = M := by
  funext n
  induction n with
  | zero => simp [Mseq, h0]
  | succ n ih =>
    simp only [Mseq]
    rw [ih]
    exact Nat.div_mul_cancel (hdvd n)

lemma large_of_half {α : ℕ → ℕ} (h : ∀ n, n + 1 ≤ 2 * α n) :
    ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α i := by
  intro A
  refine ⟨⌈2 * A⌉₊, fun i hi => ?_⟩
  have h1 : 2 * A ≤ i := le_trans (Nat.le_ceil _) (by exact_mod_cast hi)
  have h2 : (i : ℝ) + 1 ≤ 2 * α i := by exact_mod_cast h i
  linarith

/-- The second chain: `1, M_0 + g_0, M_1 + g_1, …`. -/
def M2 (M : ℕ → ℕ) (n : ℕ) : ℕ := if n = 0 then 1 else M (n - 1) + gG (n - 1)

lemma M2_zero (M : ℕ → ℕ) : M2 M 0 = 1 := by simp [M2]

lemma M2_succ (M : ℕ → ℕ) (n : ℕ) : M2 M (n + 1) = M n + gG n := by simp [M2]

theorem capstone :
    ∃ α1 α2 : ℕ → ℕ,
      (∀ i, 2 ≤ α1 i) ∧ (∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α1 i) ∧
      (∀ i, 2 ≤ α2 i) ∧ (∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α2 i) ∧
      Mseq α1 0 = 1 ∧ Mseq α2 0 = 1 ∧ (∀ n, Mseq α2 (n + 1) = Mseq α1 n + gG n) ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α1 n) ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α2 n) ∧
      (∃ z, Compat α1 z ∧ Represents α1 z) ∧ (∃ z, Compat α2 z ∧ Represents α2 z) ∧
      (∀ z, Compat α1 z → Represents α1 z → ∀ δ : ℝ, 0 < δ → ¬ Cont α1 z δ) ∧
      (∀ z, Compat α2 z → Represents α2 z → ∀ δ : ℝ, 0 < δ → ¬ Cont α2 z δ) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 16 → ∀ x : ℝ,
        (∀ n, ∃ k : ℤ, |(Mseq α1 n : ℝ) * x - k| < δ) →
        (∀ n, ∃ k : ℤ, |(Mseq α2 n : ℝ) * x - k| < δ) →
        ∀ S, ∃ N : ℤ, |∑ s ∈ Finset.range S, (gG (aG s) : ℝ) * x - N| < 1 / 4) := by
  obtain ⟨M, h0, hpos, hdvd, hE, hR, hER, hnull⟩ := theoremH_data
  -- first chain
  have hM1 : Mseq (fun n => M (n + 1) / M n) = M := Mseq_of_chain h0 hdvd
  -- second chain
  have h20 : M2 M 0 = 1 := M2_zero M
  have h2pos : ∀ n, 0 < M2 M n := by
    intro n; cases n with
    | zero => simp [h20]
    | succ k => rw [M2_succ]; have := hpos k; omega
  have h2dvd : ∀ n, M2 M n ∣ M2 M (n + 1) := by
    intro n; cases n with
    | zero => rw [h20]; exact one_dvd _
    | succ k => rw [M2_succ, M2_succ]; exact hE k
  have hM2 : Mseq (fun n => M2 M (n + 1) / M2 M n) = M2 M := Mseq_of_chain h20 h2dvd
  -- ratio facts, first chain
  have hα1_mul : ∀ n, (M (n + 1) / M n) * M n = M (n + 1) := fun n => Nat.div_mul_cancel (hdvd n)
  have hα1_ge : ∀ n, n + 2 ≤ M (n + 1) / M n := fun n =>
    (Nat.le_div_iff_mul_le (hpos n)).mpr (hR n)
  -- ratio facts, second chain
  have hα2_mul : ∀ n, (M2 M (n + 1) / M2 M n) * M2 M n = M2 M (n + 1) :=
    fun n => Nat.div_mul_cancel (h2dvd n)
  have hα2_two : ∀ n, 2 ≤ M2 M (n + 1) / M2 M n := by
    intro n
    cases n with
    | zero => simp [M2_succ, h20, h0, gG_zero]
    | succ k =>
      by_contra hlt
      push_neg at hlt
      have hlt1 : M2 M (k + 1 + 1) / M2 M (k + 1) ≤ 1 := by omega
      have e := hα2_mul (k + 1)
      have hp := h2pos (k + 1)
      have hbig : M2 M (k + 1) < M2 M (k + 1 + 1) := by
        rw [M2_succ, M2_succ]
        have h1 := hR k
        have h2 := gG_mono (Nat.le_succ k)
        have h3 := hpos k
        nlinarith
      nlinarith
  have hα2_half : ∀ n, n + 1 ≤ 2 * (M2 M (n + 1) / M2 M n) := by
    intro n
    cases n with
    | zero => simp [M2_succ, h20, h0, gG_zero]
    | succ k =>
      have e := hα2_mul (k + 1)
      have hp := h2pos (k + 1)
      have h6 := hER k
      have : (k + 2) * (M2 M (k + 1)) ≤ 2 * (M2 M (k + 1 + 1)) := by
        rw [M2_succ, M2_succ]; exact h6
      by_contra hlt
      push_neg at hlt
      have hlt' : 2 * (M2 M (k + 1 + 1) / M2 M (k + 1)) + 1 ≤ k + 1 + 1 := by omega
      nlinarith
  refine ⟨fun n => M (n + 1) / M n, fun n => M2 M (n + 1) / M2 M n, ?_, ?_, hα2_two, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; beta_reduce; have := hα1_ge i; omega
  · exact large_of_half (fun n => by beta_reduce; have := hα1_ge n; omega)
  · exact large_of_half hα2_half
  · rw [hM1]; exact h0
  · rw [hM2]; exact h20
  · intro n; rw [hM2, hM1, M2_succ]
  · rw [hM1]
    intro N hN
    obtain ⟨n0, hn0⟩ := hnull N hN
    exact ⟨n0, fun n hn => (hn0 n hn).1⟩
  · rw [hM2]
    intro N hN
    obtain ⟨n0, hn0⟩ := hnull N hN
    refine ⟨n0 + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [M2_succ]
    exact (hn0 k (by omega)).2.1
  · obtain ⟨z, hz, hzP⟩ := zetaG_residues_exist M hpos hdvd
    exact ⟨z, by simpa [Compat, hM1] using hz, by simpa [Represents, hM1] using hzP⟩
  · obtain ⟨z, hz, hzP⟩ := zetaG_residues_exist (M2 M) h2pos h2dvd
    exact ⟨z, by simpa [Compat, hM2] using hz, by simpa [Represents, hM2] using hzP⟩
  · intro z hc hr δ hδ hC
    have hα : ∀ i, 2 ≤ M (i + 1) / M i := fun i => by beta_reduce; have := hα1_ge i; omega
    have hlarge : ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ (M (i + 1) / M i : ℕ) :=
      large_of_half (fun n => by beta_reduce; have := hα1_ge n; omega)
    obtain ⟨u, i1, hu⟩ := case_dichotomy hα hlarge hc hδ hC
    refine zetaG_not_M_integer (Mseq (fun n => M (n + 1) / M n)) ?_ z hr ⟨u, i1, hu⟩
    rw [hM1]
    intro N hN
    obtain ⟨n0, hn0⟩ := hnull N hN
    exact ⟨n0, fun n hn => (hn0 n hn).1⟩
  · intro z hc hr δ hδ hC
    have hlarge : ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ (M2 M (i + 1) / M2 M i : ℕ) :=
      large_of_half hα2_half
    obtain ⟨u, i1, hu⟩ := case_dichotomy hα2_two hlarge hc hδ hC
    refine zetaG_not_M_integer (Mseq (fun n => M2 M (n + 1) / M2 M n)) ?_ z hr ⟨u, i1, hu⟩
    rw [hM2]
    intro N hN
    obtain ⟨n0, hn0⟩ := hnull N hN
    refine ⟨n0 + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [M2_succ]
    exact (hn0 k (by omega)).2.1
  · intro δ hδ0 hδ x h1 h2
    rw [hM1] at h1
    rw [hM2] at h2
    refine join_cont (g := gG) (M := M) aG (fun s => s + 1) (fun s j hj => gG_run_aG s j hj)
      (fun s => le_refl _) hδ0 hδ x h1 (fun n => ?_)
    have := h2 (n + 1)
    rwa [M2_succ] at this

end LeanCheck
