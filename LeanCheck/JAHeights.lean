import Mathlib
import LeanCheck.JAFinal2

/-!
# Buffered heights and start levels

`exists_buffered`: for every `D ≥ 3` and every `M` there is a height `X ≥ M` and depths `n_a, n_b` such that, with the start
level `s = ⌈D⌉` for both primes, the scales `2^{(s+n_a)^2}` and `3^{(s+n_b)^2}` are the last scales below `D X` and are
buffered (`4 q ≤ X`):

`D X < 2^{(s+n_a+1)^2}`, `D X < 3^{(s+n_b+1)^2}`, `4·2^{(s+n_a)^2} ≤ X`, `4·3^{(s+n_b)^2} ≤ X`.

(This is the lemma "abundance of buffered heights", in the weak form 'arbitrarily large', which is all that is used.)
Construction: take `X_0 = 4·3^{j'^2}` for large `j'`, the left end of the allowed range for the prime `3`; let `j` be the
level of `2` with `4·2^{j^2} ≤ X_0 < 4·2^{(j+1)^2}` (so `j ≥ j'`).  If `D X_0 < 2^{(j+1)^2}` we are done, otherwise
`X = 2^e X_0` with `2^e ≥ 4D` lies at the left end of the next range for `2`.

`alpha_large`: with `s = ⌈D⌉`, `α_k I_1 = p^{2(s+k)+1}·16/(15D) > 2` for every `k` and `p ≥ 2`.

`CentralBound D C`: the remaining hypothesis (component 13): for all large buffered heights the central bound holds.
`heightBound2_of_central`, `JA_of_centralBound`: the assembly with only `CentralBound` and `CompactQuotientCriterion` left.
-/

namespace LeanCheck
namespace JAHeights

open Finset JAAssembly JAFinal2

/-- The common start level. -/
noncomputable def sD (D : ℝ) : ℕ := ⌈D⌉₊

/-- `X` is a buffered height with depths `na, nb` (start level `⌈D⌉`). -/
def Buffered (D : ℝ) (X na nb : ℕ) : Prop :=
  D * X < (2 : ℝ) ^ ((sD D + na + 1) ^ 2) ∧ D * X < (3 : ℝ) ^ ((sD D + nb + 1) ^ 2) ∧
  4 * 2 ^ ((sD D + na) ^ 2) ≤ X ∧ 4 * 3 ^ ((sD D + nb) ^ 2) ≤ X

lemma real_lt_pow (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : (n : ℝ) < (b : ℝ) ^ n := by
  exact_mod_cast Nat.lt_pow_self (by omega : 1 < b)

lemma exists_floor_sq (X₀ : ℕ) (h4 : 4 ≤ X₀) :
    ∃ j : ℕ, 4 * 2 ^ (j ^ 2) ≤ X₀ ∧ X₀ < 4 * 2 ^ ((j + 1) ^ 2) := by
  classical
  have hex : ∃ j : ℕ, X₀ < 4 * 2 ^ ((j + 1) ^ 2) := by
    refine ⟨X₀, ?_⟩
    have h1 : X₀ < 2 ^ X₀ := Nat.lt_pow_self (by norm_num)
    have h2 : 2 ^ X₀ ≤ 2 ^ ((X₀ + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using h4
  · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hi]
    exact not_lt.mp this

lemma alpha_large (p : ℕ) (hp : 2 ≤ p) (D : ℝ) (hD : 3 ≤ D) (k : ℕ) :
    2 < ((p ^ (2 * (sD D + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) := by
  have hD0 : 0 < D := by linarith
  have hs : D ≤ (sD D : ℝ) := Nat.le_ceil D
  have h1 : (2 * (sD D + k) + 1 : ℝ) < ((p ^ (2 * (sD D + k) + 1) : ℕ) : ℝ) := by
    have := real_lt_pow p hp (2 * (sD D + k) + 1)
    push_cast at this ⊢
    exact this
  have h2 : 2 * D < ((p ^ (2 * (sD D + k) + 1) : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
  nlinarith

/-- **Arbitrarily large buffered heights.** -/
theorem exists_buffered (D : ℝ) (hD : 3 ≤ D) (M : ℕ) :
    ∃ X : ℕ, M ≤ X ∧ ∃ na nb : ℕ, Buffered D X na nb := by
  have hD0 : 0 < D := by linarith
  set s := sD D with hsdef
  have hsD : D ≤ (s : ℝ) := Nat.le_ceil D
  -- the constant `E = 2^{d'}` with `E ≥ 4D`
  set d' : ℕ := ⌈4 * D⌉₊ with hd'
  set E : ℕ := 2 ^ d' with hEdef
  have hE4 : 4 * D ≤ (E : ℝ) := by
    have h1 : 4 * D ≤ (d' : ℝ) := Nat.le_ceil _
    have h2 := real_lt_pow 2 le_rfl d'
    have h3 : ((2 : ℕ) : ℝ) ^ d' = (E : ℝ) := by rw [hEdef]; push_cast; ring
    rw [h3] at h2
    linarith
  have hE1 : (1 : ℝ) ≤ E := by
    have : 1 ≤ E := Nat.one_le_two_pow
    exact_mod_cast this
  -- the large index `j'`
  set j' : ℕ := max (max M s) ⌈4 * D * E⌉₊ + 1 with hj'def
  have hjM : M ≤ j' := by omega
  have hjs : s ≤ j' := by omega
  have hjbig : 4 * D * E ≤ (j' : ℝ) := by
    have h1 : 4 * D * E ≤ (⌈4 * D * E⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈4 * D * E⌉₊ ≤ j' := by omega
    have h3 : (⌈4 * D * E⌉₊ : ℝ) ≤ j' := by exact_mod_cast h2
    linarith
  have hj1 : 1 ≤ j' := by omega
  -- `3^{2j'+1} > 4 D E`
  have h3big : 4 * D * E < (3 : ℝ) ^ (2 * j' + 1) := by
    have := real_lt_pow 3 (by norm_num) (2 * j' + 1)
    push_cast at this
    have : (j' : ℝ) < ((2 * j' + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h5 := real_lt_pow 3 (by norm_num) (2 * j' + 1)
    push_cast at h5 ⊢
    linarith
  set X₀ : ℕ := 4 * 3 ^ (j' ^ 2) with hX₀
  have hX₀4 : 4 ≤ X₀ := by
    have : 1 ≤ 3 ^ (j' ^ 2) := Nat.one_le_pow _ _ (by norm_num)
    omega
  obtain ⟨j, hj1', hj2'⟩ := exists_floor_sq X₀ hX₀4
  -- `j' ≤ j`
  have hjj : j' ≤ j := by
    by_contra hlt
    push Not at hlt
    have h1 : (j + 1) ^ 2 ≤ j' ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 2 ^ ((j + 1) ^ 2) ≤ 2 ^ (j' ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : 2 ^ (j' ^ 2) ≤ 3 ^ (j' ^ 2) := Nat.pow_le_pow_left (by norm_num) _
    omega
  -- the 3-side identity
  have h3sq : (3 : ℝ) ^ ((j' + 1) ^ 2) = (3 : ℝ) ^ (j' ^ 2) * (3 : ℝ) ^ (2 * j' + 1) := by
    rw [← pow_add]; congr 1; ring
  have hX₀r : (X₀ : ℝ) = 4 * (3 : ℝ) ^ (j' ^ 2) := by rw [hX₀]; push_cast; ring
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (j' ^ 2) := by positivity
  by_cases hA : D * (X₀ : ℝ) < (2 : ℝ) ^ ((j + 1) ^ 2)
  · -- case A: `X = X₀`
    refine ⟨X₀, ?_, j - s, j' - s, ?_⟩
    · have : j' ≤ 3 ^ (j' ^ 2) := by
        have h1 : j' < 3 ^ j' := Nat.lt_pow_self (by norm_num)
        have h2 : 3 ^ j' ≤ 3 ^ (j' ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        omega
      omega
    · have e1 : sD D + (j - s) = j := by omega
      have e2 : sD D + (j' - s) = j' := by omega
      unfold Buffered
      rw [e1, e2]
      refine ⟨hA, ?_, hj1', le_of_eq hX₀.symm⟩
      rw [h3sq, hX₀r]
      nlinarith [mul_pos h3pos hD0]
  · -- case B: `X = E · X₀`
    push Not at hA
    refine ⟨E * X₀, ?_, j + 1 - s, j' - s, ?_⟩
    · have : j' ≤ 3 ^ (j' ^ 2) := by
        have h1 : j' < 3 ^ j' := Nat.lt_pow_self (by norm_num)
        have h2 : 3 ^ j' ≤ 3 ^ (j' ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        omega
      have hE1' : 1 ≤ E := Nat.one_le_two_pow
      calc M ≤ j' := hjM
        _ ≤ 3 ^ (j' ^ 2) := this
        _ ≤ X₀ := by omega
        _ ≤ E * X₀ := Nat.le_mul_of_pos_left _ hE1'
    · have e1 : sD D + (j + 1 - s) = j + 1 := by omega
      have e2 : sD D + (j' - s) = j' := by omega
      unfold Buffered
      rw [e1, e2]
      have hX₀lt : (X₀ : ℝ) < 4 * (2 : ℝ) ^ ((j + 1) ^ 2) := by exact_mod_cast hj2'
      have h2sq : (2 : ℝ) ^ ((j + 1 + 1) ^ 2) = (2 : ℝ) ^ ((j + 1) ^ 2) * (2 : ℝ) ^ (2 * j + 3) := by
        rw [← pow_add]; congr 1; ring
      have h2big : 4 * D * E < (2 : ℝ) ^ (2 * j + 3) := by
        have h5 := real_lt_pow 2 le_rfl (2 * j + 3)
        push_cast at h5
        have : (j' : ℝ) ≤ j := by exact_mod_cast hjj
        have : (j : ℝ) ≥ 0 := Nat.cast_nonneg _
        linarith
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((j + 1) ^ 2) := by positivity
      have hEX : ((E * X₀ : ℕ) : ℝ) = (E : ℝ) * (X₀ : ℝ) := by push_cast; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hEX, h2sq]
        have hEpos : (0 : ℝ) < E := by linarith
        calc D * ((E : ℝ) * (X₀ : ℝ)) = (D * E) * (X₀ : ℝ) := by ring
          _ < (D * E) * (4 * (2 : ℝ) ^ ((j + 1) ^ 2)) :=
              mul_lt_mul_of_pos_left hX₀lt (by positivity)
          _ = (4 * D * E) * (2 : ℝ) ^ ((j + 1) ^ 2) := by ring
          _ ≤ (2 : ℝ) ^ (2 * j + 3) * (2 : ℝ) ^ ((j + 1) ^ 2) :=
              mul_le_mul_of_nonneg_right h2big.le h2pos.le
          _ = _ := by ring
      · rw [hEX, h3sq, hX₀r]
        have : D * ((E : ℝ) * (4 * (3 : ℝ) ^ (j' ^ 2))) = (4 * D * E) * (3 : ℝ) ^ (j' ^ 2) := by ring
        rw [this]
        nlinarith [mul_pos h3pos hD0]
      · -- `4 · 2^{(j+1)^2} ≤ E X₀`
        have hDX : (2 : ℝ) ^ ((j + 1) ^ 2) ≤ D * (X₀ : ℝ) := hA
        have : (4 : ℝ) * (2 : ℝ) ^ ((j + 1) ^ 2) ≤ (E : ℝ) * (X₀ : ℝ) := by
          have hX₀0 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hE4 hX₀0]
        exact_mod_cast this
      · have hE1' : 1 ≤ E := Nat.one_le_two_pow
        calc 4 * 3 ^ (j' ^ 2) = X₀ := hX₀.symm
          _ ≤ E * X₀ := Nat.le_mul_of_pos_left _ hE1'

/-! ### The remaining hypothesis and the final assembly -/

/-- **The remaining hypothesis (component 13)**: for all large buffered heights (start level `⌈D⌉`) the deterministic central
bound holds with a constant `C` independent of the height. -/
def CentralBound (D C : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X na nb : ℕ, X₀ ≤ X → Buffered D X na nb → CentralAt D C X (sD D) na (sD D) nb

theorem heightBound2_of_central (D C : ℝ) (hD : 3 ≤ D) (h : CentralBound D C) :
    ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ HeightBound2 D C X := by
  intro M
  obtain ⟨X₀, hX₀⟩ := h
  obtain ⟨X, hX, na, nb, hbuf⟩ := exists_buffered D hD (max M X₀)
  refine ⟨X, le_trans (le_max_left _ _) hX, sD D, na, sD D, nb, hbuf.1, hbuf.2.1, hbuf.2.2.1,
    hbuf.2.2.2, ?_, ?_, hX₀ X na nb (le_trans (le_max_right _ _) hX) hbuf⟩
  · intro k _
    exact alpha_large 2 le_rfl D hD k
  · intro k _
    exact alpha_large 3 (by norm_num) D hD k

/-- **JA from `CentralBound` and the compact-quotient criterion.** -/
theorem JA_of_centralBound (hQ : CompactQuotientCriterion)
    (h : ∀ ε : ℝ, 0 < ε → ∃ D C : ℝ, 3 ≤ D ∧ 2 / D ≤ ε ∧ 0 < C ∧ CentralBound D C) : JAProp := by
  refine JA_of_heightBounds2 hQ (fun ε hε => ?_)
  obtain ⟨D, C, hD, hDε, hC, hcb⟩ := h ε hε
  exact ⟨D, C, hD, hDε, hC, heightBound2_of_central D C hD hcb⟩

#print axioms exists_buffered
#print axioms alpha_large
#print axioms heightBound2_of_central
#print axioms JA_of_centralBound

end JAHeights
end LeanCheck
