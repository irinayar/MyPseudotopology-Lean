import Mathlib

/-!
# TVGplus: the independent-window model of the least witness (Remark on the model)

For a finite list `S` of primes and a radius `1/m`, an integer `k ≥ 1` has the model density
`ρ(k) = ∏_{p∈S} p^{-min(R_p,a_p)²} ∏_{n=a_p+1}^{R_p} (2⌈p^{n²}/m⌉-1)/p^{n²}` where
`a_p = a_p(1/m)` is the least `a` with `m < p^(2a+1)` and `R_p(k) = max{n : p^{n²} ≤ k m}`.
`Λ(N) = ∑_{k≤N} ρ(k)`; the predicted size of the least witness is the `N*` with `Λ(N*) = 1`.

The density is constant between the breakpoints `⌈p^{n²}/m⌉`; `lam_blocks` evaluates `Λ(N)` exactly as a
finite sum over blocks (after checking that no breakpoint lies strictly inside a block), which makes
`Λ(N)` computable for `N` with thousands of digits.  The instances are in `TVGPlusModelData.lean`.
-/

namespace LeanCheck
namespace TVGModel

/-- `a_p(1/m)`: the least `a` with `m < p^(2a+1)` (searched up to `m`). -/
def aM (p m : ℕ) : ℕ := ((List.range (m + 1)).find? (fun a => decide (m < p ^ (2 * a + 1)))).getD 0

/-- `R_p(k) = max{n : p^(n²) ≤ k m}`. -/
def Rm (p m k : ℕ) : ℕ := Nat.findGreatest (fun n => p ^ (n * n) ≤ k * m) (k * m)

/-- `w_n = 2⌈p^(n²)/m⌉ - 1`. -/
def wN (p m n : ℕ) : ℕ := 2 * ((p ^ (n * n) + m - 1) / m) - 1

/-- The product over `n = a+1, …, R`. -/
def prodIoc (p m a R : ℕ) : ℚ :=
  ((List.range (R - a)).map
    (fun j => (wN p m (a + 1 + j) : ℚ) / (p : ℚ) ^ ((a + 1 + j) * (a + 1 + j)))).prod

/-- The one-prime factor of the density, with `R` given. -/
def rhoR (p m R : ℕ) : ℚ :=
  (1 / (p : ℚ) ^ (min R (aM p m) * min R (aM p m))) * prodIoc p m (aM p m) R

/-- The density `ρ(k)`. -/
def rho (S : List ℕ) (m k : ℕ) : ℚ := (S.map (fun p => rhoR p m (Rm p m k))).prod

/-- `Λ(N) = ∑_{k ≤ N} ρ(k)`. -/
def Lam (S : List ℕ) (m N : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 N, rho S m k

/-- `R` computed by a search bounded by `B`. -/
def RmB (p m B k : ℕ) : ℕ := Nat.findGreatest (fun n => p ^ (n * n) ≤ k * m) B

def rhoB (S : List ℕ) (m B k : ℕ) : ℚ := (S.map (fun p => rhoR p m (RmB p m B k))).prod

/-- Sum over the blocks `[c, c')` of a boundary list. -/
def blockSum (S : List ℕ) (m B : ℕ) : List ℕ → ℚ
  | c :: c' :: rest => ((c' - c : ℕ) : ℚ) * rhoB S m B c + blockSum S m B (c' :: rest)
  | _ => 0

/-- The breakpoint `⌈p^(n²)/m⌉`. -/
def beta (p m n : ℕ) : ℕ := (p ^ (n * n) + m - 1) / m

/-- No breakpoint lies strictly inside a block, for `n ≤ B`. -/
def noBreak (S : List ℕ) (m B : ℕ) : List ℕ → Bool
  | c :: c' :: rest =>
      decide (c < c') && S.all (fun p => (List.range B).all (fun j =>
        decide (beta p m (j + 1) ≤ c ∨ c' ≤ beta p m (j + 1)))) && noBreak S m B (c' :: rest)
  | _ => true

/-- The bound condition: `p^((B+1)²) > N m` for all `p`. -/
def boundOK (S : List ℕ) (m B N : ℕ) : Bool :=
  S.all (fun p => decide (N * m < p ^ ((B + 1) * (B + 1))))

lemma beta_le_iff {p m n k : ℕ} (hm : 0 < m) : beta p m n ≤ k ↔ p ^ (n * n) ≤ k * m := by
  unfold beta
  rw [Nat.div_le_iff_le_mul_add_pred hm, mul_comm k m]
  omega

lemma le_pow_sq {p n : ℕ} (hp : 2 ≤ p) : n ≤ p ^ (n * n) := by
  have h1 : n < p ^ n := Nat.lt_pow_self (by omega)
  have h2 : p ^ n ≤ p ^ (n * n) := Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.zero_le n])
  omega

lemma Rm_ge_iff {p m k n : ℕ} (hp : 2 ≤ p) (hm : 0 < m) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    n ≤ Rm p m k ↔ p ^ (n * n) ≤ k * m := by
  have hkm : 1 ≤ k * m := Nat.mul_pos hk hm
  constructor
  · intro h
    have hspec : p ^ (Rm p m k * Rm p m k) ≤ k * m :=
      Nat.findGreatest_spec (P := fun n => p ^ (n * n) ≤ k * m) (m := 0) (Nat.zero_le _)
        (by simpa using hkm)
    exact le_trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul h h)) hspec
  · intro h
    exact Nat.le_findGreatest (le_trans (le_pow_sq hp) h) h

lemma Rm_const {p m c k : ℕ} (hp : 2 ≤ p) (hm : 0 < m) (hc : 1 ≤ c) (hck : c ≤ k)
    (hno : ∀ n, 1 ≤ n → ¬ (c < beta p m n ∧ beta p m n ≤ k)) : Rm p m k = Rm p m c := by
  apply le_antisymm
  · by_cases h0 : Rm p m k = 0
    · rw [h0]; exact Nat.zero_le _
    · have hn : 1 ≤ Rm p m k := Nat.pos_of_ne_zero h0
      have h1 := (Rm_ge_iff hp hm (le_trans hc hck) hn).1 le_rfl
      have h2 : beta p m (Rm p m k) ≤ k := (beta_le_iff hm).2 h1
      have h3 : beta p m (Rm p m k) ≤ c := by
        by_contra hcon
        exact hno _ hn ⟨by omega, h2⟩
      exact (Rm_ge_iff hp hm hc hn).2 ((beta_le_iff hm).1 h3)
  · by_cases h0 : Rm p m c = 0
    · rw [h0]; exact Nat.zero_le _
    · have hn : 1 ≤ Rm p m c := Nat.pos_of_ne_zero h0
      have h1 := (Rm_ge_iff hp hm hc hn).1 le_rfl
      exact (Rm_ge_iff hp hm (le_trans hc hck) hn).2 (le_trans h1 (Nat.mul_le_mul_right m hck))

lemma RmB_eq {p m B k : ℕ} (hp : 2 ≤ p) (hm : 0 < m) (hk : 1 ≤ k)
    (hB : k * m < p ^ ((B + 1) * (B + 1))) : RmB p m B k = Rm p m k := by
  have hkm : 1 ≤ k * m := Nat.mul_pos hk hm
  apply le_antisymm
  · by_cases h0 : RmB p m B k = 0
    · rw [h0]; exact Nat.zero_le _
    · have hn : 1 ≤ RmB p m B k := Nat.pos_of_ne_zero h0
      have hspec : p ^ (RmB p m B k * RmB p m B k) ≤ k * m :=
        Nat.findGreatest_spec (P := fun n => p ^ (n * n) ≤ k * m) (m := 0) (Nat.zero_le _)
          (by simpa using hkm)
      exact (Rm_ge_iff hp hm hk hn).2 hspec
  · by_cases h0 : Rm p m k = 0
    · rw [h0]; exact Nat.zero_le _
    · have hn : 1 ≤ Rm p m k := Nat.pos_of_ne_zero h0
      have h1 := (Rm_ge_iff hp hm hk hn).1 le_rfl
      have hnB : Rm p m k ≤ B := by
        by_contra hcon
        push_neg at hcon
        have : p ^ ((B + 1) * (B + 1)) ≤ p ^ (Rm p m k * Rm p m k) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hcon hcon)
        omega
      exact Nat.le_findGreatest hnB h1

lemma rho_block {S : List ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {m B c c' k : ℕ} (hm : 0 < m) (hc : 1 ≤ c)
    (hck : c ≤ k) (hkc : k < c')
    (hnb : (S.all fun p => (List.range B).all fun j =>
        decide (beta p m (j + 1) ≤ c ∨ c' ≤ beta p m (j + 1))) = true)
    (hbound : ∀ p ∈ S, (c' - 1) * m < p ^ ((B + 1) * (B + 1))) : rho S m k = rhoB S m B c := by
  unfold rho rhoB
  congr 1
  apply List.map_congr_left
  intro p hp
  have hp2 := hS p hp
  have hb := hbound p hp
  have e1 : RmB p m B c = Rm p m c :=
    RmB_eq hp2 hm hc (lt_of_le_of_lt (Nat.mul_le_mul_right m (by omega)) hb)
  have e2 : Rm p m k = Rm p m c := by
    apply Rm_const hp2 hm hc hck
    intro n hn ⟨h1, h2⟩
    by_cases hnB : n ≤ B
    · simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hnb
      have := (hnb p hp) (n - 1) (by omega)
      have e : n - 1 + 1 = n := by omega
      rw [e] at this
      omega
    · push_neg at hnB
      have h3 := (beta_le_iff hm).1 h2
      have h4 : p ^ ((B + 1) * (B + 1)) ≤ p ^ (n * n) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hnB hnB)
      have h5 : k * m ≤ (c' - 1) * m := Nat.mul_le_mul_right m (by omega)
      omega
  rw [e1, e2]

def endOf (c : ℕ) : List ℕ → ℕ
  | [] => c
  | c' :: rest => endOf c' rest

lemma endOf_ge {S : List ℕ} {m B : ℕ} :
    ∀ (cs : List ℕ) (c : ℕ), noBreak S m B (c :: cs) = true → c ≤ endOf c cs := by
  intro cs
  induction cs with
  | nil => intro c _; exact le_rfl
  | cons c' rest ih =>
    intro c h
    simp only [noBreak, Bool.and_eq_true, decide_eq_true_eq] at h
    exact le_trans h.1.1.le (ih c' h.2)

lemma blocks_sum {S : List ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {m B N : ℕ} (hm : 0 < m)
    (hb : boundOK S m B N = true) :
    ∀ (cs : List ℕ) (c : ℕ), 1 ≤ c → noBreak S m B (c :: cs) = true → endOf c cs ≤ N + 1 →
      ∑ k ∈ Finset.Ico c (endOf c cs), rho S m k = blockSum S m B (c :: cs) := by
  intro cs
  induction cs with
  | nil => intro c _ _ _; simp [endOf, blockSum]
  | cons c' rest ih =>
    intro c hc hnb hend
    have hnb' := hnb
    simp only [noBreak, Bool.and_eq_true, decide_eq_true_eq] at hnb'
    obtain ⟨⟨hcc, hchk⟩, hrest⟩ := hnb'
    have hge := endOf_ge rest c' hrest
    have hsplit := Finset.sum_Ico_consecutive (fun k => rho S m k) (le_of_lt hcc) hge
    have e : endOf c (c' :: rest) = endOf c' rest := rfl
    rw [e, ← hsplit, ih c' (by omega) hrest (by rw [e] at hend; exact hend)]
    simp only [blockSum]
    congr 1
    have hbound : ∀ p ∈ S, (c' - 1) * m < p ^ ((B + 1) * (B + 1)) := by
      intro p hp
      have h1 : N * m < p ^ ((B + 1) * (B + 1)) := by
        simp only [boundOK, List.all_eq_true, decide_eq_true_eq] at hb
        exact hb p hp
      have h2 : (c' - 1) * m ≤ N * m := Nat.mul_le_mul_right m (by rw [e] at hend; omega)
      omega
    have hconst : ∀ k ∈ Finset.Ico c c', rho S m k = rhoB S m B c := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact rho_block hS hm hc hk.1 hk.2 hchk hbound
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem lam_blocks {S : List ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {m B N : ℕ} (hm : 0 < m) (cs : List ℕ)
    (hend : endOf 1 cs = N + 1) (hnb : noBreak S m B (1 :: cs) = true)
    (hb : boundOK S m B N = true) :
    Lam S m N = blockSum S m B (1 :: cs) := by
  have := blocks_sum hS hm hb cs 1 le_rfl hnb (by omega)
  rw [hend] at this
  rw [← this]
  unfold Lam
  congr 1

#print axioms lam_blocks

end TVGModel
end LeanCheck
