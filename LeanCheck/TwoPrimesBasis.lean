import Mathlib
import LeanCheck.TwoPrimesBasisData
import LeanCheck.TwoPrimesEffective
import LeanCheck.TwoPrimesWitnessLarge

/-!
# The 124-dimensional certificate: witnesses for all targets up to `2^10300`

`TwoPrimesBasisData` holds an integer matrix of size 124 together with the primes and digit numbers
of 124 digits.  Here the kernel checks that

* every row lies in the lattice `Σ d j * w j ≡ 0 (mod 3^6400)`, where `w j = ℓ^((m-1)^2)`;
* the matrix is invertible modulo 2, hence nonsingular;
* its column sums of absolute values are the listed numbers;
* the resulting digit bounds give the radius `7·10^-18` at every level.

`explicit`: for every integer `t` with `|t| ≤ 2^10300` there is `k` with `|k - t| < 2^10143`,
`P₃(k) < 7·10^-18` and `P₂(k - t) < 7·10^-18`; the difference `k - t` depends only on
`t mod 3^6400`.

Only `decide +kernel` is used for the finite checks, not `native_decide`.
-/

namespace TwoPrimesBasis

open Finset Matrix TwoPrimesBasisData TwoPrimesEffective

def B : Matrix (Fin 124) (Fin 124) ℤ := fun i j => (rows.getD i []).getD j 0

def base (j : Fin 124) : ℕ := bases.getD j 0

def dig (j : Fin 124) : ℕ := digits.getD j 0

/-- The weight `ℓ^((m-1)^2)` of the digit `j`. -/
def wN (j : Fin 124) : ℕ := base j ^ ((dig j - 1) ^ 2)

def u : ℕ := 3 ^ 6400

/-- The largest value `|d j|` may take. -/
def half (j : Fin 124) : ℕ := widths.getD j 0 / 2

/-! ## The finite checks -/

lemma rows_length : rows.length = 124 := by decide +kernel

lemma rows_all_length : rows.all (fun r => r.length == 124) = true := by decide +kernel

lemma check_congruence :
    rows.all (fun r => (List.zipWith (fun a (b : ℕ) => a * (b : ℤ)) r (List.ofFn wN)).sum
      % (u : ℤ) == 0) = true := by decide +kernel

lemma check_widths :
    rows.foldl (fun acc r => List.zipWith (fun a (x : ℤ) => a + x.natAbs) acc r)
      (List.replicate 124 0) = widths := by decide +kernel

/-- XOR of the rows of the inverse selected by the odd entries of `r`. -/
def xorRow (r : List ℤ) : ℕ :=
  (List.zipWith (fun (a : ℤ) (c : ℕ) => if a % 2 = 0 then 0 else c) r inv2).foldr (· ^^^ ·) 0

lemma inv2_length : inv2.length = 124 := by decide +kernel

lemma check_inverse :
    (List.range 124).all (fun i => xorRow (rows.getD i []) == 2 ^ i) = true := by decide +kernel

/-- `Σ w j * half j` over the digits of the prime `p` up to the digit number `m`. -/
def part (p m : ℕ) : ℕ :=
  ((List.finRange 124).map fun j => if base j = p ∧ dig j ≤ m then wN j * half j else 0).sum

lemma check_levels :
    (List.range 102).all (fun m => decide (part 2 m * 10 ^ 18 < 7 * 2 ^ (m ^ 2))
      && decide (part 3 m * 10 ^ 18 < 7 * 3 ^ (m ^ 2))) = true := by decide +kernel

lemma check_shape :
    (List.finRange 124).all (fun j => decide (dig j ≤ 101) && decide (1 ≤ dig j)
      && decide (base j = 2 ∨ base j = 3) && decide (base j = 3 → dig j ≤ 80)) = true := by
  decide +kernel

lemma check_first : base 0 = 2 ∧ dig 0 = 36 := by decide +kernel

lemma check_height : part 2 101 < 2 ^ 10143 := by decide +kernel

lemma check_high : (2 ^ 10300 + part 2 101) * 10 ^ 18 < 7 * 3 ^ 6561 := by decide +kernel

/-! ## Reading the checks -/

lemma shape (j : Fin 124) : dig j ≤ 101 ∧ 1 ≤ dig j ∧ (base j = 2 ∨ base j = 3)
    ∧ (base j = 3 → dig j ≤ 80) := by
  have h := List.all_eq_true.mp check_shape j (List.mem_finRange j)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma row_length (i : Fin 124) : (rows.getD i []).length = 124 := by
  have hi : (i : ℕ) < rows.length := by rw [rows_length]; exact i.isLt
  have e : rows.getD i [] = rows[(i : ℕ)] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [e]
  exact beq_iff_eq.mp (List.all_eq_true.mp rows_all_length _ (List.getElem_mem hi))

lemma row_mem (i : Fin 124) : rows.getD i [] ∈ rows := by
  have hi : (i : ℕ) < rows.length := by rw [rows_length]; exact i.isLt
  have e : rows.getD i [] = rows[(i : ℕ)] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [e]
  exact List.getElem_mem hi

lemma getD_get {α : Type*} (l : List α) (k : ℕ) (a : α) (h : k < l.length) : l.getD k a = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

lemma zipWith_eq_ofFn {α β γ : Type*} (f : α → β → γ) (r : List α) (s : List β) (a : α) (b : β)
    (n : ℕ) (hr : r.length = n) (hs : s.length = n) :
    List.zipWith f r s = List.ofFn (fun j : Fin n => f (r.getD j a) (s.getD j b)) := by
  have hlen : (List.zipWith f r s).length
      = (List.ofFn (fun j : Fin n => f (r.getD j a) (s.getD j b))).length := by
    rw [List.length_zipWith, List.length_ofFn, hr, hs, Nat.min_self]
  refine List.ext_getElem hlen (fun k h1 h2 => ?_)
  have hk : k < n := by rwa [List.length_ofFn] at h2
  have hk1 : k < r.length := by omega
  have hk2 : k < s.length := by omega
  rw [List.getElem_zipWith, List.getElem_ofFn]
  simp only [getD_get r k a hk1, getD_get s k b hk2]

lemma zipWith_sum_eq {α β : Type*} (f : α → β → ℤ) (r : List α) (s : List β) (a : α) (b : β)
    (n : ℕ) (hr : r.length = n) (hs : s.length = n) :
    (List.zipWith f r s).sum = ∑ j : Fin n, f (r.getD j a) (s.getD j b) := by
  rw [zipWith_eq_ofFn f r s a b n hr hs, List.sum_ofFn]

lemma eq_ofFn_getD {α : Type*} (l : List α) (a : α) (n : ℕ) (h : l.length = n) :
    l = List.ofFn (fun i : Fin n => l.getD i a) := by
  have hlen : l.length = (List.ofFn (fun i : Fin n => l.getD i a)).length := by
    rw [List.length_ofFn, h]
  refine List.ext_getElem hlen (fun k h1 h2 => ?_)
  rw [List.getElem_ofFn]
  exact (getD_get l k a h1).symm

lemma row_dvd (i : Fin 124) : (u : ℤ) ∣ ∑ j, B i j * (wN j : ℤ) := by
  have h := List.all_eq_true.mp check_congruence _ (row_mem i)
  rw [beq_iff_eq] at h
  have e := zipWith_sum_eq (fun a (b : ℕ) => a * (b : ℤ)) (rows.getD i []) (List.ofFn wN) 0 0
    124 (row_length i) (List.length_ofFn)
  rw [e] at h
  have e2 : ∀ j : Fin 124, (List.ofFn wN).getD j 0 = wN j := by
    intro j
    have hj : (j : ℕ) < (List.ofFn wN).length := by rw [List.length_ofFn]; exact j.isLt
    rw [getD_get _ _ _ hj, List.getElem_ofFn]
  simp only [e2] at h
  exact Int.dvd_of_emod_eq_zero h

lemma foldl_getD (n : ℕ) (l : List (List ℤ)) (acc : List ℕ) (hacc : acc.length = n)
    (hl : ∀ r ∈ l, r.length = n) (j : ℕ) (hj : j < n) :
    (l.foldl (fun acc r => List.zipWith (fun a (x : ℤ) => a + x.natAbs) acc r) acc).getD j 0
      = acc.getD j 0 + (l.map fun r => (r.getD j 0).natAbs).sum := by
  induction l generalizing acc with
  | nil => rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons r l ih =>
    have hr : r.length = n := hl r List.mem_cons_self
    have hlen : (List.zipWith (fun a (x : ℤ) => a + x.natAbs) acc r).length = n := by
      rw [List.length_zipWith, hacc, hr, Nat.min_self]
    rw [List.foldl_cons, ih _ hlen (fun s hs => hl s (List.mem_cons_of_mem _ hs)),
      List.map_cons, List.sum_cons]
    have e : (List.zipWith (fun a (x : ℤ) => a + x.natAbs) acc r).getD j 0
        = acc.getD j 0 + (r.getD j 0).natAbs := by
      have h1 : j < acc.length := by omega
      have h2 : j < r.length := by omega
      have h3 : j < (List.zipWith (fun a (x : ℤ) => a + x.natAbs) acc r).length := by omega
      rw [getD_get _ _ _ h3, getD_get _ _ _ h1, getD_get _ _ _ h2, List.getElem_zipWith]
    rw [e, add_assoc]

lemma column_sum (j : Fin 124) : ∑ i, |B i j| = (widths.getD j 0 : ℤ) := by
  have hl : ∀ r ∈ rows, r.length = 124 := by
    intro r hr
    exact beq_iff_eq.mp (List.all_eq_true.mp rows_all_length r hr)
  have h := foldl_getD 124 rows (List.replicate 124 0) List.length_replicate hl j j.isLt
  rw [check_widths] at h
  have h0 : (List.replicate 124 0).getD (j : ℕ) 0 = 0 := by
    have hj : (j : ℕ) < (List.replicate 124 0).length := by
      rw [List.length_replicate]; exact j.isLt
    rw [getD_get _ _ _ hj, List.getElem_replicate]
  rw [h0, zero_add] at h
  have e : (rows.map fun r => (r.getD j 0).natAbs).sum = ∑ i : Fin 124, (B i j).natAbs := by
    have e0 := eq_ofFn_getD rows [] 124 rows_length
    have e1 : (rows.map fun r => (r.getD j 0).natAbs)
        = (List.ofFn (fun i : Fin 124 => rows.getD i [])).map fun r => (r.getD j 0).natAbs :=
      congrArg (fun l => l.map fun r => (r.getD (j : ℕ) 0).natAbs) e0
    rw [e1, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [h, e, Nat.cast_sum]
  exact sum_congr rfl fun i _ => (Int.natCast_natAbs _).symm

lemma testBit_foldr_xor (l : List ℕ) (k : ℕ) :
    (((l.foldr (· ^^^ ·) 0).testBit k).toNat : ZMod 2)
      = (l.map fun x => ((x.testBit k).toNat : ZMod 2)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, Nat.testBit_xor, ← ih]
    generalize x.testBit k = a
    generalize (l.foldr (· ^^^ ·) 0).testBit k = b
    revert a b
    decide

lemma det_ne_zero : B.det ≠ 0 := by
  set f := Int.castRingHom (ZMod 2) with hf
  set C : Matrix (Fin 124) (Fin 124) (ZMod 2) :=
    fun j k => (((inv2.getD j 0).testBit k).toNat : ZMod 2) with hC
  have hmul : B.map f * C = 1 := by
    ext i k
    have h := List.all_eq_true.mp check_inverse (i : ℕ) (List.mem_range.mpr i.isLt)
    rw [beq_iff_eq] at h
    have h1 : (((xorRow (rows.getD i [])).testBit k).toNat : ZMod 2)
        = (1 : Matrix (Fin 124) (Fin 124) (ZMod 2)) i k := by
      rw [h, Nat.testBit_two_pow, Matrix.one_apply]
      by_cases hik : i = k
      · subst hik; simp
      · have : (i : ℕ) ≠ (k : ℕ) := fun e => hik (Fin.ext e)
        simp [hik, this]
    rw [← h1, xorRow, testBit_foldr_xor, Matrix.mul_apply]
    have e : ((List.zipWith (fun (a : ℤ) (c : ℕ) => if a % 2 = 0 then 0 else c)
          (rows.getD i []) inv2).map fun x => ((x.testBit k).toNat : ZMod 2))
        = List.ofFn (fun j : Fin 124 => B.map f i j * C j k) := by
      rw [zipWith_eq_ofFn (fun (a : ℤ) (c : ℕ) => if a % 2 = 0 then 0 else c) _ _ 0 0 124
        (row_length i) inv2_length, List.map_ofFn]
      refine congrArg List.ofFn (funext fun j => ?_)
      have hpar : ∀ a : ℤ, (a : ZMod 2) = if a % 2 = 0 then 0 else 1 := by
        intro a
        have : (a : ZMod 2) = ((a % 2 : ℤ) : ZMod 2) := (ZMod.intCast_mod a 2).symm
        rw [this]
        rcases Int.emod_two_eq_zero_or_one a with h | h <;> simp [h]
      have eB : B.map f i j = if ((rows.getD i []).getD j 0) % 2 = 0 then 0 else 1 := by
        rw [Matrix.map_apply, hf, eq_intCast]
        exact hpar _
      rw [Function.comp_apply, eB]
      simp only [hC]
      split
      · rw [Nat.zero_testBit, Bool.toNat_false, Nat.cast_zero, zero_mul]
      · rw [one_mul]
    rw [e, List.sum_ofFn]
  have hdet : (B.map f).det * C.det = 1 := by rw [← det_mul, hmul, det_one]
  intro h0
  have : (B.map f).det = f B.det := (f.map_det B).symm
  rw [this, h0, map_zero, zero_mul] at hdet
  exact zero_ne_one hdet

/-! ## The witnesses -/

/-- Rounding: every residue is a digit sum with `|d j| ≤ half j`. -/
lemma digits_exist (c : ℤ) : ∃ d : Fin 124 → ℤ,
    (u : ℤ) ∣ (∑ j, d j * (wN j : ℤ)) - c ∧ ∀ j, |d j| ≤ (half j : ℤ) := by
  have hco : IsCoprime ((wN 0 : ℕ) : ℤ) (u : ℤ) := by
    have h : Nat.Coprime (wN 0) u := by
      unfold wN u
      rw [check_first.1]
      exact Nat.Coprime.pow _ _ (by norm_num)
    exact Nat.Coprime.isCoprime h
  obtain ⟨a, b, hab⟩ := hco
  set z : Fin 124 → ℤ := Pi.single 0 (a * c) with hz
  have hzsum : (u : ℤ) ∣ (∑ j, z j * (wN j : ℤ)) - c := by
    have e : ∑ j, z j * (wN j : ℤ) = a * c * (wN 0 : ℤ) := by
      rw [sum_eq_single (0 : Fin 124)]
      · rw [hz, Pi.single_eq_same]
      · intro j _ hj
        rw [hz, Pi.single_eq_of_ne hj, zero_mul]
      · intro h
        exact absurd (mem_univ _) h
    rw [e]
    refine ⟨-(b * c), ?_⟩
    linear_combination c * hab
  obtain ⟨d, hd, hbound⟩ := TwoPrimesWitnessLarge.rounding B (fun j => (wN j : ℤ)) z u c
    row_dvd det_ne_zero hzsum
  refine ⟨d, hd, fun j => ?_⟩
  have h := hbound j
  rw [column_sum j] at h
  unfold half
  rw [Int.natCast_ediv]
  push_cast
  omega

/-- The part of the digit sum which belongs to the prime `p`. -/
def side (p : ℕ) (d : Fin 124 → ℤ) : ℤ := ∑ j, if base j = p then d j * (wN j : ℤ) else 0

lemma sides (d : Fin 124 → ℤ) : ∑ j, d j * (wN j : ℤ) = side 2 d + side 3 d := by
  unfold side
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rcases (shape j).2.2.1 with h | h <;> simp [h]

lemma part_eq (p m : ℕ) : (part p m : ℤ)
    = ∑ j : Fin 124, if base j = p ∧ dig j ≤ m then (wN j : ℤ) * (half j : ℤ) else 0 := by
  unfold part
  rw [← List.ofFn_eq_map, List.sum_ofFn, Nat.cast_sum]
  refine sum_congr rfl fun j _ => ?_
  split <;> simp

lemma part_stable (p m : ℕ) (hm : 101 ≤ m) : part p m = part p 101 := by
  unfold part
  congr 1
  refine List.map_congr_left fun j _ => ?_
  have h := (shape j).1
  have h1 : dig j ≤ m := le_trans h hm
  simp [h, h1]

/-- The digits up to the number `m` of the prime `p`. -/
def low (p m : ℕ) (d : Fin 124 → ℤ) : ℤ :=
  ∑ j, if base j = p ∧ dig j ≤ m then d j * (wN j : ℤ) else 0

lemma abs_low_le (p m : ℕ) (d : Fin 124 → ℤ) (hd : ∀ j, |d j| ≤ (half j : ℤ)) :
    |low p m d| ≤ (part p m : ℤ) := by
  rw [part_eq]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun j _ => ?_)
  split
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (wN j : ℤ)), mul_comm]
    exact mul_le_mul_of_nonneg_left (hd j) (by positivity)
  · simp

lemma side_split (p m : ℕ) (d : Fin 124 → ℤ) :
    ((p : ℤ) ^ (m ^ 2)) ∣ side p d - low p m d := by
  unfold side low
  rw [← sum_sub_distrib]
  refine dvd_sum fun j _ => ?_
  by_cases h : base j = p
  · by_cases hm : dig j ≤ m
    · simp [h, hm]
    · have h1 : m ^ 2 ≤ (dig j - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h2 : ((p : ℤ) ^ (m ^ 2)) ∣ (wN j : ℤ) := by
        unfold wN
        rw [h, Nat.cast_pow]
        exact pow_dvd_pow _ h1
      simp only [h, hm, and_false, ite_false, sub_zero, ite_true]
      exact h2.mul_left _
  · simp [h]

lemma abs_side_le (p : ℕ) (d : Fin 124 → ℤ) (hd : ∀ j, |d j| ≤ (half j : ℤ)) :
    |side p d| ≤ (part p 101 : ℤ) := by
  have e : side p d = low p 101 d := by
    unfold side low
    refine sum_congr rfl fun j _ => ?_
    simp [(shape j).1]
  rw [e]
  exact abs_low_le p 101 d hd

/-- A number which differs from `y` by a multiple of the modulus is within `|y| / M` of an
integer. -/
lemma dist_le (x y : ℤ) (M : ℕ) (hM : 0 < M) (h : (M : ℤ) ∣ x - y) :
    |(x : ℝ) / M - round ((x : ℝ) / M)| ≤ |(y : ℝ)| / M := by
  obtain ⟨q, hq⟩ := h
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have e : (x : ℝ) / M = (y : ℝ) / M + (q : ℝ) := by
    have h1 : x = y + (M : ℤ) * q := by omega
    rw [h1]
    push_cast
    field_simp
  refine le_trans (round_le _ q) (le_of_eq ?_)
  rw [e, add_sub_cancel_right, abs_div, abs_of_pos hMr]

lemma level_bound (p m : ℕ) (hp : p = 2 ∨ p = 3) :
    (part p m : ℝ) / ((p ^ (m ^ 2) : ℕ) : ℝ) < 7 / 10 ^ 18 := by
  have hpos : 0 < p := by omega
  have key : part p m * 10 ^ 18 < 7 * p ^ (m ^ 2) := by
    have base' : ∀ n < 102, part p n * 10 ^ 18 < 7 * p ^ (n ^ 2) := by
      intro n hn
      have h := List.all_eq_true.mp check_levels n (List.mem_range.mpr hn)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases hp with rfl | rfl
      exacts [h.1, h.2]
    by_cases hm : m < 102
    · exact base' m hm
    · rw [part_stable p m (by omega)]
      refine lt_of_lt_of_le (base' 101 (by norm_num)) (Nat.mul_le_mul_left _ ?_)
      exact Nat.pow_le_pow_right hpos (Nat.pow_le_pow_left (by omega) 2)
  have hM : (0 : ℝ) < ((p ^ (m ^ 2) : ℕ) : ℝ) := by
    have : 0 < p ^ (m ^ 2) := pow_pos hpos _
    exact_mod_cast this
  rw [div_lt_div_iff₀ hM (by positivity)]
  have h : (part p m : ℝ) * 10 ^ 18 < 7 * ((p ^ (m ^ 2) : ℕ) : ℝ) := by exact_mod_cast key
  exact h

/-- A number congruent to `side p d` modulo `p^(m^2)` is small at the level `m`. -/
lemma level_small (p m : ℕ) (hp : p = 2 ∨ p = 3) (x : ℤ) (d : Fin 124 → ℤ)
    (hd : ∀ j, |d j| ≤ (half j : ℤ)) (s : ℤ) (hs : s = side p d ∨ s = -side p d)
    (hx : ((p : ℤ) ^ (m ^ 2)) ∣ x - s) :
    |(x : ℝ) / (p : ℝ) ^ (m ^ 2) - round ((x : ℝ) / (p : ℝ) ^ (m ^ 2))| < 7 / 10 ^ 18 := by
  have hpos : 0 < p ^ (m ^ 2) := pow_pos (by omega) _
  obtain ⟨y, hy, hxy⟩ : ∃ y : ℤ, |y| ≤ (part p m : ℤ) ∧ ((p : ℤ) ^ (m ^ 2)) ∣ x - y := by
    rcases hs with h | h
    · refine ⟨low p m d, abs_low_le p m d hd, ?_⟩
      have := dvd_add hx (side_split p m d)
      rw [h] at this
      simpa using this
    · refine ⟨-low p m d, by rw [abs_neg]; exact abs_low_le p m d hd, ?_⟩
      have := dvd_sub hx (side_split p m d)
      rw [h] at this
      have e : x - -side p d - (side p d - low p m d) = x - -low p m d := by ring
      rwa [e] at this
  have h1 := dist_le x y (p ^ (m ^ 2)) hpos (by rw [Nat.cast_pow]; exact hxy)
  have e : ((p ^ (m ^ 2) : ℕ) : ℝ) = (p : ℝ) ^ (m ^ 2) := Nat.cast_pow _ _
  rw [e] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : |(y : ℝ)| ≤ (part p m : ℝ) := by exact_mod_cast hy
  refine lt_of_le_of_lt (div_le_div_of_nonneg_right h2 (by positivity)) ?_
  rw [← e]
  exact level_bound p m hp

/-- **Witnesses for every target up to `2^10300`**, with a correction which depends only on the
target modulo `3^6400`. -/
theorem explicit : ∃ z : ℤ → ℤ, (∀ t, z t = z (t % (u : ℤ))) ∧
    ∀ t : ℤ, |t| ≤ 2 ^ 10300 → |z t| < 2 ^ 10143 ∧
      Small 3 (7 / 10 ^ 18) (t + z t) ∧ Small 2 (7 / 10 ^ 18) (z t) := by
  choose d hd hbound using digits_exist
  refine ⟨fun t => -side 2 (d (t % (u : ℤ))), fun t => by simp only [Int.emod_emod], ?_⟩
  intro t ht
  set c : ℤ := t % (u : ℤ) with hc
  have hzabs : |(-side 2 (d c))| ≤ (part 2 101 : ℤ) := by
    rw [abs_neg]
    exact abs_side_le 2 (d c) (hbound c)
  have hheight : (part 2 101 : ℤ) < 2 ^ 10143 := by exact_mod_cast check_height
  have hcong : (u : ℤ) ∣ (t + -side 2 (d c)) - side 3 (d c) := by
    have h1 := hd c
    rw [sides] at h1
    have h2 : (u : ℤ) ∣ t - c := by
      rw [hc]
      exact Int.dvd_self_sub_emod
    have h3 := dvd_sub h2 h1
    have e : t - c - (side 2 (d c) + side 3 (d c) - c)
        = (t + -side 2 (d c)) - side 3 (d c) := by ring
    rwa [e] at h3
  refine ⟨lt_of_le_of_lt hzabs hheight, ?_, ?_⟩
  · intro m
    by_cases hm : m ≤ 80
    · refine level_small 3 m (Or.inr rfl) _ (d c) (hbound c) _ (Or.inl rfl) ?_
      refine dvd_trans ?_ hcong
      have h1 : m ^ 2 ≤ 6400 := le_trans (Nat.pow_le_pow_left hm 2) (by norm_num)
      have e : (u : ℤ) = (3 : ℤ) ^ 6400 := by
        unfold u
        rw [Nat.cast_pow, Nat.cast_ofNat]
      rw [e, Nat.cast_ofNat]
      exact pow_dvd_pow 3 h1
    · have hpos : (0 : ℝ) < (3 : ℝ) ^ (m ^ 2) := by positivity
      have h1 := dist_le (t + -side 2 (d c)) (t + -side 2 (d c)) (3 ^ (m ^ 2))
        (pow_pos (by norm_num) _) (by simp)
      rw [Nat.cast_pow, Nat.cast_ofNat] at h1
      rw [Nat.cast_ofNat]
      refine lt_of_le_of_lt h1 ?_
      have h2 : |t + -side 2 (d c)| ≤ ((2 ^ 10300 + part 2 101 : ℕ) : ℤ) := by
        refine le_trans (abs_add_le _ _) ?_
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        exact add_le_add ht hzabs
      have h3 : (2 ^ 10300 + part 2 101) * 10 ^ 18 < 7 * 3 ^ (m ^ 2) := by
        refine lt_of_lt_of_le check_high (Nat.mul_le_mul_left _ ?_)
        refine Nat.pow_le_pow_right (by norm_num) ?_
        exact le_trans (by norm_num : 6561 ≤ 81 ^ 2) (Nat.pow_le_pow_left (by omega) 2)
      have h4 : |((t + -side 2 (d c) : ℤ) : ℝ)| ≤ ((2 ^ 10300 + part 2 101 : ℕ) : ℝ) := by
        exact_mod_cast h2
      refine lt_of_le_of_lt (div_le_div_of_nonneg_right h4 hpos.le) ?_
      rw [div_lt_div_iff₀ hpos (by positivity)]
      have h5 : ((2 ^ 10300 + part 2 101 : ℕ) : ℝ) * (10 : ℝ) ^ 18 < 7 * (3 : ℝ) ^ (m ^ 2) := by
        exact_mod_cast h3
      exact h5
  · intro m
    refine level_small 2 m (Or.inl rfl) _ (d c) (hbound c) _ (Or.inr rfl) ?_
    rw [sub_self]
    exact dvd_zero _

/-- The statement with `k` and `k - t`. -/
theorem explicit_witness (t : ℤ) (ht : |t| ≤ 2 ^ 10300) :
    ∃ k : ℤ, |k - t| < 2 ^ 10143 ∧ Small 3 (7 / 10 ^ 18) k ∧ Small 2 (7 / 10 ^ 18) (k - t) := by
  obtain ⟨z, _, h⟩ := explicit
  obtain ⟨h1, h2, h3⟩ := h t ht
  refine ⟨t + z t, ?_, h2, ?_⟩
  · rwa [add_sub_cancel_left]
  · rwa [add_sub_cancel_left]

end TwoPrimesBasis
