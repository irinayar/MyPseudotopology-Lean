import Mathlib
import LeanCheck.PGXi

/-!
# PG: the digit sets `D_{p,k}` and the digit ideal `I_p` (Lean check)

Scope. Section 5 of `PG_v1`/`PG_v2`/`PG_v3`. For a base `p`, a *term* is a pair `(b, z)` standing for `+p^z` (`b = true`)
or `-p^z` (`b = false`); `val p l` is the sum of a list of terms and
`D p k = {val p l : l.length ≤ k}` is the set `D_{p,k}` of integers that are sums of at most `k` signed powers of `p`.

* `zero_mem_D`, `D_mono`, `D_neg`, `D_add` : `0 ∈ D_{p,k}`, monotone in `k`, symmetric, `D_{p,k} + D_{p,l} ⊆ D_{p,k+l}`;
* `Ip p` : the family of subsets of `ℤ` contained in some `D_{p,k}`; `Ip_sub`, `Ip_union`, `Ip_single`, `Ip_add`, `Ip_neg`
  are (I1), (I2), (I4), (I5). Properness (I3) rests on the counting Lemma 5.1 of the article, which is NOT formalized:
  `Ip_admissible` assumes it as the hypothesis `hproper`;
* `Ip_pow` : Proposition 5.3, `I_{p^r} = I_p` for `r ≥ 1`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Set

namespace PG

/-- The value `±p^z` of a term. -/
def sp (p : ℕ) (t : Bool × ℕ) : ℤ := (if t.1 then 1 else -1) * (p : ℤ) ^ t.2

/-- The value of a list of terms. -/
def val (p : ℕ) (l : List (Bool × ℕ)) : ℤ := (l.map (sp p)).sum

/-- `D_{p,k}`: integers that are sums of at most `k` signed powers of `p`. -/
def D (p k : ℕ) : Set ℤ := {n | ∃ l : List (Bool × ℕ), l.length ≤ k ∧ val p l = n}

theorem val_nil (p : ℕ) : val p [] = 0 := by simp [val]

theorem val_append (p : ℕ) (l₁ l₂ : List (Bool × ℕ)) : val p (l₁ ++ l₂) = val p l₁ + val p l₂ := by
  simp [val]

theorem val_cons (p : ℕ) (t : Bool × ℕ) (l : List (Bool × ℕ)) : val p (t :: l) = sp p t + val p l := by
  simp [val]

theorem zero_mem_D (p k : ℕ) : (0 : ℤ) ∈ D p k := ⟨[], by simp, val_nil p⟩

theorem D_mono {p k l : ℕ} (h : k ≤ l) : D p k ⊆ D p l := by
  rintro n ⟨m, hm, rfl⟩
  exact ⟨m, hm.trans h, rfl⟩

theorem D_add {p k l : ℕ} {n m : ℤ} (hn : n ∈ D p k) (hm : m ∈ D p l) : n + m ∈ D p (k + l) := by
  obtain ⟨a, ha, rfl⟩ := hn
  obtain ⟨b, hb, rfl⟩ := hm
  refine ⟨a ++ b, ?_, val_append p a b⟩
  simp only [List.length_append]
  omega

theorem val_flip (p : ℕ) (l : List (Bool × ℕ)) :
    val p (l.map (fun t => (!t.1, t.2))) = - val p l := by
  induction l with
  | nil => simp [val]
  | cons t l ih =>
    rw [List.map_cons, val_cons, val_cons, ih]
    obtain ⟨b, z⟩ := t
    cases b <;> simp [sp] <;> ring

theorem D_neg {p k : ℕ} {n : ℤ} (hn : n ∈ D p k) : -n ∈ D p k := by
  obtain ⟨a, ha, rfl⟩ := hn
  exact ⟨a.map (fun t => (!t.1, t.2)), by simpa using ha, val_flip p a⟩

theorem pow_mem_D (p z : ℕ) : ((p : ℤ) ^ z) ∈ D p 1 :=
  ⟨[(true, z)], by simp, by simp [val, sp]⟩

/-- Every integer lies in some `D_{p,k}`. -/
theorem mem_D_abs (p : ℕ) (n : ℤ) : n ∈ D p n.natAbs := by
  rcases le_total 0 n with h | h
  · refine ⟨List.replicate n.natAbs (true, 0), by simp, ?_⟩
    simp [val, sp, List.map_replicate, List.sum_replicate]
    omega
  · refine ⟨List.replicate n.natAbs (false, 0), by simp, ?_⟩
    simp [val, sp, List.map_replicate, List.sum_replicate]
    rw [abs_of_nonpos h]
    simp

/-- The digit ideal `I_p`: subsets of `ℤ` contained in some `D_{p,k}`. -/
def Ip (p : ℕ) : Set (Set ℤ) := {A | ∃ k, A ⊆ D p k}

theorem Ip_sub {p : ℕ} {A : Set ℤ} (hA : A ∈ Ip p) (B : Set ℤ) (hB : B ⊆ A) : B ∈ Ip p := by
  obtain ⟨k, hk⟩ := hA
  exact ⟨k, hB.trans hk⟩

theorem Ip_union {p : ℕ} {A B : Set ℤ} (hA : A ∈ Ip p) (hB : B ∈ Ip p) : A ∪ B ∈ Ip p := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨max k l, Set.union_subset (hk.trans (D_mono (le_max_left _ _))) (hl.trans (D_mono (le_max_right _ _)))⟩

theorem Ip_single (p : ℕ) (n : ℤ) : ({n} : Set ℤ) ∈ Ip p :=
  ⟨n.natAbs, by simpa using mem_D_abs p n⟩

theorem Ip_add {p : ℕ} {A B : Set ℤ} (hA : A ∈ Ip p) (hB : B ∈ Ip p) :
    Set.image2 (· + ·) A B ∈ Ip p := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨k + l, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact D_add (hk ha) (hl hb)

theorem Ip_neg {p : ℕ} {A : Set ℤ} (hA : A ∈ Ip p) : (fun x : ℤ => -x) '' A ∈ Ip p := by
  obtain ⟨k, hk⟩ := hA
  refine ⟨k, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact D_neg (hk ha)

/-- (I1)-(I5) for `I_p`, assuming properness (I3), which rests on the (not formalized) counting Lemma 5.1. -/
theorem Ip_admissible (p : ℕ) (hproper : (Set.univ : Set ℤ) ∉ Ip p) : AdmIdeal (Ip p) where
  sub := fun _ hA B hB => Ip_sub hA B hB
  union := fun _ hA _ hB => Ip_union hA hB
  single := Ip_single p
  proper := hproper
  add := fun _ hA _ hB => Ip_add hA hB
  neg := fun _ hA => Ip_neg hA

/-! ### Proposition 5.3: `I_{p^r} = I_p` -/

theorem val_pow_map (p r : ℕ) (l : List (Bool × ℕ)) :
    val (p ^ r) l = val p (l.map (fun t => (t.1, r * t.2))) := by
  induction l with
  | nil => simp [val]
  | cons t l ih =>
    rw [List.map_cons, val_cons, val_cons, ih]
    obtain ⟨b, z⟩ := t
    simp [sp, pow_mul]

theorem D_pow_subset (p r k : ℕ) : D (p ^ r) k ⊆ D p k := by
  rintro n ⟨l, hl, rfl⟩
  exact ⟨l.map (fun t => (t.1, r * t.2)), by simpa using hl, (val_pow_map p r l).symm⟩

/-- A single term `±p^n` is a sum of `p^(n % r)` terms `±(p^r)^(n / r)`. -/
theorem val_replicate_term (p r : ℕ) (hr : 1 ≤ r) (b : Bool) (n : ℕ) :
    val (p ^ r) (List.replicate (p ^ (n % r)) (b, n / r)) = sp p (b, n) := by
  simp only [val, List.map_replicate, List.sum_replicate, sp]
  have hn : n = n % r + r * (n / r) := (Nat.mod_add_div n r).symm
  have h1 : (((p ^ r : ℕ) : ℤ)) ^ (n / r) = (p : ℤ) ^ (r * (n / r)) := by
    push_cast; rw [← pow_mul]
  rw [h1]
  conv_rhs => rw [hn, pow_add]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem val_flatMap (p r : ℕ) (hr : 1 ≤ r) (l : List (Bool × ℕ)) :
    val (p ^ r) (l.flatMap (fun t => List.replicate (p ^ (t.2 % r)) (t.1, t.2 / r))) = val p l := by
  induction l with
  | nil => simp [val]
  | cons t l ih =>
    rw [List.flatMap_cons, val_append, val_cons, val_replicate_term p r hr, ih]

theorem D_subset_pow {p : ℕ} (hp : 1 ≤ p) (r k : ℕ) (hr : 1 ≤ r) : D p k ⊆ D (p ^ r) (k * p ^ (r - 1)) := by
  rintro n ⟨l, hl, rfl⟩
  refine ⟨l.flatMap (fun t => List.replicate (p ^ (t.2 % r)) (t.1, t.2 / r)), ?_, ?_⟩
  · rw [List.length_flatMap]
    simp only [List.length_replicate]
    have hle : ∀ t ∈ l, p ^ (t.2 % r) ≤ p ^ (r - 1) := by
      intro t _
      exact Nat.pow_le_pow_right hp (by have := Nat.mod_lt t.2 (by omega : 0 < r); omega)
    calc (l.map (fun t => p ^ (t.2 % r))).sum
        ≤ (l.map (fun _ => p ^ (r - 1))).sum := List.sum_le_sum (by simpa using hle)
      _ = l.length * p ^ (r - 1) := by simp
      _ ≤ k * p ^ (r - 1) := Nat.mul_le_mul_right _ hl
  · exact val_flatMap p r hr l

theorem Ip_pow {p : ℕ} (hp : 1 ≤ p) {r : ℕ} (hr : 1 ≤ r) : Ip (p ^ r) = Ip p := by
  ext A
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.trans (D_pow_subset p r k)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k * p ^ (r - 1), hk.trans (D_subset_pow hp r k hr)⟩

end PG
