import Mathlib
import LeanCheck.PGDigit

/-!
# PG: finiteness of `D_{p,k} ∩ D_{q,l}` from the S-unit equation theorem (Lean check)

Scope. Theorem 8.1 of `PG_v5`. For multiplicatively independent integers `p, q ≥ 2` the sets `D_{p,k} ∩ D_{q,l}` are finite,
assuming the S-unit equation theorem in the form `SUnitFinite p q`: for every `m` there are only finitely many lists
`y` of `m` elements of the group `Gam p q = {±p^a q^c}` with `∑ y = 1` and no nonempty sublist with sum `0`.
That theorem (Evertse; van der Poorten and Schlickewei; Evertse, Schlickewei and Schmidt) is NOT proved here: it is a hypothesis.

* `pow_mul_pow_inj`, `ratio_inj` : independence of `p` and `q` determines exponents from ratios;
* `exists_block` : a nonzero multiset of terms with sum `0` contains a minimal nonempty sub-multiset with sum `0`;
* `block_tuple_*` : a minimal block with a `q`-term becomes a nondegenerate solution of the S-unit equation;
* `reach_finite` : the set of integers `n` that are `∑` of the `p`-terms of a vanishing configuration of at most `a` `p`-terms and
  at most `b` `q`-terms is finite (strong induction on `a + b`);
* `inter_finite` : `D p k ∩ D q l` is finite; `Ip_inter_finite` : a set in `I_p` and `I_q` is finite.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Set

namespace PG

/-- Terms: `(isP, positive, exponent)` stand for `± p^e` (if `isP`) or `± q^e`. -/
abbrev Tm := Bool × Bool × ℕ

def tv (p q : ℕ) (t : Tm) : ℤ :=
  (if t.2.1 then 1 else -1) * (if t.1 then (p : ℤ) else (q : ℤ)) ^ t.2.2

def mval (p q : ℕ) (m : Multiset Tm) : ℤ := (m.map (tv p q)).sum

def Pp (m : Multiset Tm) : Multiset Tm := m.filter (fun t : Tm => t.1 = true)

theorem mval_add (p q : ℕ) (m n : Multiset Tm) : mval p q (m + n) = mval p q m + mval p q n := by
  simp [mval]

theorem mval_cons (p q : ℕ) (t : Tm) (m : Multiset Tm) : mval p q (t ::ₘ m) = tv p q t + mval p q m := by
  simp [mval]

theorem mval_zero (p q : ℕ) : mval p q 0 = 0 := by simp [mval]

theorem tv_ne_zero (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (t : Tm) : tv p q t ≠ 0 := by
  obtain ⟨a, b, e⟩ := t
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpe : (p : ℤ) ^ e ≠ 0 := pow_ne_zero _ hp'
  have hqe : (q : ℤ) ^ e ≠ 0 := pow_ne_zero _ hq'
  cases a <;> cases b <;> simp [tv, hpe, hqe]

/-! ### Minimal vanishing blocks -/

theorem exists_block (p q : ℕ) (m : Multiset Tm) (hm : mval p q m = 0) (hne : m ≠ 0) :
    ∃ B ≤ m, B ≠ 0 ∧ mval p q B = 0 ∧ ∀ C ≤ B, C ≠ 0 → mval p q C = 0 → C = B := by
  classical
  have hex : ∃ k, ∃ B ≤ m, B ≠ 0 ∧ mval p q B = 0 ∧ Multiset.card B = k :=
    ⟨_, m, le_rfl, hne, hm, rfl⟩
  obtain ⟨B, hBm, hB0, hBv, hBk⟩ := Nat.find_spec hex
  refine ⟨B, hBm, hB0, hBv, fun C hCB hC0 hCv => ?_⟩
  have h1 : Nat.find hex ≤ Multiset.card C :=
    Nat.find_min' hex ⟨C, hCB.trans hBm, hC0, hCv, rfl⟩
  exact Multiset.eq_of_le_of_card_le hCB (by rw [hBk]; exact h1)

/-! ### Independence of the bases -/

theorem pow_eq_one_zero {p n : ℕ} (hp : 2 ≤ p) (h : p ^ n = 1) : n = 0 := by
  by_contra hn
  have := Nat.one_lt_pow hn (by omega : 1 < p)
  omega

theorem pow_mul_pow_inj (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) {a b c d : ℕ}
    (h : p ^ a * q ^ b = p ^ c * q ^ d) : a = c ∧ b = d := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  rcases le_total a c with hac | hca <;> rcases le_total b d with hbd | hdb
  · obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hbd
    have h2 : p ^ a * q ^ b * 1 = p ^ a * q ^ b * (p ^ c' * q ^ d') := by
      calc p ^ a * q ^ b * 1 = p ^ (a + c') * q ^ (b + d') := by rw [mul_one]; exact h
        _ = p ^ a * q ^ b * (p ^ c' * q ^ d') := by ring
    have h3 : p ^ c' * q ^ d' = 1 :=
      (Nat.eq_of_mul_eq_mul_left (by positivity) h2).symm
    have h4 : p ^ c' = 1 := Nat.eq_one_of_mul_eq_one_right h3
    have h5 : q ^ d' = 1 := Nat.eq_one_of_mul_eq_one_left h3
    have := pow_eq_one_zero hp h4
    have := pow_eq_one_zero hq h5
    omega
  · obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hdb
    have h2 : p ^ a * q ^ d * q ^ b' = p ^ a * q ^ d * p ^ c' := by
      calc p ^ a * q ^ d * q ^ b' = p ^ a * q ^ (d + b') := by ring
        _ = p ^ (a + c') * q ^ d := h
        _ = p ^ a * q ^ d * p ^ c' := by ring
    have h3 : q ^ b' = p ^ c' := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    obtain ⟨h4, h5⟩ := hpq c' b' h3.symm
    subst h4
    subst h5
    simp at h
    omega
  · obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hbd
    have h2 : p ^ c * q ^ b * p ^ a' = p ^ c * q ^ b * q ^ d' := by
      calc p ^ c * q ^ b * p ^ a' = p ^ (c + a') * q ^ b := by ring
        _ = p ^ c * q ^ (b + d') := h
        _ = p ^ c * q ^ b * q ^ d' := by ring
    have h3 : p ^ a' = q ^ d' := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    obtain ⟨h4, h5⟩ := hpq a' d' h3
    subst h4
    subst h5
    simp
  · obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hdb
    have h2 : p ^ c * q ^ d * (p ^ a' * q ^ b') = p ^ c * q ^ d * 1 := by
      rw [mul_one]
      calc p ^ c * q ^ d * (p ^ a' * q ^ b') = p ^ (c + a') * q ^ (d + b') := by ring
        _ = p ^ c * q ^ d := h
    have h3 : p ^ a' * q ^ b' = 1 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have h4 : p ^ a' = 1 := Nat.eq_one_of_mul_eq_one_right h3
    have h5 : q ^ b' = 1 := Nat.eq_one_of_mul_eq_one_left h3
    have := pow_eq_one_zero hp h4
    have := pow_eq_one_zero hq h5
    omega

theorem ratio_inj (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) {α β α' β' : ℕ}
    (h : (p : ℚ) ^ α / (q : ℚ) ^ β = (p : ℚ) ^ α' / (q : ℚ) ^ β') : α = α' ∧ β = β' := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [div_eq_div_iff (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)] at h
  have h2 : (p : ℚ) ^ α * (q : ℚ) ^ β' = (p : ℚ) ^ α' * (q : ℚ) ^ β := by linarith
  have h3 : p ^ α * q ^ β' = p ^ α' * q ^ β := by exact_mod_cast h2
  obtain ⟨h4, h5⟩ := pow_mul_pow_inj p q hp hq hpq h3
  exact ⟨h4, h5.symm⟩

/-! ### From a minimal block to a solution of the S-unit equation -/

/-- The group `{± p^a q^c}` of the S-unit equation. -/
def Gam (p q : ℕ) : Set ℚ :=
  {x | ∃ (s : Bool) (a c : ℤ), x = (if s then 1 else -1) * (p : ℚ) ^ a * (q : ℚ) ^ c}

/-- The S-unit equation theorem, as a hypothesis: for every `m` there are only finitely many lists `y` of `m` elements of
`Gam p q` with sum `1` and no nonempty sublist with sum `0`. -/
def SUnitFinite (p q : ℕ) : Prop :=
  ∀ m : ℕ, {y : List ℚ | y.length = m ∧ (∀ x ∈ y, x ∈ Gam p q) ∧ y.sum = 1 ∧
    ∀ z : List ℚ, z.Sublist y → z ≠ [] → z.sum ≠ 0}.Finite

theorem sum_map_neg_div {α : Type*} (f : α → ℚ) (c : ℚ) (l : List α) :
    (l.map (fun t => -f t / c)).sum = -(l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem tuple_of_block {α : Type*} (f : α → ℚ) (c : ℚ) (hc : c ≠ 0) (b : List α)
    (hsum : (b.map f).sum = -c)
    (hnd : ∀ cl : List α, cl.Sublist b → cl ≠ [] → (cl.map f).sum ≠ 0) :
    (b.map (fun t => -f t / c)).sum = 1 ∧
      ∀ z : List ℚ, z.Sublist (b.map (fun t => -f t / c)) → z ≠ [] → z.sum ≠ 0 := by
  constructor
  · rw [sum_map_neg_div, hsum]
    field_simp
  · intro z hz hz0
    obtain ⟨cl, hcl, rfl⟩ := List.sublist_map_iff.1 hz
    have hcl0 : cl ≠ [] := by
      rintro rfl
      exact hz0 rfl
    rw [sum_map_neg_div]
    intro h
    apply hnd cl hcl hcl0
    rcases div_eq_zero_iff.1 h with h1 | h1
    · linarith
    · exact absurd h1 hc

theorem abs_tv_rat (p q : ℕ) (t : Tm) :
    |(tv p q t : ℚ)| = (if t.1 then (p : ℚ) else (q : ℚ)) ^ t.2.2 := by
  obtain ⟨a, b, e⟩ := t
  cases a <;> cases b <;> simp [tv, abs_pow]

theorem ratio_mem_Gam (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (tN : Tm) (hN : tN.1 = false) (t : Tm) :
    -(tv p q t : ℚ) / (tv p q tN : ℚ) ∈ Gam p q := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', f⟩ := tN
  simp only at hN
  subst hN
  cases a <;> cases b <;> cases b'
  · exact ⟨false, 0, (e : ℤ) - (f : ℤ), by
      simp [tv, zpow_sub₀ hq0, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨true, 0, (e : ℤ) - (f : ℤ), by
      simp [tv, zpow_sub₀ hq0, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨true, 0, (e : ℤ) - (f : ℤ), by
      simp [tv, zpow_sub₀ hq0, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨false, 0, (e : ℤ) - (f : ℤ), by
      simp [tv, zpow_sub₀ hq0, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨false, (e : ℤ), -(f : ℤ), by
      simp [tv, zpow_neg, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨true, (e : ℤ), -(f : ℤ), by
      simp [tv, zpow_neg, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨true, (e : ℤ), -(f : ℤ), by
      simp [tv, zpow_neg, zpow_natCast, div_eq_mul_inv]⟩
  · exact ⟨false, (e : ℤ), -(f : ℤ), by
      simp [tv, zpow_neg, zpow_natCast, div_eq_mul_inv]⟩

theorem list_sum_cast (p q : ℕ) (l : List Tm) :
    (((l.map (tv p q)).sum : ℤ) : ℚ) = (l.map (fun t => (tv p q t : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

theorem block_cand (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (B : Multiset Tm)
    (hv : mval p q B = 0)
    (hmin : ∀ C ≤ B, C ≠ 0 → mval p q C = 0 → C = B)
    (hP : ∃ t ∈ B, t.1 = true) (hQ : ∃ t ∈ B, t.1 = false) :
    ∃ y : List ℚ, y.length + 1 = Multiset.card B ∧ (∀ x ∈ y, x ∈ Gam p q) ∧ y.sum = 1 ∧
      (∀ z : List ℚ, z.Sublist y → z ≠ [] → z.sum ≠ 0) ∧
      ∃ x ∈ y, ∃ z ∈ y.sublists, ∃ α β : ℕ, |x| = (p : ℚ) ^ α / (q : ℚ) ^ β ∧
        |(mval p q (Pp B) : ℚ)| = (q : ℚ) ^ β * |z.sum| := by
  classical
  obtain ⟨tN, htN, htN1⟩ := hQ
  obtain ⟨ta, hta, hta1⟩ := hP
  obtain ⟨B', hB'⟩ : ∃ B' : Multiset Tm, B' = B.erase tN := ⟨_, rfl⟩
  have hcons : tN ::ₘ B' = B := by rw [hB']; exact Multiset.cons_erase htN
  have hB'le : B' ≤ B := by rw [hB']; exact Multiset.erase_le tN B
  obtain ⟨b', hb'c⟩ : ∃ b' : List Tm, (b' : Multiset Tm) = B' := ⟨B'.toList, Multiset.coe_toList B'⟩
  have hc : (tv p q tN : ℚ) ≠ 0 := by exact_mod_cast tv_ne_zero p q hp hq tN
  have hcardB : Multiset.card B' + 1 = Multiset.card B := by
    rw [← hcons]; simp
  have hlen : b'.length = Multiset.card B' := by rw [← hb'c]; simp
  have hsumZ : (b'.map (tv p q)).sum = - tv p q tN := by
    have h1 : mval p q (tN ::ₘ B') = tv p q tN + mval p q B' := mval_cons p q tN B'
    rw [hcons, hv] at h1
    have h2 : mval p q B' = (b'.map (tv p q)).sum := by
      rw [← hb'c]; simp [mval]
    omega
  have h3 : (b'.map (fun t => (tv p q t : ℚ))).sum = -(tv p q tN : ℚ) := by
    have := list_sum_cast p q b'
    rw [hsumZ] at this
    push_cast at this
    linarith
  have hnd : ∀ cl : List Tm, cl.Sublist b' → cl ≠ [] →
      (cl.map (fun t => (tv p q t : ℚ))).sum ≠ 0 := by
    intro cl hcl hne hz
    have hcl' : (cl : Multiset Tm) ≤ B' := by
      rw [← hb'c]; exact Multiset.coe_le.2 hcl.subperm
    have hCv : mval p q (cl : Multiset Tm) = 0 := by
      have := list_sum_cast p q cl
      rw [hz] at this
      have h0 : ((cl.map (tv p q)).sum : ℤ) = 0 := by exact_mod_cast this
      simpa [mval] using h0
    have hC0 : (cl : Multiset Tm) ≠ 0 := by
      intro h
      exact hne ((Multiset.coe_eq_zero cl).1 h)
    have heq := hmin _ (hcl'.trans hB'le) hC0 hCv
    have hcard : Multiset.card (cl : Multiset Tm) ≤ Multiset.card B' := Multiset.card_le_card hcl'
    rw [heq] at hcard
    omega
  obtain ⟨hs1, hnd1⟩ := tuple_of_block (fun t : Tm => (tv p q t : ℚ)) (tv p q tN) hc b' h3 hnd
  have hne : ta ≠ tN := by
    intro h
    rw [h] at hta1
    rw [htN1] at hta1
    exact absurd hta1 (by decide)
  have htaB' : ta ∈ b' := by
    have : ta ∈ B' := by rw [hB']; exact (Multiset.mem_erase_of_ne hne).2 hta
    rw [← hb'c] at this
    exact Multiset.mem_coe.1 this
  refine ⟨b'.map (fun t => -(tv p q t : ℚ) / (tv p q tN : ℚ)), ?_, ?_, hs1, hnd1, ?_⟩
  · rw [List.length_map, hlen]; exact hcardB
  · intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
    exact ratio_mem_Gam p q hp hq tN htN1 t
  · refine ⟨-(tv p q ta : ℚ) / (tv p q tN : ℚ), List.mem_map.2 ⟨ta, htaB', rfl⟩,
      (b'.filter (fun t => decide (t.1 = true))).map (fun t => -(tv p q t : ℚ) / (tv p q tN : ℚ)),
      List.mem_sublists.2 ((List.filter_sublist).map _), ta.2.2, tN.2.2, ?_, ?_⟩
    · rw [abs_div, abs_neg, abs_tv_rat, abs_tv_rat, hta1, htN1]
      simp
    · have hPB : Pp B = ((b'.filter (fun t => decide (t.1 = true)) : List Tm) : Multiset Tm) := by
        unfold Pp
        rw [← hcons, Multiset.filter_cons_of_neg _ (by simp [htN1]), ← hb'c, Multiset.filter_coe]
      have hS : (mval p q (Pp B) : ℚ) =
          ((b'.filter (fun t => decide (t.1 = true))).map (fun t => (tv p q t : ℚ))).sum := by
        rw [hPB]
        have := list_sum_cast p q (b'.filter (fun t => decide (t.1 = true)))
        rw [← this]
        simp [mval]
      rw [hS]
      have hz := sum_map_neg_div (fun t : Tm => (tv p q t : ℚ)) (tv p q tN : ℚ)
        (b'.filter (fun t => decide (t.1 = true)))
      beta_reduce at hz
      rw [hz, abs_div, abs_neg, abs_tv_rat]
      have hqb : (q : ℚ) ^ tN.2.2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
      simp only [htN1]
      simp
      field_simp

/-! ### Finiteness of the possible values of mixed blocks -/

def Cand (p q : ℕ) (y : List ℚ) : Set ℚ :=
  {c | ∃ x ∈ y, ∃ z ∈ y.sublists, ∃ α β : ℕ, |x| = (p : ℚ) ^ α / (q : ℚ) ^ β ∧
      c = (q : ℚ) ^ β * |z.sum|}

theorem Cand_finite (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (y : List ℚ) : (Cand p q y).Finite := by
  classical
  let S : ℚ → List ℚ → Set ℚ := fun x z =>
    {c | ∃ α β : ℕ, |x| = (p : ℚ) ^ α / (q : ℚ) ^ β ∧ c = (q : ℚ) ^ β * |z.sum|}
  have hS : ∀ x z, (S x z).Subsingleton := by
    rintro x z c1 ⟨α1, β1, h1, rfl⟩ c2 ⟨α2, β2, h2, rfl⟩
    have := ratio_inj p q hp hq hpq (h1.symm.trans h2)
    rw [this.2]
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet y.toFinset) fun x _ =>
    Set.Finite.biUnion (Finset.finite_toSet y.sublists.toFinset) fun z _ => (hS x z).finite) ?_
  rintro c ⟨x, hx, z, hz, α, β, h1, h2⟩
  simp only [Set.mem_iUnion]
  exact ⟨x, by simpa using hx, z, by simpa using hz, α, β, h1, h2⟩

theorem finite_abs_mem (F : Set ℚ) (hF : F.Finite) : {w : ℤ | |(w : ℚ)| ∈ F}.Finite := by
  refine Set.Finite.subset ((hF.image (fun c : ℚ => ⌊c⌋)).union (hF.image (fun c : ℚ => -⌊c⌋))) ?_
  intro w hw
  have h1 : |(w : ℚ)| = ((|w| : ℤ) : ℚ) := by push_cast; rfl
  rcases abs_choice w with h | h
  · left
    refine ⟨|(w : ℚ)|, hw, ?_⟩
    rw [h1]
    dsimp only
    rw [Int.floor_intCast, h]
  · right
    refine ⟨|(w : ℚ)|, hw, ?_⟩
    rw [h1]
    dsimp only
    rw [Int.floor_intCast, h]
    ring

def IsBlock (p q : ℕ) (B : Multiset Tm) : Prop :=
  B ≠ 0 ∧ mval p q B = 0 ∧ ∀ C ≤ B, C ≠ 0 → mval p q C = 0 → C = B

/-- The `p`-parts of the mixed minimal blocks with at most `M` terms. -/
def Vals (p q M : ℕ) : Set ℤ :=
  {w | ∃ B : Multiset Tm, IsBlock p q B ∧ Multiset.card B ≤ M ∧ (∃ t ∈ B, t.1 = true) ∧
    (∃ t ∈ B, t.1 = false) ∧ w = mval p q (Pp B)}

theorem Vals_finite (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (hyp : SUnitFinite p q) (M : ℕ) :
    (Vals p q M).Finite := by
  classical
  let F : Set ℚ := ⋃ N ∈ Finset.range (M + 1), ⋃ y ∈ {y : List ℚ | y.length = N - 1 ∧
      (∀ x ∈ y, x ∈ Gam p q) ∧ y.sum = 1 ∧ ∀ z : List ℚ, z.Sublist y → z ≠ [] → z.sum ≠ 0},
    Cand p q y
  have hF : F.Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun N _ =>
      Set.Finite.biUnion (hyp (N - 1)) fun y _ => Cand_finite p q hp hq hpq y
  refine Set.Finite.subset (finite_abs_mem F hF) ?_
  rintro w ⟨B, ⟨hB0, hv, hmin⟩, hcard, hP, hQ, rfl⟩
  obtain ⟨y, hlen, hGam, hsum, hnd, x, hx, z, hz, α, β, h1, h2⟩ :=
    block_cand p q hp hq B hv hmin hP hQ
  show |((mval p q (Pp B) : ℤ) : ℚ)| ∈ F
  simp only [F, Set.mem_iUnion]
  refine ⟨Multiset.card B, by simp; omega, y, ⟨by omega, hGam, hsum, hnd⟩, ?_⟩
  exact ⟨x, hx, z, hz, α, β, h1, h2⟩

/-! ### Reachable values and the main finiteness theorem -/

def Qq (m : Multiset Tm) : Multiset Tm := m.filter (fun t : Tm => ¬ t.1 = true)

theorem Pp_add_Qq (m : Multiset Tm) : Pp m + Qq m = m := Multiset.filter_add_not _ m

theorem Pp_add (m n : Multiset Tm) : Pp (m + n) = Pp m + Pp n := Multiset.filter_add _ m n

theorem Qq_add (m n : Multiset Tm) : Qq (m + n) = Qq m + Qq n := Multiset.filter_add _ m n

/-- Values `∑` of the `p`-terms of a vanishing configuration with at most `a` `p`-terms and `b` `q`-terms. -/
def Reach (p q a b : ℕ) : Set ℤ :=
  {n | ∃ m : Multiset Tm, Multiset.card (Pp m) ≤ a ∧ Multiset.card (Qq m) ≤ b ∧ mval p q m = 0 ∧
    n = mval p q (Pp m)}

theorem reach_zero_left (p q b : ℕ) : Reach p q 0 b ⊆ {0} := by
  rintro n ⟨m, ha, _, _, rfl⟩
  have : Pp m = 0 := Multiset.card_eq_zero.1 (by omega)
  simp [this, mval_zero]

theorem reach_zero_right (p q a : ℕ) : Reach p q a 0 ⊆ {0} := by
  rintro n ⟨m, _, hb, hv, rfl⟩
  have hQ : Qq m = 0 := Multiset.card_eq_zero.1 (by omega)
  have h1 := Pp_add_Qq m
  rw [hQ, add_zero] at h1
  rw [h1]
  simpa using hv

theorem reach_finite (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (hyp : SUnitFinite p q) :
    ∀ s a b : ℕ, a + b = s → (Reach p q a b).Finite := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro a b hs
  rcases a with _ | a'
  · exact (Set.finite_singleton 0).subset (reach_zero_left p q b)
  rcases b with _ | b'
  · exact (Set.finite_singleton 0).subset (reach_zero_right p q (a' + 1))
  have h1 := ih (a' + (b' + 1)) (by omega) a' (b' + 1) rfl
  have h2 := ih ((a' + 1) + b') (by omega) (a' + 1) b' rfl
  have h3 := ih (a' + b') (by omega) a' b' rfl
  have h4 := Vals_finite p q hp hq hpq hyp ((a' + 1) + (b' + 1))
  refine Set.Finite.subset ((h1.union h2).union (h4.image2 (· + ·) h3)) ?_
  rintro n ⟨m, hPm, hQm, hv, rfl⟩
  by_cases hm0 : m = 0
  · subst hm0
    left; left
    exact ⟨0, by simp [Pp], by simp [Qq], mval_zero p q, by simp [Pp, mval_zero]⟩
  obtain ⟨B, hBm, hB0, hBv, hmin⟩ := exists_block p q m hv hm0
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 hBm
  have hRv : mval p q R = 0 := by
    rw [hR, mval_add, hBv] at hv
    simpa using hv
  have hPm' : Multiset.card (Pp B) + Multiset.card (Pp R) ≤ a' + 1 := by
    rw [← Multiset.card_add, ← Pp_add, ← hR]; exact hPm
  have hQm' : Multiset.card (Qq B) + Multiset.card (Qq R) ≤ b' + 1 := by
    rw [← Multiset.card_add, ← Qq_add, ← hR]; exact hQm
  have hn : mval p q (Pp m) = mval p q (Pp B) + mval p q (Pp R) := by
    rw [hR, Pp_add, mval_add]
  by_cases hPB : ∃ t ∈ B, t.1 = true
  · by_cases hQB : ∃ t ∈ B, t.1 = false
    · -- mixed block
      obtain ⟨t1, ht1, ht1P⟩ := hPB
      obtain ⟨t2, ht2, ht2Q⟩ := hQB
      have hc1 : 0 < Multiset.card (Pp B) :=
        Multiset.card_pos_iff_exists_mem.2 ⟨t1, Multiset.mem_filter.2 ⟨ht1, ht1P⟩⟩
      have hc2 : 0 < Multiset.card (Qq B) :=
        Multiset.card_pos_iff_exists_mem.2 ⟨t2, Multiset.mem_filter.2 ⟨ht2, by simp [ht2Q]⟩⟩
      have hcB : Multiset.card B = Multiset.card (Pp B) + Multiset.card (Qq B) := by
        rw [← Multiset.card_add, Pp_add_Qq]
      right
      rw [hn]
      refine ⟨mval p q (Pp B), ⟨B, ⟨hB0, hBv, hmin⟩, by omega, ⟨t1, ht1, ht1P⟩, ⟨t2, ht2, ht2Q⟩, rfl⟩,
        mval p q (Pp R), ⟨R, by omega, by omega, hRv, rfl⟩, rfl⟩
    · -- no q-term in B: B consists of p-terms
      push_neg at hQB
      have hall : ∀ t ∈ B, t.1 = true := by
        intro t ht
        have := hQB t ht
        cases h : t.1
        · exact absurd h this
        · rfl
      have hPBB : Pp B = B := Multiset.filter_eq_self.2 hall
      obtain ⟨t1, ht1, _⟩ := hPB
      have hc1 : 0 < Multiset.card (Pp B) :=
        Multiset.card_pos_iff_exists_mem.2 ⟨t1, by rw [hPBB]; exact ht1⟩
      left; left
      rw [hn, hPBB, hBv, zero_add]
      exact ⟨R, by omega, by omega, hRv, rfl⟩
  · -- no p-term in B
    push_neg at hPB
    have hPB0 : Pp B = 0 := Multiset.filter_eq_nil.2 (fun t ht => by simpa using hPB t ht)
    obtain ⟨t1, ht1⟩ := Multiset.exists_mem_of_ne_zero hB0
    have hc2 : 0 < Multiset.card (Qq B) :=
      Multiset.card_pos_iff_exists_mem.2 ⟨t1, Multiset.mem_filter.2 ⟨ht1, by simpa using hPB t1 ht1⟩⟩
    left; right
    rw [hn, hPB0]
    simp only [mval_zero, zero_add]
    exact ⟨R, by omega, by omega, hRv, rfl⟩

theorem mval_P_list (p q : ℕ) (L : List (Bool × ℕ)) :
    mval p q (((L.map (fun t => ((true, t.1, t.2) : Tm))) : List Tm) : Multiset Tm) = val p L := by
  unfold mval val
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  congr 2

theorem mval_Q_list (p q : ℕ) (L : List (Bool × ℕ)) :
    mval p q (((L.map (fun t => ((false, !t.1, t.2) : Tm))) : List Tm) : Multiset Tm) =
      val q (L.map (fun t => (!t.1, t.2))) := by
  unfold mval val
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map, List.map_map]
  congr 2

/-- Theorem 8.1 of `PG_v5`, from the S-unit equation theorem: for multiplicatively independent `p, q ≥ 2`,
`D_{p,k} ∩ D_{q,l}` is finite. -/
theorem inter_finite (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (hyp : SUnitFinite p q) (k l : ℕ) :
    (D p k ∩ D q l).Finite := by
  refine (reach_finite p q hp hq hpq hyp (k + l) k l rfl).subset ?_
  rintro n ⟨⟨LP, hLP, hnP⟩, ⟨LQ, hLQ, hnQ⟩⟩
  let m1 : Multiset Tm := ((LP.map (fun t => ((true, t.1, t.2) : Tm)) : List Tm) : Multiset Tm)
  let m2 : Multiset Tm := ((LQ.map (fun t => ((false, !t.1, t.2) : Tm)) : List Tm) : Multiset Tm)
  have hP1 : Pp m1 = m1 := Multiset.filter_eq_self.2 (by
    intro t ht
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
    rfl)
  have hP2 : Pp m2 = 0 := Multiset.filter_eq_nil.2 (by
    intro t ht
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
    simp)
  have hQ1 : Qq m1 = 0 := Multiset.filter_eq_nil.2 (by
    intro t ht
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
    simp)
  have hQ2 : Qq m2 = m2 := Multiset.filter_eq_self.2 (by
    intro t ht
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ht)
    simp)
  have hPm : Pp (m1 + m2) = m1 := by rw [Pp_add, hP1, hP2, add_zero]
  have hQm : Qq (m1 + m2) = m2 := by rw [Qq_add, hQ1, hQ2, zero_add]
  refine ⟨m1 + m2, ?_, ?_, ?_, ?_⟩
  · rw [hPm]; simpa [m1] using hLP
  · rw [hQm]; simpa [m2] using hLQ
  · rw [mval_add]
    have e1 : mval p q m1 = n := by rw [← hnP]; exact mval_P_list p q LP
    have e2 : mval p q m2 = -n := by
      rw [← hnQ]
      have := mval_Q_list p q LQ
      rw [val_flip] at this
      exact this
    rw [e1, e2]; ring
  · rw [hPm, ← hnP]; exact (mval_P_list p q LP).symm

theorem Ip_inter_finite (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (hyp : SUnitFinite p q)
    {A : Set ℤ} (hA1 : A ∈ Ip p) (hA2 : A ∈ Ip q) : A.Finite := by
  obtain ⟨k, hk⟩ := hA1
  obtain ⟨l, hl⟩ := hA2
  exact (inter_finite p q hp hq hpq hyp k l).subset (fun x hx => ⟨hk hx, hl hx⟩)

theorem finite_mem_Ip (p : ℕ) {A : Set ℤ} (hA : A.Finite) : A ∈ Ip p := by
  obtain ⟨N, hN⟩ := (hA.image Int.natAbs).bddAbove
  exact ⟨N, fun x hx => D_mono (hN ⟨x, hx, rfl⟩) (mem_D_abs p x)⟩

theorem Ip_inter_eq (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : ∀ u v : ℕ, p ^ u = q ^ v → u = 0 ∧ v = 0) (hyp : SUnitFinite p q) (A : Set ℤ) :
    (A ∈ Ip p ∧ A ∈ Ip q) ↔ A.Finite :=
  ⟨fun h => Ip_inter_finite p q hp hq hpq hyp h.1 h.2, fun h => ⟨finite_mem_Ip p h, finite_mem_Ip q h⟩⟩

end PG
