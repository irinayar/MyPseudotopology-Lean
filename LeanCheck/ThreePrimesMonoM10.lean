import LeanCheck.ThreePrimesExactM5

/-!
# ThreePrimesMonoM10: iteration and monotonicity of the exact counting bound

* `iterate_cstarM10`: the iteration `c_{j+1} = C(c_j)`, `c_0 = 0`, equals `c*` from the index `c*` on.
* `single_cstarM10`: for one integer `p ≥ 2` with `m < p^(2a+1)` one has `c* = 0`.
* `bound_jumpM10`: raising the exponent of `p` by one when `m = p^(2 a p + 1)` does not change `D m^(c*)`.
* `boundM10_antitone`: for primes and the forced exponents, `D m^(c*)` with `m = ⌈1/δ⌉` is nonincreasing
  as `δ` increases on `0 < δ ≤ 1/2` (Proposition on monotonicity of the exact counting bound).
* `two_pow_L_monoM10`: `⌈α η² + α η⌉` with `η = log₂ m` is nondecreasing in `m ≥ 1` for `α ≥ 0`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The exact counting bound `D m^(c*)`. -/
noncomputable def boundM10 (S : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  Dprod S a * m ^ cstarM5 S a m

lemma mem_ccset_iffM10 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m N p n : ℕ) :
    (p, n) ∈ CCset S a m N ↔ p ∈ S ∧ a p < n ∧ p ^ (n ^ 2) ≤ m * Dprod S a * N := by
  constructor
  · intro h
    unfold CCset at h
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2.1, h.2.2⟩
  · rintro ⟨hp, han, hq⟩
    exact mem_ccset (hS p hp) hp han hq

lemma dprod_posM10 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) : 0 < Dprod S a := by
  unfold Dprod
  apply Finset.prod_pos
  intro p hp
  have := hS p hp
  positivity

/-- **The iteration** `c_{j+1} = C(c_j)` from `0` equals `c*` for all `j ≥ c*`. -/
theorem iterate_cstarM10 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ)
    (m : ℕ) (hm2 : 2 ≤ m) (j : ℕ) (hj : cstarM5 S a m ≤ j) :
    (fun c => (CCset S a m (m ^ c)).card)^[j] 0 = cstarM5 S a m := by
  set f : ℕ → ℕ := fun c => (CCset S a m (m ^ c)).card with hf
  set cs := cstarM5 S a m with hcs
  have hmono : Monotone f := fun x y hxy =>
    Finset.card_le_card (ccset_mono (Nat.pow_le_pow_right (by omega) hxy))
  have hspec : f cs ≤ cs := cstarM5_spec (exists_cM5 hS hne a m hm2)
  have hle : ∀ i, f^[i] 0 ≤ cs := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hmono ih) hspec
  have hlow : ∀ i, min i cs ≤ f^[i] 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      by_cases h : f^[i] 0 < cs
      · have hnot : ¬ f (f^[i] 0) ≤ f^[i] 0 := fun hc => by
          have : cs ≤ f^[i] 0 := cstarM5_le hc
          omega
        omega
      · have heq : f^[i] 0 = cs := le_antisymm (hle i) (not_lt.mp h)
        have hfix : f cs = cs := by
          refine le_antisymm hspec ?_
          by_contra hlt
          have h1 : f (f cs) ≤ f cs := hmono hspec
          have : cs ≤ f cs := cstarM5_le h1
          omega
        rw [heq, hfix]
        exact min_le_right _ _
  have h1 := hlow j
  have h2 := hle j
  omega

/-- **One prime.** If `m < p^(2a+1)` then `c* = 0`, so the counting bound is `D = p^(a²)`. -/
theorem single_cstarM10 (p : ℕ) (hp : 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (h : m < p ^ (2 * a p + 1)) :
    cstarM5 {p} a m = 0 := by
  have hS : ∀ q ∈ ({p} : Finset ℕ), 2 ≤ q := by
    intro q hq; rw [Finset.mem_singleton] at hq; omega
  refine Nat.le_zero.mp (cstarM5_le ?_)
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨q, n⟩ hx
  rw [mem_ccset_iffM10 hS] at hx
  obtain ⟨hq, han, hle⟩ := hx
  rw [Finset.mem_singleton] at hq
  subst hq
  have hD : Dprod {q} a = q ^ (a q ^ 2) := by simp [Dprod]
  have h1 : q ^ ((a q + 1) ^ 2) ≤ q ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left han 2)
  have e : (a q + 1) ^ 2 = a q ^ 2 + (2 * a q + 1) := by ring
  rw [e, pow_add] at h1
  have h2 : q ^ (a q ^ 2) * m < q ^ (a q ^ 2) * q ^ (2 * a q + 1) :=
    Nat.mul_lt_mul_of_pos_left h (pow_pos (by omega) _)
  rw [pow_zero, mul_one, hD, mul_comm] at hle
  omega

/-- **The jump of one forced exponent** does not change the bound. -/
theorem bound_jumpM10 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a a' : ℕ → ℕ)
    (m p : ℕ) (hm2 : 2 ≤ m) (hp : p ∈ S) (hmp : p ^ (2 * a p + 1) = m) (ha' : a' p = a p + 1)
    (hoth : ∀ q ∈ S, q ≠ p → a' q = a q) : boundM10 S a' m = boundM10 S a m := by
  have hDpos := dprod_posM10 hS a
  have e2 : (a p + 1) ^ 2 = (2 * a p + 1) + a p ^ 2 := by ring
  have hpow : p ^ ((a p + 1) ^ 2) = m * p ^ (a p ^ 2) := by rw [e2, pow_add, hmp]
  have hD : Dprod S a' = m * Dprod S a := by
    unfold Dprod
    rw [← Finset.mul_prod_erase S (fun q => q ^ (a' q ^ 2)) hp,
      ← Finset.mul_prod_erase S (fun q => q ^ (a q ^ 2)) hp]
    have : ∏ q ∈ S.erase p, q ^ (a' q ^ 2) = ∏ q ∈ S.erase p, q ^ (a q ^ 2) := by
      refine Finset.prod_congr rfl fun q hq => ?_
      rw [Finset.mem_erase] at hq
      rw [hoth q hq.2 hq.1]
    rw [this, ha', hpow, mul_assoc]
  have hkey : ∀ c : ℕ, p ^ ((a p + 1) ^ 2) ≤ m * Dprod S a * m ^ c := by
    intro c
    have h1 : p ^ (a p ^ 2) ≤ Dprod S a :=
      Nat.le_of_dvd hDpos (Finset.dvd_prod_of_mem (fun q => q ^ (a q ^ 2)) hp)
    rw [hpow]
    calc m * p ^ (a p ^ 2) ≤ m * Dprod S a := Nat.mul_le_mul le_rfl h1
      _ ≤ m * Dprod S a * m ^ c := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hnotin : ∀ c : ℕ, (p, a p + 1) ∉ CCset S a' m (m ^ c) := by
    intro c h
    rw [mem_ccset_iffM10 hS] at h
    omega
  have hsplit : ∀ c : ℕ,
      CCset S a m (m ^ (c + 1)) = insert (p, a p + 1) (CCset S a' m (m ^ c)) := by
    intro c
    have hcut : m * Dprod S a' * m ^ c = m * Dprod S a * m ^ (c + 1) := by
      rw [hD, pow_succ]; ring
    ext ⟨q, n⟩
    rw [Finset.mem_insert, mem_ccset_iffM10 hS, mem_ccset_iffM10 hS, hcut, Prod.mk.injEq]
    constructor
    · rintro ⟨hq, han, hle⟩
      by_cases hqp : q = p
      · subst hqp
        by_cases hn : n = a q + 1
        · exact Or.inl ⟨rfl, hn⟩
        · exact Or.inr ⟨hq, by omega, hle⟩
      · exact Or.inr ⟨hq, by rw [hoth q hq hqp]; exact han, hle⟩
    · rintro (⟨hq, hn⟩ | ⟨hq, han, hle⟩)
      · subst hq hn
        exact ⟨hp, Nat.lt_succ_self _, hkey (c + 1)⟩
      · refine ⟨hq, ?_, hle⟩
        by_cases hqp : q = p
        · subst hqp; omega
        · rw [← hoth q hq hqp]; exact han
  have hcard : ∀ c : ℕ,
      (CCset S a m (m ^ (c + 1))).card = (CCset S a' m (m ^ c)).card + 1 := by
    intro c
    rw [hsplit c, Finset.card_insert_of_notMem (hnotin c)]
  have hcard0 : 1 ≤ (CCset S a m (m ^ 0)).card := by
    refine Finset.card_pos.mpr ⟨(p, a p + 1), ?_⟩
    rw [mem_ccset_iffM10 hS]
    exact ⟨hp, Nat.lt_succ_self _, hkey 0⟩
  have hspec' := cstarM5_spec (exists_cM5 hS hne a' m hm2)
  have hspec := cstarM5_spec (exists_cM5 hS hne a m hm2)
  have h1 : cstarM5 S a m ≤ cstarM5 S a' m + 1 :=
    cstarM5_le (by rw [hcard]; omega)
  have h0 : cstarM5 S a m ≠ 0 := by
    intro h
    rw [h] at hspec
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h2 : cstarM5 S a' m ≤ k := by
    refine cstarM5_le ?_
    rw [hk, Nat.succ_eq_add_one, hcard] at hspec
    omega
  have hcs : cstarM5 S a m = cstarM5 S a' m + 1 := by omega
  unfold boundM10
  rw [hD, hcs, pow_succ]
  ring

/-- For a fixed exponent vector the bound is nondecreasing in `m`. -/
lemma bound_mono_mM10 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ)
    (m n : ℕ) (hm2 : 2 ≤ m) (hmn : m ≤ n) : boundM10 S a m ≤ boundM10 S a n := by
  have hspec := cstarM5_spec (exists_cM5 hS hne a n (le_trans hm2 hmn))
  have hc : cstarM5 S a m ≤ cstarM5 S a n := by
    refine cstarM5_le (le_trans (Finset.card_le_card ?_) hspec)
    rintro ⟨q, k⟩ h
    rw [mem_ccset_iffM10 hS] at h ⊢
    refine ⟨h.1, h.2.1, le_trans h.2.2 ?_⟩
    exact Nat.mul_le_mul (Nat.mul_le_mul hmn le_rfl) (Nat.pow_le_pow_left hmn _)
  unfold boundM10
  exact Nat.mul_le_mul le_rfl
    (le_trans (Nat.pow_le_pow_right (by omega) hc) (Nat.pow_le_pow_left hmn _))

lemma bound_congrM10 {S : Finset ℕ} (a a' : ℕ → ℕ) (m : ℕ) (h : ∀ p ∈ S, a p = a' p) :
    boundM10 S a m = boundM10 S a' m := by
  have hD : Dprod S a = Dprod S a' := by
    unfold Dprod
    exact Finset.prod_congr rfl fun p hp => by rw [h p hp]
  have hC : ∀ N, CCset S a m N = CCset S a' m N := by
    intro N
    unfold CCset
    rw [hD]
    refine Finset.filter_congr fun x hx => ?_
    rw [h x.1 (Finset.mem_product.mp hx).1]
  unfold boundM10 cstarM5
  simp only [hD, hC]

/-- The exponent at the integer `m` with the weak inequality `m ≤ p^(2a+1)`. -/
noncomputable def aGeM10 (p m : ℕ) : ℕ := sInf {a : ℕ | m ≤ p ^ (2 * a + 1)}

/-- The exponent at the integer `m` with the strict inequality `m < p^(2a+1)`. -/
noncomputable def aGtM10 (p m : ℕ) : ℕ := sInf {a : ℕ | m < p ^ (2 * a + 1)}

lemma gt_nonemptyM10 {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : {a : ℕ | m < p ^ (2 * a + 1)}.Nonempty := by
  refine ⟨m, ?_⟩
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp m
  have h3 : p ^ m ≤ p ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  show m < p ^ (2 * m + 1)
  omega

lemma jump_valuesM10 {p : ℕ} (hp : 2 ≤ p) (m k : ℕ) (h : p ^ (2 * k + 1) = m) :
    aGeM10 p m = k ∧ aGtM10 p m = k + 1 := by
  have hlt : ∀ i j : ℕ, i < j → p ^ (2 * i + 1) < p ^ (2 * j + 1) := fun i j hij =>
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hle : ∀ i j : ℕ, i ≤ j → p ^ (2 * i + 1) ≤ p ^ (2 * j + 1) := fun i j hij =>
    Nat.pow_le_pow_right (by omega) (by omega)
  constructor
  · refine le_antisymm (Nat.sInf_le (show m ≤ p ^ (2 * k + 1) from h.ge)) ?_
    refine le_csInf ⟨k, show m ≤ p ^ (2 * k + 1) from h.ge⟩ fun j hj => ?_
    by_contra hc
    have h1 := hlt j k (by omega)
    have h2 : m ≤ p ^ (2 * j + 1) := hj
    omega
  · have hmem : m < p ^ (2 * (k + 1) + 1) := h ▸ hlt k (k + 1) (by omega)
    refine le_antisymm (Nat.sInf_le (show k + 1 ∈ {a : ℕ | m < p ^ (2 * a + 1)} from hmem)) ?_
    refine le_csInf ⟨k + 1, hmem⟩ fun j hj => ?_
    by_contra hc
    have h1 := hle j k (by omega)
    have h2 : m < p ^ (2 * j + 1) := hj
    omega

lemma ge_eq_gtM10 (p m : ℕ) (h : ∀ k : ℕ, p ^ (2 * k + 1) ≠ m) : aGeM10 p m = aGtM10 p m := by
  unfold aGeM10 aGtM10
  congr 1
  ext a
  show m ≤ p ^ (2 * a + 1) ↔ m < p ^ (2 * a + 1)
  have := h a
  omega

/-- At an integer `m` the weak and the strict exponents give the same bound. -/
lemma bound_ge_gtM10 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (m : ℕ)
    (hm2 : 2 ≤ m) :
    boundM10 S (fun p => aGtM10 p m) m = boundM10 S (fun p => aGeM10 p m) m := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  by_cases h : ∃ p ∈ S, ∃ k : ℕ, p ^ (2 * k + 1) = m
  · obtain ⟨p, hp, k, hk⟩ := h
    have hv := jump_valuesM10 (hS2 p hp) m k hk
    refine bound_jumpM10 hS2 hne _ _ m p hm2 hp ?_ ?_ ?_
    · show p ^ (2 * aGeM10 p m + 1) = m
      rw [hv.1]; exact hk
    · show aGtM10 p m = aGeM10 p m + 1
      rw [hv.1, hv.2]
    · intro q hq hqp
      refine (ge_eq_gtM10 q m fun j hj => hqp ?_).symm
      have hdvd : q ∣ p ^ (2 * k + 1) := by
        rw [hk, ← hj]
        exact dvd_pow_self q (by omega)
      exact (Nat.prime_dvd_prime_iff_eq (hS q hq) (hS p hp)).mp ((hS q hq).dvd_of_dvd_pow hdvd)
  · push Not at h
    exact bound_congrM10 _ _ m fun p hp => (ge_eq_gtM10 p m (h p hp)).symm

/-- The bound for the forced exponents of a real radius equals the bound at `m = ⌈1/δ⌉`. -/
lemma bound_thrM10 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {δ : ℝ}
    (hδ : 0 < δ) (hm2 : 2 ≤ ⌈1 / δ⌉₊) :
    boundM10 S (fun p => aThr p δ) ⌈1 / δ⌉₊
      = boundM10 S (fun p => aGtM10 p ⌈1 / δ⌉₊) ⌈1 / δ⌉₊ := by
  set m := ⌈1 / δ⌉₊ with hm
  have hcond : ∀ p ∈ S, ∀ a : ℕ,
      (1 / (p : ℝ) ^ (2 * a + 1) < δ ↔ 1 / δ < ((p ^ (2 * a + 1) : ℕ) : ℝ)) := by
    intro p hp a
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    rw [Nat.cast_pow]
    exact one_div_lt (pow_pos hp0 _) hδ
  by_cases hx : 1 / δ = (m : ℝ)
  · refine bound_congrM10 _ _ m fun p hp => ?_
    unfold aThr aGtM10
    congr 1
    ext a
    show 1 / (p : ℝ) ^ (2 * a + 1) < δ ↔ m < p ^ (2 * a + 1)
    rw [hcond p hp a, hx, Nat.cast_lt]
  · have hxm : 1 / δ < (m : ℝ) := lt_of_le_of_ne (Nat.le_ceil _) hx
    rw [bound_ge_gtM10 hS hne m hm2]
    refine bound_congrM10 _ _ m fun p hp => ?_
    unfold aThr aGeM10
    congr 1
    ext a
    show 1 / (p : ℝ) ^ (2 * a + 1) < δ ↔ m ≤ p ^ (2 * a + 1)
    rw [hcond p hp a]
    constructor
    · intro h
      exact Nat.ceil_le.mpr h.le
    · intro h
      exact lt_of_lt_of_le hxm (by exact_mod_cast h)

/-- **Monotonicity of the exact counting bound** with the forced exponents: `D_S(δ) m^(c*)`,
`m = ⌈1/δ⌉`, is nonincreasing as `δ` increases on `0 < δ ≤ 1/2`. -/
theorem boundM10_antitone {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty)
    {δ δ' : ℝ} (hδ : 0 < δ) (hle : δ ≤ δ') (hhalf : δ' ≤ 1 / 2) :
    boundM10 S (fun p => aThr p δ') ⌈1 / δ'⌉₊ ≤ boundM10 S (fun p => aThr p δ) ⌈1 / δ⌉₊ := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hδ' : 0 < δ' := lt_of_lt_of_le hδ hle
  have h2 : 2 ≤ ⌈1 / δ'⌉₊ := by
    have : (1 : ℝ) < 1 / δ' := by
      rw [lt_div_iff₀ hδ']; linarith
    have : 1 < ⌈1 / δ'⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast this)
    omega
  have hmm : ⌈1 / δ'⌉₊ ≤ ⌈1 / δ⌉₊ := Nat.ceil_mono (one_div_le_one_div_of_le hδ hle)
  rw [bound_thrM10 hS hne hδ' h2, bound_thrM10 hS hne hδ (le_trans h2 hmm)]
  generalize ⌈1 / δ⌉₊ = n at hmm ⊢
  induction n, hmm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    refine le_trans ih ?_
    have hk2 : 2 ≤ k := le_trans h2 hk
    have h1 := bound_mono_mM10 hS2 hne (fun p => aGtM10 p k) k (k + 1) hk2 (Nat.le_succ k)
    rw [bound_ge_gtM10 hS hne (k + 1) (by omega)]
    exact h1

/-- `2^L` with `η = log₂ m` is nondecreasing in `m`. -/
theorem two_pow_L_monoM10 (α : ℝ) (hα : 0 ≤ α) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    2 ^ ⌈α * (Real.logb 2 m) ^ 2 + α * Real.logb 2 m⌉₊
      ≤ 2 ^ ⌈α * (Real.logb 2 n) ^ 2 + α * Real.logb 2 n⌉₊ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have h2 : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) hm0 (by exact_mod_cast hmn)
  refine Nat.pow_le_pow_right (by norm_num) (Nat.ceil_mono ?_)
  have h3 : (Real.logb 2 (m : ℝ)) ^ 2 ≤ (Real.logb 2 (n : ℝ)) ^ 2 := pow_le_pow_left₀ h1 h2 2
  exact add_le_add (mul_le_mul_of_nonneg_left h3 hα) (mul_le_mul_of_nonneg_left h2 hα)

#print axioms iterate_cstarM10
#print axioms single_cstarM10
#print axioms bound_jumpM10
#print axioms boundM10_antitone
#print axioms two_pow_L_monoM10

end TVGPlus
end LeanCheck
