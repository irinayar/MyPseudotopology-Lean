import LeanCheck.TwoPrimesGolden

/-!
# Rigidity at a height linear in the target, from S-unit sums

`EvertseCor1` is Corollary 1 of J.-H. Evertse, *On sums of S-units and linear recurrences*,
Compositio Math. 53 (1984), 225-244 (p. 227).  It is a **hypothesis** here, not proved.

A real number whose two digit products are large has few visible levels, so it is close to two
rationals with sparse expansions, one in each base.  By `EvertseCor1` two such rationals cannot be
very close unless the number is near an integer.  The resulting height is `(1+δ) Y` for an accuracy
`exp (-Y)`, for all `Y` beyond a constant which the argument does not give effectively.

* `sum_form`: the finiteness statement turned into an inequality.
* `sparse_bound`: the inequality for a difference of sparse sums in two bases.
* `rigidity_sunit`: the rigidity step.
* `witness_of_density_sunit`, `witness_of_free_heights_sunit`: the consequences, the latter with
  `|k| ≤ C (1+|t|)^(1+δ)`.

The densities are hypotheses.
-/

namespace TwoPrimesSUnit

open Finset Real TwoPrimesEffective TwoPrimesWindows TwoPrimesFreeHeight TwoPrimesAdaptive
  TwoPrimesSharpFactor TwoPrimesSmoothing

/-! ## The cited theorem -/

/-- The largest modulus of a tuple of integers. -/
def height {m : ℕ} (x : Fin m → ℤ) : ℕ := univ.sup (fun i => (x i).natAbs)

/-- **Evertse's Corollary 1** (a hypothesis): for a finite set `S` of primes, `n ≥ 1`, `c > 0`
and `0 ≤ d < 1` only finitely many tuples of integers with sum zero, no vanishing proper subsum
and greatest common divisor one satisfy `∏ (|x_k| ∏_{r∈S} |x_k|_r) ≤ c ‖x‖^d`. -/
def EvertseCor1 (S : Finset ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c d : ℝ, 0 < c → 0 ≤ d → d < 1 →
    {x : Fin (n + 1) → ℤ | ∑ i, x i = 0 ∧
      (∀ I : Finset (Fin (n + 1)), I.Nonempty → I ≠ univ → ∑ i ∈ I, x i ≠ 0) ∧
      univ.gcd x = 1 ∧
      ∏ i, (|(x i : ℝ)| * ∏ r ∈ S, (padicNorm r (x i : ℚ) : ℝ))
        ≤ c * (height x : ℝ) ^ d}.Finite

/-! ## The part prime to two primes -/

/-- `|x| |x|_p |x|_q`. -/
noncomputable def nu (p q : ℕ) (x : ℤ) : ℝ :=
  |(x : ℝ)| * (padicNorm p (x : ℚ) : ℝ) * (padicNorm q (x : ℚ) : ℝ)

section Nu

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

lemma nu_mul (a b : ℤ) : nu p q (a * b) = nu p q a * nu p q b := by
  unfold nu
  push_cast
  rw [abs_mul, padicNorm.mul, padicNorm.mul]
  push_cast
  ring

lemma nu_nonneg (a : ℤ) : 0 ≤ nu p q a := by
  unfold nu
  have h1 : (0 : ℝ) ≤ (padicNorm p (a : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have h2 : (0 : ℝ) ≤ (padicNorm q (a : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  positivity

lemma nu_le_abs (a : ℤ) : nu p q a ≤ |(a : ℝ)| := by
  unfold nu
  have h1 : (padicNorm p (a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int a
  have h2 : (padicNorm q (a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int a
  have h3 : (0 : ℝ) ≤ (padicNorm p (a : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have h4 : (0 : ℝ) ≤ (padicNorm q (a : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have h5 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (a : ℝ))
  rw [mul_one] at h5
  exact le_trans (mul_le_mul h5 h2 h4 (abs_nonneg _)) (by rw [mul_one])

lemma nu_one : nu p q 1 = 1 := by
  unfold nu
  simp

lemma nu_pow (a : ℤ) (k : ℕ) : nu p q (a ^ k) = nu p q a ^ k := by
  induction k with
  | zero => simp [nu_one]
  | succ k ih => rw [pow_succ, nu_mul, ih, pow_succ]

lemma nu_left (hne : p ≠ q) : nu p q (p : ℤ) = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have := hp.out.pos
    positivity
  have h1 : padicNorm p ((p : ℤ) : ℚ) = (p : ℚ)⁻¹ := by
    rw [Int.cast_natCast]; exact padicNorm.padicNorm_p_of_prime
  have h2 : padicNorm q ((p : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]; exact padicNorm.padicNorm_of_prime_of_ne (Ne.symm hne)
  unfold nu
  rw [h1, h2]
  push_cast
  rw [Nat.abs_cast, mul_inv_cancel₀ hp0, one_mul]

lemma nu_right (hne : p ≠ q) : nu p q (q : ℤ) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have := hq.out.pos
    positivity
  have h1 : padicNorm q ((q : ℤ) : ℚ) = (q : ℚ)⁻¹ := by
    rw [Int.cast_natCast]; exact padicNorm.padicNorm_p_of_prime
  have h2 : padicNorm p ((q : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]; exact padicNorm.padicNorm_of_prime_of_ne hne
  unfold nu
  rw [h1, h2]
  push_cast
  rw [Nat.abs_cast, mul_one, mul_inv_cancel₀ hq0]

/-- Powers of `p` and `q` do not change `nu`. -/
lemma nu_units (hne : p ≠ q) (a : ℤ) (k l : ℕ) :
    nu p q (a * (p : ℤ) ^ k * (q : ℤ) ^ l) = nu p q a := by
  rw [nu_mul, nu_mul, nu_pow, nu_pow, nu_left hne, nu_right hne, one_pow, one_pow, mul_one,
    mul_one]

/-- A nonzero integer is `p^α q^β` times a rest prime to both, and `nu` is the rest. -/
lemma decomp (hne : p ≠ q) {a : ℤ} (ha : a ≠ 0) :
    ∃ α β : ℕ, ∃ r : ℤ, a = (p : ℤ) ^ α * (q : ℤ) ^ β * r ∧ nu p q a = |(r : ℝ)| ∧ r ≠ 0 := by
  have hpp := hp.out
  have hqp := hq.out
  have hfin : ∀ (l : ℕ), l.Prime → ∀ b : ℤ, b ≠ 0 → ∃ k : ℕ, ∃ c : ℤ,
      b = (l : ℤ) ^ k * c ∧ ¬ (l : ℤ) ∣ c := by
    intro l hl b hb
    have h : FiniteMultiplicity (l : ℤ) b := by
      refine Int.finiteMultiplicity_iff.mpr ⟨?_, hb⟩
      rw [Int.natAbs_natCast]
      exact hl.one_lt.ne'
    obtain ⟨c, hc, hnd⟩ := h.exists_eq_pow_mul_and_not_dvd
    exact ⟨_, c, hc, hnd⟩
  obtain ⟨α, b, hb, hbp⟩ := hfin p hpp a ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact ha (by rw [hb, mul_zero])
  obtain ⟨β, r, hr, hrq⟩ := hfin q hqp b hb0
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hr, mul_zero])
  have hrp : ¬ (p : ℤ) ∣ r := fun h => hbp (by rw [hr]; exact h.mul_left _)
  refine ⟨α, β, r, by rw [hb, hr, mul_assoc], ?_, hr0⟩
  have e : a = r * (p : ℤ) ^ α * (q : ℤ) ^ β := by rw [hb, hr]; ring
  rw [e, nu_units hne]
  have h1 : padicNorm p (r : ℚ) = 1 := (padicNorm.int_eq_one_iff r).mpr hrp
  have h2 : padicNorm q (r : ℚ) = 1 := (padicNorm.int_eq_one_iff r).mpr hrq
  unfold nu
  rw [h1, h2]
  push_cast
  ring

lemma one_le_nu (hne : p ≠ q) {a : ℤ} (ha : a ≠ 0) : 1 ≤ nu p q a := by
  obtain ⟨_, _, r, _, h, hr⟩ := decomp hne ha
  rw [h]
  have : (1 : ℤ) ≤ |r| := Int.one_le_abs hr
  exact_mod_cast this

/-- A power of `p` dividing `a` can be taken out of `nu a`. -/
lemma pow_left_mul_nu (hne : p ≠ q) {a : ℤ} {α : ℕ} (h : (p : ℤ) ^ α ∣ a) :
    (p : ℝ) ^ α * nu p q a ≤ |(a : ℝ)| := by
  obtain ⟨c, rfl⟩ := h
  have e : (p : ℤ) ^ α * c = c * (p : ℤ) ^ α * (q : ℤ) ^ 0 := by rw [pow_zero]; ring
  have h1 : nu p q ((p : ℤ) ^ α * c) = nu p q c := by rw [e, nu_units hne]
  rw [h1]
  push_cast
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ α)]
  exact mul_le_mul_of_nonneg_left (nu_le_abs c) (by positivity)

lemma pow_right_mul_nu (hne : p ≠ q) {a : ℤ} {β : ℕ} (h : (q : ℤ) ^ β ∣ a) :
    (q : ℝ) ^ β * nu p q a ≤ |(a : ℝ)| := by
  obtain ⟨c, rfl⟩ := h
  have e : (q : ℤ) ^ β * c = c * (p : ℤ) ^ 0 * (q : ℤ) ^ β := by rw [pow_zero]; ring
  have h1 : nu p q ((q : ℤ) ^ β * c) = nu p q c := by rw [e, nu_units hne]
  rw [h1]
  push_cast
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ β)]
  exact mul_le_mul_of_nonneg_left (nu_le_abs c) (by positivity)

/-! ## From finiteness to an inequality -/

/-- **The cited theorem as an inequality**, for at most `N` terms. -/
theorem sum_form (hne : p ≠ q) (hE : EvertseCor1 {p, q}) (N : ℕ) {d : ℝ} (hd : 0 < d)
    (hd1 : d < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type} (T : Finset ι) (x : ι → ℤ), 2 ≤ T.card → T.card ≤ N →
      ∑ i ∈ T, x i = 0 → (∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ i ∈ U, x i ≠ 0) → T.gcd x = 1 →
      ∀ i ∈ T, |(x i : ℝ)| ≤ C * (∏ k ∈ T, nu p q (x k)) ^ (1 / d) := by
  classical
  have hfin : ∀ n : ℕ, ∃ M : ℕ, 1 ≤ n → ∀ y : Fin (n + 1) → ℤ, ∑ i, y i = 0 →
      (∀ I : Finset (Fin (n + 1)), I.Nonempty → I ≠ univ → ∑ i ∈ I, y i ≠ 0) →
      univ.gcd y = 1 →
      ∏ i, (|(y i : ℝ)| * ∏ r ∈ ({p, q} : Finset ℕ), (padicNorm r (y i : ℚ) : ℝ))
        ≤ 1 * (height y : ℝ) ^ d → height y ≤ M := by
    intro n
    by_cases hn : 1 ≤ n
    · have h := hE n hn 1 d one_pos hd.le hd1
      refine ⟨h.toFinset.sup height, fun _ y h1 h2 h3 h4 => ?_⟩
      refine Finset.le_sup (f := height) ?_
      rw [Set.Finite.mem_toFinset]
      exact ⟨h1, h2, h3, h4⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose M hM using hfin
  refine ⟨1 + ∑ n ∈ range N, (M n : ℝ), ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ n ∈ range N, (M n : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  intro ι T x h2 hN hsum hsub hgcd i hi
  set C : ℝ := 1 + ∑ n ∈ range N, (M n : ℝ) with hC
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) ≤ ∑ n ∈ range N, (M n : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := ⟨T.card - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  set f : Fin (n + 1) ≃ T := (T.equivFinOfCardEq hn).symm with hf
  set y : Fin (n + 1) → ℤ := fun j => x (f j) with hy
  set emb : Fin (n + 1) ↪ ι := f.toEmbedding.trans (Function.Embedding.subtype _) with hemb
  have hmap : (univ : Finset (Fin (n + 1))).map emb = T := by
    ext a
    simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact (f j).2
    · intro ha
      refine ⟨f.symm ⟨a, ha⟩, ?_⟩
      show ((f (f.symm ⟨a, ha⟩) : T) : ι) = a
      rw [Equiv.apply_symm_apply]
  have hyx : ∀ I : Finset (Fin (n + 1)), ∑ j ∈ I, y j = ∑ a ∈ I.map emb, x a := by
    intro I
    rw [sum_map]
    rfl
  have h1 : ∑ j, y j = 0 := by rw [hyx, hmap, hsum]
  have h3 : ∀ I : Finset (Fin (n + 1)), I.Nonempty → I ≠ univ → ∑ j ∈ I, y j ≠ 0 := by
    intro I hI hIu
    rw [hyx]
    refine hsub _ ?_ (hI.map) ?_
    · rw [← hmap]
      exact map_subset_map.mpr (subset_univ _)
    · intro h
      rw [← hmap] at h
      exact hIu (map_injective emb h)
  have h4 : univ.gcd y = 1 := by
    have hdvd : univ.gcd y ∣ T.gcd x := by
      refine Finset.dvd_gcd (fun a ha => ?_)
      have : y (f.symm ⟨a, ha⟩) = x a := by
        show x (f (f.symm ⟨a, ha⟩)) = x a
        rw [Equiv.apply_symm_apply]
      rw [← this]
      exact Finset.gcd_dvd (mem_univ _)
    rw [hgcd] at hdvd
    rw [← Finset.normalize_gcd]
    exact normalize_eq_one.mpr (isUnit_of_dvd_one hdvd)
  have hne0 : ∀ a ∈ T, x a ≠ 0 := by
    intro a ha h0
    refine hsub {a} (singleton_subset_iff.mpr ha) (singleton_nonempty a) ?_ ?_
    · intro h
      have := congrArg Finset.card h
      rw [card_singleton] at this
      omega
    · rw [sum_singleton, h0]
  have hprod1 : 1 ≤ ∏ k ∈ T, nu p q (x k) := by
    refine le_trans (le_of_eq prod_const_one.symm) (prod_le_prod₀ (fun _ _ => zero_le_one) ?_)
    exact fun k hk => one_le_nu hne (hne0 k hk)
  have hprody : ∏ j, (|(y j : ℝ)| * ∏ r ∈ ({p, q} : Finset ℕ), (padicNorm r (y j : ℚ) : ℝ))
      = ∏ k ∈ T, nu p q (x k) := by
    conv_rhs => rw [← hmap]
    rw [prod_map]
    refine prod_congr rfl (fun j _ => ?_)
    rw [prod_pair hne, ← mul_assoc]
    rfl
  have hxh : |(x i : ℝ)| ≤ (height y : ℝ) := by
    have : y (f.symm ⟨i, hi⟩) = x i := by
      show x (f (f.symm ⟨i, hi⟩)) = x i
      rw [Equiv.apply_symm_apply]
    rw [← this]
    have h : (y (f.symm ⟨i, hi⟩)).natAbs ≤ height y :=
      Finset.le_sup (f := fun j => (y j).natAbs) (mem_univ _)
    have h' : ((y (f.symm ⟨i, hi⟩)).natAbs : ℝ) ≤ (height y : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_natAbs, Int.cast_abs] at h'
  have hpow1 : 1 ≤ (∏ k ∈ T, nu p q (x k)) ^ (1 / d) :=
    one_le_rpow hprod1 (by positivity)
  by_cases hex : ∏ j, (|(y j : ℝ)| * ∏ r ∈ ({p, q} : Finset ℕ), (padicNorm r (y j : ℚ) : ℝ))
      ≤ 1 * (height y : ℝ) ^ d
  · have hMn := hM n hn1 y h1 h3 h4 hex
    have hnN : n ∈ range N := by rw [mem_range]; omega
    have h5 : (height y : ℝ) ≤ C := by
      have h6 : (height y : ℝ) ≤ (M n : ℝ) := by exact_mod_cast hMn
      have h7 : (M n : ℝ) ≤ ∑ m ∈ range N, (M m : ℝ) :=
        single_le_sum (f := fun m => (M m : ℝ)) (fun _ _ => Nat.cast_nonneg _) hnN
      linarith
    exact le_trans (le_trans hxh h5) (le_mul_of_one_le_right (by linarith) hpow1)
  · rw [one_mul, hprody, not_le] at hex
    have h5 : (height y : ℝ) ≤ (∏ k ∈ T, nu p q (x k)) ^ (1 / d) := by
      have h6 := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hex.le
        (show (0 : ℝ) ≤ 1 / d by positivity)
      rwa [← rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hd.ne', rpow_one] at h6
    exact le_trans (le_trans hxh h5) (le_mul_of_one_le_left (by linarith) hC1)

end Nu

/-! ## Differences of sparse sums in two bases -/

/-- The sum of `a i / l^(e i)`. -/
def val {ι : Type} (l : ℕ) (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) : ℚ :=
  ∑ i ∈ s, (a i : ℚ) / (l : ℚ) ^ (e i)

/-- The numerator of `val` over the denominator `l^E`. -/
def num {ι : Type} (l : ℕ) (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) (E : ℕ) : ℤ :=
  ∑ i ∈ s, a i * (l : ℤ) ^ (E - e i)

lemma val_eq_num {ι : Type} {l : ℕ} (hl : 0 < l) (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ) {E : ℕ}
    (hE : ∀ i ∈ s, e i ≤ E) : val l s a e = (num l s a e E : ℚ) / (l : ℚ) ^ E := by
  have hl0 : (l : ℚ) ≠ 0 := by positivity
  unfold val num
  push_cast
  rw [sum_div]
  refine sum_congr rfl (fun i hi => ?_)
  rw [div_eq_div_iff (pow_ne_zero _ hl0) (pow_ne_zero _ hl0), mul_assoc, ← pow_add,
    Nat.sub_add_cancel (hE i hi)]

/-- A rational with a `p`-power and a `q`-power denominator is an integer. -/
lemma int_of_coprime {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) {m n : ℤ}
    {E F : ℕ} (h : (m : ℚ) / (p : ℚ) ^ E = (n : ℚ) / (q : ℚ) ^ F) :
    ∃ z : ℤ, (m : ℚ) / (p : ℚ) ^ E = z := by
  have hp0 : (p : ℚ) ^ E ≠ 0 := by positivity
  have hq0 : (q : ℚ) ^ F ≠ 0 := by positivity
  rw [div_eq_div_iff hp0 hq0] at h
  have h1 : m * (q : ℤ) ^ F = n * (p : ℤ) ^ E := by exact_mod_cast h
  have hcop : IsCoprime ((p : ℤ) ^ E) ((q : ℤ) ^ F) := (Nat.Coprime.isCoprime hpq).pow
  have h2 : (p : ℤ) ^ E ∣ m := hcop.dvd_of_dvd_mul_right ⟨n, by rw [h1]; ring⟩
  obtain ⟨z, hz⟩ := h2
  refine ⟨z, ?_⟩
  rw [hz]
  push_cast
  field_simp

/-- **The inequality for sparse sums.**  After dropping parts which are equal integers, either one
side is empty or the top denominators are bounded by the coefficients and the difference. -/
theorem sparse_bound {p q : ℕ} (hpp : p.Prime) (hqp : q.Prime) (hne : p ≠ q)
    (hE : EvertseCor1 {p, q}) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι κ : Type} (s : Finset ι) (t : Finset κ) (a : ι → ℤ) (b : κ → ℤ)
      (e : ι → ℕ) (f : κ → ℕ), s.card + t.card + 1 ≤ N → (∀ i ∈ s, a i ≠ 0) →
      (∀ j ∈ t, b j ≠ 0) → val p s a e ≠ val q t b f →
      ∃ s' ⊆ s, ∃ t' ⊆ t, ∃ z : ℤ, val p s' a e = val p s a e - z ∧
        val q t' b f = val q t b f - z ∧
        (s'.Nonempty → t'.Nonempty → ∃ i ∈ s', ∃ j ∈ t',
          max ((p : ℝ) ^ e i) ((q : ℝ) ^ f j)
            ≤ C * (|(val p s a e : ℝ) - (val q t b f : ℝ)| * (p : ℝ) ^ e i * (q : ℝ) ^ f j
              * (∏ i ∈ s', |(a i : ℝ)|) * ∏ j ∈ t', |(b j : ℝ)|) ^ (1 + ε)) := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact q.Prime := ⟨hqp⟩
  have hd : 0 < 1 / (1 + ε) := by positivity
  have hd1 : 1 / (1 + ε) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  obtain ⟨C, hC1, hC⟩ := sum_form (p := p) (q := q) hne hE N hd hd1
  have hexp : 1 / (1 / (1 + ε)) = 1 + ε := one_div_one_div _
  refine ⟨C, hC1, ?_⟩
  intro ι κ s t a b e f hN ha hb hdiff
  have hp0 : 0 < p := hpp.pos
  have hq0 : 0 < q := hqp.pos
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hne
  set δ : ℚ := val p s a e - val q t b f with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hdiff
  -- a smallest pair of subsets with the same difference
  set P : Finset (Finset ι × Finset κ) :=
    (s.powerset ×ˢ t.powerset).filter (fun w => val p w.1 a e - val q w.2 b f = δ) with hP
  have hPne : P.Nonempty := ⟨(s, t), by
    rw [hP, mem_filter, mem_product]
    exact ⟨⟨mem_powerset_self s, mem_powerset_self t⟩, rfl⟩⟩
  obtain ⟨w, hwP, hmin⟩ := exists_min_image P (fun w => w.1.card + w.2.card) hPne
  rw [hP, mem_filter, mem_product, mem_powerset, mem_powerset] at hwP
  obtain ⟨⟨hs', ht'⟩, hw⟩ := hwP
  set s' := w.1 with hs'def
  set t' := w.2 with ht'def
  have hminimal : ∀ u ⊆ s', ∀ v ⊆ t', u.Nonempty ∨ v.Nonempty →
      val p u a e ≠ val q v b f := by
    intro u hu v hv hne' huv
    have hmem : (s' \ u, t' \ v) ∈ P := by
      rw [hP, mem_filter, mem_product, mem_powerset, mem_powerset]
      refine ⟨⟨sdiff_subset.trans hs', sdiff_subset.trans ht'⟩, ?_⟩
      have h1 : val p (s' \ u) a e + val p u a e = val p s' a e := sum_sdiff hu
      have h2 : val q (t' \ v) b f + val q v b f = val q t' b f := sum_sdiff hv
      show val p (s' \ u) a e - val q (t' \ v) b f = δ
      rw [← hw, ← h1, ← h2, huv]; ring
    have hle := hmin _ hmem
    have c1 := card_sdiff_add_card_eq_card hu
    have c2 := card_sdiff_add_card_eq_card hv
    have hpos : 0 < u.card + v.card := by
      rcases hne' with h | h
      · have := card_pos.mpr h; omega
      · have := card_pos.mpr h; omega
    simp only at hle
    omega
  -- the complement is an integer
  set E0 : ℕ := (s \ s').sup e with hE0
  set F0 : ℕ := (t \ t').sup f with hF0
  have hc1 : val p (s \ s') a e + val p s' a e = val p s a e := sum_sdiff hs'
  have hc2 : val q (t \ t') b f + val q t' b f = val q t b f := sum_sdiff ht'
  have hceq : val p (s \ s') a e = val q (t \ t') b f := by
    have h := hw
    rw [hδ] at h
    linear_combination hc1 - hc2 - h
  have hz : ∃ z : ℤ, val p (s \ s') a e = z := by
    have h1 := val_eq_num hp0 (s \ s') a e (E := E0) (fun i hi => le_sup hi)
    have h2 := val_eq_num hq0 (t \ t') b f (E := F0) (fun i hi => le_sup hi)
    rw [h1]
    exact int_of_coprime hp0 hq0 hpq (by rw [← h1, ← h2]; exact hceq)
  obtain ⟨z, hz⟩ := hz
  have hA : val p s' a e = val p s a e - z := by rw [← hc1, hz]; ring
  have hB : val q t' b f = val q t b f - z := by rw [← hc2, ← hceq, hz]; ring
  refine ⟨s', hs', t', ht', z, hA, hB, fun hsne htne => ?_⟩
  obtain ⟨i1, hi1, hi1m⟩ := exists_max_image s' e hsne
  obtain ⟨j1, hj1, hj1m⟩ := exists_max_image t' f htne
  refine ⟨i1, hi1, j1, hj1, ?_⟩
  set E := e i1 with hEdef
  set F := f j1 with hFdef
  set Q : ℚ := (p : ℚ) ^ E * (q : ℚ) ^ F with hQ
  have hQ0 : Q ≠ 0 := by
    have h1 : (0 : ℚ) < p := by exact_mod_cast hp0
    have h2 : (0 : ℚ) < q := by exact_mod_cast hq0
    positivity
  set X : ι ⊕ κ → ℤ := Sum.elim (fun i => a i * (p : ℤ) ^ (E - e i) * (q : ℤ) ^ F)
    (fun j => -b j * (p : ℤ) ^ E * (q : ℤ) ^ (F - f j)) with hX
  set W : Finset (ι ⊕ κ) := s'.disjSum t' with hW
  set x : Option (ι ⊕ κ) → ℤ := fun o => o.elim (-∑ w ∈ W, X w) X with hx
  set T : Finset (Option (ι ⊕ κ)) := insertNone W with hT
  have hXcast : ∀ u ⊆ s', ∀ v ⊆ t', ((∑ w ∈ u.disjSum v, X w : ℤ) : ℚ)
      = Q * (val p u a e - val q v b f) := by
    intro u hu v hv
    rw [sum_disjSum, mul_sub]
    unfold val
    rw [mul_sum, mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
    push_cast
    congr 1
    · refine sum_congr rfl (fun i hi => ?_)
      have hle : e i ≤ E := hi1m i (hu hi)
      have h1 : (p : ℚ) ^ E = (p : ℚ) ^ (E - e i) * (p : ℚ) ^ (e i) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have h2 : (p : ℚ) ^ (e i) ≠ 0 := by
        have : (0 : ℚ) < p := by exact_mod_cast hp0
        positivity
      simp only [hX, Sum.elim_inl]
      push_cast
      rw [hQ, h1]
      field_simp
    · refine sum_congr rfl (fun j hj => ?_)
      have hle : f j ≤ F := hj1m j (hv hj)
      have h1 : (q : ℚ) ^ F = (q : ℚ) ^ (F - f j) * (q : ℚ) ^ (f j) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have h2 : (q : ℚ) ^ (f j) ≠ 0 := by
        have : (0 : ℚ) < q := by exact_mod_cast hq0
        positivity
      simp only [hX, Sum.elim_inr]
      push_cast
      rw [hQ, h1]
      field_simp
  have hsumT : ∑ o ∈ T, x o = 0 := by
    rw [hT, sum_insertNone]
    show -∑ w ∈ W, X w + ∑ w ∈ W, X w = 0
    ring
  have hxnone : ((x none : ℤ) : ℚ) = -(Q * δ) := by
    show ((-∑ w ∈ W, X w : ℤ) : ℚ) = _
    rw [Int.cast_neg, hW, hXcast s' (Subset.refl _) t' (Subset.refl _), hw]
  have hcardT : T.card = s'.card + t'.card + 1 := by
    rw [hT, card_insertNone, hW, card_disjSum]
  have h3T : 3 ≤ T.card := by
    have h1 := card_pos.mpr hsne
    have h2 := card_pos.mpr htne
    omega
  have hTN : T.card ≤ N := by
    have h1 := card_le_card hs'
    have h2 := card_le_card ht'
    omega
  -- no proper subsum vanishes
  have hnosub : ∀ U ⊆ T, U.Nonempty → none ∉ U → ∑ o ∈ U, x o ≠ 0 := by
    intro U hUT hUne hnone hzero
    set V : Finset (ι ⊕ κ) := U.eraseNone with hV
    have hUV : U = V.map Function.Embedding.some := by
      ext o
      cases o with
      | none => simp [hnone]
      | some w' => simp [hV, mem_eraseNone]
    have hVW : V ⊆ W := by
      intro w' hw'
      rw [hV, mem_eraseNone] at hw'
      have := hUT hw'
      rw [hT] at this
      exact some_mem_insertNone.mp this
    have hVne : V.Nonempty := by
      rw [hUV] at hUne
      exact map_nonempty.mp hUne
    have hsplit : V.toLeft.disjSum V.toRight = V := toLeft_disjSum_toRight
    have hu : V.toLeft ⊆ s' := by
      intro i hi
      rw [mem_toLeft] at hi
      have := hVW hi
      rwa [hW, inl_mem_disjSum] at this
    have hv : V.toRight ⊆ t' := by
      intro j hj
      rw [mem_toRight] at hj
      have := hVW hj
      rwa [hW, inr_mem_disjSum] at this
    have hsumV : ∑ w ∈ V, X w = 0 := by
      rw [← hzero]
      conv_rhs => rw [hUV]
      rw [sum_map]
      rfl
    have h := hXcast _ hu _ hv
    rw [hsplit, hsumV, Int.cast_zero] at h
    have h' : val p V.toLeft a e = val q V.toRight b f := by
      rcases mul_eq_zero.mp h.symm with h0 | h0
      · exact absurd h0 hQ0
      · exact sub_eq_zero.mp h0
    refine hminimal _ hu _ hv ?_ h'
    obtain ⟨w', hw'⟩ := hVne
    cases w' with
    | inl i => exact Or.inl ⟨i, mem_toLeft.mpr hw'⟩
    | inr j => exact Or.inr ⟨j, mem_toRight.mpr hw'⟩
  have hsubT : ∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ o ∈ U, x o ≠ 0 := by
    intro U hUT hUne hUneq hzero
    by_cases hnone : none ∈ U
    · refine hnosub (T \ U) sdiff_subset ?_ ?_ ?_
      · rw [sdiff_nonempty]
        exact fun h => hUneq (Subset.antisymm hUT h)
      · rw [mem_sdiff]
        exact fun h => h.2 hnone
      · have h := sum_sdiff (f := x) hUT
        rw [hzero, hsumT, add_zero] at h
        exact h
    · exact hnosub U hUT hUne hnone hzero
  -- divide by the common divisor
  have hTne : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨y, hy, hygcd⟩ := extract_gcd x hTne
  set g : ℤ := T.gcd x with hg
  have hg0 : g ≠ 0 := by
    intro h
    have h1 : (some (Sum.inl i1) : Option (ι ⊕ κ)) ∈ T := by
      rw [hT, some_mem_insertNone, hW, inl_mem_disjSum]; exact hi1
    have h2 := hy _ h1
    rw [h, zero_mul] at h2
    have h3 : x (some (Sum.inl i1)) ≠ 0 := by
      show a i1 * (p : ℤ) ^ (E - e i1) * (q : ℤ) ^ F ≠ 0
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
      have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq0.ne'
      exact mul_ne_zero (mul_ne_zero (ha i1 (hs' hi1)) (pow_ne_zero _ hpz)) (pow_ne_zero _ hqz)
    exact h3 h2
  have hxy : ∀ U ⊆ T, ∑ o ∈ U, x o = g * ∑ o ∈ U, y o := by
    intro U hU
    rw [mul_sum]
    exact sum_congr rfl (fun o ho => hy o (hU ho))
  have hysum : ∑ o ∈ T, y o = 0 := by
    have h := hxy T (Subset.refl _)
    rw [hsumT] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hg0
  have hysub : ∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ o ∈ U, y o ≠ 0 := by
    intro U hU h1 h2 h0
    exact hsubT U hU h1 h2 (by rw [hxy U hU, h0, mul_zero])
  have hbound := hC T y (by omega) hTN hysum hysub hygcd
  rw [hexp] at hbound
  -- the pieces of `g`
  obtain ⟨α, β, r, hgr, hnug, hr0⟩ := decomp (p := p) (q := q) hne hg0
  have hnu1 : 1 ≤ nu p q g := one_le_nu hne hg0
  have hpz : IsCoprime ((p : ℤ)) ((q : ℤ)) := Nat.Coprime.isCoprime hpq
  have hmemi : (some (Sum.inl i1) : Option (ι ⊕ κ)) ∈ T := by
    rw [hT, some_mem_insertNone, hW, inl_mem_disjSum]; exact hi1
  have hmemj : (some (Sum.inr j1) : Option (ι ⊕ κ)) ∈ T := by
    rw [hT, some_mem_insertNone, hW, inr_mem_disjSum]; exact hj1
  have hgdvd : ∀ o ∈ T, g ∣ x o := fun o ho => Finset.gcd_dvd ho
  have hαa : (p : ℤ) ^ α ∣ a i1 := by
    have h1 : (p : ℤ) ^ α ∣ x (some (Sum.inl i1)) :=
      dvd_trans ⟨(q : ℤ) ^ β * r, by rw [hgr]; ring⟩ (hgdvd _ hmemi)
    have h2 : x (some (Sum.inl i1)) = a i1 * (q : ℤ) ^ F := by
      show a i1 * (p : ℤ) ^ (E - e i1) * (q : ℤ) ^ F = _
      rw [show E - e i1 = 0 by omega, pow_zero, mul_one]
    rw [h2] at h1
    exact (hpz.pow (m := α) (n := F)).dvd_of_dvd_mul_right h1
  have hβb : (q : ℤ) ^ β ∣ b j1 := by
    have h1 : (q : ℤ) ^ β ∣ x (some (Sum.inr j1)) :=
      dvd_trans ⟨(p : ℤ) ^ α * r, by rw [hgr]; ring⟩ (hgdvd _ hmemj)
    have h2 : x (some (Sum.inr j1)) = -b j1 * (p : ℤ) ^ E := by
      show -b j1 * (p : ℤ) ^ E * (q : ℤ) ^ (F - f j1) = _
      rw [show F - f j1 = 0 by omega, pow_zero, mul_one]
    rw [h2] at h1
    have h3 := (hpz.symm.pow (m := β) (n := E)).dvd_of_dvd_mul_right h1
    exact (dvd_neg).mp h3
  have hAα := pow_left_mul_nu (p := p) (q := q) hne hαa
  have hBβ := pow_right_mul_nu (p := p) (q := q) hne hβb
  -- the product of the parts prime to `p q`
  have hnux : ∏ o ∈ T, nu p q (x o)
      = nu p q (x none) * ((∏ i ∈ s', nu p q (a i)) * ∏ j ∈ t', nu p q (b j)) := by
    rw [hT, prod_insertNone, hW, prod_disjSum]
    congr 1
    congr 1
    · refine prod_congr rfl (fun i _ => ?_)
      show nu p q (a i * (p : ℤ) ^ (E - e i) * (q : ℤ) ^ F) = _
      rw [nu_units hne]
    · refine prod_congr rfl (fun j _ => ?_)
      show nu p q (-b j * (p : ℤ) ^ E * (q : ℤ) ^ (F - f j)) = _
      rw [nu_units hne]
      simp [nu]
  set PX : ℝ := ∏ o ∈ T, nu p q (x o) with hPX
  set PY : ℝ := ∏ o ∈ T, nu p q (y o) with hPY
  have hPY0 : 0 ≤ PY := prod_nonneg (fun _ _ => nu_nonneg _)
  have hPXY : PX = nu p q g ^ T.card * PY := by
    rw [hPX, hPY, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl (fun o ho => by rw [hy o ho, nu_mul])
  have hPYX : PY ^ (1 + ε) * nu p q g ≤ PX ^ (1 + ε) := by
    rw [hPXY, mul_rpow (pow_nonneg (nu_nonneg _) _) hPY0, mul_comm (PY ^ (1 + ε))]
    refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hPY0 _)
    have h1 : nu p q g ≤ nu p q g ^ T.card := le_self_pow₀ hnu1 (by omega)
    exact le_trans h1 (self_le_rpow_of_one_le (one_le_pow₀ hnu1) (by linarith))
  -- the largest of the two denominators is one of the terms
  have hmax : max ((p : ℝ) ^ E) ((q : ℝ) ^ F) ≤ |(g : ℝ)| * (C * PY ^ (1 + ε)) := by
    have key : ∀ o ∈ T, |(x o : ℝ)| ≤ |(g : ℝ)| * (C * PY ^ (1 + ε)) := by
      intro o ho
      rw [hy o ho]
      push_cast
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound o ho) (abs_nonneg _)
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_lt.le
    refine max_le ?_ ?_
    · refine le_trans ?_ (key _ hmemj)
      have h2 : x (some (Sum.inr j1)) = -b j1 * (p : ℤ) ^ E := by
        show -b j1 * (p : ℤ) ^ E * (q : ℤ) ^ (F - f j1) = _
        rw [show F - f j1 = 0 by omega, pow_zero, mul_one]
      rw [h2]
      push_cast
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ E)]
      have h3 : (1 : ℝ) ≤ |(b j1 : ℝ)| := by
        exact_mod_cast Int.one_le_abs (hb j1 (ht' hj1))
      exact le_mul_of_one_le_left (by positivity) h3
    · refine le_trans ?_ (key _ hmemi)
      have h2 : x (some (Sum.inl i1)) = a i1 * (q : ℤ) ^ F := by
        show a i1 * (p : ℤ) ^ (E - e i1) * (q : ℤ) ^ F = _
        rw [show E - e i1 = 0 by omega, pow_zero, mul_one]
      rw [h2]
      push_cast
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ F)]
      have h3 : (1 : ℝ) ≤ |(a i1 : ℝ)| := by
        exact_mod_cast Int.one_le_abs (ha i1 (hs' hi1))
      exact le_mul_of_one_le_left (by positivity) h3
  have hgabs : |(g : ℝ)| = (p : ℝ) ^ α * (q : ℝ) ^ β * nu p q g := by
    rw [hnug]
    conv_lhs => rw [hgr]
    push_cast
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ α),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ β)]
  have hstep : max ((p : ℝ) ^ E) ((q : ℝ) ^ F)
      ≤ C * ((p : ℝ) ^ α * (q : ℝ) ^ β * PX ^ (1 + ε)) := by
    refine le_trans hmax ?_
    rw [hgabs]
    have h := mul_le_mul_of_nonneg_left hPYX
      (show (0 : ℝ) ≤ C * ((p : ℝ) ^ α * (q : ℝ) ^ β) by
        have : (0 : ℝ) ≤ C := by linarith
        positivity)
    refine le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))
  -- return to the coefficients
  have hxnoneR : |(x none : ℝ)|
      = |(val p s a e : ℝ) - (val q t b f : ℝ)| * (p : ℝ) ^ E * (q : ℝ) ^ F := by
    have h : ((x none : ℤ) : ℝ)
        = -(((p : ℝ) ^ E * (q : ℝ) ^ F) * ((val p s a e : ℝ) - (val q t b f : ℝ))) := by
      have h' := congrArg (fun r : ℚ => (r : ℝ)) hxnone
      simp only [hQ, hδ] at h'
      push_cast at h'
      exact h'
    rw [h, abs_neg, abs_mul, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (p : ℝ) ^ E * (q : ℝ) ^ F)]
    ring
  refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have h1ε : (0 : ℝ) ≤ 1 + ε := by linarith
  -- one factor with the power of the prime taken out
  have absorb : ∀ (P ν A : ℝ), 1 ≤ P → 0 ≤ ν → P * ν ≤ A → P * ν ^ (1 + ε) ≤ A ^ (1 + ε) := by
    intro P ν A hP hν h
    have h1 : P ≤ P ^ (1 + ε) := self_le_rpow_of_one_le hP (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 (rpow_nonneg hν (1 + ε))
    refine le_trans h2 ?_
    rw [← mul_rpow (by linarith) hν]
    exact rpow_le_rpow (mul_nonneg (by linarith) hν) h h1ε
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_lt.le
  have FA := absorb _ _ _ (one_le_pow₀ (n := α) hpR) (nu_nonneg (p := p) (q := q) (a i1)) hAα
  have FB := absorb _ _ _ (one_le_pow₀ (n := β) hqR) (nu_nonneg (p := p) (q := q) (b j1)) hBβ
  rw [hnux, ← mul_prod_erase s' (fun i => nu p q (a i)) hi1,
    ← mul_prod_erase t' (fun j => nu p q (b j)) hj1,
    ← mul_prod_erase s' (fun i => |(a i : ℝ)|) hi1,
    ← mul_prod_erase t' (fun j => |(b j : ℝ)|) hj1, ← hxnoneR]
  set RA : ℝ := ∏ i ∈ s'.erase i1, nu p q (a i) with hRA
  set RB : ℝ := ∏ j ∈ t'.erase j1, nu p q (b j) with hRB
  set SA : ℝ := ∏ i ∈ s'.erase i1, |(a i : ℝ)| with hSA
  set SB : ℝ := ∏ j ∈ t'.erase j1, |(b j : ℝ)| with hSB
  have hRA0 : 0 ≤ RA := prod_nonneg (fun _ _ => nu_nonneg _)
  have hRB0 : 0 ≤ RB := prod_nonneg (fun _ _ => nu_nonneg _)
  have hSA0 : 0 ≤ SA := prod_nonneg (fun _ _ => abs_nonneg _)
  have hSB0 : 0 ≤ SB := prod_nonneg (fun _ _ => abs_nonneg _)
  have hRAS : RA ≤ SA := prod_le_prod₀ (fun _ _ => nu_nonneg _) (fun i _ => nu_le_abs _)
  have hRBS : RB ≤ SB := prod_le_prod₀ (fun _ _ => nu_nonneg _) (fun i _ => nu_le_abs _)
  have hn0 : 0 ≤ nu p q (x none) := nu_nonneg _
  have hna : 0 ≤ nu p q (a i1) := nu_nonneg _
  have hnb : 0 ≤ nu p q (b j1) := nu_nonneg _
  have e1 : (p : ℝ) ^ α * (q : ℝ) ^ β
        * (nu p q (x none) * (nu p q (a i1) * RA * (nu p q (b j1) * RB))) ^ (1 + ε)
      = (nu p q (x none)) ^ (1 + ε) * RA ^ (1 + ε) * RB ^ (1 + ε)
        * ((p : ℝ) ^ α * nu p q (a i1) ^ (1 + ε))
        * ((q : ℝ) ^ β * nu p q (b j1) ^ (1 + ε)) := by
    rw [mul_rpow hn0 (by positivity), mul_rpow (by positivity) (by positivity),
      mul_rpow hna hRA0, mul_rpow hnb hRB0]
    ring
  have e2 : (|(x none : ℝ)| * (|(a i1 : ℝ)| * SA) * (|(b j1 : ℝ)| * SB)) ^ (1 + ε)
      = |(x none : ℝ)| ^ (1 + ε) * SA ^ (1 + ε) * SB ^ (1 + ε)
        * |(a i1 : ℝ)| ^ (1 + ε) * |(b j1 : ℝ)| ^ (1 + ε) := by
    rw [mul_rpow (by positivity) (by positivity), mul_rpow (abs_nonneg _) (by positivity),
      mul_rpow (abs_nonneg _) hSA0, mul_rpow (abs_nonneg _) hSB0]
    ring
  rw [e1, e2]
  have m1 := rpow_le_rpow hn0 (nu_le_abs (p := p) (q := q) (x none)) h1ε
  have m2 := rpow_le_rpow hRA0 hRAS h1ε
  have m3 := rpow_le_rpow hRB0 hRBS h1ε
  refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul m1 m2 ?_ ?_) m3 ?_ ?_) FA ?_ ?_) FB
    ?_ ?_
  all_goals positivity

/-! ## Digits of a real number -/

/-- The integer nearest to `l^(n²) θ`. -/
noncomputable def mm (l : ℕ) (θ : ℝ) (n : ℕ) : ℤ := round ((l : ℝ) ^ (n ^ 2) * θ)

/-- The digit of the level `n`. -/
noncomputable def kk (l : ℕ) (θ : ℝ) (n : ℕ) : ℤ := mm l θ (n + 1) - (l : ℤ) ^ (2 * n + 1) * mm l θ n

lemma pow_succ_sq (l : ℝ) (n : ℕ) : l ^ ((n + 1) ^ 2) = l ^ (2 * n + 1) * l ^ (n ^ 2) := by
  rw [← pow_add]; congr 1; ring

lemma telescope {l : ℕ} (hl : 0 < l) (θ : ℝ) {n0 M : ℕ} (h : n0 ≤ M) :
    (mm l θ M : ℚ) / (l : ℚ) ^ (M ^ 2)
      = (mm l θ n0 : ℚ) / (l : ℚ) ^ (n0 ^ 2)
        + ∑ n ∈ Ico n0 M, (kk l θ n : ℚ) / (l : ℚ) ^ ((n + 1) ^ 2) := by
  have hl0 : (l : ℚ) ≠ 0 := by positivity
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [sum_Ico_succ_top hM, ← add_assoc, ← ih]
    have hpow : (l : ℚ) ^ ((M + 1) ^ 2) = (l : ℚ) ^ (2 * M + 1) * (l : ℚ) ^ (M ^ 2) := by
      rw [← pow_add]; congr 1; ring
    unfold kk
    push_cast
    rw [hpow]
    field_simp
    ring

lemma mm_close (l : ℕ) (θ : ℝ) (n : ℕ) : |(l : ℝ) ^ (n ^ 2) * θ - mm l θ n| ≤ 1 / 2 :=
  abs_sub_round _

lemma abs_kk_le {l : ℕ} (hl : 2 ≤ l) (θ : ℝ) (n : ℕ) : |(kk l θ n : ℝ)| ≤ (l : ℝ) ^ (2 * n + 1) := by
  have h1 := mm_close l θ n
  have h2 := mm_close l θ (n + 1)
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hP : (2 : ℝ) ≤ (l : ℝ) ^ (2 * n + 1) :=
    le_trans hl' (le_self_pow₀ (by linarith) (by omega))
  have e : (kk l θ n : ℝ) = (l : ℝ) ^ (2 * n + 1) * ((l : ℝ) ^ (n ^ 2) * θ - mm l θ n)
      - ((l : ℝ) ^ ((n + 1) ^ 2) * θ - mm l θ (n + 1)) := by
    rw [pow_succ_sq]
    unfold kk
    push_cast
    ring
  rw [e]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ (2 * n + 1))]
  have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (l : ℝ) ^ (2 * n + 1) by positivity)
  linarith

/-- Two consecutive quiet levels have the digit zero. -/
lemma kk_quiet {l D n : ℕ} (hD : 12 ≤ D) (θ : ℝ) (h1 : 50 ≤ range' l D n)
    (h2 : 50 ≤ range' l D (n + 1))
    (q1 : |(l : ℝ) ^ (n ^ 2) * θ - mm l θ n| < 12 / 25 / (D : ℝ) / range' l D n)
    (q2 : |(l : ℝ) ^ ((n + 1) ^ 2) * θ - mm l θ (n + 1)|
      < 12 / 25 / (D : ℝ) / range' l D (n + 1)) : kk l θ n = 0 := by
  have hD' : (12 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  set σ : ℝ := 12 / 25 / (D : ℝ) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 / 25 := by
    rw [hσ, div_le_iff₀ hD0]; linarith
  have hσ2 : 2 * (D : ℝ) * σ = 24 / 25 := by
    rw [hσ]; field_simp; ring
  have hJr : (50 : ℝ) ≤ (range' l D n : ℝ) := by exact_mod_cast h1
  have hJr2 : (50 : ℝ) ≤ (range' l D (n + 1) : ℝ) := by exact_mod_cast h2
  have hJ0 : (0 : ℝ) < range' l D n := by linarith
  have hmul : l ^ (2 * n + 1) ≤ 2 * D * (range' l D n + 1) :=
    le_of_lt (Nat.lt_mul_div_succ (l ^ (2 * n + 1)) (show 0 < 2 * D by omega))
  have hmul' : (l : ℝ) ^ (2 * n + 1) ≤ 2 * D * (range' l D n + 1) := by exact_mod_cast hmul
  have hA : (l : ℝ) ^ (2 * n + 1) * (σ / range' l D n) ≤ 49 / 50 := by
    rw [mul_div_assoc', div_le_iff₀ hJ0]
    have h3 := mul_le_mul_of_nonneg_right hmul' hσ0.le
    have h4 : 2 * (D : ℝ) * (range' l D n + 1) * σ = (2 * D * σ) * (range' l D n + 1) := by ring
    rw [h4, hσ2] at h3
    linarith
  have hB : σ / range' l D (n + 1) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < range' l D (n + 1))]; linarith
  have e : (kk l θ n : ℝ) = (l : ℝ) ^ (2 * n + 1) * ((l : ℝ) ^ (n ^ 2) * θ - mm l θ n)
      - ((l : ℝ) ^ ((n + 1) ^ 2) * θ - mm l θ (n + 1)) := by
    rw [pow_succ_sq]
    unfold kk
    push_cast
    ring
  have hlt : |(kk l θ n : ℝ)| < 1 := by
    rw [e]
    refine lt_of_le_of_lt (abs_sub _ _) ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ (2 * n + 1))]
    have h3 := mul_le_mul_of_nonneg_left q1.le
      (show (0 : ℝ) ≤ (l : ℝ) ^ (2 * n + 1) by positivity)
    have h4 := lt_of_lt_of_le q2 hB
    linarith
  have h5 : |kk l θ n| < 1 := by exact_mod_cast hlt
  exact Int.abs_lt_one_iff.mp h5

/-- Beyond the level `50 D` every digit range is at least `50`. -/
lemma range_far {l D n : ℕ} (hl : 2 ≤ l) (hD : 1 ≤ D) (hn : 50 * D ≤ n) : 50 ≤ range' l D n := by
  have h1 : 100 * D ≤ l ^ (2 * n + 1) := by
    have h2 : 2 * n + 1 < 2 ^ (2 * n + 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ (2 * n + 1) ≤ l ^ (2 * n + 1) := Nat.pow_le_pow_left hl _
    omega
  unfold range'
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

/-! ## Rigidity -/

/-- The terms of the expansion of `mm M / l^(M²)` from the level `n0`. -/
noncomputable def coef (l : ℕ) (θ : ℝ) (n0 : ℕ) : Option ℕ → ℤ :=
  fun o => o.elim (mm l θ n0) (kk l θ)

def expo (n0 : ℕ) : Option ℕ → ℕ := fun o => o.elim (n0 ^ 2) (fun n => (n + 1) ^ 2)

noncomputable def terms (l : ℕ) (θ : ℝ) (n0 M : ℕ) : Finset (Option ℕ) :=
  (insertNone (Ico n0 M)).filter (fun o => coef l θ n0 o ≠ 0)

lemma val_terms {l : ℕ} (hl : 0 < l) (θ : ℝ) {n0 M : ℕ} (h : n0 ≤ M) :
    val l (terms l θ n0 M) (coef l θ n0) (expo n0)
      = (mm l θ M : ℚ) / (l : ℚ) ^ (M ^ 2) := by
  unfold val terms
  rw [sum_filter_of_ne, sum_insertNone, telescope hl θ h]
  · rfl
  · intro o _ ho hc
    exact ho (by rw [hc, Int.cast_zero, zero_div])

/-- The nonzero digits lie at visible levels or just below them. -/
lemma card_terms {l D : ℕ} (hl : 2 ≤ l) (hD : 12 ≤ D) (θ : ℝ) {M N : ℕ} (hMN : M < N) :
    (terms l θ (50 * D) M).card ≤ 2 * (marked'' l D N θ).card + 1 := by
  classical
  set n0 := 50 * D with hn0
  set Mk := marked'' l D N θ with hMk
  set Z := (Ico n0 M).filter (fun n => kk l θ n ≠ 0) with hZ
  have h1 : terms l θ n0 M ⊆ insertNone Z := by
    intro o ho
    rw [terms, mem_filter] at ho
    cases o with
    | none => exact none_mem_insertNone
    | some n =>
      rw [some_mem_insertNone, hZ, mem_filter]
      exact ⟨some_mem_insertNone.mp ho.1, ho.2⟩
  have h2 : Z ⊆ Mk ∪ Mk.image (fun m => m - 1) := by
    intro n hn
    rw [hZ, mem_filter, mem_Ico] at hn
    obtain ⟨⟨hn1, hn2⟩, hk⟩ := hn
    rw [mem_union, mem_image]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨c1, c2⟩ := hcon
    have r1 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n by omega)
    have r2 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n + 1 by omega)
    have quiet : ∀ m, m < N → 50 ≤ range' l D m → m ∉ Mk →
        |(l : ℝ) ^ (m ^ 2) * θ - mm l θ m| < 12 / 25 / (D : ℝ) / range' l D m := by
      intro m hm hr hnot
      by_contra h
      exact hnot (by
        rw [hMk, marked'', mem_filter, mem_range]
        exact ⟨hm, by omega, not_lt.mp h⟩)
    refine hk (kk_quiet hD θ r1 r2 (quiet n (by omega) r1 c1) (quiet (n + 1) (by omega) r2 ?_))
    intro h
    exact c2 ⟨n + 1, h, by omega⟩
  have h3 := card_le_card h1
  rw [card_insertNone] at h3
  have h4 := le_trans (card_le_card h2) (card_union_le _ _)
  have h5 : (Mk.image (fun m => m - 1)).card ≤ Mk.card := card_image_le
  omega

lemma marked_sub_int (l D N : ℕ) (θ : ℝ) (z : ℤ) : marked'' l D N (θ - z) = marked'' l D N θ := by
  unfold marked''
  refine filter_congr (fun n _ => ?_)
  have h : (l : ℝ) ^ (n ^ 2) * (θ - z) = (l : ℝ) ^ (n ^ 2) * θ - (((l : ℤ) ^ (n ^ 2) * z : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, round_sub_intCast]
  have h' : (l : ℝ) ^ (n ^ 2) * θ - (((l : ℤ) ^ (n ^ 2) * z : ℤ) : ℝ)
      - ((round ((l : ℝ) ^ (n ^ 2) * θ) - (l : ℤ) ^ (n ^ 2) * z : ℤ) : ℝ)
      = (l : ℝ) ^ (n ^ 2) * θ - (round ((l : ℝ) ^ (n ^ 2) * θ) : ℝ) := by
    push_cast; ring
  rw [h']

/-- A disjoint window counting: among `h` windows one holds at most one level. -/
lemma exists_window (Mp Mq : Finset ℕ) (B h : ℕ) (hB : Mp.card + Mq.card ≤ B) (hh : B < 2 * h)
    (sp sq : ℝ) (A : ℕ → ℝ) (hA : Monotone A) :
    ∃ i < h, (∀ n ∈ Mp, ¬ (A i < (n : ℝ) * sp ∧ (n : ℝ) * sp ≤ A (i + 1))) ∨
      (∀ n ∈ Mq, ¬ (A i < (n : ℝ) * sq ∧ (n : ℝ) * sq ≤ A (i + 1))) := by
  classical
  set W : (ℕ → ℝ) → Finset ℕ → ℕ → Finset ℕ := fun x M i =>
    M.filter (fun n => A i < x n ∧ x n ≤ A (i + 1)) with hW
  have disj : ∀ (x : ℕ → ℝ) (M : Finset ℕ), ∑ i ∈ range h, (W x M i).card ≤ M.card := by
    intro x M
    have hd : ((range h : Finset ℕ) : Set ℕ).PairwiseDisjoint (W x M) := by
      intro i _ j _ hij
      refine disjoint_left.mpr (fun n h1 h2 => hij ?_)
      rw [hW, mem_filter] at h1 h2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hA (show i + 1 ≤ j by omega)
        linarith [h1.2.2, h2.2.1]
      · have := hA (show j + 1 ≤ i by omega)
        linarith [h2.2.2, h1.2.1]
    rw [← card_biUnion hd]
    refine card_le_card (biUnion_subset.mpr (fun i _ => filter_subset _ _))
  by_contra hcon
  have hall : ∀ i ∈ range h, 2 ≤ (W (fun n => (n : ℝ) * sp) Mp i).card
      + (W (fun n => (n : ℝ) * sq) Mq i).card := by
    intro i hi
    rw [mem_range] at hi
    have h1 : ¬ ∀ n ∈ Mp, ¬ (A i < (n : ℝ) * sp ∧ (n : ℝ) * sp ≤ A (i + 1)) := fun h' =>
      hcon ⟨i, hi, Or.inl h'⟩
    have h2 : ¬ ∀ n ∈ Mq, ¬ (A i < (n : ℝ) * sq ∧ (n : ℝ) * sq ≤ A (i + 1)) := fun h' =>
      hcon ⟨i, hi, Or.inr h'⟩
    have one : ∀ (x : ℕ → ℝ) (M : Finset ℕ), (¬ ∀ n ∈ M, ¬ (A i < x n ∧ x n ≤ A (i + 1))) →
        1 ≤ (W x M i).card := by
      intro x M h'
      push Not at h'
      obtain ⟨n, hn, hh'⟩ := h'
      refine card_pos.mpr ⟨n, ?_⟩
      rw [hW, mem_filter]
      exact ⟨hn, hh'⟩
    have a1 := one _ _ h1
    have a2 := one _ _ h2
    omega
  have hsum := sum_le_sum hall
  rw [sum_const, card_range, sum_add_distrib, smul_eq_mul] at hsum
  have d1 := disj (fun n => (n : ℝ) * sp) Mp
  have d2 := disj (fun n => (n : ℝ) * sq) Mq
  omega

set_option maxHeartbeats 2000000 in
/-- **Rigidity from the cited theorem.**  For every `Y` beyond a constant, a number with at most
`B` visible levels below the height `(1+δ) Y` is within `exp (-Y) / 2` of an integer. -/
theorem rigidity_sunit {p q : ℕ} (hpp : p.Prime) (hqp : q.Prime) (hne : p ≠ q)
    (hE : EvertseCor1 {p, q}) {D : ℕ} (hD : 12 ≤ D) (B : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ Y1 : ℝ, ∀ Y : ℝ, Y1 ≤ Y → ∀ θ : ℝ,
      (marked'' p D (⌊sqrt ((1 + δ) * Y) / sqrt (log p)⌋₊ + 1) θ).card
        + (marked'' q D (⌊sqrt ((1 + δ) * Y) / sqrt (log q)⌋₊ + 1) θ).card ≤ B →
      ∃ z : ℤ, |θ - z| ≤ exp (-Y) / 2 := by
  classical
  have hp2 : 2 ≤ p := hpp.two_le
  have hq2 : 2 ≤ q := hqp.two_le
  set h : ℕ := B / 2 + 1 with hh
  have hh0 : (0 : ℝ) < h := by
    have : 0 < h := by omega
    exact_mod_cast this
  set ε : ℝ := δ / (8 * h) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨C, hC1, hC⟩ := sparse_bound hpp hqp hne hE (2 * B + 3) hε0
  set sp : ℝ := sqrt (log p) with hsp
  set sq : ℝ := sqrt (log q) with hsq
  have hsp0 : 0 < sp := sqrt_log_pos hp2
  have hsq0 : 0 < sq := sqrt_log_pos hq2
  set c : ℝ := max sp sq with hc
  have hc0 : 0 < c := lt_of_lt_of_le hsp0 (le_max_left _ _)
  set n0 : ℕ := 50 * D with hn0
  set G : ℝ := 2 * (n0 : ℝ) ^ 2 * c ^ 2 with hG
  set K0 : ℝ := 5 / 4 * (4 + 4 * B) * c + G + 2 * B * c ^ 2 + log C with hK0
  have hlogC : 0 ≤ log C := log_nonneg hC1
  have hK00 : 0 ≤ K0 := by
    have : (0 : ℝ) ≤ G := by positivity
    have : (0 : ℝ) ≤ 5 / 4 * (4 + 4 * (B : ℝ)) * c := by positivity
    have : (0 : ℝ) ≤ 2 * (B : ℝ) * c ^ 2 := by positivity
    rw [hK0]; linarith
  set u0 : ℝ := 1 + (n0 : ℝ) * c + c + 5 * c * h / δ + 16 * h / (5 * δ) * K0 with hu0
  have hu00 : 0 ≤ u0 := by positivity
  refine ⟨u0 ^ 2, fun Y hY θ0 hcount => ?_⟩
  have hY0 : 0 ≤ Y := le_trans (sq_nonneg _) hY
  set u : ℝ := sqrt Y with hu
  have hu2 : u ^ 2 = Y := sq_sqrt hY0
  have huu0 : u0 ≤ u := by
    have := sqrt_le_sqrt hY
    rwa [sqrt_sq hu00] at this
  have t1 : (0 : ℝ) ≤ (n0 : ℝ) * c := by positivity
  have t2 : (0 : ℝ) ≤ 5 * c * h / δ := by positivity
  have t3 : (0 : ℝ) ≤ 16 * h / (5 * δ) * K0 := mul_nonneg (by positivity) hK00
  have hu1 : 1 ≤ u := by rw [hu0] at huu0; linarith [hc0.le]
  have hun : (n0 : ℝ) * c ≤ u := by rw [hu0] at huu0; linarith [hc0.le]
  have huc : c ≤ u := by rw [hu0] at huu0; linarith
  have hu5 : 5 * c * h / δ ≤ u := by rw [hu0] at huu0; linarith [hc0.le]
  have hubig : 16 * h / (5 * δ) * K0 < u := by rw [hu0] at huu0; linarith [hc0.le]
  have hupos : 0 < u := by linarith
  -- move `θ` next to zero
  set θ : ℝ := θ0 - round θ0 with hθ
  have hθ2 : |θ| ≤ 1 / 2 := abs_sub_round _
  set Np : ℕ := ⌊sqrt ((1 + δ) * Y) / sp⌋₊ + 1 with hNp
  set Nq : ℕ := ⌊sqrt ((1 + δ) * Y) / sq⌋₊ + 1 with hNq
  set Mkp := marked'' p D Np θ with hMkp
  set Mkq := marked'' q D Nq θ with hMkq
  have hcount' : Mkp.card + Mkq.card ≤ B := by
    rw [hMkp, hMkq, hθ, marked_sub_int, marked_sub_int]
    exact hcount
  suffices hmain : ∃ z : ℤ, |θ - z| ≤ exp (-Y) / 2 by
    obtain ⟨z, hz⟩ := hmain
    refine ⟨z + round θ0, ?_⟩
    have : θ0 - ((z + round θ0 : ℤ) : ℝ) = θ - z := by rw [hθ]; push_cast; ring
    rw [this]; exact hz
  -- the windows
  set A : ℕ → ℝ := fun i => sqrt (Y * (1 + i * δ / (2 * h))) with hA
  have hAmono : Monotone A := by
    intro i j hij
    refine sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hY0)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    have h2 : (i : ℝ) * δ / (2 * h) ≤ j * δ / (2 * h) := by
      gcongr
    linarith
  obtain ⟨i, hih, hfree⟩ := exists_window Mkp Mkq B h hcount' (by omega) sp sq A hAmono
  set a : ℝ := A i with ha
  set b : ℝ := A (i + 1) with hb
  have ha2 : a ^ 2 = Y * (1 + i * δ / (2 * h)) := sq_sqrt (mul_nonneg hY0 (by positivity))
  have hb2 : b ^ 2 = Y * (1 + (i + 1 : ℕ) * δ / (2 * h)) :=
    sq_sqrt (mul_nonneg hY0 (by positivity))
  have hab2 : b ^ 2 - a ^ 2 = Y * δ / (2 * h) := by
    rw [ha2, hb2]; push_cast; ring
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have hb0 : 0 ≤ b := sqrt_nonneg _
  have hab : a ≤ b := hAmono (Nat.le_succ i)
  have hua : u ≤ a := by
    refine sqrt_le_sqrt ?_
    have : (0 : ℝ) ≤ i * δ / (2 * h) := by positivity
    exact le_mul_of_one_le_right hY0 (by linarith)
  have hi1 : ((i + 1 : ℕ) : ℝ) * δ / (2 * h) ≤ δ / 2 := by
    have h1 : ((i + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hih
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right h1 hδ.le
    have e : δ / 2 * (2 * (h : ℝ)) = (h : ℝ) * δ := by ring
    linarith
  have hbtop : b ^ 2 ≤ Y * (1 + δ / 2) := by
    rw [hb2]; exact mul_le_mul_of_nonneg_left (by linarith) hY0
  have hbu : b ≤ 5 / 4 * u := by
    have h1 : b ^ 2 ≤ (5 / 4 * u) ^ 2 := by
      have h2 : Y * (1 + δ / 2) ≤ Y * (25 / 16) :=
        mul_le_mul_of_nonneg_left (by linarith) hY0
      rw [mul_pow, hu2]; linarith
    exact (pow_le_pow_iff_left₀ hb0 (by positivity) two_ne_zero).mp h1
  have hbc : c ≤ b := le_trans huc (le_trans hua hab)
  have hbY : Y ≤ (b - c) ^ 2 := by
    have h1 : Y * δ / (2 * h) ≤ b ^ 2 - Y := by
      have h2 : b ^ 2 - Y = Y * (((i + 1 : ℕ) : ℝ) * δ / (2 * h)) := by rw [hb2]; ring
      have h3 : δ / (2 * h) ≤ ((i + 1 : ℕ) : ℝ) * δ / (2 * h) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
        exact le_mul_of_one_le_left hδ.le this
      rw [h2, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 hY0
    have h4 : 2 * b * c ≤ Y * δ / (2 * h) := by
      have h5 : 5 * c * h ≤ u * δ := by rwa [div_le_iff₀ hδ] at hu5
      have h6 : 2 * b * c ≤ 5 / 2 * u * c := by
        have := mul_le_mul_of_nonneg_right hbu hc0.le
        linarith
      refine le_trans h6 ?_
      rw [le_div_iff₀ (by positivity), ← hu2]
      have := mul_le_mul_of_nonneg_left h5 hupos.le
      have e1 : 5 / 2 * u * c * (2 * (h : ℝ)) = u * (5 * c * h) := by ring
      have e2 : u ^ 2 * δ = u * (u * δ) := by ring
      linarith
    have e3 : (b - c) ^ 2 = b ^ 2 - 2 * b * c + c ^ 2 := by ring
    have := sq_nonneg c
    linarith
  -- the precision levels
  set Lp : ℕ := ⌊b / sp⌋₊ with hLp
  set Lq : ℕ := ⌊b / sq⌋₊ with hLq
  have hlev : ∀ (l : ℕ), 2 ≤ l → sqrt (log l) ≤ c →
      (⌊b / sqrt (log l)⌋₊ : ℝ) * sqrt (log l) ≤ b ∧
      b - c ≤ (⌊b / sqrt (log l)⌋₊ : ℝ) * sqrt (log l) ∧ n0 ≤ ⌊b / sqrt (log l)⌋₊ ∧
      ⌊b / sqrt (log l)⌋₊ < ⌊sqrt ((1 + δ) * Y) / sqrt (log l)⌋₊ + 1 := by
    intro l hl hlc
    have hs := sqrt_log_pos hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := Nat.floor_le (div_nonneg hb0 hs.le)
      rwa [le_div_iff₀ hs] at this
    · have := Nat.lt_floor_add_one (b / sqrt (log l))
      rw [div_lt_iff₀ hs] at this
      have e : ((⌊b / sqrt (log l)⌋₊ : ℝ) + 1) * sqrt (log l)
          = (⌊b / sqrt (log l)⌋₊ : ℝ) * sqrt (log l) + sqrt (log l) := by ring
      linarith
    · refine Nat.le_floor ?_
      rw [le_div_iff₀ hs]
      have h1 := mul_le_mul_of_nonneg_left hlc (Nat.cast_nonneg (α := ℝ) n0)
      linarith
    · refine Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ hs.le))
      refine (le_sqrt hb0 (mul_nonneg (by linarith) hY0)).mpr (le_trans hbtop ?_)
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by linarith) hY0
  have hlp := hlev p hp2 (le_max_left _ _)
  have hlq := hlev q hq2 (le_max_right _ _)
  rw [← hsp, ← hLp, ← hNp] at hlp
  rw [← hsq, ← hLq, ← hNq] at hlq
  -- logarithms of the weights
  have hlogpow : ∀ (l : ℕ), 2 ≤ l → ∀ n : ℕ, log ((l : ℝ) ^ n) = n * sqrt (log l) ^ 2 := by
    intro l hl n
    rw [log_pow, sq_sqrt (TwoPrimesEffective.log_pos' hl).le]
  have happ : ∀ (l : ℕ), 2 ≤ l → ∀ L : ℕ, b - c ≤ (L : ℝ) * sqrt (log l) →
      |θ - (mm l θ L : ℝ) / (l : ℝ) ^ (L ^ 2)| ≤ exp (-(b - c) ^ 2) / 2 := by
    intro l hl L hL
    have hl0 : (0 : ℝ) < l := by
      have : 0 < l := by omega
      exact_mod_cast this
    have hP : (0 : ℝ) < (l : ℝ) ^ (L ^ 2) := pow_pos hl0 _
    have e1 : θ - (mm l θ L : ℝ) / (l : ℝ) ^ (L ^ 2)
        = ((l : ℝ) ^ (L ^ 2) * θ - mm l θ L) / (l : ℝ) ^ (L ^ 2) := by
      field_simp
    have hbig : exp ((b - c) ^ 2) ≤ (l : ℝ) ^ (L ^ 2) := by
      rw [← exp_log hP, hlogpow l hl]
      refine exp_le_exp.mpr ?_
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ b - c) hL 2
      rw [mul_pow] at this
      push_cast
      exact this
    rw [e1, abs_div, abs_of_pos hP, exp_neg]
    rw [div_le_iff₀ hP]
    have h2 : 1 ≤ (exp ((b - c) ^ 2))⁻¹ * (l : ℝ) ^ (L ^ 2) := by
      rw [inv_mul_eq_div, le_div_iff₀ (exp_pos _), one_mul]
      exact hbig
    have h3 := mm_close l θ L
    linarith
  have hfin : ∀ (l : ℕ), 2 ≤ l → ∀ L : ℕ, b - c ≤ (L : ℝ) * sqrt (log l) → ∀ z : ℤ,
      (mm l θ L : ℚ) / (l : ℚ) ^ (L ^ 2) = z → ∃ z : ℤ, |θ - z| ≤ exp (-Y) / 2 := by
    intro l hl L hL z hz
    refine ⟨z, ?_⟩
    have hzR : (mm l θ L : ℝ) / (l : ℝ) ^ (L ^ 2) = z := by
      have := congrArg (fun r : ℚ => (r : ℝ)) hz
      push_cast at this
      exact this
    have h1 := happ l hl L hL
    rw [hzR] at h1
    exact le_trans h1 (div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith)) zero_le_two)
  -- the two sparse rationals
  set s := terms p θ n0 Lp with hs
  set t := terms q θ n0 Lq with ht
  have hvp : val p s (coef p θ n0) (expo n0) = (mm p θ Lp : ℚ) / (p : ℚ) ^ (Lp ^ 2) :=
    val_terms (by omega) θ hlp.2.2.1
  have hvq : val q t (coef q θ n0) (expo n0) = (mm q θ Lq : ℚ) / (q : ℚ) ^ (Lq ^ 2) :=
    val_terms (by omega) θ hlq.2.2.1
  by_cases hsame : val p s (coef p θ n0) (expo n0) = val q t (coef q θ n0) (expo n0)
  · rw [hvp, hvq] at hsame
    obtain ⟨z, hz⟩ := int_of_coprime (by omega) (by omega)
      ((Nat.coprime_primes hpp hqp).mpr hne) hsame
    exact hfin p hp2 Lp hlp.2.1 z hz
  have cp : s.card ≤ 2 * Mkp.card + 1 := card_terms hp2 hD θ hlp.2.2.2
  have cq : t.card ≤ 2 * Mkq.card + 1 := card_terms hq2 hD θ hlq.2.2.2
  obtain ⟨s', hs', t', ht', z, hsum1, hsum2, hbound⟩ :=
    hC s t (coef p θ n0) (coef q θ n0) (expo n0) (expo n0) (by omega)
      (fun o ho => (mem_filter.mp ho).2) (fun o ho => (mem_filter.mp ho).2) hsame
  rcases s'.eq_empty_or_nonempty with hse | hsne
  · rw [hse] at hsum1
    have : val p s (coef p θ n0) (expo n0) = z := by
      have h0 : val p (∅ : Finset (Option ℕ)) (coef p θ n0) (expo n0) = 0 := sum_empty
      rw [h0] at hsum1
      linear_combination -hsum1
    exact hfin p hp2 Lp hlp.2.1 z (by rw [← hvp]; exact this)
  rcases t'.eq_empty_or_nonempty with hte | htne
  · rw [hte] at hsum2
    have : val q t (coef q θ n0) (expo n0) = z := by
      have h0 : val q (∅ : Finset (Option ℕ)) (coef q θ n0) (expo n0) = 0 := sum_empty
      rw [h0] at hsum2
      linear_combination -hsum2
    exact hfin q hq2 Lq hlq.2.1 z (by rw [← hvq]; exact this)
  -- both sides present: contradiction
  exfalso
  obtain ⟨i1, hi1, j1, hj1, hmax⟩ := hbound hsne htne
  set E := expo n0 i1 with hEd
  set F := expo n0 j1 with hFd
  set Δ : ℝ := |(val p s (coef p θ n0) (expo n0) : ℝ)
    - (val q t (coef q θ n0) (expo n0) : ℝ)| with hΔ
  have hΔ0 : 0 < Δ := by
    rw [hΔ, abs_pos, sub_ne_zero]
    exact_mod_cast hsame
  have hΔle : Δ ≤ exp (-(b - c) ^ 2) := by
    have h1 := happ p hp2 Lp hlp.2.1
    have h2 := happ q hq2 Lq hlq.2.1
    have e1 : (val p s (coef p θ n0) (expo n0) : ℝ) = (mm p θ Lp : ℝ) / (p : ℝ) ^ (Lp ^ 2) := by
      rw [hvp]; push_cast; rfl
    have e2 : (val q t (coef q θ n0) (expo n0) : ℝ) = (mm q θ Lq : ℝ) / (q : ℝ) ^ (Lq ^ 2) := by
      rw [hvq]; push_cast; rfl
    rw [hΔ, e1, e2]
    have h3 := abs_sub_le ((mm p θ Lp : ℝ) / (p : ℝ) ^ (Lp ^ 2)) θ
      ((mm q θ Lq : ℝ) / (q : ℝ) ^ (Lq ^ 2))
    rw [abs_sub_comm _ θ] at h3
    linarith
  -- sizes of the coefficients
  set H1 : ℝ := (n0 : ℝ) ^ 2 * c ^ 2 with hH1
  set H2 : ℝ := 2 * b * c + c ^ 2 with hH2
  have hH20 : 0 ≤ H2 := by positivity
  have hH10 : 0 ≤ H1 := by positivity
  have hcoef : ∀ (l : ℕ), 2 ≤ l → sqrt (log l) ≤ c → ∀ L : ℕ, (L : ℝ) * sqrt (log l) ≤ b →
      ∀ w : Finset (Option ℕ), w ⊆ terms l θ n0 L →
      ∏ o ∈ w, |(coef l θ n0 o : ℝ)| ≤ exp (H1 + (w.eraseNone.card : ℝ) * H2) := by
    intro l hl hlc L hL w hw
    have hl0 : (0 : ℝ) < l := by
      have : 0 < l := by omega
      exact_mod_cast this
    have hsl := sqrt_log_pos hl
    have hinit : |(coef l θ n0 none : ℝ)| ≤ exp H1 := by
      show |(mm l θ n0 : ℝ)| ≤ _
      have hP : (1 : ℝ) ≤ (l : ℝ) ^ (n0 ^ 2) :=
        one_le_pow₀ (by exact_mod_cast (show 1 ≤ l by omega))
      have h1 : |(mm l θ n0 : ℝ)| ≤ (l : ℝ) ^ (n0 ^ 2) := by
        have h2 := mm_close l θ n0
        have h3 : |(l : ℝ) ^ (n0 ^ 2) * θ| ≤ (l : ℝ) ^ (n0 ^ 2) / 2 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ (n0 ^ 2))]
          have := mul_le_mul_of_nonneg_left hθ2
            (show (0 : ℝ) ≤ (l : ℝ) ^ (n0 ^ 2) by positivity)
          linarith
        have h4 := abs_sub_le (mm l θ n0 : ℝ) ((l : ℝ) ^ (n0 ^ 2) * θ) 0
        rw [sub_zero, sub_zero, abs_sub_comm (mm l θ n0 : ℝ)] at h4
        linarith
      refine le_trans h1 ?_
      rw [← exp_log (pow_pos hl0 _), hlogpow l hl]
      refine exp_le_exp.mpr ?_
      rw [hH1]
      push_cast
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsl.le hlc 2) (by positivity)
    have hdig : ∀ n : ℕ, n < L → |(coef l θ n0 (some n) : ℝ)| ≤ exp H2 := by
      intro n hn
      show |(kk l θ n : ℝ)| ≤ _
      refine le_trans (abs_kk_le hl θ n) ?_
      rw [← exp_log (pow_pos hl0 _), hlogpow l hl]
      refine exp_le_exp.mpr ?_
      have h1 : (n : ℝ) * sqrt (log l) ≤ b := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ hsl.le) hL
        exact_mod_cast hn.le
      have h2 : (n : ℝ) * sqrt (log l) ^ 2 ≤ b * c := by
        have := mul_le_mul h1 hlc hsl.le hb0
        rw [pow_two, ← mul_assoc]; exact this
      have h3 : sqrt (log l) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hsl.le hlc 2
      rw [hH2]
      push_cast
      linarith
    have hsplit : ∏ o ∈ w, |(coef l θ n0 o : ℝ)|
        ≤ exp H1 * ∏ n ∈ w.eraseNone, |(coef l θ n0 (some n) : ℝ)| := by
      have hsub : w ⊆ insertNone w.eraseNone := by
        intro o ho
        cases o with
        | none => exact none_mem_insertNone
        | some n => exact some_mem_insertNone.mpr (mem_eraseNone.mpr ho)
      have hnz : ∀ n ∈ w.eraseNone, (1 : ℝ) ≤ |(coef l θ n0 (some n) : ℝ)| := by
        intro n hn
        have := (mem_filter.mp (hw (mem_eraseNone.mp hn))).2
        exact_mod_cast Int.one_le_abs this
      have hprodnn : 0 ≤ ∏ n ∈ w.eraseNone, |(coef l θ n0 (some n) : ℝ)| :=
        prod_nonneg (fun _ _ => abs_nonneg _)
      by_cases hn : none ∈ w
      · have e : w = insertNone w.eraseNone := by
          refine Subset.antisymm hsub (fun o ho => ?_)
          cases o with
          | none => exact hn
          | some n => exact mem_eraseNone.mp (some_mem_insertNone.mp ho)
        conv_lhs => rw [e]
        rw [prod_insertNone]
        exact mul_le_mul_of_nonneg_right hinit hprodnn
      · have e : w = w.eraseNone.map Function.Embedding.some := by
          ext o
          cases o with
          | none => simp [hn]
          | some n => simp [mem_eraseNone]
        conv_lhs => rw [e]
        rw [prod_map]
        exact le_mul_of_one_le_left hprodnn (one_le_exp hH10)
    refine le_trans hsplit ?_
    rw [exp_add, exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
    refine le_trans (prod_le_prod₀ (g := fun _ => exp H2) (fun _ _ => abs_nonneg _)
      (fun n hn => ?_)) (le_of_eq (prod_const _))
    have := (mem_filter.mp (hw (mem_eraseNone.mp hn))).1
    exact hdig n (mem_Ico.mp (some_mem_insertNone.mp this)).2
  have Pp := hcoef p hp2 (le_max_left _ _) Lp hlp.1 s' (hs' : s' ⊆ terms p θ n0 Lp)
  have Pq := hcoef q hq2 (le_max_right _ _) Lq hlq.1 t' (ht' : t' ⊆ terms q θ n0 Lq)
  have hdigits : (s'.eraseNone.card : ℝ) + (t'.eraseNone.card : ℝ) ≤ 2 * B := by
    have cnt : ∀ (l : ℕ), 2 ≤ l → ∀ L N : ℕ, L < N → ∀ w : Finset (Option ℕ),
        w ⊆ terms l θ n0 L → w.eraseNone.card ≤ 2 * (marked'' l D N θ).card := by
      intro l hl L N hLN w hw
      have h1 : insertNone w.eraseNone ⊆ insertNone (terms l θ n0 L).eraseNone := by
        intro o ho
        cases o with
        | none => exact none_mem_insertNone
        | some n =>
          rw [some_mem_insertNone, mem_eraseNone] at ho ⊢
          exact hw ho
      have h2 : (terms l θ n0 L).eraseNone ⊆
          (marked'' l D N θ) ∪ (marked'' l D N θ).image (fun m => m - 1) := by
        intro n hn
        rw [mem_eraseNone, terms, mem_filter, some_mem_insertNone, mem_Ico] at hn
        obtain ⟨⟨hn1, hn2⟩, hk⟩ := hn
        rw [mem_union, mem_image]
        by_contra hcon
        rw [not_or] at hcon
        obtain ⟨c1, c2⟩ := hcon
        have r1 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n by omega)
        have r2 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n + 1 by omega)
        have quiet : ∀ m, m < N → 50 ≤ range' l D m → m ∉ marked'' l D N θ →
            |(l : ℝ) ^ (m ^ 2) * θ - mm l θ m| < 12 / 25 / (D : ℝ) / range' l D m := by
          intro m hm hr hnot
          by_contra h'
          exact hnot (by
            rw [marked'', mem_filter, mem_range]
            exact ⟨hm, by omega, not_lt.mp h'⟩)
        refine hk (kk_quiet hD θ r1 r2 (quiet n (by omega) r1 c1)
          (quiet (n + 1) (by omega) r2 ?_))
        intro h'
        exact c2 ⟨n + 1, h', by omega⟩
      have h3 : w.eraseNone ⊆ (terms l θ n0 L).eraseNone := by
        intro n hn
        rw [mem_eraseNone] at hn ⊢
        exact hw hn
      have h4 := le_trans (card_le_card (h3.trans h2)) (card_union_le _ _)
      have h5 : ((marked'' l D N θ).image (fun m => m - 1)).card ≤ (marked'' l D N θ).card :=
        card_image_le
      omega
    have a1 := cnt p hp2 Lp Np hlp.2.2.2 s' hs'
    have a2 := cnt q hq2 Lq Nq hlq.2.2.2 t' ht'
    rw [← hMkp] at a1
    rw [← hMkq] at a2
    have : s'.eraseNone.card + t'.eraseNone.card ≤ 2 * B := by omega
    exact_mod_cast this
  set H : ℝ := G + 2 * B * H2 with hHd
  have hcoefs : (∏ o ∈ s', |(coef p θ n0 o : ℝ)|) * (∏ o ∈ t', |(coef q θ n0 o : ℝ)|)
      ≤ exp H := by
    refine le_trans (mul_le_mul Pp Pq (prod_nonneg (fun _ _ => abs_nonneg _)) (exp_pos _).le) ?_
    rw [← exp_add]
    refine exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right hdigits hH20
    rw [hHd, hG]
    linarith
  -- sizes of the exponents
  set EP : ℝ := log ((p : ℝ) ^ E) with hEP
  set FQ : ℝ := log ((q : ℝ) ^ F) with hFQ
  have hexple : ∀ (l : ℕ), 2 ≤ l → sqrt (log l) ≤ c → ∀ L : ℕ, (L : ℝ) * sqrt (log l) ≤ b →
      n0 ≤ L → ∀ o ∈ terms l θ n0 L, log ((l : ℝ) ^ (expo n0 o)) ≤ b ^ 2 := by
    intro l hl hlc L hL hn0L o ho
    have hsl := sqrt_log_pos hl
    rw [hlogpow l hl]
    have key : ∀ m : ℕ, m ≤ L → ((m ^ 2 : ℕ) : ℝ) * sqrt (log l) ^ 2 ≤ b ^ 2 := by
      intro m hm
      have h1 : (m : ℝ) * sqrt (log l) ≤ b := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ hsl.le) hL
        exact_mod_cast hm
      have := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg m) hsl.le) h1 2
      rw [mul_pow] at this
      push_cast
      exact this
    cases o with
    | none => exact key n0 hn0L
    | some n =>
      have := (mem_filter.mp ho).1
      exact key (n + 1) (mem_Ico.mp (some_mem_insertNone.mp this)).2
  have hEPb : EP ≤ b ^ 2 := hexple p hp2 (le_max_left _ _) Lp hlp.1 hlp.2.2.1 i1 (hs' hi1)
  have hFQb : FQ ≤ b ^ 2 := hexple q hq2 (le_max_right _ _) Lq hlq.1 hlq.2.2.1 j1 (ht' hj1)
  -- the free base has all its exponents below the window
  have hfreele : ∀ (l : ℕ), 2 ≤ l → sqrt (log l) ≤ c → ∀ L N : ℕ, (L : ℝ) * sqrt (log l) ≤ b →
      L < N → (∀ n ∈ marked'' l D N θ,
        ¬ (a < (n : ℝ) * sqrt (log l) ∧ (n : ℝ) * sqrt (log l) ≤ b)) →
      ∀ o ∈ terms l θ n0 L, log ((l : ℝ) ^ (expo n0 o)) ≤ (a + c) ^ 2 := by
    intro l hl hlc L N hL hLN hfr o ho
    have hsl := sqrt_log_pos hl
    rw [hlogpow l hl]
    have key : ∀ m : ℕ, (m : ℝ) * sqrt (log l) ≤ a + c →
        ((m ^ 2 : ℕ) : ℝ) * sqrt (log l) ^ 2 ≤ (a + c) ^ 2 := by
      intro m h1
      have := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg m) hsl.le) h1 2
      rw [mul_pow] at this
      push_cast
      exact this
    cases o with
    | none =>
      refine key n0 ?_
      have h1 := mul_le_mul_of_nonneg_left hlc (Nat.cast_nonneg (α := ℝ) n0)
      linarith [hc0.le]
    | some n =>
      obtain ⟨hmem, hk⟩ := mem_filter.mp ho
      obtain ⟨hn1, hn2⟩ := mem_Ico.mp (some_mem_insertNone.mp hmem)
      refine key (n + 1) ?_
      have hna : (n : ℝ) * sqrt (log l) ≤ a := by
        by_contra hcon
        rw [not_le] at hcon
        have r1 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n by omega)
        have r2 := range_far (l := l) (D := D) hl (by omega) (show 50 * D ≤ n + 1 by omega)
        have hle : ∀ m : ℕ, m ≤ L → (m : ℝ) * sqrt (log l) ≤ b := by
          intro m hm
          refine le_trans (mul_le_mul_of_nonneg_right ?_ hsl.le) hL
          exact_mod_cast hm
        have quiet : ∀ m, n ≤ m → m ≤ L → 50 ≤ range' l D m →
            |(l : ℝ) ^ (m ^ 2) * θ - mm l θ m| < 12 / 25 / (D : ℝ) / range' l D m := by
          intro m hnm hmL hr
          by_contra h'
          have hmk : m ∈ marked'' l D N θ := by
            rw [marked'', mem_filter, mem_range]
            exact ⟨by omega, by omega, not_lt.mp h'⟩
          refine hfr m hmk ⟨lt_of_lt_of_le hcon ?_, hle m hmL⟩
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) hsl.le
        exact hk (kk_quiet hD θ r1 r2 (quiet n le_rfl (by omega) r1)
          (quiet (n + 1) (Nat.le_succ n) (by omega) r2))
      push_cast
      linarith
  have hmin : min EP FQ ≤ (a + c) ^ 2 := by
    rcases hfree with hfr | hfr
    · exact le_trans (min_le_left _ _)
        (hfreele p hp2 (le_max_left _ _) Lp Np hlp.1 hlp.2.2.2 hfr i1 (hs' hi1))
    · exact le_trans (min_le_right _ _)
        (hfreele q hq2 (le_max_right _ _) Lq Nq hlq.1 hlq.2.2.2 hfr j1 (ht' hj1))
  -- the logarithm of the inequality
  have hpE : (0 : ℝ) < (p : ℝ) ^ E := by
    have : (0 : ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    positivity
  have hqF : (0 : ℝ) < (q : ℝ) ^ F := by
    have : (0 : ℝ) < q := by
      have : 0 < q := by omega
      exact_mod_cast this
    positivity
  have hZle : Δ * (p : ℝ) ^ E * (q : ℝ) ^ F * (∏ o ∈ s', |(coef p θ n0 o : ℝ)|)
      * (∏ o ∈ t', |(coef q θ n0 o : ℝ)|) ≤ exp (-(b - c) ^ 2 + EP + FQ + H) := by
    have e1 : exp (-(b - c) ^ 2 + EP + FQ + H)
        = exp (-(b - c) ^ 2) * (p : ℝ) ^ E * (q : ℝ) ^ F * exp H := by
      rw [exp_add, exp_add, exp_add, hEP, hFQ, exp_log hpE, exp_log hqF]
    rw [e1, mul_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΔle hpE.le)
      hqF.le) hcoefs ?_ ?_
    · exact mul_nonneg (prod_nonneg (fun _ _ => abs_nonneg _))
        (prod_nonneg (fun _ _ => abs_nonneg _))
    · exact mul_nonneg (mul_nonneg (exp_pos _).le hpE.le) hqF.le
  have hZ0 : 0 ≤ Δ * (p : ℝ) ^ E * (q : ℝ) ^ F * (∏ o ∈ s', |(coef p θ n0 o : ℝ)|)
      * (∏ o ∈ t', |(coef q θ n0 o : ℝ)|) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hΔ0.le hpE.le) hqF.le) ?_) ?_
    · exact prod_nonneg (fun _ _ => abs_nonneg _)
    · exact prod_nonneg (fun _ _ => abs_nonneg _)
  have hfinal : max ((p : ℝ) ^ E) ((q : ℝ) ^ F)
      ≤ exp (log C + (-(b - c) ^ 2 + EP + FQ + H) * (1 + ε)) := by
    rw [exp_add, exp_log (by linarith : (0 : ℝ) < C), exp_mul]
    exact le_trans hmax (mul_le_mul_of_nonneg_left
      (rpow_le_rpow hZ0 hZle (by linarith)) (by linarith))
  have hlogmax : max EP FQ ≤ log C + (-(b - c) ^ 2 + EP + FQ + H) * (1 + ε) := by
    refine max_le ?_ ?_
    · have := log_le_log hpE (le_trans (le_max_left _ _) hfinal)
      rwa [log_exp] at this
    · have := log_le_log hqF (le_trans (le_max_right _ _) hfinal)
      rwa [log_exp] at this
  -- the contradiction
  have hsumEF : EP + FQ = min EP FQ + max EP FQ := (min_add_max _ _).symm
  have hmaxb : max EP FQ ≤ b ^ 2 := max_le hEPb hFQb
  have hkey : (b - c) ^ 2 - (a + c) ^ 2 - H ≤ log C + ε * b ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have h0 : 0 ≤ log C + ε * b ^ 2 := add_nonneg hlogC (mul_nonneg hε0.le (sq_nonneg _))
    set W : ℝ := (b - c) ^ 2 - min EP FQ - H with hW
    have hWc : log C + ε * b ^ 2 < W := by rw [hW]; linarith
    have h1 : -(b - c) ^ 2 + EP + FQ + H = max EP FQ - W := by rw [hW]; linarith
    rw [h1] at hlogmax
    have h2 := mul_le_mul_of_nonneg_left hmaxb hε0.le
    have h3 : 0 ≤ ε * W := mul_nonneg hε0.le (le_trans h0 hWc.le)
    have e : (max EP FQ - W) * (1 + ε)
        = max EP FQ - W + ε * max EP FQ - ε * W := by ring
    linarith
  have hHbound : H = G + 2 * B * (2 * b * c + c ^ 2) := by rw [hHd, hH2]
  have hgap : Y * δ / (2 * h) ≤ (4 + 4 * B) * b * c + G + 2 * B * c ^ 2 + log C + ε * b ^ 2 := by
    rw [← hab2]
    have h1 : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab hc0.le
    rw [hHbound] at hkey
    have e1 : (b - c) ^ 2 - (a + c) ^ 2 = b ^ 2 - a ^ 2 - 2 * (b * c) - 2 * (a * c) := by ring
    have e2 : G + 2 * (B : ℝ) * (2 * b * c + c ^ 2)
        = G + 4 * ((B : ℝ) * (b * c)) + 2 * (B : ℝ) * c ^ 2 := by ring
    have e3 : (4 + 4 * (B : ℝ)) * b * c = 4 * (b * c) + 4 * ((B : ℝ) * (b * c)) := by ring
    linarith
  have hεb : ε * b ^ 2 ≤ 3 / 16 * (Y * δ / h) := by
    have h1 : b ^ 2 ≤ Y * (3 / 2) :=
      le_trans hbtop (mul_le_mul_of_nonneg_left (by linarith) hY0)
    have h2 := mul_le_mul_of_nonneg_left h1 hε0.le
    refine le_trans h2 (le_of_eq ?_)
    rw [hε]; field_simp; ring
  have hlin : (4 + 4 * (B : ℝ)) * b * c + G + 2 * B * c ^ 2 + log C ≤ u * K0 := by
    have h1 : (4 + 4 * (B : ℝ)) * b * c ≤ u * (5 / 4 * (4 + 4 * B) * c) := by
      have := mul_le_mul_of_nonneg_left hbu (show (0 : ℝ) ≤ (4 + 4 * B) * c by positivity)
      have e1 : (4 + 4 * (B : ℝ)) * b * c = (4 + 4 * (B : ℝ)) * c * b := by ring
      have e2 : u * (5 / 4 * (4 + 4 * (B : ℝ)) * c)
          = (4 + 4 * (B : ℝ)) * c * (5 / 4 * u) := by ring
      linarith
    have h2 : G + 2 * B * c ^ 2 + log C ≤ u * (G + 2 * B * c ^ 2 + log C) := by
      refine le_mul_of_one_le_left ?_ hu1
      have : (0 : ℝ) ≤ G := by positivity
      have : (0 : ℝ) ≤ 2 * (B : ℝ) * c ^ 2 := by positivity
      linarith
    rw [hK0]
    linarith
  have hstrict : u * K0 < 5 / 16 * (Y * δ / h) := by
    have h1 : 16 * (h : ℝ) * K0 < u * (5 * δ) := by
      have := hubig
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at this
      exact this
    have h2 := mul_lt_mul_of_pos_left h1 hupos
    have e : 5 / 16 * (Y * δ / h) = u * (u * (5 * δ)) / (16 * h) := by
      rw [← hu2]; field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    have e3 : u * K0 * (16 * (h : ℝ)) = u * (16 * (h : ℝ) * K0) := by ring
    linarith
  have hsplitY : Y * δ / (2 * h) = 1 / 2 * (Y * δ / h) := by field_simp
  rw [hsplitY] at hgap
  linarith

/-! ## The density theorem with any rigidity step -/

/-- **Density to witnesses**, for any numbers of levels which fit below `X / 64` and satisfy
rigidity at the accuracy `exp (-Y)`. -/
theorem witness_of_density_rigid {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hD : 1 ≤ D)
    {K s Y : ℝ} (hK : 1 ≤ K) {Np Nq X : ℕ}
    (hfitp : (p : ℝ) ^ (Np ^ 2) ≤ X / 64) (hfitq : (q : ℝ) ^ (Nq ^ 2) ≤ X / 64)
    (hX100 : 100 ≤ X)
    (hrig : ∀ θ : ℝ, sqrt (1 / (17 * K)) ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| →
      ∃ z : ℤ, |θ - z| ≤ exp (-Y) / 2)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp Y / 32) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hKpos : (0 : ℝ) < K := by linarith
  have hX100r : (100 : ℝ) ≤ X := by exact_mod_cast hX100
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hVpos : (0 : ℝ) < V.card := by
    by_contra h
    have h0 : (V.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hV
    linarith
  set I' : Finset (ℤ × Idx p D Np × Idx q D Nq) :=
    V ×ˢ (idx p D Np ×ˢ idx q D Nq) with hI'
  set g : ℤ × Idx p D Np × Idx q D Nq → ℤ :=
    fun i => i.1 + val' p i.2.1 - val' q i.2.2 with hg
  have hVne : V.Nonempty := card_pos.mp (by exact_mod_cast hVpos)
  have hIne : I'.Nonempty :=
    hVne.product ((idx_nonempty p D Np).product (idx_nonempty q D Nq))
  have hcard : (I'.card : ℝ)
      = V.card * ((idx p D Np).card * (idx q D Nq).card) := by
    rw [hI', card_product, card_product]; push_cast; ring
  have hmem : ∀ i ∈ I', i.1 ∈ V ∧ i.2.1 ∈ idx p D Np ∧ i.2.2 ∈ idx q D Nq := by
    intro i hi'
    rw [hI', mem_product, mem_product] at hi'
    exact ⟨hi'.1, hi'.2.1, hi'.2.2⟩
  have svp : ∀ j ∈ idx p D Np, 64 * |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hp hD hj) hfitp
    have h2 : 64 * |(val' p j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have svq : ∀ j ∈ idx q D Nq, 64 * |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hq hD hj) hfitq
    have h2 : 64 * |(val' q j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have hvp : ∀ j ∈ idx p D Np, |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have := svp j hj
    have := abs_nonneg (val' p j)
    omega
  have hvq : ∀ j ∈ idx q D Nq, |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have := svq j hj
    have := abs_nonneg (val' q j)
    omega
  set M : ℕ := 2 * X + X / 32 with hM
  have hR : ∀ i ∈ I', |g i| ≤ ((M : ℕ) : ℤ) := by
    intro i hi'
    obtain ⟨h1, h2, h3⟩ := hmem i hi'
    have e1 := hdiff _ h1
    have a1 := haX _ h1
    have a2 := hbX _ h1
    have a3 := svp _ h2
    have a4 := svq _ h3
    have a5 : |val' p i.2.1| + |val' q i.2.2| ≤ ((X / 32 : ℕ) : ℤ) := by
      have := abs_nonneg (val' p i.2.1)
      have := abs_nonneg (val' q i.2.2)
      omega
    have a6 := le_abs_self (val' p i.2.1)
    have a7 := neg_le_abs (val' p i.2.1)
    have a8 := le_abs_self (val' q i.2.2)
    have a9 := neg_le_abs (val' q i.2.2)
    rw [abs_le] at a1 a2
    rw [abs_le]; simp only [hg, hM]; push_cast at a5 ⊢; omega
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
      ≤ (1 / V.card) * (I'.card : ℝ) ^ 2 := by
    set W := idx p D Np ×ˢ idx q D Nq with hW
    have h1 : ((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card ≤ (I' ×ˢ W).card := by
      refine card_le_card_of_injOn (fun x => (x.1, x.2.2)) ?_ ?_
      · intro x hx
        rw [mem_coe, mem_filter, mem_product] at hx
        rw [mem_coe, mem_product]
        refine ⟨hx.1.1, ?_⟩
        have := hx.1.2
        rw [hI', mem_product] at this
        exact this.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨e1, e2⟩ := hxy
        have e3 : x.2.1 = y.2.1 := by
          have gx := hx.2
          have gy := hy.2
          have e4 : g x.2 = g y.2 := by rw [e1] at gx; omega
          simp only [hg, e2] at e4
          omega
        exact Prod.ext e1 (Prod.ext e3 e2)
    have h2 : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
        ≤ (I'.card : ℝ) * ((idx p D Np).card * (idx q D Nq).card) := by
      have h3 : (I' ×ˢ W).card = I'.card * ((idx p D Np).card * (idx q D Nq).card) := by
        rw [card_product I' W, hW, card_product (idx p D Np)]
      exact_mod_cast le_trans h1 (le_of_eq h3)
    refine le_trans h2 (le_of_eq ?_)
    rw [hcard]; field_simp
  have hsupp : ((I' ×ˢ I').image (fun x => g x.1 - g x.2)).card ≤ 4 * M + 1 := by
    have hsub : (I' ×ˢ I').image (fun x => g x.1 - g x.2)
        ⊆ Icc (-(2 * (M : ℤ))) (2 * (M : ℤ)) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx', rfl⟩ := hy
      rw [mem_product] at hx'
      have a1 := hR _ hx'.1
      have a2 := hR _ hx'.2
      rw [abs_le] at a1 a2
      rw [mem_Icc]; omega
    refine le_trans (card_le_card hsub) ?_
    rw [Int.card_Icc]; omega
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (17 * K)) with hη
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (17 * K) := sq_sqrt (by positivity)
  have hfactor : ∀ θ : ℝ, S I' g θ = (∑ v ∈ V, e ((v : ℝ) * θ))
      * ((∑ j ∈ idx p D Np, e ((val' p j : ℝ) * θ))
        * (∑ j ∈ idx q D Nq, e ((val' q j : ℝ) * (-θ)))) := by
    intro θ
    rw [S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun v _ => ?_)
    rw [sum_product, sum_mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    rw [← e_add, ← e_add]
    congr 1; simp only [hg]; push_cast; ring
  have heven : ∀ θ : ℝ, prodPhi q D Nq (-θ) = prodPhi q D Nq θ := by
    intro θ
    unfold prodPhi
    refine prod_congr rfl (fun n _ => ?_)
    rw [mul_neg, phi_neg]
  have hle1 : ∀ (r N : ℕ) (θ : ℝ), |prodPhi r D N θ| ≤ 1 := by
    intro r N θ
    unfold prodPhi
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_phi_le_one _ _)
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 99 / 100 ≤ Real.cos (2 * π * (t * θ)) := by
    intro θ hθ
    have hnorm : ‖S I' g θ‖ ≤ (I'.card : ℝ)
        * (|prodPhi p D Np θ| * |prodPhi q D Nq θ|) := by
      rw [hfactor, norm_mul, norm_mul, sum_idx, sum_idx, heven,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      have hVs : ‖∑ v ∈ V, e ((v : ℝ) * θ)‖ ≤ (V.card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ v ∈ V, ‖e ((v : ℝ) * θ)‖ = 1 := by
          intro v _
          unfold e
          exact Complex.norm_exp_ofReal_mul_I _
        rw [sum_congr rfl this]; simp
      refine le_trans (mul_le_mul_of_nonneg_right hVs (by positivity)) (le_of_eq ?_)
      rw [hcard]; ring
    have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hIne
    have hboth : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    obtain ⟨z, hz⟩ := hrig θ hboth
    set y : ℝ := t * (θ - z) with hy
    have hyabs : |y| ≤ 1 / 64 := by
      rw [hy, abs_mul]
      have h3 := mul_le_mul ht hz (abs_nonneg _) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      have e1 : exp Y * exp (-Y) = 1 := by
        rw [← exp_add, add_neg_cancel, exp_zero]
      rw [div_mul_div_comm, e1]; norm_num
    have hcos : Real.cos (2 * π * (t * θ)) = Real.cos (2 * π * y) := by
      have : 2 * π * ((t : ℝ) * θ) = 2 * π * y + ((t * z : ℤ) : ℝ) * (2 * π) := by
        rw [hy]; push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h6 : |2 * π * y| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have := mul_le_mul_of_nonneg_left hyabs (show (0 : ℝ) ≤ 2 * π by positivity)
      have hpi : π < 4 := pi_lt_four
      linarith
    have h7 : (2 * π * y) ^ 2 ≤ (1 / 8) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    linarith [show ((1 : ℝ) / 8) ^ 2 = 1 / 64 by norm_num]
  have hnum : (1 + 99 / 100) * η ^ 2 * (1 / (V.card : ℝ))
      < (99 / 100) / ((4 * M + 1 : ℕ) : ℝ) := by
    rw [hη2]
    have h1 : 1 / (V.card : ℝ) ≤ K / X := by
      rw [div_le_div_iff₀ hVpos hXpos]; linarith
    have h2 : (1 + 99 / 100) * (1 / (17 * K)) * (1 / (V.card : ℝ))
        ≤ (1 + 99 / 100) * (1 / (17 * K)) * (K / X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 + 99 / 100) * (1 / (17 * K)) * (K / X) = (199 / 1700) / X := by
      field_simp; ring
    have h4 : ((4 * M + 1 : ℕ) : ℝ) ≤ 1627 / 200 * X := by
      have h5 : ((X / 32 : ℕ) : ℝ) ≤ (X : ℝ) / 32 := Nat.cast_div_le
      have h6 : ((4 * M + 1 : ℕ) : ℝ) = 8 * X + 4 * ((X / 32 : ℕ) : ℝ) + 1 := by
        rw [hM]; push_cast; ring
      rw [h6]; linarith
    refine lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) ?_
    have h7 : (0 : ℝ) < ((4 * M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (4 * M)
    rw [div_lt_div_iff₀ hXpos h7]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four' I' g t M (4 * M + 1) η (1 / V.card) (99 / 100) (by norm_num) hIne hR hcoll
      hsupp hspec hnum
  obtain ⟨v1, x1, y1⟩ := hmem i1 m1
  obtain ⟨v2, x2, y2⟩ := hmem i2 m2
  obtain ⟨v3, x3, y3⟩ := hmem i3 m3
  obtain ⟨v4, x4, y4⟩ := hmem i4 m4
  set P : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => a i.1 + val' p i.2.1 with hP
  set Q : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => b i.1 + val' q i.2.2 with hQ
  have hPQ : ∀ i ∈ I', g i = P i - Q i := by
    intro i hi'
    have := hdiff _ (hmem i hi').1
    simp only [hg, hP, hQ]; omega
  set k := (P i1 - P i2) + (P i3 - P i4) with hk
  have hkt : k - t = (Q i1 - Q i2) + (Q i3 - Q i4) := by
    rw [hPQ _ m1, hPQ _ m2, hPQ _ m3, hPQ _ m4] at hsum
    omega
  have sP : ∀ i ∈ I', Small p (s + 1 / D) (P i) := fun i hi' =>
    (ha _ (hmem i hi').1).add (small_val' hp hD (hmem i hi').2.1)
  have sQ : ∀ i ∈ I', Small q (s + 1 / D) (Q i) := fun i hi' =>
    (hb _ (hmem i hi').1).add (small_val' hq hD (hmem i hi').2.2)
  have e4 : 4 * (s + 1 / (D : ℝ))
      = ((s + 1 / D) + (s + 1 / D)) + ((s + 1 / D) + (s + 1 / D)) := by ring
  refine ⟨k, ?_, ?_, ?_⟩
  · have bound : ∀ i ∈ I', |P i| ≤ 2 * (X : ℤ) := by
      intro i hi'
      have h1 := haX _ (hmem i hi').1
      have h2 := hvp _ (hmem i hi').2.1
      have := abs_add_le (a i.1) (val' p i.2.1)
      simp only [hP]; omega
    have b1 := bound _ m1
    have b2 := bound _ m2
    have b3 := bound _ m3
    have b4 := bound _ m4
    rw [abs_le] at b1 b2 b3 b4
    rw [abs_le, hk]; omega
  · rw [e4, hk]
    exact ((sP _ m1).sub (sP _ m2)).add ((sP _ m3).sub (sP _ m4))
  · rw [e4, hkt]
    exact ((sQ _ m1).sub (sQ _ m2)).add ((sQ _ m3).sub (sQ _ m4))


/-! ## Witnesses -/

/-- **Density to witnesses** at the height `64 exp ((1+δ) Y)`, for all large `Y`. -/
theorem witness_of_density_sunit {p q : ℕ} (hpp : p.Prime) (hqp : q.Prime) (hne : p ≠ q)
    (hE : EvertseCor1 {p, q}) {D : ℕ} (hD12 : 12 ≤ D) {K : ℝ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (s : ℝ) :
    ∃ Y1 : ℝ, ∀ Y : ℝ, Y1 ≤ Y → ∀ X : ℕ, 100 ≤ X → 64 * exp ((1 + δ) * Y) ≤ X →
      ∀ (V : Finset ℤ), (X : ℝ) ≤ K * V.card → ∀ a b : ℤ → ℤ, (∀ v ∈ V, v = a v - b v) →
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) → (∀ v ∈ V, |b v| ≤ (X : ℤ)) →
      (∀ v ∈ V, Small p s (a v)) → (∀ v ∈ V, Small q s (b v)) →
      ∀ t : ℤ, |(t : ℝ)| ≤ exp Y / 32 →
      ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
        ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hp : 2 ≤ p := hpp.two_le
  have hq : 2 ≤ q := hqp.two_le
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  set B : ℕ := ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊ with hB
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨Y1, hY1⟩ := rigidity_sunit hpp hqp hne hE hD12 B hδ2 (by linarith)
  set c : ℝ := max (sqrt (log p)) (sqrt (log q)) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) (le_max_left _ _)
  set u0 : ℝ := c + 7 * c / δ with hu0
  have hu00 : 0 ≤ u0 := by positivity
  refine ⟨max Y1 (u0 ^ 2), ?_⟩
  intro Y hY X hX100 hX V hV a b hdiff haX hbX ha hb t ht
  have hYu : u0 ^ 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 ≤ Y := le_trans (sq_nonneg _) hYu
  set u : ℝ := sqrt Y with hu
  have hu2 : u ^ 2 = Y := sq_sqrt hY0
  have huu : u0 ≤ u := by
    have := sqrt_le_sqrt hYu
    rwa [sqrt_sq hu00] at this
  have hupos : 0 ≤ u := sqrt_nonneg _
  have huc : c ≤ u := by
    have : (0 : ℝ) ≤ 7 * c / δ := by positivity
    rw [hu0] at huu; linarith
  have hu7 : 7 * c ≤ u * δ := by
    have h1 : 7 * c / δ ≤ u := by rw [hu0] at huu; linarith
    rwa [div_le_iff₀ hδ] at h1
  set v : ℝ := sqrt ((1 + δ / 2) * Y) with hv
  have hv0 : 0 ≤ v := sqrt_nonneg _
  have hv2 : v ^ 2 = (1 + δ / 2) * Y := sq_sqrt (mul_nonneg (by linarith) hY0)
  have hvu : v ≤ 5 / 4 * u := by
    have h1 : v ^ 2 ≤ (5 / 4 * u) ^ 2 := by
      have h2 : (1 + δ / 2) * Y ≤ 25 / 16 * Y := mul_le_mul_of_nonneg_right (by linarith) hY0
      rw [mul_pow, hu2, hv2]; linarith
    exact (pow_le_pow_iff_left₀ hv0 (by positivity) two_ne_zero).mp h1
  have htop : (v + c) ^ 2 ≤ (1 + δ) * Y := by
    have h1 : 2 * v * c ≤ 5 / 2 * (u * c) := by
      have := mul_le_mul_of_nonneg_right hvu hc0.le
      linarith
    have h2 : c ^ 2 ≤ u * c := by
      rw [sq]; exact mul_le_mul_of_nonneg_right huc hc0.le
    have h3 := mul_le_mul_of_nonneg_left hu7 hupos
    have h4 : u * (u * δ) = δ * Y := by rw [← hu2]; ring
    rw [h4] at h3
    have h5 : (v + c) ^ 2 = v ^ 2 + 2 * v * c + c ^ 2 := by ring
    rw [h5, hv2]
    linarith
  have hfit : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c →
      (r : ℝ) ^ ((⌊v / sqrt (log r)⌋₊ + 1) ^ 2) ≤ X / 64 := by
    intro r hr hrc
    have hs0 := sqrt_log_pos hr
    have h1 : ((⌊v / sqrt (log r)⌋₊ + 1 : ℕ) : ℝ) * sqrt (log r) ≤ v + c := by
      have h := Nat.floor_le (div_nonneg hv0 hs0.le)
      rw [le_div_iff₀ hs0] at h
      push_cast; linarith
    have h2 := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hs0.le) h1 2
    rw [mul_pow, sq_sqrt (TwoPrimesEffective.log_pos' hr).le] at h2
    have h3 : (r : ℝ) ^ ((⌊v / sqrt (log r)⌋₊ + 1) ^ 2) ≤ exp ((1 + δ) * Y) := by
      have hr0 : (0 : ℝ) < r := by
        have : 0 < r := by omega
        exact_mod_cast this
      rw [← exp_log (pow_pos hr0 _), log_pow]
      refine exp_le_exp.mpr (le_trans ?_ htop)
      push_cast at h2 ⊢
      exact h2
    exact le_trans h3 (by linarith)
  refine witness_of_density_rigid hp hq hD hK (s := s) (Y := Y) (X := X)
    (Np := ⌊v / sqrt (log p)⌋₊ + 1) (Nq := ⌊v / sqrt (log q)⌋₊ + 1)
    (hfit p hp (le_max_left _ _)) (hfit q hq (le_max_right _ _)) hX100 ?_ V hV a b hdiff haX hbX
    ha hb t ht
  intro θ hθ
  have hηpos : 0 < sqrt (1 / (17 * K)) := by
    have : (0 : ℝ) < K := by linarith
    exact sqrt_pos.mpr (by positivity)
  have hlogη : -log (sqrt (1 / (17 * K))) = log (17 * K) / 2 := by
    have : (0 : ℝ) < K := by linarith
    rw [log_sqrt (by positivity), one_div, log_inv]; ring
  have hcard := card_marked_joint'' hD12 hηpos hθ
  rw [hlogη] at hcard
  refine hY1 Y (le_trans (le_max_left _ _) hY) θ ?_
  rw [hB]
  refine Nat.le_floor ?_
  push_cast
  rw [← hv]
  linarith

/-- **Fixed radius:** `|k| ≤ C (1+|t|)^(1+δ)`, with a constant which is not computed. -/
theorem witness_of_free_heights_sunit {p q : ℕ} (hpp : p.Prime) (hqp : q.Prime) (hne : p ≠ q)
    (hE : EvertseCor1 {p, q}) {D : ℕ} (hD12 : 12 ≤ D) {K XD : ℝ} (hK : 1 ≤ K)
    (dens : ∀ X : ℕ, Free {p, q} D X → XD ≤ X → ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ,
      (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
      (∀ v ∈ V, Small p (2 / D) (a v)) ∧ (∀ v ∈ V, Small q (2 / D) (b v)))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℤ, ∃ k : ℤ, |(k : ℝ)| ≤ C * (1 + |(t : ℝ)|) ^ (1 + δ)
      ∧ Small p (12 / D) k ∧ Small q (12 / D) (k - t) := by
  classical
  have hp : 2 ≤ p := hpp.two_le
  have hq : 2 ≤ q := hqp.two_le
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hcard : ({p, q} : Finset ℕ).card = 2 := card_pair hne
  have hS : ∀ l ∈ ({p, q} : Finset ℕ), 2 ≤ l := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · omega
    · rw [mem_singleton] at h; omega
  have hβ : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlog : ∀ l ∈ ({p, q} : Finset ℕ), log 2 ≤ log (l : ℝ) := fun l hl =>
    log_le_log (by norm_num) (by exact_mod_cast hS l hl)
  obtain ⟨Y1, hY1⟩ := witness_of_density_sunit hpp hqp hne hE hD12 hK hδ hδ1 (2 / D)
  set H : ℝ := ((2 : ℕ) : ℝ) * log (8 * D) + 1 with hH
  set R0 : ℝ := 8 * exp ((H + log (8 * D)) ^ 2 / (4 * log 2)) with hR0
  set M : ℝ := max (max 100 XD) R0 with hM
  have hM100 : 100 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  set Y0 : ℝ := max (max Y1 (log 32)) (log M) with hY0def
  have hY0Y1 : Y1 ≤ Y0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY032 : log 32 ≤ Y0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY0M : log M ≤ Y0 := le_max_right _ _
  have hY00 : 0 ≤ Y0 := le_trans (log_nonneg (by norm_num)) hY032
  have hMexp : M ≤ exp Y0 := by
    have := exp_le_exp.mpr hY0M
    rwa [exp_log hM0] at this
  refine ⟨1024 * exp (H + (1 + δ) * Y0), by positivity, fun t => ?_⟩
  have ht0 : (0 : ℝ) < 1 + |(t : ℝ)| := by
    have := abs_nonneg (t : ℝ); linarith
  have hT0 : 0 ≤ log (1 + |(t : ℝ)|) := log_nonneg (by
    have := abs_nonneg (t : ℝ); linarith)
  set Y : ℝ := Y0 + log (1 + |(t : ℝ)|) with hY
  have hYY0 : Y0 ≤ Y := by rw [hY]; linarith
  have hY0' : 0 ≤ Y := le_trans hY00 hYY0
  set R : ℝ := 64 * exp ((1 + δ) * Y) with hR
  have hexpR : exp Y0 ≤ R := by
    have h1 : exp Y0 ≤ exp ((1 + δ) * Y) := by
      refine exp_le_exp.mpr (le_trans hYY0 ?_)
      exact le_mul_of_one_le_left hY0' (by linarith)
    have := exp_pos ((1 + δ) * Y)
    rw [hR]; linarith
  have hMR : M ≤ R := le_trans hMexp hexpR
  have hRfree : 8 * exp (((({p, q} : Finset ℕ).card * log (8 * D) + 1) + log (8 * D)) ^ 2
      / (4 * log 2)) ≤ R := by
    rw [hcard]
    exact le_trans (le_max_right _ _) hMR
  obtain ⟨X, hXR, hXtop, hXfree⟩ := exists_free {p, q} hS hD hβ hlog hRfree
  rw [hcard, ← hH] at hXtop
  have hX100 : 100 ≤ X := by
    have : (100 : ℝ) ≤ X := le_trans hM100 (le_trans hMR hXR)
    exact_mod_cast this
  have hXD : XD ≤ (X : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans hMR hXR)
  obtain ⟨V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ := dens X hXfree hXD
  have htx : |(t : ℝ)| ≤ exp Y / 32 := by
    have h1 : (32 : ℝ) ≤ exp Y0 := by
      have := exp_le_exp.mpr hY032
      rwa [exp_log (by norm_num : (0 : ℝ) < 32)] at this
    have h2 : exp Y = exp Y0 * (1 + |(t : ℝ)|) := by rw [hY, exp_add, exp_log ht0]
    have h3 := mul_le_mul_of_nonneg_right h1 ht0.le
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32), h2]
    linarith
  obtain ⟨k, hk, hkp, hkq⟩ := hY1 Y (le_trans hY0Y1 hYY0) X hX100 hXR V hV a b hdiff haX hbX
    ha hb t htx
  have e12 : (4 : ℝ) * (2 / D + 1 / D) = 12 / D := by ring
  rw [e12] at hkp hkq
  refine ⟨k, ?_, hkp, hkq⟩
  have h1 : |(k : ℝ)| ≤ 8 * (X : ℝ) := by exact_mod_cast hk
  have h2 : 8 * (X : ℝ) ≤ 8 * (2 * exp H * R) := mul_le_mul_of_nonneg_left hXtop (by norm_num)
  have e1 : 8 * (2 * exp H * R)
      = 1024 * exp (H + (1 + δ) * Y0) * (1 + |(t : ℝ)|) ^ (1 + δ) := by
    have e2 : (1 + |(t : ℝ)|) ^ (1 + δ) = exp (log (1 + |(t : ℝ)|) * (1 + δ)) :=
      rpow_def_of_pos ht0 _
    have e3 : exp ((1 + δ) * Y)
        = exp ((1 + δ) * Y0) * exp (log (1 + |(t : ℝ)|) * (1 + δ)) := by
      rw [← exp_add]; congr 1; rw [hY]; ring
    rw [e2, hR, e3, exp_add H]
    ring
  exact le_trans h1 (le_trans h2 (le_of_eq e1))

end TwoPrimesSUnit
