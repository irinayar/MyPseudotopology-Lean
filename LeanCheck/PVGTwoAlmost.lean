import Mathlib
import LeanCheck.PVGTwoPoint

/-!
# PVGtwo, Remark 7.10: almost every added point is an obstruction (Lean check)

Notation as in `PVGTwoPoint` (levels indexed from `0`). A pattern of level `K` assigns a bit to each pair `(k, i)` with
`k ≤ K`, `i < k + 5`. For `Lv K ≤ n < 2 Lv K` the digits of `c` with indices `n² - Lv k + i` form a block.

* `bad_volume` : the numbers in `[0,1)` none of whose blocks shows a given pattern have measure at most
  `(1 - 2^{-B})^{Lv K}`, where `B` is the number of pairs;
* `ae_all_patterns` : for almost every `c` and all large `K` every pattern of level `K` occurs (Borel–Cantelli);
* `ae_cover` : hence almost every `c` has the covering property of `exists_cover`;
* `ae_point_unservable` : for almost every `c`, no non-precompact group topology below the usual one makes `aS`,
  `a ∈ A(δ)`, and `cS` totally bounded.

The probability argument is the one proposed in ChatGPT's audit of Section 7.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace PVG
namespace Two
open Q95 Lac

/-- The places `(k, i)` of a pattern of level `K`. -/
abbrev Places (K : ℕ) := Σ k : Fin (K + 1), Fin (k.val + 5)

/-- The digit index used by the block of `n` at the place `q`. -/
def pos (K n : ℕ) (q : Places K) : ℕ := n ^ 2 - Lv q.1.val + q.2.val

def Match (c : ℝ) (K n : ℕ) (w : Places K → Fin 2) : Prop := ∀ q : Places K, Real.digits c 2 (pos K n q) = w q

lemma card_places (K : ℕ) : Fintype.card (Places K) = off (K + 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h : ∀ M : ℕ, ∑ k : Fin M, (k.val + 5) = off M := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      rfl
  exact h (K + 1)

lemma pos_inj {K n n' : ℕ} {q q' : Places K} (hn : Lv K ≤ n) (hn' : Lv K ≤ n')
    (h : pos K n q = pos K n' q') : n = n' ∧ q = q' := by
  have hbig := Lv_big K
  have key : ∀ (m : ℕ) (r : Places K), Lv K ≤ m →
      pos K m r + Lv r.1.val = m ^ 2 + r.2.val ∧ Lv r.1.val ≤ Lv K ∧ r.2.val < K + 5 := by
    intro m r hm
    have h1 : Lv r.1.val ≤ Lv K := Lv_mono (Nat.lt_succ_iff.1 r.1.isLt)
    have h2 : m ≤ m ^ 2 := Nat.le_self_pow two_ne_zero _
    have h3 := r.2.isLt
    have h4 := r.1.isLt
    refine ⟨?_, h1, by omega⟩
    unfold pos; omega
  obtain ⟨e1, l1, i1⟩ := key n q hn
  obtain ⟨e2, l2, i2⟩ := key n' q' hn'
  have hsq : ∀ a b : ℕ, Lv K ≤ a → a < b → a ^ 2 + (2 * Lv K + 1) ≤ b ^ 2 := by
    intro a b ha hab
    have h3 : (a + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
    have h4 : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
    omega
  have hnn : n = n' := by
    rcases lt_trichotomy n n' with h0 | h0 | h0
    · have := hsq n n' hn h0
      omega
    · exact h0
    · have := hsq n' n hn' h0
      omega
  subst hnn
  refine ⟨rfl, ?_⟩
  obtain ⟨⟨k, hk⟩, ⟨i, hi⟩⟩ := q
  obtain ⟨⟨k', hk'⟩, ⟨i', hi'⟩⟩ := q'
  simp only at e1 e2 hi hi'
  have hkk : k = k' := by
    rcases lt_trichotomy k k' with h0 | h0 | h0
    · have := Lv_gap h0
      omega
    · exact h0
    · have := Lv_gap h0
      omega
  subst hkk
  have hii : i = i' := by omega
  subst hii
  rfl

/-- Counting: words of length `M` none of whose `N` disjoint blocks (placed by `p`) equals `w`. -/
lemma count_avoid {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq N] [DecidableEq Q] (M : ℕ)
    (p : N × Q → Fin M) (hp : Function.Injective p) (w : Q → Fin 2) :
    (Finset.univ.filter fun f : Fin M → Fin 2 => ∀ n : N, (fun q => f (p (n, q))) ≠ w).card ≤
      (2 ^ Fintype.card Q - 1) ^ Fintype.card N * 2 ^ (M - Fintype.card N * Fintype.card Q) := by
  classical
  set F := Finset.univ.filter fun f : Fin M → Fin 2 => ∀ n : N, (fun q => f (p (n, q))) ≠ w with hF
  set R : Finset (Fin M) := Finset.univ.image p with hR
  have hRcard : R.card = Fintype.card N * Fintype.card Q := by
    rw [hR, Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_prod]
  let φ : F → (N → {h : Q → Fin 2 // h ≠ w}) × ({j : Fin M // j ∉ R} → Fin 2) := fun f =>
    (fun n => ⟨fun q => f.1 (p (n, q)), (Finset.mem_filter.1 f.2).2 n⟩, fun j => f.1 j.1)
  have hφ : Function.Injective φ := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Subtype.ext (funext fun j => ?_)
    by_cases hj : j ∈ R
    · obtain ⟨⟨n, q⟩, _, rfl⟩ := Finset.mem_image.1 hj
      exact congrFun (congrArg Subtype.val (congrFun h1 n)) q
    · exact congrFun h2 ⟨j, hj⟩
  have e1 : Fintype.card {h : Q → Fin 2 // h ≠ w} = 2 ^ Fintype.card Q - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]
  have e2 : Fintype.card {j : Fin M // j ∉ R} = M - Fintype.card N * Fintype.card Q := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hRcard]
  have h1 := Fintype.card_le_of_injective φ hφ
  rwa [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, e1, e2] at h1

lemma card_le_of_blocks {N Q : Type*} [Fintype N] [Fintype Q] (M : ℕ) (p : N × Q → Fin M)
    (hp : Function.Injective p) : Fintype.card N * Fintype.card Q ≤ M := by
  have := Fintype.card_le_of_injective p hp
  rwa [Fintype.card_prod, Fintype.card_fin] at this

attribute [local irreducible] Lv off in
lemma bad_volume (K : ℕ) (w : Places K → Fin 2) :
    volume {c : ℝ | c ∈ Ico (0 : ℝ) 1 ∧ ∀ n ∈ Finset.Ico (Lv K) (2 * Lv K), ¬ Match c K n w} ≤
      ENNReal.ofReal ((1 - ((2 : ℝ) ^ off (K + 1))⁻¹) ^ Lv K) := by
  classical
  set B := off (K + 1) with hB
  set N := Finset.Ico (Lv K) (2 * Lv K) with hN
  set M := (2 * Lv K) ^ 2 + (K + 5) with hM
  have hNcard : N.card = Lv K := by rw [hN, Nat.card_Ico]; omega
  have hposlt : ∀ (n : N) (q : Places K), pos K n.1 q < M := by
    intro n q
    have h1 := (Finset.mem_Ico.1 n.2).2
    have h2 : n.1 ^ 2 ≤ (2 * Lv K) ^ 2 := Nat.pow_le_pow_left h1.le 2
    have h3 := q.2.isLt
    have h4 := q.1.isLt
    unfold pos; omega
  let p : N × Places K → Fin M := fun z => ⟨pos K z.1.1 z.2, hposlt z.1 z.2⟩
  have hp : Function.Injective p := by
    rintro ⟨n, q⟩ ⟨n', q'⟩ h
    have h1 : pos K n.1 q = pos K n'.1 q' := congrArg Fin.val h
    obtain ⟨h2, h3⟩ := pos_inj (Finset.mem_Ico.1 n.2).1 (Finset.mem_Ico.1 n'.2).1 h1
    rw [Subtype.ext h2, h3]
  set Fbad : Finset (Fin M → Fin 2) := Finset.univ.filter fun f => ∀ n : N, (fun q => f (p (n, q))) ≠ w with hF
  -- the bad set is covered by short intervals
  let v : (Fin M → Fin 2) → ℝ := fun f => ∑ j : Fin M, (f j : ℕ) * ((2 : ℝ) ^ (j.val + 1))⁻¹
  have hcover : {c : ℝ | c ∈ Ico (0 : ℝ) 1 ∧ ∀ n ∈ N, ¬ Match c K n w} ⊆
      ⋃ f ∈ Fbad, Icc (v f) (v f + ((2 : ℝ) ^ M)⁻¹) := by
    rintro c ⟨hc, hbad⟩
    set f : Fin M → Fin 2 := fun j => Real.digits c 2 j.val with hf
    refine mem_iUnion₂.2 ⟨f, ?_, ?_⟩
    · rw [hF, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun n h => hbad n.1 n.2 fun q => ?_⟩
      exact congrFun h q
    · have h1 : Real.ofDigits (Real.digits c 2) = c := Real.ofDigits_digits one_lt_two hc
      have h2 := Real.ofDigits_eq_sum_add_ofDigits (Real.digits c 2) M
      rw [h1] at h2
      have h3 : ∑ i ∈ Finset.range M, Real.ofDigitsTerm (Real.digits c 2) i = v f := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold Real.ofDigitsTerm
        simp only [hf]
        push_cast
        rfl
      rw [h3] at h2
      have h4 := Real.ofDigits_nonneg (fun i => Real.digits c 2 (i + M))
      have h5 := Real.ofDigits_le_one (fun i => Real.digits c 2 (i + M))
      have h6 : (0 : ℝ) ≤ ((2 : ℝ) ^ M)⁻¹ := by positivity
      have h7 : c = v f + ((2 : ℝ) ^ M)⁻¹ * Real.ofDigits (fun i => Real.digits c 2 (i + M)) := by
        conv_lhs => rw [h2]
        push_cast
        ring
      constructor
      · have := mul_nonneg h6 h4
        linarith
      · have := mul_le_of_le_one_right h6 h5
        linarith
  -- counting
  have hNc : Fintype.card N = Lv K := by rw [Fintype.card_coe, hNcard]
  have hQc : Fintype.card (Places K) = B := card_places K
  have hRle : Lv K * B ≤ M := by
    have := card_le_of_blocks M p hp
    rwa [hNc, hQc] at this
  have hcount : Fbad.card ≤ (2 ^ B - 1) ^ Lv K * 2 ^ (M - Lv K * B) := by
    have := count_avoid M p hp w
    rw [hNc, hQc] at this
    exact this
  -- the estimate
  have hvol : volume {c : ℝ | c ∈ Ico (0 : ℝ) 1 ∧ ∀ n ∈ N, ¬ Match c K n w} ≤
      ENNReal.ofReal (Fbad.card * ((2 : ℝ) ^ M)⁻¹) := by
    refine (measure_mono hcover).trans ((measure_biUnion_finset_le Fbad _).trans (le_of_eq ?_))
    have h1 : ∀ f ∈ Fbad, volume (Icc (v f) (v f + ((2 : ℝ) ^ M)⁻¹)) = ENNReal.ofReal (((2 : ℝ) ^ M)⁻¹) := by
      intro f _
      rw [Real.volume_Icc]; congr 1; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2B : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have h1 : (Fbad.card : ℝ) ≤ ((2 : ℝ) ^ B - 1) ^ Lv K * 2 ^ (M - Lv K * B) := by
    have h3 : (Fbad.card : ℝ) ≤ (((2 ^ B - 1) ^ Lv K * 2 ^ (M - Lv K * B) : ℕ) : ℝ) := by exact_mod_cast hcount
    refine h3.trans (le_of_eq ?_)
    push_cast [Nat.cast_sub h2B]
    rfl
  have h4 : (2 : ℝ) ^ M = (2 ^ B) ^ Lv K * 2 ^ (M - Lv K * B) := by
    rw [← pow_mul, ← pow_add]; congr 1; rw [mul_comm B]; omega
  have hb : (0 : ℝ) < 2 ^ B := by positivity
  refine (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (le_of_eq ?_)
  have h5 : (1 : ℝ) - ((2 : ℝ) ^ B)⁻¹ = (2 ^ B - 1) / 2 ^ B := by field_simp
  rw [h5, div_pow, h4]
  have h6 : (0 : ℝ) < 2 ^ (M - Lv K * B) := by positivity
  field_simp

lemma level_small (K : ℕ) (hK : 1 ≤ K) : (2 ^ off (K + 1)) ^ 2 * 2 ^ K ≤ Lv K := by
  have hoff : ∀ m, 2 * off m = m * m + 9 * m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have e : off (m + 1) = off m + (m + 5) := rfl
      have e2 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      omega
  have hLv : ∀ m, 2 ^ (6 * 4 ^ m) ≤ Lv m := by
    intro m
    induction m with
    | zero => exact le_trans (by norm_num) (Lv_ge 0)
    | succ m ih =>
      refine le_trans (le_of_eq ?_) ((Nat.pow_le_pow_left ih 4).trans (Lv_pow4 m))
      rw [← pow_mul]; congr 1; ring
  have h4 : ∀ m, 1 ≤ m → (m + 1) * (m + 1) + 9 * (m + 1) + m ≤ 6 * 4 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have e : 6 * 4 ^ (m + 1) = 4 * (6 * 4 ^ m) := by rw [pow_succ]; ring
      rw [e]
      have h5 : (m + 1 + 1) * (m + 1 + 1) + 9 * (m + 1 + 1) + (m + 1) ≤
          4 * ((m + 1) * (m + 1) + 9 * (m + 1) + m) := by nlinarith
      omega
  rw [← pow_mul, ← pow_add]
  refine le_trans (Nat.pow_le_pow_right two_pos ?_) (hLv K)
  have h1 := hoff (K + 1)
  have h2 := h4 K hK
  omega

/-- For almost every `c` and all large `K`, every pattern of level `K` occurs. -/
theorem ae_all_patterns : ∀ᵐ c ∂(volume.restrict (Ico (0 : ℝ) 1)),
    ∀ᶠ K in atTop, ∀ w : Places K → Fin 2, ∃ n ∈ Finset.Ico (Lv K) (2 * Lv K), Match c K n w := by
  classical
  set Bad : ℕ → Set ℝ := fun K => {c : ℝ | c ∈ Ico (0 : ℝ) 1 ∧
    ∃ w : Places K → Fin 2, ∀ n ∈ Finset.Ico (Lv K) (2 * Lv K), ¬ Match c K n w} with hBad
  have hbound : ∀ K, 1 ≤ K → volume (Bad K) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹) ^ K) := by
    intro K hK
    set B := off (K + 1) with hB
    set L := Lv K with hL
    have h1 : Bad K ⊆ ⋃ w ∈ (Finset.univ : Finset (Places K → Fin 2)),
        {c : ℝ | c ∈ Ico (0 : ℝ) 1 ∧ ∀ n ∈ Finset.Ico (Lv K) (2 * Lv K), ¬ Match c K n w} := by
      rintro c ⟨hc, w, hw⟩
      exact mem_iUnion₂.2 ⟨w, Finset.mem_univ _, hc, hw⟩
    set P : ℝ := 2 ^ B with hP
    have hP1 : 1 ≤ P := one_le_pow₀ one_le_two
    have hP0 : 0 < P := by positivity
    have hx0 : 0 ≤ 1 - P⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hP1)
    have h2 : volume (Bad K) ≤ ENNReal.ofReal (P * (1 - P⁻¹) ^ L) := by
      refine (measure_mono h1).trans ((measure_biUnion_finset_le _ _).trans ?_)
      refine (Finset.sum_le_sum fun w _ => bad_volume K w).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_places, nsmul_eq_mul,
        ENNReal.ofReal_mul hP0.le]
      congr 1
      rw [hP, ← hB]
      rw [ENNReal.ofReal_pow two_pos.le]
      push_cast
      norm_num
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    -- Bernoulli
    have hbern : (1 - P⁻¹) ^ L * (1 + L * P⁻¹) ≤ 1 := by
      have h3 : 1 + (L : ℝ) * P⁻¹ ≤ (1 + P⁻¹) ^ L :=
        one_add_mul_le_pow (le_trans (by norm_num) (inv_nonneg.2 hP0.le)) L
      refine (mul_le_mul_of_nonneg_left h3 (pow_nonneg hx0 _)).trans ?_
      rw [← mul_pow]
      refine pow_le_one₀ (mul_nonneg hx0 (by positivity)) ?_
      have e : (1 - P⁻¹) * (1 + P⁻¹) = 1 - P⁻¹ ^ 2 := by ring
      rw [e]
      have := sq_nonneg (P⁻¹)
      linarith
    have hLpos : (0 : ℝ) < L := by
      have : 0 < L := lt_of_lt_of_le (by norm_num) (Lv_ge K)
      exact_mod_cast this
    have h4 : (1 - P⁻¹) ^ L ≤ P / L := by
      have h5 : (L : ℝ) * P⁻¹ * (1 - P⁻¹) ^ L ≤ 1 := by
        refine le_trans ?_ hbern
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hx0 _)
      rw [le_div_iff₀ hLpos]
      have h6 := mul_le_mul_of_nonneg_left h5 hP0.le
      have e : P * ((L : ℝ) * P⁻¹ * (1 - P⁻¹) ^ L) = (1 - P⁻¹) ^ L * L := by field_simp
      rwa [e, mul_one] at h6
    have h7 : P ^ 2 * 2 ^ K ≤ (L : ℝ) := by
      have := level_small K hK
      rw [hP, hL, hB]
      exact_mod_cast this
    refine (mul_le_mul_of_nonneg_left h4 hP0.le).trans ?_
    rw [inv_pow, ← mul_div_assoc, div_le_iff₀ hLpos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hsum : ∑' K, volume (Bad K) ≠ ⊤ := by
    have h1 : ∀ K, volume (Bad K) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹) ^ K) + (if K = 0 then 1 else 0) := by
      intro K
      rcases Nat.eq_zero_or_pos K with h | h
      · rw [if_pos h]
        refine le_trans ?_ (le_add_left le_rfl)
        refine (measure_mono (t := Ico (0 : ℝ) 1) fun c hc => hc.1).trans (le_of_eq ?_)
        rw [Real.volume_Ico]; simp
      · exact (hbound K h).trans le_self_add
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
    rw [ENNReal.tsum_add, tsum_ite_eq]
    refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.one_ne_top⟩
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun K => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem hsum
  have hae' : ∀ᵐ c ∂(volume.restrict (Ico (0 : ℝ) 1)), ∀ᶠ K in atTop, c ∉ Bad K := ae_restrict_of_ae hae
  filter_upwards [hae', ae_restrict_mem measurableSet_Ico] with c hc hmem
  refine hc.mono fun K hK w => ?_
  by_contra h
  exact hK ⟨hmem, w, fun n hn hm => h ⟨n, hn, hm⟩⟩

/-- Almost every `c` has the covering property. -/
theorem ae_cover : ∀ᵐ c ∂(volume.restrict (Ico (0 : ℝ) 1)),
    ∀ x : ℝ, ∃ m : ℕ, ∀ k, dint ((x - c * sT m) / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (k + 4))⁻¹ := by
  filter_upwards [ae_all_patterns, ae_restrict_mem measurableSet_Ico] with c hpat hc01 x
  have hc0 : 0 ≤ c := hc01.1
  have hc1 : c ≤ 1 := hc01.2.le
  obtain ⟨K0, hK0⟩ := eventually_atTop.1 hpat
  obtain ⟨K1, hK1⟩ : ∃ K : ℕ, |x| ≤ K := exists_nat_ge _
  set K := max K0 K1 with hKdef
  have hK : |x| ≤ K := hK1.trans (by exact_mod_cast le_max_right K0 K1)
  set e : ℕ → Fin 2 := Real.digits c 2 with he
  have hce : Real.ofDigits e = c := Real.ofDigits_digits one_lt_two hc01
  set θ : ℕ → ℝ := fun k => Int.fract (x / 2 ^ Lv k) with hθ
  set w : Places K → Fin 2 := fun q => Real.digits (θ q.1.val) 2 q.2.val with hw
  obtain ⟨n, hn, hm⟩ := hK0 K (le_max_left _ _) w
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.1 hn
  have hLK := Lv_big K
  have hsT : sT (n - 1) = (2 : ℝ) ^ (n ^ 2) := by
    show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
    congr 2; omega
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  refine ⟨n - 1, fun k => ?_⟩
  rw [hsT]
  have hpos : (0 : ℝ) < 2 ^ Lv k := by positivity
  rcases le_or_gt k K with hk | hk
  · have hLk : Lv k ≤ Lv K := Lv_mono hk
    set M := n ^ 2 - Lv k with hM
    have hMn : (2 : ℝ) ^ (n ^ 2) = 2 ^ M * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
    obtain ⟨z, hz⟩ := shift_digits e M
    have hθ01 : θ k ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hθd : Real.ofDigits (Real.digits (θ k) 2) = θ k := Real.ofDigits_digits one_lt_two hθ01
    have hagree : ∀ i < k + 5, (fun i => e (i + M)) i = Real.digits (θ k) 2 i := by
      intro i hi
      have h := hm ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨i, hi⟩⟩
      have e1 : pos K n ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨i, hi⟩⟩ = i + M := by
        show n ^ 2 - Lv k + i = i + M
        omega
      rw [e1] at h
      exact h
    have hclose : |θ k - Real.ofDigits (fun i => e (i + M))| ≤ ((2 : ℝ) ^ (k + 5))⁻¹ := by
      have h1 := Real.abs_ofDigits_sub_ofDigits_le (b := 2) (x := Real.digits (θ k) 2)
        (y := fun i => e (i + M)) (n := k + 5) (fun i hi => (hagree i hi).symm)
      rw [hθd] at h1
      exact_mod_cast h1
    have e1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k =
        (θ k - Real.ofDigits (fun i => e (i + M))) - ((z - ⌊x / 2 ^ Lv k⌋ : ℤ) : ℝ) := by
      have h1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k = x / 2 ^ Lv k - 2 ^ M * c := by
        rw [hMn]; field_simp
      have h2 : x / 2 ^ Lv k = ⌊x / 2 ^ Lv k⌋ + θ k := (Int.floor_add_fract _).symm
      rw [h1, ← hce, hz]
      conv_lhs => rw [h2]
      push_cast
      ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans (hclose.trans ?_)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
  · have hLk := Lv_big k
    have h4 : Lv K ^ 4 ≤ Lv k := (Lv_pow4 K).trans (Lv_mono (Nat.succ_le_of_lt hk))
    have hL72 := Lv_ge K
    have hn4 : n ^ 2 ≤ 4 * Lv K ^ 2 := by
      have : n ≤ 2 * Lv K := by omega
      have := Nat.pow_le_pow_left this 2
      rw [mul_pow] at this
      simpa using this
    have h8 : 8 * Lv K ^ 2 ≤ Lv K ^ 4 := by
      have e1 : Lv K ^ 4 = Lv K ^ 2 * Lv K ^ 2 := by ring
      have h6 : 72 * 72 ≤ Lv K ^ 2 := by rw [sq]; exact Nat.mul_le_mul hL72 hL72
      rw [e1]
      exact Nat.mul_le_mul_right _ (le_trans (by omega) h6)
    have hbig : n ^ 2 + (k + 5) ≤ Lv k := by omega
    have hxk : K + (k + 5) ≤ Lv k := by omega
    refine (dint_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : |x - c * 2 ^ (n ^ 2)| ≤ |x| + 2 ^ (n ^ 2) := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_of_nonneg (mul_nonneg hc0 (by positivity))]
      exact mul_le_of_le_one_left (by positivity) hc1
    have h2 : |x| ≤ 2 ^ K := by
      have h3 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
      linarith
    have h5 : ∀ a : ℕ, a + (k + 5) ≤ Lv k → (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ (k + 4))⁻¹ * 2 ^ Lv k / 2 := by
      intro a ha
      have e1 : (2 : ℝ) ^ (a + (k + 5)) ≤ 2 ^ Lv k := pow_le_pow_right₀ one_le_two ha
      have e2 : (2 : ℝ) ^ (a + (k + 5)) = 2 ^ a * (2 ^ (k + 4) * 2) := by
        rw [← pow_succ, ← pow_add]
      rw [e2] at e1
      rw [le_div_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h6 := h5 K hxk
    have h7 := h5 (n ^ 2) hbig
    linarith

/-- **Remark 7.10.** For almost every `c ∈ [0,1)`, no non-precompact group topology below the usual one makes all `aS`,
`a ∈ A(δ)`, and `cS` totally bounded. -/
theorem ae_point_unservable : ∀ᵐ c ∂(volume.restrict (Ico (0 : ℝ) 1)),
    ∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) → Tb (@nhds ℝ γ 0) (dil c Sset) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  refine ae_cover.mono fun c hc γ hg heu hA hcS => ?_
  exact point_core c hc _ (group_half γ hg) heu (fun d hd => hA _ (inA_of_Cdig d hd)) hcS

end Two
end PVG
