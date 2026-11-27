import LeanCheck.PVGThreeSufficient
import LeanCheck.PVGThreeSquares
import LeanCheck.PVGThreeCountable

/-!
# PVGthree: classification of rigidity for fast dyadic sequences

`δ_k = 2^(-L_k)`. Assume `k^5 ≤ C L_k`, and that `L_k` lies in the first half between consecutive squares:
`L_k ≤ c^2 + c`, `c = Nat.sqrt L_k`. Then `δ` is rigid iff `L_k - c^2 → ∞` iff `A(δ)` is uncountable
(`rig_iff_of_sparse`, `rig_iff_uncountable_of_sparse`). In particular `L_k = 4^k + k` gives a rigid
sequence. Also `rig_of_far_windows`: a condition that only concerns infinitely many large jumps.

The divisor bound used (`card_divisors_pow_le`) is proved here. Sequences are indexed from `0`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

/-! ## A divisor bound -/

lemma succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self

lemma succ_pow_le (K a : ℕ) (hK : 1 ≤ K) : (a + 1) ^ K ≤ 2 ^ (K * K) * 2 ^ a := by
  have h1 : a + 1 ≤ K * (a / K + 1) := by
    have := Nat.lt_mul_div_succ a (show 0 < K by omega)
    omega
  have h2 : K * (a / K + 1) ≤ 2 ^ K * 2 ^ (a / K) :=
    Nat.mul_le_mul (Nat.lt_two_pow_self).le (succ_le_two_pow _)
  calc (a + 1) ^ K ≤ (2 ^ K * 2 ^ (a / K)) ^ K := Nat.pow_le_pow_left (h1.trans h2) K
    _ = 2 ^ (K * K) * 2 ^ (a / K * K) := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ 2 ^ (K * K) * 2 ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (Nat.div_mul_le_self a K))

/-- `d(n)^K ≤ C n`. -/
lemma card_divisors_pow_le (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ K ≤ C * n := by
  set B := 2 ^ (K * K) with hB
  have hB1 : 1 ≤ B := Nat.one_le_two_pow
  refine ⟨B ^ (2 ^ K), Nat.one_le_pow _ _ hB1, fun n hn => ?_⟩
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  have hfac : ∀ p ∈ n.primeFactors, (n.factorization p + 1) ^ K ≤
      (if p < 2 ^ K then B else 1) * p ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    set e := n.factorization p
    split_ifs with h
    · exact (succ_pow_le K e hK).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp2 e))
    · rw [one_mul]
      calc (e + 1) ^ K ≤ (2 ^ e) ^ K := Nat.pow_le_pow_left (succ_le_two_pow e) K
        _ = (2 ^ K) ^ e := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ p ^ e := Nat.pow_le_pow_left (not_lt.1 h) e
  refine (Finset.prod_le_prod' hfac).trans ?_
  rw [Finset.prod_mul_distrib]
  refine Nat.mul_le_mul ?_ (le_of_eq ?_)
  · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine Nat.pow_le_pow_right hB1 ?_
    refine (Finset.card_le_card (t := Finset.range (2 ^ K)) fun p hp => ?_).trans (Finset.card_range _).le
    exact Finset.mem_range.2 (Finset.mem_filter.1 hp).2
  · exact Nat.prod_factorization_pow_eq_self hn

/-- The number of `n` with `n^2 + M` a square `> n^2` is at most the number of divisors of `M`. -/
lemma card_sqdiff_le (U M : ℕ) [DecidablePred fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M] :
    ((Finset.Icc 1 U).filter fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M).card ≤ M.divisors.card := by
  have key : ∀ n ∈ (Finset.Icc 1 U).filter (fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M),
      0 < Nat.sqrt (n ^ 2 + M) - n ∧
        M = (Nat.sqrt (n ^ 2 + M) - n) * ((Nat.sqrt (n ^ 2 + M) - n) + 2 * n) := by
    intro n hn
    obtain ⟨m, hnm, hm⟩ := (Finset.mem_filter.1 hn).2
    have e : Nat.sqrt (n ^ 2 + M) = m := by rw [← hm, Nat.sqrt_eq']
    rw [e]
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hnm.le
    have ha' : m - n = a := by omega
    rw [ha']
    refine ⟨by omega, ?_⟩
    have h1 : m ^ 2 = n ^ 2 + a * (a + 2 * n) := by rw [ha]; ring
    omega
  refine Finset.card_le_card_of_injOn (fun n => Nat.sqrt (n ^ 2 + M) - n) (fun n hn => ?_) ?_
  · have hn' := Finset.mem_coe.1 hn
    obtain ⟨hpos, he⟩ := key n hn'
    refine Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨⟨_, he⟩, ?_⟩)
    have : 0 < (Nat.sqrt (n ^ 2 + M) - n) * ((Nat.sqrt (n ^ 2 + M) - n) + 2 * n) :=
      Nat.mul_pos hpos (by omega)
    omega
  · intro n1 h1 n2 h2 h
    obtain ⟨hpos, he1⟩ := key n1 (Finset.mem_coe.1 h1)
    obtain ⟨_, he2⟩ := key n2 (Finset.mem_coe.1 h2)
    simp only at h
    rw [← h] at he2
    have := Nat.eq_of_mul_eq_mul_left hpos (he1.symm.trans he2)
    omega

/-! ## Fast sequences -/

/-- **Rigidity for fast sequences whose distance to the square below tends to infinity.** -/
theorem rig_of_sparse (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (C : ℕ) (hC : ∀ k, k ^ 5 ≤ C * L k)
    (hr : Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop)
    (hlow : ∀ k, L k ≤ Nat.sqrt (L k) ^ 2 + Nat.sqrt (L k)) : Rig (dyseq L) := by
  classical
  have hC1 : 1 ≤ C := by
    by_contra h
    have : C = 0 := by omega
    have := hC 1
    simp [*] at this
  set g : ℕ → ℕ := fun k => Nat.findGreatest (fun j => j ^ 16 ≤ k) k with hg
  have hg16 : ∀ k, g k ^ 16 ≤ k := fun k =>
    Nat.findGreatest_spec (P := fun j => j ^ 16 ≤ k) (m := 0) (Nat.zero_le _) (by simp)
  have hgmono : ∀ a b, a ≤ b → g a ≤ g b := fun a b hab =>
    Nat.le_findGreatest ((Nat.findGreatest_le _).trans hab) ((hg16 a).trans hab)
  set w : ℕ → ℕ := fun k => min ((L k - Nat.sqrt (L k) ^ 2) / 2) (g k) with hw
  have hwtop : Tendsto w atTop atTop := by
    refine tendsto_atTop.2 fun t => ?_
    filter_upwards [hr.eventually (eventually_ge_atTop (2 * t)), eventually_ge_atTop (t ^ 16)] with k h1 h3
    refine le_min (by omega) (Nat.le_findGreatest ?_ h3)
    exact (Nat.le_self_pow (by norm_num) t).trans h3
  refine rig_of_avoids_seq L w hL h2 hwtop fun p0 N => ?_
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hr.eventually (eventually_ge_atTop (2 * p0 + 2)))
  obtain ⟨C', hC'1, hC'⟩ := card_divisors_pow_le 40 (by norm_num)
  set N0 := max N (L k0 + p0 + 1) with hN0
  set E := 648 * C ^ 5 * C' ^ 2 * p0 ^ 4 with hE
  obtain ⟨u, hu1, hu2⟩ : ∃ u : ℕ, 16 * E + 1 ≤ u ∧ 2 * N0 + 2 ≤ u :=
    ⟨16 * E + 2 * N0 + 3, by omega, by omega⟩
  have hu0 : 0 < u := by omega
  set U := u ^ 5 with hU
  have huU : u ≤ U := Nat.le_self_pow (by norm_num) u
  set Ks := (Finset.range (2 * C * u ^ 4 + 1)).filter (fun k => L k ≤ 2 * U ^ 4) with hKs
  set T := g (2 * C * u ^ 4) with hT
  set Bad : Finset ℕ := Ks.biUnion fun k => (Finset.Icc 1 T).biUnion fun t => (Finset.range p0).biUnion fun p =>
    (Finset.Icc 1 U).filter fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + (L k - t - p) with hBad
  -- a bound for the divisor counts
  obtain ⟨D, hD2, hDle⟩ : ∃ D : ℕ, D ^ 2 ≤ 2 * C' * u ∧ ∀ M, M ≤ 2 * U ^ 4 → M.divisors.card ≤ D := by
    refine ⟨Nat.sqrt (2 * C' * u), Nat.sqrt_le' _, fun M hM => ?_⟩
    rw [Nat.le_sqrt']
    rcases eq_or_ne M 0 with h0 | h0
    · simp [h0]
    refine (Nat.pow_le_pow_iff_left (n := 20) (by norm_num)).1 ?_
    rw [← pow_mul]
    norm_num only
    refine (hC' M h0).trans ?_
    have e : U ^ 4 = u ^ 20 := by rw [hU, ← pow_mul]
    have h1 : 2 * C' ≤ (2 * C') ^ 20 := Nat.le_self_pow (by norm_num) _
    calc C' * M ≤ C' * (2 * u ^ 20) := Nat.mul_le_mul_left _ (e ▸ hM)
      _ = (2 * C') * u ^ 20 := by ring
      _ ≤ (2 * C') ^ 20 * u ^ 20 := Nat.mul_le_mul_right _ h1
      _ = (2 * C' * u) ^ 20 := (mul_pow _ _ _).symm
  have hcard : Bad.card ≤ (3 * C * u ^ 4) * (T * (p0 * D)) := by
    have hKc : Ks.card ≤ 3 * C * u ^ 4 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_range]
      have h1 : 1 ≤ C * u ^ 4 := Nat.mul_pos hC1 (pow_pos hu0 4)
      nlinarith
    refine (Finset.card_biUnion_le_card_mul _ _ (T * (p0 * D)) fun k hk => ?_).trans
      (Nat.mul_le_mul_right _ hKc)
    refine (Finset.card_biUnion_le_card_mul _ _ (p0 * D) fun t _ => ?_).trans
      (le_of_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel]))
    refine (Finset.card_biUnion_le_card_mul _ _ D fun p _ => ?_).trans
      (le_of_eq (by rw [Finset.card_range]))
    refine (card_sqdiff_le U _).trans (hDle _ ?_)
    have := (Finset.mem_filter.1 hk).2
    omega
  have hT4 : T ^ 4 ≤ 2 * C * u := by
    refine (Nat.pow_le_pow_iff_left (n := 4) (by norm_num)).1 ?_
    rw [← pow_mul]
    norm_num only
    refine (hg16 _).trans ?_
    rw [mul_pow (2 * C) u 4]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) _)
  have hsmall : 2 * Bad.card < U := by
    refine (Nat.pow_lt_pow_iff_left (n := 4) (by norm_num)).1 ?_
    have h4 : Bad.card ^ 4 ≤ E * u ^ 19 := by
      refine (Nat.pow_le_pow_left hcard 4).trans ?_
      have hD4 : D ^ 4 ≤ (2 * C' * u) ^ 2 := by
        have := Nat.pow_le_pow_left hD2 2
        rwa [← pow_mul] at this
      calc (3 * C * u ^ 4 * (T * (p0 * D))) ^ 4 = (3 * C * u ^ 4) ^ 4 * (T ^ 4 * (p0 ^ 4 * D ^ 4)) := by ring
        _ ≤ (3 * C * u ^ 4) ^ 4 * ((2 * C * u) * (p0 ^ 4 * (2 * C' * u) ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hT4 (Nat.mul_le_mul_left _ hD4))
        _ = E * u ^ 19 := by rw [hE]; ring
    have e1 : (2 * Bad.card) ^ 4 = 16 * Bad.card ^ 4 := by ring
    have e2 : U ^ 4 = u * u ^ 19 := by rw [hU, ← pow_mul, ← pow_succ']
    rw [e1, e2]
    calc 16 * Bad.card ^ 4 ≤ 16 * (E * u ^ 19) := Nat.mul_le_mul_left _ h4
      _ = (16 * E) * u ^ 19 := by ring
      _ < u * u ^ 19 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hu0 19)
  -- a good `n`
  obtain ⟨n, hnI, hnB⟩ : ∃ n ∈ Finset.Ioc (U / 2) U, n ∉ Bad := by
    refine Finset.exists_mem_notMem_of_card_lt_card ?_
    rw [Nat.card_Ioc]
    omega
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.1 hnI
  have hnN0 : N0 < n := by omega
  refine ⟨n, by omega, fun k m p q hp hnm hbal hlo hhi => ?_⟩
  have hm1 : n ^ 2 + 2 * n + 1 ≤ m ^ 2 := by
    have h1 : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm 2
    have h2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  rcases lt_or_ge k k0 with hk | hk
  · have := hL.monotone hk.le
    omega
  · have hrk := hk0 k hk
    set c := Nat.sqrt (L k) with hc
    have hcL : c ^ 2 ≤ L k := Nat.sqrt_le' _
    have hwk1 : w k ≤ (L k - c ^ 2) / 2 := min_le_left _ _
    have hwk2 : w k ≤ g k := min_le_right _ _
    have hlowk : L k ≤ c ^ 2 + c := hlow k
    have hcm : c < m := by
      by_contra h
      have : m ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left (not_lt.1 h) 2
      omega
    have hm2 : c ^ 2 + 2 * c + 1 ≤ m ^ 2 := by
      have h1 : (c + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hcm 2
      have h2 : (c + 1) ^ 2 = c ^ 2 + 2 * c + 1 := by ring
      omega
    have hcn : c < n ^ 2 := by omega
    have hcU : c ≤ U ^ 2 := hcn.le.trans (Nat.pow_le_pow_left hnhi 2)
    have hLk : L k ≤ 2 * U ^ 4 := by
      have h1 : c ^ 2 ≤ U ^ 4 := by
        have := Nat.pow_le_pow_left hcU 2
        rwa [← pow_mul] at this
      have h3 : U ^ 2 ≤ U ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have hkb : k ≤ 2 * C * u ^ 4 := by
      refine (Nat.pow_le_pow_iff_left (n := 5) (by norm_num)).1 ?_
      refine (hC k).trans ((Nat.mul_le_mul_left _ hLk).trans ?_)
      have e : U ^ 4 = (u ^ 4) ^ 5 := by rw [hU, ← pow_mul, ← pow_mul]
      rw [e, mul_pow (2 * C)]
      have h1 : 2 * C ≤ (2 * C) ^ 5 := Nat.le_self_pow (by norm_num) _
      calc C * (2 * (u ^ 4) ^ 5) = (2 * C) * (u ^ 4) ^ 5 := by ring
        _ ≤ (2 * C) ^ 5 * (u ^ 4) ^ 5 := Nat.mul_le_mul_right _ h1
    refine hnB ?_
    rw [hBad, Finset.mem_biUnion]
    refine ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hLk⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨L k - q, Finset.mem_Icc.2 ⟨by omega, ?_⟩, ?_⟩
    · have : L k - q ≤ g k := by omega
      exact this.trans (hgmono _ _ hkb)
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_range.2 hp, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hnhi⟩, m, hnm, ?_⟩⟩
    omega

lemma gaps_unbounded_of_sparse (L : ℕ → ℕ) (C : ℕ) (hC : ∀ k, k ^ 5 ≤ C * L k) :
    ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1) := by
  intro G
  by_contra h
  push Not at h
  have hlin : ∀ k, L k ≤ L 0 + G * k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := h k
      rw [Nat.mul_succ]
      omega
  set k := C * (L 0 + G) + 2 with hk
  have h1 := (hC k).trans (Nat.mul_le_mul_left C (hlin k))
  have h2 : C * (L 0 + G * k) ≤ (C * (L 0 + G)) * k := by
    have h3 : L 0 + G * k ≤ (L 0 + G) * k := by
      rw [add_mul]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _
    rw [mul_assoc]
    exact Nat.mul_le_mul_left C h3
  have h4 : (C * (L 0 + G)) * k < k ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h5 : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- If the distance to the square below does not tend to infinity, one shift is a square infinitely often. -/
lemma shifted_squares_of_not_tendsto (L : ℕ → ℕ) (h : ¬ Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop) :
    ∃ j : ℤ, Set.Infinite {k : ℕ | ∃ n : ℕ, (L k : ℤ) + j = (n : ℤ) ^ 2} := by
  rw [tendsto_atTop] at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  have hinf : Set.Infinite {k : ℕ | L k - Nat.sqrt (L k) ^ 2 < b} := by
    refine Nat.frequently_atTop_iff_infinite.1 ?_
    exact hb.mono fun k hk => hk
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Set.Infinite {k : ℕ | L k - Nat.sqrt (L k) ^ 2 = r} := by
    by_contra hc
    push Not at hc
    refine hinf ?_
    refine Set.Finite.subset ((Finset.range b).finite_toSet.biUnion fun r _ => hc r) fun k hk => ?_
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hk)) rfl
  refine ⟨-(r : ℤ), hr.mono fun k hk => ⟨Nat.sqrt (L k), ?_⟩⟩
  have h1 : Nat.sqrt (L k) ^ 2 ≤ L k := Nat.sqrt_le' _
  have h2 : L k = Nat.sqrt (L k) ^ 2 + r := by
    have : L k - Nat.sqrt (L k) ^ 2 = r := hk
    omega
  have h3 : (L k : ℤ) = (Nat.sqrt (L k) : ℤ) ^ 2 + r := by exact_mod_cast h2
  omega

lemma countable_of_not_tendsto (L : ℕ → ℕ) (hL : StrictMono L)
    (h : ¬ Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop) :
    Set.Countable {a | InA (dyseq L) sT a} := by
  obtain ⟨j, hj⟩ := shifted_squares_of_not_tendsto L h
  have hc : Set.Countable (Set.range fun x : ℤ × ℕ => ((x.1 : ℝ) / 2 ^ x.2)) := Set.countable_range _
  refine hc.mono fun a ha => ?_
  obtain ⟨r, z, hz⟩ := inA_dyadic_of_infinite_shifted_squares L hL j hj a ha
  exact ⟨(z, r), hz.symm⟩

/-- **Classification for fast sequences.** -/
theorem rig_iff_of_sparse (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (C : ℕ) (hC : ∀ k, k ^ 5 ≤ C * L k)
    (hlow : ∀ k, L k ≤ Nat.sqrt (L k) ^ 2 + Nat.sqrt (L k)) :
    Rig (dyseq L) ↔ Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop := by
  refine ⟨fun hrig => ?_, fun hr => rig_of_sparse L hL h2 C hC hr hlow⟩
  by_contra h
  obtain ⟨j, hj⟩ := shifted_squares_of_not_tendsto L h
  exact not_rig_of_infinite_shifted_squares L hL (gaps_unbounded_of_sparse L C hC) j hj hrig

/-- For these sequences rigidity means uncountably many coefficients. -/
theorem rig_iff_uncountable_of_sparse (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (C : ℕ)
    (hC : ∀ k, k ^ 5 ≤ C * L k) (hlow : ∀ k, L k ≤ Nat.sqrt (L k) ^ 2 + Nat.sqrt (L k)) :
    Rig (dyseq L) ↔ ¬ Set.Countable {a | InA (dyseq L) sT a} := by
  constructor
  · intro hrig hc
    obtain ⟨G, hG⟩ := (rig_iff_bounded_of_countable L hL hc).1 hrig
    obtain ⟨k, hk⟩ := gaps_unbounded_of_sparse L C hC (G + 1)
    have := hG k
    omega
  · intro hu
    refine (rig_iff_of_sparse L hL h2 C hC hlow).2 ?_
    by_contra h
    exact hu (countable_of_not_tendsto L hL h)

/-! ## Far windows -/

/-- Only infinitely many large jumps are needed. -/
theorem rig_of_far_windows (L w : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (hw : Tendsto w atTop atTop)
    (h : ∀ K0 : ℕ, ∃ K, K0 ≤ K ∧ ∀ k, K < k → ∀ j : ℕ, L k ≤ j ^ 2 + w k → j ^ 2 ≤ L k + L K ^ 2 → False) :
    Rig (dyseq L) := by
  refine rig_of_avoids_seq L w hL h2 hw fun p0 N => ?_
  obtain ⟨K, hK, hfar⟩ := h (N + p0)
  have hKL : K ≤ L K := hL.id_le K
  have hsq : L K ≤ L K ^ 2 := Nat.le_self_pow two_ne_zero _
  refine ⟨L K, by omega, fun k m p q hp hnm hbal hlo hhi => ?_⟩
  have hm1 : L K ^ 2 + 2 * L K + 1 ≤ m ^ 2 := by
    have h1 : (L K + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm 2
    have h3 : (L K + 1) ^ 2 = L K ^ 2 + 2 * L K + 1 := by ring
    omega
  have hk : K < k := by
    by_contra hc
    have := hL.monotone (not_lt.1 hc)
    omega
  exact hfar k hk m (by omega) (by omega)

/-! ## The sequence `4^k + k` -/

lemma pow_five_le (k : ℕ) : k ^ 5 ≤ 4 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases lt_or_ge k 4 with h | h
    · interval_cases k <;> norm_num
    · have h1 : (4 * (k + 1)) ^ 5 ≤ (5 * k) ^ 5 := Nat.pow_le_pow_left (by omega) 5
      rw [mul_pow, mul_pow] at h1
      norm_num only at h1
      have e : (4 : ℕ) ^ (k + 1 + 1) = 4 ^ (k + 1) * 4 := pow_succ 4 (k + 1)
      omega

/-- `δ_k = 2^(-(4^k+k))` (indexed here from `k + 1`) is rigid. -/
theorem rig_four_pow : Rig (dyseq fun k => 4 ^ (k + 1) + (k + 1)) := by
  have hsq : ∀ k : ℕ, (4 : ℕ) ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hlt : ∀ k : ℕ, k + 1 < 2 ^ (k + 1) := fun k => Nat.lt_two_pow_self
  have hsqrt : ∀ k : ℕ, Nat.sqrt (4 ^ (k + 1) + (k + 1)) = 2 ^ (k + 1) := fun k => by
    have := hlt k
    rw [hsq]
    exact Nat.sqrt_add_eq' _ (by omega)
  have hmono : StrictMono fun k : ℕ => 4 ^ (k + 1) + (k + 1) := fun a b hab => by
    have : (4 : ℕ) ^ (a + 1) ≤ 4 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only
    omega
  refine rig_of_sparse _ hmono (by norm_num) 1 (fun k => ?_) ?_ fun k => ?_
  · have h1 := pow_five_le k
    omega
  · have e : (fun k : ℕ => 4 ^ (k + 1) + (k + 1) - Nat.sqrt (4 ^ (k + 1) + (k + 1)) ^ 2) = fun k => k + 1 := by
      funext k
      rw [hsqrt, hsq]
      omega
    rw [e]
    exact tendsto_add_atTop_nat 1
  · have := hlt k
    rw [hsqrt, hsq]
    omega

end Three
end PVG
