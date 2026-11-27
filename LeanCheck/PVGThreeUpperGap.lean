import LeanCheck.PVGThreeClassify

/-!
# PVGthree: classification by the distance to the next square

`δ_k = 2^(-L_k)`, `c = Nat.sqrt L_k`, `D_k = (c+1)^2 - L_k`. If `k^(2s+1) ≤ C D_k^s` for some `s ≥ 1`
(that is, `D_k` is at least a constant times `k^(2+1/s)`), then `δ` is rigid iff `L_k - c^2 → ∞` iff
`A(δ)` is uncountable (`rig_iff_of_upper_gap`, `rig_iff_uncountable_of_upper_gap`).

The theorem and its proof are due to ChatGPT (audit of 27 November 2026); it strengthens
`rig_iff_of_sparse`. The new point is `card_sqdiff_large`: for `M > U^4` there is at most one `n ≤ U`
with `n^2 + M` a square. Sequences are indexed from `0`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

/-- For `M > U^4` at most one `n ≤ U` makes `n^2 + M` a square larger than `n^2`. -/
lemma card_sqdiff_large (U M : ℕ) (h : U ^ 4 < M) [DecidablePred fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M] :
    ((Finset.Icc 1 U).filter fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M).card ≤ 1 := by
  have key : ∀ n1 n2 m1 m2 : ℕ, n1 < n2 → n2 ≤ U → m1 ^ 2 = n1 ^ 2 + M → m2 ^ 2 = n2 ^ 2 + M → False := by
    intro n1 n2 m1 m2 h12 hU e1 e2
    have hm1 : U ^ 2 < m1 := by
      by_contra hc
      have h1 : m1 ^ 2 ≤ (U ^ 2) ^ 2 := Nat.pow_le_pow_left (not_lt.1 hc) 2
      have h2 : (U ^ 2) ^ 2 = U ^ 4 := by rw [← pow_mul]
      omega
    have hn : n1 ^ 2 < n2 ^ 2 := Nat.pow_lt_pow_left h12 two_ne_zero
    have hm : m1 < m2 := by
      by_contra hc
      have := Nat.pow_le_pow_left (not_lt.1 hc) 2
      omega
    have h3 : m1 ^ 2 + 2 * m1 + 1 ≤ m2 ^ 2 := by
      have h4 : (m1 + 1) ^ 2 ≤ m2 ^ 2 := Nat.pow_le_pow_left hm 2
      have h5 : (m1 + 1) ^ 2 = m1 ^ 2 + 2 * m1 + 1 := by ring
      omega
    have h6 : n2 ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hU 2
    omega
  refine Finset.card_le_one.2 fun n1 h1 n2 h2 => ?_
  obtain ⟨hI1, m1, _, e1⟩ := Finset.mem_filter.1 h1
  obtain ⟨hI2, m2, _, e2⟩ := Finset.mem_filter.1 h2
  rcases lt_trichotomy n1 n2 with hlt | heq | hgt
  · exact (key n1 n2 m1 m2 hlt (Finset.mem_Icc.1 hI2).2 e1 e2).elim
  · exact heq
  · exact (key n2 n1 m2 m1 hgt (Finset.mem_Icc.1 hI1).2 e2 e1).elim

/-- **Rigidity when the next square is far.** -/
theorem rig_of_upper_gap (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (s C : ℕ) (hs : 1 ≤ s)
    (hC : ∀ k, k ^ (2 * s + 1) ≤ C * ((Nat.sqrt (L k) + 1) ^ 2 - L k) ^ s)
    (hr : Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop) : Rig (dyseq L) := by
  classical
  have hC1 : 1 ≤ C := by
    by_contra h
    have h0 : C = 0 := by omega
    have := hC 1
    rw [h0, Nat.zero_mul, one_pow] at this
    omega
  have h6s : 6 * s ≠ 0 := by omega
  set g : ℕ → ℕ := fun k => Nat.findGreatest (fun j => j ^ (6 * s) ≤ k) k with hg
  have hg6 : ∀ k, g k ^ (6 * s) ≤ k := fun k =>
    Nat.findGreatest_spec (P := fun j => j ^ (6 * s) ≤ k) (m := 0) (Nat.zero_le _)
      (by rw [zero_pow h6s]; exact Nat.zero_le _)
  have hgmono : ∀ a b, a ≤ b → g a ≤ g b := fun a b hab =>
    Nat.le_findGreatest ((Nat.findGreatest_le _).trans hab) ((hg6 a).trans hab)
  set w : ℕ → ℕ := fun k => min ((L k - Nat.sqrt (L k) ^ 2) / 2) (g k) with hw
  have hwtop : Tendsto w atTop atTop := by
    refine tendsto_atTop.2 fun t => ?_
    filter_upwards [hr.eventually (eventually_ge_atTop (2 * t)), eventually_ge_atTop (t ^ (6 * s))] with k h1 h3
    refine le_min (by omega) (Nat.le_findGreatest ?_ h3)
    exact (Nat.le_self_pow h6s t).trans h3
  refine rig_of_avoids_seq L w hL h2 hwtop fun p0 N => ?_
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hr.eventually (eventually_ge_atTop (2 * p0 + 2)))
  set e := 6 * s + 3 with he
  obtain ⟨C', hC'1, hC'⟩ := card_divisors_pow_le (4 * e) (by omega)
  set N0 := max N (L k0 + p0 + 1) with hN0
  obtain ⟨u, hu1, hu2⟩ : ∃ u : ℕ, 4 * C ^ 2 * C' * p0 + 1 ≤ u ∧ 2 * N0 + 2 ≤ u :=
    ⟨4 * C ^ 2 * C' * p0 + 2 * N0 + 3, by omega, by omega⟩
  have hu0 : 0 < u := by omega
  set U := u ^ e with hU
  have huU : u ≤ U := Nat.le_self_pow (by omega) u
  set Ks := Finset.range (C * u ^ (6 * s) + 1) with hKs
  set T := C * u with hT
  set Bad : Finset ℕ := Ks.biUnion fun k => (Finset.Icc 1 T).biUnion fun t => (Finset.range p0).biUnion fun p =>
    (Finset.Icc 1 U).filter fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + (L k - t - p) with hBad
  -- at most `C' u` solutions for each `M`
  have hcount : ∀ M : ℕ, ((Finset.Icc 1 U).filter fun n => ∃ m, n < m ∧ m ^ 2 = n ^ 2 + M).card ≤ C' * u := by
    intro M
    have h1 : 1 ≤ C' * u := Nat.mul_pos hC'1 hu0
    rcases lt_or_ge (U ^ 4) M with hM | hM
    · exact (card_sqdiff_large U M hM).trans h1
    refine (card_sqdiff_le U M).trans ?_
    rcases eq_or_ne M 0 with h0 | h0
    · simp [h0]
    refine (Nat.pow_le_pow_iff_left (n := 4 * e) (by omega)).1 ?_
    refine (hC' M h0).trans ?_
    have e1 : U ^ 4 = u ^ (4 * e) := by rw [hU, ← pow_mul, mul_comm e 4]
    rw [mul_pow C' u]
    exact Nat.mul_le_mul (Nat.le_self_pow (by omega) C') (e1 ▸ hM)
  have hcard : Bad.card ≤ (2 * C * u ^ (6 * s)) * (T * (p0 * (C' * u))) := by
    have hKc : Ks.card ≤ 2 * C * u ^ (6 * s) := by
      rw [hKs, Finset.card_range, mul_assoc, two_mul]
      exact Nat.add_le_add_left (Nat.mul_pos hC1 (pow_pos hu0 _)) _
    refine (Finset.card_biUnion_le_card_mul _ _ (T * (p0 * (C' * u))) fun k _ => ?_).trans
      (Nat.mul_le_mul_right _ hKc)
    refine (Finset.card_biUnion_le_card_mul _ _ (p0 * (C' * u)) fun t _ => ?_).trans
      (le_of_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel]))
    refine (Finset.card_biUnion_le_card_mul _ _ (C' * u) fun p _ => hcount _).trans
      (le_of_eq (by rw [Finset.card_range]))
  have hsmall : 2 * Bad.card < U := by
    have h1 : 2 * Bad.card ≤ (4 * C ^ 2 * C' * p0) * u ^ (6 * s + 2) := by
      refine (Nat.mul_le_mul_left 2 hcard).trans (le_of_eq ?_)
      rw [hT, pow_add]
      ring
    have h3 : U = u * u ^ (6 * s + 2) := by rw [hU, he, ← pow_succ']
    rw [h3]
    exact h1.trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hu0 _))
  obtain ⟨n, hnI, hnB⟩ : ∃ n ∈ Finset.Ioc (U / 2) U, n ∉ Bad := by
    refine Finset.exists_mem_notMem_of_card_lt_card ?_
    rw [Nat.card_Ioc]
    omega
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.1 hnI
  have hnN0 : N0 < n := by omega
  refine ⟨n, by omega, fun k m p q hp hnm hbal hlo hhi => ?_⟩
  have hm1 : n ^ 2 + 2 * n + 1 ≤ m ^ 2 := by
    have h1 : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm 2
    have h3 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  rcases lt_or_ge k k0 with hk | hk
  · have := hL.monotone hk.le
    omega
  · have hrk := hk0 k hk
    set c := Nat.sqrt (L k) with hc
    have hcL : c ^ 2 ≤ L k := Nat.sqrt_le' _
    have hLc : L k < (c + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hwk1 : w k ≤ (L k - c ^ 2) / 2 := min_le_left _ _
    have hwk2 : w k ≤ g k := min_le_right _ _
    have hcm : c < m := by
      by_contra h
      have : m ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left (not_lt.1 h) 2
      omega
    have hm2 : (c + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hcm 2
    have hD : (c + 1) ^ 2 - L k ≤ U ^ 2 := by
      have h1 : (c + 1) ^ 2 - L k < n ^ 2 := by omega
      exact h1.le.trans (Nat.pow_le_pow_left hnhi 2)
    have hkb : k ≤ C * u ^ (6 * s) := by
      refine (Nat.pow_le_pow_iff_left (n := 2 * s + 1) (by omega)).1 ?_
      refine (hC k).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD s)).trans ?_)
      have e1 : (U ^ 2) ^ s = (u ^ (6 * s)) ^ (2 * s + 1) := by
        rw [hU, he, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [e1, mul_pow C]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) C)
    have htT : L k - q ≤ T := by
      have h1 : L k - q ≤ g (C * u ^ (6 * s)) := by
        have : L k - q ≤ g k := by omega
        exact this.trans (hgmono _ _ hkb)
      refine h1.trans ((Nat.pow_le_pow_iff_left h6s).1 ?_)
      refine (hg6 _).trans ?_
      rw [hT, mul_pow C u]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow h6s C)
    refine hnB ?_
    rw [hBad, Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.2 (by omega), ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨L k - q, Finset.mem_Icc.2 ⟨by omega, htT⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_range.2 hp, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hnhi⟩, m, hnm, ?_⟩⟩
    omega

lemma gaps_unbounded_of_pow (L : ℕ → ℕ) (B : ℕ) (hB : ∀ k, k ^ 4 ≤ B * L k) :
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
  set k := B * (L 0 + G) + 2 with hk
  have h1 := (hB k).trans (Nat.mul_le_mul_left B (hlin k))
  have h2 : B * (L 0 + G * k) ≤ (B * (L 0 + G)) * k := by
    have h3 : L 0 + G * k ≤ (L 0 + G) * k := by
      rw [add_mul]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _
    rw [mul_assoc]
    exact Nat.mul_le_mul_left B h3
  have h4 : (B * (L 0 + G)) * k < k ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h5 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

lemma four_of_upper_gap (L : ℕ → ℕ) (h2 : ∀ k, 2 ≤ L k) (s C : ℕ) (hs : 1 ≤ s)
    (hC : ∀ k, k ^ (2 * s + 1) ≤ C * ((Nat.sqrt (L k) + 1) ^ 2 - L k) ^ s) :
    ∀ k, k ^ 4 ≤ (9 * C ^ 2) * L k := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [hk]
  set c := Nat.sqrt (L k) with hc
  have hcL : c ^ 2 ≤ L k := Nat.sqrt_le' _
  have hc1 : 1 ≤ c := by
    rw [hc, Nat.le_sqrt']
    have := h2 k
    omega
  set D := (c + 1) ^ 2 - L k with hD
  have hD3 : D ≤ 3 * c := by
    have : (c + 1) ^ 2 = c ^ 2 + 2 * c + 1 := by ring
    omega
  have hD9 : D ^ 2 ≤ 9 * L k := by
    have h1 : D ^ 2 ≤ (3 * c) ^ 2 := Nat.pow_le_pow_left hD3 2
    have h3 : (3 * c) ^ 2 = 9 * c ^ 2 := by ring
    omega
  refine (Nat.pow_le_pow_iff_left (n := s) (by omega)).1 ?_
  have h4 : (k ^ 4) ^ s ≤ (k ^ (2 * s + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right hk (by omega)
  have h5 : (k ^ (2 * s + 1)) ^ 2 ≤ C ^ 2 * (D ^ 2) ^ s := by
    have := Nat.pow_le_pow_left (hC k) 2
    rwa [mul_pow, ← pow_mul D s 2, mul_comm s 2, pow_mul D 2 s] at this
  refine h4.trans (h5.trans ?_)
  have h6 : C ^ 2 ≤ (C ^ 2) ^ s := Nat.le_self_pow (by omega) _
  calc C ^ 2 * (D ^ 2) ^ s ≤ (C ^ 2) ^ s * (9 * L k) ^ s := Nat.mul_le_mul h6 (Nat.pow_le_pow_left hD9 s)
    _ = (9 * C ^ 2 * L k) ^ s := by rw [← mul_pow]; congr 1; ring

/-- **Classification when the next square is far.** -/
theorem rig_iff_of_upper_gap (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (s C : ℕ) (hs : 1 ≤ s)
    (hC : ∀ k, k ^ (2 * s + 1) ≤ C * ((Nat.sqrt (L k) + 1) ^ 2 - L k) ^ s) :
    Rig (dyseq L) ↔ Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop := by
  refine ⟨fun hrig => ?_, fun hr => rig_of_upper_gap L hL h2 s C hs hC hr⟩
  by_contra h
  obtain ⟨j, hj⟩ := shifted_squares_of_not_tendsto L h
  have h2' : ∀ k, 2 ≤ L k := fun k => h2.trans (hL.monotone (Nat.zero_le k))
  exact not_rig_of_infinite_shifted_squares L hL
    (gaps_unbounded_of_pow L _ (four_of_upper_gap L h2' s C hs hC)) j hj hrig

theorem rig_iff_uncountable_of_upper_gap (L : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (s C : ℕ) (hs : 1 ≤ s)
    (hC : ∀ k, k ^ (2 * s + 1) ≤ C * ((Nat.sqrt (L k) + 1) ^ 2 - L k) ^ s) :
    Rig (dyseq L) ↔ ¬ Set.Countable {a | InA (dyseq L) sT a} := by
  have h2' : ∀ k, 2 ≤ L k := fun k => h2.trans (hL.monotone (Nat.zero_le k))
  constructor
  · intro hrig hc
    obtain ⟨G, hG⟩ := (rig_iff_bounded_of_countable L hL hc).1 hrig
    obtain ⟨k, hk⟩ := gaps_unbounded_of_pow L _ (four_of_upper_gap L h2' s C hs hC) (G + 1)
    have := hG k
    omega
  · intro hu
    refine (rig_iff_of_upper_gap L hL h2 s C hs hC).2 ?_
    by_contra h
    exact hu (countable_of_not_tendsto L hL h)

end Three
end PVG
