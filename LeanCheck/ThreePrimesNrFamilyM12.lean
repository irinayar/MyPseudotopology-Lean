import LeanCheck.ThreePrimesExactM5

/-!
# ThreePrimesNrFamilyM12: the counting height does not bound the least ball element avoiding `r`

`N_r(δ)` is the least positive `x` in the ball `InBall S δ` with `r ∤ x`; the statements below are
about every such `x`.  `D_S(δ) = Dvis S δ`, `c* = cstarM5 S (a_p(δ)) m`.

* `nr23_isLeastM12`: for `S = {2, 11777}`, `δ = 1/32`, `r = 23` the minimum is `32834048`.
* `nr23_counterM12`: there `D = 512`, `c* = 2`, and every such `x` exceeds `D · 32^(c*) = 524288`.
* `nrfamily_lowerM12`: for `δ = 2^(1-2a)`, `S = {2, q}`, every such `x` exceeds `D q / (2e)`,
  `e = |q - r 2^(a²)|`.
* `cstar_leM12`: the counting index of these pairs satisfies `c* ≤ c` when `c² + c + 1 > 2a`, `c ≤ a`.
* `nrfamily_powerM12`, `nrfamily_not_boundedM12`: assuming the theorem of Baker, Harman and Pintz
  (`BHPstatement`, **not** proved here), `x > D^1.475 / 4` and `x > D m^(C c*)` for suitable pairs.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-! ## From the ball to integer inequalities -/

lemma exists_nearM12 {x : ℤ} {p n : ℕ} (hn : 1 ≤ n) (hp : 0 < p)
    (h : Pn (sqScales p) x < 1 / 32) :
    ∃ j : ℤ, -((p ^ (n ^ 2) : ℕ) : ℤ) < 32 * (x - j * ((p ^ (n ^ 2) : ℕ) : ℤ)) ∧
      32 * (x - j * ((p ^ (n ^ 2) : ℕ) : ℤ)) < ((p ^ (n ^ 2) : ℕ) : ℤ) := by
  have h1 := lt_of_le_of_lt (le_Pn (mem_sqScales (ℓ := p) hn) x) h
  rw [nrm_eq, abs_lt] at h1
  have hQ0 : 0 < p ^ (n ^ 2) := pow_pos hp _
  generalize p ^ (n ^ 2) = Q at h1 hQ0 ⊢
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have e : (x : ℝ) / Q * Q = x := by field_simp
  refine ⟨round ((x : ℝ) / Q), ?_, ?_⟩
  · have h2 := mul_lt_mul_of_pos_right h1.1 hQ
    rw [sub_mul, e] at h2
    have h3 : -(Q : ℝ) < 32 * ((x : ℝ) - round ((x : ℝ) / Q) * Q) := by linarith
    exact_mod_cast h3
  · have h2 := mul_lt_mul_of_pos_right h1.2 hQ
    rw [sub_mul, e] at h2
    have h3 : 32 * ((x : ℝ) - round ((x : ℝ) / Q) * Q) < (Q : ℝ) := by linarith
    exact_mod_cast h3

lemma aThr_eqM12 {p a : ℕ} {δ : ℝ} (h1 : 1 / (p : ℝ) ^ (2 * a + 1) < δ)
    (h2 : ∀ b < a, δ ≤ 1 / (p : ℝ) ^ (2 * b + 1)) : aThr p δ = a := by
  unfold aThr
  refine le_antisymm (Nat.sInf_le h1) (le_csInf ⟨a, h1⟩ fun b hb => ?_)
  by_contra h
  exact absurd hb (not_lt.2 (h2 b (not_le.1 h)))

/-! ## The example `S = {2, 11777}` -/

lemma aThr_two_32M12 : aThr 2 (1 / 32) = 3 := by
  refine aThr_eqM12 (by norm_num) fun b hb => ?_
  interval_cases b <;> norm_num

lemma aThr_big_32M12 : aThr 11777 (1 / 32) = 0 :=
  aThr_eqM12 (by norm_num) fun b hb => absurd hb (Nat.not_lt_zero b)

lemma dvis_nr23M12 : Dvis {2, 11777} (1 / 32) = 512 := by
  unfold Dvis
  rw [Finset.prod_pair (by norm_num), aThr_two_32M12, aThr_big_32M12]
  norm_num

lemma prime_11777M12 : Nat.Prime 11777 := by norm_num

lemma table_lowM12 : ∀ j < 17, ∀ i < 7, 3 < 128 * j + i →
    (512 * (128 * j + i - 3) + 368) % 11777 ≤ 736 → (128 * j + i - 3) % 23 = 0 := by
  decide

lemma table_highM12 : ∀ k < 6, ∀ i < 7, 63489 ≤ 128 * (496 + k) + i - 3 →
    128 * (496 + k) + i - 3 < 64129 →
    (512 * (128 * (496 + k) + i - 3) + 368) % 11777 ≤ 736 →
    (128 * (496 + k) + i - 3) % 23 = 0 := by
  decide

lemma mem_nr23M12 : InBall {2, 11777} (1 / 32) 32834048 := by
  intro p hp
  refine lt_of_le_of_lt (Pn_le (sq_nonempty p) (c := 3 / 128) ?_) (by norm_num)
  rintro q ⟨n, hn, rfl⟩
  have key : ∀ (Q : ℕ) (j : ℤ), |((32834048 : ℤ) : ℝ) / (Q : ℝ) - j| ≤ 3 / 128 →
      nrm (((32834048 : ℤ) : ℝ) / (Q : ℝ)) ≤ 3 / 128 := by
    intro Q j h
    rw [nrm_eq]
    exact le_trans (round_le _ j) h
  have tail : ∀ Q : ℕ, 68719476736 ≤ Q → nrm (((32834048 : ℤ) : ℝ) / (Q : ℝ)) ≤ 3 / 128 := by
    intro Q hQ
    have hQ' : (68719476736 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le (by norm_num) hQ'
    refine le_trans (nrm_le_abs _) ?_
    rw [abs_of_nonneg (div_nonneg (by norm_num) hQ0.le), div_le_iff₀ hQ0]
    push_cast
    linarith
  rcases Finset.mem_insert.1 hp with rfl | hp
  · by_cases h6 : 6 ≤ n
    · refine tail _ ?_
      have h1 : 36 ≤ n ^ 2 := by nlinarith
      calc (68719476736 : ℕ) = 2 ^ 36 := by norm_num
        _ ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
    · have h5 : n ≤ 5 := by omega
      interval_cases n
      · exact key _ 16417024 (by norm_num)
      · exact key _ 2052128 (by norm_num)
      · exact key _ 64129 (by norm_num)
      · exact key _ 501 (by norm_num [abs_le])
      · exact key _ 1 (by norm_num [abs_le])
  · rw [Finset.mem_singleton] at hp
    subst hp
    by_cases h2 : 2 ≤ n
    · refine tail _ ?_
      have h1 : 4 ≤ n ^ 2 := by nlinarith
      calc (68719476736 : ℕ) ≤ 11777 ^ 4 := by norm_num
        _ ≤ 11777 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
    · have h1 : n = 1 := by omega
      subst h1
      exact key _ 2788 (by norm_num [abs_le])

/-- **The exact minimum** `N_23(1/32) = 32834048` for `S = {2, 11777}`. -/
theorem nr23_isLeastM12 :
    IsLeast {x : ℤ | 0 < x ∧ InBall {2, 11777} (1 / 32) x ∧ ¬ (23 : ℤ) ∣ x} 32834048 := by
  refine ⟨⟨by norm_num, mem_nr23M12, by norm_num⟩, ?_⟩
  rintro x ⟨hx0, hx, h23⟩
  by_contra hlt
  have hS : ∀ p ∈ ({2, 11777} : Finset ℕ), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact Nat.prime_two
    · rw [Finset.mem_singleton] at hp
      rw [hp]
      exact prime_11777M12
  have hD := forced hS (by norm_num) hx
  rw [dvis_nr23M12] at hD
  obtain ⟨y, hy⟩ := hD
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, y = (s : ℤ) := ⟨y.toNat, by push_cast at hy; omega⟩
  have hs0 : 0 < s := by push_cast at hy; omega
  have hs1 : s < 64129 := by push_cast at hy; omega
  have h2 := hx 2 (by simp)
  have hq := hx 11777 (by simp)
  obtain ⟨j4, h4a, h4b⟩ := exists_nearM12 (n := 4) (by norm_num) (by norm_num) h2
  obtain ⟨j5, h5a, h5b⟩ := exists_nearM12 (n := 5) (by norm_num) (by norm_num) h2
  obtain ⟨j1, h1a, h1b⟩ := exists_nearM12 (n := 1) (by norm_num) (by norm_num) hq
  have e4 : ((2 ^ (4 ^ 2) : ℕ) : ℤ) = 65536 := by norm_num
  have e5 : ((2 ^ (5 ^ 2) : ℕ) : ℤ) = 33554432 := by norm_num
  have e1 : ((11777 ^ (1 ^ 2) : ℕ) : ℤ) = 11777 := by norm_num
  rw [e4] at h4a h4b
  rw [e5] at h5a h5b
  rw [e1] at h1a h1b
  push_cast at hy
  rw [hy] at h4a h4b h5a h5b h1a h1b
  have hcond : (512 * s + 368) % 11777 ≤ 736 := by
    set w : ℤ := 512 * (s : ℤ) - j1 * 11777 with hw
    have hw1 : -368 ≤ w := by omega
    have hw2 : w ≤ 368 := by omega
    have h1 : (512 * (s : ℤ) + 368) % 11777 = w + 368 := by
      have e : 512 * (s : ℤ) + 368 = (w + 368) + j1 * 11777 := by rw [hw]; ring
      rw [e, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    have h2 : (512 * (s : ℤ) + 368) % 11777 ≤ 736 := by rw [h1]; linarith
    exact_mod_cast h2
  have hrange : s < 2048 ∨ 63489 ≤ s := by
    have h5 : j5 = 0 ∨ j5 = 1 := by omega
    rcases h5 with rfl | rfl <;> omega
  obtain ⟨j, i, hi, hsj⟩ : ∃ j i : ℕ, i < 7 ∧ s + 3 = 128 * j + i := by
    have h6 : 0 ≤ j4 := by omega
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, j4 = (j : ℤ) := ⟨j4.toNat, by omega⟩
    exact ⟨j, s + 3 - 128 * j, by omega, by omega⟩
  have hs : s = 128 * j + i - 3 := by omega
  have hmod : s % 23 = 0 := by
    rcases hrange with h | h
    · have hj : j < 17 := by omega
      by_cases h3 : 3 < 128 * j + i
      · rw [hs] at hcond ⊢
        exact table_lowM12 j hj i hi h3 hcond
      · omega
    · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 6 ∧ j = 496 + k := ⟨j - 496, by omega, by omega⟩
      rw [hs] at hcond hs1 ⊢
      exact table_highM12 k hk i hi (hs ▸ h) hs1 hcond
  apply h23
  rw [hy]
  have : (23 : ℤ) ∣ (s : ℤ) := by omega
  exact Dvd.dvd.mul_left this _

lemma cstar_nr23M12 : cstarM5 {2, 11777} (fun p => aThr p (1 / 32)) 32 = 2 := by
  have hD : Dprod {2, 11777} (fun p => aThr p (1 / 32)) = 512 := dvis_nr23M12
  have h2a : aThr 2 (1 / 32) < 4 := by rw [aThr_two_32M12]; norm_num
  have hqa : aThr 11777 (1 / 32) < 1 := by rw [aThr_big_32M12]; norm_num
  have hup : (CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 (32 ^ 2)).card ≤ 2 := by
    have hsub : CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 (32 ^ 2) ⊆ {(2, 4), (11777, 1)} := by
      intro c hc
      unfold CCset at hc
      rw [Finset.mem_filter, Finset.mem_product, hD] at hc
      obtain ⟨⟨h1, _⟩, h3, h4⟩ := hc
      obtain ⟨p, n⟩ := c
      simp only at h1 h3 h4
      rcases Finset.mem_insert.1 h1 with rfl | h1
      · rw [aThr_two_32M12] at h3
        have hn : n < 5 := by
          by_contra h
          have h5 : 2 ^ (5 ^ 2) ≤ 2 ^ (n ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
          have h6 := le_trans h5 h4
          norm_num at h6
        have : n = 4 := by omega
        subst this
        simp
      · rw [Finset.mem_singleton] at h1
        subst h1
        rw [aThr_big_32M12] at h3
        have hn : n < 2 := by
          by_contra h
          have h5 : 11777 ^ (2 ^ 2) ≤ 11777 ^ (n ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
          have h6 := le_trans h5 h4
          norm_num at h6
        have : n = 1 := by omega
        subst this
        simp
    exact le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
  unfold cstarM5
  refine le_antisymm (Nat.sInf_le hup) (le_csInf ⟨2, hup⟩ fun c hc => ?_)
  by_contra h
  have hc' : (CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 (32 ^ c)).card ≤ c := hc
  have hmemq : ∀ N, 1 ≤ N → (11777, 1) ∈ CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 N := by
    intro N hN
    refine mem_ccset (by norm_num) (by simp) hqa ?_
    rw [hD]
    calc 11777 ^ (1 ^ 2) ≤ 32 * 512 * 1 := by norm_num
      _ ≤ 32 * 512 * N := Nat.mul_le_mul_left _ hN
  have hc01 : c = 0 ∨ c = 1 := by omega
  rcases hc01 with rfl | rfl
  · have := Finset.card_pos.2 ⟨_, hmemq (32 ^ 0) (by norm_num)⟩
    omega
  · have hmem2 : (2, 4) ∈ CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 (32 ^ 1) := by
      refine mem_ccset (by norm_num) (by simp) h2a ?_
      rw [hD]
      norm_num
    have hsub : ({(2, 4), (11777, 1)} : Finset (ℕ × ℕ)) ⊆
        CCset {2, 11777} (fun p => aThr p (1 / 32)) 32 (32 ^ 1) := by
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hmem2
      · rw [Finset.mem_singleton] at hy
        rw [hy]
        exact hmemq _ (by norm_num)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair (by decide)] at h2
    omega

/-- **The counting height does not bound `N_r`.** -/
theorem nr23_counterM12 :
    Dvis {2, 11777} (1 / 32) = 512 ∧ cstarM5 {2, 11777} (fun p => aThr p (1 / 32)) 32 = 2 ∧
      ∀ x : ℤ, 0 < x → InBall {2, 11777} (1 / 32) x → ¬ (23 : ℤ) ∣ x →
        (Dvis {2, 11777} (1 / 32) : ℤ) *
          32 ^ cstarM5 {2, 11777} (fun p => aThr p (1 / 32)) 32 < x := by
  refine ⟨dvis_nr23M12, cstar_nr23M12, fun x h0 hx h23 => ?_⟩
  have h := nr23_isLeastM12.2 ⟨h0, hx, h23⟩
  rw [dvis_nr23M12, cstar_nr23M12]
  push_cast
  omega

/-! ## The family `S = {2, q}`, `δ = 2^(1-2a)` -/

lemma aThr_two_famM12 {a : ℕ} (ha : 1 ≤ a) : aThr 2 (1 / 2 ^ (2 * a - 1)) = a := by
  refine aThr_eqM12 ?_ fun b hb => ?_
  · push_cast
    exact one_div_lt_one_div_of_lt (by positivity) (pow_lt_pow_right₀ one_lt_two (by omega))
  · push_cast
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ one_le_two (by omega))

lemma aThr_q_famM12 {a q : ℕ} (hq : 2 ^ (2 * a - 1) < q) : aThr q (1 / 2 ^ (2 * a - 1)) = 0 := by
  refine aThr_eqM12 ?_ fun b hb => absurd hb (Nat.not_lt_zero b)
  rw [Nat.mul_zero, Nat.zero_add, pow_one]
  exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast hq)

lemma dvis_famM12 {a q : ℕ} (ha : 1 ≤ a) (hq : 2 ^ (2 * a - 1) < q) (hq2 : q ≠ 2) :
    Dvis {2, q} (1 / 2 ^ (2 * a - 1)) = 2 ^ (a ^ 2) := by
  unfold Dvis
  rw [Finset.prod_pair (Ne.symm hq2), aThr_two_famM12 ha, aThr_q_famM12 hq]
  simp

/-- **A family of pairs.** Every ball element not divisible by `r` exceeds `D q / (2e)`. -/
theorem nrfamily_lowerM12 {r q a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hra : r ≤ 2 ^ (2 * a - 2))
    (hq : q.Prime) (hqm : 2 ^ (2 * a - 1) < q) {x : ℤ} (hx0 : 0 < x)
    (hx : InBall {2, q} (1 / 2 ^ (2 * a - 1)) x) (hrx : ¬ (r : ℤ) ∣ x) :
    (2 : ℝ) ^ (a ^ 2) * q / (2 * |(q : ℝ) - r * 2 ^ (a ^ 2)|) < x := by
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have ha : 2 ≤ a := by
    by_contra h
    have h0 : 2 * a - 2 = 0 := by omega
    rw [h0, pow_zero] at hra
    omega
  have hq2 : q ≠ 2 := by
    have : 2 ^ 1 ≤ 2 ^ (2 * a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hS : ∀ p ∈ ({2, q} : Finset ℕ), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact Nat.prime_two
    · rw [Finset.mem_singleton] at hp
      rw [hp]
      exact hq
  have hδ : (0 : ℝ) < 1 / 2 ^ (2 * a - 1) := by positivity
  have hD := forced hS hδ hx
  rw [dvis_famM12 (by omega) hqm hq2] at hD
  obtain ⟨s, hs⟩ := hD
  push_cast at hs
  have hs0 : 0 < s := by
    refine pos_of_mul_pos_right (a := (2 : ℤ) ^ (a ^ 2)) ?_ (by positivity)
    rw [← hs]
    exact hx0
  have hrs : ¬ (r : ℤ) ∣ s := fun h => hrx (by rw [hs]; exact Dvd.dvd.mul_left h _)
  have hne : q ≠ r * 2 ^ (a ^ 2) := by
    intro h
    have h1 : 2 ^ (a ^ 2) ≠ 1 := by
      have : 2 ^ 1 ≤ 2 ^ (a ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      omega
    exact Nat.not_prime_mul (by omega) h1 (h ▸ hq)
  set e : ℝ := (q : ℝ) - r * 2 ^ (a ^ 2) with he
  have he0 : e ≠ 0 := by
    rw [he, sub_ne_zero]
    exact_mod_cast hne
  have heabs : 0 < |e| := abs_pos.2 he0
  by_contra hcon
  rw [not_lt] at hcon
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hxR : (x : ℝ) = 2 ^ (a ^ 2) * s := by exact_mod_cast hs
  have hes : 2 * |e| * s ≤ q := by
    rw [le_div_iff₀ (mul_pos two_pos heabs), hxR] at hcon
    have h2 : (0 : ℝ) < 2 ^ (a ^ 2) := by positivity
    have h3 : (2 : ℝ) ^ (a ^ 2) * (2 * |e| * s) ≤ 2 ^ (a ^ 2) * q := by
      calc (2 : ℝ) ^ (a ^ 2) * (2 * |e| * s) = 2 ^ (a ^ 2) * s * (2 * |e|) := by ring
        _ ≤ 2 ^ (a ^ 2) * q := hcon
    exact le_of_mul_le_mul_left h3 h2
  have hlow : 1 / (r : ℝ) ≤ nrm ((s : ℝ) / r) := by
    rw [nrm_eq]
    set b := round ((s : ℝ) / r) with hb
    have h1 : (s : ℝ) / r - b = ((s - b * r : ℤ) : ℝ) / r := by
      push_cast
      field_simp
    have h2 : s - b * (r : ℤ) ≠ 0 := by
      intro h
      exact hrs ⟨b, by rw [mul_comm]; omega⟩
    have h3 : (1 : ℝ) ≤ |((s - b * r : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h2
    rw [h1, abs_div, abs_of_pos hrR]
    exact div_le_div_of_nonneg_right h3 hrR.le
  have hcoord : nrm ((x : ℝ) / q) < 1 / 2 ^ (2 * a - 1) := by
    have h1 := le_Pn (mem_sqScales (ℓ := q) (n := 1) le_rfl) x
    have h2 := hx q (by simp)
    have h3 : q ^ (1 ^ 2) = q := by simp
    rw [h3] at h1
    exact lt_of_le_of_lt h1 h2
  have hsplit : (s : ℝ) / r = (x : ℝ) / q + e * s / (r * q) := by
    rw [hxR, he]
    field_simp
    ring
  have herr : |e * s / (r * q)| ≤ 1 / (2 * r) := by
    rw [abs_div, abs_mul, abs_of_pos hsR, abs_of_pos (mul_pos hrR hqR),
      div_le_div_iff₀ (mul_pos hrR hqR) (mul_pos two_pos hrR)]
    have := mul_le_mul_of_nonneg_left hes hrR.le
    linarith
  have h4 : 1 / (r : ℝ) ≤ nrm ((x : ℝ) / q) + 1 / (2 * r) := by
    refine le_trans hlow ?_
    rw [hsplit]
    exact le_trans (nrm_add_le _ _) (add_le_add le_rfl (le_trans (nrm_le_abs _) herr))
  have h5 : 1 / (2 ^ (2 * a - 1) : ℝ) ≤ 1 / (2 * r) := by
    refine one_div_le_one_div_of_le (mul_pos two_pos hrR) ?_
    have h6 : 2 * r ≤ 2 ^ (2 * a - 1) := by
      have h7 : 2 ^ (2 * a - 1) = 2 * 2 ^ (2 * a - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    exact_mod_cast h6
  have h8 : 1 / (r : ℝ) = 1 / (2 * r) + 1 / (2 * r) := by
    field_simp
    ring
  linarith

/-- **The counting index of these pairs.** -/
lemma cstar_leM12 {q a c : ℕ} (ha : 1 ≤ a) (hqD : 2 ^ (a ^ 2) < q) (hc : 2 * a < c ^ 2 + c + 1)
    (hca : c ≤ a) :
    cstarM5 {2, q} (fun p => aThr p (1 / 2 ^ (2 * a - 1))) (2 ^ (2 * a - 1)) ≤ c := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hk : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  have hmD : 2 ^ (2 * (b + 1) - 1) ≤ 2 ^ ((b + 1) ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (by rw [hk]; nlinarith)
  have hqm : 2 ^ (2 * (b + 1) - 1) < q := lt_of_le_of_lt hmD hqD
  have hq2 : q ≠ 2 := by
    have : 2 ^ 1 ≤ 2 ^ ((b + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have hD : Dprod {2, q} (fun p => aThr p (1 / 2 ^ (2 * (b + 1) - 1))) = 2 ^ ((b + 1) ^ 2) :=
    dvis_famM12 ha hqm hq2
  have hc1 : 1 ≤ c := by
    by_contra h
    have : c = 0 := by omega
    subst this
    omega
  refine cstarM5_le ?_
  have hsub : CCset {2, q} (fun p => aThr p (1 / 2 ^ (2 * (b + 1) - 1))) (2 ^ (2 * (b + 1) - 1))
        ((2 ^ (2 * (b + 1) - 1)) ^ c)
      ⊆ (Finset.Ico 1 c).image (fun j => (2, b + 1 + j)) ∪ {(q, 1)} := by
    intro y hy
    unfold CCset at hy
    rw [Finset.mem_filter, Finset.mem_product, hD] at hy
    obtain ⟨⟨h1, _⟩, h3, h4⟩ := hy
    obtain ⟨p, n⟩ := y
    simp only at h1 h3 h4
    have hprod : 2 ^ (2 * (b + 1) - 1) * 2 ^ ((b + 1) ^ 2) * (2 ^ (2 * (b + 1) - 1)) ^ c
        = 2 ^ ((b + 1) ^ 2 + (c + 1) * (2 * b + 1)) := by
      rw [hk, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    rw [hprod] at h4
    rcases Finset.mem_insert.1 h1 with rfl | h1
    · rw [aThr_two_famM12 ha] at h3
      have h5 : n ^ 2 ≤ (b + 1) ^ 2 + (c + 1) * (2 * b + 1) :=
        (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
      have h6 : n < b + 1 + c := by
        by_contra h
        have h7 : (b + 1 + c) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h8 := le_trans h7 h5
        nlinarith
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨n - (b + 1), ?_, ?_⟩)
      · rw [Finset.mem_Ico]
        omega
      · congr 1
        omega
    · rw [Finset.mem_singleton] at h1
      subst h1
      rw [aThr_q_famM12 hqm] at h3
      have hn : n < 2 := by
        by_contra h
        have h5 : p ^ (2 ^ 2) ≤ p ^ (n ^ 2) :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (by omega) 2)
        have h6 : (2 ^ ((b + 1) ^ 2)) ^ 4 < p ^ 4 := Nat.pow_lt_pow_left hqD (by norm_num)
        have h7 : 2 ^ ((b + 1) ^ 2 * 4) < 2 ^ ((b + 1) ^ 2 + (c + 1) * (2 * b + 1)) := by
          rw [pow_mul]
          exact lt_of_lt_of_le h6 (le_trans (by simpa using h5) h4)
        have h8 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h7
        have h9 : (c + 1) * (2 * b + 1) ≤ (b + 1 + 1) * (2 * b + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have : n = 1 := by omega
      subst this
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  have h1 := Finset.card_image_le (s := Finset.Ico 1 c) (f := fun j => (2, b + 1 + j))
  rw [Nat.card_Ico] at h1
  rw [Finset.card_singleton]
  omega

/-! ## With the theorem of Baker, Harman and Pintz as a hypothesis -/

/-- The theorem of Baker, Harman and Pintz on primes in short intervals. **Not proved here.** -/
def BHPstatement : Prop :=
  ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∃ q : ℕ, q.Prime ∧ x - x ^ (0.525 : ℝ) ≤ q ∧ (q : ℝ) ≤ x

theorem nrfamily_powerM12 (hBHP : BHPstatement) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ a0 : ℕ, ∀ a : ℕ, a0 ≤ a → ∃ q : ℕ, q.Prime ∧ q ≠ r ∧ 2 ^ (2 * a - 1) < q ∧
      cstarM5 {2, q} (fun p => aThr p (1 / 2 ^ (2 * a - 1))) (2 ^ (2 * a - 1))
        ≤ Nat.sqrt (2 * a) + 1 ∧
      ∀ x : ℤ, 0 < x → InBall {2, q} (1 / 2 ^ (2 * a - 1)) x → ¬ (r : ℤ) ∣ x →
        1 / 4 * ((2 : ℝ) ^ (a ^ 2)) ^ (1.475 : ℝ) < x := by
  obtain ⟨X0, hX0⟩ := hBHP
  refine ⟨max ⌈X0⌉₊ (r + 10), fun a ha => ?_⟩
  have haX : ⌈X0⌉₊ ≤ a := le_trans (le_max_left _ _) ha
  have har : r + 10 ≤ a := le_trans (le_max_right _ _) ha
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hra : r ≤ 2 ^ (2 * a - 2) :=
    le_trans (Nat.lt_two_pow_self (n := r)).le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hraD : 2 ^ (2 * a - 2) ≤ 2 ^ (a ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.sub_le _ _) (by nlinarith))
  have haD : a ≤ 2 ^ (a ^ 2) :=
    le_trans (Nat.le_self_pow (by norm_num) a) (Nat.lt_two_pow_self (n := a ^ 2)).le
  set D : ℝ := (2 : ℝ) ^ (a ^ 2) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hD8 : 8 ≤ D := by
    have : 2 ^ 3 ≤ 2 ^ (a ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    rw [hD]
    exact_mod_cast this
  set y : ℝ := (r : ℝ) * D with hy
  have hr3R : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have h3D : 3 * D ≤ y := mul_le_mul_of_nonneg_right hr3R hD0.le
  have hy8 : 8 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have haXR : X0 ≤ y := by
    have h1 : X0 ≤ (a : ℝ) := le_trans (Nat.le_ceil X0) (by exact_mod_cast haX)
    have h2 : (a : ℝ) ≤ D := by rw [hD]; exact_mod_cast haD
    linarith
  obtain ⟨q, hq, hqlo, hqhi⟩ := hX0 y haXR
  have hpow : 2 ≤ y ^ (0.475 : ℝ) := by
    have h1 : (8 : ℝ) ^ (0.475 : ℝ) ≤ y ^ (0.475 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hy8 (by norm_num)
    have h2 : (2 : ℝ) ≤ (8 : ℝ) ^ (0.475 : ℝ) := by
      have h3 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h3, ← Real.rpow_mul (by norm_num)]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((3 : ℝ) * 0.475) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hsum : y ^ (0.525 : ℝ) * y ^ (0.475 : ℝ) = y := by
    rw [← Real.rpow_add hy0]
    norm_num
  have h525 : 0 < y ^ (0.525 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have hhalf : 2 * y ^ (0.525 : ℝ) ≤ y := by
    calc 2 * y ^ (0.525 : ℝ) = y ^ (0.525 : ℝ) * 2 := mul_comm _ _
      _ ≤ y ^ (0.525 : ℝ) * y ^ (0.475 : ℝ) := mul_le_mul_of_nonneg_left hpow h525.le
      _ = y := hsum
  have hqy : y / 2 ≤ q := by linarith
  have hDq : D < q := by linarith
  have hqDn : 2 ^ (a ^ 2) < q := by
    rw [hD] at hDq
    exact_mod_cast hDq
  have hqm : 2 ^ (2 * a - 1) < q :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.sub_le _ _) (by nlinarith)))
      hqDn
  have hqr : q ≠ r := by
    have := le_trans hra hraD
    omega
  have hc1 : 2 * a < (Nat.sqrt (2 * a) + 1) ^ 2 + (Nat.sqrt (2 * a) + 1) + 1 := by
    have h1 := Nat.lt_succ_sqrt (2 * a)
    rw [Nat.succ_eq_add_one, ← pow_two] at h1
    omega
  have hca : Nat.sqrt (2 * a) + 1 ≤ a := by
    have : Nat.sqrt (2 * a) < a := Nat.sqrt_lt.2 (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))
    omega
  refine ⟨q, hq, hqr, hqm, cstar_leM12 (by omega) hqDn hc1 hca, fun x hx0 hx hrx => ?_⟩
  have h := nrfamily_lowerM12 hr hr2 hra hq hqm hx0 hx hrx
  rw [← hD, ← hy] at h
  refine lt_of_le_of_lt ?_ h
  have hqy' : (q : ℝ) ≠ y := by
    intro he
    have h1 : q = r * 2 ^ (a ^ 2) := by
      rw [hy, hD] at he
      exact_mod_cast he
    have h2 : 2 ^ (a ^ 2) ≠ 1 := by
      have : 2 ^ 1 ≤ 2 ^ (a ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      omega
    exact Nat.not_prime_mul (by omega) h2 (h1 ▸ hq)
  have habs : |(q : ℝ) - y| = y - q := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have hepos : 0 < y - (q : ℝ) := by
    have := lt_of_le_of_ne hqhi hqy'
    linarith
  have hele : y - (q : ℝ) ≤ y ^ (0.525 : ℝ) := by linarith
  rw [habs, le_div_iff₀ (mul_pos two_pos hepos)]
  have hD475 : D ^ (1.475 : ℝ) = D * D ^ (0.475 : ℝ) := by
    have : (1.475 : ℝ) = 1 + 0.475 := by norm_num
    rw [this, Real.rpow_add hD0, Real.rpow_one]
  have hDy : D ^ (0.475 : ℝ) ≤ y ^ (0.475 : ℝ) :=
    Real.rpow_le_rpow hD0.le (by linarith) (by norm_num)
  have hDpos : 0 ≤ D ^ (0.475 : ℝ) := (Real.rpow_pos_of_pos hD0 _).le
  rw [hD475]
  have h1 : D ^ (0.475 : ℝ) * (y - q) ≤ y := by
    calc D ^ (0.475 : ℝ) * (y - q) ≤ y ^ (0.475 : ℝ) * y ^ (0.525 : ℝ) :=
          mul_le_mul hDy hele hepos.le (Real.rpow_pos_of_pos hy0 _).le
      _ = y := by rw [mul_comm]; exact hsum
  have h2 : D ^ (0.475 : ℝ) * (y - q) ≤ 2 * q := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hD0.le
  have h4 : 1 / 4 * (D * D ^ (0.475 : ℝ)) * (2 * (y - q))
      = (D * (D ^ (0.475 : ℝ) * (y - q))) / 2 := by ring
  rw [h4]
  linarith

/-- No bound `D · m^(C c*)` holds uniformly over pairs (assuming `BHPstatement`). -/
theorem nrfamily_not_boundedM12 (hBHP : BHPstatement) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (C : ℕ) :
    ∃ a1 : ℕ, ∀ a : ℕ, a1 ≤ a → ∃ q : ℕ, q.Prime ∧ q ≠ r ∧
      ∀ x : ℤ, 0 < x → InBall {2, q} (1 / 2 ^ (2 * a - 1)) x → ¬ (r : ℤ) ∣ x →
        (Dvis {2, q} (1 / 2 ^ (2 * a - 1)) : ℝ) * ((2 : ℝ) ^ (2 * a - 1)) ^
          (C * cstarM5 {2, q} (fun p => aThr p (1 / 2 ^ (2 * a - 1))) (2 ^ (2 * a - 1))) < x := by
  obtain ⟨a0, h0⟩ := nrfamily_powerM12 hBHP hr hr2
  refine ⟨max a0 ((20 * C + 10) ^ 2), fun a ha => ?_⟩
  have ha0 : a0 ≤ a := le_trans (le_max_left _ _) ha
  have haC : (20 * C + 10) ^ 2 ≤ a := le_trans (le_max_right _ _) ha
  obtain ⟨q, hq, hqr, hqm, hcs, hbound⟩ := h0 a ha0
  refine ⟨q, hq, hqr, fun x hx0 hx hrx => lt_of_le_of_lt ?_ (hbound x hx0 hx hrx)⟩
  set t := Nat.sqrt a with ht
  have htC : 20 * C + 10 ≤ t := by
    rw [ht, Nat.le_sqrt, ← pow_two]
    exact haC
  have hta : t * t ≤ a := Nat.sqrt_le a
  have ha100 : 100 ≤ a := le_trans (by nlinarith) haC
  have h10t : 10 * t ≤ a := le_trans (Nat.mul_le_mul_right _ (by omega)) hta
  have hsq : Nat.sqrt (2 * a) + 1 ≤ 2 * t + 2 := by
    have h1 : a < (t + 1) * (t + 1) := by
      have := Nat.lt_succ_sqrt a
      rwa [Nat.succ_eq_add_one, ← ht] at this
    have h2 : Nat.sqrt (2 * a) < 2 * t + 2 := by
      rw [Nat.sqrt_lt]
      nlinarith
    omega
  set cs := cstarM5 {2, q} (fun p => aThr p (1 / 2 ^ (2 * a - 1))) (2 ^ (2 * a - 1)) with hcsdef
  have hcs' : cs ≤ 2 * t + 2 := le_trans hcs hsq
  have hq2 : q ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ (2 * a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [dvis_famM12 (by omega) hqm hq2]
  push_cast
  set E : ℕ := a ^ 2 + (2 * a - 1) * (C * (2 * t + 2)) with hE
  have h1 : (2 : ℝ) ^ (a ^ 2) * ((2 : ℝ) ^ (2 * a - 1)) ^ (C * cs) ≤ (2 : ℝ) ^ E := by
    rw [hE, pow_add, pow_mul (2 : ℝ) (2 * a - 1)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_right₀ (one_le_pow₀ one_le_two) (Nat.mul_le_mul_left _ hcs')
  refine le_trans h1 ?_
  have hnat : 1000 * ((2 * a) * (C * (2 * t + 2)) + 2) ≤ 475 * a ^ 2 := by
    have h2 : 20 * (a * C * (t + 1)) ≤ a * t * (t + 1) := by
      calc 20 * (a * C * (t + 1)) = a * (20 * C) * (t + 1) := by ring
        _ ≤ a * t * (t + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : 10 * (t * (t + 1)) ≤ 11 * a := by nlinarith
    have h4 : 10 * (a * t * (t + 1)) ≤ 11 * a ^ 2 := by
      calc 10 * (a * t * (t + 1)) = a * (10 * (t * (t + 1))) := by ring
        _ ≤ a * (11 * a) := Nat.mul_le_mul_left _ h3
        _ = 11 * a ^ 2 := by ring
    have h5 : (2 * a) * (C * (2 * t + 2)) = 4 * (a * C * (t + 1)) := by ring
    have h6 : 10000 ≤ a ^ 2 := by nlinarith
    rw [h5]
    omega
  have hEr : (E : ℝ) + 2 ≤ 1.475 * ((a ^ 2 : ℕ) : ℝ) := by
    have h2 : E ≤ a ^ 2 + (2 * a) * (C * (2 * t + 2)) := by
      rw [hE]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
    have h3 : 1000 * (E + 2) ≤ 1475 * a ^ 2 := by omega
    have h4 : (1000 : ℝ) * ((E : ℝ) + 2) ≤ 1475 * ((a ^ 2 : ℕ) : ℝ) := by exact_mod_cast h3
    norm_num at h4 ⊢
    linarith
  have h2 : ((2 : ℝ) ^ (a ^ 2)) ^ (1.475 : ℝ) = (2 : ℝ) ^ (((a ^ 2 : ℕ) : ℝ) * 1.475) := by
    rw [← Real.rpow_natCast 2 (a ^ 2), ← Real.rpow_mul (by norm_num)]
  have h3 : (2 : ℝ) ^ ((E : ℝ) + 2) = (2 : ℝ) ^ E * 4 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    norm_num
  have h4 : (2 : ℝ) ^ ((E : ℝ) + 2) ≤ ((2 : ℝ) ^ (a ^ 2)) ^ (1.475 : ℝ) := by
    rw [h2]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith
  rw [h3] at h4
  linarith

end TVGPlus
end LeanCheck
