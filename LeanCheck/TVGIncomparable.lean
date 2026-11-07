import LeanCheck.TVGPlusValuation
import LeanCheck.MixedPrimeDensity

/-!
# TVGplus: the topologies of `P_b` and `max (P_p, P_q)` on `ℤ` are incomparable (`b = p q`)

Formal counterpart of the Codex note of 7 November 2026, 10:39 (audited by Claude the same day).
`P_c = Pn (sqScales c)`, `P_c(x) = sup_{n ≥ 1} ‖x / c^(n²)‖`, for `c = p q`, `p`, `q`.

* `reverse_direction` (unconditional): for primes `p ≠ q` with `p` odd there are integers `h n` with
  `P_{pq}(h n) ≤ 1 / (2 q^(2n-1)) → 0` and `P_p(h n) ≥ (p^(2n-1) - 1) / (2 p^(2n-1))`; so `h n → 0` for the
  topology of `P_{pq}` but not for that of `max (P_p, P_q)`: the latter is not coarser than `τ_{pq}`.
* `first_direction` (conditional on diagonal density `DD {p, q}`, hypothesis `hDD`): there are integers `k d`
  with `P_p (k d) → 0`, `P_q (k d) → 0` and `P_{pq} (k d) ≥ 1 / (2 q)`; so `k d → 0` for `max (P_p, P_q)` but not
  for `τ_{pq}`: `τ_{pq}` is not coarser than `τ_{(p,q)}`.

Not formalized: that the two topologies have the same dual `ℤ[1/b]/ℤ` (Außenhofer and de la Barrera Mayoral,
arXiv:1107.2661, Theorem 4.4, and the pair theorem of TVGaddmore), the nondiscreteness of the join, and the
proof of `DD {p, q}` (an explicit hypothesis, as elsewhere in the TVGplus modules).
-/

open Filter Topology

namespace LeanCheck
namespace Incomparable

open LeanCheck.MixedPrime LeanCheck.TVGPlus

lemma Pn_ge {S : Set ℕ} {k : ℤ} {q : ℕ} (hq : q ∈ S) : nrm ((k : ℝ) / q) ≤ Pn S k :=
  le_ciSup (f := fun q : S => nrm ((k : ℝ) / (q : ℕ))) (bddAbove_Pn S k) ⟨q, hq⟩

/-- A centered solution of a linear congruence modulo an odd number. -/
lemma exists_centered (M : ℕ) (hM : Odd M) (Q : ℤ) (hcop : IsCoprime Q (M : ℤ)) (r : ℤ) :
    ∃ u : ℤ, (M : ℤ) ∣ u * Q - r ∧ 2 * |u| < M := by
  obtain ⟨s, t, hst⟩ := hcop
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM.pos
  set u0 : ℤ := s * r with hu0
  have e : s * Q = 1 - t * M := by linarith
  have hdvd0 : (M : ℤ) ∣ u0 * Q - r := ⟨-(r * t), by
    rw [hu0]
    calc s * r * Q - r = r * (s * Q) - r := by ring
      _ = r * (1 - t * M) - r := by rw [e]
      _ = M * (-(r * t)) := by ring⟩
  obtain ⟨c, hc⟩ := hM
  have hM2 : (M : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  set u : ℤ := (u0 + c) % M - c with hu
  have hmod : (u0 + c) % (M : ℤ) ≡ u0 + c [ZMOD M] := Int.mod_modEq _ _
  have hlt := Int.emod_lt_of_pos (u0 + c) hMpos
  have hnn := Int.emod_nonneg (u0 + c) hMpos.ne'
  have hu1 : u ≡ u0 [ZMOD M] := by
    have : (u0 + c) % (M : ℤ) - c ≡ u0 + c - c [ZMOD M] := hmod.sub_right c
    simpa [hu] using this
  refine ⟨u, ?_, ?_⟩
  · have h3 : (M : ℤ) ∣ u0 - u := Int.ModEq.dvd hu1
    have e2 : u * Q - r = (u0 * Q - r) - (u0 - u) * Q := by ring
    rw [e2]
    exact dvd_sub hdvd0 (dvd_mul_of_dvd_left h3 Q)
  · have h1 : -c ≤ u := by simp only [hu]; linarith
    have h2 : u ≤ c := by simp only [hu]; omega
    have h3 : |u| ≤ (c : ℤ) := abs_le.2 ⟨h1, h2⟩
    rw [hM2]
    linarith

/-- **Reverse direction.** For primes `p ≠ q`, `p` odd, there are integers `h n` (`n ≥ 1`) with
`P_{pq}(h n) ≤ 1 / (2 q^(2n-1))` and `P_p(h n) ≥ (p^(2n-1) - 1) / (2 p^(2n-1))`. -/
theorem reverse_direction (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hodd : p ≠ 2) :
    ∃ h : ℕ → ℤ, ∀ n : ℕ, 1 ≤ n →
      Pn (sqScales (p * q)) (h n) ≤ 1 / (2 * (q : ℝ) ^ (2 * n - 1)) ∧
      ((p : ℝ) ^ (2 * n - 1) - 1) / (2 * (p : ℝ) ^ (2 * n - 1)) ≤ Pn (sqScales p) (h n) := by
  have hpodd : Odd p := hp.odd_of_ne_two hodd
  have hcopQ : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hpq.symm)
  have key : ∀ n : ℕ, ∃ u : ℤ, (((p ^ (2 * n + 1) : ℕ) : ℤ) ∣
      u * ((q : ℤ) ^ (n ^ 2)) - (((p ^ (2 * n + 1) : ℕ) : ℤ) - 1) / 2) ∧
      2 * |u| < ((p ^ (2 * n + 1) : ℕ) : ℤ) := by
    intro n
    apply exists_centered
    · exact hpodd.pow
    · have : IsCoprime ((q : ℤ) ^ (n ^ 2)) ((p : ℤ) ^ (2 * n + 1)) := (hcopQ.pow_left).pow_right
      simpa using this
  choose u hu using key
  refine ⟨fun n => u (n - 1) * ((p * q : ℕ) : ℤ) ^ ((n - 1) ^ 2), ?_⟩
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e1 : 2 * (n' + 1) - 1 = 2 * n' + 1 := by omega
  rw [e1]
  obtain ⟨hdvd, hsmall⟩ := hu n'
  set M : ℕ := p ^ (2 * n' + 1) with hM
  have hMpos : 0 < M := pow_pos hp.pos _
  have hModd : Odd M := hpodd.pow
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hMcast : (M : ℝ) = (p : ℝ) ^ (2 * n' + 1) := by rw [hM]; push_cast; ring
  constructor
  · -- the bound for `P_{pq}`
    apply Pn_le (sq_nonempty (p * q))
    rintro s ⟨m, hm, rfl⟩
    have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    have hbpos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq0
    have hb1 : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq0
    have hc : 0 ≤ 1 / (2 * (q : ℝ) ^ (2 * n' + 1)) := by positivity
    by_cases hle : m ^ 2 ≤ n' ^ 2
    · -- an integer quotient
      have hint : ((u n' * ((p * q : ℕ) : ℤ) ^ (n' ^ 2) : ℤ) : ℝ) / (((p * q) ^ (m ^ 2) : ℕ) : ℝ) =
          ((u n' * ((p * q : ℕ) : ℤ) ^ (n' ^ 2 - m ^ 2) : ℤ) : ℝ) := by
        have : n' ^ 2 = (n' ^ 2 - m ^ 2) + m ^ 2 := by omega
        have hne : (((p * q) ^ (m ^ 2) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_pos hpq0 _).ne'
        rw [div_eq_iff hne]
        conv_lhs => rw [this]
        push_cast
        ring
      rw [hint, nrm_int]
      exact hc
    · have hlt : n' ^ 2 < m ^ 2 := not_le.1 hle
      have hnm : n' < m := by
        by_contra hcon
        exact hle (Nat.pow_le_pow_left (not_lt.1 hcon) 2)
      have hn2 : (n' + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm 2
      have hexp : 2 * n' + 1 ≤ m ^ 2 - n' ^ 2 := by
        have h3 : (n' + 1) ^ 2 = n' ^ 2 + (2 * n' + 1) := by ring
        omega
      have hsplit : (((p * q) ^ (m ^ 2) : ℕ) : ℝ) =
          (((p * q : ℕ) : ℝ)) ^ (n' ^ 2) * (((p * q : ℕ) : ℝ)) ^ (m ^ 2 - n' ^ 2) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]; push_cast; ring
      have hqt : (((p * q : ℕ) : ℝ)) ^ (n' ^ 2) ≠ 0 := (pow_pos hbpos _).ne'
      have hdiv : ((u n' * ((p * q : ℕ) : ℤ) ^ (n' ^ 2) : ℤ) : ℝ) / (((p * q) ^ (m ^ 2) : ℕ) : ℝ) =
          (u n' : ℝ) / (((p * q : ℕ) : ℝ)) ^ (m ^ 2 - n' ^ 2) := by
        rw [hsplit]; push_cast; field_simp
      refine (nrm_le_abs _).trans ?_
      rw [hdiv, abs_div, abs_of_pos (pow_pos hbpos _)]
      have hsm : 2 * |(u n' : ℝ)| < M := by exact_mod_cast hsmall
      have hpow : (((p * q : ℕ) : ℝ)) ^ (2 * n' + 1) ≤ (((p * q : ℕ) : ℝ)) ^ (m ^ 2 - n' ^ 2) :=
        pow_le_pow_right₀ hb1 hexp
      have hbq : (((p * q : ℕ) : ℝ)) ^ (2 * n' + 1) = (p : ℝ) ^ (2 * n' + 1) * (q : ℝ) ^ (2 * n' + 1) := by
        push_cast; rw [mul_pow]
      calc |(u n' : ℝ)| / (((p * q : ℕ) : ℝ)) ^ (m ^ 2 - n' ^ 2)
          ≤ |(u n' : ℝ)| / (((p * q : ℕ) : ℝ)) ^ (2 * n' + 1) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hbpos _) hpow
        _ ≤ 1 / (2 * (q : ℝ) ^ (2 * n' + 1)) := by
            rw [hbq, div_le_div_iff₀ (by positivity) (by positivity)]
            have : (M : ℝ) = (p : ℝ) ^ (2 * n' + 1) := hMcast
            nlinarith [pow_pos hqr (2 * n' + 1), pow_pos hpr (2 * n' + 1), hsm]
  · -- the lower bound for `P_p`
    have hmem : p ^ ((n' + 1) ^ 2) ∈ sqScales p := mem_sqScales (by omega)
    refine le_trans ?_ (Pn_ge hmem)
    obtain ⟨j, hj⟩ := hdvd
    have hrM : ((M : ℤ) - 1) / 2 * 2 = (M : ℤ) - 1 := by
      have : (M : ℤ) % 2 = 1 := by
        obtain ⟨c, hc⟩ := hModd; omega
      omega
    set r : ℤ := ((M : ℤ) - 1) / 2 with hr
    have hexp2 : (n' + 1) ^ 2 = n' ^ 2 + (2 * n' + 1) := by ring
    have hval : ((u n' * ((p * q : ℕ) : ℤ) ^ (n' ^ 2) : ℤ) : ℝ) / ((p ^ ((n' + 1) ^ 2) : ℕ) : ℝ) =
        (r : ℝ) / M + (j : ℝ) := by
      have hQ : (u n' : ℤ) * (q : ℤ) ^ (n' ^ 2) = r + M * j := by linarith
      have hQr : (u n' : ℝ) * (q : ℝ) ^ (n' ^ 2) = r + M * j := by exact_mod_cast hQ
      have hpe : ((p ^ ((n' + 1) ^ 2) : ℕ) : ℝ) = (p : ℝ) ^ (n' ^ 2) * M := by
        rw [hexp2, hM]; push_cast; ring
      have hne : (p : ℝ) ^ (n' ^ 2) * M ≠ 0 := by positivity
      rw [hpe, div_add' _ _ _ hMr.ne', div_eq_div_iff hne hMr.ne']
      push_cast
      have : (u n' : ℝ) * ((p : ℝ) * q) ^ (n' ^ 2) = (p : ℝ) ^ (n' ^ 2) * ((u n' : ℝ) * (q : ℝ) ^ (n' ^ 2)) := by
        rw [mul_pow]; ring
      rw [this, hQr]
      ring
    rw [hval, nrm_add_int]
    have hr2 : (r : ℝ) = ((M : ℝ) - 1) / 2 := by
      have : (r : ℝ) * 2 = (M : ℝ) - 1 := by exact_mod_cast hrM
      linarith
    have hrnn : 0 ≤ (r : ℝ) / M := by
      rw [hr2]; have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
      positivity
    have hrle : |(r : ℝ) / M| ≤ 1 / 2 := by
      rw [abs_of_nonneg hrnn, hr2, div_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [nrm_eq_abs hrle, abs_of_nonneg hrnn, hr2, hMcast, div_div]

/-! ### First direction (conditional on diagonal density for the pair) -/

lemma dvd_of_nrm_lt {y : ℤ} {M : ℕ} (hM : 0 < M) (h : nrm ((y : ℝ) / M) < 1 / M) : (M : ℤ) ∣ y := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [nrm_eq] at h
  set r : ℤ := round ((y : ℝ) / M) with hr
  have e : (y : ℝ) / M - r = ((y : ℝ) - M * r) / M := by field_simp
  rw [e, abs_div, abs_of_pos hMr, div_lt_div_iff_of_pos_right hMr] at h
  have h2 : |y - (M : ℤ) * r| < 1 := by exact_mod_cast h
  have h3 : y - (M : ℤ) * r = 0 := by
    have := abs_lt.1 h2
    omega
  exact ⟨r, by linarith⟩

lemma nrm_lower_inv {p q D : ℕ} (hp : 2 ≤ p) (hq : q.Prime) (hD : 1 ≤ D) (s j : ℤ)
    (h : (q : ℤ) * s = 1 + j * (p : ℤ) ^ D) :
    1 / (2 * (q : ℝ)) ≤ nrm ((s : ℝ) / ((p ^ D : ℕ) : ℝ)) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpD : (2 : ℝ) ≤ (p : ℝ) ^ D := by
    calc (2 : ℝ) ≤ p := hpr
      _ = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
  have hpDpos : (0 : ℝ) < (p : ℝ) ^ D := by linarith
  -- `q ∤ j`
  have hnd : ¬ (q : ℤ) ∣ j := by
    intro hd
    have h1 : (q : ℤ) ∣ 1 := by
      have : (1 : ℤ) = (q : ℤ) * s - j * (p : ℤ) ^ D := by linarith
      rw [this]
      exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)
    have := Int.le_of_dvd one_pos h1
    omega
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq.pos
  set c : ℤ := j / q with hc
  set r : ℤ := j % q with hrdef
  have hjr : j = q * c + r := (Int.mul_ediv_add_emod j q).symm
  have hr0 : 0 < r := by
    have := Int.emod_nonneg j hqz.ne'
    rcases this.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hnd
      exact Int.dvd_of_emod_eq_zero h'.symm
  have hrq : r < q := Int.emod_lt_of_pos j hqz
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hrq' : (r : ℝ) + 1 ≤ q := by exact_mod_cast hrq
  have hδ : 1 / ((p : ℝ) ^ D) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpD
  have hδ0 : 0 < 1 / ((p : ℝ) ^ D) := by positivity
  have hs : (s : ℝ) / ((p ^ D : ℕ) : ℝ) = ((r : ℝ) + 1 / ((p : ℝ) ^ D)) / q + c := by
    have hqs : (q : ℝ) * s = 1 + (q * c + r) * (p : ℝ) ^ D := by
      have : ((q : ℤ) : ℝ) * s = ((1 + j * (p : ℤ) ^ D : ℤ) : ℝ) := by exact_mod_cast h
      rw [hjr] at this
      push_cast at this ⊢
      linarith
    push_cast
    field_simp
    linarith
  rw [hs, nrm_add_int]
  have hv0 : 0 ≤ ((r : ℝ) + 1 / ((p : ℝ) ^ D)) / q := by positivity
  have hv1 : ((r : ℝ) + 1 / ((p : ℝ) ^ D)) / q < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  rw [nrm_unit hv0 hv1]
  apply le_min
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · have : 1 - ((r : ℝ) + 1 / ((p : ℝ) ^ D)) / q = (q - r - 1 / ((p : ℝ) ^ D)) / q := by
      field_simp
      ring
    rw [this, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

lemma Pn_pow_le {p : ℕ} (hp : 2 ≤ p) {n' D : ℕ} (hD : D ≤ 2 * n' + 1) :
    Pn (sqScales p) ((p : ℤ) ^ ((n' + 1) ^ 2 - D)) ≤ 1 / (p : ℝ) ^ D := by
  apply Pn_le (sq_nonempty p)
  rintro s ⟨m, hm, rfl⟩
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hexp : (n' + 1) ^ 2 = n' ^ 2 + (2 * n' + 1) := by ring
  have hDle : D ≤ (n' + 1) ^ 2 := by omega
  by_cases hle : m ^ 2 ≤ (n' + 1) ^ 2 - D
  · have hint : (((p : ℤ) ^ ((n' + 1) ^ 2 - D) : ℤ) : ℝ) / ((p ^ (m ^ 2) : ℕ) : ℝ) =
        (((p : ℤ) ^ ((n' + 1) ^ 2 - D - m ^ 2) : ℤ) : ℝ) := by
      have h3 : (n' + 1) ^ 2 - D = ((n' + 1) ^ 2 - D - m ^ 2) + m ^ 2 := by omega
      have hne : ((p ^ (m ^ 2) : ℕ) : ℝ) ≠ 0 := by positivity
      rw [div_eq_iff hne]
      conv_lhs => rw [h3]
      push_cast
      ring
    rw [hint, nrm_int]
    positivity
  · have hlt : (n' + 1) ^ 2 - D < m ^ 2 := not_le.1 hle
    have hnm : n' < m := by
      by_contra hcon
      have : m ^ 2 ≤ n' ^ 2 := Nat.pow_le_pow_left (not_lt.1 hcon) 2
      omega
    have hn2 : (n' + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm 2
    have hdiv : (((p : ℤ) ^ ((n' + 1) ^ 2 - D) : ℤ) : ℝ) / ((p ^ (m ^ 2) : ℕ) : ℝ) =
        1 / (p : ℝ) ^ (m ^ 2 - ((n' + 1) ^ 2 - D)) := by
      have h3 : m ^ 2 = ((n' + 1) ^ 2 - D) + (m ^ 2 - ((n' + 1) ^ 2 - D)) := by omega
      push_cast
      conv_lhs => rw [h3]
      rw [pow_add]
      field_simp
    refine (nrm_le_abs _).trans ?_
    rw [hdiv, abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ hp1 (by omega)

/-- **First direction** (conditional on diagonal density `DD {p, q}`). -/
theorem first_direction (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hDD : DD {p, q}) :
    ∃ k : ℕ → ℤ, Tendsto (fun d => Pn (sqScales p) (k d)) atTop (𝓝 0) ∧
      Tendsto (fun d => Pn (sqScales q) (k d)) atTop (𝓝 0) ∧
      ∀ d, 1 / (2 * (q : ℝ)) ≤ Pn (sqScales (p * q)) (k d) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have key : ∀ D : ℕ, 1 ≤ D → ∃ k : ℤ, Pn (sqScales p) k ≤ 2 / (p : ℝ) ^ D ∧
      Pn (sqScales q) k ≤ 2 / (p : ℝ) ^ D ∧ 1 / (2 * (q : ℝ)) ≤ Pn (sqScales (p * q)) k := by
    intro D hD
    set φ : ℕ := Nat.totient (p ^ D) with hφ
    obtain ⟨n', hn'⟩ : ∃ n', 1 + φ * D = n' + 1 := ⟨φ * D, by ring⟩
    set n : ℕ := n' + 1 with hn
    have hφpos : 0 < φ := Nat.totient_pos.2 (pow_pos hp.pos _)
    have hDn : D ≤ 2 * n' + 1 := by
      have : D ≤ φ * D := Nat.le_mul_of_pos_left D hφpos
      omega
    have hDn2 : D ≤ n ^ 2 := by nlinarith
    have hcop : Nat.Coprime q (p ^ D) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hp).2 hpq.symm)
    -- `q^(n^2) ≡ q mod p^D`
    have hq1 : q ^ (n ^ 2) ≡ q [MOD p ^ D] := by
      have h1 : q ^ φ ≡ 1 [MOD p ^ D] := Nat.ModEq.pow_totient hcop
      have hn2 : n ^ 2 = 1 + φ * (2 * D + φ * D ^ 2) := by
        have : n = 1 + φ * D := by omega
        rw [this]; ring
      rw [hn2, pow_add, pow_mul, pow_one]
      calc q * (q ^ φ) ^ (2 * D + φ * D ^ 2) ≡ q * 1 ^ (2 * D + φ * D ^ 2) [MOD p ^ D] :=
            Nat.ModEq.mul_left _ (h1.pow _)
        _ = q := by simp
    -- the diagonal approximation
    set ε : ℝ := 1 / (2 * ((p * q : ℕ) : ℝ) ^ (n ^ 2)) with hε
    have hbpos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq0
    have hεpos : 0 < ε := by positivity
    obtain ⟨k, hk⟩ := hDD (fun r => if r = p then ((p : ℤ) ^ (n ^ 2 - D)) else 0) ε hεpos
    have hkp : Pn (sqScales p) (k - (p : ℤ) ^ (n ^ 2 - D)) < ε := by
      have := hk p (by simp)
      simpa using this
    have hkq : Pn (sqScales q) k < ε := by
      have := hk q (by simp)
      simpa [hpq.symm] using this
    have hεp : ε < 1 / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      have hpp : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by positivity
      have hle : ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ ((p * q : ℕ) : ℝ) ^ (n ^ 2) := by
        push_cast
        rw [mul_pow]
        have : (1 : ℝ) ≤ (q : ℝ) ^ (n ^ 2) := one_le_pow₀ (by exact_mod_cast hq.one_lt.le)
        nlinarith [pow_pos (by positivity : (0 : ℝ) < p) (n ^ 2)]
      rw [hε]
      calc 1 / (2 * ((p * q : ℕ) : ℝ) ^ (n ^ 2)) ≤ 1 / (2 * ((p ^ (n ^ 2) : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ < 1 / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
            rw [div_lt_div_iff₀ (by positivity) hpp]; nlinarith
    have hεq : ε < 1 / ((q ^ (n ^ 2) : ℕ) : ℝ) := by
      have hqq : (0 : ℝ) < ((q ^ (n ^ 2) : ℕ) : ℝ) := by positivity
      have hle : ((q ^ (n ^ 2) : ℕ) : ℝ) ≤ ((p * q : ℕ) : ℝ) ^ (n ^ 2) := by
        push_cast
        rw [mul_pow]
        have : (1 : ℝ) ≤ (p : ℝ) ^ (n ^ 2) := one_le_pow₀ (by linarith)
        nlinarith [pow_pos (by positivity : (0 : ℝ) < q) (n ^ 2)]
      rw [hε]
      calc 1 / (2 * ((p * q : ℕ) : ℝ) ^ (n ^ 2)) ≤ 1 / (2 * ((q ^ (n ^ 2) : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
        _ < 1 / ((q ^ (n ^ 2) : ℕ) : ℝ) := by
            rw [div_lt_div_iff₀ (by positivity) hqq]; nlinarith
    -- divisibility at level `n`
    have hdp : ((p ^ (n ^ 2) : ℕ) : ℤ) ∣ k - (p : ℤ) ^ (n ^ 2 - D) := by
      apply dvd_of_nrm_lt (pow_pos hp.pos _)
      exact lt_of_le_of_lt (Pn_ge (mem_sqScales (by omega))) (hkp.trans hεp)
    have hdq : ((q ^ (n ^ 2) : ℕ) : ℤ) ∣ k := by
      apply dvd_of_nrm_lt (pow_pos hq.pos _)
      exact lt_of_le_of_lt (Pn_ge (mem_sqScales (by omega))) (hkq.trans hεq)
    push_cast at hdp hdq
    obtain ⟨t', ht'⟩ := hdq
    have hcopz : IsCoprime ((p : ℤ) ^ (n ^ 2 - D)) ((q : ℤ) ^ (n ^ 2)) :=
      ((Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)).pow)
    have hpk : (p : ℤ) ^ (n ^ 2 - D) ∣ k := by
      have h1 : (p : ℤ) ^ (n ^ 2 - D) ∣ (p : ℤ) ^ (n ^ 2) := pow_dvd_pow _ (by omega)
      have h2 := dvd_trans h1 hdp
      have h3 : (p : ℤ) ^ (n ^ 2 - D) ∣ (p : ℤ) ^ (n ^ 2 - D) := dvd_rfl
      have := dvd_add h2 h3
      simpa using this
    have hpt : (p : ℤ) ^ (n ^ 2 - D) ∣ t' := by
      rw [ht'] at hpk
      exact hcopz.dvd_of_dvd_mul_left hpk
    obtain ⟨s, hs⟩ := hpt
    have hk2 : k = (q : ℤ) ^ (n ^ 2) * ((p : ℤ) ^ (n ^ 2 - D) * s) := by rw [ht', hs]
    -- `q^(n^2) s ≡ 1 mod p^D`
    have hDdvd : (p : ℤ) ^ D ∣ (q : ℤ) ^ (n ^ 2) * s - 1 := by
      have hsplit : (p : ℤ) ^ (n ^ 2) = (p : ℤ) ^ (n ^ 2 - D) * (p : ℤ) ^ D := by
        rw [← pow_add]; congr 1; omega
      have h1 : (p : ℤ) ^ (n ^ 2 - D) * (p : ℤ) ^ D ∣
          (p : ℤ) ^ (n ^ 2 - D) * ((q : ℤ) ^ (n ^ 2) * s - 1) := by
        rw [← hsplit]
        have : k - (p : ℤ) ^ (n ^ 2 - D) = (p : ℤ) ^ (n ^ 2 - D) * ((q : ℤ) ^ (n ^ 2) * s - 1) := by
          rw [hk2]; ring
        rw [← this]; exact hdp
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).1 h1
    have hqmod : (p : ℤ) ^ D ∣ (q : ℤ) - (q : ℤ) ^ (n ^ 2) := by
      have := (Nat.modEq_iff_dvd.1 hq1)
      push_cast at this
      exact this
    have hqs : (p : ℤ) ^ D ∣ (q : ℤ) * s - 1 := by
      have : (q : ℤ) * s - 1 = ((q : ℤ) ^ (n ^ 2) * s - 1) + ((q : ℤ) - (q : ℤ) ^ (n ^ 2)) * s := by ring
      rw [this]
      exact dvd_add hDdvd (dvd_mul_of_dvd_left hqmod _)
    obtain ⟨j, hj⟩ := hqs
    have hqsj : (q : ℤ) * s = 1 + j * (p : ℤ) ^ D := by linarith
    -- the observation at level `n` for `P_{pq}`
    have hobs : (k : ℝ) / (((p * q) ^ (n ^ 2) : ℕ) : ℝ) = (s : ℝ) / ((p ^ D : ℕ) : ℝ) := by
      have hsplit : (p : ℝ) ^ (n ^ 2) = (p : ℝ) ^ (n ^ 2 - D) * (p : ℝ) ^ D := by
        rw [← pow_add]; congr 1; omega
      have hk2r : (k : ℝ) = (q : ℝ) ^ (n ^ 2) * ((p : ℝ) ^ (n ^ 2 - D) * s) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hk2
        simpa using this
      rw [hk2r]
      push_cast
      rw [mul_pow, hsplit]
      have h1 : (q : ℝ) ^ (n ^ 2) ≠ 0 := by positivity
      have h2 : (p : ℝ) ^ (n ^ 2 - D) ≠ 0 := by positivity
      have h3 : (p : ℝ) ^ D ≠ 0 := by positivity
      field_simp
    have hεD : ε ≤ 1 / (p : ℝ) ^ D := by
      refine (hεp.le.trans ?_)
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      exact pow_le_pow_right₀ (by linarith) hDn2
    refine ⟨k, ?_, ?_, ?_⟩
    · -- `P_p (k) ≤ 2 / p^D`
      have hx : Pn (sqScales p) ((p : ℤ) ^ (n ^ 2 - D)) ≤ 1 / (p : ℝ) ^ D := by
        have := Pn_pow_le (p := p) hp2 (n' := n') (D := D) hDn
        simpa [hn] using this
      have hadd := Pn_add_le (sq_nonempty p) (k - (p : ℤ) ^ (n ^ 2 - D)) ((p : ℤ) ^ (n ^ 2 - D))
      rw [sub_add_cancel] at hadd
      have : 2 / (p : ℝ) ^ D = 1 / (p : ℝ) ^ D + 1 / (p : ℝ) ^ D := by ring
      linarith
    · have : 1 / (p : ℝ) ^ D ≤ 2 / (p : ℝ) ^ D := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith
    · have hmem : (p * q) ^ (n ^ 2) ∈ sqScales (p * q) := mem_sqScales (by omega)
      refine le_trans ?_ (Pn_ge hmem)
      rw [hobs]
      exact nrm_lower_inv hp2 hq hD s j hqsj
  choose k hk using fun d : ℕ => key (d + 1) (by omega)
  have hlim : Tendsto (fun d : ℕ => 2 / (p : ℝ) ^ (d + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun d : ℕ => (p : ℝ) ^ (d + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  refine ⟨k, ?_, ?_, fun d => (hk d).2.2⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun d => Pn_nonneg _ _) (fun d => (hk d).1)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun d => Pn_nonneg _ _) (fun d => (hk d).2.1)

end Incomparable
end LeanCheck
