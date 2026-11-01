import LeanCheck.TVGPlusValuation
import LeanCheck.MixedPrimeSplit

/-!
# TVGplus: the exact gcd `g_S(δ) = D_S(δ)` under diagonal density

Formal counterpart of the second half of `TVGplus` Theorem "Valuation vectors and the gcd" (Section 4).  The paper argues with
the dual group of the completion; here the same fact is obtained by an elementary construction from `DD S`:

* `exists_not_dvd`: if `DD S` holds and `r ∉ S` is a prime, the ball `B^S_δ` is **not** contained in `rℤ`.
  (For each `p ∈ S` choose `y_p ≡ 1 (mod r)` with `P_p(y_p) < δ/2` (a multiple of `p^(a²)` by a unit mod `r`), approximate the
  integer targets `(y_p - 1)/r` by `w` in all `P_p` simultaneously, and put `K = 1 + r w`.  Then `P_p(K - y_p) ≤ r P_p(w - z_p) < δ/2`,
  so `K` lies in the ball, and `r ∤ K`.)
* `gcd_iff`: for `d : ℕ`, `d` divides every element of the ball iff `d ∣ D_S(δ)`; that is, `D_S(δ)` is the gcd of the ball.

Everything is checked (no axiom, no `sorry`) *under the explicit hypothesis* `DD S`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- `P_p(p^(a²)) ≤ p^(-(2a+1))`. -/
lemma pn_sq_pow_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Pn (sqScales p) ((p : ℤ) ^ (a ^ 2)) ≤ 1 / (p : ℝ) ^ (2 * a + 1) := by
  have h := Pn_prime_pow_le hp.two_le (a ^ 2)
  have hs : Nat.sqrt (a ^ 2) = a := by rw [pow_two]; exact Nat.sqrt_eq _
  rw [hs] at h
  have e : (a + 1) ^ 2 - a ^ 2 = 2 * a + 1 := by
    have : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
    omega
  rw [e] at h
  exact h

/-- For a prime `p ≠ r` and `ε > 0` there is an integer `y ≡ 1 (mod r)` with `P_p(y) < ε`. -/
lemma exists_unit_small {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℤ, (r : ℤ) ∣ y - 1 ∧ Pn (sqScales p) y < ε := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  obtain ⟨a, ha⟩ := exists_thr hp.two_le (div_pos hε hr0)
  have hpz : (p : ZMod r) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp h).symm
  set u : ZMod r := ((p : ZMod r) ^ (a ^ 2))⁻¹ with hu
  set m : ℕ := u.val with hm
  have hmlt : m < r := ZMod.val_lt u
  have hmu : (m : ZMod r) = u := ZMod.natCast_zmod_val u
  have hunit : (m : ZMod r) * (p : ZMod r) ^ (a ^ 2) = 1 := by
    rw [hmu, hu]; exact inv_mul_cancel₀ (pow_ne_zero _ hpz)
  refine ⟨(m : ℤ) * (p : ℤ) ^ (a ^ 2), ?_, ?_⟩
  · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hunit]
  · have h1 := Pn_zsmul_le (sq_nonempty p) (m : ℤ) ((p : ℤ) ^ (a ^ 2))
    have h2 := pn_sq_pow_le hp a
    have hm' : |((m : ℤ) : ℝ)| ≤ r := by
      rw [abs_of_nonneg (by positivity)]
      have : (m : ℝ) ≤ r := by exact_mod_cast hmlt.le
      simpa using this
    have h3 : Pn (sqScales p) ((m : ℤ) * (p : ℤ) ^ (a ^ 2)) ≤ r * (1 / (p : ℝ) ^ (2 * a + 1)) :=
      h1.trans (mul_le_mul hm' h2 (Pn_nonneg _ _) hr0.le)
    refine lt_of_le_of_lt h3 ?_
    have := (lt_div_iff₀ hr0).mp ha
    nlinarith

/-- **The ball is not contained in `rℤ`** for a prime `r ∉ S`, under diagonal density. -/
theorem exists_not_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {δ : ℝ} (hδ : 0 < δ)
    {r : ℕ} (hr : r.Prime) (hrS : r ∉ S) :
    ∃ k : ℤ, InBall S δ k ∧ ¬ (r : ℤ) ∣ k := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hy : ∀ p : ℕ, ∃ y : ℤ, p ∈ S → ((r : ℤ) ∣ y - 1 ∧ Pn (sqScales p) y < δ / 2) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨y, h1, h2⟩ := exists_unit_small (hS p hp) hr (fun h => hrS (h ▸ hp)) (half_pos hδ)
      exact ⟨y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose y hy using hy
  have hz : ∀ p : ℕ, ∃ z : ℤ, p ∈ S → y p - 1 = (r : ℤ) * z := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨z, hz⟩ := (hy p hp).1
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose z hz using hz
  obtain ⟨w, hw⟩ := hDD z (δ / (2 * r)) (by positivity)
  refine ⟨1 + (r : ℤ) * w, ?_, ?_⟩
  · intro p hp
    have hsub : (1 + (r : ℤ) * w) - y p = (r : ℤ) * (w - z p) := by
      have := hz p hp
      linarith
    have h1 := Pn_add_le (sq_nonempty p) ((1 + (r : ℤ) * w) - y p) (y p)
    have e : (1 + (r : ℤ) * w) - y p + y p = 1 + (r : ℤ) * w := by ring
    rw [e, hsub] at h1
    have h2 := Pn_zsmul_le (sq_nonempty p) (r : ℤ) (w - z p)
    have h3 := hw p hp
    have h4 : Pn (sqScales p) ((r : ℤ) * (w - z p)) < δ / 2 := by
      refine lt_of_le_of_lt h2 ?_
      have hrabs : |((r : ℤ) : ℝ)| = r := by simp
      rw [hrabs]
      have := mul_lt_mul_of_pos_left h3 hr0
      calc (r : ℝ) * Pn (sqScales p) (w - z p) < r * (δ / (2 * r)) := this
        _ = δ / 2 := by field_simp
    linarith [(hy p hp).2]
  · intro hd
    have h1 : (r : ℤ) ∣ 1 := by
      have := dvd_sub hd (dvd_mul_right (r : ℤ) w)
      simpa using this
    have h2 : r ∣ 1 := by exact_mod_cast h1
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)

/-- **`g_S(δ) = D_S(δ)`** under diagonal density: an integer divides every element of the ball `B^S_δ` if and only if it
divides `D_S(δ)`; i.e. `D_S(δ)` is the (positive) gcd of the ball. -/
theorem gcd_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {δ : ℝ} (hδ : 0 < δ) (d : ℕ) :
    (∀ k : ℤ, InBall S δ k → (d : ℤ) ∣ k) ↔ d ∣ Dvis S δ := by
  classical
  constructor
  · intro hd
    obtain ⟨k0, hk0, hv⟩ := gcd_valuation hS hDD hδ
    have hDne : Dvis S δ ≠ 0 := by
      unfold Dvis
      exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hS p hp).ne_zero)
    -- a prime outside `S`
    obtain ⟨r0, hr0le, hr0p⟩ := Nat.exists_infinite_primes (S.sup id + 1)
    have hr0S : r0 ∉ S := by
      intro h
      have := Finset.le_sup (f := id) h
      simp at this
      omega
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨k, hk, hnd⟩ := exists_not_dvd hS hDD hδ hr0p hr0S
      have := hd k hk
      rw [Nat.cast_zero, zero_dvd_iff] at this
      exact hnd (by simp [this])
    rw [← Nat.factorization_prime_le_iff_dvd hd0 hDne]
    intro r hr
    by_cases hrS : r ∈ S
    · have hk0ne : k0 ≠ 0 := by
        rintro rfl
        exact (hv r hrS).2 (dvd_zero _)
      have hdk : d ∣ k0.natAbs := Int.natCast_dvd.mp (hd k0 hk0)
      have hk0n : k0.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk0ne
      have h1 : d.factorization r ≤ k0.natAbs.factorization r :=
        (Nat.factorization_le_iff_dvd hd0 hk0n).mpr hdk r
      have h2 : k0.natAbs.factorization r ≤ aThr r δ ^ 2 := by
        by_contra hc
        push Not at hc
        have : r ^ (aThr r δ ^ 2 + 1) ∣ k0.natAbs :=
          (hr.pow_dvd_iff_le_factorization hk0n).mpr hc
        exact (hv r hrS).2 (Int.natCast_dvd.mpr (by exact_mod_cast this))
      have h3 : r ^ (aThr r δ ^ 2) ∣ Dvis S δ := by
        unfold Dvis
        exact Finset.dvd_prod_of_mem (fun p => p ^ (aThr p δ ^ 2)) hrS
      have h4 : aThr r δ ^ 2 ≤ (Dvis S δ).factorization r :=
        (hr.pow_dvd_iff_le_factorization hDne).mp h3
      omega
    · have : d.factorization r = 0 := by
        by_contra hc
        have hdr : r ∣ d := Nat.dvd_of_factorization_pos hc
        obtain ⟨k, hk, hnd⟩ := exists_not_dvd hS hDD hδ hr hrS
        exact hnd ((Int.natCast_dvd_natCast.mpr hdr).trans (hd k hk))
      omega
  · intro hdD k hk
    have h1 : (Dvis S δ : ℤ) ∣ k := forced hS hδ hk
    exact (Int.natCast_dvd_natCast.mpr hdD).trans h1

#print axioms exists_unit_small
#print axioms exists_not_dvd
#print axioms gcd_iff

end TVGPlus
end LeanCheck
