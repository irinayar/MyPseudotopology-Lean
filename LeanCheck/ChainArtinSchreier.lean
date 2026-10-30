import Mathlib

/-!
# Artin–Schreier for subfields of `ℝ` (TVGQ-v7 Corollary `field-universal`)

A subfield `F ⊆ ℝ` with `[ℝ : F] < ∞` equals `ℝ`.  Following Conrad's proof of the Artin–Schreier theorem
(characteristic `0`), the heart is:

* `no_prime_index_odd`: a field `M` with `[ℂ : M] = p` an odd prime and `ζ_p ∈ M` does not exist
  (Kummer: `ℂ = M(α)`, `α^p = a ∈ M`; then `X^{p²} - a` is irreducible over `M`, giving a complex number of
  degree `p² > p` over `M`);
* `no_prime_index_two`: the same for `p = 2` when `i ∈ M` (a direct computation with the minimal
  polynomial of a fourth root).

Then `finrank_eq_one_of_I_mem` shows that a field `K` with `[ℂ : K] < ∞` and `i ∈ K` has `K = ℂ`
(induction on a prime divisor of the degree through the fixed field of a subgroup of order `p` of the Galois
group), and `finite_index_subfield_real` deduces the statement for subfields of `ℝ`.
-/

open Polynomial Module

namespace LeanCheck

section PrimeIndex

variable (M : Type) [Field M] [Algebra M ℂ]

lemma charZero_of_algebra_complex : CharZero M :=
  RingHom.charZero (algebraMap M ℂ)

/-- A finite extension of a subfield `M` of `ℂ` by `ℂ` is Galois (`ℂ` is algebraically closed, char `0`). -/
lemma isGalois_complex [FiniteDimensional M ℂ] : IsGalois M ℂ := by
  haveI := charZero_of_algebra_complex M
  haveI : Algebra.IsAlgebraic M ℂ := Algebra.IsAlgebraic.of_finite M ℂ
  haveI : IsAlgClosure M ℂ := ⟨inferInstance, inferInstance⟩
  haveI : Normal M ℂ := IsAlgClosure.normal M ℂ
  exact ⟨⟩

/-- An element of `ℂ` all of whose `p`-th power lies in the image of `M`, in a prime-index situation,
cannot generate `ℂ` unless ... (used to show `a` is not a `p`-th power). -/
lemma not_pow_of_adjoin_top (p : ℕ) (hp : p.Prime) [FiniteDimensional M ℂ]
    (hfr : finrank M ℂ = p) (z : M) (hz : IsPrimitiveRoot z p) (α : ℂ) (a : M)
    (ha : algebraMap M ℂ a = α ^ p) (hα : IntermediateField.adjoin M {α} = ⊤) :
    ∀ b : M, b ^ p ≠ a := by
  intro b hb
  have hz' : IsPrimitiveRoot (algebraMap M ℂ z) p := hz.map_of_injective (algebraMap M ℂ).injective
  have hαp : α ^ p = (algebraMap M ℂ b) ^ p := by
    rw [← ha, ← hb, map_pow]
  have hmem : α ∈ Set.range (algebraMap M ℂ) := by
    by_cases hb0 : algebraMap M ℂ b = 0
    · have : α ^ p = 0 := by rw [hαp, hb0, zero_pow hp.ne_zero]
      have : α = 0 := pow_eq_zero_iff hp.ne_zero |>.1 this
      exact ⟨0, by simp [this]⟩
    · have h1 : (α / algebraMap M ℂ b) ^ p = 1 := by
        rw [div_pow, hαp, div_self (pow_ne_zero _ hb0)]
      haveI : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h1
      refine ⟨z ^ i * b, ?_⟩
      rw [map_mul, map_pow, hi]
      field_simp
  have hbot : IntermediateField.adjoin M {α} = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.mem_bot.2 hmem)
  rw [hbot] at hα
  have : finrank M ℂ = 1 := (IntermediateField.bot_eq_top_iff_finrank_eq_one).1 hα
  rw [hfr] at this
  exact hp.ne_one this

/-- **Odd prime index with `ζ_p ∈ M` is impossible.** -/
theorem no_prime_index_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) [FiniteDimensional M ℂ]
    (hfr : finrank M ℂ = p) (z : M) (hz : IsPrimitiveRoot z p) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := charZero_of_algebra_complex M
  haveI : IsGalois M ℂ := isGalois_complex M
  haveI : IsCyclic Gal(ℂ/M) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hfr])
  have hK : (primitiveRoots (finrank M ℂ) M).Nonempty :=
    ⟨z, (mem_primitiveRoots (by rw [hfr]; exact hp.pos)).2 (by rw [hfr]; exact hz)⟩
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic M ℂ hK
  rw [hfr] at ha
  have hnp := not_pow_of_adjoin_top M p hp hfr z hz α a ha hα
  have hirr : Irreducible (X ^ (p ^ 2) - C a) :=
    X_pow_sub_C_irreducible_of_prime_pow_of_ne_two hp hp2 2 hnp
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap M ℂ a) (n := p ^ 2) (pow_pos hp.pos 2)
  have hroot : aeval β (X ^ (p ^ 2) - C a : M[X]) = 0 := by simp [hβ]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C a (pow_pos hp.pos 2).ne')
  have hdeg := minpoly.natDegree_le (A := M) β
  rw [← hmin, natDegree_X_pow_sub_C, hfr] at hdeg
  have h2 := hp.two_le
  nlinarith

/-- **Index `2` with `i ∈ M` is impossible.** -/
theorem no_prime_index_two [FiniteDimensional M ℂ] (hfr : finrank M ℂ = 2) (i : M) (hi : i ^ 2 = -1) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := charZero_of_algebra_complex M
  haveI : IsGalois M ℂ := isGalois_complex M
  haveI : IsCyclic Gal(ℂ/M) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hfr])
  have hz : IsPrimitiveRoot (-1 : M) 2 := by
    refine ⟨by simp, fun l hl => ?_⟩
    have h1 : (-1 : M) ≠ 1 := by
      intro h
      have : (2 : M) = 0 := by linear_combination -h
      exact two_ne_zero this
    exact (neg_one_pow_eq_one_iff_even h1).1 hl |>.two_dvd
  have hK : (primitiveRoots (finrank M ℂ) M).Nonempty :=
    ⟨-1, (mem_primitiveRoots (by rw [hfr]; norm_num)).2 (by rw [hfr]; exact hz)⟩
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic M ℂ hK
  rw [hfr] at ha
  have hnp := not_pow_of_adjoin_top M 2 Nat.prime_two hfr (-1) hz α a ha hα
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq α (n := 2) (by norm_num)
  have hβ4 : β ^ 4 = algebraMap M ℂ a := by
    rw [ha, ← hβ]; ring
  have hnot : β ∉ Set.range (algebraMap M ℂ) := by
    rintro ⟨c, rfl⟩
    apply hnp (c ^ 2)
    apply (algebraMap M ℂ).injective
    rw [← hβ4]; simp [map_pow]; ring
  have hint : IsIntegral M β := Algebra.IsIntegral.isIntegral β
  have hd1 : (minpoly M β).natDegree ≠ 1 := by
    intro h
    exact hnot ((minpoly.natDegree_eq_one_iff).1 h)
  have hd2 : (minpoly M β).natDegree ≤ 2 := by
    have := minpoly.natDegree_le (A := M) β
    rwa [hfr] at this
  have hdpos : 0 < (minpoly M β).natDegree := minpoly.natDegree_pos hint
  have hdeg : (minpoly M β).natDegree = 2 := by omega
  have hmonic : (minpoly M β).Monic := minpoly.monic hint
  -- the relation `β² + uβ + w = 0`
  set u := (minpoly M β).coeff 1 with hu
  set w := (minpoly M β).coeff 0 with hw
  have hrel : β ^ 2 + algebraMap M ℂ u * β + algebraMap M ℂ w = 0 := by
    have h0 := minpoly.aeval M β
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Algebra.smul_def] at h0
    have h2 : (minpoly M β).coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rwa [hdeg] at this
    rw [h2] at h0
    simp only [map_one, one_mul, pow_zero, pow_one] at h0
    linear_combination h0
  have key : (2 * algebraMap M ℂ u * algebraMap M ℂ w - algebraMap M ℂ u ^ 3) * β +
      (algebraMap M ℂ w ^ 2 - algebraMap M ℂ u ^ 2 * algebraMap M ℂ w - algebraMap M ℂ a) = 0 := by
    linear_combination hβ4 - (β ^ 2 - algebraMap M ℂ u * β + (algebraMap M ℂ u ^ 2 - algebraMap M ℂ w)) * hrel
  by_cases hC : 2 * algebraMap M ℂ u * algebraMap M ℂ w - algebraMap M ℂ u ^ 3 = 0
  · have hC' : 2 * u * w - u ^ 3 = 0 := by
      apply (algebraMap M ℂ).injective
      simpa [map_sub, map_mul, map_pow, map_ofNat] using hC
    have hD : w ^ 2 - u ^ 2 * w - a = 0 := by
      apply (algebraMap M ℂ).injective
      have : algebraMap M ℂ w ^ 2 - algebraMap M ℂ u ^ 2 * algebraMap M ℂ w - algebraMap M ℂ a = 0 := by
        rw [hC, zero_mul, zero_add] at key; exact key
      simpa [map_sub, map_mul, map_pow, map_ofNat] using this
    have hfac : u * (2 * w - u ^ 2) = 0 := by linear_combination hC'
    rcases mul_eq_zero.1 hfac with h | h
    · apply hnp w
      rw [h] at hD
      linear_combination hD
    · apply hnp (i * w)
      have h2w : u ^ 2 = 2 * w := by linear_combination -h
      have : a = w ^ 2 - u ^ 2 * w := by linear_combination -hD
      rw [this, h2w]
      linear_combination (w ^ 2) * hi
  · apply hnot
    refine ⟨-(w ^ 2 - u ^ 2 * w - a) / (2 * u * w - u ^ 3), ?_⟩
    have hC2 : (2 * u * w - u ^ 3 : M) ≠ 0 := by
      intro h; apply hC
      have := congrArg (algebraMap M ℂ) h
      simpa [map_sub, map_mul, map_pow, map_ofNat] using this
    have hC3 : algebraMap M ℂ (2 * u * w - u ^ 3) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap M ℂ).injective).2 hC2
    rw [map_div₀, map_neg, div_eq_iff hC3]
    simp only [map_sub, map_mul, map_pow, map_ofNat] at hC3 ⊢
    linear_combination -key

end PrimeIndex

/-! ### Descent to prime index -/

/-- **A field `K ⊆ ℂ` with `i ∈ K` and `[ℂ : K] < ∞` has `K = ℂ`** (Artin–Schreier, characteristic `0`). -/
theorem finrank_eq_one_of_I_mem (K : Type) [Field K] [Algebra K ℂ] [FiniteDimensional K ℂ]
    (hI : ∃ i : K, algebraMap K ℂ i = Complex.I) : finrank K ℂ = 1 := by
  by_contra hne
  haveI := charZero_of_algebra_complex K
  set n := finrank K ℂ with hn
  have hnpos : 0 < n := Module.finrank_pos
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hne
  have hpn : p ∣ n := Nat.minFac_dvd n
  haveI : Fact p.Prime := ⟨hp⟩
  -- adjoin a primitive `p`-th root of unity
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p) with hζdef
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  let K' : IntermediateField K ℂ := IntermediateField.adjoin K {ζ}
  haveI : FiniteDimensional K' ℂ := Module.Finite.of_restrictScalars_finite K K' ℂ
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hd : finrank K K' = (minpoly K ζ).natDegree := IntermediateField.adjoin.finrank hint
  have hdle : (minpoly K ζ).natDegree ≤ p - 1 := by
    have hroot : aeval ζ (cyclotomic p K) = 0 := by
      have := hζ.isRoot_cyclotomic hp.pos
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this
    have hdvd := minpoly.dvd K ζ hroot
    have := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p K)
    rwa [natDegree_cyclotomic, Nat.totient_prime hp] at this
  have hdpos : 0 < (minpoly K ζ).natDegree := minpoly.natDegree_pos hint
  have hmul : finrank K K' * finrank K' ℂ = n := Module.finrank_mul_finrank K K' ℂ
  have hcop : Nat.Coprime p (finrank K K') := by
    rw [hd]
    exact Nat.coprime_of_lt_prime hdpos.ne' (lt_of_le_of_lt hdle (Nat.sub_lt hp.pos one_pos)) hp
  have hpK' : p ∣ finrank K' ℂ := by
    have : p ∣ finrank K K' * finrank K' ℂ := by rw [hmul]; exact hpn
    exact hcop.dvd_of_dvd_mul_left this
  -- a subgroup of order `p` of the Galois group
  haveI : IsGalois K' ℂ := isGalois_complex K'
  have hcard : Nat.card Gal(ℂ/K') = finrank K' ℂ := IsGalois.card_aut_eq_finrank K' ℂ
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Gal(ℂ/K')) p (by rw [hcard]; exact hpK')
  let H : Subgroup Gal(ℂ/K') := Subgroup.zpowers g
  have hH : Nat.card H = p := by rw [Nat.card_zpowers, hg]
  let M : IntermediateField K' ℂ := IntermediateField.fixedField H
  have hMfr : finrank M ℂ = p := by
    rw [IntermediateField.finrank_fixedField_eq_card H, hH]
  haveI : FiniteDimensional M ℂ := Module.Finite.of_restrictScalars_finite K' M ℂ
  -- `ζ` and `i` lie in `M`
  have hζK' : ζ ∈ K' := IntermediateField.mem_adjoin_simple_self K ζ
  have hζM : ζ ∈ M := by
    have := M.algebraMap_mem (⟨ζ, hζK'⟩ : K')
    simpa using this
  have hz : IsPrimitiveRoot (⟨ζ, hζM⟩ : M) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap M ℂ) (by simpa using hζ)
      (algebraMap M ℂ).injective
  by_cases hp2 : p = 2
  · obtain ⟨i0, hi0⟩ := hI
    have hiK' : Complex.I ∈ K' := by
      rw [← hi0]; exact K'.algebraMap_mem i0
    have hiM : Complex.I ∈ M := by
      have := M.algebraMap_mem (⟨Complex.I, hiK'⟩ : K')
      simpa using this
    refine no_prime_index_two M (by rw [hMfr, hp2]) ⟨Complex.I, hiM⟩ ?_
    apply Subtype.ext
    simp [Complex.I_sq]
  · exact no_prime_index_odd M p hp hp2 hMfr ⟨ζ, hζM⟩ hz

/-- **Finite-index subfields of `ℝ` are `ℝ`.** -/
theorem finite_index_subfield_real (F : IntermediateField ℚ ℝ) [FiniteDimensional F ℝ] : F = ⊤ := by
  haveI : FiniteDimensional F ℂ := Module.Finite.trans ℝ ℂ
  let Fi : IntermediateField F ℂ := IntermediateField.adjoin F {Complex.I}
  haveI : FiniteDimensional Fi ℂ := Module.Finite.of_restrictScalars_finite F Fi ℂ
  have h1 : finrank Fi ℂ = 1 :=
    finrank_eq_one_of_I_mem Fi ⟨⟨Complex.I, IntermediateField.mem_adjoin_simple_self F _⟩, rfl⟩
  haveI : Algebra.IsIntegral F ℂ := Algebra.IsIntegral.of_finite F ℂ
  have hint : IsIntegral F Complex.I := Algebra.IsIntegral.isIntegral _
  have hFi_deg : finrank F Fi = (minpoly F Complex.I).natDegree := IntermediateField.adjoin.finrank hint
  have hdeg2 : (minpoly F Complex.I).natDegree ≤ 2 := by
    have hroot : aeval Complex.I (X ^ 2 + 1 : F[X]) = 0 := by simp
    have hdvd := minpoly.dvd F Complex.I hroot
    have := natDegree_le_of_dvd hdvd (X_pow_add_C_ne_zero (by norm_num : 0 < 2) (1 : F))
    have h2 : (X ^ 2 + 1 : F[X]).natDegree = 2 := by
      simpa using (natDegree_X_pow_add_C (n := 2) (r := (1 : F)))
    omega
  have htower : finrank F Fi * finrank Fi ℂ = finrank F ℂ := Module.finrank_mul_finrank F Fi ℂ
  have hFR : finrank F ℝ * finrank ℝ ℂ = finrank F ℂ := Module.finrank_mul_finrank F ℝ ℂ
  rw [Complex.finrank_real_complex] at hFR
  rw [h1, mul_one, hFi_deg] at htower
  have hpos : 0 < finrank F ℝ := Module.finrank_pos
  have hone : finrank F ℝ = 1 := by omega
  rw [eq_top_iff]
  intro x _
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : ℝ) one_ne_zero).1 hone x
  rw [← hc]
  have hc1 : c • (1 : ℝ) = (c : ℝ) := by simp [Algebra.smul_def]
  rw [hc1]; exact c.2

end LeanCheck
