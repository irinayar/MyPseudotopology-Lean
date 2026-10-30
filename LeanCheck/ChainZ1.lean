import LeanCheck.ChainY7

/-!
# Theorem G, failure direction: if `H(M)` fails, `λ_{range M}` is not compatible
(TVGQ-v7 Theorem 17.6 `chains:G`, first half; HamelCharactersTVG_v18 Theorem D.6)

For a chain `M` with `M 0 = 1` and profinitely null (every positive integer divides some `M_n`), with `¬H(M)`,
the profinite integer `ζ = ∑_s M_{a_s}` (over the starts `a_s` of ever longer runs) is a noninteger character of
`ℚ/ℤ` that is continuous for `λ_{range M}`.
-/

namespace LeanCheck

open Filter Topology

/-- Ascending contraction: if `y_{j+1} = r_j y_j` modulo integers on `[a, a+k]` with `2 ≤ r_j ≤ A`,
`δ (1 + A) < 1` and `|y_j| < δ`, then `|y_a| 2^k ≤ |y_{a+k}|`. -/
lemma contract_up {δ A : ℝ} (hA : δ * (1 + A) < 1) (y : ℕ → ℝ) (r : ℕ → ℕ) (a : ℕ) :
    ∀ k : ℕ, (∀ j, a ≤ j → j < a + k → 2 ≤ r j) → (∀ j, a ≤ j → j < a + k → (r j : ℝ) ≤ A) →
      (∀ j, a ≤ j → j ≤ a + k → |y j| < δ) →
      (∀ j, a ≤ j → j < a + k → ∃ n : ℤ, y (j + 1) - r j * y j = n) →
      |y a| * 2 ^ k ≤ |y (a + k)| := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp
  | succ k ih =>
    intro hr2 hrA hy hint
    have ih' := ih (fun j h1 h2 => hr2 j h1 (by omega)) (fun j h1 h2 => hrA j h1 (by omega))
      (fun j h1 h2 => hy j h1 (by omega)) (fun j h1 h2 => hint j h1 (by omega))
    have hstep : y (a + k + 1) = r (a + k) * y (a + k) :=
      contraction_step (hrA (a + k) (by omega) (by omega)) hA (hy (a + k) (by omega) (by omega))
        (hy (a + k + 1) (by omega) le_rfl) (hint (a + k) (by omega) (by omega))
    have hr2' : (2 : ℝ) ≤ r (a + k) := by exact_mod_cast hr2 (a + k) (by omega) (by omega)
    have habs : |y (a + k + 1)| = r (a + k) * |y (a + k)| := by
      rw [hstep, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r (a + k))]
    calc |y a| * 2 ^ (k + 1) = (|y a| * 2 ^ k) * 2 := by ring
      _ ≤ |y (a + k)| * 2 := by gcongr
      _ ≤ r (a + k) * |y (a + k)| := by nlinarith [abs_nonneg (y (a + k))]
      _ = |y (a + (k + 1))| := by rw [← habs, ← add_assoc]

section ZetaSum

variable {M : ℕ → ℕ}

lemma exists_kill (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (x : TorsA) :
    ∃ K, ∀ n ≥ K, M n • (x : Circ) = 0 := by
  obtain ⟨k, hk⟩ := exists_k hnull x
  exact ⟨k, fun n hn => kill_of_dvd hM.dvd hn hk⟩

/-- The profinite integer `∑_s M_{a_s}` as a character of `ℚ/ℤ`. -/
noncomputable def zetaSum (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (a : ℕ → ℕ) (ha : StrictMono a) : TorsA →+ Circ where
  toFun x := ∑ᶠ s, (M (a s)) • (x : Circ)
  map_zero' := by simp
  map_add' x y := by
    have hfin : ∀ x : TorsA, (Function.support fun s => (M (a s)) • (x : Circ)).Finite := by
      intro x
      obtain ⟨K, hK⟩ := exists_kill hM hnull x
      refine (Set.finite_lt_nat K).subset (fun s hs => ?_)
      by_contra hsK
      have hsK' : K ≤ s := by simpa using hsK
      exact hs (hK (a s) (hsK'.trans (ha.id_le s)))
    simp only [AddSubgroup.coe_add, smul_add]
    exact finsum_add_distrib (hfin x) (hfin y)

lemma zetaSum_apply (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (a : ℕ → ℕ) (ha : StrictMono a) (x : TorsA) (K : ℕ) (hK : ∀ n ≥ K, M n • (x : Circ) = 0) :
    zetaSum hM hnull a ha x = ∑ s ∈ Finset.range K, (M (a s)) • (x : Circ) := by
  show ∑ᶠ s, (M (a s)) • (x : Circ) = _
  refine finsum_eq_sum_of_support_subset _ (fun s hs => ?_)
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hsK
  push_neg at hsK
  exact hs (hK (a s) (hsK.trans (ha.id_le s)))

/-- The partial sums `P_s = ∑_{t<s} M_{a_t}` are small compared with `M_{a_s}`. -/
lemma partial_sum_small (hM : ChainSeq M) (a : ℕ → ℕ) (ha2 : ∀ s, a s + 2 ≤ a (s + 1)) (s : ℕ) :
    3 * (∑ t ∈ Finset.range s, M (a t)) ≤ M (a s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have h4 : 4 * M (a s) ≤ M (a (s + 1)) := by
      have := hM.pow_mul_le (show a s ≤ a (s + 1) by have := ha2 s; omega)
      have h2 : 4 ≤ 2 ^ (a (s + 1) - a s) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (a (s + 1) - a s) := Nat.pow_le_pow_right (by norm_num) (by have := ha2 s; omega)
      calc 4 * M (a s) ≤ 2 ^ (a (s + 1) - a s) * M (a s) := by gcongr
        _ ≤ M (a (s + 1)) := this
    omega

/-- **Theorem G, failure direction.**  If `H(M)` fails, there is a noninteger character of `ℚ/ℤ` that is
continuous for `λ_{range M}`. -/
theorem tors_neg (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (hnot : ¬ HSeq M) :
    ∃ ζ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M)).topology _ ζ ∧
      ∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ) := by
  obtain ⟨A, hA, a, b, hab⟩ := exists_run_seq hnot
  have ha2 : ∀ s, a s + 2 ≤ a (s + 1) := fun s => by
    have h1 := (hab s).1
    have h2 := (hab s).2.2
    omega
  have ha : StrictMono a := strictMono_nat_of_lt_succ (fun s => by have := ha2 s; omega)
  set ζ := zetaSum hM hnull a ha with hζ
  have hMpos : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM.pos i
  set δ : ℝ := 1 / (2 * (A + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ4 : δ < 1 / 4 := by
    rw [hδ, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hAδ : δ * (1 + A) < 1 := by
    have : δ * (1 + A) = 1 / 2 := by rw [hδ]; field_simp; ring
    linarith
  refine ⟨ζ, ?_, ?_⟩
  · refine continuous_of_quarter (Set.range M) ζ ⟨δ, hδpos, fun x hx => ?_⟩
    obtain ⟨K, hK⟩ := exists_kill hM hnull x
    rw [hζ, zetaSum_apply hM hnull a ha x K hK]
    choose y hy1 hy2 hy3 using fun j => exists_centered (M j • (x : Circ))
    have hylt : ∀ j, |y j| < δ := fun j => by rw [← hy3 j]; exact hx (M j) ⟨j, rfl⟩
    choose α hα1 hα2 using fun i => hM.ratio_spec i
    have hint : ∀ j, ∃ n : ℤ, y (j + 1) - α j * y j = n := by
      intro j
      have h0 : ((y (j + 1) - α j * y j : ℝ) : Circ) = 0 := by
        rw [AddCircle.coe_sub, ← nsmul_coe_circ, hy1 j, hy1 (j + 1), hα1 j, mul_smul, sub_self]
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
      exact ⟨n, by simpa using hn.symm⟩
    have hyb : ∀ s, |y (a s)| < δ / 2 ^ (s + 1) := by
      intro s
      obtain ⟨hs1, hrun, -⟩ := hab s
      have hk := contract_up hAδ y α (a s) (b s - a s)
        (fun j _ _ => hα2 j)
        (fun j hj1 hj2 => by
          have := hrun j hj1 (by omega)
          have h1 : (M (j + 1) : ℝ) = α j * M j := by exact_mod_cast hα1 j
          rw [h1] at this
          exact (lt_of_mul_lt_mul_right this (hMpos j).le).le)
        (fun j _ _ => hylt j)
        (fun j _ _ => hint j)
      have hab' : a s + (b s - a s) = b s := by omega
      rw [hab'] at hk
      have hpow : (2 : ℝ) ^ (s + 1) ≤ 2 ^ (b s - a s) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpos : (0 : ℝ) < 2 ^ (b s - a s) := by positivity
      have hpos' : (0 : ℝ) < 2 ^ (s + 1) := by positivity
      have h1 : |y (a s)| < δ / 2 ^ (b s - a s) := by
        rw [lt_div_iff₀ hpos]; exact lt_of_le_of_lt hk (hylt _)
      exact lt_of_lt_of_le h1 (div_le_div_of_nonneg_left hδpos.le hpos' hpow)
    have hsum : ∑ s ∈ Finset.range K, M (a s) • (x : Circ) =
        ((∑ s ∈ Finset.range K, y (a s) : ℝ) : Circ) := by
      have key : ((∑ s ∈ Finset.range K, y (a s) : ℝ) : Circ) = ∑ s ∈ Finset.range K, ((y (a s) : ℝ) : Circ) :=
        map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (fun s => y (a s)) (Finset.range K)
      rw [key]
      exact Finset.sum_congr rfl (fun s _ => (hy1 (a s)).symm)
    rw [hsum]
    refine lt_of_le_of_lt ((norm_coe_le _ 0).trans ?_) hδ4
    rw [Int.cast_zero, sub_zero]
    calc |∑ s ∈ Finset.range K, y (a s)| ≤ ∑ s ∈ Finset.range K, |y (a s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.range K, δ / 2 ^ (s + 1) := Finset.sum_le_sum (fun s _ => (hyb s).le)
      _ = δ / 2 * ∑ s ∈ Finset.range K, (1 / 2 : ℝ) ^ s := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [pow_succ, one_div_pow]; field_simp
      _ ≤ δ / 2 * 2 := by gcongr; exact sum_geometric_two_le K
      _ = δ := by ring
  · intro u
    by_contra hcon
    push_neg at hcon
    -- some `s0` with `2 |u| < 2^{s0}`
    obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, 2 * u.natAbs < 2 ^ s0 :=
      ⟨2 * u.natAbs, Nat.lt_two_pow_self⟩
    have hMlarge : ∀ s, s0 ≤ s → 2 * u.natAbs < M (a s) := fun s hs =>
      lt_of_lt_of_le hs0 ((Nat.pow_le_pow_right (by norm_num) hs).trans
        ((Nat.pow_le_pow_right (by norm_num) (ha.id_le s)).trans (hM.pow_le (a s))))
    have hkey : ∀ s, s0 ≤ s → ((∑ t ∈ Finset.range s, M (a t) : ℕ) : ℤ) = u := by
      intro s hs
      set P : ℕ := ∑ t ∈ Finset.range s, M (a t) with hP
      set xs : TorsA := piHom (1 / (M (a s) : ℚ)) with hxs
      have hMs : (0 : ℝ) < M (a s) := by exact_mod_cast hM.pos (a s)
      have hxsc : (xs : Circ) = ((1 / (M (a s) : ℝ) : ℝ) : Circ) := by
        rw [hxs, piHom_coe]; push_cast; rfl
      have hkill : ∀ n, a s ≤ n → M n • (xs : Circ) = 0 := by
        intro n hn
        obtain ⟨c, hc⟩ := hM.dvd_of_le hn
        rw [hxsc, nsmul_coe_circ, circ_zero_iff]
        refine ⟨c, ?_⟩
        rw [hc]; push_cast; field_simp
      have hζx : ζ xs = P • (xs : Circ) := by
        rw [hζ, zetaSum_apply hM hnull a ha xs (a s) hkill]
        have hsub : Finset.range s ⊆ Finset.range (a s) := by
          intro t ht
          rw [Finset.mem_range] at ht ⊢
          exact lt_of_lt_of_le (lt_of_lt_of_le ht (ha.id_le s)) le_rfl
        rw [← Finset.sum_subset hsub (fun t ht ht' => ?_), hP, Finset.sum_smul]
        rw [Finset.mem_range] at ht'
        exact hkill _ (ha.monotone (not_lt.1 ht'))
      have h1 := hcon xs
      rw [hζx] at h1
      have h2 : ((P : ℤ) - u) • (xs : Circ) = 0 := by
        rw [sub_zsmul, natCast_zsmul, h1]
        abel
      rw [hxsc, zsmul_coe_circ, circ_zero_iff] at h2
      obtain ⟨k, hk⟩ := h2
      have hdvd : (M (a s) : ℤ) ∣ (P : ℤ) - u := by
        refine ⟨k, ?_⟩
        have : (((P : ℤ) - u : ℤ) : ℝ) = (M (a s) : ℝ) * k := by
          have := hk
          field_simp at this
          linarith
        exact_mod_cast this
      have hsmall := partial_sum_small hM a ha2 s
      have hMl := hMlarge s hs
      have habs : |(P : ℤ) - u| < M (a s) := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by simpa using habs)
      omega
    have h1 := hkey s0 le_rfl
    have h2 := hkey (s0 + 1) (by omega)
    rw [Finset.sum_range_succ] at h2
    have hpos := hM.pos (a s0)
    push_cast at h1 h2
    omega

end ZetaSum

end LeanCheck
