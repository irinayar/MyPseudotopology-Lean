import LeanCheck.ChainY6
import LeanCheck.ChainNecessaryMackey

/-!
# Theorem F (rational chain criterion): `dual(ξ_C) = Γ ⇔ H(C)`
(TVGQ-v7 Theorem 17.3 `chains:F`; HamelCharactersTVG_v18 Theorem D.3)

* `xi_dual_of_finite` : a finite nonempty set of positive integers gives `dual(ξ_C) = Γ`;
* `xi_dual_seq` : for an infinite chain `M`, `dual(ξ_{range M}) = Γ ⇔ H(M)`;
* `chains_F` : set formulation: for a divisibility chain `C` of positive integers, `dual(ξ_C) = Γ ⇔ H(C)`.
-/

namespace LeanCheck

open Filter Topology

/-- The rational characters `q ↦ p(r q)` are `ξ_C`-continuous when `C` is nonempty. -/
lemma xi_Gam_cont (C : Set ℕ) (hC : ∀ c ∈ C, 0 < c) (hne : C.Nonempty) (ψ : ℚ →+ Circ) (hψ : ψ ∈ Gam) :
    @Continuous ℚ Circ (xi C) circTop ψ := by
  obtain ⟨r, hr⟩ := hψ
  obtain ⟨c0, hc0⟩ := hne
  have hc0pos : 0 < c0 := hC c0 hc0
  set a : ℤ := r.num
  set b : ℕ := r.den
  have hbpos : 0 < b := r.den_pos
  set ε : ℝ := 1 / (8 * (|(a : ℝ)| * c0 + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hW : xiSet C b ε ∈ @nhds ℚ (xi C) 0 :=
    (xi_nhds_hasBasis C).mem_of_mem (xiSet_mem C b hbpos ε hεpos)
  letI : TopologicalSpace ℚ := xi C
  haveI : IsTopologicalAddGroup ℚ := xi_group C
  refine continuous_of_quarter_gen ψ hW (fun q hq => ?_)
  have h1 := hq c0 hc0
  -- ψ q = (a c0) • p(q / (b c0))
  have e : ψ q = ((a * c0 : ℤ)) • (((q / ((b : ℚ) * c0) : ℚ) : ℝ) : Circ) := by
    rw [hr q, zsmul_coe_circ]
    congr 1
    have hb : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have hc : (c0 : ℚ) ≠ 0 := by exact_mod_cast hc0pos.ne'
    have : (r : ℚ) = a / b := (Rat.num_div_den r).symm
    push_cast
    rw [show (r : ℚ) = a / b from this]
    push_cast
    field_simp
  rw [e]
  refine lt_of_le_of_lt (norm_zsmul_le _ _) ?_
  rw [Int.norm_eq_abs]
  have hx : ‖(((q / ((b : ℚ) * c0) : ℚ) : ℝ) : Circ)‖ < ε := h1
  have hac : |((a * c0 : ℤ) : ℝ)| = |(a : ℝ)| * c0 := by
    push_cast; rw [abs_mul, Nat.abs_cast]
  rw [hac]
  have hpos : 0 < |(a : ℝ)| * c0 + 1 := by positivity
  calc |(a : ℝ)| * c0 * ‖(((q / ((b : ℚ) * c0) : ℚ) : ℝ) : Circ)‖ ≤ (|(a : ℝ)| * c0) * ε := by
        gcongr
    _ = |(a : ℝ)| * c0 / (8 * (|(a : ℝ)| * c0 + 1)) := by rw [hε]; ring
    _ < 1 / 8 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg (a : ℝ), Nat.cast_nonneg (α := ℝ) c0]
    _ < 1 / 4 := by norm_num

lemma circ_zero_iff (x : ℝ) : ((x : ℝ) : Circ) = 0 ↔ ∃ n : ℤ, x = n := by
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩

/-- A continuous character is small on a basic neighbourhood. -/
lemma xi_cont_extract (C : Set ℕ) (ψ : ℚ →+ Circ) (h : @Continuous ℚ Circ (xi C) circTop ψ) :
    ∃ d : ℕ, 0 < d ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ xiSet C d ε, ‖ψ q‖ < 1 / 4 := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (ψ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℚ (xi C) 0 :=
    (@Continuous.continuousAt ℚ Circ (xi C) circTop ψ 0 h) hS
  obtain ⟨V, ⟨d, hd, ε, hε, rfl⟩, hV⟩ := (xi_nhds_hasBasis C).mem_iff.mp hpre
  exact ⟨d, hd, ε, hε, fun q hq => hV hq⟩

/-- **Finite case.**  For a finite nonempty set `C` of positive integers, `dual(ξ_C) = Γ`. -/
theorem xi_dual_of_finite (C : Set ℕ) (hC : ∀ c ∈ C, 0 < c) (hne : C.Nonempty) (hfin : C.Finite)
    (ψ : ℚ →+ Circ) : @Continuous ℚ Circ (xi C) circTop ψ ↔ ψ ∈ Gam := by
  refine ⟨fun h => ?_, xi_Gam_cont C hC hne ψ⟩
  obtain ⟨d, hd, ε, hε, hsmall⟩ := xi_cont_extract C ψ h
  obtain ⟨c, hc⟩ := char_Q_real ψ ε hε (fun q hq => hsmall q (xiSet_ball C d hd ε q hq))
  -- L = product of the elements of C
  set L : ℕ := ∏ c ∈ hfin.toFinset, c with hL
  have hLpos : 0 < L := Finset.prod_pos (fun c hc => hC c (hfin.mem_toFinset.1 hc))
  have hLdvd : ∀ c ∈ C, c ∣ L := fun c hc => Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hc)
  -- ψ (d L j) is small for all integers j
  have hj : ∀ j : ℤ, ‖ψ ((d * L * j : ℚ))‖ < 1 / 4 := by
    intro j
    apply hsmall
    intro c' hc'
    obtain ⟨m, hm⟩ := hLdvd c' hc'
    have hc'pos : (c' : ℚ) ≠ 0 := by exact_mod_cast (hC c' hc').ne'
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have : ((d : ℚ) * L * j) / ((d : ℚ) * c') = ((m * j : ℤ) : ℚ) := by
      rw [hm]; push_cast; field_simp
    rw [this]
    have h0 : ((((m * j : ℤ) : ℚ) : ℝ) : Circ) = 0 := by
      rw [circ_zero_iff]; exact ⟨m * j, by push_cast; simp⟩
    rw [h0, norm_zero]; exact hε
  -- hence ψ (d L) = 0
  have hzero : ψ ((d * L : ℚ)) = 0 := by
    set t : Circ := ψ ((d * L : ℚ)) with ht
    have hb : ∀ R : ℕ, 1 ≤ R → ‖t‖ ≤ 1 / (4 * R) := fun R hR => by
      apply norm_le_of_multiples t R hR
      intro j _
      have h1 := hj (j : ℤ)
      have e : ψ ((d * L * ((j : ℤ) : ℚ) : ℚ)) = j • t := by
        rw [show ((d : ℚ) * L * ((j : ℤ) : ℚ)) = j • ((d : ℚ) * L) by
          simp [nsmul_eq_mul, mul_comm], map_nsmul]
      rw [e] at h1
      exact h1
    by_contra hne
    have hpos : 0 < ‖t‖ := norm_pos_iff.2 hne
    obtain ⟨R, hR⟩ := exists_nat_gt (1 / (4 * ‖t‖))
    have hR1 : 1 ≤ R + 1 := by omega
    have h2 := hb (R + 1) hR1
    have hRr : 1 / (4 * ‖t‖) < ((R + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [div_lt_iff₀ (by positivity)] at hRr
    have h3 : ‖t‖ * (4 * ((R + 1 : ℕ) : ℝ)) ≤ 1 := by
      have hRpos : (0 : ℝ) < 4 * ((R + 1 : ℕ) : ℝ) := by positivity
      rwa [le_div_iff₀ hRpos] at h2
    nlinarith
  -- ψ q = p(c q), and c d L ∈ ℤ
  rw [hc, circ_zero_iff] at hzero
  obtain ⟨z, hz⟩ := hzero
  refine ⟨(z : ℚ) / (d * L), fun s => ?_⟩
  rw [hc s]
  congr 1
  have hdL : ((d : ℝ) * L) ≠ 0 := by
    have : 0 < d * L := Nat.mul_pos hd hLpos
    exact_mod_cast this.ne'
  have hc' : c = (z : ℝ) / (d * L) := by
    push_cast at hz
    field_simp
    linarith
  rw [hc']
  push_cast
  ring

/-- If `ψ q = p(c q)` for all `q` and `c m = z` with `m > 0` and `z` an integer, then `ψ ∈ Γ`. -/
lemma gam_of_real (ψ : ℚ →+ Circ) (c : ℝ) (hc : ∀ q : ℚ, ψ q = ((c * (q : ℝ) : ℝ) : Circ))
    (m : ℕ) (hm : 0 < m) (z : ℤ) (hz : c * m = z) : ψ ∈ Gam := by
  refine ⟨(z : ℚ) / m, fun s => ?_⟩
  rw [hc s]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc' : c = (z : ℝ) / m := by field_simp; linarith
  rw [hc']
  push_cast
  ring

/-- **Theorem F, compatible direction.**  If `H(M)` holds, every `ξ_{range M}`-continuous character is in `Γ`,
and conversely. -/
theorem xi_dual_seq {M : ℕ → ℕ} (hM : ChainSeq M) (hH : HSeq M) (ψ : ℚ →+ Circ) :
    @Continuous ℚ Circ (xi (Set.range M)) circTop ψ ↔ ψ ∈ Gam := by
  refine ⟨fun h => ?_, xi_Gam_cont (Set.range M) (fun c ⟨i, hi⟩ => hi ▸ hM.pos i) ⟨M 0, 0, rfl⟩ ψ⟩
  obtain ⟨d, hd, ε1, hε1, hsmall1⟩ := xi_cont_extract (Set.range M) ψ h
  set ε : ℝ := min ε1 (1 / 16) with hε
  have hεpos : 0 < ε := lt_min hε1 (by norm_num)
  have hε8 : ε < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsmall : ∀ q ∈ xiSet (Set.range M) d ε, ‖ψ q‖ < 1 / 4 := fun q hq =>
    hsmall1 q (fun c hc => lt_of_lt_of_le (hq c hc) (min_le_left _ _))
  obtain ⟨c, hc⟩ := char_Q_real ψ ε hεpos (fun q hq => hsmall q (xiSet_ball _ d hd ε q hq))
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hstar : ∀ n : ℤ, (∀ i, ‖(((n : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < ε) →
      ‖((c * d * n : ℝ) : Circ)‖ < 1 / 4 := by
    intro n hn
    have hq : ((d : ℚ) * n : ℚ) ∈ xiSet (Set.range M) d ε := by
      rintro _ ⟨i, rfl⟩
      have hMi : (M i : ℚ) ≠ 0 := by exact_mod_cast (hM.pos i).ne'
      have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      have : (((d : ℚ) * n) / ((d : ℚ) * (M i : ℕ)) : ℚ) = ((n : ℚ) / (M i : ℚ)) := by
        field_simp
      rw [this]
      push_cast
      exact hn i
    have := hsmall _ hq
    rw [hc] at this
    have e : c * (((d : ℚ) * n : ℚ) : ℝ) = c * d * n := by push_cast; ring
    rw [e] at this
    exact this
  obtain ⟨i, hi⟩ := key_prop hM hH hεpos hε8 (c' := c * d) (fun n hn => by simpa using hstar n hn)
  obtain ⟨z, hz⟩ := (circ_zero_iff _).1 hi
  exact gam_of_real ψ c hc (d * M i) (Nat.mul_pos hd (hM.pos i)) z (by push_cast; linarith)

/-- **Theorem F for a chain sequence.**  `dual(ξ_{range M}) = Γ` iff `H(M)`. -/
theorem chains_F_seq {M : ℕ → ℕ} (hM : ChainSeq M) :
    (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (Set.range M)) circTop ψ ↔ ψ ∈ Gam) ↔ HSeq M := by
  constructor
  · intro hdual
    by_contra hnot
    obtain ⟨γ, hirr, hcont⟩ := xi_neg hM hnot
    obtain ⟨r, hr⟩ := (hdual (psiQ γ)).1 hcont
    have h1 := hr 1
    rw [psiQ_apply] at h1
    simp only [Rat.cast_one, mul_one] at h1
    have h2 : ((γ - (r : ℝ) : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_sub, h1]
      simp
    obtain ⟨n, hn⟩ := (circ_zero_iff _).1 h2
    exact hirr ⟨r + n, by push_cast; linarith⟩
  · intro hH ψ
    exact xi_dual_seq hM hH ψ

end LeanCheck
