import LeanCheck.ChainY2

/-!
# Theorem F, failure direction: if `H(M)` fails, an irrational-parameter character is continuous
(TVGQ-v7 Theorem 17.3 `chains:F`, second sentence; HamelCharactersTVG_v18 Theorem D.3)

For a chain `M` with `¬H(M)` there is an irrational `γ` such that `q ↦ p(γ q)` is continuous for `ξ_{range M}`.
-/

namespace LeanCheck

open Filter Topology

/-- The rational character `q ↦ p(γ q)`. -/
noncomputable def psiQ (γ : ℝ) : ℚ →+ Circ where
  toFun q := ((γ * (q : ℝ) : ℝ) : Circ)
  map_zero' := by simp
  map_add' a b := by push_cast; rw [mul_add, AddCircle.coe_add]

lemma psiQ_apply (γ : ℝ) (q : ℚ) : psiQ γ q = ((γ * (q : ℝ) : ℝ) : Circ) := rfl

/-- Two centered representatives of a point whose first is `< 1/2` in absolute value coincide. -/
lemma eq_of_circ_eq_small {x y : ℝ} (h : (y : Circ) = (x : Circ)) (hy : |y| ≤ 1 / 2) (hx : |x| < 1 / 2) :
    y = x := by
  have h0 : ((y - x : ℝ) : Circ) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
  have hn' : (n : ℝ) = y - x := by simpa using hn
  have hlt : |(n : ℝ)| < 1 := by
    rw [hn']
    calc |y - x| ≤ |y| + |x| := abs_sub _ _
      _ < 1 / 2 + 1 / 2 := by linarith
      _ = 1 := by norm_num
  have : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  rw [this] at hn'
  simp at hn'
  linarith

/-- Two summable real series that agree beyond some point and differ termwise by integers have the same circle
reduction. -/
lemma tsum_circ_eq {t y : ℕ → ℝ} (hts : Summable t) (hys : Summable y) (hint : ∀ s, ∃ n : ℤ, t s - y s = n)
    (htail : ∃ s0, ∀ s, s0 ≤ s → t s = y s) :
    ((∑' s, t s : ℝ) : Circ) = ((∑' s, y s : ℝ) : Circ) := by
  obtain ⟨s0, hs0⟩ := htail
  have h1 := hts.sum_add_tsum_nat_add s0
  have h2 := hys.sum_add_tsum_nat_add s0
  have htails : ∑' s, t (s + s0) = ∑' s, y (s + s0) :=
    tsum_congr (fun s => hs0 _ (by omega))
  have hdiff : (∑' s, t s) - (∑' s, y s) = ∑ s ∈ Finset.range s0, (t s - y s) := by
    rw [← h1, ← h2, htails, Finset.sum_sub_distrib]; ring
  have hZ : ∃ n : ℤ, ∑ s ∈ Finset.range s0, (t s - y s) = n := by
    choose n hn using hint
    refine ⟨∑ s ∈ Finset.range s0, n s, ?_⟩
    push_cast
    exact Finset.sum_congr rfl (fun s _ => hn s)
  obtain ⟨n, hn⟩ := hZ
  have : ((∑' s, t s : ℝ) : Circ) - ((∑' s, y s : ℝ) : Circ) = 0 := by
    rw [← AddCircle.coe_sub, hdiff, hn, AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩
  exact sub_eq_zero.1 this

lemma summable_inv_two_pow (N : ℕ → ℕ) (h : ∀ s, 2 ^ s ≤ N s) : Summable (fun s => 1 / (N s : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_) (summable_geometric_two)
  have h1 : (2 : ℝ) ^ s ≤ N s := by exact_mod_cast h s
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  calc 1 / (N s : ℝ) ≤ 1 / 2 ^ s := one_div_le_one_div_of_le h2 h1
    _ = (1 / 2) ^ s := by rw [one_div_pow]

/-- Core estimate of Theorem F (failure direction). -/
lemma core_estimate {M : ℕ → ℕ} (hM : ChainSeq M) {A : ℝ} (hA : 2 < A) (a b : ℕ → ℕ)
    (hab : ∀ s, a s + (s + 1) ≤ b s ∧ IsRun M A (a s) (b s) ∧ b s + (s + 1) ≤ a (s + 1))
    (δ : ℝ) (hδ : δ = 1 / (2 * (A + 1))) (q : ℚ)
    (hq : ∀ i, ‖(((q : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < δ) :
    ‖((∑' s, (q : ℝ) / (M (b s) : ℝ) : ℝ) : Circ)‖ < 1 / 4 := by
  classical
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδ4 : δ < 1 / 4 := by
    rw [hδ, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hAδ : δ * (1 + A) < 1 := by
    have : δ * (1 + A) = 1 / 2 := by rw [hδ]; field_simp; ring
    linarith
  choose y hy1 hy2 hy3 using fun i => exists_centered (((q : ℝ) / (M i : ℝ) : ℝ) : Circ)
  have hylt : ∀ i, |y i| < δ := fun i => by rw [← hy3 i]; exact hq i
  choose α hα1 hα2 using fun i => hM.ratio_spec i
  have hMpos : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM.pos i
  have hint : ∀ j, ∃ n : ℤ, y j - α j * y (j + 1) = n := by
    intro j
    have h0 : ((y j - α j * y (j + 1) : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_sub, ← nsmul_coe_circ, hy1 j, hy1 (j + 1)]
      rw [nsmul_coe_circ, sub_eq_zero]
      congr 1
      have h1 : (M (j + 1) : ℝ) = α j * M j := by exact_mod_cast hα1 j
      have h2 : (M j : ℝ) ≠ 0 := (hMpos j).ne'
      have h3 : (α j : ℝ) ≠ 0 := by
        have : 2 ≤ α j := hα2 j
        exact_mod_cast (by omega : α j ≠ 0)
      rw [h1]; field_simp
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨n, by simpa using hn.symm⟩
  have hyb : ∀ s, |y (b s)| < δ / 2 ^ (s + 1) := by
    intro s
    obtain ⟨hs1, hrun, -⟩ := hab s
    have hk := contract_down hAδ y α (a s) (b s - a s)
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
    have h1 : |y (b s)| < δ / 2 ^ (b s - a s) := by
      rw [lt_div_iff₀ hpos]; exact lt_of_le_of_lt hk (hylt _)
    exact lt_of_lt_of_le h1 (div_le_div_of_nonneg_left hδpos.le hpos' hpow)
  -- the tail
  have hMb : ∀ s, 2 ^ s ≤ M (b s) := fun s =>
    (Nat.pow_le_pow_right (by norm_num) (by have := (hab s).1; omega)).trans (hM.pow_le (b s))
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, 2 * |(q : ℝ)| < 2 ^ s0 := pow_unbounded_of_one_lt _ (by norm_num)
  have htail : ∀ s, s0 ≤ s → y (b s) = (q : ℝ) / M (b s) := by
    intro s hs
    have hx : |(q : ℝ) / M (b s)| < 1 / 2 := by
      rw [abs_div, abs_of_pos (hMpos _), div_lt_iff₀ (hMpos _)]
      have h1 : (2 : ℝ) ^ s0 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hs
      have h2 : (2 : ℝ) ^ s ≤ M (b s) := by exact_mod_cast hMb s
      nlinarith [abs_nonneg (q : ℝ)]
    exact eq_of_circ_eq_small (hy1 (b s)) (hy2 _) hx
  have hgsum : Summable (fun s : ℕ => δ / 2 / 2 ^ s) := (hasSum_geometric_two' δ).summable
  have hysum : Summable (fun s => y (b s)) := by
    refine Summable.of_norm_bounded hgsum (fun s => ?_)
    rw [Real.norm_eq_abs]
    have := hyb s
    calc |y (b s)| ≤ δ / 2 ^ (s + 1) := this.le
      _ = δ / 2 / 2 ^ s := by rw [pow_succ]; field_simp
  have htsum : Summable (fun s => (q : ℝ) / (M (b s) : ℝ)) := by
    have := (summable_inv_two_pow (fun s => M (b s)) hMb).mul_left (q : ℝ)
    simpa [div_eq_mul_inv] using this
  have hcirc := tsum_circ_eq htsum hysum (fun s => by
    have h0 : ((((q : ℝ) / (M (b s) : ℝ)) - y (b s) : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_sub, ← hy1 (b s), sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨n, by simpa using hn.symm⟩) ⟨s0, fun s hs => (htail s hs).symm⟩
  rw [hcirc]
  have hbound : ‖∑' s, y (b s)‖ ≤ δ := by
    refine tsum_of_norm_bounded (hasSum_geometric_two' δ) (fun s => ?_)
    rw [Real.norm_eq_abs]
    have := hyb s
    calc |y (b s)| ≤ δ / 2 ^ (s + 1) := this.le
      _ = δ / 2 / 2 ^ s := by rw [pow_succ]; field_simp
  calc ‖((∑' s, y (b s) : ℝ) : Circ)‖ ≤ |∑' s, y (b s)| := by
        simpa using norm_coe_le (∑' s, y (b s)) 0
    _ ≤ δ := by simpa using hbound
    _ < 1 / 4 := hδ4

/-- A fast-growing divisibility series has irrational sum. -/
lemma irrational_series (N : ℕ → ℕ) (hpos : ∀ s, 0 < N s) (hdvd : ∀ s t, s ≤ t → N s ∣ N t)
    (hgrow : ∀ s, 2 ^ (s + 1) * N s ≤ N (s + 1)) : Irrational (∑' s, 1 / (N s : ℝ)) := by
  rintro ⟨r, hr⟩
  classical
  have hN2 : ∀ s, 2 ^ s ≤ N s := by
    intro s
    induction s with
    | zero => have := hpos 0; simp; omega
    | succ s ih =>
      have := hgrow s
      calc 2 ^ (s + 1) = 2 ^ (s + 1) * 1 := by ring
        _ ≤ 2 ^ (s + 1) * N s := by gcongr; exact hpos s
        _ ≤ N (s + 1) := this
  have hsum := summable_inv_two_pow N hN2
  have hNr : ∀ s, (0 : ℝ) < N s := fun s => by exact_mod_cast hpos s
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (r.den : ℝ) < 2 ^ k := pow_unbounded_of_one_lt _ (by norm_num)
  set γ : ℝ := ∑' s, 1 / (N s : ℝ) with hγ
  set Nk : ℕ := ∑ s ∈ Finset.range (k + 1), N k / N s with hNk
  have hS : (N k : ℝ) * ∑ s ∈ Finset.range (k + 1), 1 / (N s : ℝ) = Nk := by
    rw [hNk, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hsk : s ≤ k := by simpa [Nat.lt_succ_iff] using hs
    obtain ⟨c, hc⟩ := hdvd s k hsk
    have hc' : N k / N s = c := by
      rw [hc]; exact Nat.mul_div_cancel_left c (hpos s)
    rw [hc', hc]; push_cast
    have := (hNr s).ne'
    field_simp
  have hR : γ - ∑ s ∈ Finset.range (k + 1), 1 / (N s : ℝ) = ∑' s, 1 / (N (s + (k + 1)) : ℝ) := by
    have := hsum.sum_add_tsum_nat_add (k + 1)
    linarith
  have hsum2 : Summable (fun s => 1 / (N (s + (k + 1)) : ℝ)) :=
    (summable_nat_add_iff (k + 1)).2 hsum
  have hgrow1 : ∀ t, 2 * N t ≤ N (t + 1) := fun t => by
    have := hgrow t
    calc 2 * N t ≤ 2 ^ (t + 1) * N t := by
          gcongr
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ N (t + 1) := this
  have hNs : ∀ s, 2 ^ s * N (k + 1) ≤ N (s + (k + 1)) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      calc 2 ^ (s + 1) * N (k + 1) = 2 * (2 ^ s * N (k + 1)) := by ring
        _ ≤ 2 * N (s + (k + 1)) := by gcongr
        _ ≤ N (s + 1 + (k + 1)) := by
          have := hgrow1 (s + (k + 1)); rw [show s + 1 + (k + 1) = s + (k + 1) + 1 by ring]; exact this
  have hRpos : 0 < ∑' s, 1 / (N (s + (k + 1)) : ℝ) := by
    refine hsum2.tsum_pos (fun s => by positivity) 0 (by simpa using hNr (0 + (k + 1)))
  have hRle : ∑' s, 1 / (N (s + (k + 1)) : ℝ) ≤ 2 / N (k + 1) := by
    have hg : HasSum (fun s : ℕ => (1 / (N (k + 1) : ℝ)) * (1 / 2) ^ s) ((1 / (N (k + 1) : ℝ)) * 2) := by
      have := (hasSum_geometric_two).mul_left (1 / (N (k + 1) : ℝ))
      simpa using this
    have hle : ∑' s, 1 / (N (s + (k + 1)) : ℝ) ≤ (1 / (N (k + 1) : ℝ)) * 2 := by
      refine hasSum_le (fun s => ?_) hsum2.hasSum hg
      have h1 : (2 : ℝ) ^ s * N (k + 1) ≤ N (s + (k + 1)) := by exact_mod_cast hNs s
      have h2 : (0 : ℝ) < 2 ^ s * N (k + 1) := by have := hNr (k + 1); positivity
      calc 1 / (N (s + (k + 1)) : ℝ) ≤ 1 / (2 ^ s * N (k + 1)) := one_div_le_one_div_of_le h2 h1
        _ = (1 / (N (k + 1) : ℝ)) * (1 / 2) ^ s := by
          rw [one_div_pow]; field_simp
    calc _ ≤ _ := hle
      _ = 2 / N (k + 1) := by ring
  have hNk1 : 2 ^ (k + 1) * N k ≤ N (k + 1) := hgrow k
  -- the integer
  have hint : ((r.den : ℝ)) * ((N k : ℝ) * (γ - ∑ s ∈ Finset.range (k + 1), 1 / (N s : ℝ))) =
      ((r.num * N k - (r.den : ℤ) * Nk : ℤ) : ℝ) := by
    have h1 : (r.den : ℝ) * γ = r.num := by
      rw [← hr]
      have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num r)
      push_cast at h
      linarith
    push_cast
    rw [mul_sub, ← hS]
    have : (r.den : ℝ) * ((N k : ℝ) * γ) = r.num * N k := by rw [mul_left_comm, h1]; ring
    linarith
  set m : ℤ := r.num * N k - (r.den : ℤ) * Nk with hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    rw [← hint, hR]
    have := hNr k
    have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    positivity
  have hmlt : (m : ℝ) < 1 := by
    rw [← hint, hR]
    have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    have hNk1' : (2 : ℝ) ^ (k + 1) * N k ≤ N (k + 1) := by exact_mod_cast hNk1
    have hNk0 := hNr k
    have hNk10 := hNr (k + 1)
    calc (r.den : ℝ) * (N k * ∑' s, 1 / (N (s + (k + 1)) : ℝ)) ≤ r.den * (N k * (2 / N (k + 1))) := by
          gcongr
      _ = r.den * 2 * (N k / N (k + 1)) := by ring
      _ ≤ r.den * 2 * (1 / 2 ^ (k + 1)) := by
          have hq : (N k : ℝ) / N (k + 1) ≤ 1 / 2 ^ (k + 1) := by
            rw [div_le_div_iff₀ hNk10 (by positivity)]; nlinarith
          exact mul_le_mul_of_nonneg_left hq (by positivity)
      _ = r.den / 2 ^ k := by rw [pow_succ]; field_simp
      _ < 1 := by rw [div_lt_one (by positivity)]; exact hk
  have hm1 : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hm2 : m < 1 := by exact_mod_cast hmlt
  omega

/-- **Theorem F, failure direction.**  If `H(M)` fails, there is an irrational `γ` for which `q ↦ p(γ q)` is a
continuous character of `ξ_{range M}`; in particular the character group differs from `Γ`. -/
theorem xi_neg {M : ℕ → ℕ} (hM : ChainSeq M) (hnot : ¬ HSeq M) :
    ∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (Set.range M)) circTop (psiQ γ) := by
  obtain ⟨A, hA, a, b, hab⟩ := exists_run_seq hnot
  have hbs : ∀ s, b s + (s + 1) ≤ b (s + 1) := fun s => by
    have h1 := (hab s).2.2
    have h2 := (hab (s + 1)).1
    omega
  have hbmono : Monotone b := monotone_nat_of_le_succ (fun s => by have := hbs s; omega)
  have hMb : ∀ s, 2 ^ s ≤ M (b s) := fun s =>
    (Nat.pow_le_pow_right (by norm_num) (by have := (hab s).1; omega)).trans (hM.pow_le (b s))
  have hgrow : ∀ s, 2 ^ (s + 1) * M (b s) ≤ M (b (s + 1)) := fun s => by
    have h1 := hM.pow_mul_le (hbmono (Nat.le_succ s))
    have h2 : 2 ^ (s + 1) ≤ 2 ^ (b (s + 1) - b s) :=
      Nat.pow_le_pow_right (by norm_num) (by have := hbs s; omega)
    calc 2 ^ (s + 1) * M (b s) ≤ 2 ^ (b (s + 1) - b s) * M (b s) := by gcongr
      _ ≤ M (b (s + 1)) := h1
  refine ⟨∑' s, 1 / (M (b s) : ℝ), irrational_series (fun s => M (b s)) (fun s => hM.pos _)
    (fun s t hst => hM.dvd_of_le (hbmono hst)) hgrow, ?_⟩
  set δ : ℝ := 1 / (2 * (A + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hW : xiSet (Set.range M) 1 δ ∈ @nhds ℚ (xi (Set.range M)) 0 :=
    (xi_nhds_hasBasis (Set.range M)).mem_of_mem (xiSet_mem (Set.range M) 1 one_pos δ hδpos)
  letI : TopologicalSpace ℚ := xi (Set.range M)
  haveI : IsTopologicalAddGroup ℚ := xi_group (Set.range M)
  refine continuous_of_quarter_gen (psiQ _) hW (fun q hq => ?_)
  have hq' : ∀ i, ‖(((q : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < δ := fun i => by
    have := hq (M i) ⟨i, rfl⟩
    simpa using this
  have := core_estimate hM hA a b hab δ hδ q hq'
  rw [psiQ_apply]
  have e : (∑' s, 1 / (M (b s) : ℝ)) * (q : ℝ) = ∑' s, (q : ℝ) / (M (b s) : ℝ) := by
    rw [← tsum_mul_right]
    exact tsum_congr (fun s => by ring)
  rw [e]
  exact this

end LeanCheck
