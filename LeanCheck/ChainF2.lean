import LeanCheck.ChainF1

/-!
# The join of the two prime-square topologies is still weaker than the usual topology
(HamelCharactersTVG_v18 Proposition 22.3 `prop:prime-join-v8`)

Every zero-neighbourhood of `γ_2 ∨ γ_3` contains arbitrarily large positive integers; hence the join is strictly coarser than the usual
topology of `ℚ` and its restriction to `ℤ` is nondiscrete.  The proof uses simultaneous Dirichlet approximation, which we prove by
the pigeonhole principle on boxes of the torus.
-/

namespace LeanCheck

open Filter Topology

section Dirichlet

lemma coe_int_circ_zero (n : ℤ) : ((n : ℝ) : Circ) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp⟩

/-- **Simultaneous Dirichlet approximation.**  For finitely many reals `v i` and `L > 0` there is `1 ≤ z ≤ L^card` such that all
`z v i` are within `1/L` of an integer. -/
theorem dirichlet_multi {ι : Type} [Fintype ι] (L : ℕ) (hL : 0 < L) (v : ι → ℝ) :
    ∃ z : ℕ, 1 ≤ z ∧ z ≤ L ^ Fintype.card ι ∧ ∀ i, ‖(((z : ℝ) * v i : ℝ) : Circ)‖ ≤ 1 / L := by
  classical
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let box : Fin (L ^ Fintype.card ι + 1) → (ι → Fin L) := fun t i =>
    ⟨⌊(L : ℝ) * Int.fract ((t : ℕ) * v i)⌋₊, by
      rw [Nat.floor_lt (by positivity [Int.fract_nonneg ((t : ℕ) * v i)])]
      exact mul_lt_of_lt_one_right hLr (Int.fract_lt_one _)⟩
  have hcard : Fintype.card (ι → Fin L) < Fintype.card (Fin (L ^ Fintype.card ι + 1)) := by
    simp
  obtain ⟨s, t, hst, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  have key : ∀ s t : Fin (L ^ Fintype.card ι + 1), (s : ℕ) < t → box s = box t →
      ∃ z : ℕ, 1 ≤ z ∧ z ≤ L ^ Fintype.card ι ∧ ∀ i, ‖(((z : ℝ) * v i : ℝ) : Circ)‖ ≤ 1 / L := by
    intro s t hlt hb
    refine ⟨(t : ℕ) - s, by omega, by have := t.2; omega, fun i => ?_⟩
    have hi := congrFun hb i
    have hfl : ⌊(L : ℝ) * Int.fract ((s : ℕ) * v i)⌋₊ = ⌊(L : ℝ) * Int.fract ((t : ℕ) * v i)⌋₊ :=
      congrArg Fin.val hi
    set a := Int.fract (((s : ℕ) : ℝ) * v i) with ha
    set b := Int.fract (((t : ℕ) : ℝ) * v i) with hb'
    have hLa : 0 ≤ (L : ℝ) * a := by positivity [Int.fract_nonneg (((s : ℕ) : ℝ) * v i)]
    have hLb : 0 ≤ (L : ℝ) * b := by positivity [Int.fract_nonneg (((t : ℕ) : ℝ) * v i)]
    have h1 := Nat.floor_le hLa
    have h2 := Nat.lt_floor_add_one ((L : ℝ) * a)
    have h3 := Nat.floor_le hLb
    have h4 := Nat.lt_floor_add_one ((L : ℝ) * b)
    rw [hfl] at h1 h2
    have hab : |b - a| ≤ 1 / L := by
      have : |(L : ℝ) * b - (L : ℝ) * a| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      rw [← mul_sub, abs_mul, abs_of_pos hLr] at this
      rw [le_div_iff₀ hLr]; linarith
    have heq : (((t : ℕ) - (s : ℕ) : ℕ) : ℝ) * v i =
        ((⌊((t : ℕ) : ℝ) * v i⌋ - ⌊((s : ℕ) : ℝ) * v i⌋ : ℤ) : ℝ) + (b - a) := by
      rw [Nat.cast_sub hlt.le]
      have e1 := Int.floor_add_fract (((t : ℕ) : ℝ) * v i)
      have e2 := Int.floor_add_fract (((s : ℕ) : ℝ) * v i)
      push_cast
      rw [← hb', ← ha] at *
      linarith
    rw [heq, AddCircle.coe_add, coe_int_circ_zero, zero_add]
    exact (norm_coe_le _ 0).trans (by simpa using hab)
  rcases lt_or_gt_of_ne (fun h => hst (Fin.ext h)) with h | h
  · exact key s t h hbox
  · exact key t s h hbox.symm

end Dirichlet

section Good

lemma norm_half_odd (w : ℕ) (hw : Odd w) : ‖((((w : ℝ) / 2 : ℝ)) : Circ)‖ = 1 / 2 := by
  obtain ⟨u, rfl⟩ := hw
  have : (((2 * u + 1 : ℕ) : ℝ) / 2 : ℝ) = ((u : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  rw [this, AddCircle.coe_add, coe_int_circ_zero, zero_add, norm_coe_circ]
  have : round ((1 : ℝ) / 2) = 1 := by
    rw [round_eq]; norm_num
  rw [this]; norm_num

/-- A large integer all of whose multiples of the first `k+1` terms `2^{-n²}`, `3^{-n²}` are near whole numbers, bounded by a
power of `L`. -/
lemma exists_big_good (L : ℕ) (hL : 2 < L) (M k : ℕ) :
    ∃ z : ℕ, M < z ∧ z ≤ L ^ ((k + 1) + ((k + 1) + M)) ∧
      (∀ n ≤ k, ‖((((z : ℝ) / 2 ^ (n ^ 2) : ℝ)) : Circ)‖ ≤ 1 / L) ∧
      (∀ n ≤ k, ‖((((z : ℝ) / 3 ^ (n ^ 2) : ℝ)) : Circ)‖ ≤ 1 / L) := by
  let v : Fin (k + 1) ⊕ (Fin (k + 1) ⊕ Fin M) → ℝ := fun i =>
    match i with
    | Sum.inl n => 1 / 2 ^ ((n : ℕ) ^ 2)
    | Sum.inr (Sum.inl n) => 1 / 3 ^ ((n : ℕ) ^ 2)
    | Sum.inr (Sum.inr j) => 1 / 2 ^ ((j : ℕ) + 1)
  obtain ⟨z, hz1, hzB, hz⟩ := dirichlet_multi L (by omega) v
  have hcard : Fintype.card (Fin (k + 1) ⊕ (Fin (k + 1) ⊕ Fin M)) = (k + 1) + ((k + 1) + M) := by simp
  rw [hcard] at hzB
  have hL2 : (2 : ℝ) < L := by exact_mod_cast hL
  refine ⟨z, ?_, hzB, fun n hn => ?_, fun n hn => ?_⟩
  · by_contra hle
    push_neg at hle
    obtain ⟨e, w, hw, hzw⟩ := Nat.exists_eq_two_pow_mul_odd (n := z) (by omega)
    have hw1 : 1 ≤ w := hw.pos
    have h2e : 2 ^ e ≤ z := by rw [hzw]; exact Nat.le_mul_of_pos_right _ hw1
    have hek : e < M := by
      have := Nat.lt_two_pow_self (n := e)
      omega
    have h := hz (Sum.inr (Sum.inr ⟨e, hek⟩))
    simp only [v] at h
    have e1 : ((z : ℝ) * (1 / 2 ^ (e + 1))) = (w : ℝ) / 2 := by
      rw [hzw]; push_cast; rw [pow_succ]; field_simp
    rw [e1, norm_half_odd w hw] at h
    have : (1 : ℝ) / L < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  · have h := hz (Sum.inl ⟨n, by omega⟩)
    simp only [v] at h
    rwa [mul_one_div] at h
  · have h := hz (Sum.inr (Sum.inl ⟨n, by omega⟩))
    simp only [v] at h
    rwa [mul_one_div] at h

lemma exp_ineq (L M N : ℕ) (hL : 1 ≤ L) :
    L * (2 * (2 * L + L * M + N) + M) + N ≤ (2 * L + L * M + N) ^ 2 := by
  have hK : 1 ≤ 2 * L + L * M + N := by omega
  nlinarith [Nat.mul_le_mul_right (L * M + N) hK]

lemma xiSet_of_good (p : ℕ) (hp : 2 ≤ p) (d z K : ℕ) (ε δ : ℝ) (hd : 0 < d) (hδ : δ < ε)
    (hnear : ∀ n < K, ‖(((z : ℝ) / (p : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ ≤ δ)
    (htail : (z : ℝ) / 2 ^ (K ^ 2) < ε) :
    (((d * z : ℕ) : ℚ)) ∈ xiSet (Cp p) d ε := by
  intro c hc
  obtain ⟨n, rfl⟩ := mem_Cp.1 hc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : ((((d * z : ℕ) : ℚ) / ((d : ℚ) * ((p ^ (n ^ 2) : ℕ) : ℚ)) : ℚ) : ℝ) = (z : ℝ) / (p : ℝ) ^ (n ^ 2) := by
    push_cast
    field_simp
  rw [e]
  by_cases hn : n < K
  · exact lt_of_le_of_lt (hnear n hn) hδ
  · push_neg at hn
    refine lt_of_le_of_lt ((norm_coe_le _ 0).trans ?_) htail
    rw [Int.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg z) (by positivity)
    calc (2 : ℝ) ^ (K ^ 2) ≤ (2 : ℝ) ^ (n ^ 2) :=
          pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left hn 2)
      _ ≤ (p : ℝ) ^ (n ^ 2) := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) _

/-- Given `ε`, `M`, `d`, there is an integer `z > M` such that `d z` lies in the basic joint neighbourhood
`P_{2,d} < ε`, `P_{3,d} < ε`. -/
lemma exists_large_in_joint (ε : ℝ) (hε : 0 < ε) (M d : ℕ) (hd : 0 < d) :
    ∃ z : ℕ, M < z ∧ PltQ (((d * z : ℕ)) : ℚ) d ε := by
  set N : ℕ := ⌈1 / ε⌉₊ with hN
  set L : ℕ := N + 3 with hL
  have hL2 : 2 < L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hNε : 1 / ε ≤ N := Nat.le_ceil _
  have hLε : 1 / (L : ℝ) < ε := by
    rw [div_lt_iff₀ hLpos]
    have : 1 / ε < L := by
      have : (N : ℝ) < L := by rw [hL]; push_cast; linarith
      linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  set K : ℕ := 2 * L + L * M + N with hK
  have hK1 : 1 ≤ K := by omega
  obtain ⟨z, hzM, hzB, hz2, hz3⟩ := exists_big_good L hL2 M (K - 1)
  have hKk : K - 1 + 1 = K := by omega
  rw [hKk] at hzB
  have hzB' : z ≤ L ^ (2 * K + M) := by
    have : K + (K + M) = 2 * K + M := by ring
    rwa [this] at hzB
  -- z / 2^(K^2) < ε
  have hz_le : (z : ℝ) ≤ 2 ^ (L * (2 * K + M)) := by
    have h1 : (z : ℝ) ≤ (L : ℝ) ^ (2 * K + M) := by exact_mod_cast hzB'
    have h2 : (L : ℝ) ≤ 2 ^ L := by exact_mod_cast (Nat.lt_two_pow_self (n := L)).le
    calc (z : ℝ) ≤ (L : ℝ) ^ (2 * K + M) := h1
      _ ≤ ((2 : ℝ) ^ L) ^ (2 * K + M) := pow_le_pow_left₀ hLpos.le h2 _
      _ = 2 ^ (L * (2 * K + M)) := by rw [← pow_mul]
  have h2N : (1 : ℝ) < ε * 2 ^ N := by
    have : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self (n := N)
    have h3 : 1 ≤ ε * N := by
      have := mul_le_mul_of_nonneg_left hNε hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    nlinarith
  have hexp : (2 : ℝ) ^ (L * (2 * K + M) + N) ≤ 2 ^ (K ^ 2) :=
    pow_le_pow_right₀ (by norm_num) (exp_ineq L M N (by omega))
  have htail : (z : ℝ) / 2 ^ (K ^ 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    calc (z : ℝ) ≤ 2 ^ (L * (2 * K + M)) := hz_le
      _ = 1 * 2 ^ (L * (2 * K + M)) := (one_mul _).symm
      _ < (ε * 2 ^ N) * 2 ^ (L * (2 * K + M)) := by
          apply mul_lt_mul_of_pos_right h2N (by positivity)
      _ = ε * 2 ^ (L * (2 * K + M) + N) := by rw [pow_add]; ring
      _ ≤ ε * 2 ^ (K ^ 2) := mul_le_mul_of_nonneg_left hexp hε.le
  refine ⟨z, hzM, ?_, ?_⟩
  · refine xiSet_of_good 2 le_rfl d z K ε (1 / L) hd hLε (fun n hn => ?_) htail
    have := hz2 n (by omega)
    simpa using this
  · refine xiSet_of_good 3 (by norm_num) d z K ε (1 / L) hd hLε (fun n hn => ?_) htail
    have := hz3 n (by omega)
    simpa using this

end Good

section Join

/-- Every zero-neighbourhood of `γ₂ ∨ γ₃` contains a basic set `P_{2,d} < ε, P_{3,d} < ε`. -/
lemma join_nhds_pltq (U : Set ℚ) (hU : U ∈ @nhds ℚ (xi (Cp 2) ⊓ xi (Cp 3)) 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, PltQ q d ε → q ∈ U := by
  rw [@nhds_inf ℚ (xi (Cp 2)) (xi (Cp 3)) 0] at hU
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hU
  obtain ⟨s₁, ⟨d₁, hd₁, ε₁, hε₁, rfl⟩, hs₁⟩ := ((xi_nhds_hasBasis (Cp 2)).mem_iff).mp hU₁
  obtain ⟨s₂, ⟨d₂, hd₂, ε₂, hε₂, rfl⟩, hs₂⟩ := ((xi_nhds_hasBasis (Cp 3)).mem_iff).mp hU₂
  refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, min (ε₁ / d₂) (ε₂ / d₁), lt_min (by positivity) (by positivity),
    fun q hq => ?_⟩
  have hq1 : q ∈ xiSet (Cp 2) d₁ ε₁ := by
    have := xiSet_mono (Cp 2) d₁ d₂ hd₂ ε₁
    exact this (fun c hc => lt_of_lt_of_le (hq.1 c hc) (min_le_left _ _))
  have hq2 : q ∈ xiSet (Cp 3) d₂ ε₂ := by
    have := xiSet_mono (Cp 3) d₂ d₁ hd₁ ε₂
    rw [mul_comm d₂ d₁] at this
    exact this (fun c hc => lt_of_lt_of_le (hq.2 c hc) (min_le_right _ _))
  exact hsub ⟨hs₁ hq1, hs₂ hq2⟩

/-- **Proposition 22.3, first assertion.**  Every zero-neighbourhood of the join contains arbitrarily large positive integers. -/
theorem join_contains_large_integers (U : Set ℚ) (hU : U ∈ @nhds ℚ (xi (Cp 2) ⊓ xi (Cp 3)) 0) (M : ℕ) :
    ∃ z : ℕ, M < z ∧ (z : ℚ) ∈ U := by
  obtain ⟨d, hd, ε, hε, hsub⟩ := join_nhds_pltq U hU
  obtain ⟨z, hzM, hz⟩ := exists_large_in_joint ε hε M d hd
  -- the point `d z` is in `U`, and `d z > M`
  refine ⟨d * z, lt_of_lt_of_le hzM (Nat.le_mul_of_pos_left z hd), hsub _ hz⟩

/-- **Proposition 22.3.**  The join `γ₂ ∨ γ₃` is coarser than the usual topology of `ℚ` and not equal to it, and its restriction to
`ℤ` is nondiscrete. -/
theorem join_weaker_than_usual :
    (inferInstance : TopologicalSpace ℚ) < xi (Cp 2) ⊓ xi (Cp 3) ∧
      ({(0 : ℤ)} : Set ℤ) ∉ @nhds ℤ (TopologicalSpace.induced (fun z : ℤ => (z : ℚ)) (xi (Cp 2) ⊓ xi (Cp 3))) 0 := by
  refine ⟨lt_of_le_of_ne (le_inf (usual_le_xi _) (usual_le_xi _)) (fun heq => ?_), fun hnd => ?_⟩
  · have hb0 : Metric.ball (0 : ℚ) 1 ∈ nhds (0 : ℚ) := Metric.ball_mem_nhds _ one_pos
    have hball : Metric.ball (0 : ℚ) 1 ∈ @nhds ℚ (xi (Cp 2) ⊓ xi (Cp 3)) 0 := by
      rw [← heq]; exact hb0
    obtain ⟨z, hz, hmem⟩ := join_contains_large_integers _ hball 1
    rw [Metric.mem_ball, Rat.dist_eq] at hmem
    simp at hmem
    have : (1 : ℝ) < z := by exact_mod_cast hz
    linarith
  · rw [@nhds_induced ℚ ℤ (xi (Cp 2) ⊓ xi (Cp 3)) (fun z : ℤ => (z : ℚ)) 0] at hnd
    obtain ⟨V, hV, hVsub⟩ := Filter.mem_comap.1 hnd
    obtain ⟨z, hz, hzV⟩ := join_contains_large_integers V (by simpa using hV) 0
    have := hVsub (show ((z : ℤ)) ∈ (fun z : ℤ => (z : ℚ)) ⁻¹' V by simpa using hzV)
    simp at this
    omega

end Join

end LeanCheck
