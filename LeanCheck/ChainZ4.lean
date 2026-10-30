import LeanCheck.ChainZ3

/-!
# Theorem G, compatible direction: assembly
(TVGQ-v7 Theorem 17.6 `chains:G`; HamelCharactersTVG_v18 Theorem D.6)

Let `M` be a profinitely null chain with `H(M)`.  Every `λ_{range M}`-continuous character `ζ` of `ℚ/ℤ` is
`x ↦ u • x` for an integer `u`.
-/

namespace LeanCheck

open Filter Topology

section ZetaPos3

variable {M : ℕ → ℕ}

/-- A character of `ℚ/ℤ` that is `u •` on every `e_j = 1/M_j` is `u •`. -/
lemma char_of_eT (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (ζ : TorsA →+ Circ)
    (n : ℤ) (h : ∀ j, ζ (eT M j) = n • ((eT M j : TorsA) : Circ)) (x : TorsA) : ζ x = n • (x : Circ) := by
  obtain ⟨q, rfl⟩ := piHom_surjective x
  obtain ⟨n0, hn0⟩ := hnull q.den q.den_pos
  obtain ⟨w, hw⟩ := hn0 n0 le_rfl
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
    exact (hM.pos n0).ne' hw
  have hq : piHom q = (q.num * w : ℤ) • eT M n0 := by
    rw [eT, ← map_zsmul, zsmul_eq_mul]
    congr 1
    have hMn : (M n0 : ℚ) = q.den * w := by exact_mod_cast hw
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    have hw0' : (w : ℚ) ≠ 0 := by exact_mod_cast hw0
    have hqd : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    rw [hMn]
    push_cast
    rw [hqd]
    field_simp
  rw [hq, map_zsmul, h n0, AddSubgroup.coe_zsmul, smul_comm]

/-- Consistency of residues: `c r_k - r_i ∈ ℤ` when `M_k = c M_i`. -/
lemma rel_r (hM : ChainSeq M) (ζ : TorsA →+ Circ) (r : ℕ → ℝ)
    (hr1 : ∀ i, (r i : Circ) = ζ (eT M i)) {i k : ℕ} (h : i ≤ k) :
    ∃ c : ℕ, M k = c * M i ∧ ∃ b : ℤ, (c : ℝ) * r k - r i = b := by
  obtain ⟨c, hc, hrel⟩ := eT_rel hM h
  refine ⟨c, hc, ?_⟩
  have h0 : (((c : ℝ) * r k - r i : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_sub, ← nsmul_coe_circ, hr1 i, hr1 k, hrel, map_nsmul, sub_self]
  obtain ⟨b, hb⟩ := (circ_zero_iff _).1 h0
  exact ⟨b, hb⟩

lemma M_eT_zero (hM : ChainSeq M) (i : ℕ) : M i • eT M i = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, eT_coe, nsmul_coe_circ]
  have : (M i : ℝ) * (1 / (M i : ℝ)) = 1 := by
    have : (M i : ℝ) ≠ 0 := by exact_mod_cast (hM.pos i).ne'
    field_simp
  rw [this]
  show _ = (0 : Circ)
  rw [circ_zero_iff]
  exact ⟨1, by simp⟩

/-- **Theorem G, compatible direction.** -/
theorem tors_pos (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (hH : HSeq M)
    (ζ : TorsA →+ Circ) (hζ : @Continuous TorsA Circ (basisOf (Set.range M)).topology _ ζ) :
    ∃ u : ℤ, ∀ x : TorsA, ζ x = u • (x : Circ) := by
  classical
  obtain ⟨δ, hδ, hq⟩ := quarter_of_continuous (Set.range M) ζ hζ
  set ε : ℝ := min δ (1 / 16) with hεdef
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hε8 : ε < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsmall : ∀ x : TorsA, (∀ l, ‖M l • (x : Circ)‖ < ε) → ‖ζ x‖ < 1 / 4 := fun x hx =>
    hq x (by rintro _ ⟨l, rfl⟩; exact lt_of_lt_of_le (hx l) (min_le_left _ _))
  set B : ℝ := 64 / ε with hBdef
  have hB2 : 2 < B := by rw [hBdef, lt_div_iff₀ hε]; linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨L, hL⟩ := exists_big_in_window hM hH hB2
  have hex : ∀ i, ∃ k, i < k ∧ Big M B k := big_infinite_succ hM hH hB2
  choose r hr1 hr2 hr3 using fun i => exists_centered (ζ (eT M i))
  let nxt : ℕ → ℕ := fun i => Nat.find (hex i)
  have hnxt1 : ∀ i, i < nxt i ∧ Big M B (nxt i) := fun i => Nat.find_spec (hex i)
  have hnxtmin : ∀ i j, i < j → j < nxt i → ¬ Big M B j := fun i j hij hj hbig =>
    Nat.find_min (hex i) hj ⟨hij, hbig⟩
  have hnxtle : ∀ i, nxt i ≤ i + 1 + L := fun i => by
    obtain ⟨k, hk1, hk2, hk3⟩ := hL (i + 1)
    exact (Nat.find_min' (hex i) ⟨by omega, hk3⟩).trans hk2
  have hMpos : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM.pos i
  let P : ℕ → ℕ := fun i => M (nxt i + 1) / M (i + 1)
  have hPeq : ∀ i, M (nxt i + 1) = P i * M (i + 1) := fun i =>
    (Nat.div_mul_cancel (hM.dvd_of_le (by have := (hnxt1 i).1; omega))).symm
  have hrel : ∀ i, ∃ b : ℤ, (P i : ℝ) * r (nxt i + 1) - r (i + 1) = b := fun i => by
    obtain ⟨c, hc, b, hb⟩ := rel_r hM ζ r hr1
      (show i + 1 ≤ nxt i + 1 by have := (hnxt1 i).1; omega)
    have hcP : c = P i := by
      have h1 := hPeq i
      have hpos := hM.pos (i + 1)
      rw [hc] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    exact ⟨b, by rw [← hcP]; exact hb⟩
  have hAr : ∀ i, Big M B i → |r (i + 1)| ≤ 1 / (ε * ((M (i + 1) : ℝ) / M i)) := fun i hbig => by
    rw [← hr3 (i + 1)]; exact r_bound_G hM hε ζ hsmall hbig
  have halpha : ∀ i, Big M B i → B ≤ (M (i + 1) : ℝ) / M i := fun i hbig => by
    rw [le_div_iff₀ (hMpos i)]; exact hbig
  have hr64 : ∀ i, Big M B i → |r (i + 1)| ≤ 1 / 64 := fun i hbig => by
    refine (hAr i hbig).trans ?_
    have h1 : (64 : ℝ) ≤ ε * ((M (i + 1) : ℝ) / M i) := by
      have := mul_le_mul_of_nonneg_left (halpha i hbig) hε.le
      rwa [hBdef, mul_div_cancel₀ _ hε.ne'] at this
    exact one_div_le_one_div_of_le (by norm_num) h1
  by_cases hst : ∃ N, ∀ i ≥ N, Big M B i → (P i : ℝ) * r (nxt i + 1) = r (i + 1)
  · -- stable case: the signed integers `M_{i+1} r_{i+1}` are constant along the big indices
    obtain ⟨N, hN⟩ := hst
    obtain ⟨i0, hi0lt, hi0⟩ := hex N
    have hg0 : ∀ m, i0 + m ≤ nxt^[m] i0 ∧ Big M B (nxt^[m] i0) := by
      intro m
      induction m with
      | zero => simpa using hi0
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨by have := (hnxt1 (nxt^[m] i0)).1; omega, (hnxt1 _).2⟩
    have hconst : ∀ m, (M (nxt^[m] i0 + 1) : ℝ) * r (nxt^[m] i0 + 1) = (M (i0 + 1) : ℝ) * r (i0 + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        have h1 := hN (nxt^[m] i0) (by have := (hg0 m).1; omega) (hg0 m).2
        have h2 : (M (nxt (nxt^[m] i0) + 1) : ℝ) = P (nxt^[m] i0) * M (nxt^[m] i0 + 1) := by
          exact_mod_cast hPeq (nxt^[m] i0)
        rw [h2, ← ih, ← h1]; ring
    -- integrality of `M_{i0+1} r_{i0+1}`
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (M (i0 + 1) : ℝ) * r (i0 + 1) = n := by
      have h0 : (((M (i0 + 1) : ℝ) * r (i0 + 1) : ℝ) : Circ) = 0 := by
        rw [← nsmul_coe_circ, hr1, ← map_nsmul, M_eT_zero hM, map_zero]
      exact (circ_zero_iff _).1 h0
    have hall : ∀ j, ζ (eT M j) = n • ((eT M j : TorsA) : Circ) := by
      intro j
      set m := nxt^[j] i0 with hm
      have hjm : j ≤ m := by have := (hg0 j).1; omega
      obtain ⟨c, hc, b, hb⟩ := rel_r hM ζ r hr1 (show j ≤ m + 1 by omega)
      have hMj := hMpos j
      have hMm := hMpos (m + 1)
      have hMc : (M (m + 1) : ℝ) = c * M j := by exact_mod_cast hc
      have hc0 : (c : ℝ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hMc
        exact hMm.ne' hMc
      have hrm : r (m + 1) = n / M (m + 1) := by
        have := hconst j
        rw [← hm, hn] at this
        field_simp
        linarith
      have hrj : r j - n * (1 / (M j : ℝ)) = ((-b : ℤ) : ℝ) := by
        have : (c : ℝ) * (n / M (m + 1)) = n * (1 / M j) := by
          rw [hMc]; field_simp
        rw [hrm] at hb
        push_cast
        linarith
      have h0 : ((r j - n * (1 / (M j : ℝ)) : ℝ) : Circ) = 0 := (circ_zero_iff _).2 ⟨-b, hrj⟩
      rw [AddCircle.coe_sub, sub_eq_zero] at h0
      rw [← hr1 j, h0, eT_coe, zsmul_coe_circ]
    exact ⟨n, char_of_eT hM hnull ζ n hall⟩
  · -- unstable case: contradiction with continuity
    exfalso
    push_neg at hst
    set I : Set ℕ := {k | ∃ i, Big M B i ∧ nxt i = k ∧ (P i : ℝ) * r (nxt i + 1) ≠ r (i + 1)} with hIdef
    have hI : I.Infinite := Set.infinite_of_forall_exists_gt (fun N => by
      obtain ⟨i, hi, hb, hne⟩ := hst N
      exact ⟨nxt i, ⟨i, hb, rfl, hne⟩, by have := (hnxt1 i).1; omega⟩)
    have hIbig : ∀ k ∈ I, Big M B k := by
      rintro k ⟨i, -, rfl, -⟩
      exact (hnxt1 i).2
    set η : ℝ := ε / 16 with hη
    let s : ℕ → ℕ := fun k => ⌊η * ((M (k + 1) : ℝ) / M k)⌋₊
    set c0 : ℝ := (63 / 64) / B ^ L with hc0
    set c1 : ℝ := η / 2 * c0 with hc1
    have hc0pos : 0 < c0 := by positivity
    have hc1pos : 0 < c1 := by positivity
    have hmain : ∀ k ∈ I, c0 ≤ ((M (k + 1) : ℝ) / M k) * |r (k + 1)| := by
      rintro k ⟨i, hbigi, rfl, hne⟩
      obtain ⟨b, hb⟩ := hrel i
      have hb0 : b ≠ 0 := by
        rintro rfl
        apply hne
        have : (P i : ℝ) * r (nxt i + 1) = r (i + 1) := by simpa [sub_eq_zero] using hb
        exact this
      have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
        have : 1 ≤ |b| := Int.one_le_abs hb0
        exact_mod_cast this
      have hri : |r (i + 1)| ≤ 1 / 64 := hr64 i hbigi
      have hPr : (63 / 64 : ℝ) ≤ P i * |r (nxt i + 1)| := by
        have h1 : |(b : ℝ)| - |r (i + 1)| ≤ |(P i : ℝ) * r (nxt i + 1)| := by
          have e : (P i : ℝ) * r (nxt i + 1) = b + r (i + 1) := by linarith
          rw [e]
          calc |(b : ℝ)| - |r (i + 1)| = |(b : ℝ)| - |-(r (i + 1))| := by rw [abs_neg]
            _ ≤ |(b : ℝ) - -(r (i + 1))| := abs_sub_abs_le_abs_sub _ _
            _ = |(b : ℝ) + r (i + 1)| := by rw [sub_neg_eq_add]
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (P i) : (0 : ℝ) ≤ (P i : ℝ))] at h1
        linarith
      have hPle : (P i : ℝ) ≤ B ^ L * ((M (nxt i + 1) : ℝ) / M (nxt i)) := by
        have hrat := ratio_le_pow hBpos (i + 1) (nxt i) (hnxt1 i).1
          (fun j hj1 hj2 => by
            have := hnxtmin i j (by omega) hj2
            unfold Big at this
            exact not_le.1 this)
        have hexp : B ^ (nxt i - (i + 1)) ≤ B ^ L :=
          pow_le_pow_right₀ (by linarith) (by have := hnxtle i; omega)
        have hPM : (M (nxt i + 1) : ℝ) = P i * M (i + 1) := by exact_mod_cast hPeq i
        have : (P i : ℝ) * M (nxt i) ≤ B ^ L * M (nxt i + 1) := by
          calc (P i : ℝ) * M (nxt i) ≤ P i * (B ^ (nxt i - (i + 1)) * M (i + 1)) := by gcongr
            _ ≤ P i * (B ^ L * M (i + 1)) := by gcongr
            _ = B ^ L * (P i * M (i + 1)) := by ring
            _ = B ^ L * M (nxt i + 1) := by rw [hPM]
        rw [mul_div_assoc', le_div_iff₀ (hMpos _)]
        linarith
      have hα0 : 0 ≤ ((M (nxt i + 1) : ℝ) / M (nxt i)) := by positivity
      rw [hc0, div_le_iff₀ (by positivity)]
      have h1 : (63 / 64 : ℝ) ≤ B ^ L * ((M (nxt i + 1) : ℝ) / M (nxt i)) * |r (nxt i + 1)| := by
        calc (63 / 64 : ℝ) ≤ P i * |r (nxt i + 1)| := hPr
          _ ≤ B ^ L * ((M (nxt i + 1) : ℝ) / M (nxt i)) * |r (nxt i + 1)| := by gcongr
      calc (63 / 64 : ℝ) ≤ B ^ L * ((M (nxt i + 1) : ℝ) / M (nxt i)) * |r (nxt i + 1)| := h1
        _ = ((M (nxt i + 1) : ℝ) / M (nxt i)) * |r (nxt i + 1)| * B ^ L := by ring
    have hηα : ∀ i, Big M B i → 4 ≤ η * ((M (i + 1) : ℝ) / M i) := fun i hbig => by
      have h1 := halpha i hbig
      have : 4 ≤ η * B := by rw [hη, hBdef]; field_simp; norm_num
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ η)]
    have hs_up : ∀ i, (s i : ℝ) ≤ η * ((M (i + 1) : ℝ) / M i) := fun i =>
      Nat.floor_le (by positivity)
    have hs_low : ∀ i, Big M B i → η * ((M (i + 1) : ℝ) / M i) / 2 ≤ s i := fun i hbig => by
      have h4 := hηα i hbig
      have h1 : η * ((M (i + 1) : ℝ) / M i) < s i + 1 := Nat.lt_floor_add_one _
      have h2 : (1 : ℝ) ≤ s i := by
        have : (1 : ℝ) ≤ η * ((M (i + 1) : ℝ) / M i) := by linarith
        exact_mod_cast Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ _ by simpa using this)
      linarith
    refine case_unstable_G hM hε ζ hsmall (fun k => r (k + 1)) (fun k => hr1 (k + 1)) I hI s ?_ c1 hc1pos ?_
    · intro i hi
      have h1 := hs_up i
      have h2 : (M (i + 1) : ℝ) = ((M (i + 1) : ℝ) / M i) * M i := (div_mul_cancel₀ _ (hMpos i).ne').symm
      calc (s i : ℝ) * M i ≤ η * ((M (i + 1) : ℝ) / M i) * M i := by gcongr
        _ = η * M (i + 1) := by rw [mul_assoc, ← h2]
    · intro i hi
      have hbig := hIbig i hi
      have hα0 : 0 ≤ ((M (i + 1) : ℝ) / M i) := by positivity
      constructor
      · calc c1 = η / 2 * c0 := hc1
          _ ≤ η / 2 * (((M (i + 1) : ℝ) / M i) * |r (i + 1)|) := by gcongr; exact hmain i hi
          _ = (η * ((M (i + 1) : ℝ) / M i) / 2) * |r (i + 1)| := by ring
          _ ≤ s i * |r (i + 1)| := by gcongr; exact hs_low i hbig
      · have hrA := hAr i hbig
        have hαpos : 0 < ((M (i + 1) : ℝ) / M i) := lt_of_lt_of_le hBpos (halpha i hbig)
        calc (s i : ℝ) * |r (i + 1)| ≤ (η * ((M (i + 1) : ℝ) / M i)) * |r (i + 1)| := by
              gcongr; exact hs_up i
          _ ≤ (η * ((M (i + 1) : ℝ) / M i)) * (1 / (ε * ((M (i + 1) : ℝ) / M i))) := by gcongr
          _ = η / ε := by
              have h1 := (hMpos (i + 1)).ne'
              have h2 := (hMpos i).ne'
              have h3 := hε.ne'
              field_simp
          _ = 1 / 16 := by rw [hη]; field_simp
          _ ≤ 1 / 8 := by norm_num

end ZetaPos3

end LeanCheck
