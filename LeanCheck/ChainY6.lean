import LeanCheck.ChainY5

/-!
# Theorem F, compatible direction: assembly of the key proposition
-/

namespace LeanCheck

open Filter Topology

section Assembly

variable {M : ℕ → ℕ}

/-- **Case 1 (stable).**  If along the big indices `r_{nxt i} = P_i r_i` with `P_i ≥ 2`, and `|r_i| ≤ 1/64`, then
`r_{i₀} = 0` for every big `i₀`. -/
lemma case_stable (B : ℝ) (r : ℕ → ℝ) (hrb : ∀ i, Big M B i → |r i| ≤ 1 / 64)
    (nxt : ℕ → ℕ) (hnxt : ∀ i, Big M B i → Big M B (nxt i))
    (P : ℕ → ℝ) (hP : ∀ i, Big M B i → 2 ≤ P i)
    (hlt : ∀ i, i < nxt i)
    (i0 : ℕ) (hrel : ∀ i, i0 ≤ i → Big M B i → r (nxt i) = P i * r i)
    (hi0 : Big M B i0) : r i0 = 0 := by
  have hg0 : ∀ m, i0 ≤ nxt^[m] i0 ∧ Big M B (nxt^[m] i0) := by
    intro m
    induction m with
    | zero => simpa using hi0
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (hlt _).le, hnxt _ ih.2⟩
  have hg : ∀ m, Big M B (nxt^[m] i0) := fun m => (hg0 m).2
  have hge : ∀ m, 2 ^ m * |r i0| ≤ |r (nxt^[m] i0)| := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', hrel _ (hg0 m).1 (hg m), abs_mul,
        abs_of_nonneg (by linarith [hP _ (hg m)] : (0 : ℝ) ≤ P (nxt^[m] i0))]
      calc 2 ^ (m + 1) * |r i0| = 2 * (2 ^ m * |r i0|) := by ring
        _ ≤ 2 * |r (nxt^[m] i0)| := by gcongr
        _ ≤ P (nxt^[m] i0) * |r (nxt^[m] i0)| := by
          nlinarith [hP _ (hg m), abs_nonneg (r (nxt^[m] i0))]
  by_contra hne
  have hpos : 0 < |r i0| := abs_pos.2 hne
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (64 * |r i0|)) (by norm_num : (1 : ℝ) < 2)
  have h1 := (hge m).trans (hrb _ (hg m))
  rw [div_lt_iff₀ (by positivity)] at hm
  nlinarith

/-- Ratios along a block of non-big steps. -/
lemma ratio_le_pow {B : ℝ} (hB : 0 < B) (x : ℕ) : ∀ y : ℕ, x ≤ y →
    (∀ j, x ≤ j → j < y → (M (j + 1) : ℝ) < B * M j) → (M y : ℝ) ≤ B ^ (y - x) * M x := by
  intro y hxy
  induction y, hxy using Nat.le_induction with
  | base => intro _; simp
  | succ y hxy ih =>
    intro h
    have h1 := ih (fun j hj1 hj2 => h j hj1 (by omega))
    have h2 := h y hxy (by omega)
    calc (M (y + 1) : ℝ) ≤ B * M y := h2.le
      _ ≤ B * (B ^ (y - x) * M x) := by gcongr
      _ = B ^ (y + 1 - x) * M x := by
        rw [show y + 1 - x = (y - x) + 1 by omega]; ring

/-- **Key proposition (Theorem F, compatible direction).**  Let `M` be a chain with `H(M)`, `0 < ε < 1/8`, and
`c' ∈ ℝ` with the property: for every integer `n` with `‖p(n/M_i)‖ < ε` for all `i`, `‖p(c' n)‖ < 1/4`.
Then `p(c' M_i) = 0` for some `i`. -/
theorem key_prop (hM : ChainSeq M) (hH : HSeq M) {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) {c' : ℝ}
    (hstar : ∀ n : ℤ, (∀ i, ‖(((n : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < ε) → ‖((c' * n : ℝ) : Circ)‖ < 1 / 4) :
    ∃ i, ((c' * M i : ℝ) : Circ) = 0 := by
  classical
  set B : ℝ := 64 / ε with hBdef
  have hB2 : 2 < B := by rw [hBdef, lt_div_iff₀ hε]; linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨L, hL⟩ := exists_big_in_window hM hH hB2
  have hex : ∀ i, ∃ k, i < k ∧ Big M B k := big_infinite_succ hM hH hB2
  choose r hr1 hr2 hr3 using fun i => exists_centered ((c' * M i : ℝ) : Circ)
  let nxt : ℕ → ℕ := fun i => Nat.find (hex i)
  have hnxt1 : ∀ i, i < nxt i ∧ Big M B (nxt i) := fun i => Nat.find_spec (hex i)
  have hnxtmin : ∀ i j, i < j → j < nxt i → ¬ Big M B j := fun i j hij hj hbig =>
    Nat.find_min (hex i) hj ⟨hij, hbig⟩
  have hnxtle : ∀ i, nxt i ≤ i + 1 + L := fun i => by
    obtain ⟨k, hk1, hk2, hk3⟩ := hL (i + 1)
    exact (Nat.find_min' (hex i) ⟨by omega, hk3⟩).trans hk2
  have hMpos : ∀ i, (0 : ℝ) < M i := fun i => by exact_mod_cast hM.pos i
  let P : ℕ → ℕ := fun i => M (nxt i) / M i
  have hPeq : ∀ i, M (nxt i) = P i * M i := fun i =>
    (Nat.div_mul_cancel (hM.dvd_of_le (hnxt1 i).1.le)).symm
  have hP2 : ∀ i, 2 ≤ P i := fun i => by
    have h1 : M (i + 1) ≤ M (nxt i) := hM.mono (hnxt1 i).1
    have h2 := hM.two i
    have h3 := hM.pos i
    by_contra hlt
    push_neg at hlt
    have : P i * M i < 2 * M i := Nat.mul_lt_mul_of_pos_right hlt h3
    have h4 := hPeq i
    omega
  have hrel : ∀ i, ∃ n : ℤ, (P i : ℝ) * r i - r (nxt i) = n := fun i => by
    have h0 : (((P i : ℝ) * r i - r (nxt i) : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_sub, ← nsmul_coe_circ, hr1 i, hr1 (nxt i), nsmul_coe_circ, sub_eq_zero]
      congr 1
      have : (M (nxt i) : ℝ) = P i * M i := by exact_mod_cast hPeq i
      rw [this]; ring
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
    exact ⟨n, by simpa using hn.symm⟩
  have hAr : ∀ i, Big M B i → |r i| ≤ 1 / (ε * ((M (i + 1) : ℝ) / M i)) := fun i hbig => by
    rw [← hr3 i]; exact r_bound hM hε hstar hbig
  have halpha : ∀ i, Big M B i → B ≤ (M (i + 1) : ℝ) / M i := fun i hbig => by
    rw [le_div_iff₀ (hMpos i)]; exact hbig
  have hr64 : ∀ i, Big M B i → |r i| ≤ 1 / 64 := fun i hbig => by
    refine (hAr i hbig).trans ?_
    have h1 : (64 : ℝ) ≤ ε * ((M (i + 1) : ℝ) / M i) := by
      have := mul_le_mul_of_nonneg_left (halpha i hbig) hε.le
      rwa [hBdef, mul_div_cancel₀ _ hε.ne'] at this
    exact one_div_le_one_div_of_le (by norm_num) h1
  by_cases hst : ∃ N, ∀ i ≥ N, Big M B i → (P i : ℝ) * r i = r (nxt i)
  · obtain ⟨N, hN⟩ := hst
    obtain ⟨i0, hi0lt, hi0⟩ := hex N
    have := case_stable B r hr64 nxt (fun i _ => (hnxt1 i).2) (fun i => (P i : ℝ))
      (fun i _ => by exact_mod_cast hP2 i) (fun i => (hnxt1 i).1) i0
      (fun i hi hbig => (hN i (by omega) hbig).symm) hi0
    refine ⟨i0, ?_⟩
    rw [← hr1 i0, this]; simp
  · exfalso
    push_neg at hst
    set I : Set ℕ := {i | Big M B i ∧ (P i : ℝ) * r i ≠ r (nxt i)} with hIdef
    have hI : I.Infinite := Set.infinite_of_forall_exists_gt (fun N => by
      obtain ⟨i, hi, hb, hne⟩ := hst (N + 1)
      exact ⟨i, ⟨hb, hne⟩, by omega⟩)
    set η : ℝ := ε / 16 with hη
    let s : ℕ → ℕ := fun i => ⌊η * ((M (i + 1) : ℝ) / M i)⌋₊
    set c0 : ℝ := (63 / 64) / B ^ L with hc0
    set c1 : ℝ := η / 2 * c0 with hc1
    have hc0pos : 0 < c0 := by positivity
    have hc1pos : 0 < c1 := by positivity
    have hmain : ∀ i ∈ I, c0 ≤ ((M (i + 1) : ℝ) / M i) * |r i| := by
      intro i hi
      obtain ⟨hbig, hne⟩ := hi
      obtain ⟨b, hb⟩ := hrel i
      have hb0 : b ≠ 0 := by
        rintro rfl
        apply hne
        have : (P i : ℝ) * r i = r (nxt i) := by simpa [sub_eq_zero] using hb
        exact this
      have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
        have : 1 ≤ |b| := Int.one_le_abs hb0
        exact_mod_cast this
      have hrn : |r (nxt i)| ≤ 1 / 64 := hr64 _ (hnxt1 i).2
      have hPr : (63 / 64 : ℝ) ≤ P i * |r i| := by
        have h1 : |(b : ℝ)| - |r (nxt i)| ≤ |(P i : ℝ) * r i| := by
          have e : (P i : ℝ) * r i = b + r (nxt i) := by linarith
          rw [e]
          calc |(b : ℝ)| - |r (nxt i)| = |(b : ℝ)| - |-(r (nxt i))| := by rw [abs_neg]
            _ ≤ |(b : ℝ) - -(r (nxt i))| := abs_sub_abs_le_abs_sub _ _
            _ = |(b : ℝ) + r (nxt i)| := by rw [sub_neg_eq_add]
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (P i) : (0 : ℝ) ≤ (P i : ℝ))] at h1
        linarith
      have hPle : (P i : ℝ) ≤ B ^ L * ((M (i + 1) : ℝ) / M i) := by
        have hrat := ratio_le_pow hBpos (i + 1) (nxt i) (hnxt1 i).1
          (fun j hj1 hj2 => by
            have := hnxtmin i j (by omega) hj2
            unfold Big at this
            exact not_le.1 this)
        have hexp : B ^ (nxt i - (i + 1)) ≤ B ^ L :=
          pow_le_pow_right₀ (by linarith) (by have := hnxtle i; omega)
        have hPM : (M (nxt i) : ℝ) = P i * M i := by exact_mod_cast hPeq i
        have : (P i : ℝ) * M i ≤ B ^ L * M (i + 1) := by
          rw [← hPM]
          calc (M (nxt i) : ℝ) ≤ B ^ (nxt i - (i + 1)) * M (i + 1) := hrat
            _ ≤ B ^ L * M (i + 1) := by gcongr
        rw [mul_div_assoc', le_div_iff₀ (hMpos i)]
        linarith
      have hα0 : 0 ≤ ((M (i + 1) : ℝ) / M i) := by positivity
      rw [hc0, div_le_iff₀ (by positivity)]
      have h1 : (63 / 64 : ℝ) ≤ B ^ L * ((M (i + 1) : ℝ) / M i) * |r i| := by
        calc (63 / 64 : ℝ) ≤ P i * |r i| := hPr
          _ ≤ B ^ L * ((M (i + 1) : ℝ) / M i) * |r i| := by gcongr
      calc (63 / 64 : ℝ) ≤ B ^ L * ((M (i + 1) : ℝ) / M i) * |r i| := h1
        _ = ((M (i + 1) : ℝ) / M i) * |r i| * B ^ L := by ring
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
    refine case_unstable hM hε hε8 hstar r hr1 I hI s ?_ c1 hc1pos ?_
    · intro i hi
      obtain ⟨hbig, _⟩ := hi
      have h1 := hs_up i
      have h2 : (M (i + 1) : ℝ) = ((M (i + 1) : ℝ) / M i) * M i := (div_mul_cancel₀ _ (hMpos i).ne').symm
      calc (s i : ℝ) * M i ≤ η * ((M (i + 1) : ℝ) / M i) * M i := by gcongr
        _ = η * M (i + 1) := by rw [mul_assoc, ← h2]
    · intro i hi
      have hbig := hi.1
      have hα0 : 0 ≤ ((M (i + 1) : ℝ) / M i) := by positivity
      constructor
      · calc c1 = η / 2 * c0 := hc1
          _ ≤ η / 2 * (((M (i + 1) : ℝ) / M i) * |r i|) := by gcongr; exact hmain i hi
          _ = (η * ((M (i + 1) : ℝ) / M i) / 2) * |r i| := by ring
          _ ≤ s i * |r i| := by gcongr; exact hs_low i hbig
      · have hrA := hAr i hbig
        have hαpos : 0 < ((M (i + 1) : ℝ) / M i) := lt_of_lt_of_le hBpos (halpha i hbig)
        calc (s i : ℝ) * |r i| ≤ (η * ((M (i + 1) : ℝ) / M i)) * |r i| := by gcongr; exact hs_up i
          _ ≤ (η * ((M (i + 1) : ℝ) / M i)) * (1 / (ε * ((M (i + 1) : ℝ) / M i))) := by gcongr
          _ = η / ε := by
              have h1 := (hMpos (i + 1)).ne'
              have h2 := (hMpos i).ne'
              have h3 := hε.ne'
              field_simp
          _ = 1 / 16 := by rw [hη]; field_simp
          _ ≤ 1 / 8 := by norm_num

end Assembly

end LeanCheck
