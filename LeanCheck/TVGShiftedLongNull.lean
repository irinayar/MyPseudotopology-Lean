import LeanCheck.TVGPlusCount
namespace LeanCheck.ShiftedHeight
open LeanCheck.MixedPrime LeanCheck.TVGPlus
theorem pigeonhole_box_multiple (C : Finset (ℕ × ℕ)) (hq : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2)) (m X R : ℕ)
    (hm : 1 ≤ m) (hR : 1 ≤ R) (hX : m ^ C.card * R ≤ X) :
    ∃ k : ℤ, (R : Int) ≤ k ∧ k ≤ X ∧
      ∀ c ∈ C, nrm ((k : ℝ) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set q : ℕ × ℕ → ℝ := fun c => ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) with hqdef
  have hqpos : ∀ c ∈ C, 0 < q c := fun c hc => by
    simp only [hqdef]; exact_mod_cast hq c hc
  have hlt : ∀ (c : ℕ × ℕ) (x : ℕ), c ∈ C →
      ⌊(m : ℝ) * Int.fract ((x : ℝ) / q c)⌋₊ < m := by
    intro c x hc
    rw [Nat.floor_lt (by have := Int.fract_nonneg ((x : ℝ) / q c); positivity)]
    have := Int.fract_lt_one ((x : ℝ) / q c)
    nlinarith
  let F : Fin (X + 1) → (C → Fin m) × Fin R := fun x =>
    ((fun c => ⟨⌊(m : ℝ) * Int.fract (((x : ℕ) : ℝ) / q c.1)⌋₊, hlt c.1 x c.2⟩),
     ⟨(x : Nat) % R, Nat.mod_lt _ (by omega)⟩)
  have hcard : Fintype.card ((C → Fin m) × Fin R) < Fintype.card (Fin (X + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
    omega
  obtain ⟨x, y, hxy, hF⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  -- the core step, for `x < y`
  have core : ∀ x y : Fin (X + 1), x < y → F x = F y →
      ∃ k : ℤ, (R : Int) ≤ k ∧ k ≤ X ∧
        ∀ c ∈ C, nrm ((k : ℝ) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
    intro x y hlt' hFxy
    refine ⟨((y : ℕ) : ℤ) - ((x : ℕ) : ℤ), ?_, ?_, ?_⟩
    · have hpositive : (0 : Int) < ((y : Nat) : Int) - ((x : Nat) : Int) := by
        have : (x : Nat) < (y : Nat) := hlt'
        omega
      have hres : (x : Nat) % R = (y : Nat) % R :=
        congrArg Fin.val (congrArg Prod.snd hFxy)
      have hemod : ((x : Nat) : Int) % (R : Int) = ((y : Nat) : Int) % (R : Int) := by
        exact_mod_cast hres
      have hdvd : (R : Int) ∣ ((y : Nat) : Int) - ((x : Nat) : Int) :=
        Int.modEq_iff_dvd.mp hemod
      obtain ⟨z, hz⟩ := hdvd
      have hRpos : (0 : Int) < R := by exact_mod_cast hR
      have hzpos : 1 ≤ z := by nlinarith
      nlinarith
    · have := y.2
      have : ((y : ℕ) : ℤ) ≤ X := by omega
      omega
    · intro c hc
      have hfl : ⌊(m : ℝ) * Int.fract (((x : ℕ) : ℝ) / q c)⌋₊
          = ⌊(m : ℝ) * Int.fract (((y : ℕ) : ℝ) / q c)⌋₊ := by
        have := congrFun (congrArg Prod.fst hFxy) ⟨c, hc⟩
        exact congrArg Fin.val this
      set a := (m : ℝ) * Int.fract (((x : ℕ) : ℝ) / q c) with ha
      set b := (m : ℝ) * Int.fract (((y : ℕ) : ℝ) / q c) with hb
      have ha0 : 0 ≤ a := by
        have := Int.fract_nonneg (((x : ℕ) : ℝ) / q c); positivity
      have hb0 : 0 ≤ b := by
        have := Int.fract_nonneg (((y : ℕ) : ℝ) / q c); positivity
      have h1 := Nat.floor_le ha0
      have h2 := Nat.lt_floor_add_one a
      have h3 := Nat.floor_le hb0
      have h4 := Nat.lt_floor_add_one b
      rw [hfl] at h1 h2
      have hab : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
      have hfr : |Int.fract (((y : ℕ) : ℝ) / q c) - Int.fract (((x : ℕ) : ℝ) / q c)| < 1 / m := by
        have e : Int.fract (((y : ℕ) : ℝ) / q c) - Int.fract (((x : ℕ) : ℝ) / q c) = (b - a) / m := by
          rw [ha, hb]; field_simp
        rw [e, abs_div, abs_of_pos hm0, abs_sub_comm]
        exact div_lt_div_of_pos_right hab hm0
      have e2 : (((((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) : ℤ)) : ℝ) / q c
          = (Int.fract (((y : ℕ) : ℝ) / q c) - Int.fract (((x : ℕ) : ℝ) / q c))
            + ((⌊((y : ℕ) : ℝ) / q c⌋ - ⌊((x : ℕ) : ℝ) / q c⌋ : ℤ) : ℝ) := by
        push_cast
        rw [Int.fract, Int.fract]
        ring
      have e3 : nrm ((((((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) : ℤ)) : ℝ) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ))
          = nrm (Int.fract (((y : ℕ) : ℝ) / q c) - Int.fract (((x : ℕ) : ℝ) / q c)) := by
        have : ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) = q c := rfl
        rw [this, e2, nrm_add_int]
      rw [e3]
      exact lt_of_le_of_lt (nrm_le_abs _) hfr
  rcases lt_or_gt_of_ne hxy with h | h
  · exact core x y h hF
  · exact core y x h hF.symm


theorem explicit_long_null {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hs : 1 ≤ S.card) {δ : ℝ} (hδ : 0 < δ)
    (m h L R : ℕ) (hR : 1 ≤ R) (hRL : R ≤ 2 ^ L) (hm : 2 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) (hh : 1 ≤ h) :
    ∃ k : ℤ, (R : Int) ≤ k ∧ k ≤ ((2 ^ (2 * L + 4 * S.card ^ 2 * h ^ 2) : ℕ) : ℤ) ∧ InBall S δ k := by
  classical
  set s := S.card with hsdef
  set N : ℕ := 2 ^ (2 * L + 4 * s ^ 2 * h ^ 2) with hN
  set T : ℕ := 2 * L + 4 * s ^ 2 * h ^ 2 + h with hT
  set r : ℕ := Nat.sqrt T with hr
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this] at hm
    simp at hm
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hdim : L + h * (s * r) ≤ 2 * L + 4 * s ^ 2 * h ^ 2 := by
    have hr2 : r ^ 2 ≤ T := by simpa [hr, pow_two] using Nat.sqrt_le T
    have hgap : 0 ≤ (r : Int) - 2 * s * h ∨ (r : Int) - 2 * s * h ≤ 0 := le_total 0 _
    have hsq : 0 ≤ ((r : Int) - 2 * s * h) ^ 2 := sq_nonneg _
    have hsmall : h ≤ s ^ 2 * h ^ 2 := by
      have h1 : 1 ≤ s ^ 2 := Nat.one_le_pow 2 s hs
      have h2 : h ≤ h * h := Nat.le_mul_self h
      have h3 : h * h ≤ s ^ 2 * h ^ 2 := by
        calc h * h = 1 * h ^ 2 := by ring
          _ ≤ s ^ 2 * h ^ 2 := Nat.mul_le_mul_right _ h1
      exact h2.trans h3
    dsimp [T] at hr2
    nlinarith
  set C : Finset (ℕ × ℕ) := S ×ˢ Finset.Icc 1 r with hC
  have hCcard : C.card = s * r := by
    rw [hC, Finset.card_product, Nat.card_Icc]; simp [hsdef]
  have hCpos : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2) := by
    intro c hc
    rw [hC, Finset.mem_product] at hc
    have := hS c.1 hc.1
    positivity
  have hcount : m ^ C.card * R ≤ N := by
    rw [hCcard, hN]
    calc
      m ^ (s * r) * R ≤ (2 ^ h) ^ (s * r) * 2 ^ L :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hmh _) hRL
      _ = 2 ^ (L + h * (s * r)) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ (2 * L + 4 * s ^ 2 * h ^ 2) := Nat.pow_le_pow_right (by decide) hdim
  obtain ⟨k, hk1, hkN, hk⟩ := pigeonhole_box_multiple C hCpos m N R hm1 hR hcount
  refine ⟨k, hk1, by exact_mod_cast hkN, ?_⟩
  intro p hp
  have hp2 := hS p hp
  have hhalf : 1 / (m : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  have hbound : Pn (sqScales p) k ≤ δ / 2 := by
    apply Pn_le (sq_nonempty p)
    rintro q ⟨n, hn, rfl⟩
    by_cases hnr : n ≤ r
    · have hmem : (p, n) ∈ C := by
        rw [hC, Finset.mem_product]; exact ⟨hp, Finset.mem_Icc.mpr ⟨hn, hnr⟩⟩
      exact ((hk (p, n) hmem).trans_le hhalf).le
    · push_neg at hnr
      have hn2 : T < n ^ 2 := by
        have h1 := Nat.lt_succ_sqrt T
        have h2 : r + 1 ≤ n := hnr
        nlinarith
      have hq : 2 ^ T ≤ p ^ (n ^ 2) :=
        calc 2 ^ T ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) hn2.le
          _ ≤ p ^ (n ^ 2) := Nat.pow_le_pow_left hp2 _
      have hNm : N * m ≤ p ^ (n ^ 2) := by
        calc N * m ≤ N * 2 ^ h := Nat.mul_le_mul_left _ hmh
          _ = 2 ^ T := by simp only [hN, hT, pow_add]
          _ ≤ p ^ (n ^ 2) := hq
      have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      refine (nrm_le_abs _).trans ?_
      rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
      have hkabs : |(k : ℝ)| ≤ N := by
        rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
        exact_mod_cast hkN
      have hNmR : (N : ℝ) * m ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hNm
      have hN0 : (0 : ℝ) ≤ N := by positivity
      calc |(k : ℝ)| ≤ N := hkabs
        _ = (N : ℝ) * (m * δ) / (m * δ) := by field_simp
        _ ≤ (N : ℝ) * (m * δ) / 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hm
        _ = ((N : ℝ) * m) * δ / 2 := by ring
        _ ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) * δ / 2 := by gcongr
        _ = δ / 2 * ((p ^ (n ^ 2) : ℕ) : ℝ) := by ring
  linarith


#print axioms explicit_long_null
end LeanCheck.ShiftedHeight


