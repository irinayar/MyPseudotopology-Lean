import LeanCheck.ChainN1

/-!
# The mixed-prime dual has Hausdorff dimension zero: the covering bound
(TVGadd-v4 Theorem `mixed:dimension`)
-/

namespace LeanCheck

open Finset Real Filter Topology

section Pl

/-- `P(k) < δ` for the integer `k`: all the observations `k / 2^{n²}`, `k / 3^{n²}` are within `δ` of a whole number. -/
def Pl (k : ℤ) (δ : ℝ) : Prop := PltQ (k : ℚ) 1 δ

lemma Pl_iff (k : ℤ) (δ : ℝ) :
    Pl k δ ↔ ∀ n : ℕ, ‖(((k : ℝ) / (2 : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ < δ ∧ ‖(((k : ℝ) / (3 : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ < δ := by
  unfold Pl PltQ xiSet
  constructor
  · rintro ⟨h2, h3⟩ n
    have a := h2 (2 ^ (n ^ 2)) (mem_Cp.2 ⟨n, rfl⟩)
    have b := h3 (3 ^ (n ^ 2)) (mem_Cp.2 ⟨n, rfl⟩)
    refine ⟨?_, ?_⟩
    · convert a using 3; push_cast; simp
    · convert b using 3; push_cast; simp
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨n, rfl⟩ := mem_Cp.1 hc
      have := (h n).1
      convert this using 3; push_cast; simp
    · obtain ⟨n, rfl⟩ := mem_Cp.1 hc
      have := (h n).2
      convert this using 3; push_cast; simp

lemma Pl_mono {k : ℤ} {δ δ' : ℝ} (h : δ ≤ δ') (hk : Pl k δ) : Pl k δ' := by
  rw [Pl_iff] at *
  exact fun n => ⟨lt_of_lt_of_le (hk n).1 h, lt_of_lt_of_le (hk n).2 h⟩

lemma Pl_double {k : ℤ} {ε : ℝ} (hk : Pl k (ε / 2)) : Pl (2 * k) ε := by
  rw [Pl_iff] at *
  intro n
  have key : ∀ c : ℝ, ‖((((2 * k : ℤ) : ℝ) / c : ℝ) : Circ)‖ ≤ 2 * ‖(((k : ℝ) / c : ℝ) : Circ)‖ := by
    intro c
    have : (((2 * k : ℤ) : ℝ) / c) = ((2 : ℕ) : ℝ) * ((k : ℝ) / c) := by push_cast; ring
    rw [this, ← nsmul_coe_circ]
    simpa using (norm_nsmul_le : ‖(2 : ℕ) • (((k : ℝ) / c : ℝ) : Circ)‖ ≤ ((2 : ℕ) : ℝ) * ‖(((k : ℝ) / c : ℝ) : Circ)‖)
  constructor
  · have := (hk n).1; have := key ((2 : ℝ) ^ (n ^ 2)); linarith
  · have := (hk n).2; have := key ((3 : ℝ) ^ (n ^ 2)); linarith

/-- The polar `K_ε`. -/
def Kset (ε : ℝ) : Set ℝ := {α | ∀ k : ℤ, Pl k ε → ‖((α * k : ℝ) : Circ)‖ ≤ 1 / 4}

lemma Kset_eighth {ε α : ℝ} (hα : α ∈ Kset ε) {k : ℤ} (hk : Pl k (ε / 2)) : ‖((α * k : ℝ) : Circ)‖ ≤ 1 / 8 := by
  have hε : 0 ≤ ε := by
    have := (Pl_iff k (ε / 2)).1 hk 0
    have h0 := this.1
    have : 0 ≤ ‖(((k : ℝ) / (2 : ℝ) ^ (0 ^ 2) : ℝ) : Circ)‖ := norm_nonneg _
    linarith
  have h1 : ‖((α * k : ℝ) : Circ)‖ ≤ 1 / 4 := hα k (Pl_mono (by linarith) hk)
  have h2 : ‖((α * ((2 * k : ℤ) : ℝ) : ℝ) : Circ)‖ ≤ 1 / 4 := hα (2 * k) (Pl_double hk)
  set x := α * k with hx
  have e2 : α * ((2 * k : ℤ) : ℝ) = 2 * x := by push_cast; ring
  rw [e2] at h2
  rw [norm_coe_circ] at h1
  set y := x - round x with hy
  have hy4 : |y| ≤ 1 / 4 := h1
  have e3 : ((2 * x : ℝ) : Circ) = ((2 * y : ℝ) : Circ) := by
    have : 2 * x = 2 * y + ((2 * round x : ℤ) : ℝ) := by push_cast [hy]; ring
    rw [this, AddCircle.coe_add, coe_int_circ_zero, add_zero]
  rw [e3, norm_coe_eq_abs_of_le (by rw [abs_mul]; norm_num; linarith)] at h2
  rw [abs_mul] at h2
  have : |y| ≤ 1 / 8 := by norm_num at h2; linarith
  rw [norm_coe_circ]
  exact this

end Pl

section Count

lemma norm_sub_lt_of_floor_eq {u v : ℝ} {L : ℕ} (hL : 0 < L)
    (h : ⌊(L : ℝ) * Int.fract u⌋₊ = ⌊(L : ℝ) * Int.fract v⌋₊) : ‖((u - v : ℝ) : Circ)‖ < 1 / L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set a := Int.fract u with ha
  set b := Int.fract v with hb
  have hLa : 0 ≤ (L : ℝ) * a := by positivity [Int.fract_nonneg u]
  have hLb : 0 ≤ (L : ℝ) * b := by positivity [Int.fract_nonneg v]
  have h1 := Nat.floor_le hLa
  have h2 := Nat.lt_floor_add_one ((L : ℝ) * a)
  have h3 := Nat.floor_le hLb
  have h4 := Nat.lt_floor_add_one ((L : ℝ) * b)
  rw [h] at h1 h2
  have hab : |a - b| < 1 / L := by
    have : |(L : ℝ) * a - (L : ℝ) * b| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← mul_sub, abs_mul, abs_of_pos hLr] at this
    rw [lt_div_iff₀ hLr]; linarith
  have heq : u - v = ((⌊u⌋ - ⌊v⌋ : ℤ) : ℝ) + (a - b) := by
    have e1 := Int.floor_add_fract u
    have e2 := Int.floor_add_fract v
    push_cast
    rw [← ha, ← hb] at *
    linarith
  rw [heq, AddCircle.coe_add, coe_int_circ_zero, zero_add]
  exact lt_of_le_of_lt ((norm_coe_le _ 0).trans (by simp)) hab

/-- The bases `2` and `3`. -/
def ell (b : Bool) : ℕ := if b then 2 else 3

lemma ell_ge (b : Bool) : 2 ≤ ell b := by cases b <;> simp [ell]

lemma two_pow_le (b : Bool) (n : ℕ) : 2 ^ (n ^ 2) ≤ ell b ^ (n ^ 2) :=
  Nat.pow_le_pow_left (ell_ge b) _

/-- A large set of integers in `[0, N]` whose observations are all small. -/
lemma exists_large_Pl_set (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 1 / (L : ℝ) ≤ δ) (N : ℕ) :
    ∃ A : Finset ℤ, (∀ k ∈ A, 0 ≤ k ∧ k ≤ N ∧ Pl k δ) ∧
      ((N : ℝ) + 1) ≤ (L : ℝ) ^ (2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1)) * A.card := by
  classical
  set T := Nat.sqrt (Nat.log 2 (N * L)) with hT
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let obs : Bool × Fin (T + 1) → ℕ := fun i => ell i.1 ^ ((i.2 : ℕ) ^ 2)
  have hobs_pos : ∀ i, 0 < obs i := fun i => Nat.pow_pos (by have := ell_ge i.1; omega)
  let box : ℤ → (Bool × Fin (T + 1) → Fin L) := fun k i =>
    ⟨⌊(L : ℝ) * Int.fract ((k : ℝ) / (obs i : ℝ))⌋₊, by
      rw [Nat.floor_lt (by positivity [Int.fract_nonneg ((k : ℝ) / (obs i : ℝ))])]
      exact mul_lt_of_lt_one_right hLr (Int.fract_lt_one _)⟩
  haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  set s : Finset ℤ := Finset.Icc (0 : ℤ) N with hs
  have hscard : s.card = N + 1 := by simp [hs]
  have hd : Fintype.card (Bool × Fin (T + 1) → Fin L) = L ^ (2 * (T + 1)) := by
    simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool]
  have hy : ∃ y, N + 1 ≤ L ^ (2 * (T + 1)) * (s.filter (fun k => box k = y)).card := by
    by_contra hcon
    push_neg at hcon
    have hsum : ∑ y : (Bool × Fin (T + 1) → Fin L), (s.filter (fun k => box k = y)).card = s.card :=
      (Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (box k))).symm
    have hlt : ∑ y : (Bool × Fin (T + 1) → Fin L), L ^ (2 * (T + 1)) * (s.filter (fun k => box k = y)).card <
        ∑ y : (Bool × Fin (T + 1) → Fin L), (N + 1) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hcon y)
    rw [← Finset.mul_sum, hsum, hscard, Finset.sum_const, Finset.card_univ, hd, smul_eq_mul] at hlt
    exact absurd hlt (lt_irrefl _)
  obtain ⟨y, hy⟩ := hy
  set F := s.filter (fun k => box k = y) with hF
  have hFne : F.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have : F.card = 0 := by omega
    rw [this] at hy
    simp at hy
  set k0 := F.min' hFne with hk0
  have hk0F : k0 ∈ F := Finset.min'_mem F hFne
  refine ⟨F.image (fun k => k - k0), ?_, ?_⟩
  · intro k' hk'
    obtain ⟨k, hkF, rfl⟩ := Finset.mem_image.1 hk'
    have hks : k ∈ s := (Finset.mem_filter.1 hkF).1
    have hk0s : k0 ∈ s := (Finset.mem_filter.1 hk0F).1
    rw [hs, Finset.mem_Icc] at hks hk0s
    have hle : k0 ≤ k := Finset.min'_le F k hkF
    refine ⟨by omega, by omega, ?_⟩
    rw [Pl_iff]
    intro n
    have key : ∀ b : Bool, ‖((((k - k0 : ℤ) : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) : ℝ) : Circ)‖ < δ := by
      intro b
      have hcpos : (0 : ℝ) < (ell b : ℝ) ^ (n ^ 2) := by
        have := ell_ge b; positivity
      by_cases hret : ell b ^ (n ^ 2) ≤ N * L
      · have hn : n ≤ T := by
          have h1 : 2 ^ (n ^ 2) ≤ N * L := (two_pow_le b n).trans hret
          have h2 : n ^ 2 ≤ Nat.log 2 (N * L) := Nat.le_log_of_pow_le (by norm_num) h1
          exact Nat.le_sqrt'.2 h2
        have hbox : box k = box k0 := by
          rw [(Finset.mem_filter.1 hkF).2, (Finset.mem_filter.1 hk0F).2]
        have hi := congrFun hbox (b, ⟨n, Nat.lt_succ_of_le hn⟩)
        have hfl : ⌊(L : ℝ) * Int.fract ((k : ℝ) / (obs (b, ⟨n, Nat.lt_succ_of_le hn⟩) : ℝ))⌋₊ =
            ⌊(L : ℝ) * Int.fract ((k0 : ℝ) / (obs (b, ⟨n, Nat.lt_succ_of_le hn⟩) : ℝ))⌋₊ := congrArg Fin.val hi
        have hobsv : (obs (b, ⟨n, Nat.lt_succ_of_le hn⟩) : ℝ) = (ell b : ℝ) ^ (n ^ 2) := by
          simp only [obs]; push_cast; rfl
        rw [hobsv] at hfl
        have := norm_sub_lt_of_floor_eq hL hfl
        have e : (((k - k0 : ℤ) : ℝ) / ((ell b : ℝ) ^ (n ^ 2))) = (k : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) - (k0 : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) := by
          push_cast; ring
        rw [e]
        exact lt_of_lt_of_le this hδ
      · push_neg at hret
        have hN : ((k - k0 : ℤ) : ℝ) ≤ N := by
          have : (k - k0 : ℤ) ≤ N := by omega
          exact_mod_cast this
        have h0 : (0 : ℝ) ≤ ((k - k0 : ℤ) : ℝ) := by
          have : (0 : ℤ) ≤ k - k0 := by omega
          exact_mod_cast this
        have hbig : (N : ℝ) * L < (ell b : ℝ) ^ (n ^ 2) := by exact_mod_cast hret
        have hnorm : ‖((((k - k0 : ℤ) : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) : ℝ) : Circ)‖ ≤ ((k - k0 : ℤ) : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) :=
          (norm_coe_le _ 0).trans (by rw [Int.cast_zero, sub_zero, abs_of_nonneg (div_nonneg h0 hcpos.le)])
        have hlt : ((k - k0 : ℤ) : ℝ) / ((ell b : ℝ) ^ (n ^ 2)) < 1 / L := by
          rw [div_lt_div_iff₀ hcpos hLr]; nlinarith
        exact lt_of_le_of_lt hnorm (lt_of_lt_of_le hlt hδ)
    exact ⟨by simpa [ell] using key true, by simpa [ell] using key false⟩
  · rw [Finset.card_image_of_injective _ (sub_left_injective)]
    exact_mod_cast hy

end Count

section Cover

lemma sqrt2_ge : (7 : ℝ) / 5 ≤ √2 := by
  apply Real.le_sqrt_of_sq_le; norm_num

/-- **Covering bound.**  For `α ∈ K_ε ∩ [0,1)` there is a grid interval `[m/(100N), (m+1)/(100N))` containing `α` among a family of at
most `400 L^{2(T+1)}` such intervals. -/
theorem cover_Kset (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 0 < L) (hLε : 1 / (L : ℝ) ≤ ε / 2) (N : ℕ) (hN : 1 ≤ N) :
    ∃ G : Finset ℕ, (G.card : ℝ) ≤ 400 * (L : ℝ) ^ (2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1)) ∧
      ∀ α ∈ Kset ε, 0 ≤ α → α < 1 → ∃ m ∈ G, (m : ℝ) / (100 * N) ≤ α ∧ α < ((m : ℝ) + 1) / (100 * N) := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_large_Pl_set L hL (ε / 2) hLε N
  set M : ℕ := 100 * N with hM
  have hMpos : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMN : (M : ℝ) = 100 * N := by rw [hM]; push_cast; ring
  have hspread : ∀ k ∈ A, ∀ l ∈ A, |k - l| < M := by
    intro k hk l hl
    have h1 := hA k hk; have h2 := hA l hl
    rw [abs_lt]; constructor <;> omega
  set d := 2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1) with hd
  have hApos : 0 < A.card := by
    rcases Nat.eq_zero_or_pos A.card with h0 | h0
    · rw [h0] at hcard; simp at hcard; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    · exact h0
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hApos
  set G := (range M).filter (fun m : ℕ => (A.card : ℝ) ^ 2 / 4 ≤ Qf A ((m : ℝ) / M)) with hG
  have hgc := grid_count A M hMpos hspread
  refine ⟨G, ?_, ?_⟩
  · -- the cardinality bound
    have h1 : (G.card : ℝ) * (A.card : ℝ) ≤ 4 * M := by
      have : (G.card : ℝ) * ((A.card : ℝ) ^ 2 / 4) ≤ M * A.card := hgc
      have h2 : (G.card : ℝ) * A.card * (A.card : ℝ) ≤ 4 * M * A.card := by nlinarith
      exact le_of_mul_le_mul_right h2 hAr
    have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    have h3 : (G.card : ℝ) * ((N : ℝ) + 1) ≤ (G.card : ℝ) * ((L : ℝ) ^ d * A.card) :=
      mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    have h4 : (G.card : ℝ) * ((L : ℝ) ^ d * A.card) ≤ (L : ℝ) ^ d * (4 * M) := by
      calc (G.card : ℝ) * ((L : ℝ) ^ d * A.card) = (L : ℝ) ^ d * ((G.card : ℝ) * A.card) := by ring
        _ ≤ (L : ℝ) ^ d * (4 * M) := mul_le_mul_of_nonneg_left h1 hLd.le
    have h5 : (G.card : ℝ) * ((N : ℝ) + 1) ≤ 400 * (L : ℝ) ^ d * ((N : ℝ) + 1) := by
      rw [hMN] at h4
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact le_of_mul_le_mul_right h5 (by positivity)
  · intro α hα h0 h1
    set m : ℕ := ⌊α * M⌋₊ with hm
    have hm1 : (m : ℝ) ≤ α * M := Nat.floor_le (by positivity)
    have hm2 : α * M < m + 1 := Nat.lt_floor_add_one _
    have hmM : m < M := by
      have : (m : ℝ) < M := by nlinarith
      exact_mod_cast this
    have hleft : (m : ℝ) / (100 * N) ≤ α := by
      rw [← hMN, div_le_iff₀ hMr]; linarith
    have hright : α < ((m : ℝ) + 1) / (100 * N) := by
      rw [← hMN, lt_div_iff₀ hMr]; linarith
    refine ⟨m, ?_, hleft, hright⟩
    rw [hG, Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hmM, ?_⟩
    set g : ℝ := (m : ℝ) / M with hg
    have e1 : g ≤ α := by rw [hg, div_le_iff₀ hMr]; linarith
    have e2 : α < g + 1 / M := by
      rw [hg, ← add_div, lt_div_iff₀ hMr]; linarith
    have hgα : |g - α| ≤ 1 / M := by
      rw [abs_le]; constructor <;> linarith [(by positivity : (0 : ℝ) < 1 / M)]
    have hcos : ∀ k ∈ A, (1 : ℝ) / 2 ≤ Real.cos (2 * π * k * g) := by
      intro k hk
      obtain ⟨hk0, hkN, hPl⟩ := hA k hk
      have h8 := Kset_eighth hα hPl
      have hc := cos_ge_of_norm_le_eighth h8
      have hlip := Real.abs_cos_sub_cos_le (2 * π * k * g) (2 * π * (α * k))
      have hk0r : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      have hkNr : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have hdiff : |2 * π * k * g - 2 * π * (α * k)| ≤ 2 * π / 100 := by
        have : 2 * π * k * g - 2 * π * (α * k) = 2 * π * k * (g - α) := by ring
        rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * k)]
        calc 2 * π * k * |g - α| ≤ 2 * π * N * (1 / M) := by
              apply mul_le_mul (by nlinarith [Real.pi_pos]) hgα (abs_nonneg _) (by positivity)
          _ = 2 * π / 100 := by
              rw [hMN]; field_simp
      have hpi := Real.pi_lt_d2
      have h2 := sqrt2_ge
      have habs := abs_le.1 (hlip.trans hdiff)
      nlinarith [habs.1, habs.2]
    have hCf : (A.card : ℝ) / 2 ≤ Cf A g := by
      calc (A.card : ℝ) / 2 = ∑ k ∈ A, (1 : ℝ) / 2 := by simp [Finset.sum_const]; ring
        _ ≤ Cf A g := Finset.sum_le_sum hcos
    rw [Qf_eq]
    nlinarith [sq_nonneg (Sf A g), sq_nonneg (Cf A g - A.card / 2), hCf, hAr]

end Cover

section Analysis

/-- The covering number is `exp(O(√log N))`. -/
lemma exp_sqrt_bound (L : ℕ) (hL : 2 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (400 : ℝ) * (L : ℝ) ^ (2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1)) ≤ Real.exp (C * √(Real.log N)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set a : ℝ := (1 + Real.log L / Real.log 2) / Real.log 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set c1 : ℝ := √a with hc1
  set s0 : ℝ := √(Real.log 2) with hs0
  have hs0pos : 0 < s0 := Real.sqrt_pos.2 hl2
  refine ⟨2 * c1 * Real.log L + 2 * Real.log L / s0 + Real.log 400 / s0 + 1, by positivity, ?_⟩
  intro N hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set u : ℝ := Real.log N with hu
  have hu2 : Real.log 2 ≤ u := Real.log_le_log (by norm_num) hNr
  have hupos : 0 < u := lt_of_lt_of_le hl2 hu2
  have hsu : s0 ≤ √u := Real.sqrt_le_sqrt hu2
  have hX : (N * L : ℕ) ≠ 0 := by positivity
  -- bound on `Nat.log`
  have hlog : (Nat.log 2 (N * L) : ℝ) * Real.log 2 ≤ Real.log N + Real.log L := by
    have h1 : (2 : ℕ) ^ Nat.log 2 (N * L) ≤ N * L := Nat.pow_log_le_self 2 hX
    have h2 : ((2 : ℝ)) ^ Nat.log 2 (N * L) ≤ (N : ℝ) * L := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at h3
    exact h3
  have hlogL' : Real.log L ≤ (Real.log L / Real.log 2) * u := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith
  have hlog2 : (Nat.log 2 (N * L) : ℝ) ≤ a * u := by
    rw [ha, div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith
  have hT : (Nat.sqrt (Nat.log 2 (N * L)) : ℝ) ≤ c1 * √u := by
    have h1 : (Nat.sqrt (Nat.log 2 (N * L)) : ℝ) ≤ √((Nat.log 2 (N * L) : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    refine h1.trans ?_
    rw [hc1, ← Real.sqrt_mul ha0]
    exact Real.sqrt_le_sqrt hlog2
  -- the exponent
  have hexp : Real.log 400 + (2 * ((Nat.sqrt (Nat.log 2 (N * L)) : ℝ) + 1)) * Real.log L ≤
      (2 * c1 * Real.log L + 2 * Real.log L / s0 + Real.log 400 / s0 + 1) * √u := by
    have hu1 : 1 ≤ √u / s0 := by rw [le_div_iff₀ hs0pos]; linarith
    have hsq : 0 < √u := lt_of_lt_of_le hs0pos hsu
    have h4 : Real.log L * 2 ≤ 2 * Real.log L / s0 * √u := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs0pos]; nlinarith
    have h5 : Real.log 400 ≤ Real.log 400 / s0 * √u := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs0pos]
      have : 0 ≤ Real.log 400 := Real.log_nonneg (by norm_num)
      nlinarith
    have h6 : 2 * (c1 * √u) * Real.log L ≤ 2 * c1 * Real.log L * √u := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * Real.log L)]
  have e400 : (400 : ℝ) = Real.exp (Real.log 400) := (Real.exp_log (by norm_num)).symm
  have eL : (L : ℝ) ^ (2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1)) =
      Real.exp ((2 * ((Nat.sqrt (Nat.log 2 (N * L)) : ℝ) + 1)) * Real.log L) := by
    rw [← Real.exp_log (show (0 : ℝ) < (L : ℝ) ^ (2 * (Nat.sqrt (Nat.log 2 (N * L)) + 1)) by positivity)]
    rw [Real.log_pow]; congr 1; push_cast; ring
  rw [eL]
  conv_lhs => rw [e400]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 hexp

end Analysis

section Dim

open MeasureTheory

lemma sqrt_minus_linear_atBot (C s : ℝ) (hs : 0 < s) :
    Tendsto (fun x : ℝ => C * √x - s * x) atTop atBot := by
  have hg : Tendsto (fun x : ℝ => -(s / 2) * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  refine tendsto_atBot_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop ((2 * |C| / s) ^ 2 + 1)] with x hx
  have hx0 : 0 ≤ x := by nlinarith [sq_nonneg (2 * |C| / s)]
  have hsq : 2 * |C| / s ≤ √x := by
    apply Real.le_sqrt_of_sq_le; linarith
  have : |C| * √x ≤ s / 2 * x := by
    have h1 : 2 * |C| ≤ s * √x := by
      rw [div_le_iff₀ hs] at hsq; linarith
    have h2 : √x * √x = x := Real.mul_self_sqrt hx0
    nlinarith [Real.sqrt_nonneg x]
  have h3 : C * √x ≤ |C| * √x := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg x)
  nlinarith

lemma decay_tendsto (C s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => Real.exp (C * √(Real.log ((n : ℝ) + 2))) * (1 / (100 * ((n : ℝ) + 2))) ^ s) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => Real.exp (C * √(Real.log ((n : ℝ) + 2)) - s * Real.log ((n : ℝ) + 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((sqrt_minus_linear_atBot C s hs).comp hlog)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => by positivity) (fun n => ?_)
  have hx : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : (1 / (100 * ((n : ℝ) + 2))) ^ s ≤ Real.exp (-(s * Real.log ((n : ℝ) + 2))) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.2
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by norm_num) hx.ne']
    have : 0 ≤ Real.log 100 := Real.log_nonneg (by norm_num)
    nlinarith
  calc Real.exp (C * √(Real.log ((n : ℝ) + 2))) * (1 / (100 * ((n : ℝ) + 2))) ^ s
      ≤ Real.exp (C * √(Real.log ((n : ℝ) + 2))) * Real.exp (-(s * Real.log ((n : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (C * √(Real.log ((n : ℝ) + 2)) - s * Real.log ((n : ℝ) + 2)) := by
        rw [← Real.exp_add]; ring_nf

lemma Kset_translate {ε α : ℝ} (hα : α ∈ Kset ε) (z : ℤ) : α - z ∈ Kset ε := by
  intro k hk
  have := hα k hk
  have e : (α - z) * k = α * k - ((z * k : ℤ) : ℝ) := by push_cast; ring
  rw [e, AddCircle.coe_sub, coe_int_circ_zero, sub_zero]
  exact this

set_option maxHeartbeats 1600000 in
/-- Covers of a set of reals by grid intervals, with at most `exp(C √log(n+2))` intervals, force Hausdorff dimension zero. -/
lemma dimH_zero_of_grid_covers (P : Set ℝ) (z C : ℝ) (G : ℕ → Finset ℕ)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ Real.exp (C * √(Real.log ((n : ℝ) + 2))))
    (hcov : ∀ n, ∀ α ∈ P, ∃ m ∈ G n, z + (m : ℝ) / (100 * ((n : ℝ) + 2)) ≤ α ∧
      α < z + ((m : ℝ) + 1) / (100 * ((n : ℝ) + 2))) : dimH P = 0 := by
  classical
  have hdim : ∀ s : NNReal, 0 < s → dimH P ≤ s := by
    intro s hs
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    apply dimH_le_of_hausdorffMeasure_ne_top (d := s)
    let t : ∀ n : ℕ, ↥(G n) → Set ℝ := fun n i =>
      Set.Ico (z + (i.1 : ℝ) / (100 * ((n : ℝ) + 2))) (z + ((i.1 : ℝ) + 1) / (100 * ((n : ℝ) + 2)))
    have htdiam : ∀ n i, Metric.ediam (t n i) = ENNReal.ofReal (1 / (100 * ((n : ℝ) + 2))) := by
      intro n i
      show Metric.ediam (Set.Ico _ _) = _
      rw [Real.ediam_Ico]; congr 1; field_simp; ring
    have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (100 * ((n : ℝ) + 2)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (100 * ((n : ℝ) + 2))) atTop atTop := by
        apply Filter.Tendsto.const_mul_atTop (by norm_num)
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h0 : Tendsto (fun n : ℕ => 1 / (100 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
        refine h1.inv_tendsto_atTop.congr (fun n => ?_)
        simp [one_div]
      simpa using ENNReal.tendsto_ofReal h0
    have hmain : μH[(s : ℝ)] P ≤ liminf (fun n : ℕ => ∑ i : ↥(G n), Metric.ediam (t n i) ^ (s : ℝ)) atTop :=
      MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum (ι := fun n => ↥(G n)) (s : ℝ) P (l := atTop)
        (fun n : ℕ => ENNReal.ofReal (1 / (100 * ((n : ℝ) + 2)))) hr t
        (Filter.Eventually.of_forall (fun n i => (htdiam n i).le))
        (Filter.Eventually.of_forall (fun n α hα => by
          obtain ⟨m, hm, hm1, hm2⟩ := hcov n α hα
          exact Set.mem_iUnion.2 ⟨⟨m, hm⟩, hm1, hm2⟩))
    have hterm : ∀ n : ℕ, ∑ i : ↥(G n), Metric.ediam (t n i) ^ (s : ℝ)
        ≤ ENNReal.ofReal (Real.exp (C * √(Real.log ((n : ℝ) + 2))) * (1 / (100 * ((n : ℝ) + 2))) ^ (s : ℝ)) := by
      intro n
      simp only [htdiam, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs'.le,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (hcard n) (by positivity)
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (C * √(Real.log ((n : ℝ) + 2))) *
        (1 / (100 * ((n : ℝ) + 2))) ^ (s : ℝ))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (decay_tendsto C s hs')
    have hle := Filter.liminf_le_liminf (Filter.Eventually.of_forall hterm :
      ∀ᶠ n in atTop, _ ≤ _)
    rw [hlim.liminf_eq] at hle
    have : μH[(s : ℝ)] P = 0 := le_antisymm (hmain.trans hle) bot_le
    rw [this]; exact ENNReal.zero_ne_top
  apply le_antisymm _ bot_le
  refine ENNReal.le_of_forall_pos_le_add (fun s hs _ => ?_)
  simpa using hdim s hs

/-- **Quantitative covering bound** (TVGadd-v4 Theorem `mixed:dimension`, first assertion, in the grid form):
`K_ε ∩ [0,1)` is covered by at most `exp(C √log N)` intervals of length `1/(100N)`. -/
theorem covering_exp_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∃ G : Finset ℕ, (G.card : ℝ) ≤ Real.exp (C * √(Real.log N)) ∧
      ∀ α ∈ Kset ε, 0 ≤ α → α < 1 → ∃ m ∈ G, (m : ℝ) / (100 * N) ≤ α ∧ α < ((m : ℝ) + 1) / (100 * N) := by
  set L : ℕ := ⌈2 / ε⌉₊ + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hLpos : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hLε : 1 / (L : ℝ) ≤ ε / 2 := by
    have h1 : 2 / ε ≤ (L : ℝ) := by
      have := Nat.le_ceil (2 / ε)
      have h2 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) ≤ L := by rw [hL]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hLr]
    rw [div_le_iff₀ hε] at h1
    nlinarith
  obtain ⟨C, hC, hbound⟩ := exp_sqrt_bound L hL2
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨G, hG1, hG2⟩ := cover_Kset ε hε L hLpos hLε N (by omega)
  exact ⟨G, hG1.trans (hbound N hN), hG2⟩

theorem Kset_piece_dimH (ε : ℝ) (hε : 0 < ε) (z : ℤ) :
    dimH (Kset ε ∩ Set.Ico (z : ℝ) (z + 1)) = 0 := by
  classical
  obtain ⟨C, hC, hcov⟩ := covering_exp_bound ε hε
  have hcov' : ∀ n : ℕ, ∃ G : Finset ℕ, (G.card : ℝ) ≤ Real.exp (C * √(Real.log ((n : ℝ) + 2))) ∧
      ∀ α ∈ Kset ε, 0 ≤ α → α < 1 → ∃ m ∈ G, (m : ℝ) / (100 * ((n : ℝ) + 2)) ≤ α ∧
        α < ((m : ℝ) + 1) / (100 * ((n : ℝ) + 2)) := by
    intro n
    obtain ⟨G, h1, h2⟩ := hcov (n + 2) (by omega)
    push_cast at h1 h2
    exact ⟨G, h1, h2⟩
  choose G hGcard hGcov using hcov'
  refine dimH_zero_of_grid_covers _ (z : ℝ) C G hGcard (fun n α hα => ?_)
  obtain ⟨m, hm, hm1, hm2⟩ := hGcov n (α - z) (Kset_translate hα.1 z) (by linarith [hα.2.1]) (by linarith [hα.2.2])
  exact ⟨m, hm, by linarith, by linarith⟩

theorem Kset_dimH (ε : ℝ) (hε : 0 < ε) : dimH (Kset ε) = 0 := by
  have hsub : Kset ε ⊆ ⋃ z : ℤ, (Kset ε ∩ Set.Ico (z : ℝ) (z + 1)) := by
    intro α hα
    refine Set.mem_iUnion.2 ⟨⌊α⌋, hα, Int.floor_le α, Int.lt_floor_add_one α⟩
  apply le_antisymm _ bot_le
  calc dimH (Kset ε) ≤ dimH (⋃ z : ℤ, (Kset ε ∩ Set.Ico (z : ℝ) (z + 1))) := dimH_mono hsub
    _ = ⨆ z : ℤ, dimH (Kset ε ∩ Set.Ico (z : ℝ) (z + 1)) := dimH_iUnion _
    _ = 0 := by simp [Kset_piece_dimH ε hε]

/-- **TVGadd-v4 Theorem `mixed:dimension`.**  The set of real parameters `α` for which `k ↦ α k mod 1` is continuous on `(ℤ, P)` has
Hausdorff dimension zero. -/
theorem mixed_dual_dimH_zero : dimH {α : ℝ | Hint α} = 0 := by
  have hsub : {α : ℝ | Hint α} ⊆ ⋃ m : ℕ, Kset (1 / ((m : ℝ) + 1)) := by
    intro α hα
    obtain ⟨δ, hδ, hH⟩ := hα (1 / 4) (by norm_num)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine Set.mem_iUnion.2 ⟨m, fun k hk => ?_⟩
    have hk' : PltQ (k : ℚ) 1 δ := Pl_mono hm.le hk
    exact (hH k hk').le
  apply le_antisymm _ bot_le
  calc dimH {α : ℝ | Hint α} ≤ dimH (⋃ m : ℕ, Kset (1 / ((m : ℝ) + 1))) := dimH_mono hsub
    _ = ⨆ m : ℕ, dimH (Kset (1 / ((m : ℝ) + 1))) := dimH_iUnion _
    _ = 0 := by
        simp only [ENNReal.iSup_eq_zero]
        intro m
        exact Kset_dimH _ (by positivity)

end Dim

section Group

lemma Hint_add {α β : ℝ} (hα : Hint α) (hβ : Hint β) : Hint (α + β) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hα (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hβ (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun k hk => ?_⟩
  have hk₁ : PltQ (k : ℚ) 1 δ₁ := Pl_mono (min_le_left _ _) hk
  have hk₂ : PltQ (k : ℚ) 1 δ₂ := Pl_mono (min_le_right _ _) hk
  have e : ((α + β) * (k : ℝ)) = α * k + β * k := by ring
  rw [e]
  calc ‖((α * k + β * k : ℝ) : Circ)‖ ≤ ‖((α * k : ℝ) : Circ)‖ + ‖((β * k : ℝ) : Circ)‖ := norm_circ_add_le _ _
    _ < ε := by linarith [h₁ k hk₁, h₂ k hk₂]

lemma Hint_zero : Hint 0 := by
  intro ε hε
  exact ⟨1, one_pos, fun k _ => by simpa using hε⟩

lemma Hint_neg {α : ℝ} (hα : Hint α) : Hint (-α) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hα ε hε
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have := h k hk
  have e : ((-α) * (k : ℝ)) = -(α * k) := by ring
  rw [e, AddCircle.coe_neg, norm_neg]
  exact this

lemma Hint_nat_mul {α : ℝ} (hα : Hint α) : ∀ n : ℕ, Hint ((n : ℝ) * α)
  | 0 => by simpa using Hint_zero
  | n + 1 => by
      have := Hint_add (Hint_nat_mul hα n) hα
      convert this using 1; push_cast; ring

lemma Hint_int_mul {α : ℝ} (hα : Hint α) (m : ℤ) : Hint ((m : ℝ) * α) := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · simpa using Hint_nat_mul hα n
  · have := Hint_neg (Hint_nat_mul hα n)
    convert this using 1; push_cast; ring

/-- Dyadic and triadic reciprocals belong to `H`. -/
lemma Hint_inv_pow (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3) (a : ℕ) : Hint (1 / (ℓ : ℝ) ^ a) := by
  intro ε hε
  have hℓ0 : (2 : ℝ) ≤ ℓ := by rcases hℓ with rfl | rfl <;> norm_num
  set n : ℕ := a with hn
  have hna : a ≤ n ^ 2 := by nlinarith [Nat.zero_le n]
  set e : ℕ := n ^ 2 - a with he
  have hpow : (ℓ : ℝ) ^ (n ^ 2) = (ℓ : ℝ) ^ a * (ℓ : ℝ) ^ e := by
    rw [← pow_add]; congr 1; omega
  have hepos : (0 : ℝ) < (ℓ : ℝ) ^ e := by positivity
  refine ⟨ε / (ℓ : ℝ) ^ e, by positivity, fun k hk => ?_⟩
  have hobs : ‖(((k : ℝ) / (ℓ : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ < ε / (ℓ : ℝ) ^ e := by
    have := (Pl_iff k (ε / (ℓ : ℝ) ^ e)).1 hk n
    rcases hℓ with rfl | rfl
    · simpa using this.1
    · simpa using this.2
  have hrel : (1 / (ℓ : ℝ) ^ a) * k = ((ℓ ^ e : ℕ) : ℝ) * ((k : ℝ) / (ℓ : ℝ) ^ (n ^ 2)) := by
    rw [hpow]; push_cast; field_simp
  rw [hrel, ← nsmul_coe_circ]
  calc ‖(ℓ ^ e) • (((k : ℝ) / (ℓ : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ ≤ ((ℓ ^ e : ℕ) : ℝ) * ‖(((k : ℝ) / (ℓ : ℝ) ^ (n ^ 2) : ℝ) : Circ)‖ :=
        norm_nsmul_le
    _ < ((ℓ ^ e : ℕ) : ℝ) * (ε / (ℓ : ℝ) ^ e) := by
        apply mul_lt_mul_of_pos_left hobs; push_cast; exact hepos
    _ = ε := by push_cast; field_simp

/-- `ℤ[1/6]/ℤ ⊆ H`. -/
theorem Hint_Z16 (m : ℤ) (a b : ℕ) : Hint ((m : ℝ) / (2 ^ a * 3 ^ b)) := by
  have hcop : IsCoprime ((3 : ℤ) ^ b) ((2 : ℤ) ^ a) :=
    IsCoprime.pow (by norm_num [Int.isCoprime_iff_gcd_eq_one]) |>.symm.symm
  obtain ⟨x, y, hxy⟩ := hcop
  have e : (m : ℝ) / (2 ^ a * 3 ^ b) = (m * x : ℤ) * (1 / (2 : ℝ) ^ a) + ((m * y : ℤ) * (1 / (3 : ℝ) ^ b)) := by
    have h : ((x : ℝ) * 3 ^ b + y * 2 ^ a) = 1 := by exact_mod_cast hxy
    field_simp
    push_cast
    linear_combination (-(m : ℝ)) * h
  rw [e]
  exact Hint_add (Hint_int_mul (Hint_inv_pow 2 (Or.inl rfl) a) _) (Hint_int_mul (Hint_inv_pow 3 (Or.inr rfl) b) _)

/-- Almost every real parameter defines a discontinuous character. -/
theorem mixed_dual_null : MeasureTheory.volume {α : ℝ | Hint α} = 0 := by
  have h1 : dimH {α : ℝ | Hint α} < 1 := by rw [mixed_dual_dimH_zero]; exact zero_lt_one
  have := hausdorffMeasure_of_dimH_lt (d := 1) (s := {α : ℝ | Hint α}) (by simpa using h1)
  rw [NNReal.coe_one, MeasureTheory.hausdorffMeasure_real] at this
  simpa using this

end Group

end LeanCheck
