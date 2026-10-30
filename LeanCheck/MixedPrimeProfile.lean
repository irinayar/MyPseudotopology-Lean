import LeanCheck.MixedPrimeBasics

/-!
# TVGaddmore_v17: profile generators, summation lemma, summability (Lemma 7.11, Theorem 7.17)

For a finite set `L` of bases (the primes of `S`), the scale set is `Sc L = {ℓ^(n^2) | ℓ ∈ L, n ≥ 1}`,
so `Pn (Sc L)` is the paper's `P_S`.  An integer `g` has *profile* `(ε, r; P)` (centres `P ℓ`, one for each
`ℓ ∈ L`) if `‖g / ℓ^(n^2)‖ ≤ ε r^|n - P ℓ|` for all `ℓ ∈ L`, `n ≥ 1`.
-/

namespace LeanCheck
namespace MixedPrime

/-- The scales `ℓ^(n^2)`, `ℓ ∈ L`, `n ≥ 1`. -/
def Sc (L : Finset ℕ) : Set ℕ := {q | ∃ ℓ ∈ L, ∃ n : ℕ, 1 ≤ n ∧ q = ℓ ^ (n ^ 2)}

/-- `g` has profile `(ε, r; P)`. -/
def HasProfile (L : Finset ℕ) (r ε : ℝ) (P : ℕ → ℕ) (g : ℤ) : Prop :=
  ∀ ℓ ∈ L, ∀ n : ℕ, 1 ≤ n →
    nrm ((g : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) ≤ ε * r ^ (((n : ℤ) - P ℓ).natAbs)

lemma Sc_nonempty {L : Finset ℕ} (hL : L.Nonempty) : (Sc L).Nonempty := by
  obtain ⟨ℓ, hℓ⟩ := hL
  exact ⟨ℓ ^ (1 ^ 2), ℓ, hℓ, 1, le_rfl, rfl⟩

lemma HasProfile.Pn_le {L : Finset ℕ} (hL : L.Nonempty) {r ε : ℝ} (hε : 0 ≤ ε) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) {P : ℕ → ℕ} {g : ℤ} (h : HasProfile L r ε P g) : Pn (Sc L) g ≤ ε := by
  apply MixedPrime.Pn_le (Sc_nonempty hL)
  rintro q ⟨ℓ, hℓ, n, hn, rfl⟩
  have h0 := h ℓ hℓ n hn
  have h1 : r ^ (((n : ℤ) - P ℓ).natAbs) ≤ 1 := pow_le_one₀ hr0 hr1
  rw [Nat.cast_pow]
  calc nrm ((g : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) ≤ ε * r ^ (((n : ℤ) - P ℓ).natAbs) := h0
    _ ≤ ε * 1 := by gcongr
    _ = ε := mul_one ε

lemma HasProfile.nsmul {L : Finset ℕ} {r ε : ℝ} {P : ℕ → ℕ} {g : ℤ} (t : ℕ)
    (h : HasProfile L r ε P g) : HasProfile L r (t * ε) P ((t : ℤ) * g) := by
  intro ℓ hℓ n hn
  have e : (((t : ℤ) * g : ℤ) : ℝ) / ((ℓ : ℝ) ^ (n ^ 2)) = (t : ℝ) * ((g : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) := by
    push_cast; ring
  rw [e]
  calc nrm ((t : ℝ) * ((g : ℝ) / ((ℓ : ℝ) ^ (n ^ 2)))) ≤ t * nrm ((g : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) :=
        nrm_nsmul_le t _
    _ ≤ t * (ε * r ^ (((n : ℤ) - P ℓ).natAbs)) := by gcongr; exact h ℓ hℓ n hn
    _ = t * ε * r ^ (((n : ℤ) - P ℓ).natAbs) := by ring

/-- `∑_{t ∈ T} r^{|t|} ≤ (1+r)/(1-r)` for every finite set of integers. -/
lemma geomZ_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (T : Finset ℤ) :
    ∑ t ∈ T, r ^ t.natAbs ≤ (1 + r) / (1 - r) := by
  classical
  have hs : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0.le hr1
  have htsum : ∑' k : ℕ, r ^ k = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  have h1r : 0 < 1 - r := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not T (fun t => 0 ≤ t)]
  -- nonnegative part
  have hpos : ∑ t ∈ T.filter (fun t => 0 ≤ t), r ^ t.natAbs ≤ (1 - r)⁻¹ := by
    have hinj : Set.InjOn Int.toNat (T.filter (fun t => 0 ≤ t) : Set ℤ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      omega
    have e : ∑ t ∈ T.filter (fun t => 0 ≤ t), r ^ t.natAbs
        = ∑ k ∈ (T.filter (fun t => 0 ≤ t)).image Int.toNat, r ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [Finset.mem_filter] at ht
      congr 1; omega
    rw [e, ← htsum]
    exact hs.sum_le_tsum _ (fun k _ => pow_nonneg hr0.le k)
  -- negative part
  have hneg : ∑ t ∈ T.filter (fun t => ¬ 0 ≤ t), r ^ t.natAbs ≤ r * (1 - r)⁻¹ := by
    have hinj : Set.InjOn (fun t : ℤ => t.natAbs - 1) (T.filter (fun t => ¬ 0 ≤ t) : Set ℤ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb hab
      omega
    have e : ∑ t ∈ T.filter (fun t => ¬ 0 ≤ t), r ^ t.natAbs
        = ∑ k ∈ (T.filter (fun t => ¬ 0 ≤ t)).image (fun t : ℤ => t.natAbs - 1), r * r ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [Finset.mem_filter] at ht
      have : t.natAbs = (t.natAbs - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]; ring
    rw [e, ← Finset.mul_sum]
    have h := hs.sum_le_tsum ((T.filter (fun t => ¬ 0 ≤ t)).image (fun t : ℤ => t.natAbs - 1))
      (fun k _ => pow_nonneg hr0.le k)
    rw [htsum] at h
    exact mul_le_mul_of_nonneg_left h hr0.le
  calc _ ≤ (1 - r)⁻¹ + r * (1 - r)⁻¹ := add_le_add hpos hneg
    _ = (1 + r) / (1 - r) := by field_simp

/-- **Profile summation lemma** (Lemma 7.11). -/
lemma profile_sum {L : Finset ℕ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (F : Finset ℕ) (g : ℕ → ℤ)
    (ε : ℕ → ℝ) (P : ℕ → ℕ → ℕ) (E : ℝ) (hE : 0 ≤ E) (hprof : ∀ i ∈ F, HasProfile L r (ε i) (P i) (g i))
    (hεE : ∀ i ∈ F, ε i ≤ E)
    (hdist : ∀ ℓ ∈ L, ∀ i ∈ F, ∀ j ∈ F, P i ℓ = P j ℓ → i = j)
    (s : ℕ → ℤ) (hs : ∀ i ∈ F, s i = 1 ∨ s i = -1) (ℓ : ℕ) (hℓ : ℓ ∈ L) (n : ℕ) (hn : 1 ≤ n) :
    nrm ((((∑ i ∈ F, s i * g i : ℤ)) : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) ≤ E * ((1 + r) / (1 - r)) := by
  classical
  have e : ((((∑ i ∈ F, s i * g i : ℤ)) : ℝ) / ((ℓ : ℝ) ^ (n ^ 2)))
      = ∑ i ∈ F, (s i : ℝ) * ((g i : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) := by
    push_cast; rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have step1 : nrm (∑ i ∈ F, (s i : ℝ) * ((g i : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))))
      ≤ ∑ i ∈ F, nrm ((g i : ℝ) / ((ℓ : ℝ) ^ (n ^ 2))) := by
    refine (nrm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rcases hs i hi with h | h
    · simp [h]
    · simp [h, nrm_neg]
  have step2 : ∑ i ∈ F, nrm ((g i : ℝ) / ((ℓ : ℝ) ^ (n ^ 2)))
      ≤ ∑ i ∈ F, E * r ^ (((n : ℤ) - P i ℓ).natAbs) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h0 := hprof i hi ℓ hℓ n hn
    have h1 : 0 ≤ r ^ (((n : ℤ) - P i ℓ).natAbs) := pow_nonneg hr0.le _
    calc _ ≤ ε i * r ^ (((n : ℤ) - P i ℓ).natAbs) := h0
      _ ≤ E * r ^ (((n : ℤ) - P i ℓ).natAbs) := by gcongr; exact hεE i hi
  have hinj : Set.InjOn (fun i : ℕ => (n : ℤ) - P i ℓ) (F : Set ℕ) := by
    intro i hi j hj hij
    simp only at hij
    exact hdist ℓ hℓ i hi j hj (by omega)
  have e2 : ∑ i ∈ F, E * r ^ (((n : ℤ) - P i ℓ).natAbs)
      = E * ∑ t ∈ F.image (fun i : ℕ => (n : ℤ) - P i ℓ), r ^ t.natAbs := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = E * ∑ t ∈ F.image (fun i : ℕ => (n : ℤ) - P i ℓ), r ^ t.natAbs := e2
    _ ≤ E * ((1 + r) / (1 - r)) := by gcongr; exact geomZ_le hr0 hr1 _


/-- First-crossing argument: if all partial sums have circle norm at most `1/8`, steps are in `[0, β]`
with `β ≤ 1/8`, then the total is at most `1/8`. -/
lemma sum_le_eighth (b : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : β ≤ 1 / 8)
    (hb0 : ∀ i, i < N → 0 ≤ b i) (hbβ : ∀ i, i < N → b i ≤ β)
    (hnrm : ∀ m, m ≤ N → nrm (∑ i ∈ Finset.range m, b i) ≤ 1 / 8) :
    ∑ i ∈ Finset.range N, b i ≤ 1 / 8 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hex : ∃ m, 1 / 8 < ∑ i ∈ Finset.range m, b i := ⟨N, hcon⟩
  set m := Nat.find hex with hmdef
  have hm1 : 1 / 8 < ∑ i ∈ Finset.range m, b i := Nat.find_spec hex
  have hmN : m ≤ N := Nat.find_min' hex hcon
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0] at hm1; simp at hm1; linarith
  have hprev : ∑ i ∈ Finset.range (m - 1), b i ≤ 1 / 8 := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    push_neg at this; exact this
  have hsplit : ∑ i ∈ Finset.range m, b i = ∑ i ∈ Finset.range (m - 1), b i + b (m - 1) := by
    have h : m = (m - 1) + 1 := by omega
    conv_lhs => rw [h]
    rw [Finset.sum_range_succ]
  have hbm : b (m - 1) ≤ 1 / 8 := (hbβ (m - 1) (by omega)).trans hβ
  have hle : ∑ i ∈ Finset.range m, b i ≤ 1 / 4 := by linarith
  have hnn : 0 ≤ ∑ i ∈ Finset.range m, b i :=
    Finset.sum_nonneg fun i hi => hb0 i (by have := Finset.mem_range.mp hi; omega)
  have := hnrm m hmN
  rw [nrm_eq_abs (by rw [abs_of_nonneg hnn]; linarith), abs_of_nonneg hnn] at this
  linarith

/-- **Uniform profile bound and summability** (Theorem 7.17), finite form:
if `x` has Lipschitz constant `C` and `h₀,…,h_{N-1}` have profiles of sizes `ε_i ≤ 1/(16 C A_r)` with
pairwise distinct centres for each base, then `∑ ‖h_i x‖ / ε_i ≤ 2 C A_r`, `A_r = (1+r)/(1-r)`. -/
theorem profile_summability {L : Finset ℕ} (hL : L.Nonempty) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {x C : ℝ} (hC0 : 0 < C) (hC : ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn (Sc L) k)
    (N : ℕ) (h : ℕ → ℤ) (ε : ℕ → ℝ) (P : ℕ → ℕ → ℕ)
    (hprof : ∀ i < N, HasProfile L r (ε i) (P i) (h i))
    (hdist : ∀ ℓ ∈ L, ∀ i < N, ∀ j < N, P i ℓ = P j ℓ → i = j)
    (hε0 : ∀ i < N, 0 < ε i) (hεs : ∀ i < N, ε i ≤ 1 / (16 * C * ((1 + r) / (1 - r)))) :
    ∑ i ∈ Finset.range N, nrm ((h i : ℝ) * x) / ε i ≤ 2 * C * ((1 + r) / (1 - r)) := by
  classical
  set A : ℝ := (1 + r) / (1 - r) with hA
  have h1r : 0 < 1 - r := by linarith
  have hA1 : 1 ≤ A := by rw [hA, le_div_iff₀ h1r]; linarith
  have hA0 : 0 < A := by linarith
  set η : ℝ := 1 / (8 * C * A) with hηdef
  have hη : 0 < η := by positivity
  have hεη : ∀ i < N, ε i ≤ η / 2 := by
    intro i hi
    have := hεs i hi
    have e : η / 2 = 1 / (16 * C * A) := by rw [hηdef]; field_simp; ring
    rw [e]; exact this
  set t : ℕ → ℕ := fun i => ⌊η / ε i⌋₊ with htdef
  have ht2 : ∀ i < N, η / (2 * ε i) ≤ t i := by
    intro i hi
    have hy : 2 ≤ η / ε i := by rw [le_div_iff₀ (hε0 i hi)]; linarith [hεη i hi]
    have h1 : η / ε i - 1 < t i := by
      have := Nat.lt_floor_add_one (η / ε i)
      simp only [htdef]; linarith
    have e : η / (2 * ε i) = (η / ε i) / 2 := by field_simp
    rw [e]; linarith
  have ht3 : ∀ i < N, (t i : ℝ) * ε i ≤ η := by
    intro i hi
    have := Nat.floor_le (div_nonneg hη.le (hε0 i hi).le : 0 ≤ η / ε i)
    calc (t i : ℝ) * ε i ≤ (η / ε i) * ε i := mul_le_mul_of_nonneg_right this (hε0 i hi).le
      _ = η := by field_simp [(hε0 i hi).ne']
  -- character values
  set a : ℕ → ℝ := fun i => nrm ((h i : ℝ) * x) with hadef
  have ha_le : ∀ i < N, a i ≤ C * ε i := by
    intro i hi
    have h1 := hC (h i)
    have h2 := (hprof i hi).Pn_le hL (hε0 i hi).le hr0.le hr1.le
    calc a i ≤ C * Pn (Sc L) (h i) := h1
      _ ≤ C * ε i := by gcongr
  set b : ℕ → ℝ := fun i => (t i : ℝ) * a i with hbdef
  have hb0 : ∀ i, i < N → 0 ≤ b i := fun i _ => mul_nonneg (Nat.cast_nonneg _) (nrm_nonneg _)
  have hbβ : ∀ i, i < N → b i ≤ 1 / (8 * A) := by
    intro i hi
    calc b i = (t i : ℝ) * a i := rfl
      _ ≤ (t i : ℝ) * (C * ε i) := by gcongr; exact ha_le i hi
      _ = C * ((t i : ℝ) * ε i) := by ring
      _ ≤ C * η := by gcongr; exact ht3 i hi
      _ = 1 / (8 * A) := by rw [hηdef]; field_simp
  -- signs and integer parts
  have hsign : ∀ i : ℕ, ∃ (sg : ℤ) (j : ℤ), (sg = 1 ∨ sg = -1) ∧ (sg : ℝ) * ((h i : ℝ) * x) = a i + j := by
    intro i
    have hr := nrm_eq ((h i : ℝ) * x)
    by_cases hnn : 0 ≤ (h i : ℝ) * x - round ((h i : ℝ) * x)
    · refine ⟨1, round ((h i : ℝ) * x), Or.inl rfl, ?_⟩
      have ha' : a i = (h i : ℝ) * x - round ((h i : ℝ) * x) := by
        rw [hadef]; simp only; rw [hr, abs_of_nonneg hnn]
      rw [ha']; push_cast; ring
    · push_neg at hnn
      refine ⟨-1, -(round ((h i : ℝ) * x)), Or.inr rfl, ?_⟩
      have ha' : a i = -((h i : ℝ) * x - round ((h i : ℝ) * x)) := by
        rw [hadef]; simp only; rw [hr, abs_of_neg hnn]
      rw [ha']; push_cast; ring
  choose s j hs hsj using hsign
  -- prefix bounds
  have hpre : ∀ m, m ≤ N → nrm (∑ i ∈ Finset.range m, b i) ≤ 1 / 8 := by
    intro m hm
    set K : ℤ := ∑ i ∈ Finset.range m, s i * ((t i : ℤ) * h i) with hK
    have hKx : (K : ℝ) * x = ∑ i ∈ Finset.range m, b i + ((∑ i ∈ Finset.range m, (t i : ℤ) * j i : ℤ) : ℝ) := by
      rw [hK]; push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hsj i
      calc (s i : ℝ) * ((t i : ℝ) * (h i : ℝ)) * x = (t i : ℝ) * ((s i : ℝ) * ((h i : ℝ) * x)) := by ring
        _ = (t i : ℝ) * (a i + j i) := by rw [this]
        _ = b i + (t i : ℝ) * j i := by simp only [hbdef]; ring
    have hPK : Pn (Sc L) K ≤ η * A := by
      apply MixedPrime.Pn_le (Sc_nonempty hL)
      rintro q ⟨ℓ, hℓ, n, hn, rfl⟩
      rw [Nat.cast_pow]
      refine profile_sum (L := L) hr0 hr1 (Finset.range m) (fun i => (t i : ℤ) * h i)
        (fun i => (t i : ℝ) * ε i) P η hη.le ?_ ?_ ?_ s ?_ ℓ hℓ n hn
      · intro i hi
        exact (hprof i (by have := Finset.mem_range.mp hi; omega)).nsmul (t i)
      · intro i hi
        exact ht3 i (by have := Finset.mem_range.mp hi; omega)
      · intro ℓ' hℓ' i hi j' hj' hij
        exact hdist ℓ' hℓ' i (by have := Finset.mem_range.mp hi; omega) j'
          (by have := Finset.mem_range.mp hj'; omega) hij
      · intro i hi; exact hs i
    have hup : nrm ((K : ℝ) * x) ≤ 1 / 8 := by
      calc nrm ((K : ℝ) * x) ≤ C * Pn (Sc L) K := hC K
        _ ≤ C * (η * A) := by gcongr
        _ = 1 / 8 := by rw [hηdef]; field_simp
    rw [hKx, nrm_add_int] at hup
    exact hup
  have hsum : ∑ i ∈ Finset.range N, b i ≤ 1 / 8 :=
    sum_le_eighth b N (1 / (8 * A)) (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
      hb0 hbβ hpre
  -- conclusion
  have hterm : ∀ i < N, a i / ε i ≤ (2 / η) * b i := by
    intro i hi
    have hε := hε0 i hi
    have ha0 : 0 ≤ a i := nrm_nonneg _
    have h3 : η / (2 * ε i) * a i ≤ (t i : ℝ) * a i := by gcongr; exact ht2 i hi
    have e : (2 / η) * ((η / (2 * ε i)) * a i) = a i / ε i := by field_simp
    calc a i / ε i = (2 / η) * ((η / (2 * ε i)) * a i) := e.symm
      _ ≤ (2 / η) * ((t i : ℝ) * a i) := by gcongr
      _ = (2 / η) * b i := rfl
  calc ∑ i ∈ Finset.range N, nrm ((h i : ℝ) * x) / ε i
      = ∑ i ∈ Finset.range N, a i / ε i := rfl
    _ ≤ ∑ i ∈ Finset.range N, (2 / η) * b i :=
        Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi)
    _ = (2 / η) * ∑ i ∈ Finset.range N, b i := by rw [← Finset.mul_sum]
    _ ≤ (2 / η) * (1 / 8) := by gcongr
    _ = 2 * C * A := by rw [hηdef]; field_simp


/-- **Profile test 1** (Corollary 7.18, first part): a separated profile sequence with `ε_i → 0` and a
divergent series `∑ ‖h_i x‖ / ε_i` excludes every Lipschitz constant. -/
theorem not_lipschitz_of_divergent {L : Finset ℕ} (hL : L.Nonempty) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {x : ℝ} (h : ℕ → ℤ) (ε : ℕ → ℝ) (P : ℕ → ℕ → ℕ)
    (hprof : ∀ i, HasProfile L r (ε i) (P i) (h i))
    (hdist : ∀ ℓ ∈ L, ∀ i j, P i ℓ = P j ℓ → i = j)
    (hε0 : ∀ i, 0 < ε i) (hlim : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hdiv : ¬ Summable fun i => nrm ((h i : ℝ) * x) / ε i) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn (Sc L) k := by
  rintro ⟨C, hC0, hC⟩
  set A : ℝ := (1 + r) / (1 - r) with hA
  have h1r : 0 < 1 - r := by linarith
  have hA1 : 1 ≤ A := by rw [hA, le_div_iff₀ h1r]; linarith
  have hbd : 0 < 1 / (16 * C * A) := by positivity
  obtain ⟨i0, hi0⟩ := Metric.tendsto_atTop.mp hlim (1 / (16 * C * A)) hbd
  have hsm : Summable fun i => nrm ((h (i + i0) : ℝ) * x) / ε (i + i0) := by
    apply summable_of_sum_range_le (c := 2 * C * A)
    · intro i; exact div_nonneg (nrm_nonneg _) (hε0 _).le
    · intro N
      refine profile_summability hL hr0 hr1 hC0 hC N (fun i => h (i + i0)) (fun i => ε (i + i0))
        (fun i => P (i + i0)) (fun i _ => hprof _) ?_ (fun i _ => hε0 _) ?_
      · intro ℓ hℓ i _ j _ hij
        have := hdist ℓ hℓ _ _ hij
        omega
      · intro i _
        have := hi0 (i + i0) (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_pos (hε0 _)] at this
        exact this.le
  exact hdiv ((summable_nat_add_iff i0).mp hsm)

/-- **Profile test 2** (Corollary 7.18, second part): if for arbitrarily small `ε` there is an infinite
separated sequence of `ε`-profile integers with `∑ ‖h_i x‖ = ∞`, then no Lipschitz constant exists. -/
theorem not_lipschitz_of_fixed_scale {L : Finset ℕ} (hL : L.Nonempty) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {x : ℝ}
    (hex : ∀ ε : ℝ, 0 < ε → ∃ (h : ℕ → ℤ) (P : ℕ → ℕ → ℕ),
      (∀ i, HasProfile L r ε (P i) (h i)) ∧ (∀ ℓ ∈ L, ∀ i j, P i ℓ = P j ℓ → i = j) ∧
      ¬ Summable fun i => nrm ((h i : ℝ) * x)) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn (Sc L) k := by
  rintro ⟨C, hC0, hC⟩
  set A : ℝ := (1 + r) / (1 - r) with hA
  have h1r : 0 < 1 - r := by linarith
  have hA1 : 1 ≤ A := by rw [hA, le_div_iff₀ h1r]; linarith
  set ε : ℝ := 1 / (16 * C * A) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨h, P, hprof, hdist, hdiv⟩ := hex ε hε0
  apply hdiv
  apply summable_of_sum_range_le (c := 2 * C * A * ε)
  · intro i; exact nrm_nonneg _
  · intro N
    have := profile_summability hL hr0 hr1 hC0 hC N h (fun _ => ε) P (fun i _ => hprof i)
      (fun ℓ hℓ i _ j _ hij => hdist ℓ hℓ i j hij) (fun _ _ => hε0) (fun _ _ => le_rfl)
    rw [← Finset.sum_div, div_le_iff₀ hε0] at this
    exact this

end MixedPrime
end LeanCheck
