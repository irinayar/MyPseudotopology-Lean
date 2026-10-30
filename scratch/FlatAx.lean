import LeanCheck.MixedPrimeBasics

/-!
# TVGaddmore_v17: flatness of continuous characters (Theorem "flatness")

Setting: `S` is an arbitrary infinite set of positive integers ("scales"), `Pn S` the associated pseudo-norm,
`x : ℝ` a parameter with a Lipschitz bound `nrm (k x) ≤ C * Pn S k`.
Conclusion: for every `κ > 0` there is `ε > 0` with `nrm (k x) < κ * Pn S k` whenever `k ≠ 0`, `Pn S k < ε`
(the little-o form of continuity).  The proof is the block construction of the paper.
-/

namespace LeanCheck
namespace MixedPrime

/-- Geometric sums: `∑_{i<m} (1/2)^(i+1) ≤ 1`. -/
lemma geom_half_le (m : ℕ) : ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
  have : ∀ m : ℕ, ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [this]
  have : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
  linarith

/-- Data of `M` block vectors: cutoffs `lo i < hi i = lo (i+1)`, exact vanishing below `lo`,
bound `η` inside the block, tail `η / 2^(i+1)` above `hi`, signs and character values. -/
def Good (S : Set ℕ) (x η c : ℝ) (M : ℕ) (v s : ℕ → ℤ) (b lo hi : ℕ → ℝ) : Prop :=
  lo 0 = 0 ∧ (∀ i, i < M → lo (i + 1) = hi i) ∧ (∀ i, i < M → lo i < hi i) ∧
  ∀ i, i < M →
    (∀ q ∈ S, (q : ℝ) ≤ lo i → nrm ((v i : ℝ) / q) = 0) ∧
    (∀ q ∈ S, lo i < q → (q : ℝ) ≤ hi i → nrm ((v i : ℝ) / q) ≤ η) ∧
    (∀ q ∈ S, hi i < q → nrm ((v i : ℝ) / q) ≤ η / 2 ^ (i + 1)) ∧
    (s i = 1 ∨ s i = -1) ∧ c ≤ b i ∧ b i ≤ 1 / 16 ∧
    ∃ j : ℤ, ((s i : ℝ) * (v i : ℝ)) * x = b i + j

lemma Good.lo_mono {S : Set ℕ} {x η c : ℝ} {M : ℕ} {v s : ℕ → ℤ} {b lo hi : ℕ → ℝ}
    (h : Good S x η c M v s b lo hi) : ∀ i j, i ≤ j → j ≤ M → lo i ≤ lo j := by
  obtain ⟨_, h1, h2, _⟩ := h
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    have := ih (by omega)
    have h3 := h2 j (by omega)
    rw [h1 j (by omega)]
    linarith

/-- Signed sums of the block vectors have `Pn ≤ 2η` coordinatewise. -/
lemma Good.sum_bound {S : Set ℕ} {x η c : ℝ} {M : ℕ} {v s : ℕ → ℤ} {b lo hi : ℕ → ℝ}
    (hη : 0 ≤ η) (h : Good S x η c M v s b lo hi) (m : ℕ) (hm : m ≤ M) (q : ℕ) (hq : q ∈ S) :
    nrm ((((∑ i ∈ Finset.range m, s i * v i : ℤ)) : ℝ) / q) ≤ 2 * η := by
  classical
  have hmono := h.lo_mono
  obtain ⟨_, h1, h2, hv⟩ := h
  have e : ((((∑ i ∈ Finset.range m, s i * v i : ℤ)) : ℝ) / q)
      = ∑ i ∈ Finset.range m, (((s i : ℝ) * ((v i : ℝ) / q))) := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  have step1 : nrm (∑ i ∈ Finset.range m, (((s i : ℝ) * ((v i : ℝ) / q))))
      ≤ ∑ i ∈ Finset.range m, nrm ((v i : ℝ) / q) := by
    refine (nrm_sum_le _ _).trans (Finset.sum_le_sum fun i hmem => ?_)
    obtain ⟨_, _, _, hs, _⟩ := hv i (by have := Finset.mem_range.mp hmem; omega)
    rcases hs with hs | hs
    · simp [hs]
    · simp [hs, nrm_neg]
  have step2 : ∀ i ∈ Finset.range m, nrm ((v i : ℝ) / q)
      ≤ (if lo i < q ∧ (q : ℝ) ≤ hi i then η else 0) + η * (1 / 2) ^ (i + 1) := by
    intro i hmem
    have hi' : i < M := by have := Finset.mem_range.mp hmem; omega
    obtain ⟨ha, hb, hc, _⟩ := hv i hi'
    have hpow : 0 ≤ η * (1 / 2 : ℝ) ^ (i + 1) := by positivity
    by_cases hlo : (q : ℝ) ≤ lo i
    · rw [ha q hq hlo]
      split_ifs <;> linarith
    · push_neg at hlo
      by_cases hhi : (q : ℝ) ≤ hi i
      · rw [if_pos ⟨hlo, hhi⟩]
        have := hb q hq hlo hhi
        linarith
      · push_neg at hhi
        rw [if_neg (by intro hh; linarith [hh.2])]
        have := hc q hq hhi
        have e2 : η / 2 ^ (i + 1) = η * (1 / 2) ^ (i + 1) := by
          rw [one_div, inv_pow]; field_simp
        linarith
  have step3 : ∑ i ∈ Finset.range m, nrm ((v i : ℝ) / q)
      ≤ ∑ i ∈ Finset.range m, ((if lo i < q ∧ (q : ℝ) ≤ hi i then η else 0) + η * (1 / 2) ^ (i + 1)) :=
    Finset.sum_le_sum step2
  rw [Finset.sum_add_distrib] at step3
  have card1 : (Finset.filter (fun i => lo i < q ∧ (q : ℝ) ≤ hi i) (Finset.range m)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hab
    · have h3 := hmono (a + 1) b hab (by omega)
      have h4 := h1 a (by omega)
      linarith [ha.2.2, hb.2.1]
    · have h3 := hmono (b + 1) a hab (by omega)
      have h4 := h1 b (by omega)
      linarith [hb.2.2, ha.2.1]
  have sumite : ∑ i ∈ Finset.range m, (if lo i < q ∧ (q : ℝ) ≤ hi i then η else 0)
      = η * (Finset.filter (fun i => lo i < q ∧ (q : ℝ) ≤ hi i) (Finset.range m)).card := by
    rw [← Finset.sum_filter]; simp [mul_comm]
  have hgeo : ∑ i ∈ Finset.range m, η * (1 / 2 : ℝ) ^ (i + 1) ≤ η := by
    rw [← Finset.mul_sum]
    have := geom_half_le m
    nlinarith
  have hcard : η * ((Finset.filter (fun i => lo i < q ∧ (q : ℝ) ≤ hi i) (Finset.range m)).card : ℝ) ≤ η := by
    have : ((Finset.filter (fun i => lo i < q ∧ (q : ℝ) ≤ hi i) (Finset.range m)).card : ℝ) ≤ 1 := by
      exact_mod_cast card1
    nlinarith
  rw [sumite] at step3
  linarith

/-- The inductive construction of block configurations of every length. -/
lemma exists_good {S : Set ℕ} (hpos : ∀ q ∈ S, 0 < q) (hinf : S.Infinite) {x C κ : ℝ} (hC0 : 0 < C)
    (hC : ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn S k) (hκ : 0 < κ)
    (hbad : ∀ ε > 0, ∃ k : ℤ, k ≠ 0 ∧ Pn S k < ε ∧ κ * Pn S k ≤ nrm ((k : ℝ) * x)) (M : ℕ) :
    ∃ v s : ℕ → ℤ, ∃ b lo hi : ℕ → ℝ,
      Good S x (1 / (16 * C)) (κ * (1 / (16 * C)) / 2) M v s b lo hi := by
  have hSne : S.Nonempty := hinf.nonempty
  set η : ℝ := 1 / (16 * C) with hηdef
  have hη : 0 < η := by positivity
  set c : ℝ := κ * η / 2 with hcdef
  induction M with
  | zero =>
    refine ⟨fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
    exact ⟨rfl, by intro i hi; omega, by intro i hi; omega, by intro i hi; omega⟩
  | succ M ih =>
    obtain ⟨v, s, b, lo, hi, hG⟩ := ih
    have hG' := hG
    obtain ⟨hlo0, hlohi, hlt, hv⟩ := hG
    -- the lower cutoff of the new vector
    set L : ℝ := lo M with hL
    have hL0 : 0 ≤ L := by
      have := hG'.lo_mono 0 M (Nat.zero_le _) le_rfl
      rw [hlo0] at this; exact this
    have hε : 0 < min (η / 2) (1 / (L + 1)) := lt_min (by positivity) (by positivity)
    obtain ⟨k, hk0, hkP, hkb⟩ := hbad _ hε
    have hp : 0 < Pn S k := Pn_pos hpos hinf hk0
    set p := Pn S k with hpdef
    have hpη : p < η / 2 := lt_of_lt_of_le hkP (min_le_left _ _)
    have hpL : p < 1 / (L + 1) := lt_of_lt_of_le hkP (min_le_right _ _)
    -- scaling factor
    set t : ℕ := ⌊η / p⌋₊ with htdef
    have hy2 : 2 ≤ η / p := by
      rw [le_div_iff₀ hp]; linarith
    have ht1 : η / p - 1 < t := by
      have := Nat.lt_floor_add_one (η / p); linarith
    have ht2 : η / (2 * p) ≤ t := by
      have : η / (2 * p) = (η / p) / 2 := by field_simp
      rw [this]; linarith
    have ht3 : (t : ℝ) * p ≤ η := by
      have := Nat.floor_le (div_nonneg hη.le hp.le : 0 ≤ η / p)
      calc (t : ℝ) * p ≤ (η / p) * p := by gcongr
        _ = η := by field_simp
    -- new vector
    set vnew : ℤ := (t : ℤ) * k with hvnew
    have hPv : Pn S vnew ≤ η := by
      have := Pn_nsmul_le hSne t k
      linarith
    -- vanishing below L
    have hvan : ∀ q ∈ S, (q : ℝ) ≤ L → nrm ((vnew : ℝ) / q) = 0 := by
      intro q hq hqL
      have hq0 := hpos q hq
      have hlt1 : nrm ((k : ℝ) / q) < 1 / q := by
        have h1 := le_Pn hq k
        have h2 : (1 : ℝ) / (L + 1) < 1 / q := by
          have : (0 : ℝ) < q := by exact_mod_cast hq0
          apply one_div_lt_one_div_of_lt this; linarith
        linarith
      obtain ⟨r, hr⟩ := dvd_of_nrm_lt k q hq0 hlt1
      have : (vnew : ℝ) / q = ((t : ℤ) * r : ℤ) := by
        have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
        rw [hvnew, hr]; push_cast; field_simp
      rw [this]; exact nrm_int _
    -- choose the new upper cutoff
    set H : ℝ := max (L + 1) (|(vnew : ℝ)| * 2 ^ (M + 1) / η) with hH
    have hHL : L < H := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have htail : ∀ q ∈ S, H < q → nrm ((vnew : ℝ) / q) ≤ η / 2 ^ (M + 1) := by
      intro q hq hqH
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hpos q hq
      refine (nrm_le_abs _).trans ?_
      rw [abs_div, abs_of_pos hq0, div_le_div_iff₀ hq0 (by positivity)]
      have h1 : |(vnew : ℝ)| * 2 ^ (M + 1) / η < q := lt_of_le_of_lt (le_max_right _ _) hqH
      rw [div_lt_iff₀ hη] at h1
      linarith
    -- character value
    set a := nrm ((k : ℝ) * x) with hadef
    have hap : a ≤ C * p := hC k
    have hakp : κ * p ≤ a := hkb
    set bnew : ℝ := (t : ℝ) * a with hbnew
    have hb_le : bnew ≤ 1 / 16 := by
      calc bnew = t * a := rfl
        _ ≤ t * (C * p) := by gcongr
        _ = C * (t * p) := by ring
        _ ≤ C * η := by gcongr
        _ = 1 / 16 := by rw [hηdef]; field_simp
    have hb_ge : c ≤ bnew := by
      calc c = κ * η / 2 := rfl
        _ = κ * (η / (2 * p)) * p := by field_simp
        _ ≤ κ * t * p := by gcongr
        _ = t * (κ * p) := by ring
        _ ≤ t * a := by gcongr
    -- sign and integer part
    have hsign : ∃ (sg : ℤ) (j : ℤ), (sg = 1 ∨ sg = -1) ∧ ((sg : ℝ) * (vnew : ℝ)) * x = bnew + j := by
      have hr := nrm_eq ((k : ℝ) * x)
      by_cases hnn : 0 ≤ (k : ℝ) * x - round ((k : ℝ) * x)
      · refine ⟨1, (t : ℤ) * round ((k : ℝ) * x), Or.inl rfl, ?_⟩
        have ha' : a = (k : ℝ) * x - round ((k : ℝ) * x) := by
          rw [hadef, hr, abs_of_nonneg hnn]
        rw [hbnew, ha', hvnew]; push_cast; ring
      · push_neg at hnn
        refine ⟨-1, -((t : ℤ) * round ((k : ℝ) * x)), Or.inr rfl, ?_⟩
        have ha' : a = -((k : ℝ) * x - round ((k : ℝ) * x)) := by
          rw [hadef, hr, abs_of_neg hnn]
        rw [hbnew, ha', hvnew]; push_cast; ring
    obtain ⟨sg, jj, hsg, hjj⟩ := hsign
    -- assemble the new configuration
    refine ⟨Function.update v M vnew, Function.update s M sg, Function.update b M bnew,
      Function.update lo (M + 1) H, Function.update hi M H, ?_⟩
    have hloM : ∀ i, i ≤ M → Function.update lo (M + 1) H i = lo i := by
      intro i hi'; exact Function.update_of_ne (by omega) _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hloM 0 (Nat.zero_le _)]; exact hlo0
    · intro i hi'
      by_cases hiM : i = M
      · rw [hiM]; simp
      · have hi'' : i < M := by omega
        rw [hloM (i + 1) (by omega), Function.update_of_ne hiM]
        exact hlohi i hi''
    · intro i hi'
      by_cases hiM : i = M
      · rw [hiM, hloM M le_rfl]; simpa using hHL
      · have hi'' : i < M := by omega
        rw [hloM i (by omega), Function.update_of_ne hiM]
        exact hlt i hi''
    · intro i hi'
      by_cases hiM : i = M
      · rw [hiM]
        simp only [Function.update_self]
        rw [hloM M le_rfl]
        refine ⟨hvan, ?_, htail, hsg, hb_ge, hb_le, jj, ?_⟩
        · intro q hq h1 h2
          exact (le_Pn hq vnew).trans hPv
        · exact hjj
      · have hi'' : i < M := by omega
        simp only [Function.update_of_ne hiM, hloM i (by omega)]
        exact hv i hi''

end MixedPrime
end LeanCheck

namespace LeanCheck
namespace MixedPrime

/-- **Flatness of continuous characters** (TVGaddmore_v17, Theorem "flatness", necessity direction).
If `x` satisfies the Lipschitz bound `‖k x‖ ≤ C · P(k)` for all `k`, then `‖k x‖ = o(P(k))` as `P(k) → 0`.
Here the scale set `S` is an arbitrary infinite set of positive integers. -/
theorem flatness_necessity {S : Set ℕ} (hpos : ∀ q ∈ S, 0 < q) (hinf : S.Infinite) {x C : ℝ}
    (hC0 : 0 < C) (hC : ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn S k) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∀ k : ℤ, k ≠ 0 → Pn S k < ε → nrm ((k : ℝ) * x) < κ * Pn S k := by
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ ε > 0, ∃ k : ℤ, k ≠ 0 ∧ Pn S k < ε ∧ κ * Pn S k ≤ nrm ((k : ℝ) * x) := hcon
  have hSne : S.Nonempty := hinf.nonempty
  set η : ℝ := 1 / (16 * C) with hηdef
  have hη : 0 < η := by positivity
  set c : ℝ := κ * η / 2 with hcdef
  have hc : 0 < c := by positivity
  -- number of vectors
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / 8 < (M : ℝ) * c := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / (8 * c))
    refine ⟨M, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hM
    linarith
  obtain ⟨v, s, b, lo, hi, hG⟩ := exists_good hpos hinf hC0 hC hκ hbad M
  have hGc := hG
  obtain ⟨_, _, _, hv⟩ := hG
  -- partial sums of b
  have hbge : ∀ i, i < M → c ≤ b i := fun i hi => (hv i hi).2.2.2.2.1
  have hble : ∀ i, i < M → b i ≤ 1 / 16 := fun i hi => (hv i hi).2.2.2.2.2.1
  have hsumM : 1 / 8 < ∑ i ∈ Finset.range M, b i := by
    have : (M : ℝ) * c ≤ ∑ i ∈ Finset.range M, b i := by
      have := Finset.card_nsmul_le_sum (Finset.range M) b c (fun i hi => hbge i (Finset.mem_range.mp hi))
      simpa using this
    linarith
  classical
  have hex : ∃ m, 1 / 8 < ∑ i ∈ Finset.range m, b i := ⟨M, hsumM⟩
  set m := Nat.find hex with hmdef
  have hm1 : 1 / 8 < ∑ i ∈ Finset.range m, b i := Nat.find_spec hex
  have hmM : m ≤ M := Nat.find_min' hex hsumM
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0] at hm1; simp at hm1; linarith
  have hprev : ∑ i ∈ Finset.range (m - 1), b i ≤ 1 / 8 := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    push_neg at this; exact this
  have hmsplit : ∑ i ∈ Finset.range m, b i = ∑ i ∈ Finset.range (m - 1), b i + b (m - 1) := by
    have h : m = (m - 1) + 1 := by omega
    conv_lhs => rw [h]
    rw [Finset.sum_range_succ]
  have hbm : b (m - 1) ≤ 1 / 16 := hble (m - 1) (by omega)
  have hBle : ∑ i ∈ Finset.range m, b i ≤ 3 / 16 := by linarith
  have hBnn : 0 ≤ ∑ i ∈ Finset.range m, b i :=
    Finset.sum_nonneg fun i hi => le_trans hc.le (hbge i (by have := Finset.mem_range.mp hi; omega))
  -- the integer combination
  set K : ℤ := ∑ i ∈ Finset.range m, s i * v i with hK
  have hKx : ∃ N : ℤ, (K : ℝ) * x = ∑ i ∈ Finset.range m, b i + N := by
    have : ∀ n, n ≤ M → ∃ N : ℤ, ((∑ i ∈ Finset.range n, s i * v i : ℤ) : ℝ) * x
        = ∑ i ∈ Finset.range n, b i + N := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, by simp⟩
      | succ n ih =>
        intro hn
        obtain ⟨N, hN⟩ := ih (by omega)
        obtain ⟨j, hj⟩ := (hv n (by omega)).2.2.2.2.2.2
        refine ⟨N + j, ?_⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast at hN hj ⊢
        linarith
    exact this m hmM
  obtain ⟨N, hN⟩ := hKx
  have hnrmK : nrm ((K : ℝ) * x) = ∑ i ∈ Finset.range m, b i := by
    rw [hN, nrm_add_int, nrm_eq_abs (by rw [abs_of_nonneg hBnn]; linarith), abs_of_nonneg hBnn]
  have hPK : Pn S K ≤ 2 * η := by
    apply Pn_le hSne
    intro q hq
    exact hGc.sum_bound hη.le m hmM q hq
  have hup : nrm ((K : ℝ) * x) ≤ 1 / 8 := by
    calc nrm ((K : ℝ) * x) ≤ C * Pn S K := hC K
      _ ≤ C * (2 * η) := by gcongr
      _ = 1 / 8 := by rw [hηdef]; field_simp; ring
  linarith

end MixedPrime
end LeanCheck

#print axioms LeanCheck.MixedPrime.flatness_necessity
#print axioms LeanCheck.MixedPrime.Good.sum_bound
#print axioms LeanCheck.MixedPrime.exists_good
