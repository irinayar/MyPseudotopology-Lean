import Mathlib
import LeanCheck.TwoPrimesEffective

/-!
# Only a density of differences is needed

Let `W` be a set of at least `Y/K` integers, each a difference `a - b` with `|a|, |b| ≤ Y`, `a` small
for the base `q` and `b` small for the base `p`, at the radius `1/D`.  Then every target `t` with
`|t| + G ≤ Y` has a witness `|k| ≤ 35 K Y` at the radius `35 K / D`; here `G` is the larger of two
powers `q^(m^2)`, `p^(n^2)` which are themselves small at the radius `1/D`.

The proof is a covering of `[-Y, Y]` by at most `7K` translates, followed by a walk with the two
steps `q^(m^2)`, `p^(n^2)` from which all loops through one translate are cut out.

* `witness_of_support`: the statement above.
* `witness_of_energy`: the same from a bound for the collision energy.
* `support_of_range`: conversely, a range of witnessed targets forces such a set.
-/

namespace TwoPrimesSupport

open Finset TwoPrimesEffective

lemma Small.mono {p : ℕ} {s s' : ℝ} {k : ℤ} (h : Small p s k) (hs : s ≤ s') : Small p s' k :=
  fun n => lt_of_lt_of_le (h n) hs

lemma small_zero {p : ℕ} {s : ℝ} (hs : 0 < s) : Small p s 0 := by
  intro n; simpa using hs

/-- A power `ℓ^(m^2)` is small once `ℓ^(2m+1)` exceeds `D`. -/
lemma small_pow {l D m : ℕ} (hl : 2 ≤ l) (hD : 1 ≤ D) (hm : D < l ^ (2 * m + 1)) :
    Small l (1 / D) ((l : ℤ) ^ (m ^ 2)) := by
  intro j
  have hl' : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hcast : (((l : ℤ) ^ (m ^ 2) : ℤ) : ℝ) = (l : ℝ) ^ (m ^ 2) := by push_cast; rfl
  rw [hcast]
  rcases le_or_gt j m with h | h
  · have hle : j ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left h 2
    have e : (l : ℝ) ^ (m ^ 2) / (l : ℝ) ^ (j ^ 2) = ((l ^ (m ^ 2 - j ^ 2) : ℕ) : ℝ) := by
      rw [Nat.cast_pow, pow_sub₀ _ hl'.ne' hle, div_eq_mul_inv]
    rw [e, round_natCast]
    simpa using hD'
  · have h2 : m ^ 2 + (2 * m + 1) ≤ j ^ 2 := by
      have : (m + 1) ^ 2 ≤ j ^ 2 := Nat.pow_le_pow_left h 2
      nlinarith
    set v : ℝ := (l : ℝ) ^ (m ^ 2) / (l : ℝ) ^ (j ^ 2) with hv
    have hv0 : 0 ≤ v := by positivity
    have hvD : v < 1 / D := by
      rw [hv, div_lt_div_iff₀ (pow_pos hl' _) hD', one_mul]
      have h3 : (D : ℝ) < (l : ℝ) ^ (2 * m + 1) := by exact_mod_cast hm
      have h4 : (l : ℝ) ^ (m ^ 2) * D < (l : ℝ) ^ (m ^ 2) * (l : ℝ) ^ (2 * m + 1) :=
        mul_lt_mul_of_pos_left h3 (pow_pos hl' _)
      rw [← pow_add] at h4
      exact lt_of_lt_of_le h4 (pow_le_pow_right₀ hl1 h2)
    refine lt_of_le_of_lt (round_le v 0) ?_
    simpa [abs_of_nonneg hv0] using hvD

/-- A witness of target `x` with radius `c/D` and height `h`. -/
def Wit (p q D : ℕ) (c : ℕ) (h : ℕ) (x : ℤ) : Prop :=
  ∃ k : ℤ, |k| ≤ (h : ℤ) ∧ Small q (c / D) k ∧ Small p (c / D) (k - x)

lemma Wit.add {p q D c c' h h' : ℕ} {x y : ℤ} (a : Wit p q D c h x) (b : Wit p q D c' h' y) :
    Wit p q D (c + c') (h + h') (x + y) := by
  obtain ⟨k, k1, k2, k3⟩ := a
  obtain ⟨l, l1, l2, l3⟩ := b
  have e : ((c + c' : ℕ) : ℝ) / D = c / D + c' / D := by push_cast; ring
  refine ⟨k + l, ?_, ?_, ?_⟩
  · have := abs_add_le k l
    push_cast; omega
  · rw [e]; exact k2.add l2
  · rw [e, show k + l - (x + y) = (k - x) + (l - y) by ring]
    exact k3.add l3

lemma Wit.neg {p q D c h : ℕ} {x : ℤ} (a : Wit p q D c h x) : Wit p q D c h (-x) := by
  obtain ⟨k, k1, k2, k3⟩ := a
  refine ⟨-k, by rwa [abs_neg], k2.neg, ?_⟩
  rw [show -k - -x = -(k - x) by ring]
  exact k3.neg

lemma Wit.sub {p q D c c' h h' : ℕ} {x y : ℤ} (a : Wit p q D c h x) (b : Wit p q D c' h' y) :
    Wit p q D (c + c') (h + h') (x - y) := by
  rw [sub_eq_add_neg]; exact a.add b.neg

lemma Wit.mono {p q D c c' h h' : ℕ} {x : ℤ} (a : Wit p q D c h x) (hc : c ≤ c') (hh : h ≤ h') :
    Wit p q D c' h' x := by
  obtain ⟨k, k1, k2, k3⟩ := a
  have e : (c : ℝ) / D ≤ c' / D :=
    div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
  exact ⟨k, le_trans k1 (by exact_mod_cast hh), Small.mono k2 e, Small.mono k3 e⟩

/-- A walk from `c` to `x` with steps `±g₁`, `±g₂` which stays in `[lo, hi]`. -/
lemma walk {g1 g2 : ℤ} (h1 : 0 < g1) (h2 : 0 < g2) {x lo hi : ℤ}
    (hlo : lo ≤ x - g1) (hlo' : lo ≤ x - g2) (hhi : x + g1 ≤ hi) (hhi' : x + g2 ≤ hi) :
    ∀ (M : ℕ) (α β c : ℤ), α.natAbs + β.natAbs = M → x - c = α * g1 + β * g2 → lo ≤ c → c ≤ hi →
      ∃ N : ℕ, ∃ f : ℕ → ℤ, f 0 = c ∧ f N = x ∧ (∀ i ≤ N, lo ≤ f i ∧ f i ≤ hi) ∧
        (∀ i < N, f (i + 1) - f i = g1 ∨ f (i + 1) - f i = -g1
          ∨ f (i + 1) - f i = g2 ∨ f (i + 1) - f i = -g2) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro α β c hM hx hcl hch
    -- prepend one step
    have step : ∀ (c' α' β' : ℤ), α'.natAbs + β'.natAbs < M → x - c' = α' * g1 + β' * g2 →
        lo ≤ c' → c' ≤ hi → (c' - c = g1 ∨ c' - c = -g1 ∨ c' - c = g2 ∨ c' - c = -g2) →
        ∃ N : ℕ, ∃ f : ℕ → ℤ, f 0 = c ∧ f N = x ∧ (∀ i ≤ N, lo ≤ f i ∧ f i ≤ hi) ∧
          (∀ i < N, f (i + 1) - f i = g1 ∨ f (i + 1) - f i = -g1
            ∨ f (i + 1) - f i = g2 ∨ f (i + 1) - f i = -g2) := by
      intro c' α' β' hlt hx' hl hh hs
      obtain ⟨N, f, f0, fN, fb, fs⟩ := ih _ hlt α' β' c' rfl hx' hl hh
      refine ⟨N + 1, fun i => Nat.casesOn i c f, rfl, fN, ?_, ?_⟩
      · intro i hi'
        cases i with
        | zero => exact ⟨hcl, hch⟩
        | succ i => exact fb i (by omega)
      · intro i hi'
        cases i with
        | zero =>
          show f 0 - c = g1 ∨ f 0 - c = -g1 ∨ f 0 - c = g2 ∨ f 0 - c = -g2
          rw [f0]; exact hs
        | succ i => exact fs i (by omega)
    by_cases h0 : α = 0 ∧ β = 0
    · have hc : c = x := by
        rw [h0.1, h0.2] at hx; omega
      refine ⟨0, fun _ => c, rfl, hc, fun _ _ => ⟨hcl, hch⟩, fun i hi' => absurd hi' (by omega)⟩
    rcases le_or_gt c x with hcx | hcx
    · have hpos : 0 < α ∨ 0 < β := by
        by_contra hcon
        rw [not_or, not_lt, not_lt] at hcon
        have a := mul_nonpos_of_nonpos_of_nonneg hcon.1 h1.le
        have b := mul_nonpos_of_nonpos_of_nonneg hcon.2 h2.le
        have a0 : α * g1 = 0 := by omega
        have b0 : β * g2 = 0 := by omega
        rcases mul_eq_zero.mp a0 with hα | hg
        · rcases mul_eq_zero.mp b0 with hβ | hg
          · exact h0 ⟨hα, hβ⟩
          · omega
        · omega
      rcases hpos with hα | hβ
      · refine step (c + g1) (α - 1) β (by omega) ?_ (by omega) (by omega) (Or.inl (by ring))
        rw [sub_mul, one_mul]; omega
      · refine step (c + g2) α (β - 1) (by omega) ?_ (by omega) (by omega)
          (Or.inr (Or.inr (Or.inl (by ring))))
        rw [sub_mul, one_mul]; omega
    · have hneg : α < 0 ∨ β < 0 := by
        by_contra hcon
        rw [not_or, not_lt, not_lt] at hcon
        have a := mul_nonneg hcon.1 h1.le
        have b := mul_nonneg hcon.2 h2.le
        omega
      rcases hneg with hα | hβ
      · refine step (c - g1) (α + 1) β (by omega) ?_ (by omega) (by omega)
          (Or.inr (Or.inl (by ring)))
        rw [add_mul, one_mul]; omega
      · refine step (c - g2) α (β + 1) (by omega) ?_ (by omega) (by omega)
          (Or.inr (Or.inr (Or.inr (by ring))))
        rw [add_mul, one_mul]; omega

/-- **Only a density of differences is needed.** -/
theorem witness_of_support {p q D Y : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {m n : ℕ} (hm : D < q ^ (2 * m + 1)) (hn : D < p ^ (2 * n + 1))
    {K : ℝ} (hY : 1 ≤ Y) (W : Finset ℤ) (hdens : (Y : ℝ) ≤ K * W.card) (a b : ℤ → ℤ)
    (hdiff : ∀ w ∈ W, w = a w - b w)
    (haY : ∀ w ∈ W, |a w| ≤ (Y : ℤ)) (hbY : ∀ w ∈ W, |b w| ≤ (Y : ℤ))
    (ha : ∀ w ∈ W, Small q (1 / D) (a w)) (hb : ∀ w ∈ W, Small p (1 / D) (b w))
    (t : ℤ) (ht : |t| + ((max (q ^ (m ^ 2)) (p ^ (n ^ 2)) : ℕ) : ℤ) ≤ Y) :
    ∃ k : ℤ, (|k| : ℝ) ≤ 35 * K * Y ∧ Small q (35 * K / D) k ∧ Small p (35 * K / D) (k - t) := by
  classical
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < 1 / (D : ℝ) := by positivity
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hWne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · rw [h] at hdens; simp at hdens; omega
    · exact h
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast card_pos.mpr hWne
  have hK : 0 ≤ K := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.mp h) hWpos
    linarith
  set g1 : ℕ := q ^ (m ^ 2) with hg1
  set g2 : ℕ := p ^ (n ^ 2) with hg2
  have hg1pos : 0 < g1 := pow_pos (by omega) _
  have hg2pos : 0 < g2 := pow_pos (by omega) _
  have hG1 : g1 ≤ Y := by
    have : (g1 : ℤ) ≤ ((max g1 g2 : ℕ) : ℤ) := by exact_mod_cast le_max_left g1 g2
    have := abs_nonneg t
    omega
  have hG2 : g2 ≤ Y := by
    have : (g2 : ℤ) ≤ ((max g1 g2 : ℕ) : ℤ) := by exact_mod_cast le_max_right g1 g2
    have := abs_nonneg t
    omega
  -- the elementary witnesses
  have wW : ∀ w ∈ W, Wit p q D 1 Y w := by
    intro w hw
    refine ⟨a w, haY w hw, by simpa using ha w hw, ?_⟩
    have e : a w - w = b w := by have := hdiff w hw; omega
    rw [e]; simpa using hb w hw
  have wg1 : Wit p q D 1 Y (g1 : ℤ) := by
    refine ⟨(g1 : ℤ), by rw [Nat.abs_cast]; exact_mod_cast hG1, ?_, ?_⟩
    · have := small_pow hq hD hm
      simpa [hg1] using this
    · rw [sub_self]; exact small_zero (by simpa using hDpos)
  have wg2 : Wit p q D 1 Y (g2 : ℤ) := by
    refine ⟨0, by simp, small_zero (by simpa using hDpos), ?_⟩
    rw [zero_sub]
    have := (small_pow hp hD hn).neg
    simpa [hg2] using this
  -- the covering
  set I : Finset ℤ := Icc (-(Y : ℤ)) Y with hI
  set Disj : Finset ℤ → Prop := fun T =>
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ w₁ ∈ W, ∀ w₂ ∈ W, t₁ + w₁ = t₂ + w₂ → t₁ = t₂ with hDisj
  have hne : (I.powerset.filter Disj).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [mem_filter, mem_powerset]
    exact ⟨empty_subset _, fun t₁ h => absurd h (notMem_empty _)⟩
  obtain ⟨T, hT, hmax⟩ := exists_max_image (I.powerset.filter Disj) card hne
  rw [mem_filter, mem_powerset] at hT
  obtain ⟨hTI, hTd⟩ := hT
  have hWb : ∀ w ∈ W, |w| ≤ 2 * (Y : ℤ) := by
    intro w hw
    have h1 := haY w hw
    have h2 := hbY w hw
    have e := hdiff w hw
    rw [abs_le] at h1 h2 ⊢; omega
  have hTcard : (T.card : ℝ) ≤ 7 * K := by
    have h1 : T.card * W.card ≤ 6 * Y + 1 := by
      have h2 : (T ×ˢ W).card ≤ (Icc (-(3 * (Y : ℤ))) (3 * Y)).card := by
        refine card_le_card_of_injOn (fun x => x.1 + x.2) ?_ ?_
        · intro x hx
          rw [mem_coe, mem_product] at hx
          rw [mem_coe, mem_Icc]
          have h3 := hTI hx.1
          rw [hI, mem_Icc] at h3
          have h4 := hWb _ hx.2
          rw [abs_le] at h4
          simp only; omega
        · intro x hx y hy hxy
          rw [mem_coe, mem_product] at hx hy
          simp only at hxy
          have e1 := hTd _ hx.1 _ hy.1 _ hx.2 _ hy.2 hxy
          have e2 : x.2 = y.2 := by omega
          exact Prod.ext e1 e2
      rw [card_product, Int.card_Icc] at h2
      omega
    have h5 : (T.card : ℝ) * W.card ≤ 6 * Y + 1 := by exact_mod_cast h1
    have h6 : (T.card : ℝ) * Y ≤ 7 * K * Y := by
      have h7 := mul_le_mul_of_nonneg_left hdens (Nat.cast_nonneg (α := ℝ) T.card)
      have h8 := mul_le_mul_of_nonneg_left h5 hK
      nlinarith
    exact le_of_mul_le_mul_right h6 (by linarith)
  have hcover : ∀ x ∈ I, ∃ τ ∈ T, ∃ w₁ ∈ W, ∃ w₂ ∈ W, x - τ = w₁ - w₂ := by
    intro x hx
    by_cases hxT : x ∈ T
    · obtain ⟨w, hw⟩ := hWne
      exact ⟨x, hxT, w, hw, w, hw, by ring⟩
    have hnot : ¬ Disj (insert x T) := by
      intro hd
      have h1 : insert x T ∈ I.powerset.filter Disj := by
        rw [mem_filter, mem_powerset]
        exact ⟨insert_subset hx hTI, hd⟩
      have h2 := hmax _ h1
      rw [card_insert_of_notMem hxT] at h2
      omega
    simp only [hDisj, not_forall] at hnot
    obtain ⟨t₁, ht1, t₂, ht2, w₁, hw1, w₂, hw2, heq, hneq⟩ := hnot
    rw [mem_insert] at ht1 ht2
    rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hneq
    · exact ⟨t₂, h2, w₂, hw2, w₁, hw1, by omega⟩
    · exact ⟨t₁, h1, w₁, hw1, w₂, hw2, by omega⟩
    · exact absurd (hTd _ h1 _ h2 _ hw1 _ hw2 heq) hneq
  have hcover' : ∀ x : ℤ, ∃ τ : ℤ, x ∈ I → τ ∈ T ∧ ∃ w₁ ∈ W, ∃ w₂ ∈ W, x - τ = w₁ - w₂ := by
    intro x
    by_cases hx : x ∈ I
    · obtain ⟨τ, h1, h2⟩ := hcover x hx
      exact ⟨τ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose τ hτ using hcover'
  -- the walk
  have habs : |t| + (g1 : ℤ) ≤ Y ∧ |t| + (g2 : ℤ) ≤ Y := by
    have h1 : (g1 : ℤ) ≤ ((max g1 g2 : ℕ) : ℤ) := by exact_mod_cast le_max_left g1 g2
    have h2 : (g2 : ℤ) ≤ ((max g1 g2 : ℕ) : ℤ) := by exact_mod_cast le_max_right g1 g2
    constructor <;> omega
  have htb : -|t| ≤ t ∧ t ≤ |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have ht0 := abs_nonneg t
  have hcop : IsCoprime (g1 : ℤ) (g2 : ℤ) := by
    apply Nat.Coprime.isCoprime
    exact Nat.Coprime.pow _ _ hpq.symm
  obtain ⟨u, v, huv⟩ := hcop
  -- walk from `0` to `t`
  have hwalk : ∃ N : ℕ, ∃ f : ℕ → ℤ, f 0 = 0 ∧ f N = t ∧ (∀ i ≤ N, f i ∈ I) ∧
      (∀ i < N, f (i + 1) - f i = (g1 : ℤ) ∨ f (i + 1) - f i = -(g1 : ℤ)
        ∨ f (i + 1) - f i = (g2 : ℤ) ∨ f (i + 1) - f i = -(g2 : ℤ)) := by
    -- the walk lemma needs the end point inside the window with room for one step
    have h := walk (g1 := (g1 : ℤ)) (g2 := (g2 : ℤ)) (by exact_mod_cast hg1pos)
      (by exact_mod_cast hg2pos) (x := t) (lo := -(Y : ℤ)) (hi := Y)
      (by omega) (by omega) (by omega) (by omega)
      _ (t * u) (t * v) 0 rfl (by linear_combination (-t) * huv) (by omega) (by omega)
    obtain ⟨N, f, f0, fN, fb, fs⟩ := h
    refine ⟨N, f, f0, fN, fun i hi' => ?_, fs⟩
    rw [hI, mem_Icc]; exact fb i hi'
  obtain ⟨N, f, f0, fN, fI, fs⟩ := hwalk
  -- cut the loops through one translate
  have erase : ∀ d i : ℕ, N - i = d → i ≤ N →
      Wit p q D (5 * ((Icc i N).image (fun j => τ (f j))).card)
        (5 * Y * ((Icc i N).image (fun j => τ (f j))).card) (f N - f i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hd hi'
      set S := (Icc i N).image (fun j => τ (f j)) with hS
      set J := (Icc i N).filter (fun j => τ (f j) = τ (f i)) with hJ
      have hiJ : i ∈ J := by
        rw [hJ, mem_filter, mem_Icc]; exact ⟨⟨le_rfl, hi'⟩, rfl⟩
      set j := J.max' ⟨i, hiJ⟩ with hj
      have hjJ : j ∈ J := J.max'_mem _
      rw [hJ, mem_filter, mem_Icc] at hjJ
      obtain ⟨⟨hij, hjN⟩, hτj⟩ := hjJ
      have jump : Wit p q D 4 (4 * Y) (f j - f i) := by
        obtain ⟨_, w₁, h1, w₂, h2, e1⟩ := hτ _ (fI j hjN)
        obtain ⟨_, w₃, h3, w₄, h4, e2⟩ := hτ _ (fI i hi')
        have c1 : Wit p q D 2 (2 * Y) (w₁ - w₂) :=
          ((wW _ h1).sub (wW _ h2)).mono le_rfl (by omega)
        have c2 : Wit p q D 2 (2 * Y) (w₃ - w₄) :=
          ((wW _ h3).sub (wW _ h4)).mono le_rfl (by omega)
        have e : f j - f i = (w₁ - w₂) - (w₃ - w₄) := by omega
        rw [e]
        exact (c1.sub c2).mono le_rfl (by omega)
      have hS1 : 1 ≤ S.card := by
        apply card_pos.mpr
        exact ⟨τ (f i), mem_image.mpr ⟨i, mem_Icc.mpr ⟨le_rfl, hi'⟩, rfl⟩⟩
      rcases eq_or_lt_of_le hjN with hlast | hlt
      · rw [← hlast]
        refine jump.mono (by omega) ?_
        calc 4 * Y ≤ 5 * Y * 1 := by omega
          _ ≤ 5 * Y * S.card := Nat.mul_le_mul_left _ hS1
      · have one : Wit p q D 1 Y (f (j + 1) - f j) := by
          rcases fs j hlt with h | h | h | h
          · rw [h]; exact wg1
          · rw [h]; exact wg1.neg
          · rw [h]; exact wg2
          · rw [h]; exact wg2.neg
        have rest := ih (N - (j + 1)) (by omega) (j + 1) rfl (by omega)
        set S' := (Icc (j + 1) N).image (fun l => τ (f l)) with hS'
        have hsub : S' ⊆ S.erase (τ (f i)) := by
          intro x hx
          rw [hS', mem_image] at hx
          obtain ⟨l, hl, rfl⟩ := hx
          rw [mem_Icc] at hl
          rw [mem_erase]
          refine ⟨fun hcon => ?_, mem_image.mpr ⟨l, mem_Icc.mpr ⟨by omega, hl.2⟩, rfl⟩⟩
          have hlJ : l ∈ J := by
            rw [hJ, mem_filter, mem_Icc]; exact ⟨⟨by omega, hl.2⟩, hcon⟩
          have := J.le_max' l hlJ
          omega
        have hcard : S'.card + 1 ≤ S.card := by
          have h1 := card_le_card hsub
          have hmem : τ (f i) ∈ S := mem_image.mpr ⟨i, mem_Icc.mpr ⟨le_rfl, hi'⟩, rfl⟩
          rw [card_erase_of_mem hmem] at h1
          omega
        have e : f N - f i = ((f j - f i) + (f (j + 1) - f j)) + (f N - f (j + 1)) := by ring
        rw [e]
        refine ((jump.add one).add rest).mono (by omega) ?_
        calc 4 * Y + Y + 5 * Y * S'.card = 5 * Y * (S'.card + 1) := by ring
          _ ≤ 5 * Y * S.card := Nat.mul_le_mul_left _ hcard
  have fin := erase (N - 0) 0 rfl (Nat.zero_le _)
  rw [fN, f0, sub_zero] at fin
  set S := (Icc 0 N).image (fun j => τ (f j)) with hS
  have hST : S ⊆ T := by
    intro x hx
    rw [hS, mem_image] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    rw [mem_Icc] at hl
    exact (hτ _ (fI l hl.2)).1
  have hScard : (S.card : ℝ) ≤ 7 * K :=
    le_trans (by exact_mod_cast card_le_card hST) hTcard
  obtain ⟨k, k1, k2, k3⟩ := fin
  have hrad : ((5 * S.card : ℕ) : ℝ) / D ≤ 35 * K / D := by
    refine div_le_div_of_nonneg_right ?_ hD'.le
    push_cast; linarith
  refine ⟨k, ?_, Small.mono k2 hrad, Small.mono k3 hrad⟩
  have h1 : (|k| : ℝ) ≤ ((5 * Y * S.card : ℕ) : ℝ) := by exact_mod_cast k1
  refine le_trans h1 ?_
  push_cast
  have := mul_le_mul_of_nonneg_left hScard (show (0 : ℝ) ≤ 5 * Y by positivity)
  linarith

/-- Cauchy–Schwarz: few collisions force many differences. -/
lemma card_sq_le (A B : Finset ℤ) :
    (A.card * B.card) ^ 2 ≤ ((A ×ˢ B).image (fun x => x.1 - x.2)).card
      * (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2)).card := by
  classical
  set d : ℤ × ℤ → ℤ := fun x => x.1 - x.2 with hd
  set P := A ×ˢ B with hP
  set V := P.image d with hV
  set rep : ℤ → ℕ := fun v => (P.filter (fun x => d x = v)).card with hrep
  have htot : ∑ v ∈ V, rep v = A.card * B.card := by
    rw [← card_product, ← hP]
    exact (card_eq_sum_card_image d P).symm
  have hsq : ∑ v ∈ V, rep v ^ 2
      = ((P ×ˢ P).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2)).card := by
    have hmaps : ∀ y ∈ (P ×ˢ P).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2), d y.1 ∈ V := by
      intro y hy
      rw [mem_filter, mem_product] at hy
      exact mem_image_of_mem d hy.1.1
    rw [card_eq_sum_card_fiberwise (f := fun y => d y.1) (t := V) (fun y hy => hmaps y hy)]
    refine sum_congr rfl (fun v _ => ?_)
    have e : ((P ×ˢ P).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2)).filter (fun y => d y.1 = v)
        = (P.filter (fun x => d x = v)) ×ˢ (P.filter (fun x => d x = v)) := by
      ext y
      simp only [mem_filter, mem_product, hd]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨⟨h1, h4⟩, h2, by omega⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨⟨h1, h3⟩, by omega⟩, h2⟩
    rw [e, card_product, sq]
  have h := sq_sum_le_card_mul_sum_sq (s := V) (f := rep)
  rwa [htot, hsq] at h

/-- The same from a bound for the collision energy of two sets. -/
theorem witness_of_energy {p q D Y : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {m n : ℕ} (hm : D < q ^ (2 * m + 1)) (hn : D < p ^ (2 * n + 1))
    {K : ℝ} (hY : 1 ≤ Y) (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAY : ∀ x ∈ A, |x| ≤ (Y : ℤ)) (hBY : ∀ x ∈ B, |x| ≤ (Y : ℤ))
    (ha : ∀ x ∈ A, Small q (1 / D) x) (hb : ∀ x ∈ B, Small p (1 / D) x)
    (hE : (Y : ℝ)
        * (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2)).card
      ≤ K * ((A.card : ℝ) * B.card) ^ 2)
    (t : ℤ) (ht : |t| + ((max (q ^ (m ^ 2)) (p ^ (n ^ 2)) : ℕ) : ℤ) ≤ Y) :
    ∃ k : ℤ, (|k| : ℝ) ≤ 35 * K * Y ∧ Small q (35 * K / D) k ∧ Small p (35 * K / D) (k - t) := by
  classical
  set W := (A ×ˢ B).image (fun x => x.1 - x.2) with hW
  set E := (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun y => y.1.1 - y.1.2 = y.2.1 - y.2.2)).card with hEdef
  have hCS : ((A.card : ℝ) * B.card) ^ 2 ≤ W.card * E := by exact_mod_cast card_sq_le A B
  have hABpos : (0 : ℝ) < ((A.card : ℝ) * B.card) ^ 2 := by
    have h1 : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hA
    have h2 : (0 : ℝ) < B.card := by exact_mod_cast card_pos.mpr hB
    positivity
  have hEpos : (0 : ℝ) < E := by
    rcases (Nat.cast_nonneg (α := ℝ) E).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hCS; linarith
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY
  have hK : 0 ≤ K := by
    by_contra h
    have h1 := mul_neg_of_neg_of_pos (not_le.mp h) hABpos
    have h2 := mul_pos hYpos hEpos
    linarith
  have hdens : (Y : ℝ) ≤ K * W.card := by
    have h1 : (Y : ℝ) * E ≤ (K * W.card) * E := by
      have := mul_le_mul_of_nonneg_left hCS hK
      linarith
    exact le_of_mul_le_mul_right h1 hEpos
  have hpre : ∀ w ∈ W, ∃ x ∈ A ×ˢ B, x.1 - x.2 = w := fun w hw => mem_image.mp hw
  have hpre' : ∀ w : ℤ, ∃ x : ℤ × ℤ, w ∈ W → x.1 ∈ A ∧ x.2 ∈ B ∧ x.1 - x.2 = w := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨x, hx, e⟩ := hpre w hw
      rw [mem_product] at hx
      exact ⟨x, fun _ => ⟨hx.1, hx.2, e⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hw⟩
  choose c hc using hpre'
  exact witness_of_support hp hq hpq hD hm hn hY W hdens (fun w => (c w).1) (fun w => (c w).2)
    (fun w hw => (hc w hw).2.2.symm) (fun w hw => hAY _ (hc w hw).1)
    (fun w hw => hBY _ (hc w hw).2.1) (fun w hw => ha _ (hc w hw).1)
    (fun w hw => hb _ (hc w hw).2.1) t ht

/-- Conversely, a range of witnessed targets forces many differences. -/
theorem support_of_range {p q : ℕ} {ε : ℝ} {X T : ℕ}
    (h : ∀ t : ℤ, |t| ≤ (T : ℤ) → ∃ k : ℤ, |k| ≤ (X : ℤ) ∧ Small q ε k ∧ Small p ε (k - t)) :
    ∃ W : Finset ℤ, 2 * T + 1 ≤ W.card ∧ ∀ w ∈ W, ∃ a b : ℤ, w = a - b ∧ |a| ≤ (X : ℤ)
      ∧ |b| ≤ ((X + T : ℕ) : ℤ) ∧ Small q ε a ∧ Small p ε b := by
  refine ⟨Icc (-(T : ℤ)) T, by rw [Int.card_Icc]; omega, fun w hw => ?_⟩
  rw [mem_Icc, ← abs_le] at hw
  obtain ⟨k, k1, k2, k3⟩ := h w hw
  refine ⟨k, k - w, by ring, k1, ?_, k2, k3⟩
  have := abs_sub k w
  push_cast; omega

end TwoPrimesSupport
