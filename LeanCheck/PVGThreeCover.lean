import LeanCheck.PVGThreeBaire

/-!
# PVGthree: an obstruction to rigidity by covering numbers

`δ_k = 2^(-L_k)`. A finite set `E` of positions is *served* by a shift `n` at width `h` if no
`(m+1)^2 - (n+1)^2 + p`, `p ∈ E`, `m > n`, lies in a window `[L_k - h, L_k)`. If for some fixed width there are
far finite sets of positions that cannot be covered by `c` served sets, `c = 1, 2, ...`, then `δ` is not rigid
(`not_rig_of_covers`).
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Three
open Two Q95 Lac

/-- The set `E` is served by one shift (with a slack `c` for its largest elements). -/
def GoodC (L : ℕ → ℕ) (h c : ℕ) (E : Finset ℕ) : Prop :=
  ∃ n : ℕ, ∀ p ∈ E, p ≤ (n + 1) ^ 2 + c ∧ ∀ k m q : ℕ, n < m → q + (n + 1) ^ 2 = (m + 1) ^ 2 + p →
    L k ≤ q + h → q < L k → False

/-- At most `j` served sets cover the positions of `B`. -/
def Covd (L : ℕ → ℕ) (h c j : ℕ) (B : Finset ℕ) : Prop :=
  ∃ E : Finset (Finset ℕ), E.card ≤ j ∧ (∀ e ∈ E, GoodC L h c e) ∧ ∀ p ∈ B, ∃ e ∈ E, p ∈ e

lemma covd_empty (L : ℕ → ℕ) (h c j : ℕ) : Covd L h c j ∅ :=
  ⟨∅, by simp, by simp, by simp⟩

lemma covd_mono {L : ℕ → ℕ} {h c j j' : ℕ} {B B' : Finset ℕ} (hj : j ≤ j') (hB : B' ⊆ B)
    (hc : Covd L h c j B) : Covd L h c j' B' := by
  obtain ⟨E, h1, h2, h3⟩ := hc
  exact ⟨E, h1.trans hj, h2, fun p hp => h3 p (hB hp)⟩

lemma covd_union {L : ℕ → ℕ} {h c j j' : ℕ} {B B' : Finset ℕ} (hc : Covd L h c j B) (hc' : Covd L h c j' B') :
    Covd L h c (j + j') (B ∪ B') := by
  classical
  obtain ⟨E, h1, h2, h3⟩ := hc
  obtain ⟨E', h1', h2', h3'⟩ := hc'
  refine ⟨E ∪ E', (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h1'), fun e he => ?_, fun p hp => ?_⟩
  · rcases Finset.mem_union.1 he with h | h
    exacts [h2 e h, h2' e h]
  · rcases Finset.mem_union.1 hp with h | h
    · obtain ⟨e, he, hpe⟩ := h3 p h
      exact ⟨e, Finset.mem_union_left _ he, hpe⟩
    · obtain ⟨e, he, hpe⟩ := h3' p h
      exact ⟨e, Finset.mem_union_right _ he, hpe⟩

lemma dint_nat_mul_le (N : ℕ) (x : ℝ) : dint ((N : ℝ) * x) ≤ N * dint x := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact (dint_le_abs _).trans (by simp)
  | succ N ih =>
    have e : ((N + 1 : ℕ) : ℝ) * x = (N : ℝ) * x + x := by push_cast; ring
    rw [e]
    refine (dint_add_le' _ _).trans ?_
    push_cast
    linarith

/-- Spaced powers of two below `2^(p)` add up to at most a third of it. -/
lemma three_sum_le (Q : Finset ℕ) (hsep : ∀ a ∈ Q, ∀ b ∈ Q, a < b → a + 2 ≤ b) (p : ℕ)
    (hp : ∀ q ∈ Q, q + 2 ≤ p) : 3 * ∑ q ∈ Q, 2 ^ q ≤ 2 ^ p := by
  classical
  induction p using Nat.strong_induction_on generalizing Q with
  | _ p ih =>
    rcases Q.eq_empty_or_nonempty with h0 | hne
    · rw [h0]
      simp
    set M := Q.max' hne with hM
    have hMQ : M ∈ Q := Q.max'_mem hne
    have hMp := hp M hMQ
    have hrest : 3 * ∑ q ∈ Q.erase M, 2 ^ q ≤ 2 ^ M := by
      refine ih M (by omega) _ (fun a ha b hb => hsep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb))
        fun q hq => ?_
      obtain ⟨hne', hqQ⟩ := Finset.mem_erase.1 hq
      have h1 : q ≤ M := Q.le_max' q hqQ
      exact hsep q hqQ M hMQ (lt_of_le_of_ne h1 hne')
    have h2 : 2 ^ (M + 2) ≤ 2 ^ p := Nat.pow_le_pow_right two_pos hMp
    have h3 : (2 : ℕ) ^ (M + 2) = 4 * 2 ^ M := by rw [pow_add]; ring
    rw [← Finset.add_sum_erase Q _ hMQ]
    omega

lemma third_le_dint (v : ℝ) (h1 : 1 / 3 ≤ v) (h2 : v ≤ 2 / 3) : 1 / 3 ≤ dint v := by
  rw [Two.dint_eq]
  rcases lt_or_ge v (1 / 2) with h | h
  · have e : round v = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨by linarith, h⟩
    rw [e, Int.cast_zero, sub_zero, abs_of_nonneg (by linarith)]
    exact h1
  · have e : round v = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      push_cast
      exact ⟨by linarith, by linarith⟩
    rw [e, Int.cast_one, abs_of_nonpos (by linarith)]
    linarith

/-- Finitely many characters see only finitely many points up to a given error. -/
lemma finite_net (Pf : Finset ℕ) (x : ℕ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R : Finset ℕ, ∀ n : ℕ, ∃ n' ∈ R, ∀ p ∈ Pf, dint ((x n - x n') / 2 ^ (p + 1)) < ρ := by
  classical
  set f : ℕ → (Pf → AddCircle (1 : ℝ)) := fun n p => ((x n / 2 ^ ((p : ℕ) + 1) : ℝ) : AddCircle (1 : ℝ))
    with hf
  have htbf : TotallyBounded (range f) := (isCompact_univ.totallyBounded).subset (subset_univ _)
  obtain ⟨t, ht1, ht2, ht3⟩ := Metric.finite_approx_of_totallyBounded htbf _ hρ
  have hch : ∀ y ∈ t, ∃ n, f n = y := fun y hy => ht1 hy
  choose g hg' using hch
  refine ⟨ht2.toFinset.attach.image fun y => g y.1 (ht2.mem_toFinset.1 y.2), fun n => ?_⟩
  obtain ⟨y, hy, hd⟩ := mem_iUnion₂.1 (ht3 (mem_range_self n))
  refine ⟨g y hy, Finset.mem_image.2 ⟨⟨y, ht2.mem_toFinset.2 hy⟩, Finset.mem_attach _ _, rfl⟩, fun p hp => ?_⟩
  have h1 := (dist_le_pi_dist (f n) y ⟨p, hp⟩).trans_lt (Metric.mem_ball.1 hd)
  rw [← hg' y hy] at h1
  rw [sub_div]
  simp only [hf] at h1
  rw [dist_eq_norm, ← AddCircle.coe_sub] at h1
  exact h1

/-- **Unbounded covering numbers at one width exclude rigidity.** -/
theorem not_rig_of_covers (L : ℕ → ℕ) (hL : StrictMono L) (h : ℕ) (P : ℕ → Finset ℕ)
    (hsep : ∀ c c' : ℕ, ∀ p ∈ P c, ∀ q ∈ P c', p < q → p + 2 ≤ q)
    (hinc : ∀ c c' : ℕ, c < c' → ∀ p ∈ P c, ∀ q ∈ P c', p < q)
    (hfar : ∀ B : ℕ, ∀ᶠ c in atTop, ∀ p ∈ P c, B ≤ p)
    (hout : ∀ g : ℕ, ∀ᶠ c in atTop, ∀ p ∈ P c, Out L g p)
    (hcov : ∀ᶠ c in atTop, ¬ Covd L h c c (P c)) : ¬ Rig (dyseq L) := by
  classical
  intro hrig
  set B : ℝ → ℕ → ℕ → Finset ℕ := fun x r c =>
    (P c).filter fun p => ((4 : ℝ) ^ (r + 1))⁻¹ ≤ dint (x / 2 ^ (p + 1)) with hB
  set Vr : ℕ → Set ℝ := fun r => {x | ∀ c, Covd L h c (c / 4 ^ r) (B x r c)} with hVr
  have hmemB : ∀ x r c p, p ∈ B x r c ↔ p ∈ P c ∧ ((4 : ℝ) ^ (r + 1))⁻¹ ≤ dint (x / 2 ^ (p + 1)) := by
    intro x r c p
    rw [hB]
    exact Finset.mem_filter
  have h4pos : ∀ r : ℕ, (0 : ℝ) < ((4 : ℝ) ^ (r + 1))⁻¹ := fun r => by positivity
  have h4anti : ∀ a b : ℕ, a ≤ b → ((4 : ℝ) ^ (b + 1))⁻¹ ≤ ((4 : ℝ) ^ (a + 1))⁻¹ := fun a b hab =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have h4half : ∀ r : ℕ, 2 * ((4 : ℝ) ^ (r + 1 + 1))⁻¹ ≤ ((4 : ℝ) ^ (r + 1))⁻¹ := by
    intro r
    have h1 := h4pos r
    have e : ((4 : ℝ) ^ (r + 1 + 1))⁻¹ = ((4 : ℝ) ^ (r + 1))⁻¹ / 4 := by
      rw [pow_succ (4 : ℝ) (r + 1), mul_inv]
      ring
    rw [e]
    linarith
  -- the filter basis
  have hVmono : ∀ a b : ℕ, a ≤ b → Vr b ⊆ Vr a := by
    intro a b hab x hx c
    refine covd_mono (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hab) (by positivity)) ?_ (hx c)
    intro p hp
    obtain ⟨h1, h2⟩ := (hmemB _ _ _ _).1 hp
    exact (hmemB _ _ _ _).2 ⟨h1, (h4anti a b hab).trans h2⟩
  have hempty : ∀ x r c, (∀ p ∈ P c, dint (x / 2 ^ (p + 1)) < ((4 : ℝ) ^ (r + 1))⁻¹) →
      Covd L h c (c / 4 ^ r) (B x r c) := by
    intro x r c hx
    have : B x r c = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      obtain ⟨h1, h2⟩ := (hmemB _ _ _ _).1 hp
      exact absurd h2 (not_le.2 (hx p h1))
    rw [this]
    exact covd_empty _ _ _ _
  have hsub : ∀ (x y : ℝ) (r c : ℕ), c / 4 ^ (r + 1) + c / 4 ^ (r + 1) ≤ c / 4 ^ r := by
    intro _ _ r c
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    generalize c / 4 ^ r = a
    omega
  have hsum : ∀ (x y z : ℝ) (r c : ℕ), (∀ u : ℝ, dint (z / u) ≤ dint (x / u) + dint (y / u)) →
      ∀ p ∈ B z r c, p ∈ B x (r + 1) c ∪ B y (r + 1) c := by
    intro x y z r c hz p hp
    obtain ⟨h1, h2⟩ := (hmemB _ _ _ _).1 hp
    rw [Finset.mem_union, hmemB, hmemB]
    by_contra hc
    push Not at hc
    have ha := hc.1 h1
    have hb := hc.2 h1
    have := hz (2 ^ (p + 1))
    have := h4half r
    linarith
  have h0mem : ∀ r, (0 : ℝ) ∈ Vr r := by
    intro r c
    refine hempty _ _ _ fun p _ => ?_
    rw [zero_div]
    exact lt_of_le_of_lt ((dint_le_abs _).trans (by simp)) (h4pos r)
  have hneg : ∀ r, ∀ x ∈ Vr r, -x ∈ Vr r := by
    intro r x hx c
    have : B (-x) r c = B x r c := by
      ext p
      rw [hmemB, hmemB, neg_div, dint_neg]
    rw [this]
    exact hx c
  have hadd : ∀ r, ∀ x ∈ Vr (r + 1), ∀ y ∈ Vr (r + 1), x + y ∈ Vr r := by
    intro r x hx y hy c
    refine covd_mono (hsub x y r c) (hsum x y (x + y) r c fun u => ?_) (covd_union (hx c) (hy c))
    rw [add_div]
    exact dint_add_le' _ _
  let sets : Set (Set ℝ) := range Vr
  let basis : AddGroupFilterBasis ℝ := addGroupFilterBasisOfComm sets ⟨Vr 0, 0, rfl⟩
    (by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨Vr (max a b), ⟨_, rfl⟩, subset_inter (hVmono _ _ (le_max_left _ _)) (hVmono _ _ (le_max_right _ _))⟩)
    (by
      rintro _ ⟨r, rfl⟩
      exact h0mem r)
    (by
      rintro _ ⟨r, rfl⟩
      refine ⟨Vr (r + 1), ⟨_, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact hadd r x hx y hy)
    (by
      rintro _ ⟨r, rfl⟩
      exact ⟨Vr r, ⟨_, rfl⟩, fun x hx => hneg r x hx⟩)
  set γ : TopologicalSpace ℝ := basis.topology with hγ
  have hg : @IsTopologicalAddGroup ℝ γ _ := basis.isTopologicalAddGroup
  have hnh : ∀ U : Set ℝ, U ∈ @nhds ℝ γ 0 ↔ ∃ r, Vr r ⊆ U := by
    intro U
    rw [hγ, basis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨V, ⟨r, rfl⟩, hV⟩
      exact ⟨r, hV⟩
    · rintro ⟨r, hr⟩
      exact ⟨Vr r, ⟨r, rfl⟩, hr⟩
  have heu : euclidNhds 0 ≤ @nhds ℝ γ 0 := by
    intro U hU
    obtain ⟨r, hr⟩ := (hnh U).1 hU
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) (h4pos r)) fun x hx => hr fun c => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    refine hempty _ _ _ fun p _ => lt_of_le_of_lt ((dint_le_abs _).trans ?_) hx
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ (p + 1) by positivity)]
    exact div_le_self (abs_nonneg _) (one_le_pow₀ one_le_two)
  have htb : ∀ a : ℝ, InA (dyseq L) sT a → Tb (@nhds ℝ γ 0) (dil a Sset) := by
    intro a ha U hU
    obtain ⟨r, hr⟩ := (hnh U).1 hU
    set θ : ℝ := ((4 : ℝ) ^ (r + 1 + 1))⁻¹ with hθ
    have hθ0 : 0 < θ := h4pos (r + 1)
    obtain ⟨K, hK⟩ := eventually_atTop.1 (ha (θ / 2 ^ (h + 1)) (by positivity))
    obtain ⟨c1, hc1⟩ := pow_unbounded_of_one_lt (|a| / θ) (one_lt_two (α := ℝ))
    obtain ⟨c2, hc2⟩ := eventually_atTop.1 (hfar (L K + 1))
    set c0 := c1 + c2 + 4 ^ (r + 1) with hc0
    -- the exceptional positions of a dilate form one served set when `c` is large
    have hgood : ∀ c, c0 ≤ c → ∀ n : ℕ, GoodC L h c (B (a * sT n) (r + 1) c) := by
      intro c hc n
      have hc1c : c1 ≤ c := le_trans (le_trans (Nat.le_add_right c1 c2) (Nat.le_add_right _ _)) hc
      have hc2c : c2 ≤ c := le_trans (le_trans (Nat.le_add_left c2 c1) (Nat.le_add_right _ _)) hc
      refine ⟨n, fun p hp => ?_⟩
      obtain ⟨hpP, hpθ⟩ := (hmemB _ _ _ _).1 hp
      have hsT : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := rfl
      refine ⟨?_, fun k m q hnm hbal hlo hhi => ?_⟩
      · by_contra hcon
        have h1 : dint (a * sT n / 2 ^ (p + 1)) < θ := by
          refine lt_of_le_of_lt (dint_le_abs _) ?_
          rw [abs_div, abs_mul, hsT, abs_of_pos (show (0 : ℝ) < 2 ^ ((n + 1) ^ 2) by positivity),
            abs_of_pos (show (0 : ℝ) < 2 ^ (p + 1) by positivity), div_lt_iff₀ (by positivity)]
          have h2 : |a| < θ * 2 ^ c1 := by
            rw [div_lt_iff₀ hθ0] at hc1
            linarith
          have h3 : (2 : ℝ) ^ c1 * 2 ^ ((n + 1) ^ 2) ≤ 2 ^ (p + 1) := by
            rw [← pow_add]
            refine pow_le_pow_right₀ one_le_two ?_
            have h4 := not_le.1 hcon
            exact le_trans (Nat.add_le_add_right hc1c _) (by rw [Nat.add_comm]; exact le_trans h4.le (Nat.le_succ _))
          calc |a| * 2 ^ ((n + 1) ^ 2) < θ * 2 ^ c1 * 2 ^ ((n + 1) ^ 2) :=
                mul_lt_mul_of_pos_right h2 (by positivity)
            _ = θ * (2 ^ c1 * 2 ^ ((n + 1) ^ 2)) := by ring
            _ ≤ θ * 2 ^ (p + 1) := mul_le_mul_of_nonneg_left h3 hθ0.le
        exact absurd hpθ (not_le.2 h1)
      · have hpK : L K + 1 ≤ p := hc2 c hc2c p hpP
        have hsq : (n + 1) ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have hKk : K < k := by
          by_contra hc'
          have := hL.monotone (not_lt.1 hc')
          omega
        obtain ⟨s, hs⟩ : ∃ s, L k = q + s := ⟨L k - q, by omega⟩
        have hs1 : 1 ≤ s := by omega
        have hsh : s ≤ h := by omega
        have h1 := hK k hKk.le m
        have hsm : sT m = (2 : ℝ) ^ ((m + 1) ^ 2) := rfl
        have e1 : a * sT n / 2 ^ (p + 1) = ((2 ^ (s - 1) : ℕ) : ℝ) * (a * dyseq L k * sT m) := by
          have h3 : (s - 1) + (m + 1) ^ 2 + (p + 1) = (n + 1) ^ 2 + L k := by omega
          rw [hsT, hsm]
          unfold dyseq
          push_cast
          rw [div_eq_iff (by positivity)]
          have h5 : (2 : ℝ) ^ (s - 1) * 2 ^ ((m + 1) ^ 2) * 2 ^ (p + 1) = 2 ^ ((n + 1) ^ 2) * 2 ^ L k := by
            rw [← pow_add, ← pow_add, ← pow_add, h3]
          field_simp
          linear_combination (-a) * h5
        have h6 : dint (a * sT n / 2 ^ (p + 1)) < θ := by
          rw [e1]
          refine lt_of_le_of_lt (dint_nat_mul_le _ _) ?_
          have h7 : ((2 ^ (s - 1) : ℕ) : ℝ) ≤ 2 ^ h := by
            push_cast
            exact pow_le_pow_right₀ one_le_two (by omega)
          refine lt_of_le_of_lt (mul_le_mul h7 h1 (by
            unfold dint; exact norm_nonneg _) (by positivity)) ?_
          have e2 : (2 : ℝ) ^ h * (θ / 2 ^ (h + 1)) = θ / 2 := by
            rw [pow_succ]
            field_simp
          rw [e2]
          linarith
        exact absurd hpθ (not_le.2 h6)
    -- the finitely many small blocks are handled by compactness
    set Pf : Finset ℕ := (Finset.range c0).biUnion P with hPf
    obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, ∀ n : ℕ, ∃ n' ∈ R, ∀ p ∈ Pf,
        dint ((a * sT n - a * sT n') / 2 ^ (p + 1)) < ((4 : ℝ) ^ (r + 1))⁻¹ := by
      exact finite_net Pf (fun n => a * sT n) _ (h4pos r)
    set Fp : Finset ℝ := R.image (fun n' => a * sT n') with hFp
    refine ⟨insert 0 (Fp ∪ Fp.image fun y => -y), fun y hy => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hy
    have hmain : ∀ n : ℕ, ∃ n' ∈ R, a * sT n - a * sT n' ∈ Vr r := by
      intro n
      obtain ⟨n', hn', hclose⟩ := hR n
      refine ⟨n', hn', fun c => ?_⟩
      rcases lt_or_ge c c0 with hc | hc
      · exact hempty _ _ _ fun p hp => hclose p (Finset.mem_biUnion.2 ⟨c, Finset.mem_range.2 hc, hp⟩)
      · have h1 : Covd L h c 1 (B (a * sT n) (r + 1) c) :=
          ⟨{B (a * sT n) (r + 1) c}, by simp, fun e he => by
            rw [Finset.mem_singleton.1 he]
            exact hgood c hc n, fun p hp => ⟨_, Finset.mem_singleton_self _, hp⟩⟩
        have h2 : Covd L h c 1 (B (a * sT n') (r + 1) c) :=
          ⟨{B (a * sT n') (r + 1) c}, by simp, fun e he => by
            rw [Finset.mem_singleton.1 he]
            exact hgood c hc n', fun p hp => ⟨_, Finset.mem_singleton_self _, hp⟩⟩
        have h3 : 1 + 1 ≤ c / 4 ^ r := by
          rw [Nat.le_div_iff_mul_le (by positivity)]
          have h4 : (4 : ℕ) ^ (r + 1) = 4 ^ r * 4 := pow_succ 4 r
          omega
        refine covd_mono h3 (hsum (a * sT n) (a * sT n') _ r c fun u => ?_) (covd_union h1 h2)
        have e : (a * sT n - a * sT n') / u = a * sT n / u + -(a * sT n' / u) := by ring
        rw [e]
        refine (dint_add_le' _ _).trans ?_
        rw [dint_neg]
    have h0U : (0 : ℝ) ∈ U := hr (h0mem r)
    rcases hs with rfl | ⟨n, hn, rfl | rfl⟩
    · refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
      simpa using h0U
    · have e : sS n = sT (n - 1) := by
        show sS n = sS (n - 1 + 1)
        rw [Nat.sub_add_cancel hn]
      obtain ⟨n', hn', h1⟩ := hmain (n - 1)
      refine ⟨a * sT n', Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hn')), ?_⟩
      simp only
      rw [e]
      exact hr h1
    · have e : sS n = sT (n - 1) := by
        show sS n = sS (n - 1 + 1)
        rw [Nat.sub_add_cancel hn]
      obtain ⟨n', hn', h1⟩ := hmain (n - 1)
      refine ⟨-(a * sT n'), Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_image_of_mem _ hn'))), ?_⟩
      have h2 : -(a * sT (n - 1) - a * sT n') ∈ U := hr (hneg r _ h1)
      simp only
      rw [e]
      have e2 : a * -sT (n - 1) - -(a * sT n') = -(a * sT (n - 1) - a * sT n') := by ring
      rw [e2]
      exact h2
  -- rigidity fails
  have hW : Vr 1 ∈ @nhds ℝ γ 0 := (hnh _).2 ⟨1, Subset.rfl⟩
  obtain ⟨ε, hε, F, hF⟩ := hrig γ hg heu htb _ hW
  obtain ⟨g, hg'⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  rw [one_div, inv_pow] at hg'
  obtain ⟨c3, hc3⟩ := eventually_atTop.1 ((hout g).and hcov)
  set x : ℕ → ℝ := fun c => ∑ p ∈ P c, (2 : ℝ) ^ p with hx
  have hxU : ∀ c, c3 ≤ c → ∀ k, dint (dyseq L k * x c) ≤ ε := by
    intro c hc k
    rw [dyseq_mul, hx]
    refine (dint_sum_pow (P c) (L k) g fun p hp => ?_).trans hg'.le
    by_contra hcon
    push Not at hcon
    exact (hc3 c hc).1 p hp k hcon.2 hcon.1
  have hcovF : ∀ i : ℕ, ∃ f : F, x (c3 + i) - f.1 ∈ Vr 1 := by
    intro i
    obtain ⟨f, hf, h1⟩ := hF _ (hxU _ (Nat.le_add_right _ _))
    exact ⟨⟨f, hf⟩, h1⟩
  choose f hf using hcovF
  obtain ⟨i, j, hij, heq⟩ : ∃ i j : ℕ, i < j ∧ f i = f j := by
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
    rcases lt_or_gt_of_ne hab with h' | h'
    · exact ⟨a, b, h', he⟩
    · exact ⟨b, a, h', he.symm⟩
  set c := c3 + i with hc
  set c' := c3 + j with hc'
  have hcc : c < c' := by omega
  have hmem : x c' - x c ∈ Vr 0 := by
    have h1 := hf i
    have h2 := hf j
    rw [← heq] at h2
    have e : x c' - x c = (x c' - (f i).1) + -(x c - (f i).1) := by ring
    rw [e]
    exact hadd 0 _ h2 _ (hneg 1 _ h1)
  refine (hc3 c' (by omega)).2 (covd_mono (by simp) ?_ (hmem c'))
  intro p hp
  refine (hmemB _ _ _ _).2 ⟨hp, ?_⟩
  have h4 : ((4 : ℝ) ^ (0 + 1))⁻¹ ≤ 1 / 3 := by norm_num
  refine h4.trans ?_
  -- the value at `p` is `1/2` plus two small terms, up to an integer
  set lo := (P c').filter (fun q => q < p) with hlo
  set hi := (P c').filter (fun q => p < q) with hhi
  have hsplit : x c' = (∑ q ∈ lo, (2 : ℝ) ^ q) + 2 ^ p + ∑ q ∈ hi, (2 : ℝ) ^ q := by
    have e1 : P c' = insert p (lo ∪ hi) := by
      ext q
      rw [Finset.mem_insert, Finset.mem_union, hlo, hhi, Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro hq
        rcases lt_trichotomy q p with h' | h' | h'
        exacts [Or.inr (Or.inl ⟨hq, h'⟩), Or.inl h', Or.inr (Or.inr ⟨hq, h'⟩)]
      · rintro (rfl | h' | h')
        exacts [hp, h'.1, h'.1]
    have h5 : p ∉ lo ∪ hi := by
      rw [Finset.mem_union, hlo, hhi, Finset.mem_filter, Finset.mem_filter]
      omega
    have h6 : Disjoint lo hi := Finset.disjoint_left.2 fun q h1 h2 => by
      have := (Finset.mem_filter.1 h1).2
      have := (Finset.mem_filter.1 h2).2
      omega
    show ∑ q ∈ P c', (2 : ℝ) ^ q = _
    conv_lhs => rw [e1]
    rw [Finset.sum_insert h5, Finset.sum_union h6]
    ring
  have hhi_int : (∑ q ∈ hi, (2 : ℝ) ^ q) / 2 ^ (p + 1) = ((∑ q ∈ hi, (2 : ℤ) ^ (q - (p + 1)) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel (by omega : p + 1 ≤ q)]
  have hlo_le : (∑ q ∈ lo, (2 : ℝ) ^ q) / 2 ^ (p + 1) ≤ 1 / 6 := by
    have h1 : 3 * ∑ q ∈ lo, 2 ^ q ≤ 2 ^ p := by
      refine three_sum_le lo (fun a ha b hb => hsep c' c' a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1)
        p fun q hq => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
      exact hsep c' c' q h1 p hp h2
    have h2 : 3 * (∑ q ∈ lo, (2 : ℝ) ^ q) ≤ 2 ^ p := by exact_mod_cast h1
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith
  have hxc_le : x c / 2 ^ (p + 1) ≤ 1 / 6 := by
    have h1 : 3 * ∑ q ∈ P c, 2 ^ q ≤ 2 ^ p := by
      refine three_sum_le (P c) (fun a ha b hb => hsep c c a ha b hb) p fun q hq => ?_
      exact hsep c c' q hq p hp (hinc c c' hcc q hq p hp)
    have h2 : 3 * x c ≤ 2 ^ p := by
      rw [hx]
      simp only
      exact_mod_cast h1
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith
  have hhalf : (2 : ℝ) ^ p / 2 ^ (p + 1) = 1 / 2 := by
    rw [pow_succ]
    field_simp
  have hxc0 : 0 ≤ x c / 2 ^ (p + 1) := by rw [hx]; positivity
  have hlo0 : 0 ≤ (∑ q ∈ lo, (2 : ℝ) ^ q) / 2 ^ (p + 1) := by positivity
  have e2 : (x c' - x c) / 2 ^ (p + 1) =
      (1 / 2 + (∑ q ∈ lo, (2 : ℝ) ^ q) / 2 ^ (p + 1) - x c / 2 ^ (p + 1)) -
        ((-(∑ q ∈ hi, (2 : ℤ) ^ (q - (p + 1))) : ℤ) : ℝ) := by
    rw [hsplit, sub_div, add_div, add_div, hhalf, hhi_int]
    push_cast
    ring
  rw [e2, dint_sub_int]
  exact third_le_dint _ (by linarith) (by linarith)

end Three
end PVG
