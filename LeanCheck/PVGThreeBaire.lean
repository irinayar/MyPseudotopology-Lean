import LeanCheck.PVGThreeClassify

/-!
# PVGthree: uniform total boundedness, and rigidity with several classes

* `unif`: if every dilate `aS`, `a ∈ A(δ)`, is totally bounded for a group topology below the Euclidean one,
  then the dilates `bS` of the coefficients `b` that are *uniformly small* are covered by one finite set.
  This is Baire's theorem for `A(δ)` with the metric of uniform convergence; it uses no property of `δ`.
* `rig_of_classes`: a sufficient condition for rigidity of `δ_k = 2^(-L_k)` with window widths that stay
  bounded and finitely many classes of positions. It implies `rig_of_avoids_seq`.

Sequences are indexed from `0`; `sT n = 2^((n+1)^2)`.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Three
open Two Q95 Lac

/-! ## Uniformity -/

lemma inA_add (δ t : ℕ → ℝ) {a b : ℝ} (ha : InA δ t a) (hb : InA δ t b) : InA δ t (a + b) := by
  intro ε hε
  filter_upwards [ha (ε / 2) (by positivity), hb (ε / 2) (by positivity)] with k h1 h2 n
  have e : (a + b) * δ k * t n = a * δ k * t n + b * δ k * t n := by ring
  rw [e]
  refine (dint_add_le' _ _).trans ?_
  have := h1 n
  have := h2 n
  linarith

lemma inA_zero (δ t : ℕ → ℝ) : InA δ t 0 := by
  intro ε hε
  exact Eventually.of_forall fun k n => by
    rw [zero_mul, zero_mul]
    exact (dint_le_abs _).trans (by simpa using hε.le)

lemma continuous_dint' : Continuous dint := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  have h1 := dint_add_le' (x - y) y
  have h2 := dint_add_le' (y - x) x
  rw [sub_add_cancel] at h1 h2
  have h3 := dint_le_abs (x - y)
  have h4 := dint_le_abs (y - x)
  rw [abs_sub_comm y x] at h4
  exact ⟨by linarith, by linarith⟩

/-- Total boundedness of the dilates is uniform on uniformly small coefficients. -/
theorem unif (δ t : ℕ → ℝ) (S : Set ℝ) (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (hA : ∀ a : ℝ, InA δ t a → Tb N (dil a S)) (W : Set ℝ) (hW : W ∈ N) :
    ∃ η : ℝ, 0 < η ∧ ∃ F : Finset ℝ, ∀ b : ℝ, InA δ t b → |b| ≤ η → (∀ k n, dint (b * δ k * t n) ≤ η) →
      ∀ s ∈ S, ∃ f ∈ F, b * s - f ∈ W := by
  classical
  obtain ⟨V, hV, hsym, h8⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hV)
  set C : Set ℝ := closure {x | ∃ y ∈ V, ∃ z ∈ V, x = y + z} with hC
  set E : Finset ℚ → ℝ → Prop := fun G a => ∀ s ∈ S, ∃ g ∈ G, a * s - (g : ℝ) ∈ C with hE
  have hcover : ∀ a, InA δ t a → ∃ G, E G a := by
    intro a ha
    obtain ⟨F, hF⟩ := hA a ha V hV
    have hq : ∀ f : ℝ, ∃ q : ℚ, f - (q : ℝ) ∈ V := by
      intro f
      have h1 : (fun x : ℝ => f - x) ⁻¹' V ∈ 𝓝 f := by
        have h2 : Tendsto (fun x : ℝ => f - x) (𝓝 f) (𝓝 0) := by
          have := (tendsto_const_nhds (x := f)).sub (tendsto_id (α := ℝ) (x := 𝓝 f))
          rwa [sub_self] at this
        exact h2 (heu hV)
      obtain ⟨q, hq⟩ := Rat.denseRange_cast.mem_nhds h1
      exact ⟨q, hq⟩
    choose q hq using hq
    refine ⟨F.image q, fun s hs => ?_⟩
    obtain ⟨f, hf, h⟩ := hF (a * s) ⟨s, hs, rfl⟩
    refine ⟨q f, Finset.mem_image_of_mem _ hf, subset_closure ⟨a * s - f, h, f - q f, hq f, by ring⟩⟩
  -- Baire: some `E G` contains a ball of the metric of uniform convergence
  have hball : ∃ G : Finset ℚ, ∃ a0 : ℝ, InA δ t a0 ∧ ∃ η : ℝ, 0 < η ∧ ∀ a, InA δ t a → |a - a0| ≤ η →
      (∀ k n, dint ((a - a0) * δ k * t n) ≤ η) → E G a := by
    by_contra hno
    obtain ⟨e, he⟩ := exists_surjective_nat (Finset ℚ)
    have hstep : ∀ (i : ℕ) (p : {p : ℝ × ℝ // InA δ t p.1 ∧ 0 < p.2}),
        ∃ p' : {p : ℝ × ℝ // InA δ t p.1 ∧ 0 < p.2}, |p'.1.1 - p.1.1| ≤ p.1.2 / 4 ∧
          (∀ k n, dint ((p'.1.1 - p.1.1) * δ k * t n) ≤ p.1.2 / 4) ∧ p'.1.2 ≤ p.1.2 / 4 ∧
          ∀ a, |a - p'.1.1| ≤ p'.1.2 → ¬ E (e i) a := by
      rintro i ⟨⟨a, η⟩, ha, hη⟩
      have h4 : 0 < η / 4 := by simp only at hη; positivity
      have h1 : ¬ ∀ a', InA δ t a' → |a' - a| ≤ η / 4 → (∀ k n, dint ((a' - a) * δ k * t n) ≤ η / 4) →
          E (e i) a' := fun h => hno ⟨e i, a, ha, η / 4, h4, h⟩
      push Not at h1
      obtain ⟨a', ha', h2, h3, h5⟩ := h1
      simp only [hE] at h5
      push Not at h5
      obtain ⟨s, hs, h6⟩ := h5
      have hopen : IsOpen {x : ℝ | ∀ g ∈ e i, x * s - (g : ℝ) ∉ C} := by
        have e1 : {x : ℝ | ∀ g ∈ e i, x * s - (g : ℝ) ∉ C} =
            ⋂ g ∈ e i, (fun x : ℝ => x * s - (g : ℝ)) ⁻¹' Cᶜ := by
          ext x
          simp
        rw [e1]
        refine isOpen_biInter_finset fun g _ => ?_
        exact isClosed_closure.isOpen_compl.preimage (by fun_prop)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen a' h6
      refine ⟨⟨(a', min (η / 4) (r / 2)), ha', lt_min h4 (by positivity)⟩, h2, h3, min_le_left _ _,
        fun x hx hEx => ?_⟩
      have h7 : x ∈ Metric.ball a' r := by
        rw [Metric.mem_ball, Real.dist_eq]
        exact lt_of_le_of_lt (hx.trans (min_le_right _ _)) (by linarith)
      obtain ⟨g, hg, h8'⟩ := hEx s hs
      exact hball h7 g hg h8'
    choose next hn1 hn2 hn3 hn4 using hstep
    let seq : ℕ → {p : ℝ × ℝ // InA δ t p.1 ∧ 0 < p.2} :=
      fun i => Nat.rec ⟨(0, 1), inA_zero δ t, one_pos⟩ (fun i p => next i p) i
    have hseq : ∀ i, seq (i + 1) = next i (seq i) := fun i => rfl
    set a : ℕ → ℝ := fun i => (seq i).1.1 with ha
    set η : ℕ → ℝ := fun i => (seq i).1.2 with hη
    have hηpos : ∀ i, 0 < η i := fun i => (seq i).2.2
    have haA : ∀ i, InA δ t (a i) := fun i => (seq i).2.1
    have hd1 : ∀ i, |a (i + 1) - a i| ≤ η i / 4 := fun i => hn1 i (seq i)
    have hd2 : ∀ i k n, dint ((a (i + 1) - a i) * δ k * t n) ≤ η i / 4 := fun i => hn2 i (seq i)
    have hd3 : ∀ i, η (i + 1) ≤ η i / 4 := fun i => hn3 i (seq i)
    have hd4 : ∀ i x, |x - a (i + 1)| ≤ η (i + 1) → ¬ E (e i) x := fun i => hn4 i (seq i)
    -- sums of the steps
    have htail : ∀ i j, |a (i + j) - a i| + η (i + j) / 3 ≤ η i / 3 ∧
        ∀ k n, dint ((a (i + j) - a i) * δ k * t n) + η (i + j) / 3 ≤ η i / 3 := by
      intro i j
      induction j with
      | zero =>
        refine ⟨by simp, fun k n => ?_⟩
        have : dint ((a (i + 0) - a i) * δ k * t n) ≤ 0 := by
          rw [add_zero, sub_self, zero_mul, zero_mul]
          exact (dint_le_abs _).trans (by simp)
        simp only [add_zero] at this ⊢
        linarith
      | succ j ih =>
        have h1 := hd1 (i + j)
        have h3 := hd3 (i + j)
        have e1 : i + (j + 1) = i + j + 1 := by omega
        rw [e1]
        constructor
        · have h5 : |a (i + j + 1) - a i| ≤ |a (i + j + 1) - a (i + j)| + |a (i + j) - a i| :=
            abs_sub_le _ _ _
          have := ih.1
          linarith
        · intro k n
          have e2 : (a (i + j + 1) - a i) * δ k * t n =
              (a (i + j + 1) - a (i + j)) * δ k * t n + (a (i + j) - a i) * δ k * t n := by ring
          rw [e2]
          have h5 := dint_add_le' ((a (i + j + 1) - a (i + j)) * δ k * t n) ((a (i + j) - a i) * δ k * t n)
          have := ih.2 k n
          have := hd2 (i + j) k n
          linarith
    have hcauchy : CauchySeq a := by
      have h1 : ∀ i, η i ≤ ((1 : ℝ) / 4) ^ i := by
        intro i
        induction i with
        | zero => exact le_of_eq (by show (1 : ℝ) = _; simp)
        | succ i ih =>
          refine (hd3 i).trans ?_
          rw [pow_succ]
          linarith
      refine cauchySeq_of_le_geometric ((1 : ℝ) / 4) 1 (by norm_num) fun i => ?_
      rw [dist_comm, Real.dist_eq, one_mul]
      refine (hd1 i).trans ?_
      have := h1 i
      have := hηpos i
      linarith
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hlim : ∀ i, |l - a i| ≤ η i / 3 ∧ ∀ k n, dint ((l - a i) * δ k * t n) ≤ η i / 3 := by
      intro i
      have hl' : Tendsto (fun j => a (i + j) - a i) atTop (𝓝 (l - a i)) := by
        refine Tendsto.sub_const ?_ _
        have := hl.comp (tendsto_add_atTop_nat i)
        simpa [Function.comp_def, add_comm] using this
      refine ⟨le_of_tendsto hl'.abs (Eventually.of_forall fun j => ?_), fun k n => ?_⟩
      · have := (htail i j).1
        have := hηpos (i + j)
        linarith
      · have h2 : Tendsto (fun j => dint ((a (i + j) - a i) * δ k * t n)) atTop
            (𝓝 (dint ((l - a i) * δ k * t n))) :=
          (continuous_dint'.tendsto _).comp ((hl'.mul_const _).mul_const _)
        refine le_of_tendsto h2 (Eventually.of_forall fun j => ?_)
        have := (htail i j).2 k n
        have := hηpos (i + j)
        linarith
    have hlA : InA δ t l := by
      intro ε hε
      obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 4 : ℝ) < 1)
      have h1 : η i ≤ ((1 : ℝ) / 4) ^ i := by
        clear hi
        induction i with
        | zero => exact le_of_eq (by show (1 : ℝ) = _; simp)
        | succ i ih =>
          refine (hd3 i).trans ?_
          rw [pow_succ]
          linarith
      filter_upwards [haA i (ε / 2) (by positivity)] with k hk n
      have e1 : l * δ k * t n = a i * δ k * t n + (l - a i) * δ k * t n := by ring
      rw [e1]
      refine (dint_add_le' _ _).trans ?_
      have := hk n
      have := (hlim i).2 k n
      have := hηpos i
      linarith
    obtain ⟨G, hG⟩ := hcover l hlA
    obtain ⟨i, rfl⟩ := he G
    refine hd4 i l ?_ hG
    have := (hlim (i + 1)).1
    have := hηpos (i + 1)
    linarith
  obtain ⟨G, a0, ha0, η, hη, hG⟩ := hball
  have hE0 : E G a0 := by
    refine hG a0 ha0 (by simpa using hη.le) fun k n => ?_
    rw [sub_self, zero_mul, zero_mul]
    exact (dint_le_abs _).trans (by simpa using hη.le)
  refine ⟨η, hη, ((G ×ˢ G).image fun p => (p.1 : ℝ) - p.2), fun b hb hb1 hb2 s hs => ?_⟩
  have e1 : a0 + b - a0 = b := by ring
  have hE1 : E G (a0 + b) := by
    refine hG _ (inA_add δ t ha0 hb) (by rwa [e1]) fun k n => ?_
    rw [e1]
    exact hb2 k n
  obtain ⟨g1, hg1, c1⟩ := hE1 s hs
  obtain ⟨g2, hg2, c2⟩ := hE0 s hs
  refine ⟨(g1 : ℝ) - g2, Finset.mem_image.2 ⟨(g1, g2), Finset.mem_product.2 ⟨hg1, hg2⟩, rfl⟩, ?_⟩
  -- points of `C` are sums of three members of `V`
  have hC3 : ∀ x ∈ C, ∃ y ∈ V, ∃ z ∈ V, ∃ u ∈ V, x = y + z + u := by
    intro x hx
    have h1 : (fun y : ℝ => x - y) ⁻¹' V ∈ 𝓝 x := by
      have h2 : Tendsto (fun y : ℝ => x - y) (𝓝 x) (𝓝 0) := by
        have := (tendsto_const_nhds (x := x)).sub (tendsto_id (α := ℝ) (x := 𝓝 x))
        rwa [sub_self] at this
      exact h2 (heu hV)
    obtain ⟨w, hw1, y, hy, z, hz, e2⟩ := mem_closure_iff_nhds.1 hx _ h1
    exact ⟨y, hy, z, hz, x - w, hw1, by rw [e2]; ring⟩
  obtain ⟨y1, hy1, z1, hz1, u1, hu1, f1⟩ := hC3 _ c1
  obtain ⟨y2, hy2, z2, hz2, u2, hu2, f2⟩ := hC3 _ c2
  have e2 : b * s - ((g1 : ℝ) - g2) = ((y1 + z1) + (u1 + -y2)) + ((-z2 + -u2) + (0 + 0)) := by
    have : b * s - ((g1 : ℝ) - g2) = ((a0 + b) * s - g1) - (a0 * s - g2) := by ring
    rw [this, f1, f2]
    ring
  rw [e2]
  exact h8 _ hy1 _ hz1 _ hu1 _ (hsym _ hy2) _ (hsym _ hz2) _ (hsym _ hu2) _ h0V _ h0V

/-! ## Rigidity with several classes -/

/-- The position `p` lies in no window of width `h`. -/
def Out (L : ℕ → ℕ) (h p : ℕ) : Prop := ∀ k, L k ≤ p + h → p < L k → False

/-- Arbitrarily large shifts `n` serve all positions of `P` at width `h`. -/
def Fine (L : ℕ → ℕ) (h : ℕ) (P : Finset ℕ) : Prop :=
  ∀ N0 : ℕ, ∃ n : ℕ, N0 ≤ n ∧ ∀ p ∈ P, ∀ k m q : ℕ, n < m →
    q + (n + 1) ^ 2 = (m + 1) ^ 2 + p → L k ≤ q + h → q < L k → False

/-- A sum of powers of two whose exponents avoid `[L - h, L)` is close to an integer after division by `2^L`. -/
lemma dint_sum_pow (Q : Finset ℕ) (L h : ℕ) (hQ : ∀ q ∈ Q, L ≤ q ∨ q + h < L) :
    dint ((∑ q ∈ Q, (2 : ℝ) ^ q) / 2 ^ L) ≤ ((2 : ℝ) ^ h)⁻¹ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun q => L ≤ q), add_div]
  have h1 : (∑ q ∈ Q.filter (fun q => L ≤ q), (2 : ℝ) ^ q) / 2 ^ L =
      ((∑ q ∈ Q.filter (fun q => L ≤ q), (2 : ℤ) ^ (q - L) : ℤ) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq => ?_
    have := (Finset.mem_filter.1 hq).2
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel this]
  have h2 : (∑ q ∈ Q.filter (fun q => ¬ L ≤ q), (2 : ℝ) ^ q) / 2 ^ L ≤ ((2 : ℝ) ^ h)⁻¹ := by
    set R := Q.filter (fun q => ¬ L ≤ q) with hR
    rcases R.eq_empty_or_nonempty with he | ⟨q0, hq0⟩
    · rw [he]
      simp
    have hlt : ∀ q ∈ R, q < L - h := fun q hq => by
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      rcases hQ q hq1 with h3 | h3
      · exact absurd h3 hq2
      · omega
    have hhL : h < L := by
      have := hlt q0 hq0
      omega
    have h3 : ∑ q ∈ R, 2 ^ q < 2 ^ (L - h) := Nat.geomSum_lt le_rfl hlt
    have h4 : (∑ q ∈ R, (2 : ℝ) ^ q) ≤ 2 ^ (L - h) := by exact_mod_cast h3.le
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    refine (mul_le_mul_of_nonneg_right h4 (by positivity)).trans (le_of_eq ?_)
    rw [← pow_add, Nat.sub_add_cancel hhL.le]
  rw [h1, add_comm]
  refine (dint_add_le' _ _).trans ?_
  rw [dint_intZ, add_zero]
  refine (dint_le_abs _).trans ?_
  rw [abs_of_nonneg (by positivity)]
  exact h2

/-- Sums of boundedly many small elements are small. -/
lemma halves_fin (N : Filter ℝ) (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (c : ℕ) :
    ∀ W ∈ N, ∃ V ∈ N, ∀ f : Fin c → ℝ, (∀ i, f i ∈ V) → ∑ i, f i ∈ W := by
  induction c with
  | zero =>
    intro W hW
    exact ⟨W, hW, fun f _ => by simpa using mem_of_mem_nhds (heu hW)⟩
  | succ c ih =>
    intro W hW
    obtain ⟨V0, hV0, _, h0⟩ := hhalf W hW
    obtain ⟨V1, hV1, h1⟩ := ih V0 hV0
    refine ⟨V0 ∩ V1, inter_mem hV0 hV1, fun f hf => ?_⟩
    rw [Fin.sum_univ_succ]
    exact h0 _ (hf 0).1 _ (h1 _ fun i => (hf i.succ).2)

/-- The step from `‖δ_k z‖` small to two sums of powers of two outside the windows. -/
lemma split_near (L : ℕ → ℕ) (hL : StrictMono L) (h K : ℕ) (hK : h + 2 ≤ L K) (z : ℝ)
    (hz : ∀ k, dint (z / 2 ^ L k) ≤ ((2 : ℝ) ^ (h + 3))⁻¹) :
    ∃ s1 s2 : Finset ℕ, (∀ p ∈ s1, L K ≤ p ∧ Out L h p) ∧ (∀ p ∈ s2, L K ≤ p ∧ Out L h p) ∧
      |z - ((∑ p ∈ s1, (2 : ℝ) ^ p) - ∑ p ∈ s2, (2 : ℝ) ^ p)| ≤ 2 ^ L K + 1 := by
  classical
  set M : ℕ → ℕ := fun i => L (K + i) with hM
  have hMmono : StrictMono M := fun a b hab => hL (by omega)
  have hMh : ∀ i, h + 2 ≤ M i := fun i => hK.trans (hL.monotone (Nat.le_add_right _ _))
  set z' : ℤ := round z with hz'
  have hzz : |z - z'| ≤ 1 / 2 := abs_sub_round z
  set t : ℕ → ℤ := fun k => z' - round ((z' : ℝ) / 2 ^ M k) * 2 ^ M k with ht
  have hpos : ∀ k, (0 : ℝ) < 2 ^ M k := fun k => by positivity
  have htb : ∀ k, |t k| ≤ 2 ^ (M k - (h + 2)) := by
    intro k
    have hk := hMh k
    have h1 : dint ((z' : ℝ) / 2 ^ M k) ≤ dint (z / 2 ^ M k) + (1 / 2) / 2 ^ M k := by
      have e1 : (z' : ℝ) / 2 ^ M k = z / 2 ^ M k + -((z - z') / 2 ^ M k) := by ring
      rw [e1]
      refine (dint_add_le' _ _).trans ?_
      rw [dint_neg]
      refine add_le_add le_rfl ((dint_le_abs _).trans ?_)
      rw [abs_div, abs_of_pos (hpos k)]
      exact div_le_div_of_nonneg_right hzz (hpos k).le
    have h2 : (|t k| : ℝ) = 2 ^ M k * dint ((z' : ℝ) / 2 ^ M k) := by
      rw [Two.dint_eq]
      have e1 : (t k : ℝ) = 2 ^ M k * ((z' : ℝ) / 2 ^ M k - round ((z' : ℝ) / 2 ^ M k)) := by
        rw [ht]; push_cast; field_simp
      rw [← Int.cast_abs, Int.cast_abs, e1, abs_mul, abs_of_pos (hpos k)]
    have h3 : (|t k| : ℝ) ≤ 2 ^ (M k - (h + 2)) := by
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add (hz (K + k)) le_rfl)) (hpos k).le
      refine h4.trans ?_
      have e2 : (2 : ℝ) ^ M k = 2 ^ (M k - (h + 2)) * 2 ^ (h + 2) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (2 : ℝ) ^ (h + 3) = 2 ^ (h + 2) * 2 := by rw [← pow_succ]
      have e4 : (2 : ℝ) ^ M k * (((2 : ℝ) ^ (h + 3))⁻¹ + (1 / 2) / 2 ^ M k) =
          2 ^ (M k - (h + 2)) / 2 + 1 / 2 := by
        rw [mul_add]
        congr 1
        · rw [e2, e3]; field_simp
        · field_simp
      rw [e4]
      have h5 : (1 : ℝ) ≤ 2 ^ (M k - (h + 2)) := one_le_pow₀ one_le_two
      linarith
    exact_mod_cast h3
  set u : ℕ → ℤ := fun k => t (k + 1) - t k with hu
  have hudvd : ∀ k, (2 : ℤ) ^ M k ∣ u k := by
    intro k
    have h1 : (2 : ℤ) ^ M k ∣ 2 ^ M (k + 1) := pow_dvd_pow _ (hMmono.monotone (Nat.le_succ k))
    have e1 : u k = round ((z' : ℝ) / 2 ^ M k) * 2 ^ M k -
        round ((z' : ℝ) / 2 ^ M (k + 1)) * 2 ^ M (k + 1) := by
      rw [hu, ht]; ring
    rw [e1]
    exact dvd_sub (Dvd.intro_left _ rfl) (h1.mul_left _)
  have hult : ∀ k, (u k).natAbs ≤ 2 ^ (M (k + 1) - (h + 1)) := by
    intro k
    have h0 := hMh k
    have h0' := hMh (k + 1)
    have hlt := hMmono (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at hlt
    have h1 := htb (k + 1)
    have h2 := htb k
    have h3 : |u k| ≤ |t (k + 1)| + |t k| := abs_sub _ _
    have h4 : (2 : ℤ) ^ (M (k + 1) - (h + 2)) + 2 ^ (M k - (h + 2)) ≤ 2 ^ (M (k + 1) - (h + 1)) := by
      have e1 : (2 : ℤ) ^ (M (k + 1) - (h + 1)) = 2 ^ (M (k + 1) - (h + 2)) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have h5 : (2 : ℤ) ^ (M k - (h + 2)) ≤ 2 ^ (M (k + 1) - (h + 2)) :=
        pow_le_pow_right₀ one_le_two (by omega)
      rw [e1]; omega
    have h6 : ((u k).natAbs : ℤ) ≤ 2 ^ (M (k + 1) - (h + 1)) := by
      rw [Int.natCast_natAbs]; omega
    exact_mod_cast h6
  have hblock : ∀ k, ∃ s : Finset ℕ, (∀ p ∈ s, M k ≤ p ∧ p < M (k + 1) - h) ∧
      (u k).natAbs = ∑ p ∈ s, 2 ^ p := by
    intro k
    have h0' := hMh (k + 1)
    have hdvd : 2 ^ M k ∣ (u k).natAbs := by
      have := Int.natAbs_dvd_natAbs.2 (hudvd k)
      rwa [Int.natAbs_pow] at this
    obtain ⟨q, hq⟩ := hdvd
    have hlt : (u k).natAbs < 2 ^ (M (k + 1) - h) :=
      lt_of_le_of_lt (hult k) (Nat.pow_lt_pow_right one_lt_two (by omega))
    rw [hq] at hlt
    have hqlt : q < 2 ^ (M (k + 1) - h - M k) := by
      rcases le_or_gt (M k) (M (k + 1) - h) with h' | h'
      · have e1 : 2 ^ (M (k + 1) - h) = 2 ^ M k * 2 ^ (M (k + 1) - h - M k) := by
          rw [← pow_add]; congr 1; omega
        rw [e1] at hlt
        exact Nat.lt_of_mul_lt_mul_left hlt
      · have h2 : 2 ^ (M (k + 1) - h) ≤ 2 ^ M k := Nat.pow_le_pow_right two_pos h'.le
        have h3 : q = 0 := by
          by_contra hq0
          have h4 : 2 ^ M k * 1 ≤ 2 ^ M k * q := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hq0)
          omega
        rw [h3]
        positivity
    obtain ⟨s, hs, e⟩ := bits _ q hqlt
    refine ⟨s.image (fun p => M k + p), fun p hp => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      have := Finset.mem_range.1 (hs hj)
      omega
    · rw [hq, Finset.sum_image (fun x _ y _ h => Nat.add_left_cancel h), e, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => (pow_add _ _ _).symm
  choose s hs hsum using hblock
  have hout : ∀ k p, M k ≤ p → p < M (k + 1) - h → Out L h p := by
    intro k p h1 h2 j hj1 hj2
    rcases le_or_gt j (K + k) with h3 | h3
    · have : L j ≤ M k := hL.monotone h3
      omega
    · have : M (k + 1) ≤ L j := hL.monotone (show K + (k + 1) ≤ j by omega)
      omega
  set T := z'.natAbs with hT
  have htT : t T = z' := by
    have h1 : T + 2 ≤ M T := by
      have h2 : ∀ i, i + 2 ≤ M i := by
        intro i
        induction i with
        | zero => have := hMh 0; omega
        | succ i ih =>
          have := hMmono (Nat.lt_succ_self i)
          simp only [Nat.succ_eq_add_one] at this
          omega
      exact h2 T
    have h3 : |(z' : ℝ) / 2 ^ M T| < 1 / 2 := by
      rw [abs_div, abs_of_pos (hpos T), div_lt_iff₀ (hpos T)]
      have h4 : |(z' : ℝ)| = T := by rw [hT, Nat.cast_natAbs, Int.cast_abs]
      rw [h4]
      have h5 : (T : ℝ) < 2 ^ T := by exact_mod_cast Nat.lt_two_pow_self
      have h6 : (2 : ℝ) ^ (T + 2) ≤ 2 ^ M T := pow_le_pow_right₀ one_le_two h1
      rw [pow_add] at h6
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this] at h6
      linarith [pow_pos (two_pos (α := ℝ)) T]
    have h7 : round ((z' : ℝ) / 2 ^ M T) = 0 := by
      rw [round_eq_zero_iff]
      have := abs_lt.1 h3
      exact ⟨by linarith [this.1], this.2⟩
    simp only [ht]
    rw [h7, zero_mul, sub_zero]
  have htel : ∑ k ∈ Finset.range T, u k = z' - t 0 := by
    simp only [hu]
    rw [Finset.sum_range_sub, htT]
  set sp : Finset ℕ := ((Finset.range T).filter (fun k => 0 ≤ u k)).biUnion s with hsp
  set sn : Finset ℕ := ((Finset.range T).filter (fun k => ¬ 0 ≤ u k)).biUnion s with hsn
  have hdisj : ∀ I : Finset ℕ, (I : Set ℕ).PairwiseDisjoint s := by
    intro I k _ l _ hkl
    refine Finset.disjoint_left.2 fun p hpk hpl => hkl ?_
    have h1 := hs k p hpk
    have h2 := hs l p hpl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h3 | h3
    · have := hMmono.monotone (Nat.succ_le_of_lt h3)
      simp only [Nat.succ_eq_add_one] at this
      omega
    · have := hMmono.monotone (Nat.succ_le_of_lt h3)
      simp only [Nat.succ_eq_add_one] at this
      omega
  have hmem : ∀ I : Finset ℕ, ∀ p ∈ I.biUnion s, L K ≤ p ∧ Out L h p := by
    intro I p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.1 hp
    have h1 := hs k p hk
    exact ⟨le_trans (hL.monotone (Nat.le_add_right _ _)) h1.1, hout k p h1.1 h1.2⟩
  have hval : ∀ I : Finset ℕ, ∑ p ∈ I.biUnion s, (2 : ℝ) ^ p = ∑ k ∈ I, ((u k).natAbs : ℝ) := by
    intro I
    rw [Finset.sum_biUnion (hdisj I)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsum k]
    push_cast
    rfl
  refine ⟨sp, sn, hmem _, hmem _, ?_⟩
  have hdiff : (∑ p ∈ sp, (2 : ℝ) ^ p) - ∑ p ∈ sn, (2 : ℝ) ^ p = (z' : ℝ) - t 0 := by
    rw [hsp, hsn, hval, hval]
    have e1 : ∑ k ∈ (Finset.range T).filter (fun k => 0 ≤ u k), ((u k).natAbs : ℝ) =
        ∑ k ∈ (Finset.range T).filter (fun k => 0 ≤ u k), (u k : ℝ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.cast_natAbs, abs_of_nonneg (Finset.mem_filter.1 hk).2]
    have e2 : ∑ k ∈ (Finset.range T).filter (fun k => ¬ 0 ≤ u k), ((u k).natAbs : ℝ) =
        -∑ k ∈ (Finset.range T).filter (fun k => ¬ 0 ≤ u k), (u k : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.cast_natAbs, abs_of_neg (not_le.1 (Finset.mem_filter.1 hk).2), Int.cast_neg]
    rw [e1, e2, sub_neg_eq_add, Finset.sum_filter_add_sum_filter_not]
    have := congrArg (fun m : ℤ => (m : ℝ)) htel
    push_cast at this
    exact this
  rw [hdiff]
  have h0 : (|t 0| : ℝ) ≤ 2 ^ L K := by
    have h1 : |t 0| ≤ 2 ^ L K :=
      (htb 0).trans (pow_le_pow_right₀ one_le_two (show M 0 - (h + 2) ≤ L K by simp only [hM, add_zero]; omega))
    exact_mod_cast h1
  have e3 : z - ((z' : ℝ) - t 0) = (z - z') + t 0 := by ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  linarith

lemma rig_of_classes_filter (L : ℕ → ℕ) (hL : StrictMono L)
    (hdy : ∀ z j : ℕ, InA (dyseq L) sT ((z : ℝ) / 2 ^ j)) (c : ℕ)
    (hcol : ∀ h : ℕ, ∃ p1 : ℕ, ∃ col : ℕ → Fin c, ∀ P : Finset ℕ, (∀ p ∈ P, p1 ≤ p) → (∀ p ∈ P, Out L h p) →
      (∀ p ∈ P, ∀ q ∈ P, col p = col q) → Fine L h P) (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (htb : ∀ a : ℝ, InA (dyseq L) sT a → Tb N (dil a Sset)) (W : Set ℝ) (hW : W ∈ N) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : Finset ℝ, ∀ x : ℝ, (∀ k, dint (dyseq L k * x) ≤ ε) → ∃ f ∈ F, x - f ∈ W := by
  classical
  by_contra hcon
  have hbad : ∀ (i : ℕ) (F : Finset ℝ), ∃ x : ℝ,
      (∀ k, dint (dyseq L k * x) ≤ (1 : ℝ) / (8 * (i + 1))) ∧ ∀ f ∈ F, x - f ∉ W := by
    intro i F
    by_contra h
    refine hcon ⟨1 / (8 * (i + 1)), by positivity, F, fun x hx => ?_⟩
    by_contra h'
    exact h ⟨x, hx, fun f hf hfW => h' ⟨f, hf, hfW⟩⟩
  choose pick hpick using hbad
  let g : ℕ → Finset ℝ := fun n => Nat.rec ∅ (fun n G => insert (pick n G) G) n
  have hg' : ∀ n, g (n + 1) = insert (pick n (g n)) (g n) := fun n => rfl
  set x : ℕ → ℝ := fun n => pick n (g n) with hx
  have hmono : Monotone g := monotone_nat_of_le_succ fun n => by rw [hg']; exact Finset.subset_insert _ _
  have hmem : ∀ j n, j < n → x j ∈ g n := by
    intro j n hjn
    refine hmono (Nat.succ_le_of_lt hjn) ?_
    rw [Nat.succ_eq_add_one, hg']
    exact Finset.mem_insert_self _ _
  have hsmall : ∀ i k, dint (x i / 2 ^ L k) ≤ (1 : ℝ) / (8 * (i + 1)) := fun i k => by
    rw [← dyseq_mul]
    exact (hpick i (g i)).1 k
  have hsep : ∀ j n, j < n → x n - x j ∉ W := fun j n hjn => (hpick n (g n)).2 _ (hmem j n hjn)
  -- neighbourhoods
  obtain ⟨V, hV, hsym, h8⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hV)
  obtain ⟨V1, hV1, hV1c⟩ := halves_fin N hhalf heu c V hV
  obtain ⟨η, hη, F, hF⟩ := unif (dyseq L) sT Sset N hhalf heu htb V1 hV1
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  rw [one_div, inv_pow] at hh
  obtain ⟨p1, col, hfine⟩ := hcol h
  -- one class is covered
  have hclass : ∀ P : Finset ℕ, (∀ p ∈ P, p1 ≤ p) → (∀ p ∈ P, Out L h p) → (∀ p ∈ P, ∀ q ∈ P, col p = col q) →
      ∃ f ∈ F, (∑ p ∈ P, (2 : ℝ) ^ p) - f ∈ V1 := by
    intro P h1 h2 h3
    obtain ⟨n, hnbig, hn2⟩ := hfine P h1 h2 h3 (P.sup id + h + 2)
    have hn1 : ∀ p ∈ P, p + h + 2 ≤ n := fun p hp => by
      have : p ≤ P.sup id := Finset.le_sup (f := id) hp
      omega
    have hnsq : n ≤ (n + 1) ^ 2 := le_trans (Nat.le_succ n) (Nat.le_self_pow two_ne_zero _)
    have hn1' : ∀ p ∈ P, p + h ≤ (n + 1) ^ 2 := fun p hp => by
      have := hn1 p hp
      omega
    set y : ℝ := ∑ p ∈ P, (2 : ℝ) ^ p with hy
    set e := (n + 1) ^ 2 with he
    have hsT : sT n = (2 : ℝ) ^ e := rfl
    have hhη : ((2 : ℝ) ^ h)⁻¹ ≤ η / 2 := by linarith
    have hysmall : y / 2 ^ e ≤ 2 * ((2 : ℝ) ^ h)⁻¹ := by
      rcases P.eq_empty_or_nonempty with h0 | ⟨p0, hp0⟩
      · rw [hy, h0]
        simp
      have hhe : h ≤ e := le_trans (Nat.le_add_left _ _) (hn1' p0 hp0)
      have h4 : ∑ p ∈ P, 2 ^ p < 2 ^ (e - h + 1) :=
        Nat.geomSum_lt le_rfl fun p hp => by
          have := hn1' p hp
          omega
      have h5 : y ≤ 2 ^ (e - h + 1) := by
        rw [hy]
        exact_mod_cast h4.le
      rw [div_le_iff₀ (by positivity)]
      refine h5.trans (le_of_eq ?_)
      have e1 : (2 : ℝ) ^ e = 2 ^ (e - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hhe]
      rw [e1, pow_succ]
      field_simp
    have hy0 : 0 ≤ y := by rw [hy]; positivity
    have hbA : InA (dyseq L) sT (y / 2 ^ e) := by
      have := hdy (∑ p ∈ P, 2 ^ p) e
      push_cast at this
      exact this
    have hb1 : |y / 2 ^ e| ≤ η := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hb2 : ∀ k m, dint (y / 2 ^ e * dyseq L k * sT m) ≤ η := by
      intro k m
      have hsm : sT m = (2 : ℝ) ^ ((m + 1) ^ 2) := rfl
      rcases lt_trichotomy m n with hmn | hmn | hmn
      · have hgap : (m + 1) ^ 2 + n + (n + 1) ≤ e := by
          have h1 : (m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
          have h2 : e = n ^ 2 + n + (n + 1) := by rw [he]; ring
          omega
        have h4 : y * 2 ^ ((m + 1) ^ 2) * ((2 : ℝ) ^ h) ≤ 2 ^ e := by
          have h5 : y ≤ 2 ^ (n - h) := by
            have h6 : ∑ p ∈ P, 2 ^ p < 2 ^ (n - h) := Nat.geomSum_lt le_rfl fun p hp => by
              have := hn1 p hp
              omega
            rw [hy]
            exact_mod_cast h6.le
          refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 (by positivity))
            (by positivity)).trans ?_
          rw [← pow_add, ← pow_add]
          refine pow_le_pow_right₀ one_le_two ?_
          rcases P.eq_empty_or_nonempty with h0 | ⟨p0, hp0⟩
          · have : h ≤ n + 1 + h := by omega
            have h7 : n - h + (m + 1) ^ 2 + h ≤ (m + 1) ^ 2 + n + h := by omega
            have h8 : h ≤ n := by
              have := hnbig
              omega
            omega
          · have := hn1 p0 hp0
            omega
        have h9 : y / 2 ^ e * dyseq L k * sT m ≤ ((2 : ℝ) ^ h)⁻¹ := by
          have h10 : y / 2 ^ e * sT m ≤ ((2 : ℝ) ^ h)⁻¹ := by
            rw [hsm, div_mul_eq_mul_div, div_le_iff₀ (by positivity), inv_mul_eq_div,
              le_div_iff₀ (by positivity)]
            exact h4
          have h11 : dyseq L k ≤ 1 := by
            unfold dyseq
            exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
          calc y / 2 ^ e * dyseq L k * sT m = (y / 2 ^ e * sT m) * dyseq L k := by ring
            _ ≤ ((2 : ℝ) ^ h)⁻¹ * 1 := mul_le_mul h10 h11 (by unfold dyseq; positivity) (by positivity)
            _ = _ := mul_one _
        refine (dint_le_abs _).trans ?_
        rw [abs_of_nonneg (by rw [hsm]; unfold dyseq; positivity)]
        linarith
      · have e1 : y / 2 ^ e * dyseq L k * sT m = y / 2 ^ L k := by
          rw [hsm, hmn, ← he]
          unfold dyseq
          field_simp
        rw [e1, hy]
        refine (dint_sum_pow P (L k) h fun p hp => ?_).trans (by linarith)
        by_contra hc
        push Not at hc
        exact h2 p hp k hc.2 hc.1
      · have hem : e ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hem
        have e1 : y / 2 ^ e * dyseq L k * sT m = (∑ q ∈ P.image (fun p => p + d), (2 : ℝ) ^ q) / 2 ^ L k := by
          rw [Finset.sum_image (fun a _ b _ hab => Nat.add_right_cancel hab)]
          simp only [pow_add]
          rw [← Finset.sum_mul, ← hy, hsm, hd, pow_add]
          unfold dyseq
          field_simp
        rw [e1]
        refine (dint_sum_pow _ (L k) h fun q hq => ?_).trans (by linarith)
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        by_contra hc
        push Not at hc
        exact hn2 p hp k m (p + d) hmn (by omega) hc.2 hc.1
    have hS : sT n ∈ Sset := by simpa using sign_mem_Sset (c := 1) (by simp) n
    obtain ⟨f, hf, hfV⟩ := hF _ hbA hb1 hb2 _ hS
    have e2 : y / 2 ^ e * sT n = y := by
      rw [hsT]
      field_simp
    rw [e2] at hfV
    exact ⟨f, hf, hfV⟩
  -- all positions outside the windows
  set FF : Finset ℝ := (Fintype.piFinset fun _ : Fin c => F).image fun f => ∑ i, f i with hFF
  have hall : ∀ P : Finset ℕ, (∀ p ∈ P, p1 ≤ p) → (∀ p ∈ P, Out L h p) →
      ∃ f ∈ FF, (∑ p ∈ P, (2 : ℝ) ^ p) - f ∈ V := by
    intro P h1 h2
    have hi : ∀ i : Fin c, ∃ f ∈ F, (∑ p ∈ P.filter (fun p => col p = i), (2 : ℝ) ^ p) - f ∈ V1 := by
      intro i
      refine hclass _ (fun p hp => h1 p (Finset.mem_filter.1 hp).1) (fun p hp => h2 p (Finset.mem_filter.1 hp).1)
        fun p hp q hq => ?_
      rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hq).2]
    choose f hf hfV using hi
    refine ⟨∑ i, f i, Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 hf, rfl⟩, ?_⟩
    have e1 : (∑ p ∈ P, (2 : ℝ) ^ p) - ∑ i, f i =
        ∑ i, ((∑ p ∈ P.filter (fun p => col p = i), (2 : ℝ) ^ p) - f i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_fiberwise]
    rw [e1]
    exact hV1c _ hfV
  -- the covering step
  obtain ⟨K, hK⟩ : ∃ K, p1 + h + 2 ≤ L K := ⟨p1 + h + 2, hL.id_le _⟩
  obtain ⟨H, hH⟩ := tb_interval N heu (2 ^ L K + 1) V hV
  set G : Finset ℝ := ((FF ×ˢ FF) ×ˢ H).image fun p => p.1.1 - p.1.2 + p.2 with hG
  have hcov : ∀ i, 2 ^ h ≤ i → ∃ f ∈ G, ∃ v1 ∈ V, ∃ v2 ∈ V, ∃ v3 ∈ V, x i - f = v1 - v2 + v3 := by
    intro i hi
    have hz : ∀ k, dint (x i / 2 ^ L k) ≤ ((2 : ℝ) ^ (h + 3))⁻¹ := by
      intro k
      refine (hsmall i k).trans ?_
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      have h1 : (2 : ℝ) ^ h ≤ i + 1 := by
        have : 2 ^ h ≤ i + 1 := by omega
        exact_mod_cast this
      rw [pow_add]
      have : (2 : ℝ) ^ 3 = 8 := by norm_num
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    obtain ⟨s1, s2, hs1, hs2, herr⟩ := split_near L hL h K (by omega) (x i) hz
    obtain ⟨g1, hg1, k1⟩ := hall s1 (fun p hp => by have := (hs1 p hp).1; omega) fun p hp => (hs1 p hp).2
    obtain ⟨g2, hg2, k2⟩ := hall s2 (fun p hp => by have := (hs2 p hp).1; omega) fun p hp => (hs2 p hp).2
    obtain ⟨e, he, k3⟩ := hH _ (abs_le.1 herr)
    refine ⟨g1 - g2 + e, Finset.mem_image.2 ⟨((g1, g2), e),
      Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hg1, hg2⟩, he⟩, rfl⟩, _, k1, _, k2, _, k3, by ring⟩
  have hcov' : ∀ i, ∃ f ∈ G, ∃ v1 ∈ V, ∃ v2 ∈ V, ∃ v3 ∈ V, x (2 ^ h + i) - f = v1 - v2 + v3 :=
    fun i => hcov _ (Nat.le_add_right _ _)
  choose f hfG v1 hv1 v2 hv2 v3 hv3 hxf using hcov'
  obtain ⟨j, n, hjn, hfe⟩ : ∃ j n : ℕ, j < n ∧ f j = f n := by
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨f i, hfG i⟩ : G))
    have he' : f a = f b := by simpa using congrArg Subtype.val he
    rcases lt_or_gt_of_ne hab with h' | h'
    · exact ⟨a, b, h', he'⟩
    · exact ⟨b, a, h', he'.symm⟩
  refine hsep (2 ^ h + j) (2 ^ h + n) (by omega) ?_
  have e1 : x (2 ^ h + n) - x (2 ^ h + j) =
      ((v1 n + -v2 n) + (v3 n + -v1 j)) + ((v2 j + -v3 j) + (0 + 0)) := by
    have h1 := hxf n
    have h2 := hxf j
    rw [hfe] at h2
    have e2 : x (2 ^ h + n) - x (2 ^ h + j) = (x (2 ^ h + n) - f n) - (x (2 ^ h + j) - f n) := by ring
    rw [e2, h1, h2]; ring
  rw [e1]
  exact h8 _ (hv1 n) _ (hsym _ (hv2 n)) _ (hv3 n) _ (hsym _ (hv1 j)) _ (hv2 j) _ (hsym _ (hv3 j)) _ h0V _ h0V

/-- **Rigidity with finitely many classes of positions and bounded widths.** -/
theorem rig_of_classes (L : ℕ → ℕ) (hL : StrictMono L)
    (hdy : ∀ z j : ℕ, InA (dyseq L) sT ((z : ℝ) / 2 ^ j)) (c : ℕ)
    (hcol : ∀ h : ℕ, ∃ p1 : ℕ, ∃ col : ℕ → Fin c, ∀ P : Finset ℕ, (∀ p ∈ P, p1 ≤ p) → (∀ p ∈ P, Out L h p) →
      (∀ p ∈ P, ∀ q ∈ P, col p = col q) → Fine L h P) : Rig (dyseq L) := by
  intro γ hg heu htb W hW
  exact rig_of_classes_filter L hL hdy c hcol (@nhds ℝ γ 0) (group_half γ hg) heu htb W hW

end Three
end PVG
