import LeanCheck.PVGSequences

/-!
# PVG: independence of the limits of a sparse sequence (Lean check)

Scope. Formal counterpart of Lemma G and Theorem A of the research note
`PVG_Q95_independence_2026-11-07.md` (Question 9.5 of `PVG_v11`), in the concrete setting of
`PVGSequences` (`K = Hom(ℝ, 𝕋)`, `e`, the limits `L y U` along free ultrafilters):

* `arcs`, `arcs_signed` (Lemma G): if `a k > 0`, `0 < α ≤ 1`, `1 + α ≤ R α` and `R a k ≤ a (k+1)`, then for
  any prescribed centres `c k` there is `b` with `0 ≤ b ≤ 2 / a 0` and `|b a k - c k - n| ≤ α/2` for some
  integer `n`, for every `k` (the signed version is for a sequence `z` with `R |z k| ≤ |z (k+1)|`).
* `independence` (Theorem A): for a real sequence `y` with all `y k ≠ 0` and `|y (k+1)| / |y k| → ∞`,
  pairwise distinct free ultrafilters `W i` (`i : Fin n`) and real coefficients `γ i` not all zero,
  `∑ γ i • L y (W i)` is not of the form `e x`.
* `independence_finset`: the same for a finite set of free ultrafilters; in particular
  (`x = 0`) the vectors `L y U` (`U` free) are linearly independent over `ℝ` and their real span meets
  `e(ℝ)` only in `0`.

Not formalized: the consequences for the retraction `π` and for Question 9.5 (still open), Theorem B,
and the density property. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the research note requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-! ### Lemma G -/

lemma fit_arc {u v c α : ℝ} (h : 1 + α ≤ v - u) :
    ∃ j : ℤ, u ≤ j + c - α / 2 ∧ j + c + α / 2 ≤ v := by
  refine ⟨⌈u - c + α / 2⌉, ?_, ?_⟩
  · have := Int.le_ceil (u - c + α / 2); linarith
  · have := Int.ceil_lt_add_one (u - c + α / 2); linarith

/-- An interval of length `α / a k` all of whose points `b` satisfy the `k`-th arc condition. -/
structure ArcIv (a : ℕ → ℝ) (α : ℝ) (c : ℕ → ℝ) (k : ℕ) where
  l : ℝ
  r : ℝ
  len : r - l = α / a k
  good : ∀ b ∈ Set.Icc l r, ∃ n : ℤ, |b * a k - c k - n| ≤ α / 2

section ArcChain

variable {a : ℕ → ℝ} {α : ℝ} {c : ℕ → ℝ}

lemma arc_first (ha : ∀ k, 0 < a k) (hα1 : α ≤ 1) :
    ∃ J : ArcIv a α c 0, 0 ≤ J.l ∧ J.r ≤ 2 / a 0 := by
  obtain ⟨j, h1, h2⟩ := fit_arc (u := 0) (v := 2) (c := c 0) (α := α) (by linarith)
  have hp := ha 0
  refine ⟨⟨(j + c 0 - α / 2) / a 0, (j + c 0 + α / 2) / a 0, ?_, ?_⟩, ?_, ?_⟩
  · ring
  · intro b hb
    refine ⟨j, ?_⟩
    rw [Set.mem_Icc, div_le_iff₀ hp, le_div_iff₀ hp] at hb
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  · exact div_nonneg (by linarith) hp.le
  · show (j + c 0 + α / 2) / a 0 ≤ 2 / a 0
    exact div_le_div_of_nonneg_right h2 hp.le

lemma arc_next (ha : ∀ k, 0 < a k) {R : ℝ} (hα : 0 < α) (hR : 1 + α ≤ R * α)
    (hr : ∀ k, R * a k ≤ a (k + 1)) (k : ℕ) (J : ArcIv a α c k) :
    ∃ J' : ArcIv a α c (k + 1), J.l ≤ J'.l ∧ J'.r ≤ J.r := by
  have hk := ha k
  have hk1 := ha (k + 1)
  have hlen : 1 + α ≤ a (k + 1) * J.r - a (k + 1) * J.l := by
    have h1 : a (k + 1) * J.r - a (k + 1) * J.l = a (k + 1) * (α / a k) := by
      rw [← mul_sub, J.len]
    rw [h1]
    have h2 : a (k + 1) * (α / a k) = α * (a (k + 1) / a k) := by ring
    rw [h2]
    have h3 : R ≤ a (k + 1) / a k := by rw [le_div_iff₀ hk]; exact hr k
    have h4 := mul_le_mul_of_nonneg_left h3 hα.le
    linarith
  obtain ⟨j, h1, h2⟩ := fit_arc (u := a (k + 1) * J.l) (v := a (k + 1) * J.r) (c := c (k + 1)) hlen
  refine ⟨⟨(j + c (k + 1) - α / 2) / a (k + 1), (j + c (k + 1) + α / 2) / a (k + 1), ?_, ?_⟩, ?_, ?_⟩
  · ring
  · intro b hb
    refine ⟨j, ?_⟩
    rw [Set.mem_Icc, div_le_iff₀ hk1, le_div_iff₀ hk1] at hb
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  · show J.l ≤ (j + c (k + 1) - α / 2) / a (k + 1)
    rw [le_div_iff₀ hk1]; linarith
  · show (j + c (k + 1) + α / 2) / a (k + 1) ≤ J.r
    rw [div_le_iff₀ hk1]; linarith

/-- The nested chain of arc intervals. -/
noncomputable def arcChain (ha : ∀ k, 0 < a k) {R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : 1 + α ≤ R * α) (hr : ∀ k, R * a k ≤ a (k + 1)) : (k : ℕ) → ArcIv a α c k
  | 0 => Classical.choose (arc_first (c := c) ha hα1)
  | k + 1 => Classical.choose (arc_next ha hα hR hr k (arcChain ha hα hα1 hR hr k))

lemma arcChain_zero (ha : ∀ k, 0 < a k) {R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : 1 + α ≤ R * α) (hr : ∀ k, R * a k ≤ a (k + 1)) :
    0 ≤ (arcChain (c := c) ha hα hα1 hR hr 0).l ∧ (arcChain (c := c) ha hα hα1 hR hr 0).r ≤ 2 / a 0 :=
  Classical.choose_spec (arc_first (c := c) ha hα1)

lemma arcChain_succ (ha : ∀ k, 0 < a k) {R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : 1 + α ≤ R * α) (hr : ∀ k, R * a k ≤ a (k + 1)) (k : ℕ) :
    (arcChain (c := c) ha hα hα1 hR hr k).l ≤ (arcChain (c := c) ha hα hα1 hR hr (k + 1)).l ∧
      (arcChain (c := c) ha hα hα1 hR hr (k + 1)).r ≤ (arcChain (c := c) ha hα hα1 hR hr k).r :=
  Classical.choose_spec (arc_next ha hα hR hr k (arcChain (c := c) ha hα hα1 hR hr k))

end ArcChain

/-- **Lemma G** (prescribed arcs). -/
theorem arcs {a : ℕ → ℝ} {α R : ℝ} (c : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hα : 0 < α) (hα1 : α ≤ 1)
    (hR : 1 + α ≤ R * α) (hr : ∀ k, R * a k ≤ a (k + 1)) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 2 / a 0 ∧ ∀ k, ∃ n : ℤ, |b * a k - c k - n| ≤ α / 2 := by
  set J := arcChain (c := c) ha hα hα1 hR hr with hJ
  have hl : Monotone (fun k => (J k).l) :=
    monotone_nat_of_le_succ fun k => (arcChain_succ (c := c) ha hα hα1 hR hr k).1
  have hrr : Antitone (fun k => (J k).r) :=
    antitone_nat_of_succ_le fun k => (arcChain_succ (c := c) ha hα hα1 hR hr k).2
  have hlr : ∀ k, (J k).l ≤ (J k).r := by
    intro k
    have h1 := (J k).len
    have h2 : 0 < α / a k := div_pos hα (ha k)
    linarith
  have hlr' : ∀ k j, (J k).l ≤ (J j).r := by
    intro k j
    rcases le_total k j with h | h
    · exact (hl h).trans (hlr j)
    · exact (hlr k).trans (hrr h)
  have hbdd : BddAbove (Set.range fun k => (J k).l) := ⟨(J 0).r, by
    rintro _ ⟨k, rfl⟩; exact hlr' k 0⟩
  set b := ⨆ k, (J k).l with hb
  have hb1 : ∀ k, (J k).l ≤ b := fun k => le_ciSup hbdd k
  have hb2 : ∀ k, b ≤ (J k).r := fun k => ciSup_le fun j => hlr' j k
  have h0 := arcChain_zero (c := c) ha hα hα1 hR hr
  refine ⟨b, h0.1.trans (hb1 0), (hb2 0).trans h0.2, fun k => ?_⟩
  exact (J k).good b ⟨hb1 k, hb2 k⟩

/-- Lemma G for signed sequences. -/
theorem arcs_signed {z : ℕ → ℝ} {α R : ℝ} (c : ℕ → ℝ) (hz : ∀ k, z k ≠ 0) (hα : 0 < α)
    (hα1 : α ≤ 1) (hR : 1 + α ≤ R * α) (hr : ∀ k, R * |z k| ≤ |z (k + 1)|) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 2 / |z 0| ∧ ∀ k, ∃ n : ℤ, |b * z k - c k - n| ≤ α / 2 := by
  obtain ⟨b, hb0, hb1, hb⟩ := arcs (a := fun k => |z k|) (fun k => if 0 < z k then c k else -c k)
    (fun k => abs_pos.2 (hz k)) hα hα1 hR hr
  refine ⟨b, hb0, hb1, fun k => ?_⟩
  obtain ⟨n, hn⟩ := hb k
  have hn' : |b * |z k| - (if 0 < z k then c k else -c k) - n| ≤ α / 2 := hn
  by_cases hk : 0 < z k
  · refine ⟨n, ?_⟩
    have hite : (if 0 < z k then c k else -c k) = c k := by simp [hk]
    rw [hite, abs_of_pos hk] at hn'
    exact hn'
  · have hneg : z k < 0 := lt_of_le_of_ne (not_lt.1 hk) (hz k)
    refine ⟨-n, ?_⟩
    have hite : (if 0 < z k then c k else -c k) = -c k := by simp [hk]
    rw [hite, abs_of_neg hneg] at hn'
    have e1 : b * z k - c k - ((-n : ℤ) : ℝ) = -(b * -z k - -c k - n) := by push_cast; ring
    rw [e1, abs_neg]
    exact hn'

/-! ### Disjoint neighbourhoods of finitely many distinct ultrafilters -/

lemma exists_disjoint_family {n : ℕ} (W : Fin n → Ultrafilter ℕ) (hW : Function.Injective W) :
    ∃ S : Fin n → Set ℕ, (∀ i, S i ∈ W i) ∧ ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
  have hsep : ∀ i j : Fin n, i ≠ j → ∃ T : Set ℕ, T ∈ W i ∧ Tᶜ ∈ W j :=
    fun i j h => exists_separating (fun h' => h (hW h'))
  choose! T hT using hsep
  let P : Fin n → Fin n → Set ℕ := fun i j =>
    if i < j then T i j else if j < i then (T j i)ᶜ else Set.univ
  have hP : ∀ i j, P i j ∈ W i := by
    intro i j
    by_cases h1 : i < j
    · simp only [P, h1, ↓reduceIte]; exact (hT i j h1.ne).1
    · by_cases h2 : j < i
      · simp only [P, h1, h2, ↓reduceIte]; exact (hT j i h2.ne).2
      · simp only [P, h1, h2, ↓reduceIte]; exact Filter.univ_mem
  refine ⟨fun i => ⋂ j, P i j, fun i => (Filter.iInter_mem).2 (fun j => hP i j), ?_⟩
  intro i j hij
  wlog h : i < j generalizing i j
  · exact (this j i hij.symm (lt_of_le_of_ne (not_lt.1 h) hij.symm)).symm
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h1 : x ∈ P i j := Set.mem_iInter.1 hxi j
  have h2 : x ∈ P j i := Set.mem_iInter.1 hxj i
  have e1 : P i j = T i j := by simp [P, h]
  have e2 : P j i = (T i j)ᶜ := by simp [P, h, not_lt.2 h.le]
  rw [e1] at h1
  rw [e2] at h2
  exact h2 h1

/-! ### Theorem A -/

lemma norm_circle_le_sub_int (t : ℝ) (m : ℤ) : ‖(t : AddCircle (1 : ℝ))‖ ≤ |t - m| := by
  rw [AddCircle.norm_eq]
  simpa using round_le t m

lemma norm_circle_half : (1 : ℝ) / 2 ≤ ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq]
  have : round ((1 : ℝ)⁻¹ * (1 / 2 : ℝ)) = 1 := by
    rw [round_eq]; norm_num
  rw [this]; norm_num

lemma exists_pow_le_abs (y : ℕ → ℝ) (m1 : ℕ) (h : ∀ k, m1 ≤ k → 2 * |y k| ≤ |y (k + 1)|) (j : ℕ) :
    2 ^ j * |y m1| ≤ |y (m1 + j)| := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := h (m1 + j) (by omega)
    calc 2 ^ (j + 1) * |y m1| = 2 * (2 ^ j * |y m1|) := by ring
      _ ≤ 2 * |y (m1 + j)| := by linarith
      _ ≤ |y (m1 + j + 1)| := this
      _ = |y (m1 + (j + 1))| := by rw [add_assoc]

/-- **Theorem A.** For a real sequence `y` with `|y (k+1)| / |y k| → ∞`, distinct free ultrafilters
`W 0, …, W (n-1)` and real coefficients `γ` not all zero, `∑ γ i • L y (W i)` is not of the form `e x`. -/
theorem independence {n : ℕ} (y : ℕ → ℝ) (hy0 : ∀ k, y k ≠ 0)
    (hy : Tendsto (fun k => |y (k + 1)| / |y k|) atTop atTop)
    (W : Fin n → Ultrafilter ℕ) (hWi : Function.Injective W) (hWf : ∀ i, Free (W i))
    (γ : Fin n → ℝ) (hγ : ∃ i, γ i ≠ 0) (x : ℝ) :
    ∑ i, γ i • L y (W i) ≠ e x := by
  classical
  intro hsum
  obtain ⟨i0, hi0⟩ := hγ
  have hnpos : 0 < n := Fin.pos i0
  obtain ⟨S, hSW, hSd⟩ := exists_disjoint_family W hWi
  -- nonzero multipliers
  set γ' : Fin n → ℝ := fun i => if γ i = 0 then 1 else γ i with hγ'
  have hγ'ne : ∀ i, γ' i ≠ 0 := by
    intro i
    by_cases h : γ i = 0
    · simp [hγ', h]
    · simp [hγ', h]
  have hγ'eq : ∀ i, γ i ≠ 0 → γ' i = γ i := by
    intro i h; simp [hγ', h]
  let g : ℕ → ℝ := fun k => if h : ∃ i, k ∈ S i then γ' (Classical.choose h) else 1
  have hg : ∀ i k, k ∈ S i → g k = γ' i := by
    intro i k hk
    have h : ∃ i, k ∈ S i := ⟨i, hk⟩
    have hspec := Classical.choose_spec h
    have hch : Classical.choose h = i := by
      by_contra hne
      exact Set.disjoint_left.1 (hSd _ _ hne) hspec hk
    show (if h : ∃ i, k ∈ S i then γ' (Classical.choose h) else 1) = γ' i
    simp only [h, ↓reduceDIte, hch]
  have hgnone : ∀ k, (¬ ∃ i, k ∈ S i) → g k = 1 := by
    intro k hk
    show (if h : ∃ i, k ∈ S i then γ' (Classical.choose h) else 1) = 1
    simp only [hk, ↓reduceDIte]
  -- bounds for the multipliers
  set M : ℝ := 1 + ∑ i, |γ' i| with hM
  set μ : ℝ := 1 / (1 + ∑ i, |γ' i|⁻¹) with hμ
  have hsum1 : 0 ≤ ∑ i, |γ' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsum2 : 0 ≤ ∑ i, |γ' i|⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.2 (abs_nonneg _)
  have hMpos : 1 ≤ M := by rw [hM]; linarith
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one (by linarith)]; linarith
  have hγM : ∀ i, |γ' i| ≤ M := by
    intro i
    have := Finset.single_le_sum (f := fun i => |γ' i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hM]; linarith
  have hγμ : ∀ i, μ ≤ |γ' i| := by
    intro i
    have hpos : 0 < |γ' i|⁻¹ := inv_pos.2 (abs_pos.2 (hγ'ne i))
    have hle : |γ' i|⁻¹ ≤ 1 + ∑ i, |γ' i|⁻¹ := by
      have := Finset.single_le_sum (f := fun i => |γ' i|⁻¹) (fun i _ => inv_nonneg.2 (abs_nonneg _))
        (Finset.mem_univ i)
      linarith
    have h3 := one_div_le_one_div_of_le hpos hle
    have h4 : 1 / |γ' i|⁻¹ = |γ' i| := by rw [one_div, inv_inv]
    rw [h4] at h3
    rw [hμ]; exact h3
  have hgM : ∀ k, |g k| ≤ M := by
    intro k
    by_cases h : ∃ i, k ∈ S i
    · obtain ⟨i, hi⟩ := h; rw [hg i k hi]; exact hγM i
    · rw [hgnone k h]; simpa using hMpos
  have hgμ : ∀ k, μ ≤ |g k| := by
    intro k
    by_cases h : ∃ i, k ∈ S i
    · obtain ⟨i, hi⟩ := h; rw [hg i k hi]; exact hγμ i
    · rw [hgnone k h]; simpa using hμ1
  have hgne : ∀ k, g k ≠ 0 := fun k h => by
    have := hgμ k; rw [h] at this; simp at this; linarith
  -- the sequence z = g y
  set z : ℕ → ℝ := fun k => g k * y k with hzdef
  have hzne : ∀ k, z k ≠ 0 := fun k => mul_ne_zero (hgne k) (hy0 k)
  have hzabs : ∀ k, |z k| = |g k| * |y k| := fun k => abs_mul _ _
  -- arc parameters
  set α : ℝ := 1 / (4 * n) with hα
  have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hnpos
  have hαpos : 0 < α := by rw [hα]; positivity
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one (by positivity)]; linarith
  set R : ℝ := (1 + α) / α with hRdef
  have hR : 1 + α ≤ R * α := by
    rw [hRdef, div_mul_cancel₀ _ hαpos.ne']
  -- the ratio condition from some index on
  obtain ⟨m1, hm1⟩ := eventually_atTop.1 (hy.eventually_ge_atTop (max 2 (R * M / μ)))
  have hm1a : ∀ k, m1 ≤ k → 2 * |y k| ≤ |y (k + 1)| := by
    intro k hk
    have := (le_max_left _ _).trans (hm1 k hk)
    rw [le_div_iff₀ (abs_pos.2 (hy0 k))] at this
    exact this
  have hm1b : ∀ k, m1 ≤ k → R * |z k| ≤ |z (k + 1)| := by
    intro k hk
    have h1 := (le_max_right _ _).trans (hm1 k hk)
    rw [le_div_iff₀ (abs_pos.2 (hy0 k))] at h1
    have hRpos : 0 < R := by rw [hRdef]; positivity
    rw [hzabs, hzabs]
    have h2 : R * (|g k| * |y k|) ≤ R * M * |y k| := by
      have := mul_le_mul_of_nonneg_right (hgM k) (abs_nonneg (y k))
      nlinarith
    have h3 : R * M * |y k| ≤ μ * |y (k + 1)| := by
      have h4 := mul_le_mul_of_nonneg_left h1 hμpos.le
      have h5 : μ * (R * M / μ * |y k|) = R * M * |y k| := by field_simp
      linarith
    have h6 : μ * |y (k + 1)| ≤ |g (k + 1)| * |y (k + 1)| :=
      mul_le_mul_of_nonneg_right (hgμ (k + 1)) (abs_nonneg _)
    linarith
  -- choose the starting index
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (6 * |x| + 1) / (μ * |y m1|) < 2 ^ j :=
    pow_unbounded_of_one_lt _ (by norm_num)
  set m := m1 + j with hmdef
  have hmge : m1 ≤ m := by omega
  have hypos : 0 < |y m1| := abs_pos.2 (hy0 m1)
  have hP : 6 * |x| + 1 < μ * |y m| := by
    have h1 := exists_pow_le_abs y m1 hm1a j
    rw [div_lt_iff₀ (by positivity)] at hj
    have h2 : μ * (2 ^ j * |y m1|) ≤ μ * |y m| := mul_le_mul_of_nonneg_left h1 hμpos.le
    nlinarith
  have hPpos : 0 < μ * |y m| := by linarith [abs_nonneg x]
  -- Lemma G for the shifted sequence
  set θ : ℕ → ℝ := fun k => if k ∈ S i0 then 1 / 2 else 0 with hθ
  obtain ⟨b, hb0, hb1, harc⟩ := arcs_signed (z := fun j => z (j + m)) (α := α) (R := R)
    (fun j => θ (j + m)) (fun j => hzne _) hαpos hα1 hR
    (fun j => by
      have := hm1b (j + m) (by omega)
      simpa [add_right_comm] using this)
  have harc' : ∀ k, m ≤ k → ∃ n : ℤ, |b * z k - θ k - n| ≤ α / 2 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact harc j
  have hbm : b * (μ * |y m|) ≤ 2 := by
    have h1 : b * |z (0 + m)| ≤ 2 := by
      rw [le_div_iff₀ (abs_pos.2 (hzne _))] at hb1; exact hb1
    have h2 : μ * |y m| ≤ |z (0 + m)| := by
      rw [zero_add, hzabs]
      exact mul_le_mul_of_nonneg_right (hgμ m) (abs_nonneg _)
    nlinarith
  -- the ultrafilter limits
  have hcof : {k : ℕ | m ≤ k} ∈ (Filter.cofinite : Filter ℕ) := by
    rw [Filter.mem_cofinite]
    have : ({k : ℕ | m ≤ k}ᶜ : Set ℕ) = Set.Iio m := by ext k; simp
    rw [this]; exact Set.finite_Iio m
  let t : Fin n → AddCircle (1 : ℝ) := fun i => if i = i0 then ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else 0
  have hclose : ∀ i, ‖(γ i • L y (W i)) b - t i‖ ≤ α / 2 := by
    intro i
    by_cases hgi : γ i = 0
    · have hii : i ≠ i0 := fun h => hi0 (h ▸ hgi)
      have : (γ i • L y (W i)) b = 0 := by rw [hgi, smul_apply, zero_mul, map_zero]
      rw [this]
      simp only [t, hii, ↓reduceIte, sub_zero, norm_zero]
      positivity
    · have hev : ∀ᶠ k in (W i : Filter ℕ), ‖e (y k) (γ i * b) - t i‖ ≤ α / 2 := by
        have hmem : {k : ℕ | m ≤ k} ∩ S i ∈ W i := inter_mem ((hWf i) hcof) (hSW i)
        filter_upwards [hmem] with k hk
        obtain ⟨hkm, hkS⟩ := hk
        obtain ⟨n', hn'⟩ := harc' k hkm
        have hzk : z k = γ i * y k := by
          show g k * y k = γ i * y k
          rw [hg i k hkS, hγ'eq i hgi]
        have hθk : ((θ k : ℝ) : AddCircle (1 : ℝ)) = t i := by
          by_cases hii : i = i0
          · subst hii
            simp only [t, hθ, hkS, ↓reduceIte]
          · have hk0 : k ∉ S i0 := fun h => Set.disjoint_left.1 (hSd i i0 hii) hkS h
            simp only [t, hθ, hk0, hii, ↓reduceIte]
            simp
        rw [← hθk]
        have hsub : e (y k) (γ i * b) - ((θ k : ℝ) : AddCircle (1 : ℝ)) =
            ((b * z k - θ k : ℝ) : AddCircle (1 : ℝ)) := by
          rw [e_apply, hzk]
          have : γ i * b * y k = b * (γ i * y k) := by ring
          rw [this]
          rfl
        rw [hsub]
        refine (norm_circle_le_sub_int _ n').trans ?_
        have : b * z k - θ k - n' = b * z k - θ k - n' := rfl
        exact hn'
      have hlim : Tendsto (fun k => ‖e (y k) (γ i * b) - t i‖) (W i)
          (𝓝 ‖L y (W i) (γ i * b) - t i‖) :=
        (continuous_norm.tendsto _).comp
          ((((continuous_eval (γ i * b)).tendsto _).comp (tendsto_L y (W i))).sub tendsto_const_nhds)
      have := le_of_tendsto hlim hev
      exact this
  have hev : ∑ i, (γ i • L y (W i)) b = ((b * x : ℝ) : AddCircle (1 : ℝ)) := by
    have := congrArg (fun κ : K => κ b) hsum
    simpa [AddMonoidHom.finsetSum_apply] using this
  have hts : ∑ i, t i = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    simp [t]
  have hdiff : ‖((b * x : ℝ) : AddCircle (1 : ℝ)) - ((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1 / 8 := by
    rw [← hev, ← hts, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hclose i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) * (α / 2) = 1 / 8 := by
      rw [hα]; field_simp; ring
    rw [this]
  have hlow : 3 / 8 ≤ ‖((b * x : ℝ) : AddCircle (1 : ℝ))‖ := by
    have h1 := norm_sub_norm_le ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ((b * x : ℝ) : AddCircle (1 : ℝ))
    rw [norm_sub_rev] at h1
    have h2 := norm_circle_half
    linarith
  have hup : ‖((b * x : ℝ) : AddCircle (1 : ℝ))‖ < 1 / 3 := by
    refine lt_of_le_of_lt (norm_circle_le_abs _) ?_
    rw [abs_mul, abs_of_nonneg hb0]
    have h1 : b * (μ * |y m|) * |x| ≤ 2 * |x| := mul_le_mul_of_nonneg_right hbm (abs_nonneg x)
    by_contra hcon
    have hcon' : 1 / 3 ≤ b * |x| := not_lt.1 hcon
    have h2 := mul_le_mul_of_nonneg_right hcon' hPpos.le
    nlinarith
  linarith

/-- Theorem A for a finite set of free ultrafilters: a relation `∑ γ U • L y U = e x` (for example with
`x = 0`) forces all coefficients to vanish. -/
theorem independence_finset (y : ℕ → ℝ) (hy0 : ∀ k, y k ≠ 0)
    (hy : Tendsto (fun k => |y (k + 1)| / |y k|) atTop atTop)
    (s : Finset (Ultrafilter ℕ)) (hs : ∀ U ∈ s, Free U) (γ : Ultrafilter ℕ → ℝ) (x : ℝ)
    (h : ∑ U ∈ s, γ U • L y U = e x) : ∀ U ∈ s, γ U = 0 := by
  classical
  by_contra hcon
  obtain ⟨U0, hU0, hne⟩ : ∃ U ∈ s, γ U ≠ 0 := by
    by_contra hc
    exact hcon fun U hU => by
      by_contra hne
      exact hc ⟨U, hU, hne⟩
  let W : Fin s.card → Ultrafilter ℕ := fun i => (s.equivFin.symm i).1
  have hWi : Function.Injective W :=
    Subtype.val_injective.comp s.equivFin.symm.injective
  have hWf : ∀ i, Free (W i) := fun i => hs _ (s.equivFin.symm i).2
  have hsum : ∑ i : Fin s.card, γ (W i) • L y (W i) = e x := by
    rw [← h]
    calc ∑ i : Fin s.card, γ (W i) • L y (W i)
        = ∑ i : Fin s.card, (fun u : s => γ u.1 • L y u.1) (s.equivFin.symm i) := rfl
      _ = ∑ u : s, γ u.1 • L y u.1 :=
        Equiv.sum_comp s.equivFin.symm (fun u : s => γ u.1 • L y u.1)
      _ = ∑ U ∈ s, γ U • L y U := Finset.sum_coe_sort s (fun U => γ U • L y U)
  refine independence y hy0 hy W hWi hWf (fun i => γ (W i)) ⟨s.equivFin ⟨U0, hU0⟩, ?_⟩ x hsum
  show γ (s.equivFin.symm (s.equivFin ⟨U0, hU0⟩)).1 ≠ 0
  rw [Equiv.symm_apply_apply]
  exact hne

/-- The vectors `L y U`, `U` free, are linearly independent over `ℝ` (Theorem A with `x = 0`). -/
theorem linearIndependent_L (y : ℕ → ℝ) (hy0 : ∀ k, y k ≠ 0)
    (hy : Tendsto (fun k => |y (k + 1)| / |y k|) atTop atTop) :
    LinearIndependent ℝ (fun U : {U : Ultrafilter ℕ // Free U} => L y U.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hs : ∀ U ∈ s.map (Function.Embedding.subtype (fun U : Ultrafilter ℕ => Free U)), Free U := by
    intro U hU
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hU
    exact u.2
  have hsum : ∑ U ∈ s.map (Function.Embedding.subtype (fun U : Ultrafilter ℕ => Free U)),
      (fun U => if h : Free U then g ⟨U, h⟩ else 0) U • L y U = e 0 := by
    rw [Finset.sum_map]
    have h0 : e 0 = 0 := by ext b; simp
    rw [h0, ← hg]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [u.2]
  have := independence_finset y hy0 hy _ hs _ 0 hsum i.1 (Finset.mem_map_of_mem _ hi)
  simpa [i.2] using this

end Q95
end PVG
