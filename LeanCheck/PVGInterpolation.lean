import Mathlib

/-!
# PVG: the interpolation lemma and two abstract consequences (Lean check)

Scope. These declarations check, in an abstract setting, steps used in `PVG_v9`
(Pseudotopological Vector Groups on Real Line), Section 8:

* `interpolation`, `interpolation_round` : Lemma 8.26(a). For reals `y k` with `y 0 ≠ 0` and
  `4 |y k| ≤ |y (k+1)|`, and any `S ⊆ ℕ`, there is a real `b` such that `b * y k` is at
  distance at least `1/3` from the integers for `k ∈ S` and at most `1/6` for `k ∉ S`
  (the upper bound `1/2` for `k ∈ S` is automatic). Indices start at `0` instead of `1`.
* `limits_ne`, `distinct_limits` : the abstract form of Lemma 8.26(b): a continuous
  real-valued function separating the two sets of an interpolating sequence separates the
  limits along ultrafilters `V ∋ S` and `V' ∋ Sᶜ`. The compact group `Hom(ℝ, 𝕋)` is not
  formalized here; `X` and the functions `ψ b` are abstract.
* `bounded_conv_euclid` : the abstract form of Proposition 8.28(a): for any convergence
  relation on filters of `ℝ` that has unique limits, converges for every Euclidean convergent
  filter and is monotone under refinement, a bounded convergent sequence converges in the
  Euclidean sense to the same limit.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the
article statements requires mathematical review.
-/

open Filter Topology

namespace PVG

/-- `t` is at distance at least `1/3` from every integer. -/
def FarFromInt (t : ℝ) : Prop := ∀ m : ℤ, 1 / 3 ≤ |t - m|

/-- `t` is within `1/6` of some integer. -/
def NearInt (t : ℝ) : Prop := ∃ m : ℤ, |t - m| ≤ 1 / 6

lemma FarFromInt.neg {t : ℝ} (h : FarFromInt t) : FarFromInt (-t) := by
  intro m
  have := h (-m)
  have e : -t - (m : ℝ) = -(t - ((-m : ℤ) : ℝ)) := by push_cast; ring
  rw [e, abs_neg]
  exact this

lemma NearInt.neg {t : ℝ} (h : NearInt t) : NearInt (-t) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨-m, ?_⟩
  have e : -t - ((-m : ℤ) : ℝ) = -(t - m) := by push_cast; ring
  rw [e, abs_neg]
  exact hm

lemma farFromInt_mul_abs {b y : ℝ} (h : FarFromInt (b * |y|)) : FarFromInt (b * y) := by
  rcases abs_choice y with hy | hy
  · rwa [hy] at h
  · rw [hy] at h
    have := h.neg
    rwa [show -(b * -y) = b * y by ring] at this

lemma nearInt_mul_abs {b y : ℝ} (h : NearInt (b * |y|)) : NearInt (b * y) := by
  rcases abs_choice y with hy | hy
  · rwa [hy] at h
  · rw [hy] at h
    have := h.neg
    rwa [show -(b * -y) = b * y by ring] at this

/-- The condition required of `b * y k`. -/
def Good (S : Set ℕ) (k : ℕ) (t : ℝ) : Prop := (k ∈ S → FarFromInt t) ∧ (k ∉ S → NearInt t)

lemma window_far {a l r : ℝ} (ha : 0 < a) (h : 4 / 3 ≤ a * (r - l)) :
    ∃ l' r', l ≤ l' ∧ r' ≤ r ∧ r' - l' = 1 / (3 * a) ∧ ∀ b ∈ Set.Icc l' r', FarFromInt (b * a) := by
  set j : ℤ := ⌈a * l - 1 / 3⌉ with hj
  have hj1 : a * l - 1 / 3 ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < a * l - 1 / 3 + 1 := Int.ceil_lt_add_one _
  refine ⟨((j : ℝ) + 1 / 3) / a, ((j : ℝ) + 2 / 3) / a, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]; linarith
  · rw [div_le_iff₀ ha]; nlinarith
  · field_simp; ring
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [le_div_iff₀ ha] at hb2
    rw [div_le_iff₀ ha] at hb1
    intro m
    by_cases hm : m ≤ j
    · have : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h1 : 1 / 3 ≤ b * a - m := by linarith
      exact h1.trans (le_abs_self _)
    · have hm' : (j : ℝ) + 1 ≤ m := by
        have : j + 1 ≤ m := by omega
        exact_mod_cast this
      have h1 : 1 / 3 ≤ m - b * a := by linarith
      have := neg_abs_le (b * a - m)
      linarith [abs_sub_comm (b * a) (m : ℝ), neg_le_abs (b * a - m), le_abs_self (m - b * a)]

lemma window_near {a l r : ℝ} (ha : 0 < a) (h : 4 / 3 ≤ a * (r - l)) :
    ∃ l' r', l ≤ l' ∧ r' ≤ r ∧ r' - l' = 1 / (3 * a) ∧ ∀ b ∈ Set.Icc l' r', NearInt (b * a) := by
  set j : ℤ := ⌈a * l + 1 / 6⌉ with hj
  have hj1 : a * l + 1 / 6 ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < a * l + 1 / 6 + 1 := Int.ceil_lt_add_one _
  refine ⟨((j : ℝ) - 1 / 6) / a, ((j : ℝ) + 1 / 6) / a, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]; linarith
  · rw [div_le_iff₀ ha]; nlinarith
  · field_simp; ring
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [le_div_iff₀ ha] at hb2
    rw [div_le_iff₀ ha] at hb1
    refine ⟨j, ?_⟩
    rw [abs_le]
    constructor <;> linarith

lemma window (S : Set ℕ) (k : ℕ) {a l r : ℝ} (ha : 0 < a) (h : 4 / 3 ≤ a * (r - l)) :
    ∃ l' r', l ≤ l' ∧ r' ≤ r ∧ r' - l' = 1 / (3 * a) ∧
      ∀ b ∈ Set.Icc l' r', Good S k (b * a) := by
  by_cases hk : k ∈ S
  · obtain ⟨l', r', h1, h2, h3, h4⟩ := window_far ha h
    exact ⟨l', r', h1, h2, h3, fun b hb => ⟨fun _ => h4 b hb, fun h => absurd hk h⟩⟩
  · obtain ⟨l', r', h1, h2, h3, h4⟩ := window_near ha h
    exact ⟨l', r', h1, h2, h3, fun b hb => ⟨fun h => absurd h hk, fun _ => h4 b hb⟩⟩

/-- A closed interval of length `1 / (3 a k)` all of whose points are good at stage `k`. -/
structure Iv (S : Set ℕ) (a : ℕ → ℝ) (k : ℕ) where
  l : ℝ
  r : ℝ
  len : r - l = 1 / (3 * a k)
  good : ∀ b ∈ Set.Icc l r, Good S k (b * a k)

section chain

variable (S : Set ℕ) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hr : ∀ k, 4 * a k ≤ a (k + 1))
include ha hr

omit hr in
lemma exists_first : ∃ J : Iv S a 0, 0 ≤ J.l := by
  obtain ⟨l', r', h1, h2, h3, h4⟩ := window S 0 (a := a 0) (l := 0) (r := 2 / a 0) (ha 0)
    (by
      have e : a 0 * (2 / a 0 - 0) = 2 := by
        have := (ha 0).ne'
        rw [sub_zero]
        field_simp
      rw [e]; norm_num)
  exact ⟨⟨l', r', h3, h4⟩, h1⟩

lemma exists_next (k : ℕ) (J : Iv S a k) :
    ∃ J' : Iv S a (k + 1), J.l ≤ J'.l ∧ J'.r ≤ J.r := by
  have hk := ha k
  have hk1 := ha (k + 1)
  have hlen : 4 / 3 ≤ a (k + 1) * (J.r - J.l) := by
    rw [J.len]
    have h4 := hr k
    have : a (k + 1) * (1 / (3 * a k)) = a (k + 1) / (3 * a k) := by ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨l', r', h1, h2, h3, h4⟩ := window S (k + 1) hk1 hlen
  exact ⟨⟨l', r', h3, h4⟩, h1, h2⟩

noncomputable def chain : (k : ℕ) → Iv S a k
  | 0 => Classical.choose (exists_first S ha)
  | k + 1 => Classical.choose (exists_next S ha hr k (chain k))

lemma chain_succ_le (k : ℕ) :
    (chain S ha hr k).l ≤ (chain S ha hr (k + 1)).l ∧ (chain S ha hr (k + 1)).r ≤ (chain S ha hr k).r :=
  Classical.choose_spec (exists_next S ha hr k (chain S ha hr k))

end chain

/-- Lemma 8.26(a) (interpolation), in the form `Good`. -/
theorem interpolation (y : ℕ → ℝ) (h0 : y 0 ≠ 0) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|)
    (S : Set ℕ) : ∃ b : ℝ, ∀ k, Good S k (b * y k) := by
  set a : ℕ → ℝ := fun k => |y k| with hadef
  have ha : ∀ k, 0 < a k := by
    intro k
    induction k with
    | zero => exact abs_pos.2 h0
    | succ k ih =>
      have := hr k
      simp only [hadef] at ih ⊢
      linarith
  have hr' : ∀ k, 4 * a k ≤ a (k + 1) := hr
  set t : ℕ → Set ℝ := fun k => Set.Icc (chain S ha hr' k).l (chain S ha hr' k).r with htdef
  have hnest : ∀ k, t (k + 1) ⊆ t k := by
    intro k x hx
    obtain ⟨h1, h2⟩ := chain_succ_le S ha hr' k
    exact ⟨h1.trans hx.1, hx.2.trans h2⟩
  have hne : ∀ k, (t k).Nonempty := by
    intro k
    refine ⟨(chain S ha hr' k).l, le_refl _, ?_⟩
    have := (chain S ha hr' k).len
    have hp : 0 < 1 / (3 * a k) := by have := ha k; positivity
    linarith
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hnest hne
    isCompact_Icc (fun k => isClosed_Icc)
  refine ⟨b, fun k => ?_⟩
  have hbk : b ∈ t k := Set.mem_iInter.1 hb k
  have hg := (chain S ha hr' k).good b hbk
  exact ⟨fun hk => farFromInt_mul_abs (hg.1 hk), fun hk => nearInt_mul_abs (hg.2 hk)⟩

/-- Lemma 8.26(a) in terms of the distance `|t - round t|` to the nearest integer. -/
theorem interpolation_round (y : ℕ → ℝ) (h0 : y 0 ≠ 0) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|)
    (S : Set ℕ) : ∃ b : ℝ, ∀ k,
      (k ∈ S → 1 / 3 ≤ |b * y k - round (b * y k)| ∧ |b * y k - round (b * y k)| ≤ 1 / 2) ∧
      (k ∉ S → |b * y k - round (b * y k)| ≤ 1 / 6) := by
  obtain ⟨b, hb⟩ := interpolation y h0 hr S
  refine ⟨b, fun k => ⟨fun hk => ⟨hb k |>.1 hk (round (b * y k)), abs_sub_round _⟩, fun hk => ?_⟩⟩
  obtain ⟨m, hm⟩ := (hb k).2 hk
  exact (round_le _ m).trans hm

/-- Abstract Lemma 8.26(b): limits along ultrafilters separated by `S` are different. -/
theorem limits_ne {X : Type*} [TopologicalSpace X] (f : ℕ → X) (ψ : X → ℝ) (hψ : Continuous ψ)
    (S : Set ℕ) (hS : ∀ k ∈ S, 1 / 3 ≤ ψ (f k)) (hS' : ∀ k ∉ S, ψ (f k) ≤ 1 / 6)
    (V V' : Ultrafilter ℕ) (hV : S ∈ V) (hV' : Sᶜ ∈ V') (l l' : X)
    (hl : Tendsto f V (𝓝 l)) (hl' : Tendsto f V' (𝓝 l')) : l ≠ l' := by
  intro hll
  have h1 : Tendsto (ψ ∘ f) V (𝓝 (ψ l)) := (hψ.tendsto l).comp hl
  have h2 : Tendsto (ψ ∘ f) V' (𝓝 (ψ l')) := (hψ.tendsto l').comp hl'
  have a1 : 1 / 3 ≤ ψ l :=
    ge_of_tendsto h1 (Filter.mem_of_superset hV fun k hk => hS k hk)
  have a2 : ψ l' ≤ 1 / 6 :=
    le_of_tendsto h2 (Filter.mem_of_superset hV' fun k hk => hS' k hk)
  rw [← hll] at a2
  linarith

/-- Abstract Lemma 8.26(b): distinct ultrafilters on `ℕ` have distinct limits of `e ∘ y`
whenever the functions `ψ b` are continuous and read off the distance to the integers. -/
theorem distinct_limits {X : Type*} [TopologicalSpace X] (e : ℝ → X) (ψ : ℝ → X → ℝ)
    (hψ : ∀ b, Continuous (ψ b)) (hψe : ∀ b t, ψ b (e t) = |b * t - round (b * t)|)
    (y : ℕ → ℝ) (h0 : y 0 ≠ 0) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|)
    (V V' : Ultrafilter ℕ) (hVV : V ≠ V') (l l' : X)
    (hl : Tendsto (fun k => e (y k)) V (𝓝 l)) (hl' : Tendsto (fun k => e (y k)) V' (𝓝 l')) :
    l ≠ l' := by
  obtain ⟨S, hSV, hSV'⟩ : ∃ S : Set ℕ, S ∈ V ∧ Sᶜ ∈ V' := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    apply hVV
    have hle : (V' : Filter ℕ) ≤ V := by
      intro s hs
      by_contra hns
      exact hcon s hs ((Ultrafilter.compl_mem_iff_notMem).2 hns)
    exact (Ultrafilter.coe_le_coe.1 hle).symm
  obtain ⟨b, hb⟩ := interpolation_round y h0 hr S
  refine limits_ne (fun k => e (y k)) (ψ b) (hψ b) S ?_ ?_ V V' hSV hSV' l l' hl hl'
  · intro k hk
    rw [hψe]
    exact ((hb k).1 hk).1
  · intro k hk
    rw [hψe]
    exact (hb k).2 hk

/-- Abstract Proposition 8.28(a). `conv F x` is read as "`F` converges to `x`"; `G ≤ F` means
that `G` refines `F`. -/
theorem bounded_conv_euclid (conv : Filter ℝ → ℝ → Prop)
    (hmono : ∀ F G x, G ≤ F → conv F x → conv G x)
    (hcoarse : ∀ F y, F ≤ 𝓝 y → conv F y)
    (hT2 : ∀ F x x', F.NeBot → conv F x → conv F x' → x = x')
    (a : ℕ → ℝ) (hb : Bornology.IsBounded (Set.range a)) (x : ℝ)
    (hx : conv (Filter.map a atTop) x) : Tendsto a atTop (𝓝 x) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨y, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := fun n => a (ns n))
    (hb.subset (Set.range_comp_subset_range ns a) |> fun h => h)
    (fun n => ⟨n, rfl⟩)
  refine ⟨φ, ?_⟩
  have ht : Tendsto (ns ∘ φ) atTop atTop := hns.comp hφ.tendsto_atTop
  have hsub : Filter.map (a ∘ ns ∘ φ) atTop ≤ Filter.map a atTop := by
    have e : a ∘ ns ∘ φ = a ∘ (ns ∘ φ) := rfl
    rw [e, ← Filter.map_map]
    exact Filter.map_mono ht
  have h1 : conv (Filter.map (a ∘ ns ∘ φ) atTop) x := hmono _ _ x hsub hx
  have h2 : conv (Filter.map (a ∘ ns ∘ φ) atTop) y := hcoarse _ y hlim
  have hxy : x = y := hT2 _ x y (Filter.map_neBot) h1 h2
  rw [hxy]
  exact hlim

end PVG
