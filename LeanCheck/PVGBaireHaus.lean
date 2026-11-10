import Mathlib
import LeanCheck.PVGNoFU

/-!
# PVG: an unbounded convergent sequence destroys the Hausdorff property of the modification (Lean check)

Scope. Theorem 8.58 ("Theorem A", Baire argument) and Corollary 8.59 of PVG_v26, Addendum L of the research note. Let `conv` be a PVG on `ℝ`
(`IsPVG conv`) that is coarser than the Euclidean convergence, and let `u : ℕ → ℝ` be a sequence with `conv (map u atTop) 0` that is
unbounded in the sense `∀ R N, ∃ n ≥ N, R < |u n|`. Then any `conv`-open neighbourhood of `0` meets any `conv`-open neighbourhood of any
point `x` (here "`conv`-open" means open in the topological modification `modTop conv`: `ConvOpen`). The proof uses only dilations and
translations, and Baire's theorem; it does not use addition of neighbourhoods.

* `baire_step`: if `ℝ` is the union of sets `D N`, every nonempty open `V` contains a nonempty open set inside `closure (D N)` for some `N`;
* `convOpen_isOpen`, `convOpen_translate`, `convOpen_dilate`: properties of `conv`-open sets;
* `theorem_A`: the theorem;
* `seq_euclid_of_hausdorff`: if the modification is Hausdorff, then every `conv`-convergent sequence converges in the Euclidean topology;
* `noFU_xi_of_xiseq`, `noFU_of_hausdorff_topology`: Proposition `noFUxi` for `ξ_{γ,I}` with an arbitrary Hausdorff topology `γ` for which
  `ξ_{γ,I}` is a PVG (no group structure of `γ` assumed).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- `U` is open in the topological modification of `conv`. -/
def ConvOpen (conv : Filter ℝ → ℝ → Prop) (U : Set ℝ) : Prop := ∀ x ∈ U, ∀ F, conv F x → U ∈ F

/-- Baire's theorem in the form needed: if `ℝ = ⋃ D N`, a nonempty open `V` contains a nonempty open subset of some `closure (D N)`. -/
theorem baire_step (D : ℕ → Set ℝ) (hD : ∀ a : ℝ, ∃ N, a ∈ D N) (V : Set ℝ) (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ N, (V ∩ interior (closure (D N))).Nonempty := by
  have hc : ∀ N, IsClosed (closure (D N)) := fun N => isClosed_closure
  have hU : ⋃ N, closure (D N) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨N, hN⟩ := hD a
    exact Set.mem_iUnion.2 ⟨N, subset_closure hN⟩
  have hdense := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyV, hyU⟩ := hdense.inter_open_nonempty V hV hne
  obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hyU
  exact ⟨N, y, hyV, hN⟩

/-- A `conv`-open set is Euclidean open when `conv` is coarser than the Euclidean convergence. -/
theorem convOpen_isOpen {conv : Filter ℝ → ℝ → Prop} (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ 𝓝 x → conv F x) {U : Set ℝ}
    (hU : ConvOpen conv U) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  exact hU y hy (𝓝 y) (hcoarse (𝓝 y) y le_rfl)

/-- Translation: if `U` is `conv`-open, so is `{w | w + x ∈ U}`. -/
theorem convOpen_translate {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv) (x : ℝ) {U : Set ℝ} (hU : ConvOpen conv U) :
    ConvOpen conv {w | w + x ∈ U} := by
  intro z hz F hF
  have h1 := hP.add hF (hP.p1 x)
  rw [Filter.map₂_pure_right] at h1
  have h2 : U ∈ Filter.map (fun a => a + x) F := hU (z + x) hz _ h1
  exact h2

/-- Dilation: if `U` is a `conv`-open neighbourhood of `0` and `conv (map u atTop) 0`, then `a * u k ∈ U` eventually. -/
theorem convOpen_dilate {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv) {u : ℕ → ℝ} (hu : conv (Filter.map u atTop) 0)
    {U : Set ℝ} (hU : ConvOpen conv U) (h0 : (0 : ℝ) ∈ U) (a : ℝ) : ∀ᶠ k in atTop, a * u k ∈ U := by
  have h1 := hP.smul a hu
  rw [smul_zero] at h1
  have h2 : U ∈ Filter.map (fun z : ℝ => a • z) (Filter.map u atTop) := hU 0 h0 _ h1
  simpa using h2

/-- **Theorem A (Theorem 8.58).** Let `conv` be a PVG on `ℝ` that is coarser than the Euclidean convergence, and `u` an unbounded
sequence that converges to `0` for `conv`. Then every `conv`-open neighbourhood of `0` meets every `conv`-open neighbourhood of every
point `x`. -/
theorem theorem_A {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv) (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ 𝓝 x → conv F x)
    {u : ℕ → ℝ} (hu : conv (Filter.map u atTop) 0) (hunb : ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N, R < |u n|) (x : ℝ) {O O' : Set ℝ}
    (hO : ConvOpen conv O) (h0 : (0 : ℝ) ∈ O) (hO' : ConvOpen conv O') (hx : x ∈ O') : (O ∩ O').Nonempty := by
  set O'' : Set ℝ := {w | w + x ∈ O'} with hO''def
  have hO''c : ConvOpen conv O'' := convOpen_translate hP x hO'
  have h0'' : (0 : ℝ) ∈ O'' := by simpa [hO''def] using hx
  have hOo : IsOpen O := convOpen_isOpen hcoarse hO
  have hO''o : IsOpen O'' := convOpen_isOpen hcoarse hO''c
  -- the sets D N
  let D1 : ℕ → Set ℝ := fun N => {a | ∀ k ≥ N, a * u k ∈ O}
  let D2 : ℕ → Set ℝ := fun N => {a | ∀ k ≥ N, a * u k ∈ O''}
  have hD1 : ∀ a : ℝ, ∃ N, a ∈ D1 N := by
    intro a
    obtain ⟨N, hN⟩ := eventually_atTop.1 (convOpen_dilate hP hu hO h0 a)
    exact ⟨N, fun k hk => hN k hk⟩
  have hD2 : ∀ a : ℝ, ∃ N, a ∈ D2 N := by
    intro a
    obtain ⟨N, hN⟩ := eventually_atTop.1 (convOpen_dilate hP hu hO''c h0'' a)
    exact ⟨N, fun k hk => hN k hk⟩
  -- first Baire step
  obtain ⟨N1, hN1⟩ := baire_step D1 hD1 Set.univ isOpen_univ ⟨0, trivial⟩
  set W1 : Set ℝ := interior (closure (D1 N1)) with hW1
  have hW1o : IsOpen W1 := isOpen_interior
  have hW1ne : W1.Nonempty := by
    obtain ⟨y, -, hy⟩ := hN1
    exact ⟨y, hy⟩
  have hW1sub : W1 ⊆ closure (D1 N1) := interior_subset
  -- second Baire step
  obtain ⟨N2, hN2⟩ := baire_step D2 hD2 W1 hW1o hW1ne
  set W2 : Set ℝ := W1 ∩ interior (closure (D2 N2)) with hW2
  have hW2o : IsOpen W2 := hW1o.inter isOpen_interior
  have hW2ne : W2.Nonempty := hN2
  have hW2D1 : W2 ⊆ closure (D1 N1) := fun y hy => hW1sub hy.1
  have hW2D2 : W2 ⊆ closure (D2 N2) := fun y hy => interior_subset hy.2
  obtain ⟨p, hp⟩ := hW2ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW2o p hp
  -- choose n with |x / u n| < ε
  obtain ⟨n, hn, hnR⟩ := hunb (|x| / ε) (max N1 N2)
  have hN1n : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hN2n : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hpos : 0 < |u n| := lt_of_le_of_lt (div_nonneg (abs_nonneg x) hε.le) hnR
  have hune : u n ≠ 0 := abs_pos.1 hpos
  set s : ℝ := x / u n with hs
  have hsmall : |s| < ε := by
    rw [hs, abs_div]
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hε] at hnR
    linarith
  have hsu : s * u n = x := by rw [hs]; field_simp
  -- the open set W3
  set W3 : Set ℝ := W2 ∩ {a | a - s ∈ W2} with hW3
  have hW3o : IsOpen W3 := hW2o.inter (hW2o.preimage (continuous_id.sub continuous_const))
  have hpW3 : p ∈ W3 := by
    refine ⟨hp, ?_⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    simpa using hsmall
  -- the countably many open sets
  let S : ℕ ⊕ ℕ → Set ℝ := fun i =>
    match i with
    | Sum.inl k => {a | k < N1 ∨ a * u k ∈ O} ∪ (closure W3)ᶜ
    | Sum.inr k => {a | k < N2 ∨ (a - s) * u k ∈ O''} ∪ (closure W3)ᶜ
  have hSo : ∀ i, IsOpen (S i) := by
    intro i
    rcases i with k | k
    · show IsOpen ({a | k < N1 ∨ a * u k ∈ O} ∪ (closure W3)ᶜ)
      refine IsOpen.union ?_ isClosed_closure.isOpen_compl
      by_cases hk : k < N1
      · simp [hk]
      · have : {a : ℝ | k < N1 ∨ a * u k ∈ O} = (fun a : ℝ => a * u k) ⁻¹' O := by
          ext a; simp [hk]
        rw [this]
        exact hOo.preimage (continuous_id.mul continuous_const)
    · show IsOpen ({a | k < N2 ∨ (a - s) * u k ∈ O''} ∪ (closure W3)ᶜ)
      refine IsOpen.union ?_ isClosed_closure.isOpen_compl
      by_cases hk : k < N2
      · simp [hk]
      · have : {a : ℝ | k < N2 ∨ (a - s) * u k ∈ O''} = (fun a : ℝ => (a - s) * u k) ⁻¹' O'' := by
          ext a; simp [hk]
        rw [this]
        exact hO''o.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hW3cl1 : W3 ⊆ closure (D1 N1) := fun y hy => hW2D1 hy.1
  have hW3cl2 : W3 ⊆ closure {a | a - s ∈ D2 N2} := by
    intro y hy
    have h1 : y - s ∈ closure (D2 N2) := hW2D2 hy.2
    have := (Homeomorph.subRight s).preimage_closure (D2 N2)
    have h2 : y ∈ (Homeomorph.subRight s) ⁻¹' closure (D2 N2) := h1
    rw [this] at h2
    exact h2
  have hSd : ∀ i, Dense (S i) := by
    intro i
    rcases i with k | k
    · intro y
      by_cases hy : y ∈ closure W3
      · have hsub : D1 N1 ⊆ {a | k < N1 ∨ a * u k ∈ O} ∪ (closure W3)ᶜ := by
          intro a ha
          by_cases hk : k < N1
          · exact Or.inl (Or.inl hk)
          · exact Or.inl (Or.inr (ha k (not_lt.1 hk)))
        have : closure W3 ⊆ closure (S (Sum.inl k)) := by
          refine closure_minimal ?_ isClosed_closure
          exact hW3cl1.trans (closure_mono hsub)
        exact this hy
      · exact subset_closure (Or.inr hy)
    · intro y
      by_cases hy : y ∈ closure W3
      · have hsub : {a | a - s ∈ D2 N2} ⊆ {a | k < N2 ∨ (a - s) * u k ∈ O''} ∪ (closure W3)ᶜ := by
          intro a ha
          by_cases hk : k < N2
          · exact Or.inl (Or.inl hk)
          · exact Or.inl (Or.inr (ha k (not_lt.1 hk)))
        have : closure W3 ⊆ closure (S (Sum.inr k)) := by
          refine closure_minimal ?_ isClosed_closure
          exact hW3cl2.trans (closure_mono hsub)
        exact this hy
      · exact subset_closure (Or.inr hy)
  have hdense : Dense (⋂ i, S i) := dense_iInter_of_isOpen hSo hSd
  obtain ⟨a, haW3, haS⟩ := hdense.inter_open_nonempty W3 hW3o ⟨p, hpW3⟩
  have haS' := Set.mem_iInter.1 haS
  have hcl : a ∈ closure W3 := subset_closure haW3
  have h1 : a * u n ∈ O := by
    rcases haS' (Sum.inl n) with h | h
    · rcases h with h | h
      · exact absurd hN1n (not_le.2 h)
      · exact h
    · exact absurd hcl h
  have h2 : (a - s) * u n ∈ O'' := by
    rcases haS' (Sum.inr n) with h | h
    · rcases h with h | h
      · exact absurd hN2n (not_le.2 h)
      · exact h
    · exact absurd hcl h
  refine ⟨a * u n, h1, ?_⟩
  have h3 : (a - s) * u n + x = a * u n := by
    rw [sub_mul, hsu]; ring
  have h4 : (a - s) * u n + x ∈ O' := h2
  rw [h3] at h4
  exact h4

#print axioms theorem_A

end Q95
end PVG
