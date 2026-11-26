import Mathlib
import LeanCheck.PVGIndependence
import LeanCheck.PVGTwoNoWitness
import LeanCheck.PVGTwoAverage

/-!
# PVGtwo, Section 7: which sets of coefficients can be served? (Lean check)

Scope. In Mathlib's order `t₁ ≤ t₂` means that `t₁` is finer, so `γ ≤ bohrTop` says that `γ` contains the Bohr topology and
`euclidNhds x ≤ nhds x` that `γ` is contained in the usual topology. `Tb N Y` says that `Y` is totally bounded for the
neighbourhood filter `N` of `0`; `dil a Sset` is the dilate `aS`; `sT n = 2^((n+1)^2)`.

* `trace_of_tb` : if every `a_i S` is totally bounded, then `γ` and the Bohr topology agree on every subset of
  `[-m,m] + a₁T + ⋯ + a_rT`;
* `served_of_tb` : the same statement for a single coefficient and `[-1,1] + aT + (-a)T`;
* `av_tb_iff` : for the averaged topology, `aS` is totally bounded exactly when `a ∈ Λ`;
* `ae_volume_pos` : the projection estimate, for a probability measure with `μ(ball) ≤ M r^s`, `1/2 < s < 1`;
* `ae_sum_eq_univ` : for almost every `lam ∈ [1,2]`, every real number is `a + lam b` with `a, b ∈ A(δ)`;
* `exists_two_unservable` : there is `lam` such that no non-precompact group topology below the usual one makes all `aS`
  and all `(lam a)S`, `a ∈ A(δ)`, totally bounded, and every group topology coarser than both `γ_δ` and `γ_{δ/lam}` is
  precompact.

Not formalized: the reduction to topologies with a countable base, and the theorem of Comfort and Ross.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set MeasureTheory
open scoped Pointwise ENNReal

namespace PVG
namespace Two
open Q95 Lac

/-! ## Total boundedness gives the Bohr trace -/

lemma sT_ne (n : ℕ) : sT n ≠ 0 := by
  unfold sT sS
  positivity

lemma sT_ratio : Tendsto (fun k => |sT (k + 1)| / |sT k|) atTop atTop := by
  refine tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) (fun k => ?_) tendsto_natCast_atTop_atTop
  have hpos : ∀ n, 0 < sT n := fun n => by unfold sT sS; positivity
  rw [abs_of_pos (hpos _), abs_of_pos (hpos _), le_div_iff₀ (hpos _)]
  have h1 : k * 2 ^ ((k + 1) ^ 2) ≤ 2 ^ ((k + 1 + 1) ^ 2) := by
    have h2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    calc k * 2 ^ ((k + 1) ^ 2) ≤ 2 ^ k * 2 ^ ((k + 1) ^ 2) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (k + (k + 1) ^ 2) := by rw [pow_add]
      _ ≤ 2 ^ ((k + 1 + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  unfold sT sS
  exact_mod_cast h1

lemma e_eq_zero {t : ℝ} (h : e t = 0) : t = 0 := by
  by_contra ht
  have h1 : e t (1 / (2 * t)) = 0 := by rw [h]; rfl
  rw [e_apply] at h1
  have e1 : 1 / (2 * t) * t = 1 / 2 := by field_simp
  rw [e1] at h1
  have h2 : dint (1 / 2) = 0 := by
    unfold dint
    rw [h1, norm_zero]
  rw [dint_half] at h2
  norm_num at h2

lemma sumT_repr : ∀ (l : List ℝ) (x : ℝ), x ∈ sumT sT l →
    ∃ τ : Fin l.length → ℝ, (∀ i, τ i ∈ Tset sT) ∧ x = ∑ i, l.get i * τ i := by
  intro l
  induction l with
  | nil =>
    intro x hx
    have h0 : x = 0 := by simpa [sumT] using hx
    exact ⟨fun i => 0, fun i => Or.inl rfl, by simp [h0]⟩
  | cons a l ih =>
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 hx
    obtain ⟨t, ht, rfl⟩ := Set.mem_smul_set.1 hu
    obtain ⟨τ, hτ, hv'⟩ := ih v hv
    refine ⟨Fin.cons t τ, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ht
      · simpa using hτ j
    · show a • t + v = ∑ i : Fin (l.length + 1), (a :: l).get i * (Fin.cons t τ : Fin (l.length + 1) → ℝ) i
      rw [Fin.sum_univ_succ, hv']
      simp [smul_eq_mul]

lemma Tset_repr {τ : ℝ} (h : τ ∈ Tset sT) :
    ∃ c ∈ ({-1, 0, 1} : Finset ℝ), ∃ n : ℕ, τ = c * sT n := by
  rcases h with rfl | ⟨n, rfl | rfl⟩
  · exact ⟨0, by simp, 0, by simp⟩
  · exact ⟨1, by simp, n, by simp⟩
  · exact ⟨-1, by simp, n, by simp⟩

lemma sign_mem_Sset {c : ℝ} (hc : c ∈ ({-1, 0, 1} : Finset ℝ)) (n : ℕ) : c * sT n ∈ Sset := by
  have hs : sS (n + 1) = sT n := rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Or.inr ⟨n + 1, by omega, Or.inr (by rw [hs]; ring)⟩
  · exact Or.inl (by simp)
  · exact Or.inr ⟨n + 1, by omega, Or.inl (by rw [hs]; ring)⟩

/-- Sums of convergent functions for a neighbourhood filter with halving. -/
lemma tendsto_add_N (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W) {α : Type*} {l : Filter α}
    {f g : α → ℝ} (hf : Tendsto f l N) (hg : Tendsto g l N) : Tendsto (fun x => f x + g x) l N := by
  intro W hW
  obtain ⟨V, hV, _, h⟩ := hhalf W hW
  rw [mem_map]
  filter_upwards [hf hV, hg hV] with x hx hy
  exact h _ hx _ hy

lemma tendsto_sum_N (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (h0 : ∀ W ∈ N, (0 : ℝ) ∈ W) {α ι : Type*} {l : Filter α} (s : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ s, Tendsto (f i) l N) : Tendsto (fun x => ∑ i ∈ s, f i x) l N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro W hW
    rw [mem_map]
    exact Eventually.of_forall fun x => by simpa using h0 W hW
  | insert a s ha ih =>
    have h1 := tendsto_add_N N hhalf (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine h1.congr fun x => ?_
    rw [Finset.sum_insert ha]

/-- A free ultrafilter image of a totally bounded dilate is Cauchy. -/
lemma cauchy_of_tb (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W) (a : ℝ)
    (htb : Tb N (dil a Sset)) {c : ℝ} (hc : c ∈ ({-1, 0, 1} : Finset ℝ)) (U : Ultrafilter ℕ) :
    Tendsto (fun q : ℕ × ℕ => a * c * sT q.1 - a * c * sT q.2) ((U : Filter ℕ) ×ˢ (U : Filter ℕ)) N := by
  intro W hW
  obtain ⟨V, hV, hsym, hsub⟩ := hhalf W hW
  obtain ⟨F, hF⟩ := htb V hV
  have hex : ∀ᶠ n in (U : Filter ℕ), ∃ f ∈ (F : Set ℝ), a * c * sT n - f ∈ V := by
    refine Eventually.of_forall fun n => ?_
    have hmem : a * c * sT n ∈ dil a Sset := ⟨c * sT n, sign_mem_Sset hc n, by ring⟩
    obtain ⟨f, hf, h⟩ := hF _ hmem
    exact ⟨f, hf, h⟩
  obtain ⟨f, _, hf⟩ := (Ultrafilter.eventually_exists_mem_iff F.finite_toSet).1 hex
  rw [mem_map]
  filter_upwards [prod_mem_prod hf hf] with q hq
  obtain ⟨h1, h2⟩ := hq
  have h3 := hsub _ h1 _ (hsym _ h2)
  have e1 : a * c * sT q.1 - f + -(a * c * sT q.2 - f) = a * c * sT q.1 - a * c * sT q.2 := by ring
  rwa [e1] at h3

lemma induced_eq_of_ultra (γ : TopologicalSpace ℝ) (hfine : γ ≤ bohrTop) (J : Set ℝ)
    (h : ∀ x ∈ J, ∀ F : Ultrafilter ℝ, J ∈ F → (F : Filter ℝ) ≤ @nhds ℝ bohrTop x → (F : Filter ℝ) ≤ @nhds ℝ γ x) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  refine le_antisymm (induced_mono hfine) ?_
  refine le_of_nhds_le_nhds fun x => ?_
  rw [@nhds_induced ℝ J bohrTop, @nhds_induced ℝ J γ]
  refine Filter.le_iff_ultrafilter.2 fun G hG => ?_
  have h1 : (G.map (Subtype.val : J → ℝ) : Filter ℝ) ≤ @nhds ℝ bohrTop x.1 := by
    rw [Ultrafilter.coe_map]; exact map_le_iff_le_comap.2 hG
  have h2 : J ∈ G.map (Subtype.val : J → ℝ) :=
    Ultrafilter.mem_map.2 (Eventually.of_forall fun y => y.2)
  have h3 := h x.1 x.2 _ h2 h1
  rw [Ultrafilter.coe_map] at h3
  exact map_le_iff_le_comap.1 h3

lemma sum_smul_K {ι : Type*} (s : Finset ι) (f : ι → ℝ) (κ : K) :
    (∑ i ∈ s, f i) • κ = ∑ i ∈ s, f i • κ := by
  ext b
  rw [smul_apply, AddMonoidHom.finsetSum_apply, Finset.sum_mul, map_sum]
  rfl

lemma zero_smul_K (κ : K) : (0 : ℝ) • κ = 0 := by
  ext b
  rw [smul_apply, zero_mul, map_zero]
  rfl

attribute [local irreducible] sT sS in
/-- The core of Theorem 7.1, for a neighbourhood filter `N` of `0`. -/
theorem conv_core (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (m : ℝ) (l : List ℝ) (hl : ∀ a ∈ l, Tb N (dil a Sset))
    (J : Set ℝ) (hJ : J ⊆ Icc (-m) m + sumT sT l) (x : ℝ) (F : Ultrafilter ℝ) (hJF : J ∈ F)
    (hex : Tendsto e (F : Filter ℝ) (𝓝 (e x))) : Tendsto (fun z => z - x) (F : Filter ℝ) N := by
  classical
  have hrep : ∀ z : ℝ, ∃ (u : ℝ) (c : Fin l.length → ℝ) (n : Fin l.length → ℕ),
      z ∈ J → u ∈ Icc (-m) m ∧ (∀ i, c i ∈ ({-1, 0, 1} : Finset ℝ)) ∧
        z = u + ∑ i, l.get i * (c i * sT (n i)) := by
    intro z
    by_cases hz : z ∈ J
    · obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.1 (hJ hz)
      obtain ⟨τ, hτ, hv'⟩ := sumT_repr l v hv
      choose c hc n hn using fun i => Tset_repr (hτ i)
      refine ⟨u, c, n, fun _ => ⟨hu, hc, ?_⟩⟩
      rw [← huv, hv']
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← hn i]
    · exact ⟨0, fun _ => 0, fun _ => 0, fun h => absurd h hz⟩
  choose u c n hrep using hrep
  have hJev : ∀ᶠ z in (F : Filter ℝ), z ∈ J := hJF
  -- the signs are eventually constant
  have hsign : ∀ i, ∃ d ∈ ({-1, 0, 1} : Finset ℝ), ∀ᶠ z in (F : Filter ℝ), c z i = d := by
    intro i
    have hex : ∀ᶠ z in (F : Filter ℝ), ∃ d ∈ (({-1, 0, 1} : Finset ℝ) : Set ℝ), c z i = d :=
      hJev.mono fun z hz => ⟨c z i, (hrep z hz).2.1 i, rfl⟩
    obtain ⟨d, hd, h⟩ := (Ultrafilter.eventually_exists_mem_iff (Finset.finite_toSet _)).1 hex
    exact ⟨d, hd, h⟩
  choose d hd hdev using hsign
  -- the interval part converges
  obtain ⟨u0, _, hu0⟩ : ∃ u0 ∈ Icc (-m) m, ((F.map u : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓝 u0 := by
    refine isCompact_Icc.ultrafilter_le_nhds (F.map u) ?_
    rw [le_principal_iff]
    exact Ultrafilter.mem_map.2 (hJev.mono fun z hz => (hrep z hz).1)
  have hu : Tendsto u (F : Filter ℝ) (𝓝 u0) := by
    rw [Ultrafilter.coe_map] at hu0; exact hu0
  let W : Fin l.length → Ultrafilter ℕ := fun i => F.map (fun z => n z i)
  let I : Finset (Fin l.length) := Finset.univ.filter fun i => Free (W i)
  have hpure : ∀ i, ¬ Free (W i) → ∃ k : ℕ, ∀ᶠ z in (F : Filter ℝ), n z i = k := by
    intro i hi
    rcases (W i).le_cofinite_or_eq_pure with h | ⟨k, hk⟩
    · exact absurd h hi
    · refine ⟨k, ?_⟩
      have h1 : ({k} : Set ℕ) ∈ W i := by rw [hk]; exact Ultrafilter.mem_pure.2 rfl
      exact Ultrafilter.mem_map.1 h1
  have hk : ∀ i, ∃ k : ℕ, ¬ Free (W i) → ∀ᶠ z in (F : Filter ℝ), n z i = k := by
    intro i
    by_cases h : Free (W i)
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨k, hk⟩ := hpure i h
      exact ⟨k, fun _ => hk⟩
  choose k hk using hk
  set c0 : ℝ := ∑ i ∈ Finset.univ.filter (fun i => ¬ Free (W i)), l.get i * (d i * sT (k i)) with hc0
  set b : Fin l.length → ℝ := fun i => l.get i * d i with hb
  have hz : ∀ᶠ z in (F : Filter ℝ), z = u z + c0 + ∑ i ∈ I, b i * sT (n z i) := by
    have h1 : ∀ᶠ z in (F : Filter ℝ), ∀ i, c z i = d i := eventually_all.2 hdev
    have h2 : ∀ᶠ z in (F : Filter ℝ), ∀ i, ¬ Free (W i) → n z i = k i := by
      refine eventually_all.2 fun i => ?_
      by_cases h : Free (W i)
      · exact Eventually.of_forall fun _ h' => absurd h h'
      · exact (hk i h).mono fun z hz _ => hz
    filter_upwards [hJev, h1, h2] with z hzJ h1 h2
    conv_lhs => rw [(hrep z hzJ).2.2]
    rw [add_assoc, hc0]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Free (W i)), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [h1 i, h2 i (Finset.mem_filter.1 hi).2]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i, hb]; ring
  -- the limit in the Bohr compactification
  have hlim : Tendsto (fun z => e (u z) + e c0 + ∑ i ∈ I, b i • e (sT (n z i))) (F : Filter ℝ)
      (𝓝 (e u0 + e c0 + ∑ i ∈ I, b i • L sT (W i))) := by
    refine ((continuous_e.tendsto u0).comp hu |>.add tendsto_const_nhds).add (tendsto_finsetSum I fun i _ => ?_)
    have h1 : Tendsto (fun z => n z i) (F : Filter ℝ) (W i : Filter ℕ) := by
      show Filter.map _ _ ≤ _
      exact le_of_eq (Ultrafilter.coe_map _ _).symm
    exact ((continuous_smul_const (b i)).tendsto _).comp ((tendsto_L sT (W i)).comp h1)
  have hex' : Tendsto e (F : Filter ℝ) (𝓝 (e u0 + e c0 + ∑ i ∈ I, b i • L sT (W i))) := by
    refine hlim.congr' (hz.mono fun z hz => ?_)
    have h1 : e (∑ i ∈ I, b i * sT (n z i)) = ∑ i ∈ I, b i • e (sT (n z i)) := by
      show eHom (∑ i ∈ I, b i * sT (n z i)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_e _ _).symm
    conv_rhs => rw [hz]
    rw [e_add, e_add, h1]
  have heq : e x = e u0 + e c0 + ∑ i ∈ I, b i • L sT (W i) := tendsto_nhds_unique hex hex'
  -- the coefficients of each ultrafilter add up to zero
  set s : Finset (Ultrafilter ℕ) := I.image W with hs
  set g : Ultrafilter ℕ → ℝ := fun U => ∑ i ∈ I.filter (fun i => W i = U), b i with hgdef
  have hfib : ∑ U ∈ s, g U • L sT U = ∑ i ∈ I, b i • L sT (W i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := W) (t := s) (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun U _ => ?_
    simp only [hgdef]
    rw [sum_smul_K]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  have hsum : ∑ U ∈ s, g U • L sT U = e (x - u0 - c0) := by
    rw [hfib]
    have h1 : e (x - u0 - c0) + e u0 + e c0 = e x := by
      rw [← e_add, ← e_add]; congr 1; ring
    rw [heq] at h1
    refine add_left_cancel (a := e u0 + e c0) ?_
    rw [← h1]; abel
  have hfree : ∀ U ∈ s, Free U := by
    intro U hU
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hU
    exact (Finset.mem_filter.1 hi).2
  have hg0 := independence_finset sT sT_ne sT_ratio s hfree g _ hsum
  have hx0 : x = u0 + c0 := by
    have h1 : e (x - u0 - c0) = 0 := by
      rw [← hsum]
      exact Finset.sum_eq_zero fun U hU => by rw [hg0 U hU]; exact zero_smul_K _
    have := e_eq_zero h1
    linarith
  -- convergence for `N`
  have hsub : Tendsto (fun z => z - x) (F : Filter ℝ) N := by
    set G : Filter (s → ℕ) := Filter.pi fun U : s => ((U : Ultrafilter ℕ) : Filter ℕ) with hG
    have hGne : G.NeBot := by rw [hG]; infer_instance
    have hmem : ∀ i ∈ I, W i ∈ s := fun i hi => Finset.mem_image_of_mem _ hi
    have hmain : Tendsto (fun p : ℝ × (s → ℕ) => (u p.1 - u0) +
        ∑ i ∈ I.attach, (b i.1 * sT (n p.1 i.1) - b i.1 * sT (p.2 ⟨W i.1, hmem i.1 i.2⟩)))
        ((F : Filter ℝ) ×ˢ G) N := by
      have h1 : Tendsto (fun p : ℝ × (s → ℕ) => u p.1 - u0) ((F : Filter ℝ) ×ˢ G) N := by
        have h2 : Tendsto (fun z => u z - u0) (F : Filter ℝ) (𝓝 (0 : ℝ)) := by
          have := hu.sub_const u0
          rwa [sub_self] at this
        exact (h2.mono_right heu).comp tendsto_fst
      have h3 : ∀ i ∈ I.attach, Tendsto
          (fun p : ℝ × (s → ℕ) => b i.1 * sT (n p.1 i.1) - b i.1 * sT (p.2 ⟨W i.1, hmem i.1 i.2⟩))
          ((F : Filter ℝ) ×ˢ G) N := by
        intro i _
        have hc := cauchy_of_tb N hhalf (l.get i.1) (hl _ (List.get_mem _ _)) (hd i.1) (W i.1)
        have h4 : Tendsto (fun p : ℝ × (s → ℕ) => (n p.1 i.1, p.2 ⟨W i.1, hmem i.1 i.2⟩))
            ((F : Filter ℝ) ×ˢ G) ((W i.1 : Filter ℕ) ×ˢ (W i.1 : Filter ℕ)) := by
          have h5 : Tendsto (fun z => n z i.1) (F : Filter ℝ) (W i.1 : Filter ℕ) := by
            show Filter.map _ _ ≤ _
            exact le_of_eq (Ultrafilter.coe_map _ _).symm
          have h6 : Tendsto (fun m : s → ℕ => m ⟨W i.1, hmem i.1 i.2⟩) G (W i.1 : Filter ℕ) := by
            rw [hG]
            exact Filter.tendsto_eval_pi (fun U : s => ((U : Ultrafilter ℕ) : Filter ℕ)) ⟨W i.1, hmem i.1 i.2⟩
          exact (h5.comp tendsto_fst).prodMk (h6.comp tendsto_snd)
        have hc' : Tendsto (fun q : ℕ × ℕ => b i.1 * sT q.1 - b i.1 * sT q.2)
            ((W i.1 : Filter ℕ) ×ˢ (W i.1 : Filter ℕ)) N := by
          simpa only [hb] using hc
        exact Tendsto.comp hc' h4
      have h0 : ∀ W ∈ N, (0 : ℝ) ∈ W := fun W hW => mem_of_mem_nhds (heu hW)
      exact tendsto_add_N N hhalf h1 (tendsto_sum_N N hhalf h0 I.attach h3)
    have hid : ∀ᶠ p in (F : Filter ℝ) ×ˢ G, (u p.1 - u0) +
        ∑ i ∈ I.attach, (b i.1 * sT (n p.1 i.1) - b i.1 * sT (p.2 ⟨W i.1, hmem i.1 i.2⟩)) = p.1 - x := by
      filter_upwards [hz.prod_inl G] with p hp
      have hzero : ∑ i ∈ I.attach, b i.1 * sT (p.2 ⟨W i.1, hmem i.1 i.2⟩) = 0 := by
        set f : Ultrafilter ℕ → ℝ := fun U => if h : U ∈ s then sT (p.2 ⟨U, h⟩) else 0 with hf
        have h1 : ∑ i ∈ I.attach, b i.1 * sT (p.2 ⟨W i.1, hmem i.1 i.2⟩) = ∑ i ∈ I, b i * f (W i) := by
          rw [← Finset.sum_attach I (fun i => b i * f (W i))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hf]
          simp only [dif_pos (hmem i.1 i.2)]
        rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := W) (t := s) (fun i hi => hmem i hi)]
        refine Finset.sum_eq_zero fun U hU => ?_
        have h2 : ∑ i ∈ I.filter (fun i => W i = U), b i * f (W i) = g U * f U := by
          rw [hgdef, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
        rw [h2, hg0 U hU, zero_mul]
      have h3 : ∑ i ∈ I.attach, b i.1 * sT (n p.1 i.1) = ∑ i ∈ I, b i * sT (n p.1 i) :=
        Finset.sum_attach I (fun i => b i * sT (n p.1 i))
      rw [Finset.sum_sub_distrib, hzero, sub_zero, h3, hx0]
      linarith
    have h8 := hmain.congr' hid
    have h9 : Filter.map Prod.fst ((F : Filter ℝ) ×ˢ G) = (F : Filter ℝ) := Filter.map_fst_prod _ _
    rw [← h9, tendsto_map'_iff]
    exact h8
  exact hsub

/-- **Theorem 7.1.** If every `a S`, `a ∈ l`, is `γ`-totally bounded, then `γ` induces the Bohr topology on every
subset of `[-m,m] + a₁T + ⋯ + a_rT`. -/
theorem trace_of_tb (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hfine : γ ≤ bohrTop)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (m : ℝ) (l : List ℝ) (hl : ∀ a ∈ l, Tb (@nhds ℝ γ 0) (dil a Sset))
    (J : Set ℝ) (hJ : J ⊆ Icc (-m) m + sumT sT l) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  refine induced_eq_of_ultra γ hfine J fun x _ F hJF hFx => ?_
  rw [nhds_bohr] at hFx
  have h1 := conv_core (@nhds ℝ γ 0) (group_half γ hg) heu m l hl J hJ x F hJF (tendsto_iff_comap.2 hFx)
  intro V hV
  have h0 := (mem_nhds_translate γ hg x V).1 hV
  have h2 := h1 h0
  rw [mem_map] at h2
  refine mem_of_superset h2 fun z hz => ?_
  have e1 : x + (z - x) = z := by ring
  have : x + (z - x) ∈ V := hz
  rwa [e1] at this

/-- The case of one coefficient: total boundedness of `aS` gives the Bohr trace on `[-1,1] + aT + (-a)T`. -/
theorem served_of_tb (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hfine : γ ≤ bohrTop)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (a : ℝ) (ha : Tb (@nhds ℝ γ 0) (dil a Sset)) :
    TopologicalSpace.induced (Subtype.val : (Icc (-1 : ℝ) 1 + sumT sT [a, -a] : Set ℝ) → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : (Icc (-1 : ℝ) 1 + sumT sT [a, -a] : Set ℝ) → ℝ) bohrTop := by
  have hneg : Tb (@nhds ℝ γ 0) (dil (-a) Sset) := by
    intro V hV
    obtain ⟨F, hF⟩ := ha V hV
    refine ⟨F, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have hs' : -s ∈ Sset := by
      rcases hs with rfl | ⟨k, hk, rfl | rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inr ⟨k, hk, Or.inr rfl⟩
      · exact Or.inr ⟨k, hk, Or.inl (by simp)⟩
    have : -a * s ∈ dil a Sset := ⟨-s, hs', by ring⟩
    exact hF _ this
  refine trace_of_tb γ hg hfine heu 1 [a, -a] (fun b hb => ?_) _ (Subset.refl _)
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ha
  · rw [List.mem_singleton] at hb
    subst hb; exact hneg

/-! ## The averaged topology -/

/-- The averaged topology serves exactly `Λ`. -/
theorem av_tb_iff (a : ℝ) : Tb (@nhds ℝ avTop 0) (dil a Sset) ↔ InL a := by
  constructor
  · intro h ε hε
    have hW : {x : ℝ | ∀ N, avPhi N x ≤ ε / 2} ∈ @nhds ℝ avTop 0 :=
      (mem_nhds_av _).2 ⟨univ, Filter.univ_mem, ε / 2, by linarith, fun x _ hx => hx⟩
    obtain ⟨F, hF⟩ := h _ hW
    have hsmall : ∀ᶠ N : ℕ in atTop, ∀ f ∈ F, avPhi N f ≤ ε / 2 := by
      refine (eventually_all_finset F).2 fun f _ => ?_
      have h1 : Tendsto (fun N : ℕ => |f| / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      exact (h1.eventually_le_const (by linarith : (0 : ℝ) < ε / 2)).mono fun N h =>
        (avPhi_le_abs_div N f).trans h
    refine hsmall.mono fun N hN n => ?_
    have hmem : a * sT n ∈ dil a Sset := by
      refine ⟨sT n, ?_, rfl⟩
      have := sign_mem_Sset (c := 1) (by simp) n
      rwa [one_mul] at this
    obtain ⟨f, hf, h⟩ := hF _ hmem
    have h2 := avPhi_add_le N (a * sT n - f) f
    rw [sub_add_cancel] at h2
    have := h N
    have := hN f hf
    linarith
  · intro ha
    have hneg := inL_neg ha
    have htr := av_trace 1 [a, -a] (fun b hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · rw [List.mem_singleton] at hb; subst hb; exact hneg) (Ja a) (by
      rintro x ⟨s, hs, t, ht, rfl⟩
      refine Set.mem_add.2 ⟨0, ⟨by norm_num, by norm_num⟩, a * s + -a * t, ?_, by simp⟩
      refine Set.mem_add.2 ⟨a • s, Set.smul_mem_smul_set (Sset_subset_Tset hs), -a * t, ?_, rfl⟩
      refine Set.mem_add.2 ⟨-a • t, Set.smul_mem_smul_set (Sset_subset_Tset ht), 0, by simp [sumT], by simp⟩)
    exact tb_of_trace avTop a htr

/-! ## The projection estimate -/

section Projection

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (s M : ℝ)

lemma energy_bound (hs : 1 / 2 < s) (hs1 : s < 1) (hM : 0 ≤ M)
    (hball : ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (M * r ^ s)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y : ℝ, ∫⁻ y', ENNReal.ofReal (|y - y'| ^ (s - 1)) ∂μ ≤ C := by
  set t : ℝ := 1 - s with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  set q : ℝ := (2 : ℝ) ^ (t - s) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by rw [ht]; linarith)
  have hsum : Summable (fun j : ℕ => M * 2 ^ t * q ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hterm0 : ∀ j : ℕ, 0 ≤ M * 2 ^ t * q ^ j := fun j =>
    mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (by norm_num) _)) (pow_nonneg hq0 _)
  refine ⟨1 + ∑' j : ℕ, ENNReal.ofReal (M * 2 ^ t * q ^ j), ?_, fun y => ?_⟩
  · rw [← ENNReal.ofReal_tsum_of_nonneg hterm0 hsum]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
  set w : ℕ → ℝ := fun j => (2 : ℝ) ^ (((j : ℝ) + 1) * t) with hw
  set rad : ℕ → ℝ := fun j => ((1 : ℝ) / 2) ^ j with hrad
  have hpt : ∀ y' : ℝ, ENNReal.ofReal (|y - y'| ^ (s - 1)) ≤
      1 + ∑' j : ℕ, (Metric.closedBall y (rad j)).indicator (fun _ => ENNReal.ofReal (w j)) y' := by
    intro y'
    have hexp : s - 1 = -t := by rw [ht]; ring
    rw [hexp]
    by_cases h0 : |y - y'| = 0
    · rw [h0, Real.zero_rpow (by linarith : -t ≠ 0), ENNReal.ofReal_zero]; exact zero_le
    have hpos : 0 < |y - y'| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
    by_cases h1 : 1 ≤ |y - y'|
    · refine le_add_right ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
    push Not at h1
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near_of_lt_one hpos h1.le (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
    refine le_add_left (le_trans ?_ (ENNReal.le_tsum j))
    have hmem : y' ∈ Metric.closedBall y (rad j) := by
      rw [Metric.mem_closedBall, dist_comm, Real.dist_eq]
      exact hj2
    rw [indicator_of_mem hmem]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (((1 : ℝ) / 2) ^ (j + 1)) ^ (-t) = w j := by
      rw [hw]
      have e1 : ((1 : ℝ) / 2) ^ (j + 1) = (2 : ℝ) ^ (-((j : ℝ) + 1)) := by
        rw [Real.rpow_neg (by norm_num), div_pow, one_pow, one_div]
        congr 1
        rw [← Real.rpow_natCast]; push_cast; rfl
      rw [e1, ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    rw [← h2]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1.le (by linarith)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_one, measure_univ,
    lintegral_tsum (fun j => (measurable_const.indicator measurableSet_closedBall).aemeasurable)]
  gcongr with j
  rw [lintegral_indicator_const measurableSet_closedBall]
  have hr : 0 < rad j := by rw [hrad]; positivity
  refine (mul_le_mul_right (hball y (rad j) hr) _).trans (le_of_eq ?_)
  have hw0 : 0 ≤ w j := Real.rpow_nonneg (by norm_num) _
  rw [← ENNReal.ofReal_mul hw0]
  congr 1
  have h1 : rad j ^ s = (2 : ℝ) ^ (-((j : ℝ) * s)) := by
    have e1 : rad j = (2 : ℝ) ^ (-(j : ℝ)) := by
      rw [hrad]
      simp only []
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_pow, one_pow, one_div]
    rw [e1, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have h2 : q ^ j = (2 : ℝ) ^ ((t - s) * j) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h3 : (2 : ℝ) ^ (((j : ℝ) + 1) * t) * (2 : ℝ) ^ (-((j : ℝ) * s)) = 2 ^ t * 2 ^ ((t - s) * j) := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1; ring
  rw [h1, h2, hw]
  calc (2 : ℝ) ^ (((j : ℝ) + 1) * t) * (M * 2 ^ (-((j : ℝ) * s)))
      = M * ((2 : ℝ) ^ (((j : ℝ) + 1) * t) * (2 : ℝ) ^ (-((j : ℝ) * s))) := by ring
    _ = M * 2 ^ t * 2 ^ ((t - s) * j) := by rw [h3]; ring

/-- The pairs of pairs whose images under `(x,y) ↦ x + lam y` are `r`-close. -/
def close (r lam : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {q | |(q.1.1 + lam * q.1.2) - (q.2.1 + lam * q.2.2)| ≤ r}

lemma measurableSet_close_total (r : ℝ) :
    MeasurableSet {p : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) | p.2 ∈ close r p.1} := by
  have h : IsClosed {p : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) |
      |(p.2.1.1 + p.1 * p.2.1.2) - (p.2.2.1 + p.1 * p.2.2.2)| ≤ r} :=
    isClosed_le (by fun_prop) continuous_const
  exact h.measurableSet

lemma volume_lam_le (u v r : ℝ) (hr : 0 < r) :
    volume {lam : ℝ | lam ∈ Icc (1 : ℝ) 2 ∧ |u + lam * v| ≤ r} ≤ ENNReal.ofReal (min 1 (2 * r / |v|)) ∨ v = 0 := by
  by_cases hv : v = 0
  · exact Or.inr hv
  refine Or.inl ?_
  have hv' : 0 < |v| := abs_pos.2 hv
  rw [ENNReal.ofReal_min]
  refine le_min ?_ ?_
  · refine (measure_mono (t := Icc (1 : ℝ) 2) fun lam h => h.1).trans (le_of_eq ?_)
    rw [Real.volume_Icc]; norm_num
  · have hsub : {lam : ℝ | lam ∈ Icc (1 : ℝ) 2 ∧ |u + lam * v| ≤ r} ⊆ Metric.closedBall (-u / v) (r / |v|) := by
      intro lam h
      rw [Metric.mem_closedBall, Real.dist_eq, le_div_iff₀ hv', ← abs_mul]
      have e1 : (lam - -u / v) * v = u + lam * v := by field_simp; ring
      rw [e1]; exact h.2
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [Real.volume_closedBall]
    congr 1; ring

lemma average_bound (hs : 1 / 2 < s) (hs1 : s < 1) (hM : 0 ≤ M)
    (hball : ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (M * r ^ s)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ lam in Icc (1 : ℝ) 2, ((μ.prod μ).prod (μ.prod μ)) (close r lam) ≤ C * ENNReal.ofReal r := by
  obtain ⟨Cen, hCen, hen⟩ := energy_bound μ s M hs hs1 hM hball
  set A : ℝ := M * 3 ^ s with hA
  have hA0 : 0 ≤ A := mul_nonneg hM (Real.rpow_nonneg (by norm_num) _)
  refine ⟨ENNReal.ofReal (A * M) + ENNReal.ofReal (2 * A) * Cen,
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCen⟩,
    fun r hr hr1 => ?_⟩
  set g : ℝ → ℝ := fun v => if v = 0 then 1 else min 1 (2 * r / |v|) with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => by
    rw [hg]; simp only []; split
    · exact zero_le_one
    · exact le_min zero_le_one (div_nonneg (by linarith) (abs_nonneg _))
  have hgm : Measurable g := by
    rw [hg]
    refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact measurable_const.min (measurable_const.div continuous_abs.measurable)
  -- Tonelli in `lam`
  set S : Set (ℝ × ((ℝ × ℝ) × (ℝ × ℝ))) := {p | p.2 ∈ close r p.1} with hS
  have hSm : MeasurableSet S := measurableSet_close_total r
  have hswap : ∫⁻ lam in Icc (1 : ℝ) 2, ((μ.prod μ).prod (μ.prod μ)) (close r lam) =
      ∫⁻ q, (volume.restrict (Icc (1 : ℝ) 2)) ((fun lam => (lam, q)) ⁻¹' S) ∂((μ.prod μ).prod (μ.prod μ)) := by
    have h1 := Measure.prod_apply (μ := volume.restrict (Icc (1 : ℝ) 2)) (ν := (μ.prod μ).prod (μ.prod μ)) hSm
    have h2 := Measure.prod_apply_symm (μ := volume.restrict (Icc (1 : ℝ) 2))
      (ν := (μ.prod μ).prod (μ.prod μ)) hSm
    rw [h1] at h2
    exact h2
  set B : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun q =>
    {q : (ℝ × ℝ) × (ℝ × ℝ) | |q.1.1 - q.2.1| ≤ 2 * |q.1.2 - q.2.2| + r}.indicator
      (fun q => ENNReal.ofReal (g (q.1.2 - q.2.2))) q with hB
  have hBset : MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) | |q.1.1 - q.2.1| ≤ 2 * |q.1.2 - q.2.2| + r} := by
    refine (isClosed_le ?_ ?_).measurableSet <;> fun_prop
  have hBm : Measurable B := by
    refine Measurable.indicator ?_ hBset
    exact (hgm.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1.2 - q.2.2)).ennreal_ofReal
  have hpt : ∀ q, (volume.restrict (Icc (1 : ℝ) 2)) ((fun lam => (lam, q)) ⁻¹' S) ≤ B q := by
    intro q
    set u := q.1.1 - q.2.1 with hu
    set v := q.1.2 - q.2.2 with hv
    have hset : (fun lam => (lam, q)) ⁻¹' S = {lam : ℝ | |u + lam * v| ≤ r} := by
      ext lam
      have e1 : (q.1.1 + lam * q.1.2) - (q.2.1 + lam * q.2.2) = u + lam * v := by rw [hu, hv]; ring
      simp only [hS, close, mem_preimage, mem_ofPred_eq, e1]
    have hm : MeasurableSet {lam : ℝ | |u + lam * v| ≤ r} :=
      (isClosed_le (by fun_prop) continuous_const).measurableSet
    rw [hset, Measure.restrict_apply hm]
    have hcomm : {lam : ℝ | |u + lam * v| ≤ r} ∩ Icc (1 : ℝ) 2 =
        {lam : ℝ | lam ∈ Icc (1 : ℝ) 2 ∧ |u + lam * v| ≤ r} := by
      ext lam; exact and_comm
    rw [hcomm]
    by_cases hmem : |u| ≤ 2 * |v| + r
    · have hBq : B q = ENNReal.ofReal (g v) := by
        rw [hB]; exact indicator_of_mem (by exact hmem) _
      rw [hBq]
      rcases volume_lam_le u v r hr with h | h
      · by_cases hv0 : v = 0
        · refine (measure_mono (t := Icc (1 : ℝ) 2) fun lam h => h.1).trans ?_
          rw [Real.volume_Icc, hg]
          simp only [if_pos hv0]
          norm_num
        · rw [hg]; simp only [if_neg hv0]; exact h
      · refine (measure_mono (t := Icc (1 : ℝ) 2) fun lam h => h.1).trans ?_
        rw [Real.volume_Icc, hg]
        simp only [if_pos h]
        norm_num
    · have hempty : {lam : ℝ | lam ∈ Icc (1 : ℝ) 2 ∧ |u + lam * v| ≤ r} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun lam h => hmem ?_
        have h1 : |u| ≤ |u + lam * v| + |lam * v| := by
          have := abs_sub (u + lam * v) (lam * v)
          rwa [add_sub_cancel_right] at this
        have h2 : |lam * v| ≤ 2 * |v| := by
          rw [abs_mul, abs_of_nonneg (by linarith [h.1.1] : (0 : ℝ) ≤ lam)]
          exact mul_le_mul_of_nonneg_right h.1.2 (abs_nonneg _)
        have := h.2
        linarith
      rw [hempty, measure_empty]; exact zero_le
  rw [hswap]
  refine (lintegral_mono hpt).trans ?_
  set G : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (M * (2 * |v| + r) ^ s) * ENNReal.ofReal (g v) with hG
  have hGm : Measurable G := by
    refine Measurable.mul ?_ hgm.ennreal_ofReal
    refine (Continuous.measurable ?_).ennreal_ofReal
    refine continuous_const.mul (Continuous.rpow_const (by fun_prop) fun v => Or.inr (by linarith))
  have hstep : ∫⁻ q, B q ∂((μ.prod μ).prod (μ.prod μ)) ≤ ∫⁻ y, ∫⁻ y', G (y - y') ∂μ ∂μ := by
    rw [lintegral_prod _ hBm.aemeasurable]
    have hinner : ∀ a : ℝ × ℝ, ∫⁻ b, B (a, b) ∂(μ.prod μ) ≤ ∫⁻ y', G (a.2 - y') ∂μ := by
      intro a
      have hBa : Measurable fun b => B (a, b) := hBm.comp measurable_prodMk_left
      rw [lintegral_prod_symm' _ hBa]
      refine lintegral_mono fun y' => ?_
      have h1 : ∀ x' : ℝ, B (a, (x', y')) =
          (Metric.closedBall a.1 (2 * |a.2 - y'| + r)).indicator
            (fun _ => ENNReal.ofReal (g (a.2 - y'))) x' := by
        intro x'
        have hiff : ((a, (x', y')) ∈ {q : (ℝ × ℝ) × (ℝ × ℝ) | |q.1.1 - q.2.1| ≤ 2 * |q.1.2 - q.2.2| + r}) ↔
            x' ∈ Metric.closedBall a.1 (2 * |a.2 - y'| + r) := by
          rw [Metric.mem_closedBall, dist_comm, Real.dist_eq]; rfl
        by_cases h : x' ∈ Metric.closedBall a.1 (2 * |a.2 - y'| + r)
        · rw [indicator_of_mem h, hB]; exact indicator_of_mem (hiff.2 h) _
        · rw [indicator_of_notMem h, hB]; exact indicator_of_notMem (fun h' => h (hiff.1 h')) _
      simp only [h1]
      rw [lintegral_indicator_const measurableSet_closedBall, hG]
      simp only []
      rw [mul_comm]
      refine mul_le_mul_left (hball a.1 _ ?_) _
      have := abs_nonneg (a.2 - y')
      linarith
    refine (lintegral_mono hinner).trans ?_
    have hm2 : Measurable fun y : ℝ => ∫⁻ y', G (y - y') ∂μ := by
      have : Measurable (Function.uncurry fun y y' : ℝ => G (y - y')) :=
        hGm.comp (measurable_fst.sub measurable_snd)
      exact this.lintegral_prod_right'
    have hm3 : Measurable fun a : ℝ × ℝ => ∫⁻ y', G (a.2 - y') ∂μ := hm2.comp measurable_snd
    rw [lintegral_prod _ hm3.aemeasurable]
    simp only []
    rw [lintegral_const, measure_univ, mul_one]
  refine hstep.trans ?_
  have hGle : ∀ y y' : ℝ, G (y - y') ≤
      (Metric.closedBall y r).indicator (fun _ => ENNReal.ofReal (A * r ^ s)) y' +
        ENNReal.ofReal (2 * A * r) * ENNReal.ofReal (|y - y'| ^ (s - 1)) := by
    intro y y'
    set v := y - y' with hv
    rw [hG]
    simp only []
    rw [← ENNReal.ofReal_mul (mul_nonneg hM (Real.rpow_nonneg (by positivity) _))]
    by_cases h : |v| ≤ r
    · refine le_add_right ?_
      have hmem : y' ∈ Metric.closedBall y r := by
        rw [Metric.mem_closedBall, dist_comm, Real.dist_eq]; exact h
      rw [indicator_of_mem hmem]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (2 * |v| + r) ^ s ≤ 3 ^ s * r ^ s := by
        rw [← Real.mul_rpow (by norm_num) hr.le]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h2 : g v ≤ 1 := by
        rw [hg]; simp only []; split
        · exact le_refl _
        · exact min_le_left _ _
      calc M * (2 * |v| + r) ^ s * g v ≤ M * (3 ^ s * r ^ s) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hM) h2 (hg0 v)
              (mul_nonneg hM (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hr.le _)))
        _ = A * r ^ s := by rw [hA]; ring
    · push Not at h
      refine le_add_left ?_
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hA0) hr.le)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hvpos : 0 < |v| := lt_trans hr h
      have hv0 : v ≠ 0 := abs_pos.1 hvpos
      have h1 : (2 * |v| + r) ^ s ≤ 3 ^ s * |v| ^ s := by
        rw [← Real.mul_rpow (by norm_num) hvpos.le]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h2 : g v ≤ 2 * r / |v| := by
        rw [hg]; simp only [if_neg hv0]; exact min_le_right _ _
      have h3 : |v| ^ (s - 1) = |v| ^ s / |v| := by rw [Real.rpow_sub hvpos, Real.rpow_one]
      calc M * (2 * |v| + r) ^ s * g v ≤ M * (3 ^ s * |v| ^ s) * (2 * r / |v|) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hM) h2 (hg0 v)
              (mul_nonneg hM (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)))
        _ = 2 * A * r * |v| ^ (s - 1) := by rw [h3, hA]; ring
  have hbound : ∀ y : ℝ, ∫⁻ y', G (y - y') ∂μ ≤
      ENNReal.ofReal (A * r ^ s) * ENNReal.ofReal (M * r ^ s) + ENNReal.ofReal (2 * A * r) * Cen := by
    intro y
    refine (lintegral_mono (hGle y)).trans ?_
    rw [lintegral_add_left (measurable_const.indicator measurableSet_closedBall),
      lintegral_indicator_const measurableSet_closedBall,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact add_le_add (mul_le_mul_right (hball y r hr) _) (mul_le_mul_right (hen y) _)
  refine (lintegral_mono hbound).trans ?_
  rw [lintegral_const, measure_univ, mul_one, add_mul]
  refine add_le_add ?_ (le_of_eq ?_)
  · rw [← ENNReal.ofReal_mul (mul_nonneg hA0 (Real.rpow_nonneg hr.le _)),
      ← ENNReal.ofReal_mul (mul_nonneg hA0 hM)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : r ^ s * r ^ s ≤ r := by
      rw [← Real.rpow_add hr]
      conv_rhs => rw [← Real.rpow_one r]
      exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    calc A * r ^ s * (M * r ^ s) = A * M * (r ^ s * r ^ s) := by ring
      _ ≤ A * M * r := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0 hM)
  · rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA0), mul_right_comm]

/-- For one `lam`: the `r`-neighbourhood of the projection is large if few pairs are `r`-close. -/
lemma cells (K : Set ℝ) (hK : IsCompact K) (hKm : μ Kᶜ = 0) (lam r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal r ≤
      volume (Metric.cthickening r ((fun p : ℝ × ℝ => p.1 + lam * p.2) '' (K ×ˢ K))) *
        ((μ.prod μ).prod (μ.prod μ)) (close r lam) := by
  classical
  set P : ℝ × ℝ → ℝ := fun p => p.1 + lam * p.2 with hP
  set ν := μ.prod μ with hν
  set Kl := P '' (K ×ˢ K) with hKl
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hKlc : IsCompact Kl := (hK.prod hK).image hPc
  set idx : ℝ → ℤ := fun w => ⌊w / r⌋ with hidx
  have hfin : (idx '' Kl).Finite := by
    obtain ⟨R, hR⟩ := hKlc.isBounded.subset_closedBall 0
    refine (Set.finite_Icc ⌊-R / r⌋ ⌊R / r⌋).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hR hw
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h1
    exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right h1.1 hr.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right h1.2 hr.le)⟩
  set T : Finset ℤ := hfin.toFinset with hT
  set I : ℤ → Set (ℝ × ℝ) := fun k => (fun p => idx (P p)) ⁻¹' {k} with hI
  have hidxm : Measurable fun p => idx (P p) :=
    Int.measurable_floor.comp (hPc.measurable.div_const r)
  have hIm : ∀ k, MeasurableSet (I k) := fun k => hidxm (measurableSet_singleton k)
  have hdisj : Set.PairwiseDisjoint (T : Set ℤ) I := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun p ha hb => hab ?_
    exact (show idx (P p) = a from ha).symm.trans hb
  -- total mass one
  have hmass : (1 : ℝ) ≤ ∑ k ∈ T, (ν (I k)).toReal := by
    have h1 : ν (K ×ˢ K)ᶜ = 0 := by
      refine measure_mono_null (t := (Kᶜ ×ˢ univ) ∪ (univ ×ˢ Kᶜ)) ?_ ?_
      · intro p hp
        by_cases h : p.1 ∈ K
        · exact Or.inr ⟨mem_univ _, fun h2 => hp ⟨h, h2⟩⟩
        · exact Or.inl ⟨h, mem_univ _⟩
      · refine measure_union_null ?_ ?_
        · rw [hν, Measure.prod_prod, hKm, zero_mul]
        · rw [hν, Measure.prod_prod, hKm, mul_zero]
    have h2 : ν (K ×ˢ K) = 1 := (prob_compl_eq_zero_iff (hK.isClosed.prod hK.isClosed).measurableSet).1 h1
    have h3 : K ×ˢ K ⊆ ⋃ k ∈ T, I k := by
      intro p hp
      refine mem_iUnion₂.2 ⟨idx (P p), ?_, rfl⟩
      rw [hT, Set.Finite.mem_toFinset]
      exact ⟨P p, ⟨p, hp, rfl⟩, rfl⟩
    have h4 : (1 : ℝ≥0∞) ≤ ∑ k ∈ T, ν (I k) := by
      rw [← h2]
      exact (measure_mono h3).trans (measure_biUnion_finset_le T I)
    have h5 := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun k _ => measure_ne_top ν _) h4
    rwa [ENNReal.toReal_one, ENNReal.toReal_sum (fun k _ => measure_ne_top ν _)] at h5
  -- squares
  have hsq : ∑ k ∈ T, (ν (I k)).toReal ^ 2 ≤ ((ν.prod ν) (close r lam)).toReal := by
    have h1 : ∑ k ∈ T, (ν.prod ν) (I k ×ˢ I k) = (ν.prod ν) (⋃ k ∈ T, I k ×ˢ I k) := by
      refine (measure_biUnion_finset ?_ fun k _ => (hIm k).prod (hIm k)).symm
      intro a ha b hb hab
      exact Set.disjoint_left.2 fun q hqa hqb => Set.disjoint_left.1 (hdisj ha hb hab) hqa.1 hqb.1
    have h2 : (⋃ k ∈ T, I k ×ˢ I k) ⊆ close r lam := by
      intro q hq
      obtain ⟨k, _, h1, h2⟩ := mem_iUnion₂.1 hq
      have h1' : ⌊P q.1 / r⌋ = k := h1
      have h2' : ⌊P q.2 / r⌋ = k := h2
      have h3 := Int.abs_sub_lt_one_of_floor_eq_floor (h1'.trans h2'.symm)
      rw [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at h3
      exact h3.le
    have h3 := ENNReal.toReal_mono (measure_ne_top _ _) ((h1.le).trans (measure_mono h2))
    rw [ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)] at h3
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h3
    rw [Measure.prod_prod, ENNReal.toReal_mul, sq]
  -- the cells lie in the neighbourhood
  have hcells : (T.card : ℝ≥0∞) * ENNReal.ofReal r ≤ volume (Metric.cthickening r Kl) := by
    set J : ℤ → Set ℝ := fun k => Ico ((k : ℝ) * r) (((k : ℝ) + 1) * r) with hJ
    have hmemJ : ∀ (k : ℤ) (w : ℝ), w ∈ J k ↔ idx w = k := by
      intro k w
      rw [hidx]
      simp only [hJ, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hr, div_lt_iff₀ hr]
    have h1 : (⋃ k ∈ T, J k) ⊆ Metric.cthickening r Kl := by
      intro w hw
      obtain ⟨k, hk, hwk⟩ := mem_iUnion₂.1 hw
      rw [hT, Set.Finite.mem_toFinset] at hk
      obtain ⟨z, hz, hzk⟩ := hk
      refine Metric.mem_cthickening_of_dist_le w z r Kl hz ?_
      have h2 := Int.abs_sub_lt_one_of_floor_eq_floor
        (((hmemJ k w).1 hwk).trans hzk.symm)
      rw [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at h2
      rw [Real.dist_eq]; exact h2.le
    have h3 : volume (⋃ k ∈ T, J k) = ∑ k ∈ T, volume (J k) := by
      refine measure_biUnion_finset ?_ fun k _ => measurableSet_Ico
      intro a _ b _ hab
      exact Set.disjoint_left.2 fun w ha hb => hab (((hmemJ a w).1 ha).symm.trans ((hmemJ b w).1 hb))
    have h4 : ∀ k ∈ T, volume (J k) = ENNReal.ofReal r := by
      intro k _
      rw [hJ]
      simp only [Real.volume_Ico]
      congr 1; ring
    rw [Finset.sum_congr rfl h4, Finset.sum_const, nsmul_eq_mul] at h3
    rw [← h3]
    exact measure_mono h1
  have hCS : (1 : ℝ) ≤ T.card * ((ν.prod ν) (close r lam)).toReal := by
    have h1 : (∑ k ∈ T, (ν (I k)).toReal) ^ 2 ≤ T.card * ∑ k ∈ T, (ν (I k)).toReal ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h2 : (1 : ℝ) ≤ (∑ k ∈ T, (ν (I k)).toReal) ^ 2 := one_le_pow₀ hmass
    exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)))
  have hCS' : (1 : ℝ≥0∞) ≤ T.card * (ν.prod ν) (close r lam) := by
    have h := ENNReal.ofReal_le_ofReal hCS
    rwa [ENNReal.ofReal_one, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  calc ENNReal.ofReal r = ENNReal.ofReal r * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal r * (T.card * (ν.prod ν) (close r lam)) := mul_le_mul_right hCS' _
    _ = (T.card * ENNReal.ofReal r) * (ν.prod ν) (close r lam) := by ring
    _ ≤ volume (Metric.cthickening r Kl) * (ν.prod ν) (close r lam) := mul_le_mul_left hcells _

/-- **The projection estimate.** If `μ(ball r) ≤ M r^s` with `1/2 < s < 1` and `μ` lives on the compact set `K`,
then `K + lam K` has positive measure for almost every `lam ∈ [1,2]`. -/
theorem ae_volume_pos (hs : 1 / 2 < s) (hs1 : s < 1) (hM : 0 ≤ M)
    (hball : ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (M * r ^ s))
    (K : Set ℝ) (hK : IsCompact K) (hKm : μ Kᶜ = 0) :
    ∀ᵐ lam ∂(volume.restrict (Icc (1 : ℝ) 2)),
      0 < volume ((fun p : ℝ × ℝ => p.1 + lam * p.2) '' (K ×ˢ K)) := by
  obtain ⟨C, hC, havg⟩ := average_bound μ s M hs hs1 hM hball
  set r : ℕ → ℝ := fun n => (1 / 2) ^ n with hr
  have hr0 : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hr1 : ∀ n, r n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  set E : ℕ → ℝ → ℝ≥0∞ := fun n lam => ((μ.prod μ).prod (μ.prod μ)) (close (r n) lam) with hE
  have hEm : ∀ n, Measurable (E n) := fun n =>
    measurable_measure_prodMk_left (measurableSet_close_total (r n))
  set f : ℕ → ℝ → ℝ≥0∞ := fun n lam => E n lam * (ENNReal.ofReal (r n))⁻¹ with hf
  have hfm : ∀ n, Measurable (f n) := fun n => (hEm n).mul_const _
  have hint : ∀ n, ∫⁻ lam in Icc (1 : ℝ) 2, f n lam ≤ C := by
    intro n
    have hne : ENNReal.ofReal (r n) ≠ 0 := (ENNReal.ofReal_pos.2 (hr0 n)).ne'
    rw [hf]
    simp only []
    rw [lintegral_mul_const _ (hEm n)]
    refine (mul_le_mul_left (havg (r n) (hr0 n) (hr1 n)) _).trans (le_of_eq ?_)
    rw [mul_assoc, ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, mul_one]
  have hfatou : ∫⁻ lam in Icc (1 : ℝ) 2, liminf (fun n => f n lam) atTop ≤ C := by
    refine (lintegral_liminf_le hfm).trans ?_
    exact liminf_le_of_frequently_le' (Eventually.of_forall hint).frequently
  have hae : ∀ᵐ lam ∂(volume.restrict (Icc (1 : ℝ) 2)), liminf (fun n => f n lam) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hfm) (ne_top_of_le_ne_top hC hfatou)
  refine hae.mono fun lam hlam => ?_
  set Kl := (fun p : ℝ × ℝ => p.1 + lam * p.2) '' (K ×ˢ K) with hKl
  have hKlc : IsCompact Kl := (hK.prod hK).image (by fun_prop)
  set Lim := liminf (fun n => f n lam) atTop with hLim
  have hfreq : ∃ᶠ n in atTop, f n lam < Lim + 1 :=
    frequently_lt_of_liminf_lt (h := ENNReal.lt_add_right hlam.ne one_ne_zero)
  have hlow : ∃ᶠ n in atTop, (Lim + 1)⁻¹ ≤ volume (Metric.cthickening (r n) Kl) := by
    refine hfreq.mono fun n hn => ?_
    have hne : ENNReal.ofReal (r n) ≠ 0 := (ENNReal.ofReal_pos.2 (hr0 n)).ne'
    have h1 := cells μ K hK hKm lam (r n) (hr0 n)
    have h2 : (1 : ℝ≥0∞) ≤ volume (Metric.cthickening (r n) Kl) * f n lam := by
      rw [hf]
      simp only []
      rw [← mul_assoc]
      have h3 := mul_le_mul_left h1 (ENNReal.ofReal (r n))⁻¹
      rwa [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top] at h3
    have h4 : (1 : ℝ≥0∞) ≤ volume (Metric.cthickening (r n) Kl) * (Lim + 1) :=
      h2.trans (mul_le_mul_right hn.le _)
    have h5 : Lim + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hlam.ne, ENNReal.one_ne_top⟩
    have h6 : Lim + 1 ≠ 0 := by simp
    have h7 := mul_le_mul_left h4 (Lim + 1)⁻¹
    rwa [one_mul, mul_assoc, ENNReal.mul_inv_cancel h6 h5, mul_one] at h7
  have htend : Tendsto (fun n => volume (Metric.cthickening (r n) Kl)) atTop (𝓝 (volume Kl)) := by
    have h1 : Tendsto r atTop (𝓝 0) := by
      rw [hr]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact (tendsto_measure_cthickening_of_isCompact (μ := volume) hKlc).comp h1
  have hle : (Lim + 1)⁻¹ ≤ volume Kl := by
    by_contra h
    push Not at h
    have h1 := htend.eventually_lt_const h
    obtain ⟨n, hn1, hn2⟩ := (hlow.and_eventually h1).exists
    exact absurd hn1 (not_le.2 hn2)
  refine lt_of_lt_of_le ?_ hle
  rw [ENNReal.inv_pos]
  exact ENNReal.add_ne_top.2 ⟨hlam.ne, ENNReal.one_ne_top⟩

end Projection

/-! ## The measure on the digit set -/

open Classical in
/-- Digits of `t` placed at the positions outside `Z`. -/
noncomputable def spread (t : ℝ) : ℝ :=
  Real.ofDigits (b := 2) (fun j => if j ∈ Zset then 0 else Real.digits t 2 (freeCount j))

open Classical in
lemma spread_allowed (t : ℝ) :
    Allowed (fun j => if j ∈ Zset then 0 else Real.digits t 2 (freeCount j)) := fun j hj => by simp [hj]

lemma spread_mem (t : ℝ) : spread t ∈ Cset := ⟨_, spread_allowed t, rfl⟩

lemma measurable_spread : Measurable spread := by
  classical
  refine Real.continuous_ofDigits.measurable.comp (Measurable.of_eval fun j => ?_)
  by_cases h : j ∈ Zset
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have h1 : Measurable fun t : ℝ => ⌊(2 : ℝ) * (2 : ℝ) ^ freeCount j * t⌋₊ :=
      Nat.measurable_floor.comp (measurable_const.mul measurable_id)
    have h2 : (fun t : ℝ => Real.digits t 2 (freeCount j)) =
        (fun k : ℕ => (Fin.ofNat 2 k : Fin 2)) ∘ fun t : ℝ => ⌊t * (2 : ℝ) ^ (freeCount j + 1)⌋₊ := by
      funext t
      simp [Real.digits]
    rw [h2]
    exact (measurable_from_nat).comp (Nat.measurable_floor.comp (measurable_id.mul_const _))

lemma holderMap_spread {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : holderMap (spread t) = t := by
  classical
  set g : ℕ → Fin 2 := Real.digits t 2 with hg
  set d : ℕ → Fin 2 := fun j => if j ∈ Zset then 0 else g (freeCount j) with hd
  have hdA : Allowed d := fun j hj => by simp [hd, hj]
  have hsp : spread t = Real.ofDigits d := by
    unfold spread
    congr 1
  have hmem : Real.ofDigits d ∈ Cset := ⟨d, hdA, rfl⟩
  rw [hsp]
  unfold holderMap
  rw [dif_pos hmem]
  obtain ⟨hA, hval⟩ := Classical.choose_spec hmem
  have hsame : Classical.choose hmem = d := by
    by_contra hne
    have hex : ∃ i, Classical.choose hmem i ≠ d i := Function.ne_iff.1 hne
    set j0 := Nat.find hex with hj0
    have h1 : Classical.choose hmem j0 ≠ d j0 := Nat.find_spec hex
    have h2 : ∀ i < j0, Classical.choose hmem i = d i := fun i hi => not_not.1 (Nat.find_min hex hi)
    obtain ⟨j1, hj1, hlt, _⟩ := forced_after j0
    have htwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ (j1 + 1))⁻¹ := by positivity
    rcases htwo (Classical.choose hmem j0) with h | h <;> rcases htwo (d j0) with h' | h'
    · exact h1 (h.trans h'.symm)
    · have := separation d _ hdA hA j0 j1 (fun i hi => (h2 i hi).symm) h' h hj1 hlt
      rw [hval] at this
      linarith
    · have := separation _ d hA hdA j0 j1 h2 h h' hj1 hlt
      rw [hval] at this
      linarith
    · exact h1 (h.trans h'.symm)
  rw [hsame]
  have hcomp : (fun i => d (freePos i)) = g := by
    funext i
    have h1 : freePos i ∉ Zset := freePos_mem i
    have h2 : freeCount (freePos i) = i := Nat.count_nth_of_infinite free_infinite i
    simp [hd, h1, h2]
  rw [hcomp]
  exact Real.ofDigits_digits one_lt_two ht

lemma isCompact_Cset : IsCompact Cset := by
  have h1 : IsClosed {d : ℕ → Fin 2 | Allowed d} := by
    have e1 : {d : ℕ → Fin 2 | Allowed d} = ⋂ j ∈ Zset, {d | d j = 0} := by
      ext d; simp [Allowed]
    rw [e1]
    exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
  have e2 : Cset = (Real.ofDigits (b := 2)) '' {d : ℕ → Fin 2 | Allowed d} := by
    ext a; simp [Cset]
  rw [e2]
  exact h1.isCompact.image Real.continuous_ofDigits

noncomputable def muC : Measure ℝ := Measure.map spread (volume.restrict (Ico (0 : ℝ) 1))

instance : IsProbabilityMeasure muC := by
  refine ⟨?_⟩
  rw [muC, Measure.map_apply measurable_spread MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Ico]
  simp

lemma muC_compl : muC Csetᶜ = 0 := by
  rw [muC, Measure.map_apply measurable_spread isCompact_Cset.isClosed.measurableSet.compl]
  have : spread ⁻¹' Csetᶜ = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ht => ht (spread_mem t)
  rw [this, measure_empty]

lemma muC_ball : ∃ M : ℝ, 0 ≤ M ∧ ∀ x r : ℝ, 0 < r →
    muC (Metric.closedBall x r) ≤ ENNReal.ofReal (M * r ^ (3 / 4 : ℝ)) := by
  have hs0 : (0 : ℝ) < 3 / 4 := by norm_num
  have hs1 : (3 / 4 : ℝ) < 1 := by norm_num
  obtain ⟨c, hc⟩ := exponent_bound (3 / 4) hs0 hs1
  refine ⟨2 ^ c * 2 ^ (3 / 4 : ℝ), mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _),
    fun x r hr => ?_⟩
  rw [muC, Measure.map_apply measurable_spread measurableSet_closedBall,
    Measure.restrict_apply (measurable_spread measurableSet_closedBall)]
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun t ht t' ht' => ?_)
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx := Classical.choose_spec (spread_mem t)
  have hy := Classical.choose_spec (spread_mem t')
  have hest := holder_estimate (3 / 4) hs0 hs1 c hc _ _ hx.1 hy.1
  rw [hx.2, hy.2] at hest
  have hfx : holderMap (spread t) =
      Real.ofDigits (fun i => Classical.choose (spread_mem t) (freePos i)) := dif_pos _
  have hfy : holderMap (spread t') =
      Real.ofDigits (fun i => Classical.choose (spread_mem t') (freePos i)) := dif_pos _
  rw [← hfx, ← hfy, holderMap_spread ht.2, holderMap_spread ht'.2] at hest
  rw [Real.dist_eq]
  refine hest.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  rw [← Real.mul_rpow (by norm_num) hr.le]
  refine Real.rpow_le_rpow (abs_nonneg _) ?_ hs0.le
  have h1 : dist (spread t) x ≤ r := ht.1
  have h2 : dist (spread t') x ≤ r := ht'.1
  have h3 := dist_triangle_right (spread t) (spread t') x
  rw [Real.dist_eq] at h3
  linarith

/-! ## The sum of two groups -/

lemma Agroup_zero : (0 : ℝ) ∈ Agroup := by
  have h := dyadic_mem 0 0
  simpa using h

lemma Agroup_add {a b : ℝ} (ha : a ∈ Agroup) (hb : b ∈ Agroup) : a + b ∈ Agroup := by
  intro ε hε
  filter_upwards [ha (ε / 2) (by linarith), hb (ε / 2) (by linarith)] with k h1 h2 n
  have e1 : (a + b) * dlt k * sT n = a * dlt k * sT n + b * dlt k * sT n := by ring
  rw [e1]
  have := dint_add_le (a * dlt k * sT n) (b * dlt k * sT n)
  have := h1 n
  have := h2 n
  linarith

/-- **Theorem 7.4.** For almost every `lam ∈ [1,2]` every real number is `a + lam b` with `a, b ∈ A(δ)`. -/
theorem ae_sum_eq_univ : ∀ᵐ lam ∂(volume.restrict (Icc (1 : ℝ) 2)),
    ∀ x : ℝ, ∃ a ∈ Agroup, ∃ b ∈ Agroup, x = a + lam * b := by
  obtain ⟨M, hM, hball⟩ := muC_ball
  have h := ae_volume_pos muC (3 / 4) M (by norm_num) (by norm_num) hM hball Cset isCompact_Cset muC_compl
  refine h.mono fun lam hlam => ?_
  set Kl := (fun p : ℝ × ℝ => p.1 + lam * p.2) '' (Cset ×ˢ Cset) with hKl
  have hKlc : IsCompact Kl := (isCompact_Cset.prod isCompact_Cset).image (by fun_prop)
  let H : AddSubgroup ℝ :=
    { carrier := {x | ∃ a ∈ Agroup, ∃ b ∈ Agroup, x = a + lam * b}
      zero_mem' := ⟨0, Agroup_zero, 0, Agroup_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a + a', Agroup_add ha ha', b + b', Agroup_add hb hb', by ring⟩
      neg_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨-a, Agroup_neg ha, -b, Agroup_neg hb, by ring⟩ }
  have hsub : Kl ⊆ H := by
    rintro _ ⟨⟨a, b⟩, ⟨⟨d, hd, rfl⟩, ⟨d', hd', rfl⟩⟩, rfl⟩
    exact ⟨_, ofDigits_mem d hd, _, ofDigits_mem d' hd', rfl⟩
  have hnhds : Kl - Kl ∈ 𝓝 (0 : ℝ) :=
    Measure.sub_mem_nhds_zero_of_addHaar_pos volume Kl hKlc.isClosed.measurableSet hlam
  have hH : (H : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    refine mem_of_superset hnhds ?_
    rintro _ ⟨y, hy, z, hz, rfl⟩
    exact H.sub_mem (hsub hy) (hsub hz)
  intro x
  have h1 : Tendsto (fun N : ℕ => x / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat x
  obtain ⟨N, hN, hN1⟩ := ((h1.eventually hH).and (eventually_ge_atTop 1)).exists
  have h2 : N • (x / N) = x := by
    rw [nsmul_eq_mul]
    have : (N : ℝ) ≠ 0 := by
      have : 0 < N := hN1
      positivity
    field_simp
  have h3 : x ∈ H := by
    have := H.nsmul_mem hN N
    rwa [h2] at this
  exact h3

/-- Total boundedness of `aS` for `γ_δ` when `a ∈ A(δ)`. -/
lemma tb_gam (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (a : ℝ) (ha : InA δ sT a) :
    Tb (@nhds ℝ (gamTop δ) 0) (dil a Sset) := by
  have hneg : InA δ sT (-a) := by
    intro ε hε
    filter_upwards [ha ε hε] with k hk n
    have e1 : -a * δ k * sT n = -(a * δ k * sT n) := by ring
    rw [e1, dint_neg]; exact hk n
  refine tb_of_trace _ a (trace_eq δ sT hδ 1 [a, -a] (fun b hb => ?_) (Ja a) ?_)
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · rw [List.mem_singleton] at hb; subst hb; exact hneg
  · rintro x ⟨s, hs, t, ht, rfl⟩
    refine Set.mem_add.2 ⟨0, ⟨by norm_num, by norm_num⟩, a * s + -a * t, ?_, by simp⟩
    refine Set.mem_add.2 ⟨a • s, Set.smul_mem_smul_set (Sset_subset_Tset hs), -a * t, ?_, rfl⟩
    exact Set.mem_add.2 ⟨-a • t, Set.smul_mem_smul_set (Sset_subset_Tset ht), 0, by simp [sumT], by simp⟩

lemma tb_sum (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (a b : ℝ)
    (ha : Tb (@nhds ℝ γ 0) (dil a Sset)) (hb : Tb (@nhds ℝ γ 0) (dil b Sset)) :
    Tb (@nhds ℝ γ 0) (dil (a + b) Sset) := by
  classical
  intro W hW
  letI : TopologicalSpace ℝ := γ
  haveI : IsTopologicalAddGroup ℝ := hg
  obtain ⟨V, hV, hsub⟩ := exists_nhds_zero_half hW
  obtain ⟨F, hF⟩ := ha V hV
  obtain ⟨F', hF'⟩ := hb V hV
  refine ⟨(F ×ˢ F').image (fun p => p.1 + p.2), ?_⟩
  rintro y ⟨s, hs, rfl⟩
  obtain ⟨f, hf, h1⟩ := hF (a * s) ⟨s, hs, rfl⟩
  obtain ⟨f', hf', h2⟩ := hF' (b * s) ⟨s, hs, rfl⟩
  refine ⟨f + f', Finset.mem_image.2 ⟨(f, f'), Finset.mem_product.2 ⟨hf, hf'⟩, rfl⟩, ?_⟩
  have e1 : (a + b) * s - (f + f') = (a * s - f) + (b * s - f') := by ring
  show (a + b) * s - (f + f') ∈ W
  rw [e1]
  exact hsub _ h1 _ h2

/-- **Corollary 7.5.** Two groups, each served by a locally quasi-convex topology, whose union is served by no
group topology. -/
theorem exists_two_unservable : ∃ lam : ℝ, lam ∈ Icc (1 : ℝ) 2 ∧
    (∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a ∈ Agroup, Tb (@nhds ℝ γ 0) (dil a Sset)) →
      (∀ a ∈ Agroup, Tb (@nhds ℝ γ 0) (dil (lam * a) Sset)) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) ∧
    (∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → gamTop dlt ≤ γ →
      gamTop (fun k => dlt k / lam) ≤ γ →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) := by
  have hne : (ae (volume.restrict (Icc (1 : ℝ) 2))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    norm_num
  obtain ⟨lam, hlam, hmem⟩ := (ae_sum_eq_univ.and (ae_restrict_mem measurableSet_Icc)).exists
  have hd2 : Tendsto (fun k => dlt k / lam) atTop (𝓝 0) := by
    have := dlt_tendsto.div_const lam
    rwa [zero_div] at this
  have hlam0 : lam ≠ 0 := by
    have : (0 : ℝ) < lam := by linarith [hmem.1]
    exact this.ne'
  have hfirst : ∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a ∈ Agroup, Tb (@nhds ℝ γ 0) (dil a Sset)) →
      (∀ a ∈ Agroup, Tb (@nhds ℝ γ 0) (dil (lam * a) Sset)) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
    intro γ hg heu h1 h2
    refine group_tb_of_dilates γ hg heu Sset Sset_unbounded fun x => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hlam x
    exact tb_sum γ hg a (lam * b) (h1 a ha) (h2 b hb)
  refine ⟨lam, hmem, hfirst, fun γ hg h1 h2 => ?_⟩
  have hM : ∀ k, |dlt k| ≤ 1 := by
    intro k
    rw [abs_of_pos (dlt_pos k)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have heu : euclidNhds 0 ≤ @nhds ℝ γ 0 :=
    (gam_coarser_euclid dlt 1 hM 0).trans (nhds_mono h1)
  have hmono : ∀ (τ : TopologicalSpace ℝ), τ ≤ γ → ∀ a : ℝ,
      Tb (@nhds ℝ τ 0) (dil a Sset) → Tb (@nhds ℝ γ 0) (dil a Sset) :=
    fun τ hτ a h V hV => h V (nhds_mono hτ hV)
  refine hfirst γ hg heu (fun a ha => hmono _ h1 a (tb_gam dlt dlt_tendsto a ha)) (fun a ha => ?_)
  refine hmono _ h2 _ (tb_gam _ hd2 _ ?_)
  intro ε hε
  filter_upwards [ha ε hε] with k hk n
  have e1 : lam * a * (dlt k / lam) * sT n = a * dlt k * sT n := by field_simp
  rw [e1]; exact hk n

end Two
end PVG
