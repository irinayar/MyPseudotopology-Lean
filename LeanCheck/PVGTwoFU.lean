import Mathlib
import LeanCheck.PVGTwoServed

/-!
# PVGtwo, Section 8: a Fréchet–Urysohn pseudotopological vector group (Lean check)

Scope. `sT n = 2^((n+1)^2)`. `Stail N` is `{0} ∪ {±sT n : n ≥ N}`, `Bset a N` is `(-1/(N+1), 1/(N+1)) + a₁ Stail N + ⋯`.
`UConv U x` says that the ultrafilter `U` contains, for one finite tuple `a` and all `N`, the set `x + Bset a N`.
`TConv F x` says that every ultrafilter finer than `F` does so. In Mathlib's order `F ≤ G` means that `F` is finer.

* `tconv_pure`, `tconv_mono`, `tconv_of_ultra` : the axioms of a pseudotopology;
* `tconv_add`, `tconv_mul` : addition and the dilations are continuous;
* `tconv_nhds` : coarser than the usual convergence; `tconv_sT` : the sequence `sT` converges to `0`;
* `tconv_unique` : Hausdorff;
* `tconv_frechet` : Fréchet–Urysohn;
* `tconv_not_pretopological` : the intersection of all filters converging to `0` does not converge to `0`;
* `xi_iff` : the lacunary PVG is the combination of this convergence with the Bohr topology.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-! ## The convergence -/

def Stail (N : ℕ) : Set ℝ := {x | x = 0 ∨ ∃ n, N ≤ n ∧ (x = sT n ∨ x = -sT n)}

def Bset {r : ℕ} (a : Fin r → ℝ) (N : ℕ) : Set ℝ :=
  {x | ∃ u : ℝ, |u| < 1 / (N + 1) ∧ ∃ σ : Fin r → ℝ, (∀ i, σ i ∈ Stail N) ∧ x = u + ∑ i, a i * σ i}

def UConv (U : Ultrafilter ℝ) (x : ℝ) : Prop :=
  ∃ (r : ℕ) (a : Fin r → ℝ), ∀ N : ℕ, {z | z - x ∈ Bset a N} ∈ U

def TConv (F : Filter ℝ) (x : ℝ) : Prop := ∀ U : Ultrafilter ℝ, (U : Filter ℝ) ≤ F → UConv U x

lemma Stail_anti {M N : ℕ} (h : N ≤ M) : Stail M ⊆ Stail N := by
  rintro x (rfl | ⟨n, hn, h'⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨n, h.trans hn, h'⟩

lemma Bset_anti {r : ℕ} (a : Fin r → ℝ) {M N : ℕ} (h : N ≤ M) : Bset a M ⊆ Bset a N := by
  rintro x ⟨u, hu, σ, hσ, rfl⟩
  refine ⟨u, hu.trans_le ?_, σ, fun i => Stail_anti h (hσ i), rfl⟩
  have h' : (N : ℝ) ≤ M := by exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma zero_mem_Stail (N : ℕ) : (0 : ℝ) ∈ Stail N := Or.inl rfl

/-- (P1) -/
theorem tconv_pure (x : ℝ) : TConv (pure x) x := by
  intro U hU
  refine ⟨0, Fin.elim0, fun N => hU (mem_pure.2 ?_)⟩
  refine ⟨0, by rw [abs_zero]; positivity, Fin.elim0, fun i => i.elim0, by simp⟩

/-- (P2) -/
theorem tconv_mono {F G : Filter ℝ} {x : ℝ} (h : TConv G x) (hFG : F ≤ G) : TConv F x :=
  fun U hU => h U (hU.trans hFG)

/-- (P3) -/
theorem tconv_of_ultra {F : Filter ℝ} {x : ℝ} (h : ∀ U : Ultrafilter ℝ, (U : Filter ℝ) ≤ F → TConv U x) :
    TConv F x :=
  fun U hU => h U hU U le_rfl

/-- Addition is continuous. -/
theorem tconv_add {F G : Filter ℝ} {x y : ℝ} (hF : TConv F x) (hG : TConv G y) :
    TConv (Filter.map₂ (· + ·) F G) (x + y) := by
  intro W hW
  rw [← Filter.map_prod_eq_map₂] at hW
  set p : ℝ × ℝ → ℝ := fun q => q.1 + q.2 with hp
  have hne : (comap p (W : Filter ℝ) ⊓ (F ×ˢ G)).NeBot := by
    refine inf_neBot_iff.2 fun {s} hs {t} ht => ?_
    obtain ⟨s', hs', hss⟩ := mem_comap.1 hs
    have h1 : p '' t ∈ map p (F ×ˢ G) := image_mem_map ht
    have h2 : (s' ∩ p '' t) ∈ (W : Filter ℝ) := inter_mem hs' (hW h1)
    obtain ⟨w, hw1, q, hq, rfl⟩ := Ultrafilter.nonempty_of_mem h2
    exact ⟨q, hss hw1, hq⟩
  set H : Ultrafilter (ℝ × ℝ) := Ultrafilter.of (comap p (W : Filter ℝ) ⊓ (F ×ˢ G)) with hH
  have hHle : (H : Filter (ℝ × ℝ)) ≤ comap p (W : Filter ℝ) ⊓ (F ×ˢ G) := Ultrafilter.of_le _
  have hHW : H.map p = W := by
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_map]
    exact map_le_iff_le_comap.2 (hHle.trans inf_le_left)
  have h1 : ((H.map Prod.fst : Ultrafilter ℝ) : Filter ℝ) ≤ F := by
    rw [Ultrafilter.coe_map]
    exact (map_mono (hHle.trans inf_le_right)).trans tendsto_fst
  have h2 : ((H.map Prod.snd : Ultrafilter ℝ) : Filter ℝ) ≤ G := by
    rw [Ultrafilter.coe_map]
    exact (map_mono (hHle.trans inf_le_right)).trans tendsto_snd
  obtain ⟨r, a, ha⟩ := hF _ h1
  obtain ⟨s, b, hb⟩ := hG _ h2
  refine ⟨r + s, Fin.append a b, fun N => ?_⟩
  have h3 : {z | z - x ∈ Bset a (2 * N + 1)} ∈ H.map Prod.fst := ha _
  have h4 : {z | z - y ∈ Bset b (2 * N + 1)} ∈ H.map Prod.snd := hb _
  rw [← hHW]
  refine Ultrafilter.mem_map.2 ?_
  filter_upwards [Ultrafilter.mem_map.1 h3, Ultrafilter.mem_map.1 h4] with q hq1 hq2
  obtain ⟨u, hu, σ, hσ, e1⟩ := hq1
  obtain ⟨v, hv, τ, hτ, e2⟩ := hq2
  show q.1 + q.2 - (x + y) ∈ Bset (Fin.append a b) N
  refine ⟨u + v, ?_, Fin.append σ τ, fun i => ?_, ?_⟩
  · have h5 : (1 : ℝ) / ((2 * N + 1 : ℕ) + 1) + 1 / ((2 * N + 1 : ℕ) + 1) = 1 / (N + 1) := by
      push_cast
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      field_simp
      ring
    have h6 := abs_add_le u v
    linarith
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact Stail_anti (by omega) (hσ j)
    · rw [Fin.append_right]; exact Stail_anti (by omega) (hτ j)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e3 : q.1 + q.2 - (x + y) = (q.1 - x) + (q.2 - y) := by ring
    rw [e3, e1, e2]; ring

/-- The dilations are continuous. -/
theorem tconv_mul {F : Filter ℝ} {x : ℝ} (c : ℝ) (hF : TConv F x) : TConv (map (fun z => c * z) F) (c * x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h1 : map (fun z : ℝ => 0 * z) F ≤ pure (0 * x) := by
      rw [le_pure_iff]
      exact mem_map.2 (by simp)
    exact tconv_mono (tconv_pure _) h1
  intro W hW
  have hinv : ((W.map fun z => c⁻¹ * z : Ultrafilter ℝ) : Filter ℝ) ≤ F := by
    rw [Ultrafilter.coe_map]
    refine (map_mono hW).trans ?_
    rw [map_map]
    have : ((fun z => c⁻¹ * z) ∘ fun z => c * z) = id := by
      funext z; simp [← mul_assoc, hc]
    rw [this, map_id]
  obtain ⟨r, a, ha⟩ := hF _ hinv
  refine ⟨r, fun i => c * a i, fun N => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ M ∧ |c| * (1 / (M + 1)) ≤ 1 / (N + 1) := by
    obtain ⟨K, hK⟩ := exists_nat_ge (|c| * (N + 1))
    refine ⟨max N K, le_max_left _ _, ?_⟩
    have h1 : (K : ℝ) ≤ (max N K : ℕ) := by exact_mod_cast le_max_right N K
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    linarith
  have h2 := Ultrafilter.mem_map.1 (ha M)
  refine mem_of_superset h2 fun w hw => ?_
  obtain ⟨u, hu, σ, hσ, e1⟩ := hw
  show w - c * x ∈ Bset (fun i => c * a i) N
  refine ⟨c * u, ?_, σ, fun i => Stail_anti hM.1 (hσ i), ?_⟩
  · rw [abs_mul]
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left hu (abs_pos.2 hc)) hM.2
  · have e2 : w - c * x = c * (c⁻¹ * w - x) := by field_simp
    rw [e2, e1, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Coarser than the usual convergence. -/
theorem tconv_nhds (x : ℝ) : TConv (𝓝 x) x := by
  intro U hU
  refine ⟨0, Fin.elim0, fun N => hU ?_⟩
  have h : Metric.ball x (1 / (N + 1)) ∈ 𝓝 x := Metric.ball_mem_nhds x (by positivity)
  refine mem_of_superset h fun z hz => ?_
  rw [Metric.mem_ball, Real.dist_eq] at hz
  exact ⟨z - x, hz, Fin.elim0, fun i => i.elim0, by simp⟩

/-- The unbounded sequence `sT` converges to `0`. -/
theorem tconv_sT : TConv (map sT atTop) 0 := by
  intro U hU
  refine ⟨1, fun _ => 1, fun N => hU ?_⟩
  rw [mem_map]
  filter_upwards [eventually_ge_atTop N] with n hn
  show sT n - 0 ∈ Bset (fun _ : Fin 1 => (1 : ℝ)) N
  exact ⟨0, by rw [abs_zero]; positivity, fun _ => sT n, fun _ => Or.inr ⟨n, hn, Or.inl rfl⟩, by simp⟩

/-! ## The limit relation -/

open Classical in
/-- If `∑ c_i sT(n_i k)` converges along an ultrafilter along which all indices `n_i` tend to infinity, the limit is `0`
and the coefficients belonging to each image ultrafilter add up to `0`. -/
lemma limit_relation {ι α : Type*} [Fintype ι] (Q : Ultrafilter α) (c : ι → ℝ) (n : ι → α → ℕ)
    (hfree : ∀ i, Free (Q.map (n i))) (t : ℝ)
    (h : Tendsto (fun k => ∑ i, c i * sT (n i k)) (Q : Filter α) (euclidNhds t)) :
    t = 0 ∧ ∀ U : Ultrafilter ℕ,
      ∑ i ∈ Finset.univ.filter (fun i => Q.map (n i) = U), c i = 0 := by
  classical
  set W : ι → Ultrafilter ℕ := fun i => Q.map (n i) with hW
  have h1 : Tendsto (fun k => e (∑ i, c i * sT (n i k))) (Q : Filter α) (𝓝 (e t)) :=
    (continuous_e.tendsto t).comp h
  have h2 : Tendsto (fun k => ∑ i, c i • e (sT (n i k))) (Q : Filter α) (𝓝 (∑ i, c i • L sT (W i))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have h3 : Tendsto (n i) (Q : Filter α) (W i : Filter ℕ) := by
      show Filter.map _ _ ≤ _
      exact le_of_eq (Ultrafilter.coe_map _ _).symm
    exact ((continuous_smul_const (c i)).tendsto _).comp ((tendsto_L sT (W i)).comp h3)
  have h4 : (fun k => e (∑ i, c i * sT (n i k))) = fun k => ∑ i, c i • e (sT (n i k)) := by
    funext k
    show eHom (∑ i, c i * sT (n i k)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (smul_e _ _).symm
  rw [h4] at h1
  have heq : e t = ∑ i, c i • L sT (W i) := tendsto_nhds_unique h1 h2
  set s : Finset (Ultrafilter ℕ) := Finset.univ.image W with hs
  set g : Ultrafilter ℕ → ℝ := fun U => ∑ i ∈ Finset.univ.filter (fun i => W i = U), c i with hg
  have hfib : ∑ U ∈ s, g U • L sT U = ∑ i, c i • L sT (W i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := W) (t := s) (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun U _ => ?_
    simp only [hg]
    rw [sum_smul_K]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  have hfr : ∀ U ∈ s, Free U := by
    intro U hU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hU
    exact hfree i
  have hg0 := independence_finset sT sT_ne sT_ratio s hfr g t (by rw [hfib, heq])
  have ht : t = 0 := by
    refine e_eq_zero ?_
    rw [heq, ← hfib]
    exact Finset.sum_eq_zero fun U hU => by rw [hg0 U hU]; exact zero_smul_K _
  refine ⟨ht, fun U => ?_⟩
  by_cases hU : U ∈ s
  · exact hg0 U hU
  · refine Finset.sum_eq_zero fun i hi => absurd ?_ hU
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, (Finset.mem_filter.1 hi).2⟩

/-! ## Hausdorff -/

lemma Stail_repr {N : ℕ} {σ : ℝ} (h : σ ∈ Stail N) :
    ∃ c ∈ ({-1, 0, 1} : Finset ℝ), ∃ n, N ≤ n ∧ σ = c * sT n := by
  rcases h with rfl | ⟨n, hn, rfl | rfl⟩
  · exact ⟨0, by simp, N, le_rfl, by simp⟩
  · exact ⟨1, by simp, n, hn, by simp⟩
  · exact ⟨-1, by simp, n, hn, by simp⟩

lemma const_sign {α : Type*} (Q : Ultrafilter α) (c : α → ℝ) (h : ∀ᶠ k in (Q : Filter α), c k ∈ ({-1, 0, 1} : Finset ℝ)) :
    ∃ d ∈ ({-1, 0, 1} : Finset ℝ), ∀ᶠ k in (Q : Filter α), c k = d := by
  have hex : ∀ᶠ k in (Q : Filter α), ∃ d ∈ (({-1, 0, 1} : Finset ℝ) : Set ℝ), c k = d :=
    h.mono fun k hk => ⟨c k, hk, rfl⟩
  obtain ⟨d, hd, h'⟩ := (Ultrafilter.eventually_exists_mem_iff (Finset.finite_toSet _)).1 hex
  exact ⟨d, hd, h'⟩

lemma free_of_tendsto {α : Type*} (Q : Ultrafilter α) (n : α → ℕ) (h : Tendsto n (Q : Filter α) atTop) :
    Free (Q.map n) := by
  show ((Q.map n : Ultrafilter ℕ) : Filter ℕ) ≤ cofinite
  rw [Ultrafilter.coe_map, Nat.cofinite_eq_atTop]
  exact h

/-- Hausdorff. -/
theorem tconv_unique {F : Filter ℝ} [F.NeBot] {x y : ℝ} (hx : TConv F x) (hy : TConv F y) : x = y := by
  classical
  set U : Ultrafilter ℝ := Ultrafilter.of F with hU
  have hUF : (U : Filter ℝ) ≤ F := Ultrafilter.of_le F
  obtain ⟨r, a, ha⟩ := hx U hUF
  obtain ⟨s, b, hb⟩ := hy U hUF
  set Q : Ultrafilter ℕ := hyperfilter ℕ with hQ
  have hQat : (Q : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
  have hz : ∀ N, ∃ z, z - x ∈ Bset a N ∧ z - y ∈ Bset b N := by
    intro N
    obtain ⟨z, h1, h2⟩ := Ultrafilter.nonempty_of_mem (inter_mem (ha N) (hb N))
    exact ⟨z, h1, h2⟩
  choose z hzx hzy using hz
  choose u hu σ hσ ex using hzx
  choose v hv τ hτ ey using hzy
  choose ca hca na hna eσ using fun N i => Stail_repr (hσ N i)
  choose cb hcb nb hnb eτ using fun N i => Stail_repr (hτ N i)
  have hda := fun i => const_sign Q (fun N => ca N i) (Eventually.of_forall fun N => hca N i)
  have hdb := fun i => const_sign Q (fun N => cb N i) (Eventually.of_forall fun N => hcb N i)
  choose da _ hda using hda
  choose db _ hdb using hdb
  set c : Fin r ⊕ Fin s → ℝ := Sum.elim (fun i => a i * da i) (fun j => -(b j * db j)) with hc
  set n : Fin r ⊕ Fin s → ℕ → ℕ := Sum.elim (fun i N => na N i) (fun j N => nb N j) with hn
  have hfree : ∀ i, Free (Q.map (n i)) := by
    rintro (i | j)
    · exact free_of_tendsto Q _ (tendsto_atTop_mono (fun N => hna N i) (tendsto_id'.2 hQat))
    · exact free_of_tendsto Q _ (tendsto_atTop_mono (fun N => hnb N j) (tendsto_id'.2 hQat))
  have hsmall : ∀ w : ℕ → ℝ, (∀ N, |w N| < 1 / (N + 1)) → Tendsto w (Q : Filter ℕ) (𝓝 0) := by
    intro w hw
    have h1 : Tendsto w atTop (𝓝 0) :=
      squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact (hw N).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.mono_left hQat
  have hlim : Tendsto (fun N => ∑ i, c i * sT (n i N)) (Q : Filter ℕ) (𝓝 (y - x)) := by
    have h1 : Tendsto (fun N => (y - x) + (v N - u N)) (Q : Filter ℕ) (𝓝 ((y - x) + (0 - 0))) :=
      tendsto_const_nhds.add ((hsmall v hv).sub (hsmall u hu))
    rw [sub_zero, add_zero] at h1
    refine h1.congr' ?_
    have h2 : ∀ᶠ N in (Q : Filter ℕ), (∀ i, ca N i = da i) ∧ ∀ j, cb N j = db j :=
      (eventually_all.2 hda).and (eventually_all.2 hdb)
    filter_upwards [h2] with N hN
    have e1 : ∑ i, c i * sT (n i N) = ∑ i, a i * σ N i - ∑ j, b j * τ N j := by
      rw [Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hc, hn, Sum.elim_inl]
        rw [eσ N i, hN.1 i]; ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc, hn, Sum.elim_inr]
        rw [eτ N j, hN.2 j]; ring
    have e2 := ex N
    have e3 := ey N
    rw [e1]; linarith
  have := (limit_relation Q c n hfree (y - x) hlim).1
  linarith

/-! ## Fréchet–Urysohn -/

theorem tconv_frechet (A : Set ℝ) (x : ℝ) (h : ∃ F : Filter ℝ, F.NeBot ∧ A ∈ F ∧ TConv F x) :
    ∃ z : ℕ → ℝ, (∀ n, z n ∈ A) ∧ TConv (map z atTop) x := by
  obtain ⟨F, hF, hAF, hc⟩ := h
  haveI := hF
  set U : Ultrafilter ℝ := Ultrafilter.of F with hU
  have hUF : (U : Filter ℝ) ≤ F := Ultrafilter.of_le F
  obtain ⟨r, a, ha⟩ := hc U hUF
  have hz : ∀ N, ∃ z, z ∈ A ∧ z - x ∈ Bset a N := by
    intro N
    obtain ⟨z, h1, h2⟩ := Ultrafilter.nonempty_of_mem (inter_mem (hUF hAF) (ha N))
    exact ⟨z, h1, h2⟩
  choose z hzA hzB using hz
  refine ⟨z, hzA, fun H hH => ⟨r, a, fun N => hH ?_⟩⟩
  rw [mem_map]
  filter_upwards [eventually_ge_atTop N] with k hk
  exact Bset_anti a hk (hzB k)

/-! ## Representation of elements of the lacunary ideal -/

lemma split_ultra {α : Type*} (Q : Ultrafilter α) {r : ℕ} (b : Fin r → ℝ) (c : α → Fin r → ℝ) (m : α → Fin r → ℕ)
    (hc : ∀ᶠ k in (Q : Filter α), ∀ i, c k i ∈ ({-1, 0, 1} : Finset ℝ)) :
    ∃ (d : Fin r → ℝ) (I : Finset (Fin r)) (c0 : ℝ), (∀ i, d i ∈ ({-1, 0, 1} : Finset ℝ)) ∧
      (∀ i ∈ I, Tendsto (fun k => m k i) (Q : Filter α) atTop) ∧
      ∀ᶠ k in (Q : Filter α), ∑ i, b i * (c k i * sT (m k i)) = c0 + ∑ i ∈ I, b i * (d i * sT (m k i)) := by
  classical
  have hd := fun i => const_sign Q (fun k => c k i) (hc.mono fun k h => h i)
  choose d hd hdev using hd
  set I : Finset (Fin r) := Finset.univ.filter fun i => Tendsto (fun k => m k i) (Q : Filter α) atTop with hI
  have hk : ∀ i, ∃ j : ℕ, ¬ Tendsto (fun k => m k i) (Q : Filter α) atTop → ∀ᶠ k in (Q : Filter α), m k i = j := by
    intro i
    by_cases h : Tendsto (fun k => m k i) (Q : Filter α) atTop
    · exact ⟨0, fun h' => absurd h h'⟩
    rcases (Q.map fun k => m k i).le_cofinite_or_eq_pure with h1 | ⟨j, hj⟩
    · refine absurd ?_ h
      rw [Ultrafilter.coe_map, Nat.cofinite_eq_atTop] at h1
      exact h1
    · refine ⟨j, fun _ => ?_⟩
      have h2 : ({j} : Set ℕ) ∈ Q.map fun k => m k i := by rw [hj]; exact Ultrafilter.mem_pure.2 rfl
      exact Ultrafilter.mem_map.1 h2
  choose j hj using hk
  refine ⟨d, I, ∑ i ∈ Finset.univ.filter (fun i => ¬ Tendsto (fun k => m k i) (Q : Filter α) atTop),
    b i * (d i * sT (j i)), hd, fun i hi => (Finset.mem_filter.1 hi).2, ?_⟩
  have h2 : ∀ᶠ k in (Q : Filter α), ∀ i, ¬ Tendsto (fun k => m k i) (Q : Filter α) atTop → m k i = j i := by
    refine eventually_all.2 fun i => ?_
    by_cases h : Tendsto (fun k => m k i) (Q : Filter α) atTop
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · exact (hj i h).mono fun k hk _ => hk
  filter_upwards [eventually_all.2 hdev, h2] with k h1 h2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => Tendsto (fun k => m k i) (Q : Filter α) atTop), add_comm, hI]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h1 i, h2 i (Finset.mem_filter.1 hi).2]
  · exact Finset.sum_congr rfl fun i _ => by rw [h1 i]

/-! ## Not pretopological -/

theorem tconv_not_pretopological : ¬ TConv (sSup {F : Filter ℝ | TConv F 0}) 0 := by
  classical
  intro hV
  set Q : Ultrafilter ℕ := hyperfilter ℕ with hQ
  have hQat : (Q : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
  have hQfree : Free (Q.map id) := free_of_tendsto Q id (tendsto_id'.2 hQat)
  set a : ℕ → ℝ := fun j => (j : ℝ) + 1 with ha
  set Uj : ℕ → Ultrafilter ℝ := fun j => Q.map fun n => a j * sT n with hUj
  have hconv : ∀ j, TConv (Uj j : Filter ℝ) 0 := by
    intro j H hH
    have hHj : H = Uj j := Ultrafilter.coe_le_coe.1 hH
    refine ⟨1, fun _ => a j, fun N => ?_⟩
    rw [hHj]
    refine Ultrafilter.mem_map.2 ?_
    filter_upwards [hQat (eventually_ge_atTop N)] with n hn
    show a j * sT n - 0 ∈ Bset (fun _ : Fin 1 => a j) N
    exact ⟨0, by rw [abs_zero]; positivity, fun _ => sT n, fun _ => Or.inr ⟨n, hn, Or.inl rfl⟩, by simp⟩
  set U : Ultrafilter ℝ := Q.bind Uj with hUdef
  have hUmem : ∀ s : Set ℝ, s ∈ U ↔ {j | s ∈ Uj j} ∈ Q := fun s => Iff.rfl
  have hUV : (U : Filter ℝ) ≤ sSup {F : Filter ℝ | TConv F 0} := by
    intro s hs
    rw [mem_sSup] at hs
    refine (hUmem s).2 ?_
    have : {j | s ∈ Uj j} = univ := eq_univ_of_forall fun j => hs _ (hconv j)
    rw [this]; exact univ_mem
  obtain ⟨r, b, hb⟩ := hV U hUV
  set Fb : Finset ℝ := (Fintype.piFinset fun _ : Fin r => ({-1, 0, 1} : Finset ℝ)).biUnion
    (fun d => Finset.univ.powerset.image fun I : Finset (Fin r) => ∑ i ∈ I, b i * d i) with hFb
  have hkey : ∀ j, {z : ℝ | z - 0 ∈ Bset b 0} ∈ Uj j → a j ∈ Fb := by
    intro j hj
    have h1 : ∀ᶠ n in (Q : Filter ℕ), a j * sT n - 0 ∈ Bset b 0 := Ultrafilter.mem_map.1 hj
    have h2 : ∀ n, ∃ (u : ℝ) (c : Fin r → ℝ) (m : Fin r → ℕ), a j * sT n - 0 ∈ Bset b 0 →
        |u| ≤ 1 ∧ (∀ i, c i ∈ ({-1, 0, 1} : Finset ℝ)) ∧ a j * sT n = u + ∑ i, b i * (c i * sT (m i)) := by
      intro n
      by_cases h : a j * sT n - 0 ∈ Bset b 0
      · obtain ⟨u, hu, σ, hσ, e1⟩ := h
        choose c hc m _ em using fun i => Stail_repr (hσ i)
        refine ⟨u, c, m, fun _ => ⟨?_, hc, ?_⟩⟩
        · simpa using hu.le
        · rw [sub_zero] at e1
          rw [e1]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [← em i]
      · exact ⟨0, fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
    choose u c m h2 using h2
    obtain ⟨d, I, c0, hd, hI, hsplit⟩ := split_ultra Q b c m
      (h1.mono fun n hn => (h2 n hn).2.1)
    obtain ⟨u0, _, hu0⟩ : ∃ u0 ∈ Icc (-1 : ℝ) 1, ((Q.map u : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓝 u0 := by
      refine isCompact_Icc.ultrafilter_le_nhds (Q.map u) ?_
      rw [le_principal_iff]
      exact Ultrafilter.mem_map.2 (h1.mono fun n hn => abs_le.1 (h2 n hn).1)
    have hu : Tendsto u (Q : Filter ℕ) (𝓝 u0) := by
      rw [Ultrafilter.coe_map] at hu0; exact hu0
    set cc : Option I → ℝ := fun o => o.elim (a j) (fun i => -(b i.1 * d i.1)) with hcc
    set nn : Option I → ℕ → ℕ := fun o k => o.elim k (fun i => m k i.1) with hnn
    have hfree : ∀ o, Free (Q.map (nn o)) := by
      rintro (_ | i)
      · exact hQfree
      · exact free_of_tendsto Q _ (hI i.1 i.2)
    have hlim : Tendsto (fun k => ∑ o, cc o * sT (nn o k)) (Q : Filter ℕ) (𝓝 (u0 + c0)) := by
      refine (hu.add_const c0).congr' ?_
      filter_upwards [h1, hsplit] with k hk hs
      have e1 : ∑ o, cc o * sT (nn o k) = a j * sT k - ∑ i ∈ I, b i * (d i * sT (m k i)) := by
        rw [Fintype.sum_option, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        rw [← Finset.sum_coe_sort I (fun i => -(b i * (d i * sT (m k i))))]
        exact Finset.sum_congr rfl fun i _ => by simp only [hcc, hnn, Option.elim]; ring
      rw [e1, (h2 k hk).2.2, hs]; ring
    have hrel := (limit_relation Q cc nn hfree _ hlim).2 (Q.map id)
    have e2 : ∑ o ∈ Finset.univ.filter (fun o => Q.map (nn o) = Q.map id), cc o =
        a j - ∑ i ∈ I.filter (fun i => Q.map (fun k => m k i) = Q.map id), b i * d i := by
      rw [Finset.sum_filter, Fintype.sum_option]
      have h0 : Q.map (nn none) = Q.map id := rfl
      rw [if_pos h0, sub_eq_add_neg, Finset.sum_filter, ← Finset.sum_neg_distrib]
      congr 1
      rw [← Finset.sum_coe_sort I (fun i => -(if Q.map (fun k => m k i) = Q.map id then b i * d i else 0))]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h3 : Q.map (nn (some i)) = Q.map (fun k => m k i.1) := rfl
      rw [h3]
      split <;> simp [hcc]
    rw [e2] at hrel
    have e3 : a j = ∑ i ∈ I.filter (fun i => Q.map (fun k => m k i) = Q.map id), b i * d i := by linarith
    rw [e3, hFb]
    exact Finset.mem_biUnion.2 ⟨d, Fintype.mem_piFinset.2 hd,
      Finset.mem_image.2 ⟨_, Finset.mem_powerset.2 (Finset.subset_univ _), rfl⟩⟩
  have h3 : {j | {z : ℝ | z - 0 ∈ Bset b 0} ∈ Uj j} ∈ Q := (hUmem _).1 (hb 0)
  have h4 : {j | {z : ℝ | z - 0 ∈ Bset b 0} ∈ Uj j}.Finite := by
    have hinj : Function.Injective a := fun i j hij => by
      have : (i : ℝ) = j := by simpa [ha] using hij
      exact_mod_cast this
    refine (Fb.finite_toSet.preimage hinj.injOn).subset fun j hj => hkey j hj
  have h5 : {j | {z : ℝ | z - 0 ∈ Bset b 0} ∈ Uj j}ᶜ ∈ Q := hyperfilter_le_cofinite h4.compl_mem_cofinite
  obtain ⟨j, hj1, hj2⟩ := Ultrafilter.nonempty_of_mem (inter_mem h3 h5)
  exact hj2 hj1

/-! ## The relation with the lacunary PVG -/

/-- An ultrafilter converges in the lacunary PVG (Bohr neighbourhoods and a member of the ideal) exactly when it
converges both here and in the Bohr topology. -/
theorem xi_iff (U : Ultrafilter ℝ) (x : ℝ) :
    ((U : Filter ℝ) ≤ @nhds ℝ bohrTop x ∧ ∃ (m : ℝ) (l : List ℝ), Icc (-m) m + sumT sT l ∈ U) ↔
      ((U : Filter ℝ) ≤ @nhds ℝ bohrTop x ∧ UConv U x) := by
  classical
  refine and_congr_right fun hB => ⟨?_, ?_⟩
  · rintro ⟨m, l, hJ⟩
    have hrep : ∀ z : ℝ, ∃ (u : ℝ) (c : Fin l.length → ℝ) (n : Fin l.length → ℕ),
        z ∈ Icc (-m) m + sumT sT l → u ∈ Icc (-m) m ∧ (∀ i, c i ∈ ({-1, 0, 1} : Finset ℝ)) ∧
          z = u + ∑ i, l.get i * (c i * sT (n i)) := by
      intro z
      by_cases hz : z ∈ Icc (-m) m + sumT sT l
      · obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.1 hz
        obtain ⟨τ, hτ, hv'⟩ := sumT_repr l v hv
        choose c hc n hn using fun i => Tset_repr (hτ i)
        refine ⟨u, c, n, fun _ => ⟨hu, hc, ?_⟩⟩
        rw [← huv, hv']
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [← hn i]
      · exact ⟨0, fun _ => 0, fun _ => 0, fun h => absurd h hz⟩
    choose u c n hrep using hrep
    have hJev : ∀ᶠ z in (U : Filter ℝ), z ∈ Icc (-m) m + sumT sT l := hJ
    obtain ⟨d, I, c0, hd, hI, hsplit⟩ := split_ultra U (fun i => l.get i) c n (hJev.mono fun z hz => (hrep z hz).2.1)
    obtain ⟨u0, _, hu0⟩ : ∃ u0 ∈ Icc (-m) m, ((U.map u : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓝 u0 := by
      refine isCompact_Icc.ultrafilter_le_nhds (U.map u) ?_
      rw [le_principal_iff]
      exact Ultrafilter.mem_map.2 (hJev.mono fun z hz => (hrep z hz).1)
    have hu : Tendsto u (U : Filter ℝ) (euclidNhds u0) := by
      rw [Ultrafilter.coe_map] at hu0; exact hu0
    have hz : ∀ᶠ z in (U : Filter ℝ), z = u z + c0 + ∑ i ∈ I, l.get i * (d i * sT (n z i)) := by
      filter_upwards [hJev, hsplit] with z hzJ hs
      conv_lhs => rw [(hrep z hzJ).2.2]
      rw [hs]; ring
    -- the limit in the Bohr compactification
    have hxu : x = u0 + c0 := by
      have hex : Tendsto e (U : Filter ℝ) (𝓝 (e x)) := by
        have h := hB
        rw [nhds_bohr] at h
        exact tendsto_iff_comap.2 h
      set W : Fin l.length → Ultrafilter ℕ := fun i => U.map (fun z => n z i) with hW
      have hlim : Tendsto (fun z => e (u z) + e c0 + ∑ i ∈ I, (l.get i * d i) • e (sT (n z i))) (U : Filter ℝ)
          (𝓝 (e u0 + e c0 + ∑ i ∈ I, (l.get i * d i) • L sT (W i))) := by
        refine ((continuous_e.tendsto u0).comp hu |>.add tendsto_const_nhds).add (tendsto_finsetSum I fun i _ => ?_)
        have h1 : Tendsto (fun z => n z i) (U : Filter ℝ) (W i : Filter ℕ) := by
          show Filter.map _ _ ≤ _
          exact le_of_eq (Ultrafilter.coe_map _ _).symm
        exact ((continuous_smul_const _).tendsto _).comp ((tendsto_L sT (W i)).comp h1)
      have hex' : Tendsto e (U : Filter ℝ) (𝓝 (e u0 + e c0 + ∑ i ∈ I, (l.get i * d i) • L sT (W i))) := by
        refine hlim.congr' (hz.mono fun z hz => ?_)
        have h1 : e (∑ i ∈ I, l.get i * (d i * sT (n z i))) = ∑ i ∈ I, (l.get i * d i) • e (sT (n z i)) := by
          show eHom (∑ i ∈ I, l.get i * (d i * sT (n z i))) = _
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_e]
          show e _ = e _
          congr 1; ring
        conv_rhs => rw [hz]
        rw [e_add, e_add, h1]
      have heq : e x = e u0 + e c0 + ∑ i ∈ I, (l.get i * d i) • L sT (W i) := tendsto_nhds_unique hex hex'
      set s : Finset (Ultrafilter ℕ) := I.image W with hs
      set g : Ultrafilter ℕ → ℝ := fun V => ∑ i ∈ I.filter (fun i => W i = V), l.get i * d i with hg
      have hfib : ∑ V ∈ s, g V • L sT V = ∑ i ∈ I, (l.get i * d i) • L sT (W i) := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := W) (t := s) (fun i hi => Finset.mem_image_of_mem _ hi)]
        refine Finset.sum_congr rfl fun V _ => ?_
        simp only [hg]
        rw [sum_smul_K]
        exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
      have hsum : ∑ V ∈ s, g V • L sT V = e (x - u0 - c0) := by
        rw [hfib]
        have h1 : e (x - u0 - c0) + e u0 + e c0 = e x := by
          rw [← e_add, ← e_add]; congr 1; ring
        rw [heq] at h1
        refine add_left_cancel (a := e u0 + e c0) ?_
        rw [← h1]; abel
      have hfr : ∀ V ∈ s, Free V := by
        intro V hV
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hV
        exact free_of_tendsto U _ (hI i hi)
      have hg0 := independence_finset sT sT_ne sT_ratio s hfr g _ hsum
      have h1 : e (x - u0 - c0) = 0 := by
        rw [← hsum]
        exact Finset.sum_eq_zero fun V hV => by rw [hg0 V hV]; exact zero_smul_K _
      have := e_eq_zero h1
      linarith
    refine ⟨l.length, fun i => if i ∈ I then l.get i else 0, fun N => ?_⟩
    have h1 : ∀ᶠ z in (U : Filter ℝ), |u z - u0| < 1 / (N + 1) := by
      have h2 : Tendsto (fun z => |u z - u0|) (U : Filter ℝ) (euclidNhds 0) := by
        have h3 : Tendsto u (U : Filter ℝ) (𝓝 u0) := hu
        have := (h3.sub_const u0).abs
        rwa [sub_self, abs_zero] at this
      exact h2.eventually_lt_const (by positivity)
    have h4 : ∀ᶠ z in (U : Filter ℝ), ∀ i ∈ I, N ≤ n z i :=
      (eventually_all_finset I).2 fun i hi => (hI i hi).eventually_ge_atTop N
    show ∀ᶠ z in (U : Filter ℝ), z - x ∈ Bset (fun i => if i ∈ I then l.get i else 0) N
    filter_upwards [h1, h4, hz] with z h1 h4 hz
    refine ⟨u z - u0, h1, fun i => if i ∈ I then d i * sT (n z i) else 0, fun i => ?_, ?_⟩
    · by_cases hi : i ∈ I
      · simp only [if_pos hi]
        have hdi := hd i
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdi
        rcases hdi with h | h | h
        · exact Or.inr ⟨n z i, h4 i hi, Or.inr (by rw [h]; ring)⟩
        · exact Or.inl (by rw [h]; ring)
        · exact Or.inr ⟨n z i, h4 i hi, Or.inl (by rw [h]; ring)⟩
      · simp only [if_neg hi]; exact zero_mem_Stail N
    · have e1 : ∑ i, (if i ∈ I then l.get i else 0) * (if i ∈ I then d i * sT (n z i) else 0) =
          ∑ i ∈ I, l.get i * (d i * sT (n z i)) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ I)]
        have e2 : ∑ i ∈ Finset.univ.filter (fun i => i ∉ I),
            (if i ∈ I then l.get i else 0) * (if i ∈ I then d i * sT (n z i) else 0) = 0 :=
          Finset.sum_eq_zero fun i hi => by rw [if_neg (Finset.mem_filter.1 hi).2, zero_mul]
        rw [e2, add_zero, Finset.filter_univ_mem]
        exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi, if_pos hi]
      rw [e1]
      conv_lhs => rw [hz]
      rw [hxu]; ring
  · rintro ⟨r, a, ha⟩
    refine ⟨|x| + 1, List.ofFn a, mem_of_superset (ha 0) fun z hz => ?_⟩
    obtain ⟨u, hu, σ, hσ, e1⟩ := hz
    have hu' : |u| < 1 := by simpa using hu
    refine Set.mem_add.2 ⟨x + u, ?_, ∑ i, a i * σ i, ?_, by rw [add_assoc, ← e1]; ring⟩
    · rw [mem_Icc, ← abs_le]
      exact (abs_add_le _ _).trans (by linarith)
    · have hsum : ∀ (r : ℕ) (a σ : Fin r → ℝ), (∀ i, σ i ∈ Tset sT) → ∑ i, a i * σ i ∈ sumT sT (List.ofFn a) := by
        intro r
        induction r with
        | zero => intro a σ _; simp [sumT]
        | succ r ih =>
          intro a σ hσ
          rw [List.ofFn_succ, Fin.sum_univ_succ]
          refine Set.mem_add.2 ⟨a 0 • σ 0, Set.smul_mem_smul_set (hσ 0), _,
            ih (fun i => a i.succ) (fun i => σ i.succ) (fun i => hσ i.succ), by rw [smul_eq_mul]⟩
      refine hsum r a σ fun i => ?_
      rcases hσ i with h | ⟨n, _, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, Or.inl h⟩
      · exact Or.inr ⟨n, Or.inr h⟩

end Two
end PVG
