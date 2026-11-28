import Mathlib
import LeanCheck.PGThreeGroups
import LeanCheck.PGThreeSequences

/-!
# PGfour: a large null ultrafilter on a torsion-free group

* `bohr_coarsest` : on a torsion-free abelian group, for countably many ultrafilters, if some ultrafilter converging to
  `0` in the generated PG has all its sets `E + E - E - E` among the Bohr neighbourhoods of `0`, then the Bohr
  neighbourhood filter is the coarsest symmetric halvable null filter containing `0` in its members;
* `bog_of_dense` : on `ℤ`, if `E` has positive upper density along the intervals `[-n, n]`, then `E + E - E - E` is a
  Bohr neighbourhood of `0`;
* `bohr_coarsest_int` : the two together on `ℤ`;
* `indiscrete_not_pretopological` : there is a nonprincipal ultrafilter on `ℤ` whose PG has every principal ultrafilter
  converging to `0`, so that the intersection of the null filters is trivial, and that intersection is not null.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Section4Bohr

open Sel PG.Idem PG.Words PG.Bohr PG.One PG.Groups PG.Seq

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

variable {G : Type} [AddCommGroup G]

/-- The limits in the Bohr compactification are additive in the character. -/
theorem additive_of_mem_K (S : Set (Ultrafilter G)) {a : Circles G} (ha : a ∈ K (ultraGen S))
    (χ ψ : G →+ UnitAddCircle) : a (χ + ψ) = a χ + a ψ := by
  have hlam : ∀ (p : Ultrafilter G), lam p (χ + ψ) = lam p χ + lam p ψ := by
    intro p
    have h := lim_lam p
    unfold Lim at h
    have h1 := tendsto_pi_nhds.1 h (χ + ψ)
    have h2 := (tendsto_pi_nhds.1 h χ).add (tendsto_pi_nhds.1 h ψ)
    exact tendsto_nhds_unique h1 h2
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, _, hux⟩ := L_ultraGen S hx
    rw [← hux]
    exact hlam u
  | zero => simp
  | add x y _ _ ihx ihy =>
    simp only [Pi.add_apply, ihx, ihy]
    abel
  | neg x _ ih =>
    simp only [Pi.neg_apply, ih]
    abel

/-- On a torsion-free group the subgroup of limits has no element of finite order. -/
theorem K_torsionfree (htf : ∀ (n : ℕ) (g : G), 0 < n → n • g = 0 → g = 0) (S : Set (Ultrafilter G))
    {a : Circles G} (ha : a ∈ K (ultraGen S)) (hfin : IsOfFinAddOrder a) : a = 0 := by
  obtain ⟨n, hn, hna⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
  funext χ
  have hinj : Function.Injective ((nsmulAddMonoidHom n : G →+ G).toIntLinearMap) := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    exact htf n g hn hg
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property _ hinj χ.toIntLinearMap
  have hψ' : n • ψ.toAddMonoidHom = χ := by
    ext g
    have h1 := LinearMap.congr_fun hψ g
    have h2 : ψ (n • g) = χ g := h1
    rw [map_nsmul] at h2
    exact h2
  have hmul : ∀ k : ℕ, a (k • ψ.toAddMonoidHom) = k • a ψ.toAddMonoidHom := by
    intro k
    induction k with
    | zero =>
      have h := additive_of_mem_K S ha 0 0
      rw [add_zero] at h
      rw [zero_nsmul, zero_nsmul]
      exact (add_eq_left.1 h.symm)
    | succ k ih => rw [succ_nsmul, additive_of_mem_K S ha, ih, succ_nsmul]
  rw [← hψ', hmul]
  exact congrFun hna ψ.toAddMonoidHom

/-- A null ultrafilter with the Bogolyubov property makes the Bohr filter null. -/
theorem bohr_null (S : Set (Ultrafilter G)) (p : Ultrafilter G) (hp : (p : Filter G) ∈ genFam (ultraGen S))
    (hbog : ∀ E ∈ p, dsum E ∈ comap (iota (G := G)) (𝓝 0)) :
    comap (iota (G := G)) (𝓝 0) ∈ genFam (ultraGen S) := by
  obtain ⟨τ, hτ, hpτ⟩ := hp.2 p le_rfl
  have hne : (comap (iota (G := G)) (𝓝 0)).NeBot := by
    refine ⟨fun h => ?_⟩
    have h1 : (∅ : Set G) ∈ comap (iota (G := G)) (𝓝 0) := by rw [h]; exact mem_bot
    exact (comap_iota_nbhd G).zero_mem _ h1
  refine mem_genFam_of_le (SumClosure.add (SumClosure.add hτ hτ) (sumClosure_neg (SumClosure.add hτ hτ))) ?_
  intro s hs
  obtain ⟨t1, ht1, t2, ht2, h⟩ := Filter.mem_map₂_iff.1 hs
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_map₂_iff.1 ht1
  obtain ⟨C, hC, D, hD, hCD⟩ := Filter.mem_map₂_iff.1 (Filter.mem_map.1 ht2)
  have ht : A ∩ B ∩ C ∩ D ∈ τ := Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hD
  have hE : A ∩ B ∩ C ∩ D ∈ p := hpτ ht
  refine Filter.mem_of_superset (hbog _ hE) (fun z hz => ?_)
  obtain ⟨a, ma, b, mb, c, mc, d, md, e⟩ := hz
  have e' : z = (a + b) + -(c + d) := by
    rw [e]
    abel
  rw [e']
  refine h (mem_image2_of_mem (hAB (mem_image2_of_mem ma.1.1.1 mb.1.1.2)) ?_)
  have h1 : c + d ∈ (fun x : G => -x) ⁻¹' t2 := hCD (mem_image2_of_mem mc.1.2 md.2)
  exact h1

/-- The Bohr filter is then the coarsest symmetric halvable null filter. -/
theorem bohr_coarsest (htf : ∀ (n : ℕ) (g : G), 0 < n → n • g = 0 → g = 0) (S : Set (Ultrafilter G))
    (hS : S.Countable) (p : Ultrafilter G) (hp : (p : Filter G) ∈ genFam (ultraGen S))
    (hbog : ∀ E ∈ p, dsum E ∈ comap (iota (G := G)) (𝓝 0)) :
    (IsNbhdFilter (comap (iota (G := G)) (𝓝 0)) ∧ comap (iota (G := G)) (𝓝 0) ∈ genFam (ultraGen S)) ∧
      ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ comap (iota (G := G)) (𝓝 0) := by
  refine ⟨⟨comap_iota_nbhd G, bohr_null S p hp hbog⟩, fun N hN hNC => ?_⟩
  have h : Lim N 0 := tendsto_zero_of_torsionfree (ultraGen S) (countable_K S hS)
    (fun a ha hfin => K_torsionfree htf S ha hfin) N hN hNC
  exact tendsto_iff_comap.1 h

/-! ### The integers -/

/-- Bogolyubov's lemma on `ℤ` for sets of positive upper density along the intervals `[-n, n]`. -/
theorem bog_of_dense (E : Set ℤ) (hE : DenseF IntF E) : dsum E ∈ comap (iota (G := ℤ)) (𝓝 0) := by
  classical
  obtain ⟨α, hα, H⟩ := hE
  set good : Set ℕ := {n | 1 ≤ n ∧ α * (IntF n).card ≤ (cntF IntF E n : ℝ)} with hgood
  have hinf : good.Infinite := by
    refine Set.infinite_of_forall_exists_gt (fun N => ?_)
    obtain ⟨n, hn, h1⟩ := H (N + 1)
    exact ⟨n, ⟨by omega, h1⟩, by omega⟩
  let ρ : ∀ n : ℕ, ℤ → ZMod (8 * n + 1) := fun n z => (z : ZMod (8 * n + 1))
  let D : ∀ n : ℕ, Finset (ZMod (8 * n + 1)) := fun n => ((IntF n).filter (fun x => x ∈ E)).image (ρ n)
  have hcongr : ∀ (n : ℕ) (x y : ℤ), ρ n x = ρ n y → |x - y| < 8 * (n : ℤ) + 1 → x = y := by
    intro n x y h h'
    have h1 : ((x - y : ℤ) : ZMod (8 * n + 1)) = 0 := by
      rw [Int.cast_sub, sub_eq_zero]
      exact h
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
    refine sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h2 ?_)
    push_cast
    exact h'
  have hIcc : ∀ n x, x ∈ IntF n → -(n : ℤ) ≤ x ∧ x ≤ n := fun n x hx => Finset.mem_Icc.1 hx
  refine bohr_of_levels (fun n => ZMod (8 * n + 1)) ρ D good hinf (α / 4) (by positivity) (fun n hn => ?_)
    (fun z z' => Filter.Eventually.of_forall (fun n => by simp only [ρ, Int.cast_add])) (dsum E) (fun z => ?_)
  · have hcard : (D n).card = cntF IntF E n := by
      refine Finset.card_image_of_injOn (fun x hx y hy h => hcongr n x y h ?_)
      have h1 := hIcc n x (Finset.mem_filter.1 hx).1
      have h2 := hIcc n y (Finset.mem_filter.1 hy).1
      rw [abs_lt]
      omega
    rw [hcard, ZMod.card]
    refine le_trans ?_ hn.2
    rw [IntF_card]
    have h3 : ((8 * n + 1 : ℕ) : ℝ) ≤ 4 * ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 8 * n + 1 ≤ 4 * (2 * n + 1))
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ α / 4)
    linarith
  · filter_upwards [eventually_ge_atTop (z.natAbs + 1)] with n hn
    rintro ⟨a, ha, b, hb, c, hc, d, hdd, h⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hdd
    rw [Finset.mem_filter] at ha' hb' hc' hd'
    refine ⟨a', ha'.2, b', hb'.2, c', hc'.2, d', hd'.2, hcongr n _ _ ?_ ?_⟩
    · rw [h]
      simp only [ρ, Int.cast_add, Int.cast_sub]
    · have h1 := hIcc n _ ha'.1
      have h2 := hIcc n _ hb'.1
      have h3 := hIcc n _ hc'.1
      have h4 := hIcc n _ hd'.1
      have h5 : |z| = (z.natAbs : ℤ) := (Int.natCast_natAbs z).symm
      have h6 : -|z| ≤ z := neg_abs_le z
      have h7 : z ≤ |z| := le_abs_self z
      rw [abs_lt]
      omega

/-- On `ℤ`: if some null ultrafilter has all its members of positive upper density, the Bohr filter is the coarsest
symmetric halvable null filter. No assumption is made on the Bohr limits of the generators. -/
theorem bohr_coarsest_int (S : Set (Ultrafilter ℤ)) (hS : S.Countable) (p : Ultrafilter ℤ)
    (hp : (p : Filter ℤ) ∈ genFam (ultraGen S)) (hd : ∀ E ∈ p, DenseF IntF E) :
    (IsNbhdFilter (comap (iota (G := ℤ)) (𝓝 0)) ∧ comap (iota (G := ℤ)) (𝓝 0) ∈ genFam (ultraGen S)) ∧
      ∀ N : Filter ℤ, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ comap (iota (G := ℤ)) (𝓝 0) := by
  refine bohr_coarsest (fun n g hn h => ?_) S hS p hp (fun E hE => bog_of_dense E (hd E hE))
  rw [nsmul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hn.ne')

/-! ### Without the Hausdorff property -/

/-- A nonprincipal ultrafilter on `ℤ` whose PG has every principal ultrafilter converging to `0`, while the
intersection of the null filters, here the trivial filter `⊤`, is not null. -/
theorem indiscrete_not_pretopological :
    ∃ u : Ultrafilter ℤ, (∀ a, u ≠ pure a) ∧
      (∀ g : ℤ, (pure g : Filter ℤ) ∈ genFam (ultraGen {u})) ∧
      (⊤ : Filter ℤ) ∉ genFam (ultraGen {u}) := by
  obtain ⟨q, hq, habove, _⟩ := bog_int
  have hq0 : ∀ a, q ≠ pure a := by
    intro a h
    have h1 := habove (a.natAbs + 1)
    rw [h] at h1
    have h2 : a ≠ 0 ∧ ∀ s ∈ tsupp a, a.natAbs + 1 < s := h1
    obtain ⟨s, hs⟩ := tsupp_nonempty a h2.1
    have h3 := h2.2 s hs
    exact (mem_tsupp a s).1 hs (flat_of_large a s (by omega))
  set u : Ultrafilter ℤ := q.map (fun x => 1 + x) with hu
  have hfree : ∀ a, u ≠ pure a := by
    intro a h
    refine hq0 (a - 1) (Ultrafilter.coe_le_coe.1 ?_)
    rw [Ultrafilter.coe_pure, le_pure_iff]
    have h1 : ({a} : Set ℤ) ∈ u := by rw [h]; exact rfl
    refine Filter.mem_of_superset (Ultrafilter.mem_map.1 h1) (fun x hx => ?_)
    have h2 : 1 + x = a := hx
    show x = a - 1
    omega
  have hall : ∀ g : ℤ, (pure g : Filter ℤ) ∈ genFam (ultraGen {u}) := by
    intro g
    have h := (translated_idempotents (G := ℤ) (I := Unit) (fun _ => 1) (fun _ => q) (fun _ => hq) g).2
    have h1 : Set.range (fun _ : Unit => q.map (fun x => (1 : ℤ) + x)) = {u} := by
      rw [hu]
      exact Set.range_const
    rw [h1] at h
    refine h ?_
    have h2 : Set.range (fun _ : Unit => (1 : ℤ)) = {1} := Set.range_const
    rw [h2]
    exact AddSubgroup.mem_closure_singleton.2 ⟨g, by simp⟩
  refine ⟨u, hfree, hall, fun htop => ?_⟩
  have hlt : (1 : Cardinal.{0}) < (2 : Cardinal.{0}) ^ Cardinal.continuum :=
    Cardinal.one_lt_aleph0.trans (lt_trans Cardinal.aleph0_lt_continuum (Cardinal.cantor _))
  have h1 : Cardinal.mk ({u} : Set (Ultrafilter ℤ)) < (2 : Cardinal.{0}) ^ Cardinal.continuum := by
    rwa [Cardinal.mk_singleton]
  have h2 : Cardinal.mk ({0} : Set ℤ) < (2 : Cardinal.{0}) ^ Cardinal.continuum := by
    rwa [Cardinal.mk_singleton]
  obtain ⟨p, _, _, hp⟩ := exists_divergent (G := ℤ) {u} h1 {0} h2 univ infinite_univ
  exact hp 0 rfl ((genFam_nullFamily _).finer _ htop _ le_top (Filter.NeBot.map p.neBot _))

end Section4Bohr

end PG
