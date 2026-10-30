import LeanCheck.ChainF2

/-!
# Two compatible chains: the complete printed statement, including profinite compactness
(HamelCharactersTVG_v18 Theorem E.1 `twochains:H`; TVGQ-v7 Theorem 18.1)

`profT` is the profinite topology on `ℤ`: the coarsest topology in which every reduction `z ↦ z mod N` into the discrete
group `ℤ/N` is continuous.  A sequence tends to `0` there exactly when every positive integer eventually divides its
terms, and the set formed by such a sequence and `0` is compact (`isCompact_of_null`).  We combine this with `capstone` /
`final_capstone` to obtain every property listed in the printed theorem.
-/

namespace LeanCheck

open Filter Topology

/-- The profinite topology on `ℤ`. -/
def profT : TopologicalSpace ℤ :=
  ⨅ n : ℕ, TopologicalSpace.induced (fun z : ℤ => (z : ZMod (n + 1))) ⊥

theorem tendsto_profT_zero (a : ℕ → ℤ) (h : ∀ N : ℕ, 0 < N → ∃ n0, ∀ n ≥ n0, (N : ℤ) ∣ a n) :
    Tendsto a atTop (@nhds ℤ profT 0) := by
  unfold profT
  rw [nhds_iInf, tendsto_iInf]
  intro n
  rw [nhds_induced, tendsto_comap_iff]
  haveI : @DiscreteTopology (ZMod (n + 1)) ⊥ := ⟨rfl⟩
  rw [@nhds_discrete (ZMod (n + 1)) ⊥ this]
  rw [tendsto_pure]
  obtain ⟨n0, hn0⟩ := h (n + 1) (Nat.succ_pos n)
  rw [eventually_atTop]
  refine ⟨n0, fun m hm => ?_⟩
  have := hn0 m hm
  simp only [Function.comp, Int.cast_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast this)

/-- If every positive integer eventually divides the terms of `a`, then `{0} ∪ {a n}` is compact in the profinite topology. -/
theorem isCompact_of_null (a : ℕ → ℤ) (h : ∀ N : ℕ, 0 < N → ∃ n0, ∀ n ≥ n0, (N : ℤ) ∣ a n) :
    @IsCompact ℤ profT (insert 0 (Set.range a)) :=
  @Filter.Tendsto.isCompact_insert_range ℤ profT a 0 (tendsto_profT_zero a h)

/-- **Theorem E.1 / 18.1, complete.**  There are two divisibility chains `F₁ = {M_n}`, `F₂ = {M2_n}`, each containing `1`, with
consecutive ratios at least `2` and tending to infinity, with every positive integer eventually dividing the terms, such that
the topologies `λ_{F₁}`, `λ_{F₂}` on `ℚ/ℤ` are Hausdorff with continuous characters exactly the maps `x ↦ u x` (`u ∈ ℤ`),
while their join has a continuous character that is not of this form; and the sets `{0} ∪ F_i` are compact in the profinite
topology of `ℤ`. -/
theorem twochains_complete :
    ∃ (α1 α2 : ℕ → ℕ) (ζ : TorsA →+ Circ),
      (∀ i, 2 ≤ α1 i) ∧ (∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α1 i) ∧
      (∀ i, 2 ≤ α2 i) ∧ (∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α2 i) ∧
      Mseq α1 0 = 1 ∧ Mseq α2 0 = 1 ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α1 n) ∧
      (∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α2 n) ∧
      @T2Space TorsA (basisOf (Set.range (Mseq α1))).topology ∧
      @T2Space TorsA (basisOf (Set.range (Mseq α2))).topology ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range (Mseq α1))).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range (Mseq α2))).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      @Continuous TorsA Circ
        ((basisOf (Set.range (Mseq α1))).topology ⊓ (basisOf (Set.range (Mseq α2))).topology) _ ζ ∧
      (∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) ∧
      @IsCompact ℤ profT (insert 0 (Set.range fun n => (Mseq α1 n : ℤ))) ∧
      @IsCompact ℤ profT (insert 0 (Set.range fun n => (Mseq α2 n : ℤ))) := by
  obtain ⟨α1, α2, hα1, hl1, hα2, hl2, h01, h02, hrel, hn1, hn2, ⟨z1, hc1, hr1⟩,
    ⟨z2, hc2, hr2⟩, _, _, hjoin⟩ := capstone
  have h1r : 1 ∈ Set.range (Mseq α1) := ⟨0, h01⟩
  have h2r : 1 ∈ Set.range (Mseq α2) := ⟨0, h02⟩
  refine ⟨α1, α2, zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1, hα1, hl1, hα2, hl2, h01, h02, hn1, hn2,
    t2_basisOf h1r, t2_basisOf h2r,
    fun χ => dual_exact hα1 hl1 hn1 h01 χ, fun χ => dual_exact hα2 hl2 hn2 h02 χ,
    zeta_join_continuous hn1 hc1 hr1 hjoin, zeta_not_int hn1 hc1 hr1, ?_, ?_⟩
  · refine isCompact_of_null _ (fun N hN => ?_)
    obtain ⟨n0, hn0⟩ := hn1 N hN
    exact ⟨n0, fun n hn => by exact_mod_cast hn0 n hn⟩
  · refine isCompact_of_null _ (fun N hN => ?_)
    obtain ⟨n0, hn0⟩ := hn2 N hN
    exact ⟨n0, fun n hn => by exact_mod_cast hn0 n hn⟩

/-- **Corollary E.2 / 18.2.**  There are two profinitely compact sets `C₁, C₂ ⊆ ℕ ⊆ ℤ`, each containing `0` and `1`, such that
`λ_{C₁}` and `λ_{C₂}` are Hausdorff with continuous characters exactly `x ↦ u x`, while `λ_{C₁ ∪ C₂}` (their join) has a
continuous character that is not of this form.  (The positive union result inside one chain is `Gjoin`.) -/
theorem twochains_compact_union :
    ∃ (C₁ C₂ : Set ℕ) (ζ : TorsA →+ Circ),
      @IsCompact ℤ profT (((↑) : ℕ → ℤ) '' (insert 0 C₁)) ∧ @IsCompact ℤ profT (((↑) : ℕ → ℤ) '' (insert 0 C₂)) ∧
      1 ∈ C₁ ∧ 1 ∈ C₂ ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf C₁).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf C₂).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      @Continuous TorsA Circ (basisOf (C₁ ∪ C₂)).topology _ ζ ∧
      (∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) := by
  obtain ⟨α1, α2, ζ, -, -, -, -, h01, h02, hn1, hn2, -, -, hd1, hd2, hj, hni, hc1, hc2⟩ := twochains_complete
  refine ⟨Set.range (Mseq α1), Set.range (Mseq α2), ζ, ?_, ?_, ⟨0, h01⟩, ⟨0, h02⟩, hd1, hd2, ?_, hni⟩
  · have : ((↑) : ℕ → ℤ) '' (insert 0 (Set.range (Mseq α1))) = insert 0 (Set.range fun n => (Mseq α1 n : ℤ)) := by
      ext x; simp [Set.image_insert_eq, Set.range_comp]
    rw [this]; exact hc1
  · have : ((↑) : ℕ → ℤ) '' (insert 0 (Set.range (Mseq α2))) = insert 0 (Set.range fun n => (Mseq α2 n : ℤ)) := by
      ext x; simp [Set.image_insert_eq, Set.range_comp]
    rw [this]; exact hc2
  · rw [← lam_inf_union]; exact hj

end LeanCheck
