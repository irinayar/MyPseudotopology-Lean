import LeanCheck.ChainBaire
import LeanCheck.ChainLQC
import LeanCheck.ChainTransferQ

/-!
# A necessary Mackey topology on the rational quotient (TVGQ-v7 Theorem `necessary-rational-v4`)

If `𝒞^ℚ_{f,ℚ}` has a greatest member `μ`, then the dual pair `(ℚ, Γ)` has a greatest compatible Hausdorff locally
quasi-convex group topology, and it is also the greatest member of `𝒟_Γ`.

Notation: `Lcls Gam` = Hausdorff locally quasi-convex group topologies on `ℚ` with full character set `Γ`,
`Ccls Gam = 𝒟_Γ` = those with all rational multiplications continuous.  Mathlib's order is reversed with respect
to the paper's inclusion ("greatest" = finest = least in Mathlib's `≤`).

Proof structure (as in the paper):
1. `λ = λ_μ` is the quotient topology of `μ` along `f`; its dual is `Γ` (`lamTop_dual`, from the quotient lemma).
2. For every `δ ∈ Lcls Γ`: the saturation `δ^[ℚ] ∈ 𝒟_Γ` (`saturation`), `S_f(δ^[ℚ]) ∈ 𝒞^ℚ_{f,ℚ}`
   (`Tq_mem_Ccls`), so `μ ⊆ ...`, i.e. `S_f(δ^[ℚ]) ⊆ μ`; then `f : (ℝ,μ) → (ℚ,δ^[ℚ])` is continuous and
   `δ ⊆ δ^[ℚ] ⊆ λ` (`lam_le`).
3. `λ_qc` = the join of all Hausdorff locally quasi-convex group topologies coarser than `λ`: it is again such a
   topology, squeezed between `λ` and a compatible topology, so it has dual `Γ`, and it is greatest.
4. Corollary `mackey-equivalence` on `ℚ` gives rational scalar continuity and greatestness in `𝒟_Γ`.
-/

namespace LeanCheck

open Topology Filter

/-- `Γ = {q ↦ p(r q) : r ∈ ℚ}`, as a set of characters of `ℚ`. -/
def Gam : Set (ℚ →+ Circ) := {ψ | ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)}

/-- `Γ` is invariant under rational rescaling of arguments. -/
theorem Gam_ratInv : RatInv Gam := by
  rintro χ ⟨r, hr⟩ q
  refine ⟨r * q, fun s => ?_⟩
  have h1 : (χ.comp (mq q)) s = χ (q * s) := by
    show χ (mq q s) = _
    rw [mq_apply, smul_eq_mul]
  rw [h1, hr (q * s)]
  push_cast; ring_nf

/-- The quotient topology `λ_μ` on `ℚ` (coinduced along `f`). -/
noncomputable def lamTop (f : ℝ →+ ℚ) (μ : TopologicalSpace ℝ) : TopologicalSpace ℚ :=
  TopologicalSpace.coinduced (fun x : ℝ => f x) μ

/-- The dual of `λ_μ` is `Γ` (from the quotient lemma). -/
theorem lamTop_dual (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Lcls (Hq f)) (ψ : ℚ →+ Circ) :
    @Continuous ℚ Circ (lamTop f μ) circTop ψ ↔ ψ ∈ Gam := by
  have h := QCompat.of_Lcls (W := ⟨μ⟩) hμ
  have key := QuotQ_dual h u hu (show QuotQ ⟨μ⟩ f →+ Circ from ψ)
  constructor
  · intro hc
    obtain ⟨r, hr⟩ := key.1 hc
    refine ⟨r, fun s => ?_⟩
    rw [show ψ s = (show QuotQ ⟨μ⟩ f →+ Circ from ψ) s from rfl, hr s, psi0_apply]
  · rintro ⟨r, hr⟩
    refine key.2 ⟨r, fun q => ?_⟩
    rw [psi0_apply]
    exact hr q

/-- `S_f(δ)` lies in `𝒞^ℚ_{f,ℚ}` whenever `δ ∈ 𝒟_Γ`. -/
theorem Tq_mem_Ccls (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hδ : δ ∈ Ccls Gam) : Tq f δ ∈ Ccls (Hq f) := by
  obtain ⟨⟨hg, ht, hl, hd⟩, hs⟩ := hδ
  have hs' : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x) := by
    intro s
    have := hs s
    have e : (fun x : ℚ => s * x) = ⇑(mq s) := by funext x; simp [mq_apply]
    rw [e]; exact this
  refine ⟨⟨Tq_group f δ hg, Tq_t2 f δ, lqc_Tq f δ hl, ?_⟩, ?_⟩
  · intro χ
    rw [show χ ∈ Hq f ↔ ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x from Iff.rfl]
    exact dual_Tq f u hu δ hg (fun ψ => hd ψ) χ
  · intro q
    have e : (mq q : ℝ → ℝ) = fun x : ℝ => (q : ℝ) * x := mq_real q
    rw [e]
    exact Tq_rat_dilation f δ hs' q

/-- Key step: if `μ` is greatest in `𝒞^ℚ_{f,ℚ}`, then `λ_μ` is finer than every compatible topology on `ℚ`
(`δ ⊆ λ_μ` in the paper's notation). -/
theorem lam_le (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hgr : ∀ τ ∈ Ccls (Hq f), μ ≤ τ) (δ : TopologicalSpace ℚ) (hδ : δ ∈ Lcls Gam) :
    lamTop f μ ≤ δ := by
  obtain ⟨hs, hle, -⟩ := saturation Gam Gam_ratInv δ hδ
  have hT := Tq_mem_Ccls f u hu (sat δ) hs
  have hμT : μ ≤ Tq f (sat δ) := hgr _ hT
  have hcont : Continuous[μ, sat δ] f := continuous_le_dom hμT (f_cont_Tq f (sat δ))
  have : lamTop f μ ≤ sat δ := by
    unfold lamTop
    exact continuous_iff_coinduced_le.1 hcont
  exact this.trans hle

/-- **Theorem `necessary-rational-v4`.**  If `𝒞^ℚ_{f,ℚ}` has a greatest member `μ`, then the dual pair
`(ℚ, Γ)` has a greatest compatible Hausdorff locally quasi-convex group topology `ν`; it also has all
rational scalars continuous and is the greatest member of `𝒟_Γ`. -/
theorem necessary_mackey_rational (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Ccls (Hq f)) (hgr : ∀ τ ∈ Ccls (Hq f), μ ≤ τ) :
    ∃ ν : TopologicalSpace ℚ,
      (ν ∈ Lcls Gam ∧ ∀ δ ∈ Lcls Gam, ν ≤ δ) ∧ (ν ∈ Ccls Gam ∧ ∀ δ ∈ Ccls Gam, ν ≤ δ) := by
  have hlam : ∀ δ ∈ Lcls Gam, lamTop f μ ≤ δ := fun δ hδ => lam_le f u hu μ hgr δ hδ
  -- the family of Hausdorff locally quasi-convex group topologies coarser than `λ_μ`
  let Fam : Set (TopologicalSpace ℚ) :=
    {ν | @IsTopologicalAddGroup ℚ ν _ ∧ @T2Space ℚ ν ∧ LocQC ν ∧ lamTop f μ ≤ ν}
  -- a compatible topology exists (the lifted chain topology), so the family is nonempty
  obtain ⟨g1, g2, hg1, -, ht1, -, hl1, -, -, -, hd1, -, -⟩ := lift_capstone_lqc
  have hg1L : g1 ∈ Lcls Gam := ⟨hg1, ht1, hl1, fun χ => hd1 χ⟩
  have hg1F : g1 ∈ Fam := ⟨hg1, ht1, hl1, hlam g1 hg1L⟩
  let ν : TopologicalSpace ℚ := ⨅ δ : Fam, δ.1
  have hνle : ν ≤ g1 := iInf_le (fun δ : Fam => δ.1) ⟨g1, hg1F⟩
  have hlamν : lamTop f μ ≤ ν := le_iInf fun δ => δ.2.2.2.2
  have hνgrp : @IsTopologicalAddGroup ℚ ν _ := isTopologicalAddGroup_iInf fun δ => δ.2.1
  have hνt2 : @T2Space ℚ ν := by
    have hc : Continuous[ν, g1] (id : ℚ → ℚ) := continuous_id_of_le hνle
    exact @T2Space.of_injective_continuous ℚ ℚ ν g1 ht1 id Function.injective_id hc
  have hνlqc : LocQC ν := lqc_iInf _ fun δ => δ.2.2.2.1
  have hνdual : ∀ χ : ℚ →+ Circ, @Continuous ℚ Circ ν circTop χ ↔ χ ∈ Gam := by
    intro χ
    constructor
    · intro hc
      exact (lamTop_dual f u hu μ hμ.1 χ).1 (continuous_le_dom hlamν hc)
    · intro hχ
      exact continuous_le_dom hνle (hd1 χ |>.2 hχ)
  have hνL : ν ∈ Lcls Gam := ⟨hνgrp, hνt2, hνlqc, hνdual⟩
  have hνgreat : ∀ δ ∈ Lcls Gam, ν ≤ δ := fun δ hδ =>
    iInf_le (fun δ : Fam => δ.1) ⟨δ, ⟨hδ.1, hδ.2.1, hδ.2.2.1, hlam δ hδ⟩⟩
  refine ⟨ν, ⟨hνL, hνgreat⟩, ?_⟩
  exact ((mackey_equivalence Gam Gam_ratInv).1 ν).2 ⟨hνL, hνgreat⟩

/-- **The necessary rational condition fails**: `(ℚ, Γ)` has no greatest compatible Hausdorff locally
quasi-convex group topology (two lifted chain topologies have an incompatible join). -/
theorem no_mackey_rational :
    ¬ ∃ ν : TopologicalSpace ℚ, ν ∈ Lcls Gam ∧ ∀ δ ∈ Lcls Gam, ν ≤ δ := by
  rintro ⟨ν, hν, hgreat⟩
  obtain ⟨g1, g2, hg1, hg2, ht1, ht2, hl1, hl2, -, -, hd1, hd2, ψ, hψ, hne⟩ := lift_capstone_lqc
  have hg1L : g1 ∈ Lcls Gam := ⟨hg1, ht1, hl1, fun χ => hd1 χ⟩
  have hg2L : g2 ∈ Lcls Gam := ⟨hg2, ht2, hl2, fun χ => hd2 χ⟩
  have hle : ν ≤ g1 ⊓ g2 := le_inf (hgreat g1 hg1L) (hgreat g2 hg2L)
  have hc : @Continuous ℚ Circ ν circTop ψ := continuous_le_dom hle hψ
  obtain ⟨r, hr⟩ := (hν.2.2.2 ψ).1 hc
  obtain ⟨s, hs⟩ := hne r
  exact hs (hr s)

/-- Consequently `𝒞^ℚ_{f,ℚ}` has no greatest member (a second route to the non-existence of a Mackey topology
for `(ℝ, H_{f,ℚ})`, through the rational quotient). -/
theorem no_greatest_via_quotient (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ¬ ∃ μ : TopologicalSpace ℝ, μ ∈ Ccls (Hq f) ∧ ∀ τ ∈ Ccls (Hq f), μ ≤ τ := by
  rintro ⟨μ, hμ, hgr⟩
  obtain ⟨ν, ⟨hνL, hνgreat⟩, -⟩ := necessary_mackey_rational f u hu μ hμ hgr
  exact no_mackey_rational ⟨ν, hνL, hνgreat⟩

end LeanCheck
