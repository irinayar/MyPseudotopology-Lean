import LeanCheck.ChainD3
import LeanCheck.ChainNecessaryMackey

/-!
# The rational quotient for the TVG class `𝒞_f` and the necessary rational Mackey condition
(HamelCharactersTVG_v18 Lemma 19.1 `lem:quotient-v8`, Corollary 19.4 `cor:necessary-v8`, Corollary 26.6 `cor:sandwich-v13`)

For `η ∈ ℒ_f` (Hausdorff group topology with dual `H_f = {x ↦ p(c x + f(a x))}`), `E = ker f` is closed, and the
quotient topology `λ_η` of `ℝ/E ≅ ℚ` has exactly the characters `Γ`.  Here we redo the quotient lemma of `ChainBaire`
(proved there for `H_{f,ℚ}`) for `H_f`.
-/

namespace LeanCheck

open Topology Filter

section QuotientTVG

variable {W : TopW} {f : ℝ →+ ℚ}

lemma pfHom_memF (f : ℝ →+ ℚ) (q : ℚ) : pfHom f (q : ℝ) ∈ (Hset f ⊤ : Set Chars) :=
  ⟨0, q, trivial, fun x => by simp [pfHom_apply, chiH]⟩

/-- `ker f` is closed (for `η ∈ ℒ_f`, only continuity of the characters `p ∘ q f` is used). -/
theorem ker_closed' (hq : ∀ q : ℚ, Continuous (show RT W.t → Circ from pfHom f (q : ℝ))) :
    IsClosed {x : RT W.t | f x.val = 0} := by
  have hN : {x : RT W.t | f x.val = 0} =
      ⋂ q : ℚ, (fun x : RT W.t => (pfHom f (q : ℝ)) x.val) ⁻¹' {0} := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      refine Set.mem_iInter.2 (fun q => ?_)
      show (pfHom f (q : ℝ)) x.val = 0
      rw [pfHom_apply, f_ratmul]
      have hx' : f x.val = 0 := hx
      rw [hx']; simp
    · intro hx
      by_contra hne
      have hne' : f x.val ≠ 0 := hne
      have h1 := Set.mem_iInter.1 hx (1 / (2 * f x.val) : ℚ)
      change (pfHom f (((1 / (2 * f x.val) : ℚ)) : ℝ)) x.val = 0 at h1
      rw [pfHom_apply, f_ratmul] at h1
      apply half_ne_zero_circ
      convert h1 using 2
      push_cast
      field_simp
  rw [hN]
  refine isClosed_iInter fun q => ?_
  exact isClosed_singleton.preimage (hq q)

/-- `f : (ℝ, η) → (ℚ, λ_η)` is an open map. -/
theorem fQ_isOpenMap' (hg : IsTopologicalAddGroup (RT W.t)) : IsOpenMap (fQ W f) := by
  haveI := hg
  intro V hV
  have key : fQ W f ⁻¹' (fQ W f '' V) =
      ⋃ n ∈ {x : RT W.t | f x.val = 0}, (fun x : RT W.t => x - n) ⁻¹' V := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨v, hv, hvx⟩
      refine Set.mem_iUnion₂.2 ⟨x - v, ?_, ?_⟩
      · show f (x - v).val = 0
        have e : f (x - v).val = fQ W f x - fQ W f v := fQ_sub W f x v
        rw [e, hvx]; exact sub_self _
      · show x - (x - v) ∈ V
        rw [sub_sub_cancel]; exact hv
    · intro hx
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.1 hx
      refine ⟨x - n, hxn, ?_⟩
      have hn' : f n.val = 0 := hn
      have e : fQ W f (x - n) = fQ W f x - fQ W f n := fQ_sub W f x n
      have hn2 : fQ W f n = 0 := hn'
      rw [e, hn2]; exact sub_zero _
  refine (isOpen_coinduced (f := fun x : ℝ => (f x : ℚ)) (t := W.t)).2 ?_
  show IsOpen (fQ W f ⁻¹' (fQ W f '' V))
  rw [key]
  exact isOpen_biUnion fun n _ => hV.preimage (continuous_sub_right n)

theorem QuotQ_group' (hg : IsTopologicalAddGroup (RT W.t)) (u : ℝ) (hu : f u = 1) :
    IsTopologicalAddGroup (QuotQ W f) := by
  haveI := hg
  have hoq : IsOpenQuotientMap (fQ W f) := ⟨fQ_surjective u hu, fQ_continuous W f, fQ_isOpenMap' hg⟩
  have hoq2 : IsOpenQuotientMap (Prod.map (fQ W f) (fQ W f)) := hoq.prodMap hoq
  have hadd : Continuous (fun p : QuotQ W f × QuotQ W f => p.1 + p.2) := by
    rw [← hoq2.continuous_comp_iff]
    have : ((fun p : QuotQ W f × QuotQ W f => p.1 + p.2) ∘ Prod.map (fQ W f) (fQ W f)) =
        fQ W f ∘ (fun p : RT W.t × RT W.t => p.1 + p.2) := by
      funext p; exact (fQ_add W f p.1 p.2).symm
    rw [this]
    exact (fQ_continuous W f).comp continuous_add
  have hneg : Continuous (fun p : QuotQ W f => -p) := by
    rw [← hoq.continuous_comp_iff]
    have : ((fun p : QuotQ W f => -p) ∘ fQ W f) = fQ W f ∘ (fun p : RT W.t => -p) := by
      funext p; exact (fQ_neg W f p).symm
    rw [this]
    exact (fQ_continuous W f).comp continuous_neg
  exact { continuous_add := hadd, continuous_neg := hneg }

theorem QuotQ_t2' (hg : IsTopologicalAddGroup (RT W.t))
    (hq : ∀ q : ℚ, Continuous (show RT W.t → Circ from pfHom f (q : ℝ))) (u : ℝ) (hu : f u = 1) :
    T2Space (QuotQ W f) := by
  haveI := hg
  haveI := QuotQ_group' hg u hu
  have hN := ker_closed' hq
  haveI : T1Space (QuotQ W f) := by
    refine ⟨fun q => ?_⟩
    obtain ⟨x₀, hx₀⟩ := fQ_surjective (W := W) (f := f) u hu q
    have hpre : fQ W f ⁻¹' {q} = (fun x : RT W.t => x - x₀) ⁻¹' {x : RT W.t | f x.val = 0} := by
      apply Set.ext
      intro x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      have e : f (x - x₀).val = fQ W f x - fQ W f x₀ := fQ_sub W f x x₀
      rw [e, hx₀]
      exact ⟨sub_eq_zero.2, sub_eq_zero.1⟩
    exact isClosed_coinduced.2 (by
      show IsClosed (fQ W f ⁻¹' {q})
      rw [hpre]; exact hN.preimage (continuous_sub_right x₀))
  infer_instance

/-- **Lemma 19.1 (dual part).**  For `η` a group topology with dual `H_f`, the quotient topology `λ_η` of `ℚ ≅ ℝ/ker f`
has exactly the characters `Γ`. -/
theorem QuotQ_dualF (hg : IsTopologicalAddGroup (RT W.t))
    (hdual : ∀ χ : ℝ →+ Circ, Continuous (show RT W.t → Circ from χ) ↔ χ ∈ (Hset f ⊤ : Set Chars))
    (u : ℝ) (hu : f u = 1) (ψ : QuotQ W f →+ Circ) :
    Continuous ψ ↔ ∃ r : ℚ, ∀ q : QuotQ W f, ψ q = psi0 (r * (show ℚ from q)) := by
  haveI := hg
  constructor
  · intro hψ
    let ψ' : ℝ →+ Circ := ψ.comp (f : ℝ →+ QuotQ W f)
    have hψ'x : ∀ x : ℝ, ψ' x = ψ (show QuotQ W f from f x) := fun x => rfl
    have hcont : Continuous (show RT W.t → Circ from ψ') := hψ.comp (fQ_continuous W f)
    obtain ⟨c, a, -, hca⟩ := (hdual ψ').1 hcont
    -- `h x = c x + f(a x)` vanishes on `ker f`
    have hker : ∀ x : ℝ, f x = 0 → c * x + ((f (a * x) : ℚ) : ℝ) = 0 := by
      intro x hx
      have h1 := hca x
      have h2 : ψ' x = 0 := by
        rw [hψ'x]
        have : (show QuotQ W f from f x) = 0 := hx
        rw [this]
        exact map_zero ψ
      rw [h2] at h1
      unfold chiH at h1
      have h3 : ∀ n : ℕ, 0 < n → ∃ k : ℤ, (c * x + ((f (a * x) : ℚ) : ℝ)) / n = k := by
        intro n hn
        have hxn : f (x / n) = 0 := by
          have : x / (n : ℝ) = (((1 : ℚ) / n : ℚ) : ℝ) * x := by push_cast; ring
          rw [this, f_ratmul, hx]; simp
        have h1n := hca (x / n)
        have h2n : ψ' (x / n) = 0 := by
          rw [hψ'x]
          have : (show QuotQ W f from f (x / n)) = 0 := hxn
          rw [this]
          exact map_zero ψ
        rw [h2n] at h1n
        unfold chiH at h1n
        have h1n' := h1n.symm
        rw [AddCircle.coe_eq_zero_iff] at h1n'
        obtain ⟨k, hk⟩ := h1n'
        refine ⟨k, ?_⟩
        simp only [zsmul_eq_mul, mul_one] at hk
        have e : f (a * (x / n)) = (1 / (n : ℚ)) * f (a * x) := by
          have : a * (x / (n : ℝ)) = (((1 : ℚ) / n : ℚ) : ℝ) * (a * x) := by push_cast; ring
          rw [this, f_ratmul]
        rw [e] at hk
        push_cast at hk
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
        field_simp at hk
        linarith
      exact int_of_all_div _ h3
    obtain ⟨x0, hx0N, hx0⟩ : ∃ x0 : ℝ, f x0 = 0 ∧ x0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ker_uncountable f u hu
      refine (Set.countable_singleton (0 : ℝ)).mono (fun x hx => ?_)
      by_contra hne
      exact hne (by simpa using hcon x hx)
    -- `c = 0`: otherwise `c ker f ⊆ ℚ`, but `ker f` is uncountable
    have hc : c = 0 := by
      by_contra hc0
      apply ker_uncountable f u hu
      have hsub : {x : ℝ | f x = 0} ⊆ Set.range (fun q : ℚ => (q : ℝ) / c) := by
        intro x hx
        refine ⟨-(f (a * x)), ?_⟩
        have := hker x hx
        push_cast
        field_simp
        linarith
      exact (Set.countable_range _).mono hsub
    have hfa : ∀ x : ℝ, f x = 0 → f (a * x) = 0 := by
      intro x hx
      have := hker x hx
      rw [hc, zero_mul, zero_add] at this
      exact_mod_cast this
    -- `f_a = r f` with `r = f(a u)`
    have hfr : ∀ y : ℝ, f (a * y) = f (a * u) * f y := by
      intro y
      have hy : f (y - ((f y : ℚ) : ℝ) * u) = 0 := by
        rw [map_sub, f_ratmul, hu]; ring
      have h2 := hfa _ hy
      have e : a * (y - ((f y : ℚ) : ℝ) * u) = a * y - ((f y : ℚ) : ℝ) * (a * u) := by ring
      rw [e, map_sub, f_ratmul] at h2
      linarith
    refine ⟨f (a * u), fun q => ?_⟩
    obtain ⟨x, hx⟩ := f_surjective f u hu (show ℚ from q)
    have h1 := hca x
    have h2 : ψ' x = ψ q := by
      rw [hψ'x]
      have : (show QuotQ W f from f x) = q := hx
      rw [this]
    rw [h2] at h1
    rw [h1, psi0_apply]
    unfold chiH
    rw [hc, zero_mul, zero_add, hfr x, hx]
  · rintro ⟨r, hr⟩
    have hfun : (ψ : QuotQ W f → Circ) ∘ fQ W f = fun x : RT W.t => (pfHom f (r : ℝ)) x.val := by
      funext x
      simp only [Function.comp, fQ_apply]
      rw [hr (show QuotQ W f from f x.val), psi0_apply, pfHom_apply, f_ratmul]
    refine continuous_coinduced_dom.2 ?_
    show Continuous (ψ ∘ fQ W f)
    rw [hfun]
    exact (hdual _).2 (pfHom_memF f r)

/-- **Lemma 19.1** (assembled): for `η ∈ ℒ_f`, `ker f` is closed, `f` is an open continuous surjection onto
`(ℚ, λ_η)`, which is a Hausdorff group topology with full dual `Γ`. -/
theorem quotient_lemma_F (hη : W.t ∈ Lcls (Hset f ⊤ : Set Chars)) (u : ℝ) (hu : f u = 1) :
    IsClosed {x : RT W.t | f x.val = 0} ∧
    (IsOpenMap (fQ W f) ∧ Continuous (fQ W f) ∧ Function.Surjective (fQ W f)) ∧
    (IsTopologicalAddGroup (QuotQ W f) ∧ T2Space (QuotQ W f)) ∧
    (∀ ψ : QuotQ W f →+ Circ, Continuous ψ ↔ ∃ r : ℚ, ∀ q : QuotQ W f, ψ q = psi0 (r * (show ℚ from q))) := by
  have hq : ∀ q : ℚ, Continuous (show RT W.t → Circ from pfHom f (q : ℝ)) :=
    fun q => (hη.2.2.2 _).2 (pfHom_memF f q)
  exact ⟨ker_closed' hq, ⟨fQ_isOpenMap' hη.1, fQ_continuous W f, fQ_surjective u hu⟩,
    ⟨QuotQ_group' hη.1 u hu, QuotQ_t2' hη.1 hq u hu⟩, QuotQ_dualF hη.1 hη.2.2.2 u hu⟩

/-- The dual of `λ_μ` (coinduced along `f`) is `Γ`, for `μ ∈ ℒ_f`. -/
theorem lamTop_dualF (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Lcls (Hset f ⊤ : Set Chars)) (ψ : ℚ →+ Circ) :
    @Continuous ℚ Circ (lamTop f μ) circTop ψ ↔ ψ ∈ Gam := by
  have key := QuotQ_dualF (W := ⟨μ⟩) hμ.1 hμ.2.2.2 u hu (show QuotQ ⟨μ⟩ f →+ Circ from ψ)
  constructor
  · intro hc
    obtain ⟨r, hr⟩ := key.1 hc
    refine ⟨r, fun s => ?_⟩
    rw [show ψ s = (show QuotQ ⟨μ⟩ f →+ Circ from ψ) s from rfl, hr s, psi0_apply]
  · rintro ⟨r, hr⟩
    refine key.2 ⟨r, fun q => ?_⟩
    rw [psi0_apply]
    exact hr q

end QuotientTVG

section NecessaryMackeyTVG

/-- `T_f(δ) ∈ 𝒞_f` for `δ ∈ 𝒬_Γ`. -/
theorem Tf_mem_Kcls (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (hδ : δ ∈ Ccls Gam) :
    Tf f δ ∈ Kcls (Hset f ⊤ : Set Chars) realDil := by
  obtain ⟨⟨hg, ht, hl, hd⟩, hs⟩ := hδ
  have hs' : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x) := by
    intro s
    have := hs s
    have e : (fun x : ℚ => s * x) = ⇑(mq s) := by funext x; simp [mq_apply]
    rw [e]; exact this
  have hmem : ∀ χ : Chars, (∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ↔ χ ∈ (Hset f ⊤ : Set Chars) :=
    fun χ => ⟨fun ⟨c, a, h⟩ => ⟨c, a, Submodule.mem_top, h⟩, fun ⟨c, a, _, h⟩ => ⟨c, a, h⟩⟩
  refine ⟨Tf_group f δ hg, Tf_t2 f δ, lqc_Tf f δ hl, fun χ => ?_, ?_⟩
  · exact (dual_Tf f δ hg hs' (fun ψ => hd ψ) χ).trans (hmem χ)
  · rintro _ ⟨a, rfl⟩
    exact Tf_dilation f δ a

/-- If `μ` is greatest in `𝒞_f`, then `λ_μ` is finer than every compatible topology on `ℚ`. -/
theorem lam_le_F (f : ℝ →+ ℚ) (μ : TopologicalSpace ℝ)
    (hgr : ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ) (δ : TopologicalSpace ℚ) (hδ : δ ∈ Lcls Gam) :
    lamTop f μ ≤ δ := by
  obtain ⟨hs, hle, -⟩ := saturation Gam Gam_ratInv δ hδ
  have hT := Tf_mem_Kcls f (sat δ) hs
  have hμT : μ ≤ Tf f (sat δ) := hgr _ hT
  have hf1 : Continuous[Tf f (sat δ), sat δ] f := by
    have := fa_cont f (sat δ) 1
    have e : (fa f 1 : ℝ → ℚ) = f := by funext x; simp [fa]
    rw [e] at this; exact this
  have hcont : Continuous[μ, sat δ] f := continuous_le_dom hμT hf1
  have : lamTop f μ ≤ sat δ := by
    unfold lamTop
    exact continuous_iff_coinduced_le.1 hcont
  exact this.trans hle

/-- **Corollary 19.4.**  If `𝒞_f` has a greatest member, then `(ℚ, Γ)` has a Mackey topology: a greatest
Hausdorff locally quasi-convex group topology with dual `Γ` (which is also greatest in `𝒬_Γ`). -/
theorem necessary_mackey_F (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (μ : TopologicalSpace ℝ)
    (hμ : μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil)
    (hgr : ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ) :
    ∃ ν : TopologicalSpace ℚ,
      (ν ∈ Lcls Gam ∧ ∀ δ ∈ Lcls Gam, ν ≤ δ) ∧ (ν ∈ Ccls Gam ∧ ∀ δ ∈ Ccls Gam, ν ≤ δ) := by
  have hlam : ∀ δ ∈ Lcls Gam, lamTop f μ ≤ δ := fun δ hδ => lam_le_F f μ hgr δ hδ
  let Fam : Set (TopologicalSpace ℚ) :=
    {ν | @IsTopologicalAddGroup ℚ ν _ ∧ @T2Space ℚ ν ∧ LocQC ν ∧ lamTop f μ ≤ ν}
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
  have hμL : μ ∈ Lcls (Hset f ⊤ : Set Chars) := ⟨hμ.1, hμ.2.1, hμ.2.2.1, hμ.2.2.2.1⟩
  have hνdual : ∀ χ : ℚ →+ Circ, @Continuous ℚ Circ ν circTop χ ↔ χ ∈ Gam := by
    intro χ
    constructor
    · intro hc
      exact (lamTop_dualF u hu μ hμL χ).1 (continuous_le_dom hlamν hc)
    · intro hχ
      exact continuous_le_dom hνle (hd1 χ |>.2 hχ)
  have hνL : ν ∈ Lcls Gam := ⟨hνgrp, hνt2, hνlqc, hνdual⟩
  have hνgreat : ∀ δ ∈ Lcls Gam, ν ≤ δ := fun δ hδ =>
    iInf_le (fun δ : Fam => δ.1) ⟨δ, ⟨hδ.1, hδ.2.1, hδ.2.2.1, hlam δ hδ⟩⟩
  refine ⟨ν, ⟨hνL, hνgreat⟩, ?_⟩
  exact ((mackey_equivalence Gam Gam_ratInv).1 ν).2 ⟨hνL, hνgreat⟩

/-- **Corollary 26.6 (position of the conjecture)** for a coefficient function `f` with `f u = 1`:
a Mackey topology for `(ℝ, H_f)` ⇒ the TVG class `𝒞_f` has a greatest member ⇒ `(ℚ, Γ)` has a Mackey topology. -/
theorem sandwich (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ((∃ μ ∈ Kcls (Hset f ⊤ : Set Chars) ∅, ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) ∅, μ ≤ τ) →
      ∃ μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ) ∧
    ((∃ μ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, ∀ τ ∈ Kcls (Hset f ⊤ : Set Chars) realDil, μ ≤ τ) →
      ∃ ν : TopologicalSpace ℚ, ν ∈ Lcls Gam ∧ ∀ δ ∈ Lcls Gam, ν ≤ δ) := by
  constructor
  · rintro ⟨μ, hμ, hgr⟩
    exact ⟨μ, mackey_implies_conjecture f μ hμ hgr⟩
  · rintro ⟨μ, hμ, hgr⟩
    obtain ⟨ν, hν, -⟩ := necessary_mackey_F f u hu μ hμ hgr
    exact ⟨ν, hν⟩

end NecessaryMackeyTVG

end LeanCheck
