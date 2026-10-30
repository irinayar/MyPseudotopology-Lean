import LeanCheck.ChainComp7
import LeanCheck.ChainSaturation

/-!
# The rational quotient and the Baire obstruction (TVGQ-v7 Lemma `quotient-v4`, Theorem `nonbaire-v4`)

Let `η` be a Hausdorff locally quasi-convex group topology on `ℝ` whose full character group is exactly
`H_{f,ℚ} = {x ↦ p(c x + r f(x)) : c ∈ ℝ, r ∈ ℚ}` (no rational scalar continuity is assumed).  Put `N = ker f`
and let `λ_η` be the quotient topology of `ℝ/N ≅ ℚ` (through `f`), i.e. the coinduced topology of `f`.

* `ker_closed`: `N` is closed;
* `fQ_isOpenMap`, `fQ_continuous`, `fQ_surjective`: `f : (ℝ, η) → (ℚ, λ_η)` is an open continuous surjection;
* `QuotQ_isTopologicalAddGroup`, `QuotQ_t2`: `λ_η` is a Hausdorff group topology;
* `QuotQ_dual`: the full character group of `(ℚ, λ_η)` is exactly `Γ = {q ↦ p(r q) : r ∈ ℚ}`;
* `QuotQ_not_discrete`: `λ_η` is not discrete;
* `not_baire`: `(ℝ, η)` is not a Baire space (the rationals give countably many dense open sets with empty
  intersection); hence `not_locallyCompact` and `not_completelyMetrizable`.

(`ℝ` with the topology `η` is the type `RT η`, and `η` is carried inside the wrapper `TopW`, so that no
local instance on `ℝ` captures the topology of the circle.)
-/

namespace LeanCheck

open Topology Filter

/-- A wrapper around a topology on `ℝ` (not a class, hence no local-instance capture). -/
structure TopW where
  t : TopologicalSpace ℝ

/-- The real number underlying a point of `RT η`. -/
def RT.val {η : TopologicalSpace ℝ} (x : RT η) : ℝ := x

/-- `ℚ ≅ ℝ/N` with the quotient topology of `f`. -/
def QuotQ (_W : TopW) (_f : ℝ →+ ℚ) : Type := ℚ

noncomputable instance (W : TopW) (f : ℝ →+ ℚ) : AddCommGroup (QuotQ W f) :=
  inferInstanceAs (AddCommGroup ℚ)

instance (W : TopW) (f : ℝ →+ ℚ) : TopologicalSpace (QuotQ W f) :=
  TopologicalSpace.coinduced (fun x : ℝ => (f x : ℚ)) W.t

/-- The quotient map `f : (ℝ, η) → (ℚ, λ_η)`. -/
def fQ (W : TopW) (f : ℝ →+ ℚ) : RT W.t → QuotQ W f := fun x => f x.val

lemma fQ_apply (W : TopW) (f : ℝ →+ ℚ) (x : RT W.t) : fQ W f x = f x.val := rfl

lemma fQ_continuous (W : TopW) (f : ℝ →+ ℚ) : Continuous (fQ W f) :=
  continuous_coinduced_rng

lemma fQ_add (W : TopW) (f : ℝ →+ ℚ) (x y : RT W.t) : fQ W f (x + y) = fQ W f x + fQ W f y :=
  map_add f x.val y.val

lemma fQ_neg (W : TopW) (f : ℝ →+ ℚ) (x : RT W.t) : fQ W f (-x) = - fQ W f x :=
  map_neg f x.val

lemma fQ_sub (W : TopW) (f : ℝ →+ ℚ) (x y : RT W.t) : fQ W f (x - y) = fQ W f x - fQ W f y :=
  map_sub f x.val y.val

/-- Standing hypotheses: `η` is a Hausdorff group topology with full dual `H_{f,ℚ}`. -/
structure QCompat (W : TopW) (f : ℝ →+ ℚ) : Prop where
  grp : IsTopologicalAddGroup (RT W.t)
  t2 : T2Space (RT W.t)
  dual : ∀ χ : ℝ →+ Circ, Continuous (show RT W.t → Circ from χ) ↔ χ ∈ Hq f

theorem QCompat.of_Lcls {W : TopW} {f : ℝ →+ ℚ} (hη : W.t ∈ Lcls (Hq f)) : QCompat W f :=
  ⟨hη.1, hη.2.1, fun χ => hη.2.2.2 χ⟩

lemma pfHom_mem (f : ℝ →+ ℚ) (q : ℚ) : pfHom f (q : ℝ) ∈ Hq f :=
  ⟨0, q, fun x => by simp [pfHom_apply, chiH]⟩

lemma half_ne_zero_circ : (((1 / 2 : ℝ)) : Circ) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  simp only [zsmul_eq_mul, mul_one] at hn
  have h1 : (2 : ℝ) * n = 1 := by linarith
  have h2 : (2 : ℤ) * n = 1 := by exact_mod_cast h1
  omega

variable {W : TopW} {f : ℝ →+ ℚ}

/-- **`N = ker f` is closed.** -/
theorem ker_closed (h : QCompat W f) : IsClosed {x : RT W.t | f x.val = 0} := by
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
  have hc : Continuous (show RT W.t → Circ from (pfHom f (q : ℝ))) :=
    (h.dual _).2 (pfHom_mem f q)
  exact isClosed_singleton.preimage hc

lemma fQ_surjective (u : ℝ) (hu : f u = 1) : Function.Surjective (fQ W f) := by
  intro q
  obtain ⟨x, hx⟩ := f_surjective f u hu q
  exact ⟨x, hx⟩

/-- **`f : (ℝ, η) → (ℚ, λ_η)` is an open map.** -/
theorem fQ_isOpenMap (h : QCompat W f) : IsOpenMap (fQ W f) := by
  haveI := h.grp
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

lemma fQ_openQuotient (h : QCompat W f) (u : ℝ) (hu : f u = 1) : IsOpenQuotientMap (fQ W f) :=
  ⟨fQ_surjective u hu, fQ_continuous W f, fQ_isOpenMap h⟩

/-- **The quotient topology `λ_η` is a group topology.** -/
theorem QuotQ_isTopologicalAddGroup (h : QCompat W f) (u : ℝ) (hu : f u = 1) :
    IsTopologicalAddGroup (QuotQ W f) := by
  haveI := h.grp
  have hoq := fQ_openQuotient h u hu
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

/-- **`λ_η` is Hausdorff.** -/
theorem QuotQ_t2 (h : QCompat W f) (u : ℝ) (hu : f u = 1) : T2Space (QuotQ W f) := by
  haveI := h.grp
  haveI := QuotQ_isTopologicalAddGroup h u hu
  have hN := ker_closed h
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

/-- **The full character group of `(ℚ, λ_η)` is exactly `Γ = {q ↦ p(r q) : r ∈ ℚ}`.** -/
theorem QuotQ_dual (h : QCompat W f) (u : ℝ) (hu : f u = 1) (ψ : QuotQ W f →+ Circ) :
    Continuous ψ ↔ ∃ r : ℚ, ∀ q : QuotQ W f, ψ q = psi0 (r * (show ℚ from q)) := by
  haveI := h.grp
  constructor
  · intro hψ
    let ψ' : ℝ →+ Circ := ψ.comp (f : ℝ →+ QuotQ W f)
    have hψ'x : ∀ x : ℝ, ψ' x = ψ (show QuotQ W f from f x) := fun x => rfl
    have hcont : Continuous (show RT W.t → Circ from ψ') := hψ.comp (fQ_continuous W f)
    obtain ⟨c, r, hcr⟩ := (h.dual ψ').1 hcont
    obtain ⟨x0, hx0N, hx0⟩ : ∃ x0 : ℝ, f x0 = 0 ∧ x0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ker_uncountable f u hu
      refine (Set.countable_singleton (0 : ℝ)).mono (fun x hx => ?_)
      by_contra hne
      exact hne (by simpa using hcon x hx)
    have hψ0 : ∀ x : ℝ, f x = 0 → ((c * x : ℝ) : Circ) = 0 := by
      intro x hx
      have h1 := hcr x
      have h2 : ψ' x = 0 := by
        rw [hψ'x]
        have : (show QuotQ W f from f x) = 0 := hx
        rw [this]
        exact map_zero ψ
      rw [h2] at h1
      have h3 : f ((r : ℝ) * x) = 0 := by rw [f_ratmul, hx]; simp
      unfold chiH at h1
      rw [h3] at h1
      simpa using h1.symm
    have hc : c = 0 := by
      have h1 : c * x0 = 0 := by
        apply int_of_all_div
        intro n hn
        have hxn : f (x0 / n) = 0 := by
          have : x0 / (n : ℝ) = (((1 : ℚ) / n : ℚ) : ℝ) * x0 := by push_cast; ring
          rw [this, f_ratmul, hx0N]; simp
        have := hψ0 _ hxn
        rw [AddCircle.coe_eq_zero_iff] at this
        obtain ⟨k, hk⟩ := this
        refine ⟨k, ?_⟩
        simp only [zsmul_eq_mul, mul_one] at hk
        rw [hk]; ring
      exact (mul_eq_zero.1 h1).resolve_right hx0
    refine ⟨r, fun q => ?_⟩
    obtain ⟨x, hx⟩ := f_surjective f u hu (show ℚ from q)
    have h1 := hcr x
    have h2 : ψ' x = ψ q := by
      rw [hψ'x]
      have : (show QuotQ W f from f x) = q := hx
      rw [this]
    rw [h2] at h1
    rw [h1, psi0_apply]
    unfold chiH
    rw [hc, zero_mul, zero_add, f_ratmul, hx]
  · rintro ⟨r, hr⟩
    have hfun : (ψ : QuotQ W f → Circ) ∘ fQ W f = fun x : RT W.t => (pfHom f (r : ℝ)) x.val := by
      funext x
      simp only [Function.comp, fQ_apply]
      rw [hr (show QuotQ W f from f x.val), psi0_apply, pfHom_apply, f_ratmul]
    refine continuous_coinduced_dom.2 ?_
    show Continuous (ψ ∘ fQ W f)
    rw [hfun]
    exact (h.dual _).2 (pfHom_mem f r)

/-- **`λ_η` is not discrete.** -/
theorem QuotQ_not_discrete (h : QCompat W f) (u : ℝ) (hu : f u = 1) : ¬ DiscreteTopology (QuotQ W f) := by
  intro hdisc
  let ψ0 : ℚ →+ Circ :=
    { toFun := fun q => (((Real.sqrt 2 * (q : ℝ)) : ℝ) : Circ)
      map_zero' := by simp
      map_add' := fun a b => by
        push_cast
        rw [mul_add]
        exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _ }
  let ψ : QuotQ W f →+ Circ := ψ0
  have hψ : Continuous ψ := continuous_of_discreteTopology
  obtain ⟨r, hr⟩ := (QuotQ_dual h u hu ψ).1 hψ
  have key : ∀ n : ℕ, 0 < n → ∃ k : ℤ, (Real.sqrt 2 - r) / n = k := by
    intro n hn
    have h1 := hr (show QuotQ W f from ((1 / n : ℚ)))
    have h1' : (((Real.sqrt 2 * ((1 / (n : ℚ) : ℚ) : ℝ)) : ℝ) : Circ) =
        ((((r : ℝ) * ((1 / (n : ℚ) : ℚ) : ℝ)) : ℝ) : Circ) := by
      have h1c : ((((Real.sqrt 2 * (((1 / (n : ℚ) : ℚ)) : ℝ)) : ℝ)) : Circ) = psi0 (r * (1 / (n : ℚ))) := h1
      rw [psi0_apply] at h1c
      push_cast at h1c ⊢
      exact h1c
    have h2 : ((((Real.sqrt 2 * ((1 / (n : ℚ) : ℚ) : ℝ)) - ((r : ℝ) * ((1 / (n : ℚ) : ℚ) : ℝ)) : ℝ)) :
        Circ) = 0 := by
      rw [AddCircle.coe_sub, h1', sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    push_cast at hk
    rw [hk]; ring
  have h0 : Real.sqrt 2 - r = 0 := int_of_all_div _ key
  exact irrational_sqrt_two ⟨r, by linarith⟩

/-- **Lemma `quotient-v4`** (assembled): for `η ∈ ℒ(H_{f,ℚ})` the kernel is closed, `f` is an open continuous
surjection onto `(ℚ, λ_η)`, `λ_η` is a Hausdorff group topology with full dual `Γ`, and it is not discrete. -/
theorem quotient_lemma (hη : W.t ∈ Lcls (Hq f)) (u : ℝ) (hu : f u = 1) :
    IsClosed {x : RT W.t | f x.val = 0} ∧
    (IsOpenMap (fQ W f) ∧ Continuous (fQ W f) ∧ Function.Surjective (fQ W f)) ∧
    (IsTopologicalAddGroup (QuotQ W f) ∧ T2Space (QuotQ W f)) ∧
    (∀ ψ : QuotQ W f →+ Circ, Continuous ψ ↔ ∃ r : ℚ, ∀ q : QuotQ W f, ψ q = psi0 (r * (show ℚ from q))) ∧
    ¬ DiscreteTopology (QuotQ W f) := by
  have h := QCompat.of_Lcls hη
  exact ⟨ker_closed h, ⟨fQ_isOpenMap h, fQ_continuous W f, fQ_surjective u hu⟩,
    ⟨QuotQ_isTopologicalAddGroup h u hu, QuotQ_t2 h u hu⟩, QuotQ_dual h u hu, QuotQ_not_discrete h u hu⟩

/-! ### The Baire obstruction -/

/-- **Theorem `nonbaire-v4`.**  Every topology in `ℒ(H_{f,ℚ})` is non-Baire. -/
theorem not_baire (hη : W.t ∈ Lcls (Hq f)) (u : ℝ) (hu : f u = 1) : ¬ BaireSpace (RT W.t) := by
  have h := QCompat.of_Lcls hη
  haveI := h.grp
  haveI := QuotQ_isTopologicalAddGroup h u hu
  haveI := QuotQ_t2 h u hu
  intro hB
  -- the countably many open dense sets `{x | f x ≠ q}`
  let U : ℚ → Set (RT W.t) := fun q => fQ W f ⁻¹' {(show QuotQ W f from q)}ᶜ
  have hUo : ∀ q, IsOpen (U q) := fun q =>
    (isClosed_singleton (x := (show QuotQ W f from q))).isOpen_compl.preimage (fQ_continuous W f)
  have hUd : ∀ q, Dense (U q) := by
    intro q
    rw [dense_iff_inter_open]
    intro V hVo hVne
    by_contra hVU
    have hsub : V ⊆ fQ W f ⁻¹' {(show QuotQ W f from q)} := by
      intro x hx
      by_contra hxq
      exact hVU ⟨x, hx, hxq⟩
    obtain ⟨v, hv⟩ := hVne
    have hopen : IsOpen (fQ W f '' V) := fQ_isOpenMap h V hVo
    have hsing : fQ W f '' V = {(show QuotQ W f from q)} := by
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hsub hx
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨v, hv, by rw [hy]; exact hsub hv⟩
    rw [hsing] at hopen
    have hzero : IsOpen ({0} : Set (QuotQ W f)) := by
      have hc : Continuous (fun y : QuotQ W f => y + (show QuotQ W f from q)) :=
        continuous_id.add continuous_const
      have := hopen.preimage hc
      convert this using 1
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hy => Set.mem_singleton_iff.2 (by rw [hy]; exact zero_add _),
        fun hy => add_eq_right.1 (Set.mem_singleton_iff.1 hy)⟩
    exact QuotQ_not_discrete h u hu (discreteTopology_of_isOpen_singleton_zero hzero)
  have hdense := dense_iInter_of_isOpen hUo hUd
  have hempty : (⋂ q, U q) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have := Set.mem_iInter.1 hx (fQ W f x)
    exact this rfl
  rw [hempty] at hdense
  have h0 : (0 : RT W.t) ∈ closure (∅ : Set (RT W.t)) := hdense 0
  simp at h0

/-- Every member of `𝒞_ℚ(H_{f,ℚ})` is a member of `ℒ(H_{f,ℚ})`, hence non-Baire. -/
theorem not_baire_Ccls (hη : W.t ∈ Ccls (Hq f)) (u : ℝ) (hu : f u = 1) : ¬ BaireSpace (RT W.t) :=
  not_baire hη.1 u hu

/-- No member of `ℒ(H_{f,ℚ})` is locally compact. -/
theorem not_locallyCompact (hη : W.t ∈ Lcls (Hq f)) (u : ℝ) (hu : f u = 1) :
    ¬ LocallyCompactSpace (RT W.t) := by
  intro hlc
  haveI := (QCompat.of_Lcls hη).t2
  haveI := (QCompat.of_Lcls hη).grp
  exact not_baire hη u hu inferInstance

/-- No member of `ℒ(H_{f,ℚ})` is completely metrizable. -/
theorem not_completelyMetrizable (hη : W.t ∈ Lcls (Hq f)) (u : ℝ) (hu : f u = 1) :
    ¬ TopologicalSpace.IsCompletelyMetrizableSpace (RT W.t) := by
  intro hcm
  exact not_baire hη u hu inferInstance

end LeanCheck
