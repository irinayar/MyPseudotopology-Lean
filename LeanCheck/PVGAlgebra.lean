import Mathlib

/-!
# PVG: linear-algebra and cardinality facts (Lean check)

Scope. These declarations check, in an abstract setting, algebraic steps used in
`PVG_v9` (Pseudotopological Vector Groups on Real Line), Section 8:

* `maximal_admissible_iff`  : Corollary 8.27(a) (maximal admissible subspaces are complements);
* `exists_maximal_admissible`: every admissible subspace lies in a maximal one;
* `no_common_admissible`    : the algebraic core of Corollary 8.24;
* `retractionEquiv`         : Corollary 8.27(c), complements of the line versus linear retractions;
* `card_retractions`        : the count `2 ^ (2 ^ 𝔠)` of such retractions;
* `rank_eq_of_card`         : the dimension step in Lemma 8.26(c) and Proposition 8.28(b).

The space `K` is an arbitrary real vector space and the line `ℝ ∙ e1` stands for `e(ℝ)`.
Nothing here mentions the compact group `Hom(ℝ, 𝕋)`, ultrafilters or pseudotopologies;
the correspondence with the article statements requires mathematical review.
-/

namespace PVG

open Cardinal Module

section Admissible

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

/-- `G` is admissible with respect to the line `L` if it meets `L` only in zero. -/
def Admissible (L G : Submodule ℝ K) : Prop := Disjoint G L

/-- Corollary 8.27(a): an admissible subspace is maximal iff it is a complement of the line. -/
theorem maximal_admissible_iff (L G : Submodule ℝ K) (hG : Admissible L G) :
    (∀ G' : Submodule ℝ K, Admissible L G' → G ≤ G' → G' ≤ G) ↔ Codisjoint G L := by
  constructor
  · intro hmax
    by_contra hnc
    have hne : G ⊔ L ≠ ⊤ := fun h => hnc (codisjoint_iff.2 h)
    obtain ⟨κ, hκ⟩ : ∃ κ, κ ∉ G ⊔ L := by
      by_contra h
      have h' : ∀ x, x ∈ G ⊔ L := fun x => by
        by_contra hx
        exact h ⟨x, hx⟩
      exact hne (eq_top_iff.2 fun x _ => h' x)
    have hadm : Admissible L (G ⊔ ℝ ∙ κ) := by
      rw [Admissible, Submodule.disjoint_def]
      intro x hx hxL
      obtain ⟨g, hg, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      by_cases hc : c = 0
      · subst hc
        simp only [zero_smul, add_zero] at hxL ⊢
        exact Submodule.disjoint_def.1 hG g hg hxL
      · exfalso
        apply hκ
        have h1 : c • κ = (g + c • κ) - g := by abel
        have h2 : c • κ ∈ G ⊔ L :=
          h1 ▸ Submodule.sub_mem _ (Submodule.mem_sup_right hxL) (Submodule.mem_sup_left hg)
        have h3 := (G ⊔ L).smul_mem c⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    have hle := hmax _ hadm le_sup_left
    apply hκ
    exact Submodule.mem_sup_left (hle (Submodule.mem_sup_right (Submodule.mem_span_singleton_self κ)))
  · intro hc G' hG' hle x hx
    have hx' : x ∈ G ⊔ L := by rw [codisjoint_iff.1 hc]; trivial
    obtain ⟨g, hg, l, hl, rfl⟩ := Submodule.mem_sup.1 hx'
    have hlG' : l ∈ G' := by
      have := G'.sub_mem hx (hle hg)
      simpa using this
    have hl0 : l = 0 := Submodule.disjoint_def.1 hG' l hlG' hl
    simp [hl0, hg]

/-- Every admissible subspace is contained in a maximal admissible subspace. -/
theorem exists_maximal_admissible (L G : Submodule ℝ K) (hG : Admissible L G) :
    ∃ H : Submodule ℝ K, G ≤ H ∧ Admissible L H ∧
      ∀ G' : Submodule ℝ K, Admissible L G' → H ≤ G' → G' ≤ H := by
  have := zorn_le_nonempty₀ {G' : Submodule ℝ K | Admissible L G'} ?_ G hG
  · obtain ⟨H, hGH, hHm⟩ := this
    refine ⟨H, hGH, hHm.prop, fun G' hG' hHG' => ?_⟩
    exact (hHm.eq_of_ge hG' hHG').le
  · intro c hcs hc y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    show Admissible L (sSup c)
    rw [Admissible, Submodule.disjoint_def]
    intro x hx hxL
    rw [Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    exact Submodule.disjoint_def.1 (hcs hz) x hxz hxL

/-- Algebraic core of Corollary 8.24: if `φ a ∈ L` forces `a = 0`, then the graph subspace
`{e a + φ a}` is admissible, and no subspace containing both `range φ` and the graph is
admissible. -/
theorem no_common_admissible (e1 : K) (he : e1 ≠ 0) (φ : ℝ →ₗ[ℝ] K)
    (hφ : ∀ a : ℝ, φ a ∈ (ℝ ∙ e1) → a = 0) :
    Admissible (ℝ ∙ e1) (LinearMap.range (LinearMap.toSpanSingleton ℝ K e1 + φ)) ∧
    ∀ G : Submodule ℝ K, LinearMap.range φ ≤ G →
      LinearMap.range (LinearMap.toSpanSingleton ℝ K e1 + φ) ≤ G →
      ¬ Admissible (ℝ ∙ e1) G := by
  constructor
  · rw [Admissible, Submodule.disjoint_def]
    rintro x ⟨a, rfl⟩ hxL
    have h1 : φ a ∈ (ℝ ∙ e1) := by
      have : φ a = (LinearMap.toSpanSingleton ℝ K e1 + φ) a - a • e1 := by simp
      rw [this]
      refine Submodule.sub_mem _ hxL (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e1))
    have ha := hφ a h1
    subst ha
    simp
  · intro G h1 h2 hG
    have h3 : e1 ∈ G := by
      have := G.sub_mem (h2 ⟨1, rfl⟩) (h1 ⟨1, rfl⟩)
      simpa using this
    have := Submodule.disjoint_def.1 hG e1 h3 (Submodule.mem_span_singleton_self e1)
    exact he this

end Admissible

section Retraction

variable {K : Type*} [AddCommGroup K] [Module ℝ K] {e1 : K}

/-- The kernel of a linear retraction `π` (`π e1 = 1`) is a complement of the line. -/
theorem ker_isCompl (π : K →ₗ[ℝ] ℝ) (hπ : π e1 = 1) :
    IsCompl (ℝ ∙ e1) (LinearMap.ker π) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxk
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have h : c = 0 := by
      have := LinearMap.mem_ker.1 hxk
      simpa [hπ] using this
    simp [h]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = π x • e1 + (x - π x • e1) := by abel
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e1)) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, hπ]
    simp

/-- A linear retraction is determined by its kernel. -/
theorem retraction_unique (π π' : K →ₗ[ℝ] ℝ) (h1 : π e1 = 1) (h2 : π' e1 = 1)
    (hk : LinearMap.ker π = LinearMap.ker π') : π = π' := by
  ext x
  have hmem : x - π x • e1 ∈ LinearMap.ker π := by
    rw [LinearMap.mem_ker, map_sub, map_smul, h1]; simp
  have hmem' : x - π x • e1 ∈ LinearMap.ker π' := hk ▸ hmem
  rw [LinearMap.mem_ker, map_sub, map_smul, h2] at hmem'
  simp only [smul_eq_mul, mul_one] at hmem'
  linarith

/-- The retraction along a complement `H` of the line `ℝ ∙ e1`. -/
noncomputable def retraction (he : e1 ≠ 0) (H : Submodule ℝ K) (h : IsCompl (ℝ ∙ e1) H) :
    K →ₗ[ℝ] ℝ :=
  (LinearEquiv.toSpanNonzeroSingleton ℝ K e1 he).symm.toLinearMap ∘ₗ
    Submodule.projectionOnto (ℝ ∙ e1) H h

theorem retraction_apply_e1 (he : e1 ≠ 0) (H : Submodule ℝ K) (h : IsCompl (ℝ ∙ e1) H) :
    retraction he H h e1 = 1 := by
  have hmem : e1 ∈ (ℝ ∙ e1) := Submodule.mem_span_singleton_self e1
  have h1 := Submodule.projectionOnto_apply_left h ⟨e1, hmem⟩
  simp only [retraction, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h1, LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.toSpanNonzeroSingleton_apply]

theorem ker_retraction (he : e1 ≠ 0) (H : Submodule ℝ K) (h : IsCompl (ℝ ∙ e1) H) :
    LinearMap.ker (retraction he H h) = H := by
  ext x
  simp only [LinearMap.mem_ker, retraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    map_eq_zero_iff _ (LinearEquiv.injective _)]
  rw [← LinearMap.mem_ker, Submodule.ker_projectionOnto]

/-- Corollary 8.27(c): complements of the line correspond bijectively to linear retractions. -/
noncomputable def retractionEquiv (he : e1 ≠ 0) :
    {H : Submodule ℝ K // IsCompl (ℝ ∙ e1) H} ≃ {π : K →ₗ[ℝ] ℝ // π e1 = 1} where
  toFun H := ⟨retraction he H.1 H.2, retraction_apply_e1 he H.1 H.2⟩
  invFun π := ⟨LinearMap.ker π.1, ker_isCompl π.1 π.2⟩
  left_inv H := Subtype.ext (ker_retraction he H.1 H.2)
  right_inv π := Subtype.ext
    (retraction_unique _ _ (retraction_apply_e1 he _ _) π.2 (ker_retraction he _ _))

end Retraction

section Card

open Cardinal

/-- The dimension step: a real vector space of cardinality `2 ^ 𝔠` has dimension `2 ^ 𝔠`. -/
theorem rank_eq_of_card (V : Type) [AddCommGroup V] [Module ℝ V] (h : #V = 2 ^ #ℝ) :
    Module.rank ℝ V = 2 ^ #ℝ := by
  apply le_antisymm
  · exact h ▸ rank_le_card ℝ V
  · let b := Module.Basis.ofVectorSpace ℝ V
    have hb : #(Module.Basis.ofVectorSpaceIndex ℝ V) = Module.rank ℝ V := b.mk_eq_rank''
    have hV : #V = #((Module.Basis.ofVectorSpaceIndex ℝ V) →₀ ℝ) := Cardinal.mk_congr b.repr.toEquiv
    by_cases hinf : Infinite (Module.Basis.ofVectorSpaceIndex ℝ V)
    · rw [Cardinal.mk_finsupp_of_infinite] at hV
      rw [← hb]
      rcases le_total (#(Module.Basis.ofVectorSpaceIndex ℝ V)) #ℝ with hle | hle
      · rw [max_eq_right hle, h] at hV
        exact absurd hV (by rw [mk_real]; exact (cantor 𝔠).ne')
      · rw [max_eq_left hle, h] at hV
        exact hV.le
    · exfalso
      have hfin : Finite (Module.Basis.ofVectorSpaceIndex ℝ V) := not_infinite_iff_finite.1 hinf
      have hlt : #(Module.Basis.ofVectorSpaceIndex ℝ V) < ℵ₀ := Cardinal.lt_aleph0_of_finite _
      have h2 : #V ≤ 𝔠 := by
        rw [hV]
        have : #((Module.Basis.ofVectorSpaceIndex ℝ V) →₀ ℝ) =
            #((Module.Basis.ofVectorSpaceIndex ℝ V) → ℝ) :=
          Cardinal.mk_congr Finsupp.equivFunOnFinite
        rw [this, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, mk_real]
        calc 𝔠 ^ #(Module.Basis.ofVectorSpaceIndex ℝ V) ≤ 𝔠 ^ ℵ₀ :=
              Cardinal.power_le_power_left Cardinal.continuum_ne_zero hlt.le
          _ = 𝔠 := Cardinal.continuum_power_aleph0
      rw [h, mk_real] at h2
      exact absurd h2 (not_le.2 (cantor 𝔠))

/-- The number of linear retractions onto the line `ℝ ∙ e1` in a real vector space of dimension
`2 ^ 𝔠` is exactly `2 ^ (2 ^ 𝔠)` (Corollary 8.27(c)). -/
theorem card_retractions {K : Type} [AddCommGroup K] [Module ℝ K] {e1 : K} (he : e1 ≠ 0)
    (hrank : Module.rank ℝ K = 2 ^ #ℝ) :
    #{π : K →ₗ[ℝ] ℝ // π e1 = 1} = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ #ℝ) := by
  obtain ⟨ι, b, i0, hbi, hι⟩ : ∃ (ι : Type) (b : Module.Basis ι ℝ K) (i0 : ι),
      b i0 = e1 ∧ #ι = 2 ^ #ℝ := by
    have hs : LinearIndepOn ℝ id ({e1} : Set K) := LinearIndepOn.singleton he
    refine ⟨_, Module.Basis.extend hs, ⟨e1, hs.subset_extend _ rfl⟩,
      Module.Basis.extend_apply_self hs _, ?_⟩
    rw [(Module.Basis.extend hs).mk_eq_rank'', hrank]
  have hle : ℵ₀ ≤ #ι := by
    rw [hι, mk_real]
    exact Cardinal.aleph0_le_continuum.trans (cantor 𝔠).le
  classical
  have : Infinite ι := Cardinal.infinite_iff.2 hle
  have e : {π : K →ₗ[ℝ] ℝ // π e1 = 1} ≃ {f : ι → ℝ // f i0 = 1} :=
    Equiv.subtypeEquiv (b.constr ℝ).symm.toEquiv (fun π => by
      have key : π (b i0) = ((b.constr ℝ).symm π) i0 := by
        conv_lhs => rw [← (b.constr ℝ).apply_symm_apply π]
        exact b.constr_basis ℝ _ i0
      rw [← hbi, key]
      rfl)
  rw [Cardinal.mk_congr e]
  apply le_antisymm
  · calc #{f : ι → ℝ // f i0 = 1} ≤ #(ι → ℝ) := Cardinal.mk_subtype_le _
      _ = (𝔠 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0})) := by
        rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, mk_real, hι, mk_real]
      _ ≤ ((2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0})) ^ ((2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0})) :=
        Cardinal.power_le_power_right (cantor 𝔠).le
      _ = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0})) :=
        Cardinal.power_self_eq (Cardinal.aleph0_le_continuum.trans (cantor 𝔠).le)
      _ = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ #ℝ) := by rw [mk_real]
  · have hc : #(↥({i0}ᶜ : Set ι)) = #ι := by
      apply Cardinal.mk_compl_of_infinite
      simp only [Cardinal.mk_singleton]
      exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hle
    let F : (↥({i0}ᶜ : Set ι) → Bool) → {f : ι → ℝ // f i0 = 1} := fun g =>
      ⟨fun i => if h : i = i0 then 1 else if g ⟨i, h⟩ then 1 else 0, by simp⟩
    have hF : Function.Injective F := by
      intro g g' hgg
      funext x
      have hx : x.1 ≠ i0 := x.2
      have := congrFun (congrArg Subtype.val hgg) x.1
      simp only [F, hx, dite_false] at this
      cases hg : g x <;> cases hg' : g' x <;> simp_all
    have h1 := Cardinal.mk_le_of_injective hF
    have h2 : #(↥({i0}ᶜ : Set ι) → Bool) = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ #ℝ) := by
      rw [← Cardinal.power_def, Cardinal.mk_bool, hc, hι]
    rw [h2] at h1
    exact h1

end Card

end PVG
