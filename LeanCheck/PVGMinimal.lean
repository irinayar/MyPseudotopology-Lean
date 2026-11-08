import LeanCheck.PVGClassify
import LeanCheck.PVGSorted
import LeanCheck.PVGCharacters

/-!
# PVG: minimal Hausdorff PVGs, sequential compactness and incompatible coarsenings (Lean check)

Scope. Formal counterpart of the convergence statements of Corollary `noCoarsestPVG` (8.25), Corollary `minimalfamily` (8.27, the
parts about convergence), Proposition `lacred` (8.30) and Proposition `admref` (8.32) of `PVG_v19`, in the setting of `PVGPseudo`
and `PVGClassify` (`K = Hom(ℝ, 𝕋)`, `η_G`, density of `e(ℝ)` as the hypothesis `hdense : DenseRange e`).

* `etaConv_ker_iff`: for a real linear `π : K → ℝ` with `π (e 1) = 1`, `F → x` for `η_{ker π}` iff `π (Lr U) = x` for every ultrafilter
  `U` finer than `F`; `ultra_converges`: every ultrafilter converges to exactly one point (`(ℝ, η_{ker π})` is compact);
* `minimal_ker`: `η_{ker π}` is minimal among the Hausdorff PVGs on `ℝ` (any Hausdorff PVG coarser than it is equal to it);
* `SeqCompact G`: every real sequence has a subsequence converging for `η_G`; `seqConv_iff`: a subsequence `a ∘ φ` converges to `x`
  for `η_{ker π}` iff `π (L_a U) = x` for all free ultrafilters `U` containing `range φ`; `seqCompact_iff`, `lacred`
  (Proposition 8.30): sequential compactness of `(ℝ, η_{ker π})` is equivalent to `SC π a` for every sequence and to `SC π y` for
  every lacunary sequence `y`; `admref` (Proposition 8.32): some `η_{ker π}` is sequentially compact iff there is a choice of the sets
  `B_y` with admissible span;
* `noCoarsestPVG` (Corollary 8.25): there are two admissible subspaces such that no Hausdorff PVG on `ℝ` is coarser than both
  `η_{G₁}` and `η_{G₂}` (the example `H₀` of Proposition `coarserPVG` and the graph subspace).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-! ### Convergence for `ker π` -/

lemma etaConv_ker_iff (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) (F : Filter ℝ) (x : ℝ) :
    etaConv (LinearMap.ker π) F x ↔ ∀ U : Ultrafilter ℝ, (U : Filter ℝ) ≤ F → π (Lr U) = x := by
  constructor
  · intro h U hU
    have := h U hU
    rw [LinearMap.mem_ker, map_sub, linear_retraction_e π h1] at this
    linarith
  · intro h U hU
    rw [LinearMap.mem_ker, map_sub, linear_retraction_e π h1, h U hU, sub_self]

lemma ker_admissible (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) : IsAdmissible (LinearMap.ker π) :=
  ((ker_isCompl π h1).symm).disjoint

/-- Every ultrafilter converges for `η_{ker π}` to exactly one point. -/
theorem ultra_converges (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) (U : Ultrafilter ℝ) :
    etaConv (LinearMap.ker π) U (π (Lr U)) ∧ ∀ y, etaConv (LinearMap.ker π) U y → y = π (Lr U) := by
  constructor
  · rw [etaConv_ker_iff π h1]
    intro V hV
    have : V = U := Ultrafilter.eq_of_le hV
    rw [this]
  · intro y hy
    rw [etaConv_ker_iff π h1] at hy
    exact (hy U le_rfl).symm

/-- **Minimality of `η_{ker π}`** (Corollary 8.27(b)): a Hausdorff PVG on `ℝ` coarser than `η_{ker π}` is equal to it. -/
theorem minimal_ker (hdense : DenseRange e) (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) {conv : Filter ℝ → ℝ → Prop}
    (hp : IsPVG conv) (hH : PHausdorff conv) (hco : ∀ F x, etaConv (LinearMap.ker π) F x → conv F x) (F : Filter ℝ)
    (x : ℝ) : conv F x ↔ etaConv (LinearMap.ker π) F x := by
  have hc : ∀ F x, bohrConv F x → conv F x := fun F x hb => hco F x (bohr_coarser _ hb)
  have hcl := classify hp hH hc
  have hker : LinearMap.ker π ≤ GnullSub hp :=
    (etaConv_le_iff hdense (GnullSub hp) (LinearMap.ker π)).1 (fun F x h => (hcl F x).1 (hco F x h))
  have hadm := GnullSub_admissible hp hH hc
  have hcodis : Codisjoint (LinearMap.ker π) (ℝ ∙ e 1) := ((ker_isCompl π h1).symm).codisjoint
  have hmax := (maximal_admissible_iff (ℝ ∙ e 1) (LinearMap.ker π) (ker_admissible π h1)).2 hcodis
  have hle : GnullSub hp ≤ LinearMap.ker π := hmax _ hadm hker
  have heq : GnullSub hp = LinearMap.ker π := le_antisymm hle hker
  rw [hcl F x, heq]

/-! ### Sequential compactness -/

/-- The subsequence `a ∘ φ` converges to `x` for `η_G`. -/
def SeqConv (G : Submodule ℝ K) (a : ℕ → ℝ) (φ : ℕ → ℕ) (x : ℝ) : Prop :=
  etaConv G (Filter.map (fun k => a (φ k)) Filter.atTop) x

/-- `(ℝ, η_G)` is sequentially compact: every real sequence has a convergent subsequence. -/
def SeqCompact (G : Submodule ℝ K) : Prop :=
  ∀ a : ℕ → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℝ, SeqConv G a φ x

lemma Lr_map (g : ℕ → ℝ) (V : Ultrafilter ℕ) : Lr (Ultrafilter.map g V) = L g V := by
  apply Lr_eq_of_tendsto
  rw [Ultrafilter.coe_map, Filter.tendsto_map'_iff]
  exact tendsto_L g V

lemma free_iff_le_atTop (U : Ultrafilter ℕ) : Free U ↔ (U : Filter ℕ) ≤ Filter.atTop := by
  unfold Free
  rw [Nat.cofinite_eq_atTop]

/-- **The criterion for a subsequence to converge.** -/
theorem seqConv_iff (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) (a : ℕ → ℝ) {φ : ℕ → ℕ} (hφ : StrictMono φ) (x : ℝ) :
    SeqConv (LinearMap.ker π) a φ x ↔ ∀ U : Ultrafilter ℕ, Free U → Set.range φ ∈ U → π (L a U) = x := by
  unfold SeqConv
  rw [etaConv_ker_iff π h1]
  constructor
  · intro h U hU hr
    obtain ⟨W, hW, rfl⟩ := exists_pre_ultra hφ.injective hU hr
    have hWle : (W : Filter ℕ) ≤ Filter.atTop := (free_iff_le_atTop W).1 hW
    have hT : ((Ultrafilter.map (fun k => a (φ k)) W : Ultrafilter ℝ) : Filter ℝ) ≤
        Filter.map (fun k => a (φ k)) Filter.atTop := by
      rw [Ultrafilter.coe_map]; exact Filter.map_mono hWle
    have := h _ hT
    rw [Lr_map, L_comp a φ W] at this
    exact this
  · intro h T hT
    obtain ⟨V, hV, hVT⟩ := exists_ultra_map (fun k => a (φ k)) Filter.atTop T hT
    have hVfree : Free V := (free_iff_le_atTop V).2 hV
    have := h (Ultrafilter.map φ V) (free_map hφ.injective hVfree) (range_mem_map φ V)
    rw [← hVT, Lr_map, L_comp a φ V]
    exact this

lemma SC_iff_seq (π : K → ℝ) (a : ℕ → ℝ) :
    SC π a ↔ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℝ, ∀ U : Ultrafilter ℕ, Free U → Set.range φ ∈ U → π (L a U) = x := by
  constructor
  · rintro ⟨B, hB, x, hx⟩
    have hBS : (setOf (· ∈ B)).Infinite := hB
    refine ⟨Nat.nth (· ∈ B), Nat.nth_strictMono hBS, x, fun U hU hr => hx U hU ?_⟩
    rwa [Nat.range_nth_of_infinite hBS] at hr
  · rintro ⟨φ, hφ, x, hx⟩
    exact ⟨Set.range φ, Set.infinite_range_of_injective hφ.injective, x, hx⟩

/-- **Proposition 8.30, (a) ⇔ (b)**: sequential compactness of `(ℝ, η_{ker π})` is equivalent to the criterion `SC π a` for every
real sequence `a`. -/
theorem seqCompact_iff (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) :
    SeqCompact (LinearMap.ker π) ↔ ∀ a : ℕ → ℝ, SC π a := by
  constructor
  · intro h a
    obtain ⟨φ, hφ, x, hx⟩ := h a
    exact (SC_iff_seq π a).2 ⟨φ, hφ, x, (seqConv_iff π h1 a hφ x).1 hx⟩
  · intro h a
    obtain ⟨φ, hφ, x, hx⟩ := (SC_iff_seq π a).1 (h a)
    exact ⟨φ, hφ, x, (seqConv_iff π h1 a hφ x).2 hx⟩

/-- **Proposition 8.30** (reduction to lacunary sequences). -/
theorem lacred (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) :
    (SeqCompact (LinearMap.ker π) ↔ ∀ a : ℕ → ℝ, SC π a) ∧ ((∀ a : ℕ → ℝ, SC π a) ↔ ∀ y ∈ Lac, SC π y) :=
  ⟨seqCompact_iff π h1, R1_linear π h1⟩

/-- **Proposition 8.32** (reformulation by admissibility). -/
theorem admref :
    (∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ SeqCompact (LinearMap.ker π)) ↔
    ∃ Bsel : (ℕ → ℝ) → Set ℕ, (∀ y ∈ Lac, (Bsel y).Infinite) ∧
      Disjoint (Submodule.span ℝ {v : K | ∃ y ∈ Lac, ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧
        Bsel y ∈ U ∧ Bsel y ∈ V ∧ v = L y U - L y V}) (ℝ ∙ e 1) := by
  rw [← R1_R4]
  constructor
  · rintro ⟨π, h1, h⟩
    exact ⟨π, h1, (seqCompact_iff π h1).1 h⟩
  · rintro ⟨π, h1, h⟩
    exact ⟨π, h1, (seqCompact_iff π h1).2 h⟩

/-! ### Incompatible coarsenings (Corollary 8.25) -/

/-- The character `χ_a (b) = f (a b) mod 1` for an additive `f : ℝ → ℚ`. -/
noncomputable def chi (f : ℝ →+ ℚ) (a : ℝ) : K :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →+ ℝ).comp (f.comp (AddMonoidHom.mulLeft a)))

lemma chi_apply (f : ℝ →+ ℚ) (a b : ℝ) : chi f a b = (((f (a * b) : ℚ) : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- `a ↦ χ_a` is real linear. -/
noncomputable def chiLin (f : ℝ →+ ℚ) : ℝ →ₗ[ℝ] K where
  toFun := chi f
  map_add' a a' := by ext b; simp [chi_apply, add_mul]
  map_smul' c a := by
    ext b
    simp only [chi_apply, smul_apply, smul_eq_mul, RingHom.id_apply]
    congr 2
    ring_nf

lemma chiLin_ne (f : ℝ →+ ℚ) (hf : f ≠ 0) (a : ℝ) (h : chiLin f a ∈ ℝ ∙ e 1) : a = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have hce : chi f a = e c := by
    have : (c • e 1 : K) = e c := (e_eq_smul c).symm
    rw [← this]; exact hc.symm
  have hint : ∀ b : ℝ, ∃ n : ℤ, ((f (a * b) : ℚ) : ℝ) - c * b = n := by
    intro b
    have h1 := congrArg (fun κ : K => κ b) hce
    simp only [chi_apply, e_apply] at h1
    have h2 := (QuotientAddGroup.eq).1 h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨-k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    push_cast
    linarith
  exact (trivial_intersection f hf a c hint).2

lemma exists_nonzero_hom : ∃ f : ℝ →+ ℚ, f ≠ 0 := by
  let b := Module.Basis.ofVectorSpace ℚ ℝ
  obtain ⟨i⟩ := b.index_nonempty
  refine ⟨(b.coord i).toAddMonoidHom, fun h => ?_⟩
  have := congrArg (fun g : ℝ →+ ℚ => g (b i)) h
  simp at this

/-- **Corollary 8.25.** There are two admissible subspaces such that no Hausdorff PVG on `ℝ` is coarser than both `η_{G₁}` and `η_{G₂}`;
in particular there is no coarsest Hausdorff PVG on `ℝ`. -/
theorem noCoarsestPVG (hdense : DenseRange e) :
    ∃ G₁ G₂ : Submodule ℝ K, IsAdmissible G₁ ∧ IsAdmissible G₂ ∧
      ∀ conv : Filter ℝ → ℝ → Prop, IsPVG conv → PHausdorff conv → (∀ F x, etaConv G₁ F x → conv F x) →
        (∀ F x, etaConv G₂ F x → conv F x) → False := by
  obtain ⟨f, hf⟩ := exists_nonzero_hom
  have hφ := chiLin_ne f hf
  have hnc := no_common_admissible (e 1) e_one_ne_zero (chiLin f) hφ
  refine ⟨LinearMap.range (chiLin f),
    LinearMap.range (LinearMap.toSpanSingleton ℝ K (e 1) + chiLin f), ?_, hnc.1, ?_⟩
  · rw [IsAdmissible, Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ hL
    have := hφ a hL
    subst this
    simp
  · intro conv hp hH h1 h2
    have hc : ∀ F x, bohrConv F x → conv F x := fun F x hb => h1 F x (bohr_coarser _ hb)
    have hcl := classify hp hH hc
    have hG1 : LinearMap.range (chiLin f) ≤ GnullSub hp :=
      (etaConv_le_iff hdense (GnullSub hp) _).1 (fun F x h => (hcl F x).1 (h1 F x h))
    have hG2 : LinearMap.range (LinearMap.toSpanSingleton ℝ K (e 1) + chiLin f) ≤ GnullSub hp :=
      (etaConv_le_iff hdense (GnullSub hp) _).1 (fun F x h => (hcl F x).1 (h2 F x h))
    exact hnc.2 (GnullSub hp) hG1 hG2 (GnullSub_admissible hp hH hc)

#print axioms etaConv_ker_iff
#print axioms ultra_converges
#print axioms minimal_ker
#print axioms seqConv_iff
#print axioms lacred
#print axioms admref
#print axioms noCoarsestPVG

end Q95
end PVG
