import LeanCheck.PVGSequences

/-!
# PVG: pseudotopologies, PVGs and the convergence `η_G` (Lean check)

Scope. First module of the formalization of the convergence statements of Section 8 of `PVG_v19`
(Proposition `coarserPVG`, Theorem `classifyPVG`, ...). Concrete setting as in `PVGSequences`: `K = Hom(ℝ, 𝕋)`, `e`,
the real vector space structure of `K`.

* `IsPseudoTop conv`, `PHausdorff conv`, `IsPVG conv` (Definitions 2.1 to 2.3 of the article, with the addition axiom in the form
  `F → x`, `G → y` implies `F + G → x + y` of Lemma 2.4): a convergence relation between filters on a set `X` (on a real vector
  space for `IsPVG`) and points;
* `Lr U`: the Bohr limit of an ultrafilter `U` on `ℝ` (the limit of `e` along `U` in the compact group `K`);
* `etaConv G`: the convergence `η_G`: `F → x` iff `Lr U - e x ∈ G` for every ultrafilter `U` finer than `F`;
* `exists_ultra_map`: an ultrafilter finer than the image filter `f(F)` is the image of an ultrafilter finer than `F`;
* `lr_add_decomp`: an ultrafilter finer than `F + G` has Bohr limit `Lr U + Lr V` for ultrafilters `U ≤ F`, `V ≤ G` (compactness of `K`);
* `etaConv_isPVG`: for an admissible subspace `G` (`Disjoint G (ℝ e(1))`, i.e. `G ∩ e(ℝ) = {0}`), `η_G` is a Hausdorff PVG on `ℝ`
  coarser than the Bohr topology (`bohrConv`): the general form of Proposition `coarserPVG`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-! ### Pseudotopologies and PVGs -/

/-- A pseudotopology on `X`: a convergence relation between filters and points with (P1), (P2), (P3). -/
structure IsPseudoTop {X : Type*} (conv : Filter X → X → Prop) : Prop where
  p1 : ∀ x, conv (pure x) x
  p2 : ∀ {F G : Filter X} {x : X}, conv F x → G ≤ F → conv G x
  p3 : ∀ (F : Filter X) [F.NeBot] (x : X), (∀ U : Ultrafilter X, (U : Filter X) ≤ F → conv U x) → conv F x

/-- No (nonempty) filter converges to two different points. -/
def PHausdorff {X : Type*} (conv : Filter X → X → Prop) : Prop :=
  ∀ (F : Filter X) [F.NeBot] (x y : X), conv F x → conv F y → x = y

/-- A pseudotopological vector group: a pseudotopology on a real vector space with continuous addition (in the form of Lemma 2.4)
and continuous dilations. -/
structure IsPVG {X : Type*} [AddCommGroup X] [Module ℝ X] (conv : Filter X → X → Prop) : Prop extends IsPseudoTop conv where
  add : ∀ {F G : Filter X} {x y : X}, conv F x → conv G y → conv (Filter.map₂ (· + ·) F G) (x + y)
  smul : ∀ (a : ℝ) {F : Filter X} {x : X}, conv F x → conv (F.map (fun z => a • z)) (a • x)

/-- Convergence in the Bohr topology: the topology induced by `e : ℝ → K`. -/
def bohrConv (F : Filter ℝ) (x : ℝ) : Prop := Tendsto e F (𝓝 (e x))

/-! ### Bohr limits of ultrafilters on `ℝ` -/

/-- `Lr U = lim_U e`. -/
noncomputable def Lr (U : Ultrafilter ℝ) : K := (Ultrafilter.map e U).lim

lemma tendsto_Lr (U : Ultrafilter ℝ) : Tendsto e U (𝓝 (Lr U)) := by
  have h := Ultrafilter.le_nhds_lim (Ultrafilter.map e U)
  rw [Ultrafilter.coe_map] at h
  exact h

lemma Lr_eq_of_tendsto {U : Ultrafilter ℝ} {κ : K} (h : Tendsto e U (𝓝 κ)) : Lr U = κ :=
  tendsto_nhds_unique (tendsto_Lr U) h

lemma Lr_pure (x : ℝ) : Lr (pure x) = e x := by
  apply Lr_eq_of_tendsto
  rw [Ultrafilter.coe_pure]
  exact tendsto_pure_nhds e x

lemma e_injective' : Function.Injective e := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h0 : e (x - y) = 0 := by
    have : e (x - y) + e y = e y := by rw [← e_add]; simp [hxy]
    have h2 : e (x - y) = 0 := by simpa using this
    exact h2
  have h1 := congrArg (fun κ : K => κ (1 / (2 * (x - y)))) h0
  simp only [e_apply, AddMonoidHom.zero_apply] at h1
  have : ((1 / (2 * (x - y)) * (x - y) : ℝ) : AddCircle (1 : ℝ)) = 0 := h1
  have h3 : (1 / (2 * (x - y)) * (x - y) : ℝ) = 1 / 2 := by field_simp
  rw [h3] at this
  have h4 := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 this
  obtain ⟨n, hn⟩ := h4
  have : (n : ℝ) = 1 / 2 := by simpa using hn
  have h5 : (2 : ℝ) * n = 1 := by linarith
  have h6 : (2 : ℤ) * n = 1 := by exact_mod_cast h5
  omega

/-! ### Image ultrafilters -/

/-- An ultrafilter finer than the image filter `f(F)` is the image of an ultrafilter finer than `F`. -/
lemma exists_ultra_map {α β : Type*} (f : α → β) (F : Filter α) (W : Ultrafilter β) (h : (W : Filter β) ≤ F.map f) :
    ∃ V : Ultrafilter α, (V : Filter α) ≤ F ∧ Ultrafilter.map f V = W := by
  have hne : (F ⊓ Filter.comap f W).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨B, hB, hBt⟩ := Filter.mem_comap.1 ht
    have h1 : f '' s ∈ (W : Filter β) := h (Filter.image_mem_map hs)
    obtain ⟨y, hy1, hy2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 hB)
    obtain ⟨a, ha, rfl⟩ := hy1
    exact ⟨a, ha, hBt hy2⟩
  refine ⟨Ultrafilter.of (F ⊓ Filter.comap f W), (Ultrafilter.of_le _).trans inf_le_left, ?_⟩
  apply Ultrafilter.eq_of_le
  have h2 : (Ultrafilter.of (F ⊓ Filter.comap f W) : Filter α) ≤ Filter.comap f W :=
    (Ultrafilter.of_le _).trans inf_le_right
  rw [Ultrafilter.coe_map]
  exact Filter.map_le_iff_le_comap.2 h2

/-- An ultrafilter finer than `F + G` has Bohr limit `Lr U + Lr V` with `U ≤ F`, `V ≤ G` ultrafilters. -/
lemma lr_add_decomp (F G : Filter ℝ) (W : Ultrafilter ℝ) (h : (W : Filter ℝ) ≤ Filter.map₂ (· + ·) F G) :
    ∃ U V : Ultrafilter ℝ, (U : Filter ℝ) ≤ F ∧ (V : Filter ℝ) ≤ G ∧ Lr W = Lr U + Lr V := by
  have h' : (W : Filter ℝ) ≤ (F ×ˢ G).map ((fun p : ℝ × ℝ => p.1 + p.2)) := by
    rw [Filter.map_prod_eq_map₂ (fun x y : ℝ => x + y)]; exact h
  obtain ⟨V', hV'le, hV'W⟩ := exists_ultra_map _ _ W h'
  refine ⟨Ultrafilter.map Prod.fst V', Ultrafilter.map Prod.snd V', ?_, ?_, ?_⟩
  · rw [Ultrafilter.coe_map]
    exact (Filter.map_mono hV'le).trans Filter.tendsto_fst
  · rw [Ultrafilter.coe_map]
    exact (Filter.map_mono hV'le).trans Filter.tendsto_snd
  · apply Lr_eq_of_tendsto
    rw [← hV'W, Ultrafilter.coe_map]
    have h1 : Tendsto (fun p : ℝ × ℝ => e p.1) V' (𝓝 (Lr (Ultrafilter.map Prod.fst V'))) := by
      have := tendsto_Lr (Ultrafilter.map Prod.fst V')
      rw [Ultrafilter.coe_map] at this
      exact this
    have h2 : Tendsto (fun p : ℝ × ℝ => e p.2) V' (𝓝 (Lr (Ultrafilter.map Prod.snd V'))) := by
      have := tendsto_Lr (Ultrafilter.map Prod.snd V')
      rw [Ultrafilter.coe_map] at this
      exact this
    have h3 := h1.add h2
    rw [Filter.tendsto_map'_iff]
    refine h3.congr (fun p => ?_)
    simp [e_add]

lemma e_zero : e 0 = 0 := by ext b; simp

lemma e_sub (x y : ℝ) : e (x - y) = e x - e y := by
  have : e x = e (x - y) + e y := by rw [← e_add]; simp
  rw [this]; abel

/-! ### The convergence `η_G` -/

/-- An admissible subspace: `G ∩ e(ℝ) = {0}`. -/
def IsAdmissible (G : Submodule ℝ K) : Prop := Disjoint G (ℝ ∙ e 1)

/-- The convergence `η_G`: `F → x` iff `Lr U - e x ∈ G` for every ultrafilter `U` finer than `F`. -/
def etaConv (G : Submodule ℝ K) (F : Filter ℝ) (x : ℝ) : Prop :=
  ∀ U : Ultrafilter ℝ, (U : Filter ℝ) ≤ F → Lr U - e x ∈ G

lemma etaConv_pseudo (G : Submodule ℝ K) : IsPseudoTop (etaConv G) where
  p1 x := by
    intro U hU
    have h0 : (U : Filter ℝ) = pure x := (Filter.NeBot.le_pure_iff (inferInstance : (U : Filter ℝ).NeBot)).1 hU
    have h : U = pure x := Ultrafilter.coe_injective (by rw [Ultrafilter.coe_pure]; exact h0)
    rw [h, Lr_pure, sub_self]
    exact G.zero_mem
  p2 := fun h hGF U hU => h U (hU.trans hGF)
  p3 := fun F _ x h U hU => h U hU U le_rfl

lemma etaConv_isPVG (G : Submodule ℝ K) : IsPVG (etaConv G) where
  toIsPseudoTop := etaConv_pseudo G
  add := by
    intro F G' x y hF hG' W hW
    obtain ⟨U, V, hU, hV, hWUV⟩ := lr_add_decomp F G' W hW
    have h1 := hF U hU
    have h2 := hG' V hV
    have : Lr W - e (x + y) = (Lr U - e x) + (Lr V - e y) := by rw [hWUV, e_add]; abel
    rw [this]
    exact G.add_mem h1 h2
  smul := by
    intro a F x hF W hW
    obtain ⟨U, hU, hUW⟩ := exists_ultra_map (fun z => a • z) F W hW
    have hLr : Lr W = a • Lr U := by
      apply Lr_eq_of_tendsto
      rw [← hUW, Ultrafilter.coe_map, Filter.tendsto_map'_iff]
      have h := ((continuous_smul_const a).tendsto (Lr U)).comp (tendsto_Lr U)
      refine h.congr (fun z => ?_)
      simp only [Function.comp, smul_eq_mul]
      rw [smul_e]
    have : Lr W - e (a • x) = a • (Lr U - e x) := by
      rw [hLr, smul_sub, smul_eq_mul, smul_e]
    rw [this]
    exact G.smul_mem a (hF U hU)

lemma etaConv_hausdorff {G : Submodule ℝ K} (hG : IsAdmissible G) : PHausdorff (etaConv G) := by
  intro F _ x y hx hy
  have hU := Ultrafilter.of_le F
  have h1 := hx _ hU
  have h2 := hy _ hU
  have h3 : e (y - x) ∈ G := by
    have : e (y - x) = (Lr (Ultrafilter.of F) - e x) - (Lr (Ultrafilter.of F) - e y) := by
      rw [e_sub]; abel
    rw [this]
    exact G.sub_mem h1 h2
  have h4 : e (y - x) ∈ ℝ ∙ e 1 :=
    Submodule.mem_span_singleton.2 ⟨y - x, by rw [e_eq_smul (y - x)]⟩
  have h5 : e (y - x) = 0 := Submodule.disjoint_def.1 hG _ h3 h4
  have h6 : y - x = 0 := e_injective' (h5.trans e_zero.symm)
  linarith

/-- Every filter converging in the Bohr topology converges for `η_G`. -/
lemma bohr_coarser (G : Submodule ℝ K) {F : Filter ℝ} {x : ℝ} (h : bohrConv F x) : etaConv G F x := by
  intro U hU
  have : Lr U = e x := Lr_eq_of_tendsto (h.mono_left hU)
  rw [this, sub_self]
  exact G.zero_mem

/-- **Proposition `coarserPVG`, general form.** For an admissible subspace `G`, `η_G` is a Hausdorff PVG on `ℝ` coarser than the
Bohr topology. -/
theorem etaConv_pvg {G : Submodule ℝ K} (hG : IsAdmissible G) :
    IsPVG (etaConv G) ∧ PHausdorff (etaConv G) ∧ ∀ (F : Filter ℝ) (x : ℝ), bohrConv F x → etaConv G F x :=
  ⟨etaConv_isPVG G, etaConv_hausdorff hG, fun _ _ h => bohr_coarser G h⟩

#print axioms exists_ultra_map
#print axioms lr_add_decomp
#print axioms etaConv_pvg

end Q95
end PVG
