import LeanCheck.PVGPseudo

/-!
# PVG: the classification below the Bohr topology (Lean check)

Scope. Formal counterpart of Theorem `classifyPVG` (Theorem 8.23) of `PVG_v19`, in the setting of `PVGPseudo`: the Hausdorff PVG
pseudotopologies on `ℝ` coarser than the Bohr topology are exactly the convergences `η_G` for admissible subspaces `G` of `K`,
`G` is unique and `η_G` is coarser than `η_{G'}` exactly when `G' ⊆ G`.

The article uses that `e(ℝ)` is dense in `K` (`K` is the Bohr compactification of `ℝ`, a fact it cites); here it is the hypothesis
`hdense : DenseRange e`, used only for the uniqueness of `G` and the order reversal.

* `Gnull conv`: the real subspace of `K` of the Bohr limits of the `conv`-null ultrafilters (a submodule by the continuity of addition
  and of dilations; `lr_add_decomp`); it is admissible when `conv` is Hausdorff and coarser than the Bohr topology;
* `classify`: `conv F x ↔ etaConv (Gnull conv) F x` for every filter `F` and point `x`;
* `etaConv_inj`, `etaConv_le_iff`: uniqueness of `G` and the order reversal (with `hdense`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

instance : ContinuousNeg K := ⟨(continuous_smul_const (-1 : ℝ)).congr (fun κ => neg_one_smul ℝ κ)⟩

instance : IsTopologicalAddGroup K := {}

lemma Lr_translate (U : Ultrafilter ℝ) (c : ℝ) : Lr (Ultrafilter.map (fun a => a + c) U) = Lr U + e c := by
  apply Lr_eq_of_tendsto
  rw [Ultrafilter.coe_map, Filter.tendsto_map'_iff]
  have h := (tendsto_Lr U).add_const (e c)
  refine h.congr (fun a => ?_)
  simp [e_add]

lemma Lr_smul (a : ℝ) (U : Ultrafilter ℝ) : Lr (Ultrafilter.map (fun z => a • z) U) = a • Lr U := by
  apply Lr_eq_of_tendsto
  rw [Ultrafilter.coe_map, Filter.tendsto_map'_iff]
  have h := ((continuous_smul_const a).tendsto (Lr U)).comp (tendsto_Lr U)
  refine h.congr (fun z => ?_)
  simp only [Function.comp, smul_eq_mul]
  rw [smul_e]

/-- The Bohr limits of the `conv`-null ultrafilters. -/
def Gnull (conv : Filter ℝ → ℝ → Prop) : Set K := {κ | ∃ U : Ultrafilter ℝ, conv U 0 ∧ Lr U = κ}

/-- `Gnull` is a real subspace of `K`. -/
def GnullSub {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) : Submodule ℝ K where
  carrier := Gnull conv
  zero_mem' := ⟨pure 0, by simpa using h.p1 0, by rw [Lr_pure, e_zero]⟩
  add_mem' := by
    rintro _ _ ⟨U₁, hU₁, rfl⟩ ⟨U₂, hU₂, rfl⟩
    have hne : (Filter.map₂ (· + ·) (U₁ : Filter ℝ) (U₂ : Filter ℝ)).NeBot := Filter.NeBot.map₂ inferInstance inferInstance
    set W := Ultrafilter.of (Filter.map₂ (· + ·) (U₁ : Filter ℝ) (U₂ : Filter ℝ)) with hW
    have hWle : (W : Filter ℝ) ≤ Filter.map₂ (· + ·) (U₁ : Filter ℝ) (U₂ : Filter ℝ) := Ultrafilter.of_le _
    refine ⟨W, ?_, ?_⟩
    · have := h.p2 (h.add hU₁ hU₂) hWle
      simpa using this
    · obtain ⟨U, V, hU, hV, hLr⟩ := lr_add_decomp _ _ W hWle
      have h1 : U = U₁ := Ultrafilter.eq_of_le hU
      have h2 : V = U₂ := Ultrafilter.eq_of_le hV
      rw [hLr, h1, h2]
  smul_mem' := by
    rintro a _ ⟨U, hU, rfl⟩
    refine ⟨Ultrafilter.map (fun z => a • z) U, ?_, Lr_smul a U⟩
    have := h.smul a hU
    rw [Ultrafilter.coe_map]
    simpa using this

lemma mem_GnullSub {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) {κ : K} :
    κ ∈ GnullSub h ↔ ∃ U : Ultrafilter ℝ, conv U 0 ∧ Lr U = κ := Iff.rfl

/-- `Gnull` is admissible for a Hausdorff PVG coarser than the Bohr topology. -/
lemma GnullSub_admissible {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) (hH : PHausdorff conv)
    (hc : ∀ F x, bohrConv F x → conv F x) : IsAdmissible (GnullSub h) := by
  rw [IsAdmissible, Submodule.disjoint_def]
  intro κ hκ hκ1
  obtain ⟨U, hU0, rfl⟩ := hκ
  obtain ⟨c, hcκ⟩ := Submodule.mem_span_singleton.1 hκ1
  have hLr : Lr U = e c := by rw [← hcκ, e_eq_smul c]
  have hb : bohrConv U c := by
    unfold bohrConv
    rw [← hLr]; exact tendsto_Lr U
  have hcU := hc _ _ hb
  have : c = 0 := hH (U : Filter ℝ) c 0 hcU hU0
  rw [hLr, this, e_zero]

/-- A filter `T` with `T` finer than `(T - V) + V` for an ultrafilter pair with the same Bohr limit. -/
lemma conv_of_same_lr {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) (hc : ∀ F x, bohrConv F x → conv F x)
    (T V : Ultrafilter ℝ) (hLr : Lr T = Lr V) (hV : conv V 0) : conv T 0 := by
  set A : Filter ℝ := Filter.map₂ (fun a b => a - b) (T : Filter ℝ) (V : Filter ℝ) with hA
  have hAb : bohrConv A 0 := by
    unfold bohrConv
    rw [hA, ← Filter.map_prod_eq_map₂ (fun a b : ℝ => a - b)]
    rw [Filter.tendsto_map'_iff]
    have h1 : Tendsto (fun p : ℝ × ℝ => e p.1) ((T : Filter ℝ) ×ˢ (V : Filter ℝ)) (𝓝 (Lr T)) :=
      (tendsto_Lr T).comp Filter.tendsto_fst
    have h2 : Tendsto (fun p : ℝ × ℝ => e p.2) ((T : Filter ℝ) ×ˢ (V : Filter ℝ)) (𝓝 (Lr V)) :=
      (tendsto_Lr V).comp Filter.tendsto_snd
    have h3 := h1.sub h2
    rw [hLr, sub_self, ← e_zero] at h3
    refine h3.congr (fun p => ?_)
    simp [e_sub, e_zero]
  have hA0 : conv A 0 := hc _ _ hAb
  have hsum : conv (Filter.map₂ (· + ·) A (V : Filter ℝ)) (0 + 0) := h.add hA0 hV
  have hle : (T : Filter ℝ) ≤ Filter.map₂ (· + ·) A (V : Filter ℝ) := by
    intro S hS
    obtain ⟨X, hX, Y, hY, hXY⟩ := Filter.mem_map₂_iff.1 hS
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Filter.mem_map₂_iff.1 hX
    refine Filter.mem_of_superset hP (fun a ha => ?_)
    obtain ⟨b, hbQ, hbY⟩ := Filter.nonempty_of_mem (Filter.inter_mem hQ hY)
    have h1 : a - b ∈ X := hPQ ⟨a, ha, b, hbQ, rfl⟩
    have h2 : (a - b) + b ∈ S := hXY ⟨a - b, h1, b, hbY, rfl⟩
    simpa using h2
  have := h.p2 hsum hle
  simpa using this

/-- **Theorem `classifyPVG`**: a Hausdorff PVG on `ℝ` coarser than the Bohr topology is `η_G` for `G = Gnull`. -/
theorem classify {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) (hH : PHausdorff conv)
    (hc : ∀ F x, bohrConv F x → conv F x) (F : Filter ℝ) (x : ℝ) :
    conv F x ↔ etaConv (GnullSub h) F x := by
  constructor
  · intro hF U hU
    have hUx : conv U x := h.p2 hF hU
    have h1 : conv (Filter.map₂ (· + ·) (U : Filter ℝ) (pure (-x))) (x + -x) := h.add hUx (h.p1 (-x))
    rw [Filter.map₂_pure_right] at h1
    rw [add_neg_cancel] at h1
    refine ⟨Ultrafilter.map (fun a => a + -x) U, ?_, ?_⟩
    · rw [Ultrafilter.coe_map]; exact h1
    · rw [Lr_translate, show e (-x) = - e x by rw [← zero_sub, e_sub, e_zero, zero_sub]]; abel
  · intro hF
    by_cases hbot : F.NeBot
    · refine h.p3 F x (fun U hU => ?_)
      obtain ⟨V, hV0, hVLr⟩ := hF U hU
      set T : Ultrafilter ℝ := Ultrafilter.map (fun a => a + -x) U with hT
      have hTLr : Lr T = Lr V := by
        rw [hT, Lr_translate, hVLr, show e (-x) = - e x by rw [← zero_sub, e_sub, e_zero, zero_sub]]; abel
      have hT0 : conv T 0 := conv_of_same_lr h hc T V hTLr hV0
      have h1 : conv (Filter.map₂ (· + ·) (T : Filter ℝ) (pure x)) (0 + x) := h.add hT0 (h.p1 x)
      rw [Filter.map₂_pure_right, zero_add] at h1
      have h2 : (U : Filter ℝ) ≤ Filter.map (fun a => a + x) (T : Filter ℝ) := by
        rw [hT, Ultrafilter.coe_map, Filter.map_map]
        have : ((fun a : ℝ => a + x) ∘ fun a => a + -x) = id := by funext a; simp
        rw [this, Filter.map_id]
      exact h.p2 h1 h2
    · have hb : F = ⊥ := by simpa using hbot
      subst hb
      exact h.p2 (h.p1 x) bot_le

/-! ### Uniqueness of `G` and order reversal (with the density of `e(ℝ)`) -/

lemma exists_ultra_lr (hdense : DenseRange e) (κ : K) : ∃ U : Ultrafilter ℝ, Lr U = κ := by
  have hne : (Filter.comap e (𝓝 κ)).NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, ht1, ⟨a, rfl⟩⟩ := mem_closure_iff_nhds.1 (hdense.closure_eq ▸ Set.mem_univ κ) t ht
    exact ⟨a, ht1⟩
  refine ⟨Ultrafilter.of (Filter.comap e (𝓝 κ)), Lr_eq_of_tendsto ?_⟩
  exact Filter.tendsto_iff_comap.2 (Ultrafilter.of_le _)

lemma etaConv_ultra_zero (G : Submodule ℝ K) (U : Ultrafilter ℝ) : etaConv G U 0 ↔ Lr U ∈ G := by
  constructor
  · intro h
    have := h U le_rfl
    simpa [e_zero] using this
  · intro h V hV
    have : V = U := Ultrafilter.eq_of_le hV
    subst this
    simpa [e_zero] using h

/-- `η_{G'}` is coarser than `η_G` exactly when `G ≤ G'`... in the direction used: `η_{G'}`-convergence implies `η_G`-convergence
for all filters iff `G' ≤ G`. -/
theorem etaConv_le_iff (hdense : DenseRange e) (G G' : Submodule ℝ K) :
    (∀ (F : Filter ℝ) (x : ℝ), etaConv G' F x → etaConv G F x) ↔ G' ≤ G := by
  constructor
  · intro h κ hκ
    obtain ⟨U, rfl⟩ := exists_ultra_lr hdense κ
    exact (etaConv_ultra_zero G U).1 (h _ _ ((etaConv_ultra_zero G' U).2 hκ))
  · intro hle F x hF U hU
    exact hle (hF U hU)

/-- **Uniqueness of `G`.** -/
theorem etaConv_inj (hdense : DenseRange e) (G G' : Submodule ℝ K)
    (h : ∀ (F : Filter ℝ) (x : ℝ), etaConv G F x ↔ etaConv G' F x) : G = G' := by
  apply le_antisymm
  · exact (etaConv_le_iff hdense G' G).1 (fun F x => (h F x).1)
  · exact (etaConv_le_iff hdense G G').1 (fun F x => (h F x).2)

/-- **Theorem `classifyPVG` in one statement.** -/
theorem classifyPVG (hdense : DenseRange e) {conv : Filter ℝ → ℝ → Prop} (h : IsPVG conv) (hH : PHausdorff conv)
    (hc : ∀ F x, bohrConv F x → conv F x) :
    ∃! G : Submodule ℝ K, IsAdmissible G ∧ ∀ F x, conv F x ↔ etaConv G F x := by
  refine ⟨GnullSub h, ⟨GnullSub_admissible h hH hc, classify h hH hc⟩, ?_⟩
  rintro G' ⟨_, hG'⟩
  exact etaConv_inj hdense G' (GnullSub h) (fun F x => (hG' F x).symm.trans (classify h hH hc F x))

#print axioms classify
#print axioms etaConv_le_iff
#print axioms classifyPVG

end Q95
end PVG
