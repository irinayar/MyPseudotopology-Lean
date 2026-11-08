import LeanCheck.PVGCard
import LeanCheck.PVGNull

/-!
# PVG: non-Fréchet–Urysohn examples below the Bohr topology (Lean check)

Scope. Formal counterpart of the parts of Corollary 8.29 (`nonzeroG`) of `PVG_v19` that do not use the cited minimality of the Bohr
topology: `η_G` is a Hausdorff PVG coarser than the Euclidean convergence; nonzero admissible subspaces exist; and `η_G` is not
Fréchet–Urysohn when `0 < dim_ℝ G < 2^𝔠`.

* `IsFU conv`: a convergence relation is Fréchet–Urysohn if every point of the `conv`-closure of a set is the limit of a sequence
  in the set (the closure of `A` is the set of limits of filters containing `A`);
* `euclid_coarser`: every filter converging in the Euclidean topology converges for `η_G`;
* `exists_nonzero_admissible`: the subspace `H₀ = {χ_a}` of Proposition 8.18 (`chiLin`) is nonzero and admissible;
* `not_FU` (the last assertion of Corollary 8.29, with the density `hdense : DenseRange e` of `e(ℝ)` in `K`): for an admissible `G` with
  `0 < dim_ℝ G < 2^𝔠`, `η_G` is not Fréchet–Urysohn (a closed neighbourhood `N` of a nonzero `g₀ ∈ G` not containing `0`, `A = e⁻¹(N)`,
  Proposition 8.28).

Not formalized: the statements that `η_G` is not pretopological for `G ≠ 0` (they use Corollary 8.24 and the cited minimality of the
Bohr topology).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Cardinal

namespace PVG
namespace Q95

/-- Fréchet–Urysohn: every point of the closure of a set (the limits of filters containing the set) is the limit of a sequence in
the set. -/
def IsFU {X : Type*} (conv : Filter X → X → Prop) : Prop :=
  ∀ (A : Set X) (x : X), (∃ F : Filter X, F.NeBot ∧ A ∈ F ∧ conv F x) →
    ∃ a : ℕ → X, (∀ n, a n ∈ A) ∧ conv (Filter.map a Filter.atTop) x

/-- Every Euclidean convergent filter converges for `η_G`. -/
lemma euclid_coarser (G : Submodule ℝ K) {F : Filter ℝ} {x : ℝ} (h : F ≤ 𝓝 x) : etaConv G F x :=
  bohr_coarser G (by unfold bohrConv; exact (continuous_e.tendsto x).comp h)

/-- The subspace `H₀` is nonzero and admissible. -/
theorem exists_nonzero_admissible : ∃ G : Submodule ℝ K, IsAdmissible G ∧ G ≠ ⊥ := by
  obtain ⟨f, hf⟩ := exists_nonzero_hom
  have hφ := chiLin_ne f hf
  refine ⟨LinearMap.range (chiLin f), ?_, ?_⟩
  · rw [IsAdmissible, Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ hL
    have := hφ a hL
    subst this
    simp
  · intro hbot
    obtain ⟨b, hb⟩ : ∃ b, f b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf (AddMonoidHom.ext hcon)
    set q : ℚ := f b with hq
    have hq0 : q ≠ 0 := hb
    let fl : ℝ →ₗ[ℚ] ℚ := AddMonoidHom.toRatLinearMap f
    set r : ℚ := 1 / (2 * q) with hr
    have hfa : f ((r : ℝ) * b) = 1 / 2 := by
      have : fl ((r : ℚ) • b) = r • fl b := map_smul fl r b
      have h2 : (r : ℚ) • b = (r : ℝ) * b := by rw [Rat.smul_def]
      have h3 : fl ((r : ℚ) • b) = f ((r : ℝ) * b) := by rw [h2]; rfl
      rw [← h3, this]
      simp only [smul_eq_mul, hr]
      have : fl b = q := rfl
      rw [this]; field_simp
    have hmem : chiLin f ((r : ℝ) * b) ∈ (⊥ : Submodule ℝ K) := by
      rw [← hbot]; exact ⟨_, rfl⟩
    have h0 : chiLin f ((r : ℝ) * b) = 0 := (Submodule.mem_bot ℝ).1 hmem
    have h1 := congrArg (fun κ : K => κ 1) h0
    simp only [chiLin, LinearMap.coe_mk, AddHom.coe_mk, chi_apply, mul_one, AddMonoidHom.zero_apply] at h1
    rw [hfa] at h1
    have h2 : (((1 / 2 : ℚ) : ℝ) : AddCircle (1 : ℝ)) = 0 := h1
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    have h3 : (n : ℝ) = 1 / 2 := by simpa using hn
    have h4 : (2 : ℝ) * n = 1 := by linarith
    have h5 : (2 : ℤ) * n = 1 := by exact_mod_cast h4
    omega

/-- **Corollary 8.29, last assertion.** If `G` is admissible with `0 < dim_ℝ G < 2^𝔠`, then `η_G` is not Fréchet–Urysohn. -/
theorem not_FU (hdense : DenseRange e) (G : Submodule ℝ K) (hG : IsAdmissible G) (hne : G ≠ ⊥)
    (hdim : Module.rank ℝ G < 2 ^ #ℝ) : ¬ IsFU (etaConv G) := by
  intro hFU
  obtain ⟨g0, hg0G, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  -- a closed neighbourhood `N` of `g0` that does not contain `0`
  have hopen : IsOpen ({(0 : K)}ᶜ : Set K) := isOpen_compl_singleton
  have hg0mem : g0 ∈ ({(0 : K)}ᶜ : Set K) := hg0
  obtain ⟨N, hNnhds, hNclosed, hNsub⟩ := exists_mem_nhds_isClosed_subset (hopen.mem_nhds hg0mem)
  have h0N : (0 : K) ∉ N := fun h => hNsub h rfl
  set A : Set ℝ := e ⁻¹' N with hA
  -- `0` is in the closure of `A`
  have hne1 : (Filter.comap e (𝓝 g0)).NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, ht1, ⟨a, rfl⟩⟩ := mem_closure_iff_nhds.1 (hdense.closure_eq ▸ Set.mem_univ g0) t ht
    exact ⟨a, ht1⟩
  set U : Ultrafilter ℝ := Ultrafilter.of (Filter.comap e (𝓝 g0)) with hU
  have hUle : (U : Filter ℝ) ≤ Filter.comap e (𝓝 g0) := Ultrafilter.of_le _
  have hLr : Lr U = g0 := Lr_eq_of_tendsto (Filter.tendsto_iff_comap.2 hUle)
  have hAU : A ∈ (U : Filter ℝ) := by
    have : e ⁻¹' N ∈ Filter.comap e (𝓝 g0) := Filter.preimage_mem_comap hNnhds
    exact hUle this
  have hconv : etaConv G (U : Filter ℝ) 0 := by
    intro V hV
    have : V = U := Ultrafilter.eq_of_le hV
    subst this
    rw [hLr, e_zero, sub_zero]; exact hg0G
  obtain ⟨a, haA, ha⟩ := hFU A 0 ⟨(U : Filter ℝ), inferInstance, hAU, hconv⟩
  by_cases hb : ∃ M, ∀ n, |a n| ≤ M
  · have hp := etaConv_isPVG G
    have hlim := seqG_bounded hp (etaConv_hausdorff hG) (fun F x h => bohr_coarser G h) a 0 hb ha
    have h1 : Tendsto (fun n => e (a n)) atTop (𝓝 (e 0)) := (continuous_e.tendsto 0).comp hlim
    have h2 : (0 : K) ∈ N := by
      rw [e_zero] at h1
      exact hNclosed.mem_of_tendsto h1 (Filter.Eventually.of_forall (fun n => haA n))
    exact h0N h2
  · push Not at hb
    have hunb : ∀ M : ℝ, ∃ k, M < |a k| := hb
    have := seqG_unbounded G a 0 hunb ha
    exact absurd this (ne_of_lt hdim)

#print axioms euclid_coarser
#print axioms exists_nonzero_admissible
#print axioms not_FU

end Q95
end PVG
