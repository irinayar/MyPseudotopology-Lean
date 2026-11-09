import LeanCheck.PVGBohr

/-!
# PVG: weak topologies of dilation-invariant subgroups of characters (Lean check)

Scope. A bridge between the PVGs `η_G` below the Bohr topology and TVG topologies above it. Elements of `K = Hom(ℝ, 𝕋)` are also
the abstract characters `x ↦ κ(x)` of the group `ℝ`; the Euclidean-continuous ones are `e(b)`. For a real subspace `D ≤ K` (so
`D` is invariant under the dilation operators `D_c`) the weak topology `weakTop D` on `ℝ` is the initial topology of the characters in `D`.

* `WD D` (a type synonym of `ℝ` carrying `weakTop D`), with the instances `IsTopologicalAddGroup` and `ContinuousConstSMul ℝ` (dilations,
  because `D` is a subspace), and `weakW_continuous_char`: every `d ∈ D` is continuous;
* `weakW_t2` (if `e(b) ∈ D` for all `b`): it is Hausdorff;
* `weakTop_le_bohr` (if `e(b) ∈ D` for all `b`): it contains the Bohr topology.

For `D = e(ℝ) ⊕ G` with `G` admissible this is the TVG-side counterpart of `η_G` (the dual of `weakTop D` is `D`; that statement
uses Pontryagin duality and is not formalized here).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires mathematical
review.
-/

open Topology

namespace PVG
namespace Q95

/-- `x ↦ (d(x))_{d ∈ D}` as an additive homomorphism into a product of circles. -/
def weakMap (D : Submodule ℝ K) : ℝ →+ (↥D → AddCircle (1 : ℝ)) where
  toFun x d := (d : K) x
  map_zero' := by ext d; simp
  map_add' x y := by ext d; simp

/-- The weak topology of `D` on `ℝ`. -/
def weakTop (D : Submodule ℝ K) : TopologicalSpace ℝ := TopologicalSpace.induced (weakMap D) inferInstance

/-- `ℝ` with the weak topology of `D` (a type synonym, so that instances are unambiguous). -/
def WD (_D : Submodule ℝ K) : Type := ℝ

instance (D : Submodule ℝ K) : AddCommGroup (WD D) := inferInstanceAs (AddCommGroup ℝ)
instance (D : Submodule ℝ K) : Module ℝ (WD D) := inferInstanceAs (Module ℝ ℝ)
instance (D : Submodule ℝ K) : TopologicalSpace (WD D) := weakTop D

/-- The underlying real number. -/
def toR {D : Submodule ℝ K} (x : WD D) : ℝ := x

/-- The weak map on `WD D`. -/
def weakMapW (D : Submodule ℝ K) : WD D →+ (↥D → AddCircle (1 : ℝ)) := weakMap D

lemma weakW_inducing (D : Submodule ℝ K) : Topology.IsInducing (weakMapW D) := ⟨rfl⟩

instance (D : Submodule ℝ K) : IsTopologicalAddGroup (WD D) := by
  have := topologicalAddGroup_induced (weakMapW D)
  exact this

/-- Every character in `D` is continuous for the weak topology. -/
theorem weakW_continuous_char (D : Submodule ℝ K) {d : K} (hd : d ∈ D) :
    Continuous (fun x : WD D => d (toR x)) :=
  (continuous_apply (⟨d, hd⟩ : ↥D)).comp (weakW_inducing D).continuous

/-- The dilations are continuous for the weak topology (`D` is invariant under the operators `D_c`). -/
instance weakW_constSMul (D : Submodule ℝ K) : ContinuousConstSMul ℝ (WD D) := by
  refine ⟨fun c => ?_⟩
  rw [(weakW_inducing D).continuous_iff]
  refine continuous_pi (fun d => ?_)
  have hd : c • (d : K) ∈ D := D.smul_mem c d.2
  refine (weakW_continuous_char D hd).congr (fun x => ?_)
  show (c • (d : K)) (toR x) = (d : K) (toR (c • x))
  rw [smul_apply]
  rfl

/-- If `e(b) ∈ D` for all `b`, the weak topology is Hausdorff. -/
theorem weakW_t2 (D : Submodule ℝ K) (hD : ∀ b, e b ∈ D) : T2Space (WD D) := by
  have hinj : Function.Injective (weakMapW D) := by
    intro x y hxy
    by_contra hne
    have hz : toR x - toR y ≠ 0 := sub_ne_zero.2 hne
    have h1 : ∀ d : ↥D, (d : K) (toR x) = (d : K) (toR y) := fun d => congrFun hxy d
    have h2 := h1 ⟨e (1 / (2 * (toR x - toR y))), hD _⟩
    simp only [e_apply] at h2
    have h3 : (((1 / (2 * (toR x - toR y))) * (toR x - toR y) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [← sub_eq_zero, ← AddCircle.coe_sub] at h2
      have e1 : toR x * (1 / (2 * (toR x - toR y))) - toR y * (1 / (2 * (toR x - toR y))) =
          (1 / (2 * (toR x - toR y))) * (toR x - toR y) := by ring
      rw [e1] at h2
      exact h2
    have h4 : (1 / (2 * (toR x - toR y)) * (toR x - toR y) : ℝ) = 1 / 2 := by field_simp
    rw [h4] at h3
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h3
    have h5 : (n : ℝ) = 1 / 2 := by simpa using hn
    have h6 : (2 : ℝ) * n = 1 := by linarith
    have h7 : (2 : ℤ) * n = 1 := by exact_mod_cast h6
    omega
  exact (Topology.IsEmbedding.mk (weakW_inducing D) hinj).t2Space

/-- If `e(b) ∈ D` for all `b`, the weak topology contains the Bohr topology: the map `e` is continuous from `WD D` to `K`, and
the Bohr topology is the topology induced by `e`. -/
theorem weakTop_le_bohr (D : Submodule ℝ K) (hD : ∀ b, e b ∈ D) : weakTop D ≤ bohrTop := by
  have h1 : Continuous (fun x : WD D => e (toR x)) := by
    rw [isEmbedding_coe.isInducing.continuous_iff]
    refine continuous_pi (fun b => ?_)
    refine (weakW_continuous_char D (hD b)).congr (fun x => ?_)
    simp [e_apply, mul_comm]
  intro s hs
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hs
  exact h1.isOpen_preimage O hO

#print axioms weakW_continuous_char
#print axioms weakW_t2
#print axioms weakTop_le_bohr

end Q95
end PVG
