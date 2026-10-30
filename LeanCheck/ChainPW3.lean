import Mathlib

/-!
# Peter–Weyl, part 3: a commuting family of operators on a finite-dimensional complex space has a common
eigenvector (induction on the dimension of an invariant subspace).
-/

namespace LeanCheck
namespace PW

open Module

theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] {ι : Type*} (T : ι → V →ₗ[ℂ] V)
    (hcomm : ∀ i j x, T i (T j x) = T j (T i x)) :
    ∃ w : V, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i w = c • w := by
  have key : ∀ n : ℕ, ∀ W : Submodule ℂ V, finrank ℂ W = n → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ w ∈ W, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i w = c • w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W hn hWbot hinv
      by_cases hall : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
      · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
        exact ⟨w, hwW, hw0, fun i => by
          obtain ⟨c, hc⟩ := hall i
          exact ⟨c, hc w hwW⟩⟩
      · push_neg at hall
        obtain ⟨i₀, hi₀⟩ := hall
        haveI : FiniteDimensional ℂ W := inferInstance
        haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hWbot
        let S : W →ₗ[ℂ] W := (T i₀).restrict (fun x hx => hinv i₀ x hx)
        obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue S
        obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
        have hvS : S v = c • v := Module.End.mem_eigenspace_iff.1 hv.1
        have hvT : T i₀ (v : V) = c • (v : V) := by
          have := congrArg Subtype.val hvS
          simpa [S] using this
        let W' : Submodule ℂ V := W ⊓ LinearMap.ker (T i₀ - c • LinearMap.id)
        have hW'W : W' ≤ W := inf_le_left
        have hvW' : (v : V) ∈ W' := by
          refine ⟨v.2, ?_⟩
          simp [LinearMap.mem_ker, hvT]
        have hW'bot : W' ≠ ⊥ := by
          intro h
          have : (v : V) = 0 := by
            have := hvW'; rw [h] at this; simpa using this
          exact hv.2 (Subtype.ext this)
        have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
          intro j x hx
          refine ⟨hinv j x hx.1, ?_⟩
          have hx2 : T i₀ x = c • x := by
            have := hx.2
            simpa [LinearMap.mem_ker, sub_eq_zero] using this
          show (T i₀ - c • (LinearMap.id : V →ₗ[ℂ] V) : V →ₗ[ℂ] V) (T j x) = 0
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
          rw [hcomm, hx2, map_smul, sub_self]
        have hW'lt : W' < W := by
          refine lt_of_le_of_ne hW'W (fun h => ?_)
          obtain ⟨x, hxW, hx⟩ := hi₀ c
          apply hx
          have : x ∈ W' := h ▸ hxW
          simpa [LinearMap.mem_ker, sub_eq_zero] using this.2
        have hlt : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hW'lt
        obtain ⟨w, hwW', hw0, hw⟩ := ih _ hlt W' rfl hW'bot hW'inv
        exact ⟨w, hW'W hwW', hw0, hw⟩
  obtain ⟨w, -, hw0, hw⟩ := key _ ⊤ rfl (by simpa using (Submodule.nontrivial_iff_ne_bot.1 inferInstance).symm ▸ top_ne_bot)
    (fun i x _ => Submodule.mem_top)
  exact ⟨w, hw0, hw⟩

end PW
end LeanCheck
