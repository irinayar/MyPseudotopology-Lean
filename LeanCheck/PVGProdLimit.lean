import Mathlib
import LeanCheck.PVGSequences
import LeanCheck.PVGLacCount
import LeanCheck.PVGBohr

/-!
# PVG: a net that tends to zero in the Bohr topology (Lean check)

Scope. Lemma 8.90 of `PVG_v42`/`PVG_v43` (Part II), the step used in Propositions 8.88, 8.91 and 8.97.
For a real number `a` and a free ultrafilter `U` on `ℕ`, put `x_{n,m} = a s_n - a s_m` with `s_n = sS n = 2^(n^2)`.
The statement is the iterated-limit form of "`x_{n,m} → 0` along the product ultrafilter `U ⊗ U` (restricted to `n < m`) in the
Bohr topology":

* `prodLimit_K` : for every neighbourhood `O` of `0` in the compact group `K = Hom(ℝ,𝕋)`, for `U`-most `n` and `U`-most `m`
  one has `e (a s_n - a s_m) ∈ O`;
* `prodLimit_bohr` : the same for every neighbourhood `V` of `0` in `bohrTop` (`x_{n,m} ∈ V`);
* `prodLimit_lt` : for a free `U` and every `n`, `U`-most `m` satisfy `n < m`, so the pairs with `n < m` belong to the product.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Lac
open Q95

lemma continuous_subK : Continuous (fun p : K × K => p.1 - p.2) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun b => ?_
  show Continuous fun p : K × K => p.1 b - p.2 b
  exact ((continuous_eval b).comp continuous_fst).sub ((continuous_eval b).comp continuous_snd)

lemma e_sub' (x y : ℝ) : e (x - y) = e x - e y := by
  ext b; simp [mul_sub]

/-- Iterated limit in `K`: `lim_n lim_m (e (a s_n) - e (a s_m)) = 0`, in neighbourhood form. -/
theorem prodLimit_K (a : ℝ) (U : Ultrafilter ℕ) (O : Set K) (hO : O ∈ 𝓝 (0 : K)) :
    ∀ᶠ n in (U : Filter ℕ), ∀ᶠ m in (U : Filter ℕ), e (a * sS n - a * sS m) ∈ O := by
  set κ : K := L (fun n => a * sS n) U with hκ
  have ht : Tendsto (fun n => e (a * sS n)) (U : Filter ℕ) (𝓝 κ) := tendsto_L _ U
  have hcont : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
    continuous_subK.tendsto (κ, κ)
  rw [sub_self] at hcont
  have hpre : (fun p : K × K => p.1 - p.2) ⁻¹' O ∈ 𝓝 (κ, κ) := hcont hO
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hpre
  have h1 : ∀ᶠ n in (U : Filter ℕ), e (a * sS n) ∈ t₁ := ht ht₁
  have h2 : ∀ᶠ m in (U : Filter ℕ), e (a * sS m) ∈ t₂ := ht ht₂
  filter_upwards [h1] with n hn
  filter_upwards [h2] with m hm
  have hmem : (e (a * sS n), e (a * sS m)) ∈ t₁ ×ˢ t₂ := ⟨hn, hm⟩
  have := hsub hmem
  simpa [e_sub'] using this

/-- The same statement for the Bohr topology of `ℝ`. -/
theorem prodLimit_bohr (a : ℝ) (U : Ultrafilter ℕ) (V : Set ℝ) (hV : V ∈ @nhds ℝ bohrTop 0) :
    ∀ᶠ n in (U : Filter ℕ), ∀ᶠ m in (U : Filter ℕ), a * sS n - a * sS m ∈ V := by
  rw [nhds_bohr] at hV
  obtain ⟨O, hO, hOV⟩ := Filter.mem_comap.1 hV
  have hO0 : O ∈ 𝓝 (0 : K) := by rwa [show (0 : K) = e 0 from e_zero.symm]
  filter_upwards [prodLimit_K a U O hO0] with n hn
  filter_upwards [hn] with m hm
  exact hOV hm

/-- For a free ultrafilter and every `n`, `U`-most `m` are larger than `n`. -/
theorem prodLimit_lt (U : Ultrafilter ℕ) (hU : Free U) (n : ℕ) :
    ∀ᶠ m in (U : Filter ℕ), n < m := by
  have h : (U : Filter ℕ) ≤ atTop := by
    have := hU
    unfold Free at this
    rwa [Nat.cofinite_eq_atTop] at this
  exact h (eventually_gt_atTop n)

/-- The combined form: for `U`-most `n` and `U`-most `m`, `n < m` and `x_{n,m}` lies in a given Bohr neighbourhood of `0`. -/
theorem prodLimit (a : ℝ) (U : Ultrafilter ℕ) (hU : Free U) (V : Set ℝ) (hV : V ∈ @nhds ℝ bohrTop 0) :
    ∀ᶠ n in (U : Filter ℕ), ∀ᶠ m in (U : Filter ℕ), n < m ∧ a * sS n - a * sS m ∈ V := by
  filter_upwards [prodLimit_bohr a U V hV] with n hn
  filter_upwards [hn, prodLimit_lt U hU n] with m hm hlt
  exact ⟨hlt, hm⟩

end Lac
end PVG
