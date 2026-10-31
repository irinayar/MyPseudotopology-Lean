import Mathlib
import LeanCheck.JAAssembly
import LeanCheck.JAEnergyIdentity

/-!
# From the spectral window to a large difference set (end of components 16 and 17)

Combines `JAEnergyLink.energy_normalized` (weighted energy `≤ K (T_2 T_3)^2`), `JAEnergyIdentity.sum_sq_rep_energyE`
(the representation energy is that energy) and `JAAssembly.card_V_ge` (weighted Cauchy-Schwarz):

for nonnegative periodic weights `f_2, f_3` (periods `q_2, q_3 ∣ N`) restricted to `[0, X]`, and any finite sets
`A_2, A_3 ⊆ [0, X]` outside which the weights vanish,
`|A_3 - A_2| ≥ 1 / K`, `K = 3 L^3 ν(arc(m-1)) / ((X+1-q_2)^2 (X+1-q_3)^2 (S_2 S_3)^2)`,
where `ν = |f̂_2|^2 * |f̂_3|^2` and `L = X + 1 + q_2 + q_3`.

This is the step "weighted Cauchy-Schwarz gives `|V_X| ≥ c_D (2X+1)`" once the spectral mass `ν(arc(m-1))` is bounded
by the normalized-product argument.
-/

namespace LeanCheck
namespace JAEnergyFinal

open Finset JAEnergy JAEnergyLink JAEnergyIdentity JAAssembly JATransfer JABlocks JALocalize

lemma rep_support (A A' B B' : Finset ℤ) (F G : ℤ → ℝ) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hF : ∀ a ∈ A, a ∉ A' → F a = 0) (hG : ∀ b ∈ B, b ∉ B' → G b = 0) (d : ℤ) :
    rep A' B' F G d = rep A B F G d := by
  unfold rep
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hA hp.1.1, hB hp.1.2⟩, hp.2⟩
  · intro p hp hnp
    simp only [Finset.mem_filter, Finset.mem_product] at hp hnp
    by_cases h1 : p.1 ∈ A'
    · have h2 : p.2 ∉ B' := fun h2 => hnp ⟨⟨h1, h2⟩, hp.2⟩
      rw [hG p.2 hp.1.2 h2, mul_zero]
    · rw [hF p.1 hp.1.1 h1, zero_mul]

lemma sum_support (A A' : Finset ℤ) (F : ℤ → ℝ) (hA : A' ⊆ A) (hF : ∀ a ∈ A, a ∉ A' → F a = 0) :
    ∑ a ∈ A', F a = ∑ a ∈ A, F a :=
  Finset.sum_subset hA (fun a ha h => hF a ha h)

/-- **The spectral bound gives a large difference set.** -/
theorem card_V_ge_spectral {q₂ q₃ N d₂ d₃ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero N]
    (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hLm : N ≤ (X + 1 + q₂ + q₃) * m) (hX₂ : q₂ < X + 1) (hX₃ : q₃ < X + 1)
    (hS₂ : 0 < ∑ x ∈ range q₂, fn f₂ x) (hS₃ : 0 < ∑ x ∈ range q₃, fn f₃ x)
    (hB : 0 < ∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t)
    (A₂ A₃ : Finset ℤ) (hA₂ : A₂ ⊆ Aset X) (hA₃ : A₃ ⊆ Aset X)
    (hs₂ : ∀ a ∈ Aset X, a ∉ A₂ → Fw f₂ a = 0) (hs₃ : ∀ a ∈ Aset X, a ∉ A₃ → Fw f₃ a = 0)
    (hT : 0 < (∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x)) :
    1 / (3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t) /
        ((((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) *
          ((∑ x ∈ range q₂, fn f₂ x) * (∑ x ∈ range q₃, fn f₃ x))) ^ 2)) ≤
      ((Vset A₃ A₂).card : ℝ) := by
  set Kc : ℝ := 3 * ((X + 1 + q₂ + q₃ : ℕ) : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1), nuM N q₂ q₃ d₂ d₃ f₂ f₃ t) /
        ((((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) *
          ((∑ x ∈ range q₂, fn f₂ x) * (∑ x ∈ range q₃, fn f₃ x))) ^ 2) with hKc
  have hX₂R : (0 : ℝ) < (X : ℝ) + 1 - q₂ := by
    have : (q₂ : ℝ) < X + 1 := by exact_mod_cast hX₂
    linarith
  have hX₃R : (0 : ℝ) < (X : ℝ) + 1 - q₃ := by
    have : (q₃ : ℝ) < X + 1 := by exact_mod_cast hX₃
    linarith
  have hKpos : 0 < Kc := by
    rw [hKc]
    have : (0 : ℝ) < ((X + 1 + q₂ + q₃ : ℕ) : ℝ) := by positivity
    positivity
  have hE := energy_normalized hN₂ hN₃ f₂ f₃ hf₂ hf₃ X m hm hmN hLm hX₂ hX₃ hS₂ hS₃
  rw [← hKc] at hE
  have hI := sum_sq_rep_energyE f₂ f₃ X
  -- weight sums over the supports
  have hT₂ : ∑ a ∈ A₂, Fw f₂ a = ∑ x ∈ range (X + 1), fn f₂ x := by
    rw [sum_support (Aset X) A₂ _ hA₂ hs₂, sum_Aset]
    simp [Fw]
  have hT₃ : ∑ a ∈ A₃, Fw f₃ a = ∑ x ∈ range (X + 1), fn f₃ x := by
    rw [sum_support (Aset X) A₃ _ hA₃ hs₃, sum_Aset]
    simp [Fw]
  have hrep : ∀ d, rep A₃ A₂ (Fw f₃) (Fw f₂) d = rep (Aset X) (Aset X) (Fw f₃) (Fw f₂) d :=
    fun d => rep_support (Aset X) A₃ (Aset X) A₂ _ _ hA₃ hA₂ hs₃ hs₂ d
  have hmain : ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep A₃ A₂ (Fw f₃) (Fw f₂) d) ^ 2 =
      energyE f₂ f₃ X := by
    rw [← hI]
    exact Finset.sum_congr rfl (fun d _ => by rw [hrep d])
  have hXpos : (0 : ℝ) < 2 * (X : ℝ) + 1 := by positivity
  have hm0 : 0 < (∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b) := by
    rw [hT₂, hT₃, mul_comm]; exact hT
  have hcard := card_V_ge X A₃ A₂ (Fw f₃) (Fw f₂)
    (fun a ha => by
      have := hA₃ ha
      unfold Aset at this
      simp only [Finset.mem_image, Finset.mem_range] at this
      obtain ⟨x, hx, rfl⟩ := this
      omega)
    (fun a ha => by
      have := hA₂ ha
      unfold Aset at this
      simp only [Finset.mem_image, Finset.mem_range] at this
      obtain ⟨x, hx, rfl⟩ := this
      omega)
    hm0 (Kc * (2 * (X : ℝ) + 1)) (by positivity) (by
      rw [hmain]
      have : Kc * (2 * (X : ℝ) + 1) * ((∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b)) ^ 2 /
          (2 * (X : ℝ) + 1) = Kc * ((∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b)) ^ 2 := by
        field_simp
      rw [this, hT₂, hT₃, mul_comm (∑ x ∈ range (X + 1), fn f₃ x)]
      exact hE)
  have : (2 * (X : ℝ) + 1) / (Kc * (2 * (X : ℝ) + 1)) = 1 / Kc := by
    field_simp
  rw [this] at hcard
  exact hcard

#print axioms rep_support
#print axioms card_V_ge_spectral

end JAEnergyFinal
end LeanCheck
