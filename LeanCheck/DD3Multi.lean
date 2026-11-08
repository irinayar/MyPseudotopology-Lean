import Mathlib
import LeanCheck.DD3Energy
import LeanCheck.JAMulti2
import LeanCheck.JAProduct

/-!
# Diagonal density for three primes: shifts at all levels of three chains (Lean check)

Scope. Phase 5c of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`). It is the three-chain counterpart of `JAMulti` and `JAMulti2.multi_realization`
(the `Chain` structure, `Mavg`, `kernq` are those of `JAMulti`).

* `Phi3 L νa νb νc = ∑_x (νa ∗ (νb ∗ νc))(x) Ψ³_L(x)` and its linearity (`Phi3_sum_left`, `Phi3_smul_left`) and symmetry
  (`Phi3_swap12`, `Phi3_swap13`);
* `Claim3`, `Claim3_step`, `multi_exists3`: for three chains of depths `na, nb, nc` there are shifts at ALL levels with
  `Φ³(kernq g_a, kernq g_b, kernq g_c) ≤ Φ³(Mavg_a, Mavg_b, Mavg_c)` (the average over the first shift of one chain is
  the next `Mavg`; the other two chains are carried along; the steps for the second and third chain follow by symmetry);
* `multi_realization3`: the three-fold energy of the last-level weights is at most
  `3 L⁴ (Mavg_a ∗ (Mavg_b ∗ Mavg_c))(arc(m-1)) / (Q_a Q_b Q_c)²`, `L = X + 1 + Q_a + Q_b + Q_c`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Multi

open Finset JATransfer JARandom JAPackaging JAEnergyLink JARealization JABlocks JALocalize JAMulti DD3Energy

section avg

variable (N : ℕ) [NeZero N]

/-- `Φ³(ν_a, ν_b, ν_c) = ∑_x (ν_a ∗ (ν_b ∗ ν_c))(x) Ψ³_L(x)`. -/
noncomputable def Phi3 (L : ℕ) (νa νb νc : ZMod N → ℝ) : ℝ :=
  ∑ x, conv νa (conv νb νc) x * Psi3 L (ang N x)

lemma Phi3_sum_left (L : ℕ) {ι : Type*} [Fintype ι] (A : ι → ZMod N → ℝ) (νb νc : ZMod N → ℝ) :
    Phi3 N L (fun y => ∑ i, A i y) νb νc = ∑ i, Phi3 N L (A i) νb νc := by
  unfold Phi3
  simp_rw [conv_sum_left, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma Phi3_smul_left (L : ℕ) (a : ℝ) (νa νb νc : ZMod N → ℝ) :
    Phi3 N L (fun x => a * νa x) νb νc = a * Phi3 N L νa νb νc := by
  unfold Phi3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [conv_smul_left]
  ring

lemma Phi3_swap12 (L : ℕ) (νa νb νc : ZMod N → ℝ) :
    Phi3 N L νa νb νc = Phi3 N L νb νa νc := by
  unfold Phi3
  apply Finset.sum_congr rfl
  intro x _
  have e : conv νa (conv νb νc) x = conv νb (conv νa νc) x := by
    rw [conv_comm' N νa (conv νb νc) x, JAProduct.conv_assoc νb νc νa x]
    have : conv νc νa = conv νa νc := funext (conv_comm' N νc νa)
    rw [this]
  rw [e]

lemma Phi3_swap13 (L : ℕ) (νa νb νc : ZMod N → ℝ) :
    Phi3 N L νa νb νc = Phi3 N L νc νb νa := by
  unfold Phi3
  apply Finset.sum_congr rfl
  intro x _
  have e : conv νa (conv νb νc) x = conv νc (conv νb νa) x := by
    rw [← JAProduct.conv_assoc νa νb νc x, conv_comm' N (conv νa νb) νc x]
    have : conv νa νb = conv νb νa := funext (conv_comm' N νa νb)
    rw [this]
  rw [e]

/-! ### Existence of shifts at all levels, three chains -/

/-- The statement for three chains of depths `na`, `nb`, `nc`. -/
def Claim3 (L na nb nc : ℕ) : Prop :=
  ∀ (ca cb cc : Chain), (∀ k, k ≤ na → ca.q k ∣ N) → (∀ k, k ≤ nb → cb.q k ∣ N) →
    (∀ k, k ≤ nc → cc.q k ∣ N) →
    ∀ (seeda : ZMod (ca.q 0) → ℝ) (seedb : ZMod (cb.q 0) → ℝ) (seedc : ZMod (cc.q 0) → ℝ),
    ∃ (τa : ∀ k, ZMod (ca.q k)) (τb : ∀ k, ZMod (cb.q k)) (τc : ∀ k, ZMod (cc.q k)),
      Phi3 N L (kernq N (ca.q na) (ca.weights τa seeda na)) (kernq N (cb.q nb) (cb.weights τb seedb nb))
          (kernq N (cc.q nc) (cc.weights τc seedc nc)) ≤
      Phi3 N L (Mavg N na ca (kernq N (ca.q 0) seeda)) (Mavg N nb cb (kernq N (cb.q 0) seedb))
        (Mavg N nc cc (kernq N (cc.q 0) seedc))

lemma Claim3_swap12 (L na nb nc : ℕ) (h : Claim3 N L na nb nc) : Claim3 N L nb na nc := by
  intro ca cb cc hNa hNb hNc seeda seedb seedc
  obtain ⟨τb, τa, τc, hle⟩ := h cb ca cc hNb hNa hNc seedb seeda seedc
  refine ⟨τa, τb, τc, ?_⟩
  exact (Phi3_swap12 N L _ _ _).le.trans (hle.trans (Phi3_swap12 N L _ _ _).le)

lemma Claim3_swap13 (L na nb nc : ℕ) (h : Claim3 N L na nb nc) : Claim3 N L nc nb na := by
  intro ca cb cc hNa hNb hNc seeda seedb seedc
  obtain ⟨τc, τb, τa, hle⟩ := h cc cb ca hNc hNb hNa seedc seedb seeda
  refine ⟨τa, τb, τc, ?_⟩
  exact (Phi3_swap13 N L _ _ _).le.trans (hle.trans (Phi3_swap13 N L _ _ _).le)

lemma Claim3_zero (L : ℕ) : Claim3 N L 0 0 0 := by
  intro ca cb cc _ _ _ seeda seedb seedc
  exact ⟨fun k => 0, fun k => 0, fun k => 0, le_of_eq rfl⟩

/-- Peel the first level of the chain `a`. -/
lemma Claim3_step (L na nb nc : ℕ) (IH : Claim3 N L na nb nc) : Claim3 N L (na + 1) nb nc := by
  classical
  intro ca cb cc hNa hNb hNc seeda seedb seedc
  set g1a : ZMod (ca.q 0) → ZMod (ca.q 1) → ℝ :=
    fun τ x => seeda (rd (ca.dvd 0) x - τ) * ca.w 1 x with hg1a
  set seed'a : ZMod N → ℝ := fun x => (1 / ((ca.q 0 : ℕ) : ℝ) ^ 2) *
    conv (kernq N (ca.q 0) seeda) (kernq N (ca.q 1) (ca.w 1)) x with hseed'a
  have hPa : ((ca.q 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ca.pos 0).ne'
  have hEa : ∀ x, ∑ τ : ZMod (ca.q 0), kernq N (ca.q 1) (g1a τ) x = ((ca.q 0 : ℕ) : ℝ) * seed'a x := by
    intro x
    obtain ⟨α, hα⟩ := ca.dvd 0
    have hNQ : N = ca.q 1 * (N / ca.q 1) := (Nat.mul_div_cancel' (hNa 1 (by omega))).symm
    have hNP : N = ca.q 0 * (N / ca.q 0) := (Nat.mul_div_cancel' (hNa 0 (by omega))).symm
    have h := expected_measure (N := N) (P := ca.q 0) (Q := ca.q 1) (α := α) hα hNQ hNP seeda (ca.w 1) x
    simp only [hseed'a, kernq, hg1a]
    rw [← h]
    field_simp
  set Mb := Mavg N nb cb (kernq N (cb.q 0) seedb) with hMb
  set Mc := Mavg N nc cc (kernq N (cc.q 0) seedc) with hMc
  have key : ∀ τ₀a : ZMod (ca.q 0),
      ∃ (τa' : ∀ k, ZMod (ca.tail.q k)) (τb' : ∀ k, ZMod (cb.q k)) (τc' : ∀ k, ZMod (cc.q k)),
        Phi3 N L (kernq N (ca.tail.q na) (ca.tail.weights τa' (g1a τ₀a) na))
            (kernq N (cb.q nb) (cb.weights τb' seedb nb))
            (kernq N (cc.q nc) (cc.weights τc' seedc nc)) ≤
        Phi3 N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ₀a))) Mb Mc :=
    fun τ₀a => IH ca.tail cb cc (fun k hk => hNa (k + 1) (by omega)) hNb hNc (g1a τ₀a) seedb seedc
  have havg : ∑ τ : ZMod (ca.q 0), Phi3 N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb Mc =
      ((ca.q 0 : ℕ) : ℝ) * Phi3 N L (Mavg N (na + 1) ca (kernq N (ca.q 0) seeda)) Mb Mc := by
    have e1 : (fun y => ∑ τ : ZMod (ca.q 0), Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ)) y) =
        fun y => ((ca.q 0 : ℕ) : ℝ) * Mavg N na ca.tail seed'a y := by
      rw [← Mavg_sum N na ca.tail (fun τ => kernq N (ca.tail.q 0) (g1a τ))]
      have : (fun x => ∑ τ : ZMod (ca.q 0), kernq N (ca.tail.q 0) (g1a τ) x) =
          fun x => ((ca.q 0 : ℕ) : ℝ) * seed'a x := funext hEa
      rw [this]
      exact Mavg_smul N _ na ca.tail seed'a
    have h3 := Phi3_sum_left N L (fun τ : ZMod (ca.q 0) =>
      Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb Mc
    rw [← h3, e1, Phi3_smul_left]
    rfl
  have hne : (Finset.univ : Finset (ZMod (ca.q 0))).Nonempty := Finset.univ_nonempty
  set tgt : ℝ := Phi3 N L (Mavg N (na + 1) ca (kernq N (ca.q 0) seeda)) Mb Mc with htgt
  have hcard : ((Finset.univ : Finset (ZMod (ca.q 0))).card : ℝ) = ((ca.q 0 : ℕ) : ℝ) := by
    rw [Finset.card_univ, ZMod.card]
  have hle : ∑ τ : ZMod (ca.q 0), Phi3 N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb Mc ≤
      ∑ τ : ZMod (ca.q 0), tgt := by
    rw [havg, Finset.sum_const, nsmul_eq_mul, hcard]
  obtain ⟨τ₀, _, hp⟩ := Finset.exists_le_of_sum_le hne hle
  obtain ⟨τa', τb', τc', hτ⟩ := key τ₀
  refine ⟨ca.consShift τ₀ τa', τb', τc', ?_⟩
  rw [weights_cons]
  exact hτ.trans hp

lemma Claim3_stepB (L na nb nc : ℕ) (IH : Claim3 N L na nb nc) : Claim3 N L na (nb + 1) nc :=
  Claim3_swap12 N L _ _ _
    (Claim3_step N L nb na nc (Claim3_swap12 N L _ _ _ IH))

lemma Claim3_stepC (L na nb nc : ℕ) (IH : Claim3 N L na nb nc) : Claim3 N L na nb (nc + 1) :=
  Claim3_swap13 N L _ _ _
    (Claim3_step N L nc nb na (Claim3_swap13 N L _ _ _ IH))

theorem multi_exists3 (L na nb nc : ℕ) : Claim3 N L na nb nc := by
  have h0 : ∀ n, Claim3 N L n 0 0 := by
    intro n
    induction n with
    | zero => exact Claim3_zero N L
    | succ n ih => exact Claim3_step N L n 0 0 ih
  have h1 : ∀ n k, Claim3 N L n k 0 := by
    intro n k
    induction k with
    | zero => exact h0 n
    | succ k ih => exact Claim3_stepB N L n k 0 ih
  induction nc with
  | zero => exact h1 na nb
  | succ nc ih => exact Claim3_stepC N L na nb nc ih

end avg

/-! ### The energy bound for the three cascades -/

theorem multi_realization3 {N : ℕ} [NeZero N] (na nb nc : ℕ) (ca cb cc : Chain)
    (hNa : ∀ k, k ≤ na → ca.q k ∣ N) (hNb : ∀ k, k ≤ nb → cb.q k ∣ N) (hNc : ∀ k, k ≤ nc → cc.q k ∣ N)
    (hwa : ∀ k x, 0 ≤ ca.w k x) (hwb : ∀ k x, 0 ≤ cb.w k x) (hwc : ∀ k x, 0 ≤ cc.w k x)
    (seeda : ZMod (ca.q 0) → ℝ) (seedb : ZMod (cb.q 0) → ℝ) (seedc : ZMod (cc.q 0) → ℝ)
    (hsa : ∀ x, 0 ≤ seeda x) (hsb : ∀ x, 0 ≤ seedb x) (hsc : ∀ x, 0 ≤ seedc x)
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ (X + 1 + ca.q na + cb.q nb + cc.q nc) * m) :
    ∃ (τa : ∀ k, ZMod (ca.q k)) (τb : ∀ k, ZMod (cb.q k)) (τc : ∀ k, ZMod (cc.q k)),
      energyE3 (ca.weights τa seeda na) (cb.weights τb seedb nb) (cc.weights τc seedc nc) X ≤
        3 * ((X + 1 + ca.q na + cb.q nb + cc.q nc : ℕ) : ℝ) ^ 4 *
          (∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
            (conv (Mavg N nb cb (kernq N (cb.q 0) seedb)) (Mavg N nc cc (kernq N (cc.q 0) seedc))) t) /
          (((ca.q na : ℝ) * cb.q nb * cc.q nc) ^ 2) := by
  classical
  set L : ℕ := X + 1 + ca.q na + cb.q nb + cc.q nc with hL
  obtain ⟨τa, τb, τc, hΦ⟩ := multi_exists3 N L na nb nc ca cb cc hNa hNb hNc seeda seedb seedc
  refine ⟨τa, τb, τc, ?_⟩
  have hga := weights_nonneg ca hwa τa seeda hsa na
  have hgb := weights_nonneg cb hwb τb seedb hsb nb
  have hgc := weights_nonneg cc hwc τc seedc hsc nc
  have hN₂ : N = ca.q na * (N / ca.q na) := (Nat.mul_div_cancel' (hNa na le_rfl)).symm
  have hN₃ : N = cb.q nb * (N / cb.q nb) := (Nat.mul_div_cancel' (hNb nb le_rfl)).symm
  have hN₅ : N = cc.q nc * (N / cc.q nc) := (Nat.mul_div_cancel' (hNc nc le_rfl)).symm
  have hE := energy3_le_psi (N := N) (q₂ := ca.q na) (q₃ := cb.q nb) (q₅ := cc.q nc) (d₂ := N / ca.q na)
    (d₃ := N / cb.q nb) (d₅ := N / cc.q nc) hN₂ hN₃ hN₅ (ca.weights τa seeda na) (cb.weights τb seedb nb)
    (cc.weights τc seedc nc) hga hgb hgc X
  have hPDa : PD (Mavg N na ca (kernq N (ca.q 0) seeda)) :=
    Mavg_PD N na ca hwa hNa _ (kernq_PD N (ca.q 0) (hNa 0 (Nat.zero_le _)) seeda hsa)
  have hPDb : PD (Mavg N nb cb (kernq N (cb.q 0) seedb)) :=
    Mavg_PD N nb cb hwb hNb _ (kernq_PD N (cb.q 0) (hNb 0 (Nat.zero_le _)) seedb hsb)
  have hPDc : PD (Mavg N nc cc (kernq N (cc.q 0) seedc)) :=
    Mavg_PD N nc cc hwc hNc _ (kernq_PD N (cc.q 0) (hNc 0 (Nat.zero_le _)) seedc hsc)
  have hPD := hPDa.conv (hPDb.conv hPDc)
  have hwin := spectral_window3 L m hm hmN hLm _ hPD.nonneg hPD.coef
  have hQ : (0 : ℝ) < ((ca.q na : ℝ) * cb.q nb * cc.q nc) ^ 2 := by
    have h1 : (0 : ℝ) < ca.q na := by exact_mod_cast ca.pos na
    have h2 : (0 : ℝ) < cb.q nb := by exact_mod_cast cb.pos nb
    have h3 : (0 : ℝ) < cc.q nc := by exact_mod_cast cc.pos nc
    positivity
  have hΦ' : ∑ x, nuM3 N (ca.q na) (cb.q nb) (cc.q nc) (N / ca.q na) (N / cb.q nb) (N / cc.q nc)
        (ca.weights τa seeda na) (cb.weights τb seedb nb) (cc.weights τc seedc nc) x *
        Psi3 L (ang N x) ≤
      3 * (L : ℝ) ^ 4 * ∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
        (conv (Mavg N nb cb (kernq N (cb.q 0) seedb)) (Mavg N nc cc (kernq N (cc.q 0) seedc))) t :=
    hΦ.trans hwin
  calc energyE3 (ca.weights τa seeda na) (cb.weights τb seedb nb) (cc.weights τc seedc nc) X
      ≤ 1 / ((ca.q na : ℝ) * cb.q nb * cc.q nc) ^ 2 * ∑ x, nuM3 N (ca.q na) (cb.q nb) (cc.q nc)
          (N / ca.q na) (N / cb.q nb) (N / cc.q nc) (ca.weights τa seeda na) (cb.weights τb seedb nb)
          (cc.weights τc seedc nc) x * Psi3 L (ang N x) := hE
    _ ≤ 1 / ((ca.q na : ℝ) * cb.q nb * cc.q nc) ^ 2 * (3 * (L : ℝ) ^ 4 * ∑ t ∈ arc N (m - 1),
          conv (Mavg N na ca (kernq N (ca.q 0) seeda))
            (conv (Mavg N nb cb (kernq N (cb.q 0) seedb)) (Mavg N nc cc (kernq N (cc.q 0) seedc))) t) :=
        mul_le_mul_of_nonneg_left hΦ' (by positivity)
    _ = _ := by rw [hL]; ring

#print axioms Phi3_swap12
#print axioms Phi3_swap13
#print axioms Claim3_step
#print axioms multi_exists3
#print axioms multi_realization3

end DD3Multi
end LeanCheck
