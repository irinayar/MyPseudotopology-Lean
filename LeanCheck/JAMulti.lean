import Mathlib
import LeanCheck.JARealization

/-!
# Multi-level realization (the cascade of all earlier levels)

A **chain** is a sequence of scales `q_0 ∣ q_1 ∣ q_2 ∣ …` with windows `w_k : ZMod q_k → ℝ`.  Given a seed on `ZMod q_0` and
shifts `τ_k ∈ ZMod q_k`, the weights are `g_0 = seed`, `g_{k+1}(x) = g_k(x mod q_k - τ_k) · w_{k+1}(x)`.

For a fixed ambient group `ZMod N` (all `q_k ∣ N`) put `kernq w = kern N Q (N/Q) w`, and let `Mavg n c s` be the **expected
kernel measure** of the `n`-th level: `Mavg 0 c s = s` and
`Mavg (n+1) c s = Mavg n c.tail ((1/q_0^2) · (s ∗ kernq (q_1) (w_1)))`.
(`JAPackaging.expected_measure` says exactly that averaging the last shift replaces the kernel measure of the seed by
`P^{-2}` times its convolution with the kernel of the window; iterating gives `Mavg`.)

Checked here (no axiom, no `sorry`):

* `Chain.weights`, `weights_cons`, `weights_nonneg`: the weights and their first-level decomposition;
* `Mavg_sum`, `Mavg_smul`, `Mavg_PD`: `Mavg` is linear in the seed measure and preserves positive definiteness;
* `Phi`, `Phi_sum`, `Phi_smul`: the bilinear functional `Φ(ν_a, ν_b) = ∑_x (ν_a ∗ ν_b)(x) Ψ_L(x)`;
* `multi_exists`: for two chains of depths `na`, `nb`, **there are shifts at ALL levels** with
  `Φ(kernq(g_n^a), kernq(g_n^b)) ≤ Φ(Mavg_a, Mavg_b)` (induction on `n`: choose the first shifts so that the later problem
  with the new seeds is at most its mean, which is bilinear in the seeds' kernel measures);
* `multi_realization`: the energy of the pair of last-level weights is at most
  `3 L^3 (Mavg_a ∗ Mavg_b)(arc(m-1)) / (Q_a Q_b)^2`, `L = X + 1 + Q_a + Q_b`.
-/

namespace LeanCheck
namespace JAMulti

open Finset JATransfer JARandom JAPackaging JAEnergyLink JARealization JABlocks

/-! ### Chains -/

structure Chain where
  q : ℕ → ℕ
  pos : ∀ k, 0 < q k
  dvd : ∀ k, q k ∣ q (k + 1)
  w : ∀ k, ZMod (q k) → ℝ

instance (c : Chain) (k : ℕ) : NeZero (c.q k) := ⟨(c.pos k).ne'⟩

/-- Forget level `0`. -/
def Chain.tail (c : Chain) : Chain where
  q := fun k => c.q (k + 1)
  pos := fun k => c.pos (k + 1)
  dvd := fun k => c.dvd (k + 1)
  w := fun k => c.w (k + 1)

/-- The weights `g_0 = seed`, `g_{k+1}(x) = g_k(x mod q_k - τ_k) w_{k+1}(x)`. -/
noncomputable def Chain.weights (c : Chain) (τ : ∀ k, ZMod (c.q k)) (seed : ZMod (c.q 0) → ℝ) :
    (k : ℕ) → ZMod (c.q k) → ℝ
  | 0 => seed
  | k + 1 => fun x => Chain.weights c τ seed k (rd (c.dvd k) x - τ k) * c.w (k + 1) x

/-- Prepend a first shift to a family of shifts of the tail. -/
def Chain.consShift (c : Chain) (τ₀ : ZMod (c.q 0)) (τ' : ∀ k, ZMod (c.tail.q k)) : ∀ k, ZMod (c.q k) :=
  fun k => Nat.casesOn (motive := fun k => ZMod (c.q k)) k τ₀ (fun j => τ' j)

lemma weights_cons (c : Chain) (τ₀ : ZMod (c.q 0)) (τ' : ∀ k, ZMod (c.tail.q k))
    (seed : ZMod (c.q 0) → ℝ) (n : ℕ) :
    c.weights (c.consShift τ₀ τ') seed (n + 1) =
      c.tail.weights τ' (fun x : ZMod (c.q 1) => seed (rd (c.dvd 0) x - τ₀) * c.w 1 x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show c.weights (c.consShift τ₀ τ') seed (n + 1) (rd (c.dvd (n + 1)) x - (show ZMod (c.q (n + 1)) from τ' n)) * c.w (n + 2) x =
      c.tail.weights τ' (fun x : ZMod (c.q 1) => seed (rd (c.dvd 0) x - τ₀) * c.w 1 x) n
        (rd (c.tail.dvd n) x - τ' n) * c.tail.w (n + 1) x
    rw [ih]
    rfl

lemma weights_nonneg (c : Chain) (hw : ∀ k x, 0 ≤ c.w k x) (τ : ∀ k, ZMod (c.q k))
    (seed : ZMod (c.q 0) → ℝ) (hs : ∀ x, 0 ≤ seed x) :
    ∀ (k : ℕ) (x : ZMod (c.q k)), 0 ≤ c.weights τ seed k x := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih => intro x; exact mul_nonneg (ih _) (hw _ _)

/-! ### The expected kernel measure -/

section avg

variable (N : ℕ) [NeZero N]

/-- Kernel measure on `ZMod N` of a weight on `ZMod Q`. -/
noncomputable def kernq (Q : ℕ) [NeZero Q] (w : ZMod Q → ℝ) : ZMod N → ℝ := kern N Q (N / Q) w

/-- The expected kernel measure of the `n`-th level. -/
noncomputable def Mavg : ℕ → Chain → (ZMod N → ℝ) → (ZMod N → ℝ)
  | 0, _, s => s
  | n + 1, c, s => Mavg n c.tail
      (fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv s (kernq N (c.q 1) (c.w 1)) x)

lemma conv_sum_left {ι : Type*} [Fintype ι] (s : ι → ZMod N → ℝ) (v : ZMod N → ℝ) (x : ZMod N) :
    conv (fun y => ∑ i, s i y) v x = ∑ i, conv (s i) v x := by
  unfold conv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

lemma conv_smul_left (a : ℝ) (s v : ZMod N → ℝ) (x : ZMod N) :
    conv (fun y => a * s y) v x = a * conv s v x := by
  unfold conv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma Mavg_sum {ι : Type*} [Fintype ι] :
    ∀ (n : ℕ) (c : Chain) (s : ι → ZMod N → ℝ),
      Mavg N n c (fun x => ∑ i, s i x) = fun x => ∑ i, Mavg N n c (s i) x := by
  intro n
  induction n with
  | zero => intro c s; rfl
  | succ n ih =>
    intro c s
    simp only [Mavg]
    have h : (fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv (fun y => ∑ i, s i y)
        (kernq N (c.q 1) (c.w 1)) x) =
        fun x => ∑ i, (fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv (s i) (kernq N (c.q 1) (c.w 1)) x) x := by
      funext x
      rw [conv_sum_left, Finset.mul_sum]
    rw [h]
    exact ih c.tail (fun i x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv (s i) (kernq N (c.q 1) (c.w 1)) x)

lemma Mavg_smul (a : ℝ) :
    ∀ (n : ℕ) (c : Chain) (s : ZMod N → ℝ),
      Mavg N n c (fun x => a * s x) = fun x => a * Mavg N n c s x := by
  intro n
  induction n with
  | zero => intro c s; rfl
  | succ n ih =>
    intro c s
    simp only [Mavg]
    have h : (fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv (fun y => a * s y)
        (kernq N (c.q 1) (c.w 1)) x) =
        fun x => a * ((fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv s (kernq N (c.q 1) (c.w 1)) x) x) := by
      funext x
      rw [conv_smul_left]
      ring
    rw [h]
    exact ih c.tail (fun x => (1 / ((c.q 0 : ℕ) : ℝ) ^ 2) * conv s (kernq N (c.q 1) (c.w 1)) x)

lemma kernq_PD (Q : ℕ) [NeZero Q] (hQ : Q ∣ N) (w : ZMod Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    PD (kernq N Q w) :=
  kern_PD (Nat.mul_div_cancel' hQ).symm w hw

lemma Mavg_PD : ∀ (n : ℕ) (c : Chain), (∀ k x, 0 ≤ c.w k x) → (∀ k, k ≤ n → c.q k ∣ N) →
    ∀ s : ZMod N → ℝ, PD s → PD (Mavg N n c s) := by
  intro n
  induction n with
  | zero => intro c _ _ s hs; exact hs
  | succ n ih =>
    intro c hw hN s hs
    simp only [Mavg]
    apply ih c.tail (fun k x => hw (k + 1) x) (fun k hk => hN (k + 1) (by omega))
    exact (hs.conv (kernq_PD N (c.q 1) (hN 1 (by omega)) (c.w 1) (hw 1))).smul (by positivity)

/-! ### The spectral functional -/

/-- `Φ(ν_a, ν_b) = ∑_x (ν_a ∗ ν_b)(x) Ψ_L(x)`. -/
noncomputable def Phi (L : ℕ) (νa νb : ZMod N → ℝ) : ℝ :=
  ∑ x, conv νa νb x * JASpectral.Psi L (ang N x)

lemma Phi_sum (L : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → ZMod N → ℝ) (B : κ → ZMod N → ℝ) :
    Phi N L (fun y => ∑ i, A i y) (fun y => ∑ k, B k y) = ∑ i, ∑ k, Phi N L (A i) (B k) := by
  unfold Phi
  have h : ∀ x, conv (fun y => ∑ i, A i y) (fun y => ∑ k, B k y) x = ∑ i, ∑ k, conv (A i) (B k) x :=
    fun x => (sum_conv A B x).symm
  simp_rw [h, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

lemma Phi_smul (L : ℕ) (a b : ℝ) (νa νb : ZMod N → ℝ) :
    Phi N L (fun x => a * νa x) (fun x => b * νb x) = (a * b) * Phi N L νa νb := by
  unfold Phi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [conv_smul]
  ring

/-! ### Existence of shifts at all levels -/

lemma conv_sum_right {ι : Type*} [Fintype ι] (u : ZMod N → ℝ) (s : ι → ZMod N → ℝ) (x : ZMod N) :
    conv u (fun y => ∑ i, s i y) x = ∑ i, conv u (s i) x := by
  unfold conv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma conv_comm' (u v : ZMod N → ℝ) (x : ZMod N) : conv u v x = conv v u x := by
  unfold conv
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

lemma Phi_comm (L : ℕ) (νa νb : ZMod N → ℝ) : Phi N L νa νb = Phi N L νb νa := by
  unfold Phi
  apply Finset.sum_congr rfl
  intro x _
  rw [conv_comm']

lemma Phi_sum_left (L : ℕ) {ι : Type*} [Fintype ι] (A : ι → ZMod N → ℝ) (νb : ZMod N → ℝ) :
    Phi N L (fun y => ∑ i, A i y) νb = ∑ i, Phi N L (A i) νb := by
  unfold Phi
  simp_rw [conv_sum_left, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma Phi_smul_left (L : ℕ) (a : ℝ) (νa νb : ZMod N → ℝ) :
    Phi N L (fun x => a * νa x) νb = a * Phi N L νa νb := by
  unfold Phi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [conv_smul_left]
  ring

/-- The statement for two chains of depths `na`, `nb`. -/
def Claim (L na nb : ℕ) : Prop :=
  ∀ (ca cb : Chain), (∀ k, k ≤ na → ca.q k ∣ N) → (∀ k, k ≤ nb → cb.q k ∣ N) →
    ∀ (seeda : ZMod (ca.q 0) → ℝ) (seedb : ZMod (cb.q 0) → ℝ),
    ∃ (τa : ∀ k, ZMod (ca.q k)) (τb : ∀ k, ZMod (cb.q k)),
      Phi N L (kernq N (ca.q na) (ca.weights τa seeda na)) (kernq N (cb.q nb) (cb.weights τb seedb nb)) ≤
      Phi N L (Mavg N na ca (kernq N (ca.q 0) seeda)) (Mavg N nb cb (kernq N (cb.q 0) seedb))

lemma Claim_swap (L na nb : ℕ) (h : Claim N L na nb) : Claim N L nb na := by
  intro ca cb hNa hNb seeda seedb
  obtain ⟨τb, τa, hle⟩ := h cb ca hNb hNa seedb seeda
  refine ⟨τa, τb, ?_⟩
  exact (Phi_comm N L _ _).le.trans (hle.trans (Phi_comm N L _ _).le)

lemma Claim_zero (L : ℕ) : Claim N L 0 0 := by
  intro ca cb _ _ seeda seedb
  exact ⟨fun k => 0, fun k => 0, le_of_eq rfl⟩

/-- Peel the first level of the chain `a`. -/
lemma Claim_step (L na nb : ℕ) (IH : Claim N L na nb) : Claim N L (na + 1) nb := by
  classical
  intro ca cb hNa hNb seeda seedb
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
  have key : ∀ τ₀a : ZMod (ca.q 0),
      ∃ (τa' : ∀ k, ZMod (ca.tail.q k)) (τb' : ∀ k, ZMod (cb.q k)),
        Phi N L (kernq N (ca.tail.q na) (ca.tail.weights τa' (g1a τ₀a) na))
            (kernq N (cb.q nb) (cb.weights τb' seedb nb)) ≤
        Phi N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ₀a))) Mb :=
    fun τ₀a => IH ca.tail cb (fun k hk => hNa (k + 1) (by omega)) hNb (g1a τ₀a) seedb
  have havg : ∑ τ : ZMod (ca.q 0), Phi N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb =
      ((ca.q 0 : ℕ) : ℝ) * Phi N L (Mavg N (na + 1) ca (kernq N (ca.q 0) seeda)) Mb := by
    have e1 : (fun y => ∑ τ : ZMod (ca.q 0), Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ)) y) =
        fun y => ((ca.q 0 : ℕ) : ℝ) * Mavg N na ca.tail seed'a y := by
      rw [← Mavg_sum N na ca.tail (fun τ => kernq N (ca.tail.q 0) (g1a τ))]
      have : (fun x => ∑ τ : ZMod (ca.q 0), kernq N (ca.tail.q 0) (g1a τ) x) =
          fun x => ((ca.q 0 : ℕ) : ℝ) * seed'a x := funext hEa
      rw [this]
      exact Mavg_smul N _ na ca.tail seed'a
    have h3 := Phi_sum_left N L (fun τ : ZMod (ca.q 0) =>
      Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb
    rw [← h3, e1, Phi_smul_left]
    rfl
  have hne : (Finset.univ : Finset (ZMod (ca.q 0))).Nonempty := Finset.univ_nonempty
  set tgt : ℝ := Phi N L (Mavg N (na + 1) ca (kernq N (ca.q 0) seeda)) Mb with htgt
  have hcard : ((Finset.univ : Finset (ZMod (ca.q 0))).card : ℝ) = ((ca.q 0 : ℕ) : ℝ) := by
    rw [Finset.card_univ, ZMod.card]
  have hle : ∑ τ : ZMod (ca.q 0), Phi N L (Mavg N na ca.tail (kernq N (ca.tail.q 0) (g1a τ))) Mb ≤
      ∑ τ : ZMod (ca.q 0), tgt := by
    rw [havg, Finset.sum_const, nsmul_eq_mul, hcard]
  obtain ⟨τ₀, _, hp⟩ := Finset.exists_le_of_sum_le hne hle
  obtain ⟨τa', τb', hτ⟩ := key τ₀
  refine ⟨ca.consShift τ₀ τa', τb', ?_⟩
  rw [weights_cons]
  exact hτ.trans hp

theorem multi_exists (L na nb : ℕ) : Claim N L na nb := by
  have h0 : ∀ n, Claim N L n 0 := by
    intro n
    induction n with
    | zero => exact Claim_zero N L
    | succ n ih => exact Claim_step N L n 0 ih
  have h1 : ∀ n, Claim N L 0 n := fun n => Claim_swap N L n 0 (h0 n)
  induction na with
  | zero => exact h1 nb
  | succ na ih => exact Claim_step N L na nb ih

end avg

#print axioms weights_cons
#print axioms Mavg_sum
#print axioms Mavg_smul
#print axioms Mavg_PD
#print axioms Phi_sum
#print axioms multi_exists

end JAMulti
end LeanCheck
