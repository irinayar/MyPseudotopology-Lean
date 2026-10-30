import LeanCheck.ChainTop

/-!
# The character `ζ_z : ℚ/ℤ → ℝ/ℤ` of a compatible residue system, and the dictionary

For a divisibility chain `M` (profinitely null) and a compatible residue system `z`
(`M k ∣ z (k+1) - z k`), the profinite integer `ζ` acts on `x ∈ ℚ/ℤ = TorsA` by `ζ x = z k • x`
for any `k` with `M k • x = 0`.  We show this is a well-defined additive character, and that
continuity of `ζ` for `λ_{range M}` yields the quarter-arc statement `Cont` of `ChainDichotomy`.
-/

namespace LeanCheck

open Filter Topology

section zeta

variable {M : ℕ → ℕ}

lemma chain_dvd (hM : ∀ n, M n ∣ M (n + 1)) {a b : ℕ} (h : a ≤ b) : M a ∣ M b := by
  induction b, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b _ ih => exact ih.trans (hM b)

lemma z_dvd {z : ℕ → ℤ} (hM : ∀ n, M n ∣ M (n + 1)) (hz : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k)
    {a b : ℕ} (h : a ≤ b) : (M a : ℤ) ∣ z b - z a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have h1 : (M a : ℤ) ∣ z (b + 1) - z b :=
      (Int.natCast_dvd_natCast.mpr (chain_dvd hM hb)).trans (hz b)
    have e : z (b + 1) - z a = (z (b + 1) - z b) + (z b - z a) := by ring
    rw [e]
    exact dvd_add h1 ih

lemma kill_of_dvd (hM : ∀ n, M n ∣ M (n + 1)) {a b : ℕ} (h : a ≤ b) {y : Circ}
    (ha : M a • y = 0) : M b • y = 0 := by
  obtain ⟨m, hm⟩ := chain_dvd hM h
  rw [hm, mul_comm, mul_smul, ha, smul_zero]

lemma exists_k (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (x : TorsA) :
    ∃ k, M k • (x : Circ) = 0 := by
  have hx : IsOfFinAddOrder (x : Circ) := x.2
  obtain ⟨N, hN, hNx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  obtain ⟨n0, hn0⟩ := hnull N hN
  obtain ⟨m, hm⟩ := hn0 n0 le_rfl
  exact ⟨n0, by rw [hm, mul_comm, mul_smul, hNx, smul_zero]⟩

lemma zsmul_eq {z : ℕ → ℤ} (hM : ∀ n, M n ∣ M (n + 1)) (hz : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k)
    {y : Circ} {k1 k2 : ℕ} (h1 : M k1 • y = 0) (h2 : M k2 • y = 0) : z k1 • y = z k2 • y := by
  have key : ∀ {a b : ℕ}, a ≤ b → M a • y = 0 → z a • y = z b • y := by
    intro a b hab ha
    obtain ⟨c, hc⟩ := z_dvd hM hz hab
    have h0 : (z b - z a) • y = 0 := by
      rw [hc, mul_comm, mul_smul, natCast_zsmul, ha, smul_zero]
    rw [sub_zsmul] at h0
    exact (add_neg_eq_zero.mp h0).symm
  rcases le_total k1 k2 with h | h
  · exact key h h1
  · exact (key h h2).symm

/-- `ζ` as an additive character of `ℚ/ℤ`. -/
noncomputable def zetaHom (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (hM : ∀ n, M n ∣ M (n + 1)) (z : ℕ → ℤ) (hz : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k) :
    TorsA →+ Circ where
  toFun x := z (Classical.choose (exists_k hnull x)) • (x : Circ)
  map_zero' := by simp
  map_add' := by
    intro x y
    have hx := Classical.choose_spec (exists_k hnull x)
    have hy := Classical.choose_spec (exists_k hnull y)
    set kx := Classical.choose (exists_k hnull x)
    set ky := Classical.choose (exists_k hnull y)
    have hxy := Classical.choose_spec (exists_k hnull (x + y))
    set kxy := Classical.choose (exists_k hnull (x + y))
    set K := max (max kx ky) kxy with hK
    have hxK : M K • (x : Circ) = 0 :=
      kill_of_dvd hM (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hyK : M K • (y : Circ) = 0 :=
      kill_of_dvd hM (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    have hxyK : M K • ((x + y : TorsA) : Circ) = 0 :=
      kill_of_dvd hM (le_max_right _ _) hxy
    show z kxy • ((x + y : TorsA) : Circ) = z kx • (x : Circ) + z ky • (y : Circ)
    rw [zsmul_eq hM hz hxy hxyK, zsmul_eq hM hz hx hxK, zsmul_eq hM hz hy hyK,
      AddSubgroup.coe_add, smul_add]

lemma zetaHom_apply (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (hM : ∀ n, M n ∣ M (n + 1)) (z : ℕ → ℤ) (hz : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k)
    (x : TorsA) {k : ℕ} (hk : M k • (x : Circ) = 0) :
    zetaHom hnull hM z hz x = z k • (x : Circ) :=
  zsmul_eq hM hz (Classical.choose_spec (exists_k hnull x)) hk

end zeta

end LeanCheck
