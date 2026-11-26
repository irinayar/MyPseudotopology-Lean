import Mathlib
import LeanCheck.PGThreeOne

/-!
# PGthree: an ultrafilter without a coreflection on every group with an infinite direct sum (Lean check)

Scope. Section 9 of the third article (`PGthree.tex`).

* `finite_bogolyubov_gen` : Bogolyubov's lemma in a finite abelian group;
* `mem_bohr_of_approx` : the passage to a Bohr neighbourhood of `0` by taking limits of characters;
* `bog_int`, `bog_tor` : in `ℤ` and in a direct sum of cyclic groups of prime orders, there is an idempotent
  ultrafilter `q` such that for every `E ∈ q` the set `E + E - E - E` is a Bohr neighbourhood of `0`;
* `abstract_no_coreflection` : the construction for a direct sum of groups with such ultrafilters and with supports;
* `no_coreflection_of_independent` : if an abelian group contains a sequence of independent nonzero elements, there is
  a nonprincipal ultrafilter on it whose PG has unique limits and no coarsest symmetric halvable null filter
  containing `0` in its members.

No set-theoretic hypothesis is used. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Groups

open Sel PG.Idem PG.Words PG.Bohr PG.One

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

/-! ### Bogolyubov's lemma in a finite abelian group -/

section Finite

variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

noncomputable def fh (D : Finset A) (χ : AddChar A ℂ) : ℂ := ∑ x ∈ D, χ x

theorem normSq_fh (D : Finset A) (χ : AddChar A ℂ) :
    ((Complex.normSq (fh D χ) : ℝ) : ℂ) = ∑ p ∈ D ×ˢ D, χ (p.1 - p.2) := by
  rw [← Complex.mul_conj]
  unfold fh
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

theorem parseval_gen (D : Finset A) :
    (∑ χ : AddChar A ℂ, Complex.normSq (fh D χ)) = (Fintype.card A : ℝ) * D.card := by
  have h : (∑ χ : AddChar A ℂ, ((Complex.normSq (fh D χ) : ℝ) : ℂ))
      = (Fintype.card A : ℂ) * (D.card : ℂ) := by
    simp only [normSq_fh]
    rw [Finset.sum_comm]
    simp only [AddChar.sum_apply_eq_ite]
    rw [Finset.sum_product]
    have h1 : ∀ x ∈ D, (∑ y ∈ D, (if x - y = 0 then (Fintype.card A : ℂ) else 0)) = (Fintype.card A : ℂ) := by
      intro x hx
      simp only [sub_eq_zero]
      rw [Finset.sum_ite_eq D x (fun _ => (Fintype.card A : ℂ)), if_pos hx]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact_mod_cast h

theorem rep_of_ne_zero (D : Finset A) (z : A)
    (h : (∑ χ : AddChar A ℂ, ((Complex.normSq (fh D χ) : ℝ) : ℂ) ^ 2 * χ z) ≠ 0) :
    ∃ a ∈ D, ∃ b ∈ D, ∃ c ∈ D, ∃ d ∈ D, z = a + b - c - d := by
  by_contra hno
  apply h
  have e : ∀ χ : AddChar A ℂ, ((Complex.normSq (fh D χ) : ℝ) : ℂ) ^ 2 * χ z
      = ∑ p ∈ D ×ˢ D, ∑ r ∈ D ×ˢ D, χ (p.1 - p.2 + (r.1 - r.2) + z) := by
    intro χ
    rw [sq, normSq_fh, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun r hr => ?_)
  rw [AddChar.sum_apply_eq_ite, if_neg]
  intro h0
  rw [Finset.mem_product] at hp hr
  refine hno ⟨p.2, hp.2, r.2, hr.2, p.1, hp.1, r.1, hr.1, ?_⟩
  have h1 : z = -(p.1 - p.2 + (r.1 - r.2)) := eq_neg_of_add_eq_zero_right h0
  rw [h1]
  abel

theorem finite_bogolyubov_gen (D : Finset A) (β : ℝ) (hβ : 0 < β) (hD : β * Fintype.card A ≤ D.card) :
    ∃ R : Finset (AddChar A ℂ), (R.card : ℝ) ≤ 2 / β ^ 2 ∧
      ∀ z : A, (∀ χ ∈ R, 0 ≤ (χ z).re) → ∃ a ∈ D, ∃ b ∈ D, ∃ c ∈ D, ∃ d ∈ D, z = a + b - c - d := by
  classical
  set N : ℝ := (Fintype.card A : ℝ) with hN
  set m : ℝ := (D.card : ℝ) with hm
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Fintype.card_pos
  have hmpos : 0 < m := lt_of_lt_of_le (mul_pos hβ hNpos) hD
  set τ : ℝ := m ^ 3 / (2 * N) with hτ
  have hτpos : 0 < τ := by positivity
  set g : AddChar A ℂ → ℝ := fun χ => Complex.normSq (fh D χ) with hg
  have hgnn : ∀ χ, 0 ≤ g χ := fun χ => Complex.normSq_nonneg _
  set R : Finset (AddChar A ℂ) := Finset.univ.filter (fun χ => χ ≠ 1 ∧ τ ≤ g χ) with hR
  have hpar : (∑ χ : AddChar A ℂ, g χ) = N * m := parseval_gen D
  refine ⟨R, ?_, fun z hz => ?_⟩
  · have h1 : (R.card : ℝ) * τ ≤ N * m := by
      rw [← hpar]
      calc (R.card : ℝ) * τ = ∑ _χ ∈ R, τ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ χ ∈ R, g χ := Finset.sum_le_sum (fun χ hχ => (Finset.mem_filter.1 hχ).2.2)
        _ ≤ ∑ χ : AddChar A ℂ, g χ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun χ _ _ => hgnn χ)
    have h2 : (R.card : ℝ) * m ^ 2 ≤ 2 * N ^ 2 := by
      have h3 : (R.card : ℝ) * m ^ 3 ≤ (N * m) * (2 * N) := by
        have h4 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * N)
        have e : (R.card : ℝ) * τ * (2 * N) = (R.card : ℝ) * m ^ 3 := by
          rw [hτ]
          field_simp
        rwa [e] at h4
      have h5 : ((R.card : ℝ) * m ^ 2) * m ≤ (2 * N ^ 2) * m := by
        calc ((R.card : ℝ) * m ^ 2) * m = (R.card : ℝ) * m ^ 3 := by ring
          _ ≤ (N * m) * (2 * N) := h3
          _ = (2 * N ^ 2) * m := by ring
      exact le_of_mul_le_mul_right h5 hmpos
    rw [le_div_iff₀ (by positivity)]
    have h6 : (R.card : ℝ) * (β * N) ^ 2 ≤ 2 * N ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hβ hNpos).le hD 2)
        (Nat.cast_nonneg _)) h2
    have h7 : ((R.card : ℝ) * β ^ 2) * N ^ 2 ≤ 2 * N ^ 2 := by
      calc ((R.card : ℝ) * β ^ 2) * N ^ 2 = (R.card : ℝ) * (β * N) ^ 2 := by ring
        _ ≤ 2 * N ^ 2 := h6
    exact le_of_mul_le_mul_right h7 (by positivity)
  · refine rep_of_ne_zero D z (fun h0 => ?_)
    have hre : (∑ χ : AddChar A ℂ, ((g χ : ℝ) : ℂ) ^ 2 * χ z).re = ∑ χ : AddChar A ℂ, g χ ^ 2 * (χ z).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have hone : g 1 = m ^ 2 := by
      have e : fh D (1 : AddChar A ℂ) = (D.card : ℂ) := by
        unfold fh
        simp
      show Complex.normSq (fh D 1) = m ^ 2
      rw [e, Complex.normSq_natCast, hm, sq]
    have key : ∀ χ : AddChar A ℂ, (if χ = 1 then m ^ 4 else 0) - τ * g χ ≤ g χ ^ 2 * (χ z).re := by
      intro χ
      have hnn : 0 ≤ τ * g χ := mul_nonneg hτpos.le (hgnn χ)
      by_cases h1 : χ = 1
      · rw [if_pos h1, h1, hone, AddChar.one_apply, Complex.one_re, mul_one]
        rw [h1, hone] at hnn
        nlinarith
      · rw [if_neg h1, zero_sub]
        by_cases hR' : χ ∈ R
        · have h2 : 0 ≤ g χ ^ 2 * (χ z).re := mul_nonneg (sq_nonneg _) (hz χ hR')
          linarith
        · have hlt : g χ < τ := by
            by_contra hge
            exact hR' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, not_lt.1 hge⟩)
          have h2 : -1 ≤ (χ z).re := by
            have h3 := Complex.abs_re_le_norm (χ z)
            rw [AddChar.norm_apply] at h3
            exact (abs_le.1 h3).1
          have h4 : -(g χ ^ 2) ≤ g χ ^ 2 * (χ z).re := by
            have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (g χ))
            rwa [mul_neg_one] at h5
          have h6 : g χ ^ 2 ≤ τ * g χ := by
            rw [sq]
            exact mul_le_mul_of_nonneg_right hlt.le (hgnn χ)
          linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun χ (_ : χ ∈ Finset.univ) => key χ)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (1 : AddChar A ℂ) (fun _ => m ^ 4),
      if_pos (Finset.mem_univ _), ← Finset.mul_sum, hpar, ← hre] at hsum
    have e : m ^ 4 - τ * (N * m) = m ^ 4 / 2 := by
      rw [hτ]
      field_simp
      ring
    rw [e] at hsum
    have h8 : (∑ χ : AddChar A ℂ, ((g χ : ℝ) : ℂ) ^ 2 * χ z) = 0 := h0
    rw [h8, Complex.zero_re] at hsum
    have h9 : 0 < m ^ 4 / 2 := by positivity
    linarith

end Finite

/-! ### Limits of characters -/

theorem mem_bohr_of_approx {C : Type} [AddCommGroup C] (w : Ultrafilter ℕ) (d : ℕ)
    (ψ : ℕ → Fin d → C → Circle)
    (hadd : ∀ j z z', ∀ᶠ n in (w : Filter ℕ), ψ n j (z + z') = ψ n j z * ψ n j z')
    (T : Set C) (hT : ∀ z, ∀ᶠ n in (w : Filter ℕ), (∀ j, 0 < ((ψ n j z : Circle) : ℂ).re) → z ∈ T) :
    T ∈ comap (iota (G := C)) (𝓝 0) := by
  have hlim : ∀ (j : Fin d) (z : C), ∃ c : Circle, Tendsto (fun n => ψ n j z) (w : Filter ℕ) (𝓝 c) := by
    intro j z
    obtain ⟨c, _, hc⟩ := (isCompact_univ (X := Circle)).ultrafilter_le_nhds
      (w.map (fun n => ψ n j z)) (by simp)
    exact ⟨c, hc⟩
  choose Ψ hΨ using hlim
  have hmul : ∀ j z z', Ψ j (z + z') = Ψ j z * Ψ j z' := by
    intro j z z'
    refine tendsto_nhds_unique (hΨ j (z + z')) ?_
    refine ((hΨ j z).mul (hΨ j z')).congr' ?_
    filter_upwards [hadd j z z'] with n hn using hn.symm
  set e := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) with he
  have he' : ∀ x : UnitAddCircle, e x = AddCircle.toCircle x := fun x => AddCircle.homeomorphCircle_apply _ x
  have hχadd : ∀ j z z', e.symm (Ψ j (z + z')) = e.symm (Ψ j z) + e.symm (Ψ j z') := by
    intro j z z'
    apply e.injective
    rw [e.apply_symm_apply, he', AddCircle.toCircle_add, ← he', ← he', e.apply_symm_apply, e.apply_symm_apply]
    exact hmul j z z'
  let χ : Fin d → (C →+ UnitAddCircle) := fun j => AddMonoidHom.mk' (fun z => e.symm (Ψ j z)) (hχadd j)
  set W : Set (Circles C) := ⋂ j : Fin d, {f | 0 < ((e (f (χ j)) : Circle) : ℂ).re} with hW
  have hWo : IsOpen W := by
    refine isOpen_iInter_of_finite (fun j => ?_)
    refine isOpen_lt continuous_const ?_
    exact Complex.continuous_re.comp (continuous_subtype_val.comp (e.continuous.comp (continuous_apply (χ j))))
  have h0 : (0 : Circles C) ∈ W := by
    refine mem_iInter.2 (fun j => ?_)
    show 0 < ((e (0 : UnitAddCircle) : Circle) : ℂ).re
    rw [he', AddCircle.toCircle_zero]
    simp
  refine mem_comap.2 ⟨W, hWo.mem_nhds h0, fun z hz => ?_⟩
  have hpos : ∀ j, 0 < ((Ψ j z : Circle) : ℂ).re := by
    intro j
    have h1 : 0 < ((e (e.symm (Ψ j z)) : Circle) : ℂ).re := mem_iInter.1 hz j
    rwa [e.apply_symm_apply] at h1
  have hev : ∀ᶠ n in (w : Filter ℕ), ∀ j, 0 < ((ψ n j z : Circle) : ℂ).re := by
    rw [eventually_all]
    intro j
    have h2 : Tendsto (fun n => ((ψ n j z : Circle) : ℂ).re) (w : Filter ℕ) (𝓝 ((Ψ j z : Circle) : ℂ).re) :=
      (Complex.continuous_re.comp continuous_subtype_val).continuousAt.tendsto.comp (hΨ j z)
    exact h2.eventually (lt_mem_nhds (hpos j))
  obtain ⟨n, h1, h2⟩ := (hev.and (hT z)).exists
  exact h2 h1

/-- The passage from finite levels to a Bohr neighbourhood. -/
theorem bohr_of_levels {C : Type} [AddCommGroup C] (V : ℕ → Type) [∀ n, AddCommGroup (V n)] [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] (ρ : ∀ n, C → V n) (D : ∀ n, Finset (V n)) (good : Set ℕ) (hinf : good.Infinite)
    (β : ℝ) (hβ : 0 < β) (hD : ∀ n ∈ good, β * Fintype.card (V n) ≤ (D n).card)
    (hρ : ∀ z z' : C, ∀ᶠ n in atTop, ρ n (z + z') = ρ n z + ρ n z') (T : Set C)
    (hT : ∀ z : C, ∀ᶠ n in atTop, (∃ a ∈ D n, ∃ b ∈ D n, ∃ c ∈ D n, ∃ d ∈ D n, ρ n z = a + b - c - d) → z ∈ T) :
    T ∈ comap (iota (G := C)) (𝓝 0) := by
  classical
  set d : ℕ := ⌊2 / β ^ 2⌋₊ with hd
  have hR : ∀ n, ∃ R : Finset (AddChar (V n) ℂ), n ∈ good → R.card ≤ d ∧
      ∀ z : V n, (∀ χ ∈ R, 0 ≤ (χ z).re) → ∃ a ∈ D n, ∃ b ∈ D n, ∃ c ∈ D n, ∃ e ∈ D n, z = a + b - c - e := by
    intro n
    by_cases hn : n ∈ good
    · obtain ⟨R, h1, h2⟩ := finite_bogolyubov_gen (D n) β hβ (hD n hn)
      exact ⟨R, fun _ => ⟨Nat.le_floor h1, h2⟩⟩
    · exact ⟨∅, fun h => absurd h hn⟩
  choose R hR using hR
  let χ : (n : ℕ) → Fin d → AddChar (V n) ℂ := fun n j =>
    if h : (j : ℕ) < (R n).card then ((R n).equivFin.symm ⟨j, h⟩ : AddChar (V n) ℂ) else 1
  let ψ : ℕ → Fin d → C → Circle := fun n j z =>
    ⟨χ n j (ρ n z), mem_sphere_zero_iff_norm.2 (AddChar.norm_apply _ _)⟩
  have hne : (atTop ⊓ 𝓟 good : Filter ℕ).NeBot := by
    rw [inf_principal_neBot_iff]
    intro U hU
    obtain ⟨N, hN⟩ := mem_atTop_sets.1 hU
    obtain ⟨n, hn, h1⟩ := hinf.exists_gt N
    exact ⟨n, hN n h1.le, hn⟩
  set w : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 good) with hw
  have hwle : (w : Filter ℕ) ≤ atTop ⊓ 𝓟 good := Ultrafilter.of_le _
  have hat : (w : Filter ℕ) ≤ atTop := hwle.trans inf_le_left
  have hg : ∀ᶠ n in (w : Filter ℕ), n ∈ good := (hwle.trans inf_le_right) (mem_principal_self _)
  refine mem_bohr_of_approx w d ψ (fun j z z' => ?_) T (fun z => ?_)
  · filter_upwards [(hρ z z').filter_mono hat] with n hn
    refine Subtype.ext ?_
    show χ n j (ρ n (z + z')) = χ n j (ρ n z) * χ n j (ρ n z')
    rw [hn, AddChar.map_add_eq_mul]
  · filter_upwards [hg, (hT z).filter_mono hat] with n hn hTn hpos
    obtain ⟨hcard, hrep⟩ := hR n hn
    refine hTn (hrep (ρ n z) (fun χ0 hχ0 => ?_))
    set k := (R n).equivFin ⟨χ0, hχ0⟩ with hk
    have hkd : (k : ℕ) < d := lt_of_lt_of_le k.2 hcard
    have h1 : χ n ⟨k, hkd⟩ = χ0 := by
      show (if h : (k : ℕ) < (R n).card then ((R n).equivFin.symm ⟨k, h⟩ : AddChar (V n) ℂ) else 1) = χ0
      rw [dif_pos k.2]
      have h2 : (⟨(k : ℕ), k.2⟩ : Fin (R n).card) = k := Fin.eta _ _
      rw [h2, hk, Equiv.symm_apply_apply]
    have h3 : 0 < (χ n ⟨k, hkd⟩ (ρ n z)).re := hpos ⟨k, hkd⟩
    rw [h1] at h3
    exact h3.le

/-! ### Idempotents of positive density -/

section Density

variable {C : Type} [AddCommGroup C] (F : ℕ → Finset C)

open Classical in
noncomputable def cntF (s : Set C) (n : ℕ) : ℕ := ((F n).filter (fun x => x ∈ s)).card

def DenseF (s : Set C) : Prop := ∃ α : ℝ, 0 < α ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ α * (F n).card ≤ (cntF F s n : ℝ)

theorem cntF_mono {s t : Set C} (h : s ⊆ t) (n : ℕ) : cntF F s n ≤ cntF F t n := by
  classical
  refine Finset.card_le_card (fun x hx => ?_)
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem denseF_mono {s t : Set C} (h : s ⊆ t) (hs : DenseF F s) : DenseF F t := by
  obtain ⟨α, hα, H⟩ := hs
  refine ⟨α, hα, fun N => ?_⟩
  obtain ⟨n, hn, h1⟩ := H N
  exact ⟨n, hn, h1.trans (by exact_mod_cast cntF_mono F h n)⟩

theorem denseF_union (hF : ∀ n, (F n).Nonempty) {s t : Set C} (h : DenseF F (s ∪ t)) :
    DenseF F s ∨ DenseF F t := by
  classical
  by_contra hno
  rw [not_or] at hno
  obtain ⟨α, hα, H⟩ := h
  have aux : ∀ u : Set C, ¬ DenseF F u → ∃ N : ℕ, ∀ n, N ≤ n → (cntF F u n : ℝ) < α / 2 * (F n).card := by
    intro u hu
    by_contra hc
    refine hu ⟨α / 2, half_pos hα, fun N => ?_⟩
    by_contra h2
    exact hc ⟨N, fun n hn => not_le.1 (fun h3 => h2 ⟨n, hn, h3⟩)⟩
  obtain ⟨N1, h1⟩ := aux s hno.1
  obtain ⟨N2, h2⟩ := aux t hno.2
  obtain ⟨n, hn, h3⟩ := H (max N1 N2)
  have h4 : cntF F (s ∪ t) n ≤ cntF F s n + cntF F t n := by
    refine le_trans (Finset.card_le_card (fun x hx => ?_)) (Finset.card_union_le _ _)
    simp only [Finset.mem_union, Finset.mem_filter, mem_union] at hx ⊢
    rcases hx.2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  have h5 : (cntF F (s ∪ t) n : ℝ) ≤ (cntF F s n : ℝ) + cntF F t n := by exact_mod_cast h4
  have h6 := h1 n (le_trans (le_max_left _ _) hn)
  have h7 := h2 n (le_trans (le_max_right _ _) hn)
  linarith

theorem denseF_univ : DenseF F (univ : Set C) := by
  classical
  refine ⟨1, one_pos, fun N => ⟨N, le_rfl, ?_⟩⟩
  have h : cntF F (univ : Set C) N = (F N).card := by
    unfold cntF
    simp
  rw [h, one_mul]

theorem not_denseF_zero (hgrow : ∀ M : ℕ, ∃ N, ∀ n, N ≤ n → M < (F n).card) : ¬ DenseF F ({0} : Set C) := by
  classical
  rintro ⟨α, hα, H⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / α)
  obtain ⟨N, hN⟩ := hgrow M
  obtain ⟨n, hn, h1⟩ := H N
  have h2 : cntF F ({0} : Set C) n ≤ 1 := by
    refine Finset.card_le_one.2 (fun x hx y hy => ?_)
    rw [Finset.mem_filter, mem_singleton_iff] at hx hy
    rw [hx.2, hy.2]
  have h3 : (M : ℝ) < (F n).card := by exact_mod_cast hN n hn
  have h4 : 1 < (F n).card * α := (div_lt_iff₀ hα).1 (lt_trans hM h3)
  have h5 : (cntF F ({0} : Set C) n : ℝ) ≤ 1 := by exact_mod_cast h2
  nlinarith

theorem exists_idem_dense (hF : ∀ n, (F n).Nonempty) (hgrow : ∀ M : ℕ, ∃ N, ∀ n, N ≤ n → M < (F n).card)
    (htrans : ∀ (a : C) (s : Set C), DenseF F ((fun z => a + z) ⁻¹' s) → DenseF F s) :
    ∃ q : Ultrafilter C, q + q = q ∧ ∀ s ∈ q, DenseF F s := by
  let Fi : Filter C :=
    { sets := {s | ¬ DenseF F sᶜ}
      univ_sets := by
        show ¬ DenseF F (univ : Set C)ᶜ
        rw [compl_univ]
        intro h
        exact not_denseF_zero F hgrow (denseF_mono F (empty_subset _) h)
      sets_of_superset := fun hx hxy h => hx (denseF_mono F (compl_subset_compl.2 hxy) h)
      inter_sets := fun {x y} hx hy h => by
        rw [compl_inter] at h
        rcases denseF_union F hF h with h | h
        · exact hx h
        · exact hy h }
  have hFi : Fi.NeBot := by
    refine ⟨fun h => ?_⟩
    have h1 : (∅ : Set C) ∈ Fi := by rw [h]; exact mem_bot
    have h2 : ¬ DenseF F (∅ : Set C)ᶜ := h1
    rw [compl_empty] at h2
    exact h2 (denseF_univ F)
  set X : Set (Ultrafilter C) := {p | ∀ s ∈ p, DenseF F s} with hX
  have hne : X.Nonempty := by
    refine ⟨Ultrafilter.of Fi, fun s hs => ?_⟩
    by_contra h
    have h1 : sᶜ ∈ Fi := by
      show ¬ DenseF F sᶜᶜ
      rwa [compl_compl]
    exact Ultrafilter.compl_mem_iff_notMem.1 (Ultrafilter.of_le Fi h1) hs
  have hclosed : IsClosed X := by
    have h1 : X = ⋂ s ∈ {s : Set C | ¬ DenseF F s}, {p : Ultrafilter C | sᶜ ∈ p} := by
      ext p
      rw [mem_iInter₂]
      constructor
      · intro hp s hs
        exact Ultrafilter.compl_mem_iff_notMem.2 (fun h => hs (hp s h))
      · intro hp s hs
        by_contra h
        exact Ultrafilter.compl_mem_iff_notMem.1 (hp s h) hs
    rw [h1]
    exact isClosed_biInter (fun s _ => ultrafilter_isClosed_basic _)
  have hadd : ∀ p ∈ X, ∀ r ∈ X, p + r ∈ X := by
    intro p _ r hr s hs
    rw [PG.Idem.mem_add] at hs
    obtain ⟨x, hx⟩ := Ultrafilter.nonempty_of_mem hs
    have hx' : {z : C | x + z ∈ s} ∈ r := hx
    exact htrans x s (hr _ hx')
  obtain ⟨q, hqX, hqq⟩ := exists_idempotent_in_compact_add_subsemigroup
    (M := Ultrafilter C) Ultrafilter.continuous_add_left X hne hclosed.isCompact hadd
  exact ⟨q, hqq, hqX⟩

end Density

/-- An idempotent ultrafilter contains every subgroup of finite index. -/
theorem idem_mem_finiteIndex {C : Type} [AddCommGroup C] (q : Ultrafilter C) (hq : q + q = q)
    (W : AddSubgroup C) [W.FiniteIndex] : (W : Set C) ∈ q := by
  have hmap := map_add_hom (QuotientAddGroup.mk' W) q q
  rw [hq] at hmap
  obtain ⟨c, _, hc⟩ := Ultrafilter.eq_pure_of_finite_mem (f := q.map (QuotientAddGroup.mk' W))
    finite_univ Filter.univ_mem
  rw [hc] at hmap
  have hsum : ((pure c : Ultrafilter (C ⧸ W)) + pure c) = pure (c + c) := by
    refine Ultrafilter.ext (fun s => ?_)
    rw [PG.Idem.mem_add]
    rfl
  rw [hsum] at hmap
  have hc0 : c = 0 := add_eq_left.1 (Ultrafilter.pure_injective hmap).symm
  have h1 : ({c} : Set (C ⧸ W)) ∈ q.map (QuotientAddGroup.mk' W) := by
    rw [hc]
    exact rfl
  refine Filter.mem_of_superset (Ultrafilter.mem_map.1 h1) (fun z hz => ?_)
  have h3 : (z : C ⧸ W) = 0 := Eq.trans hz hc0
  exact (QuotientAddGroup.eq_zero_iff z).1 h3

/-- The sets `E + E - E - E`. -/
def dsum {C : Type} [AddCommGroup C] (E : Set C) : Set C :=
  {z | ∃ a ∈ E, ∃ b ∈ E, ∃ c ∈ E, ∃ d ∈ E, z = a + b - c - d}

/-! ### The integers -/

/-- `x` has no ternary digit at position `t` (up to the carries). -/
def Flat (t : ℕ) (x : ℤ) : Prop := ∃ k : ℤ, 6 * |x - 3 ^ (t + 1) * k| < 3 ^ (t + 1)

theorem three_pow_gt (n : ℕ) : 6 * (n : ℤ) < 3 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have e : (3 : ℤ) ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by ring
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have : (1 : ℤ) ≤ n := by exact_mod_cast h
      push_cast
      rw [e]
      omega

open Classical in
noncomputable def tsupp (x : ℤ) : Finset ℕ := (Finset.range (x.natAbs + 1)).filter (fun t => ¬ Flat t x)

theorem flat_of_large (x : ℤ) (t : ℕ) (h : x.natAbs ≤ t) : Flat t x := by
  refine ⟨0, ?_⟩
  rw [mul_zero, sub_zero]
  have h1 : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
  have h2 := three_pow_gt t
  have h3 : (x.natAbs : ℤ) ≤ t := by exact_mod_cast h
  omega

theorem mem_tsupp (x : ℤ) (t : ℕ) : t ∈ tsupp x ↔ ¬ Flat t x := by
  classical
  unfold tsupp
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra h1
  exact h (flat_of_large x t (by omega))

theorem flat_zero (t : ℕ) : Flat t 0 := flat_of_large 0 t (Nat.zero_le _)

theorem tsupp_zero : tsupp 0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun t ht => ?_)
  exact (mem_tsupp 0 t).1 ht (flat_zero t)

theorem tsupp_nonempty (x : ℤ) (hx : x ≠ 0) : (tsupp x).Nonempty := by
  classical
  have hex : ∃ t : ℕ, ¬ (3 : ℤ) ^ (t + 1) ∣ x := by
    refine ⟨x.natAbs, fun h => hx ?_⟩
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    have h1 : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
    have h2 := three_pow_gt x.natAbs
    omega
  set t := Nat.find hex with ht
  have h1 : ¬ (3 : ℤ) ^ (t + 1) ∣ x := Nat.find_spec hex
  have h2 : (3 : ℤ) ^ t ∣ x := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, pow_zero]
      exact one_dvd _
    · have h3 := Nat.find_min hex (show t - 1 < t by omega)
      rw [not_not, show t - 1 + 1 = t by omega] at h3
      exact h3
  refine ⟨t, (mem_tsupp x t).2 ?_⟩
  rintro ⟨k, hk⟩
  obtain ⟨v, hv⟩ := h2
  have e : x - 3 ^ (t + 1) * k = 3 ^ t * (v - 3 * k) := by
    rw [hv]
    ring
  have h4 : v - 3 * k ≠ 0 := by
    intro h5
    refine h1 ⟨k, ?_⟩
    rw [h5, mul_zero] at e
    exact sub_eq_zero.1 e
  have h6 : (1 : ℤ) ≤ |v - 3 * k| := Int.one_le_abs h4
  have hp : (0 : ℤ) < 3 ^ t := by positivity
  have h7 : (3 : ℤ) ^ t ≤ |x - 3 ^ (t + 1) * k| := by
    rw [e, abs_mul, abs_of_pos hp]
    exact le_mul_of_one_le_right hp.le h6
  have h8 : (3 : ℤ) ^ (t + 1) = 3 * 3 ^ t := by ring
  omega

theorem flat_window (x : ℤ) (t : ℕ) : ∀ j, j ≤ t → (∀ s, s ≤ t → t ≤ s + j → Flat s x) →
    ∃ k : ℤ, 6 * 3 ^ j * |x - 3 ^ (t + 1) * k| < 3 ^ (t + 1) := by
  intro j
  induction j with
  | zero =>
    intro _ h
    obtain ⟨k, hk⟩ := h t le_rfl (by omega)
    exact ⟨k, by simpa using hk⟩
  | succ j ih =>
    intro hj h
    obtain ⟨k, hk⟩ := ih (by omega) (fun s hs1 hs2 => h s hs1 (by omega))
    obtain ⟨k', hk'⟩ := h (t - (j + 1)) (by omega) (by omega)
    refine ⟨k, ?_⟩
    have e1 : t - (j + 1) + 1 = t - j := by omega
    rw [e1] at hk'
    set P : ℤ := 3 ^ (t - j) with hP
    have hPpos : 0 < P := by positivity
    have e2 : (3 : ℤ) ^ (t + 1) = P * 3 ^ (j + 1) := by
      rw [hP, ← pow_add]
      congr 1
      omega
    set r : ℤ := x - 3 ^ (t + 1) * k with hr
    set r' : ℤ := x - P * k' with hr'
    have h1 : 2 * |r| < P := by
      have h2 : 3 ^ j * (6 * |r|) < 3 ^ j * (3 * P) := by
        calc 3 ^ j * (6 * |r|) = 6 * 3 ^ j * |r| := by ring
          _ < 3 ^ (t + 1) := hk
          _ = 3 ^ j * (3 * P) := by rw [e2]; ring
      have h3 := lt_of_mul_lt_mul_left h2 (by positivity)
      omega
    have h4 : r = r' := by
      have h5 : P ∣ r - r' := by
        refine ⟨k' - 3 ^ (j + 1) * k, ?_⟩
        rw [hr, hr', e2]
        ring
      have h6 : |r - r'| < P := by
        have := abs_sub r r'
        omega
      exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h5 h6)
    have h7 : 6 * |r| < P := by rw [h4]; exact hk'
    calc 6 * 3 ^ (j + 1) * |r| = 3 ^ (j + 1) * (6 * |r|) := by ring
      _ < 3 ^ (j + 1) * P := mul_lt_mul_of_pos_left h7 (by positivity)
      _ = 3 ^ (t + 1) := by rw [e2]; ring

theorem tsupp_window (L : ℕ) (ε : Fin L → ℤ) (a : Fin L → ℤ) (hε : ∀ l, ε l = 1 ∨ ε l = -1) (t : ℕ)
    (ht : t ∈ tsupp (∑ l, ε l • a l)) : ∃ l, ∃ s ∈ tsupp (a l), s ≤ t ∧ t ≤ s + L := by
  by_contra hno
  apply (mem_tsupp _ _).1 ht
  have hflat : ∀ l s, s ≤ t → t ≤ s + L → Flat s (a l) := by
    intro l s h1 h2
    by_contra h
    exact hno ⟨l, s, (mem_tsupp _ _).2 h, h1, h2⟩
  have key : ∀ (j : ℕ), j ≤ t → j ≤ L → ∀ l, ∃ k : ℤ, 6 * 3 ^ j * |a l - 3 ^ (t + 1) * k| < 3 ^ (t + 1) :=
    fun j hj hjL l => flat_window (a l) t j hj (fun s h1 h2 => hflat l s h1 (by omega))
  have habs : ∀ l (k : ℤ), |ε l * (a l - 3 ^ (t + 1) * k)| = |a l - 3 ^ (t + 1) * k| := by
    intro l k
    rcases hε l with h | h <;> rw [h] <;> simp [abs_sub_comm]
  have hsum : ∀ k : Fin L → ℤ, (∑ l, ε l • a l) - 3 ^ (t + 1) * (∑ l, ε l * k l)
      = ∑ l, ε l * (a l - 3 ^ (t + 1) * k l) := by
    intro k
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_eq_mul]
    ring
  by_cases hLt : L ≤ t
  · choose k hk using key L hLt le_rfl
    refine ⟨∑ l, ε l * k l, ?_⟩
    rw [hsum]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL
      simp
    · have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
      have h1 : 3 ^ L * (6 * |∑ l, ε l * (a l - 3 ^ (t + 1) * k l)|) < 3 ^ L * 3 ^ (t + 1) := by
        have h2 : |∑ l, ε l * (a l - 3 ^ (t + 1) * k l)| ≤ ∑ l, |a l - 3 ^ (t + 1) * k l| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          exact Finset.sum_congr rfl (fun l _ => habs l (k l))
        have h3 : (∑ l : Fin L, 6 * 3 ^ L * |a l - 3 ^ (t + 1) * k l|) < ∑ _l : Fin L, (3 : ℤ) ^ (t + 1) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun l _ => hk l)
        have h4 : (L : ℤ) ≤ 3 ^ L := by
          exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le
        calc 3 ^ L * (6 * |∑ l, ε l * (a l - 3 ^ (t + 1) * k l)|)
            ≤ 3 ^ L * (6 * ∑ l, |a l - 3 ^ (t + 1) * k l|) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity)
          _ = ∑ l : Fin L, 6 * 3 ^ L * |a l - 3 ^ (t + 1) * k l| := by
              rw [Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun l _ => by ring)
          _ < ∑ _l : Fin L, (3 : ℤ) ^ (t + 1) := h3
          _ = (L : ℤ) * 3 ^ (t + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ 3 ^ L * 3 ^ (t + 1) := mul_le_mul_of_nonneg_right h4 (by positivity)
      exact lt_of_mul_lt_mul_left h1 (by positivity)
  · choose k hk using key t le_rfl (by omega)
    refine ⟨∑ l, ε l * k l, ?_⟩
    rw [hsum]
    have h0 : ∀ l, a l - 3 ^ (t + 1) * k l = 0 := by
      intro l
      have h1 := hk l
      have h2 : 3 ^ t * (6 * |a l - 3 ^ (t + 1) * k l|) < 3 ^ t * 3 := by
        calc 3 ^ t * (6 * |a l - 3 ^ (t + 1) * k l|) = 6 * 3 ^ t * |a l - 3 ^ (t + 1) * k l| := by ring
          _ < 3 ^ (t + 1) := h1
          _ = 3 ^ t * 3 := by ring
      have h3 := lt_of_mul_lt_mul_left h2 (by positivity)
      have h4 : |a l - 3 ^ (t + 1) * k l| = 0 := by
        have := abs_nonneg (a l - 3 ^ (t + 1) * k l)
        omega
      exact abs_eq_zero.1 h4
    simp only [h0, mul_zero, Finset.sum_const_zero, abs_zero]
    positivity

def IntF (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

theorem IntF_card (n : ℕ) : (IntF n).card = 2 * n + 1 := by
  unfold IntF
  rw [Int.card_Icc]
  omega

theorem int_translate (a : ℤ) (s : Set ℤ) (h : DenseF IntF ((fun z => a + z) ⁻¹' s)) : DenseF IntF s := by
  classical
  obtain ⟨α, hα, H⟩ := h
  refine ⟨α / 2, half_pos hα, fun N => ?_⟩
  obtain ⟨n, hn, h1⟩ := H (max N a.natAbs)
  have hna : a.natAbs ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨n + a.natAbs, le_trans (le_trans (le_max_left _ _) hn) (Nat.le_add_right _ _), ?_⟩
  have h2 : cntF IntF ((fun z => a + z) ⁻¹' s) n ≤ cntF IntF s (n + a.natAbs) := by
    refine Finset.card_le_card_of_injOn (fun z => a + z) (fun z hz => ?_) (fun x _ y _ h => add_left_cancel h)
    rw [Finset.coe_filter] at hz ⊢
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, hz2⟩
    unfold IntF at hz1 ⊢
    rw [Finset.mem_Icc] at hz1 ⊢
    have h3 : |a| = (a.natAbs : ℤ) := (Int.natCast_natAbs a).symm
    have h4 := neg_abs_le a
    have h5 := le_abs_self a
    push_cast
    omega
  have h3 : (cntF IntF ((fun z => a + z) ⁻¹' s) n : ℝ) ≤ cntF IntF s (n + a.natAbs) := by exact_mod_cast h2
  have h4 : ((IntF (n + a.natAbs)).card : ℝ) ≤ 2 * (IntF n).card := by
    rw [IntF_card, IntF_card]
    exact_mod_cast (by omega : 2 * (n + a.natAbs) + 1 ≤ 2 * (2 * n + 1))
  have h5 := mul_le_mul_of_nonneg_left h4 (half_pos hα).le
  linarith

theorem bog_int : ∃ q : Ultrafilter ℤ, q + q = q ∧
    (∀ K : ℕ, {z : ℤ | z ≠ 0 ∧ ∀ s ∈ tsupp z, K < s} ∈ q) ∧
    ∀ E ∈ q, dsum E ∈ comap (iota (G := ℤ)) (𝓝 0) := by
  classical
  have hF : ∀ n, (IntF n).Nonempty := fun n => by
    rw [← Finset.card_pos, IntF_card]
    omega
  have hgrow : ∀ M : ℕ, ∃ N, ∀ n, N ≤ n → M < (IntF n).card := fun M =>
    ⟨M, fun n hn => by rw [IntF_card]; omega⟩
  obtain ⟨q, hq, hd⟩ := exists_idem_dense IntF hF hgrow int_translate
  refine ⟨q, hq, fun K => ?_, fun E hE => ?_⟩
  · have h0 : ({0} : Set ℤ)ᶜ ∈ q :=
      Ultrafilter.compl_mem_iff_notMem.2 (fun h => not_denseF_zero IntF hgrow (hd _ h))
    have hfi : (AddSubgroup.zmultiples ((3 : ℤ) ^ (K + 1))).FiniteIndex := by
      refine ⟨?_⟩
      rw [Int.index_zmultiples]
      exact Int.natAbs_ne_zero.2 (pow_ne_zero _ (by norm_num))
    have h1 := idem_mem_finiteIndex q hq (AddSubgroup.zmultiples ((3 : ℤ) ^ (K + 1)))
    refine Filter.mem_of_superset (Filter.inter_mem h0 h1) (fun z hz => ⟨hz.1, fun s hs => ?_⟩)
    by_contra hsK
    apply (mem_tsupp z s).1 hs
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hz.2
    have h2 : (3 : ℤ) ^ (s + 1) ∣ z := by
      refine dvd_trans (pow_dvd_pow 3 (show s + 1 ≤ K + 1 by omega)) ⟨m, ?_⟩
      rw [← hm, smul_eq_mul, mul_comm]
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [hk, sub_self, abs_zero, mul_zero]
    positivity
  · obtain ⟨α, hα, H⟩ := hd E hE
    set good : Set ℕ := {n | 1 ≤ n ∧ α * (IntF n).card ≤ (cntF IntF E n : ℝ)} with hgood
    have hinf : good.Infinite := by
      refine Set.infinite_of_forall_exists_gt (fun N => ?_)
      obtain ⟨n, hn, h1⟩ := H (N + 1)
      exact ⟨n, ⟨by omega, h1⟩, by omega⟩
    let ρ : ∀ n : ℕ, ℤ → ZMod (8 * n + 1) := fun n z => (z : ZMod (8 * n + 1))
    let D : ∀ n : ℕ, Finset (ZMod (8 * n + 1)) := fun n => ((IntF n).filter (fun x => x ∈ E)).image (ρ n)
    have hcongr : ∀ (n : ℕ) (x y : ℤ), ρ n x = ρ n y → |x - y| < 8 * (n : ℤ) + 1 → x = y := by
      intro n x y h h'
      have h1 : ((x - y : ℤ) : ZMod (8 * n + 1)) = 0 := by
        rw [Int.cast_sub, sub_eq_zero]
        exact h
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
      refine sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h2 ?_)
      push_cast
      exact h'
    have hIcc : ∀ n x, x ∈ IntF n → -(n : ℤ) ≤ x ∧ x ≤ n := fun n x hx => Finset.mem_Icc.1 hx
    refine bohr_of_levels (fun n => ZMod (8 * n + 1)) ρ D good hinf (α / 4) (by positivity) (fun n hn => ?_)
      (fun z z' => Filter.Eventually.of_forall (fun n => by simp only [ρ, Int.cast_add])) (dsum E) (fun z => ?_)
    · have hcard : (D n).card = cntF IntF E n := by
        refine Finset.card_image_of_injOn (fun x hx y hy h => hcongr n x y h ?_)
        have h1 := hIcc n x (Finset.mem_filter.1 hx).1
        have h2 := hIcc n y (Finset.mem_filter.1 hy).1
        rw [abs_lt]
        omega
      rw [hcard, ZMod.card]
      refine le_trans ?_ hn.2
      rw [IntF_card]
      have h3 : ((8 * n + 1 : ℕ) : ℝ) ≤ 4 * ((2 * n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 8 * n + 1 ≤ 4 * (2 * n + 1))
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ α / 4)
      linarith
    · filter_upwards [eventually_ge_atTop (z.natAbs + 1)] with n hn
      rintro ⟨a, ha, b, hb, c, hc, d, hdd, h⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hdd
      rw [Finset.mem_filter] at ha' hb' hc' hd'
      refine ⟨a', ha'.2, b', hb'.2, c', hc'.2, d', hd'.2, hcongr n _ _ ?_ ?_⟩
      · rw [h]
        simp only [ρ, Int.cast_add, Int.cast_sub]
      · have h1 := hIcc n _ ha'.1
        have h2 := hIcc n _ hb'.1
        have h3 := hIcc n _ hc'.1
        have h4 := hIcc n _ hd'.1
        have h5 : |z| = (z.natAbs : ℤ) := (Int.natCast_natAbs z).symm
        have h6 : -|z| ≤ z := neg_abs_le z
        have h7 : z ≤ |z| := le_abs_self z
        rw [abs_lt]
        omega

/-! ### Direct sums of cyclic groups of prime order -/

section Torsion

variable (p : ℕ → ℕ) [hp : ∀ k, Fact (p k).Prime]

abbrev Tor : Type := Π₀ k : ℕ, ZMod (p k)

instance (k : ℕ) : NeZero (p k) := ⟨(hp k).out.ne_zero⟩

abbrev Lev (n : ℕ) : Type := ∀ k : Fin n, ZMod (p k)

noncomputable def emT (n : ℕ) : Lev p n →+ Tor p :=
  ∑ k : Fin n, (DFinsupp.singleAddHom (fun j : ℕ => ZMod (p j)) (k : ℕ)).comp
    (Pi.evalAddMonoidHom (fun j : Fin n => ZMod (p j)) k)

def reT (n : ℕ) : Tor p →+ Lev p n where
  toFun z k := z (k : ℕ)
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp

theorem emT_apply (n : ℕ) (x : Lev p n) (j : ℕ) :
    emT p n x j = if h : j < n then x ⟨j, h⟩ else 0 := by
  unfold emT
  rw [AddMonoidHom.finset_sum_apply, DFinsupp.finsetSum_apply]
  by_cases h : j < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin n)]
    · show (DFinsupp.single (β := fun i : ℕ => ZMod (p i)) j (x ⟨j, h⟩)) j = x ⟨j, h⟩
      rw [DFinsupp.single_eq_same]
    · intro b _ hb
      show (DFinsupp.single (β := fun i : ℕ => ZMod (p i)) (b : ℕ) (x b)) j = 0
      exact DFinsupp.single_eq_of_ne (fun e => hb (Fin.ext e.symm))
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    show (DFinsupp.single (β := fun i : ℕ => ZMod (p i)) (b : ℕ) (x b)) j = 0
    exact DFinsupp.single_eq_of_ne (fun e => h (e ▸ b.2))

theorem emT_injective (n : ℕ) : Function.Injective (emT p n) := by
  intro x y h
  funext k
  have h1 := DFunLike.congr_fun h (k : ℕ)
  rwa [emT_apply, emT_apply, dif_pos k.2, dif_pos k.2] at h1

theorem emT_reT (n : ℕ) (z : Tor p) (hz : ∀ j, z j ≠ 0 → j < n) : emT p n (reT p n z) = z := by
  ext j
  rw [emT_apply]
  by_cases h : j < n
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    by_contra h'
    exact h (hz j (Ne.symm h'))

open Classical in
noncomputable def TorF (n : ℕ) : Finset (Tor p) := Finset.univ.image (emT p n)

theorem TorF_card (n : ℕ) : (TorF p n).card = Fintype.card (Lev p n) := by
  classical
  unfold TorF
  rw [Finset.card_image_of_injective _ (emT_injective p n), Finset.card_univ]

theorem bounded_support (z : Tor p) : ∃ N, ∀ j, z j ≠ 0 → j < N := by
  classical
  refine ⟨z.support.sup id + 1, fun j hj => ?_⟩
  have h1 : j ∈ z.support := DFinsupp.mem_support_iff.2 hj
  have h2 : j ≤ z.support.sup id := Finset.le_sup (f := id) h1
  omega

theorem tor_translate (a : Tor p) (s : Set (Tor p)) (h : DenseF (TorF p) ((fun z => a + z) ⁻¹' s)) :
    DenseF (TorF p) s := by
  classical
  obtain ⟨α, hα, H⟩ := h
  obtain ⟨M, hM⟩ := bounded_support p a
  refine ⟨α, hα, fun N => ?_⟩
  obtain ⟨n, hn, h1⟩ := H (max N M)
  refine ⟨n, le_trans (le_max_left _ _) hn, le_trans h1 ?_⟩
  have ha : emT p n (reT p n a) = a :=
    emT_reT p n a (fun j hj => lt_of_lt_of_le (hM j hj) (le_trans (le_max_right _ _) hn))
  have h2 : cntF (TorF p) ((fun z => a + z) ⁻¹' s) n ≤ cntF (TorF p) s n := by
    refine Finset.card_le_card_of_injOn (fun z => a + z) (fun z hz => ?_) (fun x _ y _ h => add_left_cancel h)
    rw [Finset.coe_filter] at hz ⊢
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, hz2⟩
    unfold TorF at hz1 ⊢
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hz1
    refine Finset.mem_image.2 ⟨reT p n a + x, Finset.mem_univ _, ?_⟩
    rw [map_add, ha]
  exact_mod_cast h2

theorem bog_tor : ∃ q : Ultrafilter (Tor p), q + q = q ∧
    (∀ K : ℕ, {z : Tor p | z ≠ 0 ∧ ∀ j, z j ≠ 0 → K < j} ∈ q) ∧
    ∀ E ∈ q, dsum E ∈ comap (iota (G := Tor p)) (𝓝 0) := by
  classical
  have hF : ∀ n, (TorF p n).Nonempty := fun n => by
    rw [← Finset.card_pos, TorF_card]
    exact Fintype.card_pos
  have hcardge : ∀ n, n < (TorF p n).card := by
    intro n
    rw [TorF_card, Fintype.card_pi]
    have h1 : ∀ k : Fin n, 2 ≤ Fintype.card (ZMod (p k)) := fun k => by
      rw [ZMod.card]
      exact (hp k).out.two_le
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ = ∏ _k : Fin n, 2 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ k : Fin n, Fintype.card (ZMod (p k)) := Finset.prod_le_prod' (fun k _ => h1 k)
  have hgrow : ∀ M : ℕ, ∃ N, ∀ n, N ≤ n → M < (TorF p n).card := fun M =>
    ⟨M, fun n hn => lt_of_le_of_lt hn (hcardge n)⟩
  obtain ⟨q, hq, hd⟩ := exists_idem_dense (TorF p) hF hgrow (tor_translate p)
  refine ⟨q, hq, fun K => ?_, fun E hE => ?_⟩
  · have h0 : ({0} : Set (Tor p))ᶜ ∈ q :=
      Ultrafilter.compl_mem_iff_notMem.2 (fun h => not_denseF_zero (TorF p) hgrow (hd _ h))
    have h1 := idem_mem_finiteIndex q hq (reT p (K + 1)).ker
    refine Filter.mem_of_superset (Filter.inter_mem h0 h1) (fun z hz => ⟨hz.1, fun j hj => ?_⟩)
    by_contra h
    have h2 : reT p (K + 1) z = 0 := hz.2
    exact hj (congrFun h2 ⟨j, by omega⟩)
  · obtain ⟨α, hα, H⟩ := hd E hE
    set good : Set ℕ := {n | α * (TorF p n).card ≤ (cntF (TorF p) E n : ℝ)} with hgood
    have hinf : good.Infinite := by
      refine Set.infinite_of_forall_exists_gt (fun N => ?_)
      obtain ⟨n, hn, h1⟩ := H (N + 1)
      exact ⟨n, h1, by omega⟩
    let D : ∀ n : ℕ, Finset (Lev p n) := fun n => Finset.univ.filter (fun x => emT p n x ∈ E)
    refine bohr_of_levels (Lev p) (fun n => reT p n) D good hinf α hα (fun n hn => ?_)
      (fun z z' => Filter.Eventually.of_forall (fun n => map_add _ _ _)) (dsum E) (fun z => ?_)
    · have hcard : (D n).card = cntF (TorF p) E n := by
        have e : (TorF p n).filter (fun x => x ∈ E) = (D n).image (emT p n) := by
          unfold TorF
          rw [Finset.filter_image]
        unfold cntF
        rw [e, Finset.card_image_of_injective _ (emT_injective p n)]
      rw [hcard, ← TorF_card]
      exact hn
    · obtain ⟨N, hN⟩ := bounded_support p z
      filter_upwards [eventually_ge_atTop N] with n hn
      rintro ⟨a, ha, b, hb, c, hc, d, hdd, h⟩
      refine ⟨_, (Finset.mem_filter.1 ha).2, _, (Finset.mem_filter.1 hb).2, _, (Finset.mem_filter.1 hc).2,
        _, (Finset.mem_filter.1 hdd).2, ?_⟩
      rw [← map_add, ← map_sub, ← map_sub, ← h,
        emT_reT p n z (fun j hj => lt_of_lt_of_le (hN j hj) hn)]

end Torsion

/-! ### The construction on a direct sum -/

/-- The direct sum of the groups `C i`, as the sequences with finitely many nonzero terms. -/
def FSum (C : ℕ → Type) [∀ i, AddCommGroup (C i)] : AddSubgroup (∀ i, C i) where
  carrier := {f | ∃ N : ℕ, ∀ i, N ≤ i → f i = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨N, hf⟩ ⟨M, hg⟩
    refine ⟨max N M, fun i hi => ?_⟩
    rw [Pi.add_apply, hf i (le_trans (le_max_left _ _) hi), hg i (le_trans (le_max_right _ _) hi), add_zero]
  neg_mem' := by
    rintro f ⟨N, hf⟩
    refine ⟨N, fun i hi => ?_⟩
    rw [Pi.neg_apply, hf i hi, neg_zero]

section Abstract

variable (C : ℕ → Type) [∀ i, AddCommGroup (C i)]

noncomputable def incS (i : ℕ) : C i →+ FSum C :=
  AddMonoidHom.codRestrict (AddMonoidHom.single C i) (FSum C) (fun z => ⟨i + 1, fun k hk => by
    rw [AddMonoidHom.single_apply]
    exact Pi.single_eq_of_ne (by omega : k ≠ i) z⟩)

def compS (i : ℕ) : FSum C →+ C i where
  toFun y := y.1 i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem comp_inc_same (i : ℕ) (z : C i) : compS C i (incS C i z) = z := by
  show (Pi.single i z : ∀ k, C k) i = z
  rw [Pi.single_eq_same]

theorem comp_inc_ne (i j : ℕ) (h : j ≠ i) (z : C j) : compS C i (incS C j z) = 0 := by
  show (Pi.single j z : ∀ k, C k) i = 0
  rw [Pi.single_eq_of_ne h.symm]

theorem compS_fin (y : FSum C) : ∃ N : ℕ, ∀ i, N ≤ i → compS C i y = 0 := y.2

variable (supp : ∀ i, C i → Finset ℕ) (q : ∀ i, Ultrafilter (C i))
  (hsupp0 : ∀ i, supp i 0 = ∅)
  (hsupp1 : ∀ i (z : C i), z ≠ 0 → (supp i z).Nonempty)
  (hwin : ∀ i (L : ℕ) (ε : Fin L → ℤ) (a : Fin L → C i), (∀ l, ε l = 1 ∨ ε l = -1) → ∀ t,
    t ∈ supp i (∑ l, ε l • a l) → ∃ l, ∃ s ∈ supp i (a l), s ≤ t ∧ t ≤ s + L)
  (hq : ∀ i, q i + q i = q i)
  (habove : ∀ i K, {z : C i | z ≠ 0 ∧ ∀ s ∈ supp i z, K < s} ∈ q i)
  (hbog : ∀ i, ∀ E ∈ q i, dsum E ∈ comap (iota (G := C i)) (𝓝 0))

noncomputable def Qs (i : ℕ) : Ultrafilter (FSum C) := (q i).map (incS C i)

include hq in
theorem Qs_idem (i : ℕ) : Qs C q i + Qs C q i = Qs C q i := by
  have h := map_add_hom (incS C i) (q i) (q i)
  rw [hq] at h
  exact h.symm

/-- Elements with the components `j, ..., j + n`, each supported above the next. -/
def Ss (j n : ℕ) : Set (FSum C) :=
  {x | (∀ i, compS C i x ≠ 0 ↔ j ≤ i ∧ i ≤ j + n) ∧
    ∀ i, j ≤ i → i < j + n → ∀ s ∈ supp i (compS C i x), ∀ t ∈ supp (i + 1) (compS C (i + 1) x), t < s}

include habove in
theorem Ss_mem : ∀ n j : ℕ, Ss C supp j n ∈ chain (Qs C q) j n
  | 0, j => by
    rw [chain, Qs, Ultrafilter.mem_map]
    refine Filter.mem_of_superset (habove j 0) (fun t ht => ?_)
    rw [mem_preimage]
    refine ⟨fun i => ?_, fun i h1 h2 => by omega⟩
    by_cases h : j = i
    · subst h
      rw [comp_inc_same]
      exact ⟨fun _ => by omega, fun _ => ht.1⟩
    · rw [comp_inc_ne C i j h]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (by omega : j = i) h⟩
  | n + 1, j => by
    rw [chain, PG.Idem.mem_add]
    refine Filter.mem_of_superset (Ss_mem n (j + 1)) (fun y hy => ?_)
    rw [mem_setOf_eq, Qs, Ultrafilter.mem_map]
    obtain ⟨N, hN⟩ := compS_fin C y
    set M : ℕ := (Finset.range N).sup (fun i => (supp i (compS C i y)).sup id) with hM
    have hyj : compS C j y = 0 := by
      by_contra h
      have := (hy.1 j).1 h
      omega
    refine Filter.mem_of_superset (habove j M) (fun t ht => ?_)
    rw [mem_preimage, mem_setOf_eq]
    have hj : compS C j (y + incS C j t) = t := by
      rw [map_add, hyj, zero_add, comp_inc_same]
    have hne : ∀ i, j ≠ i → compS C i (y + incS C j t) = compS C i y := by
      intro i h
      rw [map_add, comp_inc_ne C i j h, add_zero]
    refine ⟨fun i => ?_, fun i h1 h2 s hs t' ht' => ?_⟩
    · by_cases h : j = i
      · subst h
        rw [hj]
        exact ⟨fun _ => by omega, fun _ => ht.1⟩
      · rw [hne i h, hy.1 i]
        omega
    · have hne1 : j ≠ i + 1 := by omega
      rw [hne (i + 1) hne1] at ht'
      by_cases h : j = i
      · subst h
        rw [hj] at hs
        have hi1 : j + 1 < N := by
          by_contra hge
          have h3 : compS C (j + 1) y = 0 := hN _ (not_lt.1 hge)
          exact ((hy.1 (j + 1)).2 ⟨le_rfl, by omega⟩) h3
        have h4 : t' ≤ M := le_trans (Finset.le_sup (f := id) ht')
          (Finset.le_sup (f := fun i => (supp i (compS C i y)).sup id) (Finset.mem_range.2 hi1))
        exact lt_of_le_of_lt h4 (ht.2 s hs)
      · rw [hne i h] at hs
        exact hy.2 i (by omega) (by omega) s hs t' ht'

noncomputable def us : Ultrafilter (FSum C) := chainLim (Qs C q)

def As : Set (FSum C) := ⋃ n, Ss C supp 0 n

include habove in
theorem As_mem : As C supp ∈ us C q := by
  unfold us
  rw [mem_chainLim]
  refine Filter.mem_of_superset Filter.univ_mem (fun n _ => ?_)
  exact Filter.mem_of_superset (Ss_mem C supp q habove n 0) (subset_iUnion (fun n => Ss C supp 0 n) n)

include habove in
theorem us_free (a : FSum C) : us C q ≠ pure a := by
  intro h
  have h1 : ∀ m, {x : FSum C | compS C m x ≠ 0} ∈ us C q := by
    intro m
    unfold us
    rw [mem_chainLim]
    refine Filter.mem_of_superset (Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop m)) (fun n hn => ?_)
    have hn' : m ≤ n := hn
    refine Filter.mem_of_superset (Ss_mem C supp q habove n 0) (fun x hx => ?_)
    exact (hx.1 m).2 ⟨Nat.zero_le _, by omega⟩
  obtain ⟨N, hN⟩ := compS_fin C a
  have h3 := h1 N
  rw [h] at h3
  have h4 : compS C N a ≠ 0 := h3
  exact h4 (hN N le_rfl)

/-- Signed sums of `L` elements of `As`. -/
def ns (L : ℕ) : Set (FSum C) :=
  {y | ∃ ε : Fin L → ℤ, ∃ a : Fin L → FSum C, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, a l ∈ As C supp) ∧
    ∑ l, ε l • a l = y}

include habove in
theorem ns_of_sumClosure {σ : Filter (FSum C)} (h : SumClosure (ultraGen {us C q}) σ) :
    ∃ L, ns C supp L ∈ σ := by
  have hA : As C supp ∈ us C q := As_mem C supp q habove
  have hgen : ∀ F : Filter (FSum C), F ∈ ultraGen {us C q} → As C supp ∈ F := by
    rintro F ⟨v, hv, rfl⟩
    rw [mem_singleton_iff.1 hv]
    exact hA
  induction h with
  | zero =>
    exact ⟨0, Filter.mem_pure.2 ⟨fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0,
      by simp⟩⟩
  | gen hF =>
    refine ⟨1, Filter.mem_of_superset (hgen _ hF) (fun x hx => ?_)⟩
    exact ⟨fun _ => 1, fun _ => x, fun _ => Or.inl rfl, fun _ => hx, by simp⟩
  | neg hF =>
    refine ⟨1, Filter.mem_map.2 (Filter.mem_of_superset (hgen _ hF) (fun x hx => ?_))⟩
    exact ⟨fun _ => -1, fun _ => x, fun _ => Or.inr rfl, fun _ => hx, by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨L1, h1⟩ := ih1
    obtain ⟨L2, h2⟩ := ih2
    refine ⟨L1 + L2, Filter.mem_of_superset (Filter.image2_mem_map₂ h1 h2) ?_⟩
    rintro _ ⟨y1, ⟨ε, a, hε, ha, rfl⟩, y2, ⟨δ, b, hδ, hb, rfl⟩, rfl⟩
    refine ⟨Fin.append ε δ, Fin.append a b, fun l => ?_, fun l => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · rw [Fin.append_left]
        exact hε i
      · rw [Fin.append_right]
        exact hδ i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · rw [Fin.append_left]
        exact ha i
      · rw [Fin.append_right]
        exact hb i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]

/-- The components `0, ..., m - 1`, each supported more than `m` below the next. -/
def Is (m : ℕ) : Set (FSum C) :=
  {y | (∀ i, compS C i y ≠ 0 ↔ i < m) ∧
    ∀ i j, i < j → j < m → ∀ s ∈ supp i (compS C i y), ∀ t ∈ supp j (compS C j y), s + m < t}

theorem Ss_order {x : FSum C} {n : ℕ} (hx : x ∈ Ss C supp 0 n)
    (hs1 : ∀ i (z : C i), z ≠ 0 → (supp i z).Nonempty) :
    ∀ k i, i + (k + 1) ≤ n → ∀ s ∈ supp i (compS C i x),
      ∀ t ∈ supp (i + (k + 1)) (compS C (i + (k + 1)) x), t < s := by
  intro k
  induction k with
  | zero =>
    intro i hi s hs t ht
    exact hx.2 i (Nat.zero_le _) (by omega) s hs t ht
  | succ k ih =>
    intro i hi s hs t ht
    have hne : compS C (i + (k + 1)) x ≠ 0 := (hx.1 _).2 ⟨Nat.zero_le _, by omega⟩
    obtain ⟨r, hr⟩ := hs1 _ _ hne
    have h1 := ih i (by omega) s hs r hr
    exact (hx.2 (i + (k + 1)) (Nat.zero_le _) (by omega) r hr t ht).trans h1

include hsupp0 hsupp1 hwin in
theorem ns_disjoint_Is {L m : ℕ} (h : L < m) (y : FSum C) (hy : y ∈ ns C supp L) (hI : y ∈ Is C supp m) :
    False := by
  classical
  obtain ⟨ε, a, hε, ha, hsum⟩ := hy
  have hpick : ∀ i : Fin m, ∃ t, t ∈ supp i (compS C i y) ∧
      ∃ l : Fin L, ∃ s ∈ supp i (compS C i (a l)), s ≤ t ∧ t ≤ s + L := by
    intro i
    obtain ⟨t, ht⟩ := hsupp1 _ _ ((hI.1 i).2 i.2)
    refine ⟨t, ht, ?_⟩
    have e : compS C i y = ∑ l, ε l • compS C i (a l) := by
      rw [← hsum, map_sum]
      exact Finset.sum_congr rfl (fun l _ => map_zsmul _ _ _)
    rw [e] at ht
    exact hwin i L ε (fun l => compS C i (a l)) hε t ht
  choose t ht l s hs hs1 hs2 using hpick
  obtain ⟨i, j, hij, hl⟩ : ∃ i j : Fin m, i < j ∧ l i = l j := by
    have hni : ¬ Function.Injective l := by
      intro hinj
      have h1 := Fintype.card_le_of_injective l hinj
      simp at h1
      omega
    obtain ⟨i, j, h1, h2⟩ := Function.not_injective_iff.1 hni
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · exact ⟨i, j, h3, h1⟩
    · exact ⟨j, i, h3, h1.symm⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 (ha (l i))
  have hnej : compS C (j : ℕ) (a (l i)) ≠ 0 := by
    intro h0
    have h1 := hs j
    rw [← hl, h0, hsupp0] at h1
    simp at h1
  have hjn : (j : ℕ) ≤ n := by
    have := ((hn.1 j).1 hnej).2
    omega
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have e : (i : ℕ) + (((j : ℕ) - i - 1) + 1) = j := by omega
  have key : ∀ k, k = (j : ℕ) → ∀ r ∈ supp k (compS C k (a (l i))), r < s i := by
    intro k hk r hr
    have h2 := Ss_order C supp hn hsupp1 ((j : ℕ) - i - 1) i (by omega) (s i) (hs i)
    rw [e] at h2
    subst hk
    exact h2 r hr
  have h1 : s j < s i := by
    refine key j rfl (s j) ?_
    rw [hl]
    exact hs j
  have h2 : t i + m < t j := hI.2 i j hij' j.2 (t i) (ht i) (t j) (ht j)
  have h3 := hs1 i
  have h4 := hs2 j
  omega

/-- The Bohr neighbourhoods of `0` of the `i`-th summand. -/
noncomputable def Ns (i : ℕ) : Filter (FSum C) := Filter.map (incS C i) (comap (iota (G := C i)) (𝓝 0))

theorem comap_iota_nbhd (G : Type) [AddCommGroup G] : IsNbhdFilter (comap (iota (G := G)) (𝓝 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨W, hW, h⟩ := mem_comap.1 hA
    refine h ?_
    show iota (0 : G) ∈ W
    rw [map_zero]
    exact mem_of_mem_nhds hW
  · intro A hA
    obtain ⟨W, hW, h⟩ := mem_comap.1 hA
    have h1 : (fun f : Circles G => -f) ⁻¹' W ∈ 𝓝 (0 : Circles G) := by
      have h2 := (continuous_neg (G := Circles G)).tendsto 0
      rw [neg_zero] at h2
      exact h2 hW
    refine mem_comap.2 ⟨_, h1, fun x hx => h ?_⟩
    show iota (-x) ∈ W
    rw [map_neg]
    exact hx
  · intro A hA
    obtain ⟨W, hW, h⟩ := mem_comap.1 hA
    obtain ⟨V, hVo, h0, hV⟩ := exists_open_nhds_zero_half hW
    refine ⟨iota ⁻¹' V, mem_comap.2 ⟨V, hVo.mem_nhds h0, Subset.rfl⟩, fun x hx y hy => h ?_⟩
    show iota (x + y) ∈ W
    rw [map_add]
    exact hV _ hx _ hy

theorem map_nbhd {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) {N : Filter G} (hN : IsNbhdFilter N) :
    IsNbhdFilter (Filter.map f N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    have h := hN.zero_mem _ (Filter.mem_map.1 hA)
    rwa [mem_preimage, map_zero] at h
  · intro A hA
    refine Filter.mem_map.2 (Filter.mem_of_superset (hN.neg_mem _ (Filter.mem_map.1 hA)) (fun x hx => ?_))
    show -(f x) ∈ A
    have hx' : f (-x) ∈ A := hx
    rwa [map_neg] at hx'
  · intro A hA
    obtain ⟨B, hB, h⟩ := hN.halve _ (Filter.mem_map.1 hA)
    refine ⟨f '' B, Filter.image_mem_map hB, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_add]
    exact h x hx y hy

theorem Ns_nbhd (i : ℕ) : IsNbhdFilter (Ns C i) := map_nbhd _ (comap_iota_nbhd _)

include hq hbog in
theorem Ns_null (i : ℕ) : Ns C i ∈ genFam (ultraGen {us C q}) := by
  have hgen : SumClosure (ultraGen {us C q}) (us C q : Filter (FSum C)) := SumClosure.gen ⟨_, rfl, rfl⟩
  obtain ⟨τ, hτs, hQ⟩ : ∃ τ : Filter (FSum C), SumClosure (ultraGen {us C q}) τ ∧
      (Qs C q i : Filter (FSum C)) ≤ τ :=
    ⟨_, SumClosure.add (tri_sumClosure hgen i) (sumClosure_neg (tri_sumClosure hgen (i + 1))),
      Q_le_chainLim (Qs C q) (fun k => schur_of_idempotent (Qs_idem C q hq k)) i⟩
  have hne : (Ns C i).NeBot := by
    refine ⟨fun h => ?_⟩
    have h1 : (∅ : Set (FSum C)) ∈ Ns C i := by rw [h]; exact mem_bot
    exact (Ns_nbhd C i).zero_mem _ h1
  refine mem_genFam_of_le (SumClosure.add (SumClosure.add hτs hτs) (sumClosure_neg (SumClosure.add hτs hτs))) ?_
  intro s hs
  obtain ⟨t1, ht1, t2, ht2, h⟩ := Filter.mem_map₂_iff.1 hs
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_map₂_iff.1 ht1
  obtain ⟨C', hC', D, hD, hCD⟩ := Filter.mem_map₂_iff.1 (Filter.mem_map.1 ht2)
  have ht : A ∩ B ∩ C' ∩ D ∈ τ := Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC') hD
  have hE0 : A ∩ B ∩ C' ∩ D ∈ Qs C q i := hQ ht
  have hE : incS C i ⁻¹' (A ∩ B ∩ C' ∩ D) ∈ q i := Ultrafilter.mem_map.1 hE0
  refine Filter.mem_map.2 (Filter.mem_of_superset (hbog i _ hE) (fun z hz => ?_))
  obtain ⟨a, ma, b, mb, c, mc, d, md, e⟩ := hz
  have e' : incS C i z = (incS C i a + incS C i b) + -(incS C i c + incS C i d) := by
    rw [e, map_sub, map_sub, map_add]
    abel
  show incS C i z ∈ s
  rw [e']
  refine h (mem_image2_of_mem (hAB (mem_image2_of_mem ma.1.1.1 mb.1.1.2)) ?_)
  have h1 : incS C i c + incS C i d ∈ (fun x : FSum C => -x) ⁻¹' t2 := hCD (mem_image2_of_mem mc.1.2 md.2)
  exact h1

include hq in
theorem q_le_bohr (i : ℕ) : (q i : Filter (C i)) ≤ comap (iota (G := C i)) (𝓝 0) := by
  have h := lim_lam (q i)
  rw [lam_idempotent (hq i)] at h
  exact tendsto_iff_comap.1 h

include hq habove in
theorem meets_Is (N0 : Filter (FSum C)) (hN0 : IsNbhdFilter N0) (hmax : ∀ i, Ns C i ≤ N0)
    (s : Set (FSum C)) (hs : s ∈ N0) (m : ℕ) : (s ∩ Is C supp m).Nonempty := by
  classical
  obtain ⟨t, ht, hsum⟩ := sum_halve hN0 m s hs
  have hpick : ∀ i M : ℕ, ∃ z : C i, incS C i z ∈ t ∧ z ≠ 0 ∧ ∀ r ∈ supp i z, M < r := by
    intro i M
    have h1 : incS C i ⁻¹' t ∈ comap (iota (G := C i)) (𝓝 0) := Filter.mem_map.1 (hmax i ht)
    have h2 : incS C i ⁻¹' t ∈ q i := q_le_bohr C q hq i h1
    obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h2 (habove i M))
    exact ⟨z, hz1, hz2⟩
  choose pick hpickt hpick0 hpickA using hpick
  let M : ℕ → ℕ := fun i => Nat.rec 0 (fun k Mk => max Mk ((supp k (pick k (Mk + m))).sup id)) i
  let z : ∀ i, C i := fun i => pick i (M i + m)
  have hMsucc : ∀ i, M (i + 1) = max (M i) ((supp i (z i)).sup id) := fun i => rfl
  have hMmono : Monotone M := monotone_nat_of_le_succ (fun i => by rw [hMsucc]; exact le_max_left _ _)
  have horder : ∀ i j, i < j → ∀ a ∈ supp i (z i), ∀ b ∈ supp j (z j), a + m < b := by
    intro i j hij a ha b hb
    have h1 : a ≤ M (i + 1) := by
      rw [hMsucc]
      exact le_trans (Finset.le_sup (f := id) ha) (le_max_right _ _)
    have h2 : M (i + 1) ≤ M j := hMmono hij
    have h3 : M j + m < b := hpickA j (M j + m) b hb
    omega
  set y : FSum C := ∑ i : Fin m, incS C (i : ℕ) (z i) with hy
  have hylt : ∀ k, k < m → compS C k y = z k := by
    intro k hk
    rw [hy, map_sum, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
    · exact comp_inc_same C k (z k)
    · intro b _ hb
      exact comp_inc_ne C k b (fun h : (b : ℕ) = k => hb (Fin.ext h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hyge : ∀ k, ¬ k < m → compS C k y = 0 := by
    intro k hk
    rw [hy, map_sum]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    exact comp_inc_ne C k b (fun h : (b : ℕ) = k => hk (by rw [← h]; exact b.2)) _
  refine ⟨y, hsum _ (fun i => hpickt i (M i + m)), fun k => ?_, fun i j hij hj a ha b hb => ?_⟩
  · by_cases hk : k < m
    · rw [hylt k hk]
      exact ⟨fun _ => hk, fun _ => hpick0 k (M k + m)⟩
    · rw [hyge k hk]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hk⟩
  · rw [hylt i (hij.trans hj)] at ha
    rw [hylt j hj] at hb
    exact horder i j hij a ha b hb

include hq in
theorem lam_chains : ∀ n j : ℕ, lam (chain (Qs C q) j n) = 0
  | 0, j => lam_idempotent (Qs_idem C q hq j)
  | n + 1, j => by
    rw [chain, lam_add, lam_chains n (j + 1), lam_idempotent (Qs_idem C q hq j), add_zero]

include hq in
theorem us_hausdorff (g : FSum C) (hg : (pure g : Filter (FSum C)) ∈ genFam (ultraGen {us C q})) : g = 0 := by
  have hlam : lam (us C q) = 0 := by
    refine lam_eq ?_
    refine tendsto_nhds.2 (fun W hW h0 => ?_)
    show iota ⁻¹' W ∈ us C q
    unfold us
    rw [mem_chainLim]
    refine Filter.mem_of_superset Filter.univ_mem (fun n _ => ?_)
    have h1 := lim_lam (chain (Qs C q) 0 n)
    rw [lam_chains C q hq n 0] at h1
    exact h1 (hW.mem_nhds h0)
  have h1 : iota g ∈ K (ultraGen {us C q}) := iota_mem_K _ g hg
  have h2 : K (ultraGen {us C q}) ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 (fun b hb => ?_)
    obtain ⟨v, hv, rfl⟩ := L_ultraGen _ hb
    rw [mem_singleton_iff.1 hv, hlam]
    exact (⊥ : AddSubgroup (Circles (FSum C))).zero_mem
  have h3 : iota g = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact iota_injective (h3.trans (map_zero iota).symm)

include hsupp0 hsupp1 hwin hq habove hbog in
theorem abstract_no_coreflection :
    ∃ u : Ultrafilter (FSum C), (∀ a, u ≠ pure a) ∧
      (∀ g : FSum C, (pure g : Filter (FSum C)) ∈ genFam (ultraGen {u}) → g = 0) ∧
      ¬ ∃ N0 : Filter (FSum C), (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter (FSum C), IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0 := by
  refine ⟨us C q, us_free C supp q habove, us_hausdorff C q hq, ?_⟩
  rintro ⟨N0, ⟨hN0, hN0C⟩, hmax⟩
  have hC : NullFamily (genFam (ultraGen {us C q})) := genFam_nullFamily _
  set J : ℕ → Set (FSum C) := fun k => ⋃ m, ⋃ (_ : k ≤ m), Is C supp m with hJ
  have hJanti : Antitone J := by
    intro k k' h x hx
    simp only [hJ, mem_iUnion] at hx ⊢
    obtain ⟨m, hm, hx⟩ := hx
    exact ⟨m, h.trans hm, hx⟩
  have hne : ∀ k, (N0 ⊓ 𝓟 (J k)).NeBot := by
    intro k
    rw [inf_principal_neBot_iff]
    intro s hs
    obtain ⟨y, hy1, hy2⟩ := meets_Is C supp q hq habove N0 hN0
      (fun i => hmax _ (Ns_nbhd C i) (Ns_null C q hq hbog i)) s hs k
    exact ⟨y, hy1, mem_iUnion₂.2 ⟨k, le_rfl, hy2⟩⟩
  have hdir : Directed (· ≥ ·) (fun k => N0 ⊓ 𝓟 (J k)) :=
    Antitone.directed_ge (fun k k' h => inf_le_inf_left _ (principal_mono.2 (hJanti h)))
  have hinf : (⨅ k, N0 ⊓ 𝓟 (J k)).NeBot := iInf_neBot_of_directed' hdir hne
  set r : Ultrafilter (FSum C) := Ultrafilter.of (⨅ k, N0 ⊓ 𝓟 (J k)) with hr
  have hrle : ∀ k, (r : Filter (FSum C)) ≤ N0 ⊓ 𝓟 (J k) := fun k => (Ultrafilter.of_le _).trans (iInf_le _ k)
  have hrC : (r : Filter (FSum C)) ∈ genFam (ultraGen {us C q}) :=
    hC.finer _ hN0C _ ((hrle 0).trans inf_le_left) r.neBot
  obtain ⟨σ, hσ, hrσ⟩ := hrC.2 r le_rfl
  obtain ⟨L, hL⟩ := ns_of_sumClosure C supp q habove hσ
  have h1 : ns C supp L ∈ (r : Filter (FSum C)) := hrσ hL
  have h3 : J (L + 1) ∈ (r : Filter (FSum C)) := (hrle (L + 1)).trans inf_le_right (mem_principal_self _)
  obtain ⟨y, hy1, hy2⟩ := Ultrafilter.nonempty_of_mem (f := r) (Filter.inter_mem h1 h3)
  simp only [hJ, mem_iUnion] at hy2
  obtain ⟨m, hm, hI⟩ := hy2
  exact ns_disjoint_Is C supp hsupp0 hsupp1 hwin (by omega) y hy1 hI

end Abstract

/-! ### Transfer along an injective homomorphism -/

section Transfer

variable {H G : Type} [AddCommGroup H] [AddCommGroup G] (f : H →+ G)

theorem map_neg_comm (F : Filter H) :
    Filter.map (fun x : G => -x) (Filter.map f F) = Filter.map f (Filter.map (fun x : H => -x) F) := by
  rw [Filter.map_map, Filter.map_map]
  congr 1
  funext x
  simp

theorem map_add_comm (F F' : Filter H) :
    Filter.map f (Filter.map₂ (· + ·) F F') = Filter.map₂ (· + ·) (Filter.map f F) (Filter.map f F') :=
  Filter.map_map₂_distrib (fun a b => map_add f a b)

theorem sumClosure_map (u : Ultrafilter H) {σ : Filter G} (h : SumClosure (ultraGen {u.map f}) σ) :
    ∃ σ' : Filter H, SumClosure (ultraGen {u}) σ' ∧ σ = Filter.map f σ' := by
  have hgen : ∀ F : Filter G, F ∈ ultraGen {u.map f} → F = Filter.map f (u : Filter H) := by
    rintro F ⟨v, hv, rfl⟩
    rw [mem_singleton_iff.1 hv, Ultrafilter.coe_map]
  have hu : (u : Filter H) ∈ ultraGen {u} := ⟨u, rfl, rfl⟩
  induction h with
  | zero => exact ⟨pure 0, SumClosure.zero, by rw [Filter.map_pure, map_zero]⟩
  | gen hF => exact ⟨u, SumClosure.gen hu, hgen _ hF⟩
  | neg hF =>
    refine ⟨_, SumClosure.neg hu, ?_⟩
    rw [hgen _ hF, map_neg_comm]
  | add _ _ ih1 ih2 =>
    obtain ⟨a, ha, e1⟩ := ih1
    obtain ⟨b, hb, e2⟩ := ih2
    exact ⟨_, SumClosure.add ha hb, by rw [e1, e2, map_add_comm]⟩

theorem sumClosure_map' (u : Ultrafilter H) {σ' : Filter H} (h : SumClosure (ultraGen {u}) σ') :
    SumClosure (ultraGen {u.map f}) (Filter.map f σ') := by
  have hgen : ∀ F : Filter H, F ∈ ultraGen {u} → Filter.map f F ∈ ultraGen {u.map f} := by
    rintro F ⟨v, hv, rfl⟩
    refine ⟨u.map f, rfl, ?_⟩
    rw [mem_singleton_iff.1 hv, Ultrafilter.coe_map]
  induction h with
  | zero =>
    rw [Filter.map_pure, map_zero]
    exact SumClosure.zero
  | gen hF => exact SumClosure.gen (hgen _ hF)
  | neg hF =>
    rw [← map_neg_comm]
    exact SumClosure.neg (hgen _ hF)
  | add _ _ ih1 ih2 =>
    rw [map_add_comm]
    exact SumClosure.add ih1 ih2

variable (hf : Function.Injective f)

include hf in
theorem ultra_of_range (U : Ultrafilter G) (h : range f ∈ U) : ∃ U' : Ultrafilter H, U'.map f = U := by
  refine ⟨U.comap hf h, ?_⟩
  refine Ultrafilter.coe_injective ?_
  rw [Ultrafilter.coe_map, Ultrafilter.coe_comap, Filter.map_comap_of_mem]
  exact h

include hf in
theorem le_of_map_le (A B : Filter H) (h : Filter.map f A ≤ Filter.map f B) : A ≤ B :=
  (Filter.map_le_map_iff hf).1 h

include hf in
theorem genFam_map (u : Ultrafilter H) (N : Filter H) (hN : N ∈ genFam (ultraGen {u})) :
    Filter.map f N ∈ genFam (ultraGen {u.map f}) := by
  have := hN.1
  refine ⟨inferInstance, fun U hU => ?_⟩
  have h1 : range f ∈ U := hU (Filter.range_mem_map)
  obtain ⟨U', rfl⟩ := ultra_of_range f hf U h1
  rw [Ultrafilter.coe_map] at hU
  have h2 := le_of_map_le f hf _ _ hU
  obtain ⟨σ, hσ, h3⟩ := hN.2 U' h2
  refine ⟨_, sumClosure_map' f u hσ, ?_⟩
  rw [Ultrafilter.coe_map]
  exact Filter.map_mono h3

include hf in
theorem genFam_comap (u : Ultrafilter H) (N : Filter G) (hN : N ∈ genFam (ultraGen {u.map f})) :
    Filter.map f (Filter.comap f N) = N ∧ Filter.comap f N ∈ genFam (ultraGen {u}) := by
  have h1 : range f ∈ N := by
    refine Filter.mem_iff_ultrafilter.2 (fun U hU => ?_)
    obtain ⟨σ, hσ, h2⟩ := hN.2 U hU
    obtain ⟨σ', _, rfl⟩ := sumClosure_map f u hσ
    exact h2 Filter.range_mem_map
  have h3 : Filter.map f (Filter.comap f N) = N := Filter.map_comap_of_mem h1
  have h4 : (Filter.comap f N).NeBot := by
    have h5 := hN.1
    rw [← h3] at h5
    exact Filter.NeBot.of_map h5
  refine ⟨h3, h4, fun U hU => ?_⟩
  have h6 : ((U.map f : Ultrafilter G) : Filter G) ≤ N := by
    rw [Ultrafilter.coe_map, ← h3]
    exact Filter.map_mono hU
  obtain ⟨σ, hσ, h7⟩ := hN.2 _ h6
  obtain ⟨σ', hσ', rfl⟩ := sumClosure_map f u hσ
  rw [Ultrafilter.coe_map] at h7
  exact ⟨σ', hσ', le_of_map_le f hf _ _ h7⟩

theorem comap_nbhd {N : Filter G} (hN : IsNbhdFilter N) : IsNbhdFilter (Filter.comap f N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, h⟩ := Filter.mem_comap.1 hA
    refine h ?_
    show f 0 ∈ B
    rw [map_zero]
    exact hN.zero_mem B hB
  · intro A hA
    obtain ⟨B, hB, h⟩ := Filter.mem_comap.1 hA
    refine Filter.mem_comap.2 ⟨_, hN.neg_mem B hB, fun x hx => h ?_⟩
    show f (-x) ∈ B
    rw [map_neg]
    exact hx
  · intro A hA
    obtain ⟨B, hB, h⟩ := Filter.mem_comap.1 hA
    obtain ⟨D, hD, h2⟩ := hN.halve B hB
    refine ⟨f ⁻¹' D, Filter.preimage_mem_comap hD, fun x hx y hy => h ?_⟩
    show f (x + y) ∈ B
    rw [map_add]
    exact h2 _ hx _ hy

include hf in
theorem transfer
    (h : ∃ u : Ultrafilter H, (∀ a, u ≠ pure a) ∧
      (∀ g : H, (pure g : Filter H) ∈ genFam (ultraGen {u}) → g = 0) ∧
      ¬ ∃ N0 : Filter H, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter H, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0) :
    ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
      (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen {u}) → g = 0) ∧
      ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0 := by
  obtain ⟨u, hfree, hhaus, hno⟩ := h
  refine ⟨u.map f, fun a ha => ?_, fun g hg => ?_, ?_⟩
  · have h1 : range f ∈ u.map f := by
      rw [Ultrafilter.mem_map]
      exact Filter.univ_mem' (fun x => mem_range_self x)
    rw [ha] at h1
    obtain ⟨b, hb⟩ := (h1 : a ∈ range f)
    have h2 : ({a} : Set G) ∈ u.map f := by
      rw [ha]
      exact rfl
    have h3 : ({b} : Set H) ∈ u :=
      Filter.mem_of_superset (Ultrafilter.mem_map.1 h2) (fun x hx => hf (hx.trans hb.symm))
    obtain ⟨c, _, h4⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton b) h3
    exact hfree c h4
  · obtain ⟨h3, h4⟩ := genFam_comap f hf u (pure g) hg
    have h5 : g ∈ range f := by
      have h6 : range f ∈ Filter.map f (Filter.comap f (pure g : Filter G)) := Filter.range_mem_map
      rw [h3] at h6
      exact h6
    obtain ⟨b, rfl⟩ := h5
    have h7 : Filter.comap f (pure (f b) : Filter G) = pure b := by
      rw [← Filter.map_pure, Filter.comap_map hf]
    rw [h7] at h4
    rw [hhaus b h4, map_zero]
  · rintro ⟨N0, ⟨hN0, hN0C⟩, hmax⟩
    obtain ⟨h1, h2⟩ := genFam_comap f hf u N0 hN0C
    refine hno ⟨Filter.comap f N0, ⟨comap_nbhd f hN0, h2⟩, fun N hN hNC => ?_⟩
    have h3 := hmax _ (map_nbhd f hN) (genFam_map f hf u N hNC)
    exact Filter.map_le_iff_le_comap.1 h3

end Transfer

/-! ### Every group with an infinite sequence of independent elements -/

noncomputable def sumHom {G : Type} [AddCommGroup G] (C : ℕ → Type) [∀ i, AddCommGroup (C i)] (φ : ∀ i, C i →+ G) :
    FSum C →+ G where
  toFun x := ∑ᶠ i, φ i (x.1 i)
  map_zero' := by
    refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
    exact map_zero (φ i)
  map_add' x y := by
    have hfin : ∀ z : FSum C, (Function.support (fun i => φ i (z.1 i))).Finite := by
      intro z
      obtain ⟨N, hN⟩ := z.2
      refine (Set.finite_lt_nat N).subset (fun i (hi : φ i (z.1 i) ≠ 0) => ?_)
      show i < N
      refine not_le.1 (fun h => hi ?_)
      rw [hN i h, map_zero]
    rw [← finsum_add_distrib (hfin x) (hfin y)]
    exact finsum_congr (fun i => map_add (φ i) _ _)

theorem sumHom_eq {G : Type} [AddCommGroup G] (C : ℕ → Type) [∀ i, AddCommGroup (C i)] (φ : ∀ i, C i →+ G)
    (x : FSum C) (N : ℕ) (hN : ∀ i, N ≤ i → x.1 i = 0) : sumHom C φ x = ∑ i ∈ Finset.range N, φ i (x.1 i) := by
  show (∑ᶠ i, φ i (x.1 i)) = _
  refine finsum_eq_sum_of_support_subset _ (fun i hi => ?_)
  rw [Finset.coe_range, mem_Iio]
  refine not_le.1 (fun h => hi ?_)
  show φ i (x.1 i) = 0
  rw [hN i h, map_zero]

/-- Independence of a sequence: a vanishing combination vanishes term by term. -/
def IndepSeq {G : Type} [AddCommGroup G] (g : ℕ → G) : Prop :=
  ∀ (s : Finset ℕ) (c : ℕ → ℤ), ∑ k ∈ s, c k • g k = 0 → ∀ k ∈ s, c k • g k = 0

theorem indep_comp {G : Type} [AddCommGroup G] {g : ℕ → G} (h : IndepSeq g) (σ : ℕ → ℕ)
    (hσ : Function.Injective σ) (m : ℕ → ℤ) : IndepSeq (fun k => m k • g (σ k)) := by
  classical
  intro s c hs k hk
  have e : ∑ j ∈ s.image σ, (Function.extend σ (fun i => c i * m i) 0 j) • g j = 0 := by
    rw [Finset.sum_image (fun x _ y _ h => hσ h)]
    rw [← hs]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hσ.extend_apply, mul_smul]
  have h1 := h _ _ e (σ k) (Finset.mem_image_of_mem σ hk)
  rwa [hσ.extend_apply, mul_smul] at h1

theorem case_int {G : Type} [AddCommGroup G] (g : ℕ → G) (hg : IndepSeq g)
    (hord : ∀ k (c : ℤ), c • g k = 0 → c = 0) :
    ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
      (∀ x : G, (pure x : Filter G) ∈ genFam (ultraGen {u}) → x = 0) ∧
      ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0 := by
  obtain ⟨q, hq, habove, hbog⟩ := bog_int
  have habs := abstract_no_coreflection (fun _ : ℕ => ℤ) (fun _ => tsupp) (fun _ => q) (fun _ => tsupp_zero)
    (fun _ => tsupp_nonempty) (fun _ L ε a hε t ht => tsupp_window L ε a hε t ht) (fun _ => hq)
    (fun _ => habove) (fun _ => hbog)
  let φ : ∀ _ : ℕ, ℤ →+ G := fun i => zmultiplesHom G (g i)
  refine transfer (sumHom (fun _ => ℤ) φ) ?_ habs
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨N, hN⟩ := x.2
  rw [sumHom_eq _ _ x N hN] at hx
  refine Subtype.ext (funext (fun i => ?_))
  by_cases hi : i < N
  · have h1 := hg (Finset.range N) (fun i => x.1 i) hx i (Finset.mem_range.2 hi)
    exact hord i _ h1
  · exact hN i (not_lt.1 hi)

theorem case_tor {G : Type} [AddCommGroup G] (p : ℕ → ℕ) [hp : ∀ k, Fact (p k).Prime] (g : ℕ → G)
    (hg : IndepSeq g) (h0 : ∀ k, g k ≠ 0) (hord : ∀ k, p k • g k = 0) :
    ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
      (∀ x : G, (pure x : Filter G) ∈ genFam (ultraGen {u}) → x = 0) ∧
      ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0 := by
  classical
  have hP : ∀ i k : ℕ, Fact (p (Nat.pair i k)).Prime := fun i k => hp _
  choose q hq habove hbog using fun i : ℕ => bog_tor (fun k => p (Nat.pair i k))
  have habs := abstract_no_coreflection (fun i : ℕ => Tor (fun k => p (Nat.pair i k)))
    (fun i z => z.support) q (fun i => DFinsupp.support_zero)
    (fun i z hz => Finset.nonempty_iff_ne_empty.2 (fun h => hz (DFinsupp.support_eq_empty.1 h)))
    (fun i L ε a _ t ht => by
      have h1 : (∑ l, ε l • a l) t ≠ 0 := DFinsupp.mem_support_iff.1 ht
      rw [DFinsupp.finsetSum_apply] at h1
      obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      refine ⟨l, t, DFinsupp.mem_support_iff.2 (fun h => hl ?_), le_rfl, Nat.le_add_right _ _⟩
      rw [DFinsupp.smul_apply, h, smul_zero])
    hq
    (fun i K => Filter.mem_of_superset (habove i K) (fun z hz =>
      ⟨hz.1, fun s hs => hz.2 s (DFinsupp.mem_support_iff.1 hs)⟩))
    hbog
  have hz : ∀ i k : ℕ, (zmultiplesHom G (g (Nat.pair i k))) (p (Nat.pair i k) : ℤ) = 0 := by
    intro i k
    rw [zmultiplesHom_apply, natCast_zsmul]
    exact hord _
  let ℓ : ∀ i k : ℕ, ZMod (p (Nat.pair i k)) →+ G := fun i k =>
    ZMod.lift (p (Nat.pair i k)) ⟨zmultiplesHom G (g (Nat.pair i k)), hz i k⟩
  have hℓ : ∀ i k (x : ZMod (p (Nat.pair i k))), ℓ i k x = (x.cast : ℤ) • g (Nat.pair i k) := by
    intro i k x
    conv_lhs => rw [← ZMod.intCast_zmod_cast x]
    show ZMod.lift (p (Nat.pair i k)) ⟨zmultiplesHom G (g (Nat.pair i k)), hz i k⟩ ((x.cast : ℤ) : ZMod _) = _
    rw [ZMod.lift_coe]
    rfl
  let φ : ∀ i : ℕ, Tor (fun k => p (Nat.pair i k)) →+ G := fun i => DFinsupp.sumAddHom (ℓ i)
  refine transfer (sumHom (fun i => Tor (fun k => p (Nat.pair i k))) φ) ?_ habs
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨N, hN⟩ := x.2
  rw [sumHom_eq _ _ x N hN] at hx
  have hbd : ∃ M : ℕ, ∀ i < N, ∀ k, (x.1 i) k ≠ 0 → k < M := by
    refine ⟨(Finset.range N).sup (fun i => (x.1 i).support.sup id) + 1, fun i hi k hk => ?_⟩
    have h1 : k ∈ (x.1 i).support := DFinsupp.mem_support_iff.2 hk
    have h2 : k ≤ (x.1 i).support.sup id := Finset.le_sup (f := id) h1
    have h3 : (x.1 i).support.sup id ≤ (Finset.range N).sup (fun i => (x.1 i).support.sup id) :=
      Finset.le_sup (f := fun i => (x.1 i).support.sup id) (Finset.mem_range.2 hi)
    omega
  obtain ⟨M, hM⟩ := hbd
  have hφ : ∀ i < N, φ i (x.1 i) = ∑ k ∈ Finset.range M, ℓ i k ((x.1 i) k) := by
    intro i hi
    have e : x.1 i = ∑ k ∈ Finset.range M,
        DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k ((x.1 i) k) := by
      refine DFinsupp.ext (fun j => ?_)
      rw [DFinsupp.finsetSum_apply]
      by_cases hj : j < M
      · rw [Finset.sum_eq_single j]
        · rw [DFinsupp.single_eq_same]
        · intro b _ hb
          exact DFinsupp.single_eq_of_ne (Ne.symm hb)
        · intro h
          exact absurd (Finset.mem_range.2 hj) h
      · have h1 : (x.1 i) j = 0 := by
          by_contra h
          exact hj (hM i hi j h)
        rw [h1]
        refine (Finset.sum_eq_zero (fun b hb => ?_)).symm
        exact DFinsupp.single_eq_of_ne (fun h => hj (by rw [h]; exact Finset.mem_range.1 hb))
    conv_lhs => rw [e]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => DFinsupp.sumAddHom_single _ _ _)
  set c : ℕ → ℤ := fun n => (((x.1 n.unpair.1) n.unpair.2 : ZMod (p (Nat.pair n.unpair.1 n.unpair.2))).cast : ℤ)
    with hc
  have hcpair : ∀ i k, c (Nat.pair i k) • g (Nat.pair i k) = ℓ i k ((x.1 i) k) := by
    intro i k
    rw [hℓ]
    have key : ∀ a b : ℕ, a = i → b = k →
        (((x.1 a) b : ZMod (p (Nat.pair a b))).cast : ℤ) = (((x.1 i) k : ZMod (p (Nat.pair i k))).cast : ℤ) := by
      rintro a b rfl rfl
      rfl
    have h1 : c (Nat.pair i k) = (((x.1 i) k : ZMod (p (Nat.pair i k))).cast : ℤ) :=
      key _ _ (by rw [Nat.unpair_pair]) (by rw [Nat.unpair_pair])
    rw [h1]
  set S : Finset ℕ := (Finset.range N ×ˢ Finset.range M).image (fun r => Nat.pair r.1 r.2) with hS
  have hinj : Set.InjOn (fun r : ℕ × ℕ => Nat.pair r.1 r.2) (Finset.range N ×ˢ Finset.range M : Finset (ℕ × ℕ)) := by
    intro r _ r' _ h
    have h1 := congrArg Nat.unpair h
    simp only [Nat.unpair_pair] at h1
    exact h1
  have hsum : ∑ n ∈ S, c n • g n = 0 := by
    rw [hS, Finset.sum_image hinj, Finset.sum_product, ← hx]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hφ i (Finset.mem_range.1 hi)]
    exact Finset.sum_congr rfl (fun k _ => hcpair i k)
  refine Subtype.ext (funext (fun i => ?_))
  by_cases hi : i < N
  · refine DFinsupp.ext (fun k => ?_)
    show (x.1 i) k = 0
    by_cases hk : k < M
    · have h1 := hg S c hsum (Nat.pair i k)
        (Finset.mem_image.2 ⟨(i, k), Finset.mem_product.2 ⟨Finset.mem_range.2 hi, Finset.mem_range.2 hk⟩, rfl⟩)
      rw [hcpair, hℓ] at h1
      have h2 : (addOrderOf (g (Nat.pair i k)) : ℤ) ∣ (((x.1 i) k).cast : ℤ) :=
        addOrderOf_dvd_iff_zsmul_eq_zero.2 h1
      have h3 : addOrderOf (g (Nat.pair i k)) = p (Nat.pair i k) :=
        addOrderOf_eq_prime (hord _) (h0 _)
      rw [h3] at h2
      have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
      rwa [ZMod.intCast_zmod_cast] at h4
    · by_contra h
      exact hk (hM i hi k h)
  · exact hN i (not_lt.1 hi)

/-- If an abelian group contains a sequence of independent nonzero elements, some nonprincipal ultrafilter on it
generates a PG with unique limits and no coarsest group topology of the kind considered. -/
theorem no_coreflection_of_independent {G : Type} [AddCommGroup G] (g : ℕ → G) (h0 : ∀ k, g k ≠ 0)
    (hg : IndepSeq g) :
    ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
      (∀ x : G, (pure x : Filter G) ∈ genFam (ultraGen {u}) → x = 0) ∧
      ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0 := by
  classical
  by_cases hinf : {k | addOrderOf (g k) = 0}.Infinite
  · set σ : ℕ → ℕ := fun n => Nat.nth (fun k => addOrderOf (g k) = 0) n with hσ
    have hσinj : Function.Injective σ := (Nat.nth_strictMono hinf).injective
    have hσmem : ∀ n, addOrderOf (g (σ n)) = 0 := fun n => Nat.nth_mem_of_infinite hinf n
    have hind := indep_comp hg σ hσinj (fun _ => 1)
    simp only [one_smul] at hind
    refine case_int (fun n => g (σ n)) hind (fun n c hc => ?_)
    have h1 : (addOrderOf (g (σ n)) : ℤ) ∣ c := addOrderOf_dvd_iff_zsmul_eq_zero.2 hc
    rw [hσmem, Nat.cast_zero] at h1
    exact zero_dvd_iff.1 h1
  · have hfin : {k | addOrderOf (g k) ≠ 0}.Infinite := (Set.not_infinite.1 hinf).infinite_compl
    set σ : ℕ → ℕ := fun n => Nat.nth (fun k => addOrderOf (g k) ≠ 0) n with hσ
    have hσinj : Function.Injective σ := (Nat.nth_strictMono hfin).injective
    have hσmem : ∀ n, addOrderOf (g (σ n)) ≠ 0 := fun n => Nat.nth_mem_of_infinite hfin n
    set p : ℕ → ℕ := fun n => (addOrderOf (g (σ n))).minFac with hp
    have hne1 : ∀ n, addOrderOf (g (σ n)) ≠ 1 := fun n h => h0 _ (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have : ∀ n, Fact (p n).Prime := fun n => ⟨Nat.minFac_prime (hne1 n)⟩
    set m : ℕ → ℕ := fun n => addOrderOf (g (σ n)) / p n with hm
    have hpm : ∀ n, p n * m n = addOrderOf (g (σ n)) := fun n => Nat.mul_div_cancel' (Nat.minFac_dvd _)
    have hind := indep_comp hg σ hσinj (fun n => (m n : ℤ))
    simp only [natCast_zsmul] at hind
    refine case_tor p (fun n => m n • g (σ n)) hind (fun n h => ?_) (fun n => ?_)
    · have h1 : addOrderOf (g (σ n)) ∣ m n := addOrderOf_dvd_iff_nsmul_eq_zero.2 h
      have h2 : 0 < m n := by
        refine Nat.pos_of_ne_zero (fun h3 => hσmem n ?_)
        rw [← hpm n, h3, mul_zero]
      have h4 : m n < addOrderOf (g (σ n)) := by
        rw [← hpm n]
        exact lt_mul_of_one_lt_left h2 (Nat.Prime.one_lt (this n).out)
      exact absurd (Nat.le_of_dvd h2 h1) (not_le.2 h4)
    · rw [← mul_nsmul', hpm, addOrderOf_nsmul_eq_zero]

end Groups

end PG
