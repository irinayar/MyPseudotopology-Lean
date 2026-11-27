import Mathlib
import LeanCheck.PVGTwoRest

/-!
# PVGtwo: three further statements (Lean check)

* `xi_finest` : Corollary 5.5: a group topology in which every lacunary convergent filter converges is contained in the
  Bohr topology; `bohr_xi` says that the Bohr topology is one of them;
* `trace_forces_usual` : Remark 5.4 (ii): the Bohr trace on one set `J_a` already puts a group topology below the usual one;
* `no_rigidity` : Remark 7.14: there is a sequence `δ` with `A(δ) = {0}` for which some `U(ε)` is not covered by finitely
  many translates of the usual neighbourhood `(-1, 1)`.

A lacunary convergent filter is a Bohr convergent filter that contains a set `[-m, m] + a₁S + ⋯ + a_rS`.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-- Every lacunary convergent filter converges in `γ`. -/
def BelowXi (γ : TopologicalSpace ℝ) : Prop :=
  ∀ (x : ℝ) (F : Filter ℝ), F ≤ @nhds ℝ bohrTop x → (∃ (m : ℝ) (l : List ℝ), Icc (-m) m + sumT sT l ∈ F) →
    F ≤ @nhds ℝ γ x

lemma bohr_xi : BelowXi bohrTop := fun _ _ h _ => h

lemma Icc_subset_Jt (a : ℝ) : Icc (-1 : ℝ) 1 ⊆ Jt a := by
  intro x hx
  rw [Jt_eq]
  have h0 : (0 : ℝ) ∈ Tset sT := Or.inl rfl
  have h1 : (0 : ℝ) ∈ a • Tset sT := ⟨0, h0, by simp⟩
  have h2 : (0 : ℝ) ∈ (-a) • Tset sT := ⟨0, h0, by simp⟩
  have := add_mem_add hx (add_mem_add h1 h2)
  simpa using this

lemma usual_of_trace (W : Set ℝ) (B : Set ℝ) (hB : B ∈ @nhds ℝ bohrTop 0) (a : ℝ) (h : B ∩ Jt a ⊆ W) :
    W ∈ euclidNhds 0 := by
  have h1 : B ∈ euclidNhds 0 := by
    have := continuous_e.le_induced
    exact nhds_mono this hB
  have h2 : Icc (-1 : ℝ) 1 ∈ euclidNhds 0 := Icc_mem_nhds (by norm_num) (by norm_num)
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) fun x hx => h ⟨hx.1, Icc_subset_Jt a hx.2⟩

/-- Remark 5.4 (ii). -/
theorem trace_forces_usual (γ : TopologicalSpace ℝ) (a : ℝ)
    (htr : TopologicalSpace.induced (Subtype.val : Jt a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Jt a → ℝ) bohrTop) : euclidNhds 0 ≤ @nhds ℝ γ 0 := by
  intro W hW
  obtain ⟨B, hB, h⟩ := trace_nhds γ (Jt a) (zero_mem_Jt a) htr W hW
  exact usual_of_trace W B hB a h

/-- Corollary 5.5. -/
theorem xi_finest (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hxi : BelowXi γ) : bohrTop ≤ γ := by
  set γ' := γ ⊓ bohrTop with hγ'
  have hg' : @IsTopologicalAddGroup ℝ γ' _ := isTopologicalAddGroup_inf hg bohr_group
  have hfine : γ' ≤ bohrTop := inf_le_right
  have e1 : ∀ x : ℝ, @nhds ℝ γ' x = @nhds ℝ γ x ⊓ @nhds ℝ bohrTop x := fun x => @nhds_inf ℝ γ bohrTop x
  -- `γ'` induces the Bohr topology on every `[-m, m] + a₁S + ⋯`
  have htr : ∀ (m : ℝ) (l : List ℝ), TopologicalSpace.induced (Subtype.val : (Icc (-m) m + sumT sT l : Set ℝ) → ℝ) γ' =
      TopologicalSpace.induced (Subtype.val : (Icc (-m) m + sumT sT l : Set ℝ) → ℝ) bohrTop := by
    intro m l
    refine le_antisymm (induced_mono hfine) ?_
    set J : Set ℝ := Icc (-m) m + sumT sT l with hJ
    refine le_of_nhds_le_nhds fun x => ?_
    have key : ∀ s : TopologicalSpace ℝ, @nhds J (TopologicalSpace.induced (Subtype.val : J → ℝ) s) x =
        Filter.comap (Subtype.val : J → ℝ) (@nhds ℝ s x.1) := by
      intro s
      letI := s
      exact nhds_induced _ _
    rw [key bohrTop, key γ', e1, Filter.comap_inf]
    refine le_inf ?_ le_rfl
    rw [← Filter.map_le_iff_le_comap]
    refine hxi x.1 _ Filter.map_comap_le ⟨m, l, ?_⟩
    exact Filter.mem_map.2 (Filter.Eventually.of_forall fun y => y.2)
  have heu : euclidNhds 0 ≤ @nhds ℝ γ' 0 := trace_forces_usual γ' 0 (htr 1 [0, -0])
  have hpre : Pre γ' := by
    refine no_witness γ' hg' heu fun a => ?_
    have hsub : Ja a ⊆ Icc (-1 : ℝ) 1 + sumT sT [a, -a] := by
      rintro x ⟨s, hs, t, ht, rfl⟩
      rw [← Tset_sT] at hs ht
      have h3 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
      have h4 : a * s + -a * t ∈ sumT sT [a, -a] := by
        simp only [sumT]
        rw [singleton_zero, add_zero]
        exact add_mem_add ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      have := add_mem_add h3 h4
      rwa [zero_add] at this
    have h := htr 1 [a, -a]
    have h2 := congrArg (TopologicalSpace.induced (inclusion hsub)) h
    rwa [induced_compose, induced_compose] at h2
  exact (below_bohr γ' hg' heu hpre).trans inf_le_left

/-! ## Remark 7.14 -/

noncomputable def jz (k : ℕ) : ℤ := (Denumerable.eqv (ℕ × ℤ)).symm k |>.2

lemma jz_infinitely (j : ℤ) (K : ℕ) : ∃ k, K ≤ k ∧ jz k = j := by
  have h : (Set.range fun i : ℕ => Denumerable.eqv (ℕ × ℤ) (i, j)).Infinite := by
    refine Set.infinite_range_of_injective fun a b hab => ?_
    have := (Denumerable.eqv (ℕ × ℤ)).injective hab
    exact (Prod.mk.inj this).1
  obtain ⟨k, ⟨i, rfl⟩, hk⟩ := h.exists_gt K
  exact ⟨_, hk.le, by simp [jz]⟩

/-- The exponents `m_k`, increasing fast enough. -/
noncomputable def mz : ℕ → ℕ
  | 0 => (jz 0).natAbs + 1
  | k + 1 => mz k + (jz (k + 1)).natAbs + (jz k).natAbs + k + 1

noncomputable def Lz (k : ℕ) : ℤ := (mz k : ℤ) ^ 2 - jz k

lemma mz_ge (k : ℕ) : k + 1 ≤ mz k := by
  induction k with
  | zero => simp [mz]
  | succ k ih => simp only [mz]; omega

lemma Lz_gap (k : ℕ) : (k : ℤ) ≤ Lz (k + 1) - Lz k := by
  have h1 : mz k + (jz (k + 1)).natAbs + (jz k).natAbs + k + 1 = mz (k + 1) := rfl
  have h2 : (mz k : ℤ) + (jz (k + 1)).natAbs + (jz k).natAbs + k + 1 = (mz (k + 1) : ℤ) := by exact_mod_cast h1
  have hm := mz_ge k
  have hm0 : (1 : ℤ) ≤ mz k := by exact_mod_cast (show 1 ≤ mz k by omega)
  have h3 : jz (k + 1) ≤ ((jz (k + 1)).natAbs : ℤ) := Int.le_natAbs
  have h4 : -((jz k).natAbs : ℤ) ≤ jz k := by
    have := Int.le_natAbs (a := -jz k)
    rw [Int.natAbs_neg] at this
    omega
  have h5 : (0 : ℤ) ≤ ((jz (k + 1)).natAbs : ℤ) := Int.natCast_nonneg _
  have h6 : (0 : ℤ) ≤ ((jz k).natAbs : ℤ) := Int.natCast_nonneg _
  unfold Lz
  rw [← h2]
  nlinarith

noncomputable def dz (k : ℕ) : ℝ := (2 : ℝ) ^ (-Lz k)

lemma Lz_mono_from (i k : ℕ) (hik : i < k) : (i : ℤ) ≤ Lz k - Lz i := by
  induction k, hik using Nat.le_induction with
  | base => exact Lz_gap i
  | succ k hk ih =>
    have := Lz_gap k
    omega

lemma dz_pow (i k : ℕ) : dz k * (2 : ℝ) ^ (Lz i) = (2 : ℝ) ^ (Lz i - Lz k) := by
  unfold dz
  rw [← zpow_add₀ two_ne_zero]
  congr 1
  ring

lemma dint_int (z : ℤ) : dint (z : ℝ) = 0 := by
  have := dint_sub_int 0 (-z)
  rw [dint_zero] at this
  simpa using this

/-- `A(δ) = {0}`. -/
theorem A_dz (a : ℝ) (ha : InA dz sT a) : a = 0 := by
  have h2 : ∀ j : ℤ, dint (a * (2 : ℝ) ^ j) = 0 := by
    intro j
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (dint_nonneg _)
    rw [zero_add]
    obtain ⟨K, hK⟩ := eventually_atTop.1 (ha ε hε)
    obtain ⟨k, hk, hj⟩ := jz_infinitely j K
    have hm := mz_ge k
    have h := hK k hk (mz k - 1)
    have hs : sT (mz k - 1) = (2 : ℝ) ^ (((mz k : ℤ)) ^ 2) := by
      show (2 : ℝ) ^ ((mz k - 1 + 1) ^ 2) = _
      rw [← zpow_natCast]
      congr 1
      have : mz k - 1 + 1 = mz k := by omega
      rw [this]
      push_cast
      ring
    have e1 : a * dz k * sT (mz k - 1) = a * (2 : ℝ) ^ j := by
      rw [hs, mul_assoc]
      congr 1
      unfold dz
      rw [← zpow_add₀ two_ne_zero]
      congr 1
      unfold Lz
      rw [hj]
      ring
    rwa [e1] at h
  by_contra hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := (1 / 2) / |a|) (div_pos (by norm_num) (abs_pos.2 hne))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsmall : |a * (2 : ℝ) ^ (-(n : ℤ))| < 1 / 2 := by
    rw [abs_mul, zpow_neg, zpow_natCast, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹)]
    rw [lt_div_iff₀ (abs_pos.2 hne), one_div, inv_pow] at hn
    rw [one_div, mul_comm]
    exact hn
  have h := h2 (-(n : ℤ))
  have h3 : dint (a * (2 : ℝ) ^ (-(n : ℤ))) = |a * (2 : ℝ) ^ (-(n : ℤ))| := by
    rw [dint_eq]
    have h4 : round (a * (2 : ℝ) ^ (-(n : ℤ))) = 0 := by
      rw [round_eq_zero_iff]
      have := abs_lt.1 hsmall
      exact ⟨this.1.le, this.2⟩
    rw [h4]
    simp
  rw [h3, abs_eq_zero] at h
  exact hne ((mul_eq_zero.1 h).resolve_right (zpow_ne_zero _ two_ne_zero))

/-- **Remark 7.14.** For the sequence `dz`, `A(δ) = {0}` and `U(1/4)` is not covered by finitely many translates of
`(-1, 1)`. -/
theorem no_rigidity : (∀ a : ℝ, InA dz sT a → a = 0) ∧
    ¬ ∃ F : Finset ℝ, ∀ x : ℝ, (∀ k, dint (dz k * x) ≤ 1 / 4) → ∃ f ∈ F, |x - f| < 1 := by
  refine ⟨A_dz, ?_⟩
  rintro ⟨F, hF⟩
  have hmem : ∀ i : ℕ, 2 ≤ i → ∀ k, dint (dz k * (2 : ℝ) ^ (Lz i)) ≤ 1 / 4 := by
    intro i hi k
    rw [dz_pow]
    by_cases hk : k ≤ i
    · have hle : 0 ≤ Lz i - Lz k := by
        rcases lt_or_eq_of_le hk with h | h
        · have := Lz_mono_from k i h
          omega
        · rw [h, sub_self]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hle
      have e1 : (2 : ℝ) ^ (Lz i - Lz k) = (((2 : ℤ) ^ n : ℤ) : ℝ) := by
        rw [hn, zpow_natCast]; push_cast; rfl
      rw [e1, dint_int]
      norm_num
    · have h := Lz_mono_from i k (not_le.1 hk)
      refine (dint_le_abs _).trans ?_
      rw [abs_of_pos (by positivity)]
      have e1 : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) := by norm_num
      rw [e1]
      exact zpow_le_zpow_right₀ one_le_two (by omega)
  -- the points `2 ^ (L_i)` are unbounded
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ f ∈ F, f ≤ R := by
    obtain ⟨R, hR⟩ := F.bddAbove
    exact ⟨R, fun f hf => hR hf⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R + 1) (one_lt_two (α := ℝ))
  set i := n + 2 with hi
  have hLi : (n : ℤ) ≤ Lz i := by
    have h1 : ∀ k : ℕ, (k : ℤ) ≤ Lz (k + 2) := by
      intro k
      have h0 : 0 ≤ Lz 0 := by
        have hm : (jz 0).natAbs + 1 = mz 0 := rfl
        have hm' : ((jz 0).natAbs : ℤ) + 1 = mz 0 := by exact_mod_cast hm
        have h3 : jz 0 ≤ ((jz 0).natAbs : ℤ) := Int.le_natAbs
        have h5 : (0 : ℤ) ≤ ((jz 0).natAbs : ℤ) := Int.natCast_nonneg _
        unfold Lz
        rw [← hm']
        nlinarith
      have h01 := Lz_gap 0
      induction k with
      | zero =>
        have := Lz_gap 1
        simp only [Nat.cast_zero, zero_add] at this h01 ⊢
        have e : Lz (1 + 1) = Lz 2 := rfl
        omega
      | succ k ih =>
        have := Lz_gap (k + 2)
        have e : Lz (k + 2 + 1) = Lz (k + 1 + 2) := rfl
        push_cast at this ⊢
        omega
    exact h1 n
  obtain ⟨f, hf, h⟩ := hF _ (hmem i (by omega))
  have h1 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (Lz i) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ one_le_two hLi
  have h2 := (abs_lt.1 h).2
  have h3 := hR f hf
  linarith

end Two
end PVG
