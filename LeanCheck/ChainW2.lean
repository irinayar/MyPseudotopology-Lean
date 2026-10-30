import LeanCheck.ChainW1

/-!
# Subsets of one chain: Theorems F and G in set form, and the join corollaries
(TVGQ-v7 Corollaries 17.4 `chains:Fjoin` and 17.7 `chains:Gjoin`; HamelCharactersTVG_v18 Corollaries D.4, D.7)

For a divisibility chain `m` and a set `U` of indices, the selected terms are `m '' U`.  The enumeration
`selSeq m U` of the selected terms (in increasing order) is a chain sequence; `H(U)` (`HSet m U`) agrees with the
sequence form `HSeq (selSeq m U)` of the earlier files.  We prove:

* `chains_F_set`    : for nonempty `U`, `dual(ξ_{m''U}) = Γ ↔ H(U)`;
* `xi_inf_union`, `lam_inf_union` : the joins of the topologies of two subsets are the topology of the union;
* `Fjoin`           : (Cor. 17.4) no incompatible pair among subsets of one chain;
* `compat_iff_HSet` : (Thm. 17.6) `λ_{m''U}` is compatible iff `H(U)`;
* `Gjoin`           : (Cor. 17.7) the compact-union question inside one chain has a positive answer.
-/

namespace LeanCheck

open Filter Topology

section Bridge

variable {m : ℕ → ℕ} {U : Set ℕ}

/-- The selected terms `m (u₀), m (u₁), …` of `m`, in increasing order of the index set `U`. -/
noncomputable def selSeq (m : ℕ → ℕ) (U : Set ℕ) : ℕ → ℕ := fun i => m (Nat.nth (· ∈ U) i)

lemma selSeq_chain (hm : ChainSeq m) (hU : U.Infinite) : ChainSeq (selSeq m U) where
  pos i := hm.pos _
  dvd i := hm.dvd_of_le (le_of_lt (Nat.nth_strictMono hU (Nat.lt_succ_self i)))
  two i := by
    have h1 := hm.two (Nat.nth (· ∈ U) i)
    have h2 : Nat.nth (· ∈ U) i + 1 ≤ Nat.nth (· ∈ U) (i + 1) := Nat.nth_strictMono hU (Nat.lt_succ_self i)
    exact h1.trans (hm.mono h2)

lemma range_selSeq (hU : U.Infinite) : Set.range (selSeq m U) = m '' U := by
  show Set.range (m ∘ Nat.nth (· ∈ U)) = m '' U
  have h := Nat.range_nth_of_infinite (p := fun x => x ∈ U) hU
  rw [Set.range_comp, h]
  rfl

lemma HSeq_of_HSet (hU : U.Infinite) (h : HSet m U) : HSeq (selSeq m U) := by
  intro A hA
  obtain ⟨L, hL⟩ := h A hA
  refine ⟨L, fun a b hrun => ?_⟩
  by_contra hb
  push_neg at hb
  have := hL (b - a) (fun j => Nat.nth (· ∈ U) (a + j))
    ⟨fun j _ => Nat.nth_mem_of_infinite hU _, fun j hj =>
      ⟨Nat.nth_strictMono hU (by omega), by
        have := hrun (a + j) (by omega) (by omega)
        simpa [selSeq, add_assoc] using this⟩⟩
  omega

lemma HSet_of_HSeq (hm : ChainSeq m) (hU : U.Infinite) (h : HSeq (selSeq m U)) : HSet m U := by
  classical
  intro A hA
  obtain ⟨L, hL⟩ := h A hA
  refine ⟨L, fun k w hw => ?_⟩
  set i : ℕ → ℕ := fun j => Nat.count (· ∈ U) (w j) with hi
  have hnth : ∀ j, j ≤ k → Nat.nth (· ∈ U) (i j) = w j := fun j hj => Nat.nth_count (hw.1 j hj)
  have hmono : ∀ j j', j < j' → j' ≤ k → i j < i j' := fun j j' hjj hj' =>
    Nat.count_strict_mono (hw.1 j (by omega)) (hw.lt hjj hj')
  have hrun : IsRun (selSeq m U) A (i 0) (i k) := by
    intro t ht1 ht2
    have hex : ∃ q, t < i q := ⟨k, ht2⟩
    obtain ⟨q, hq, hmin⟩ : ∃ q, t < i q ∧ ∀ q' < q, i q' ≤ t :=
      ⟨Nat.find hex, Nat.find_spec hex, fun q' hq' => not_lt.1 (Nat.find_min hex hq')⟩
    have hqk : q ≤ k := by
      by_contra h'
      push_neg at h'
      have := hmin k h'
      omega
    have hq0 : q ≠ 0 := by
      rintro rfl
      omega
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have hp : i p ≤ t := hmin p (by omega)
    have hstep := (hw.2 p (by omega)).2
    have hA1 : (selSeq m U (t + 1) : ℝ) ≤ m (w (p + 1)) := by
      rw [← hnth (p + 1) hqk]
      exact Nat.cast_le.2 (hm.mono ((Nat.nth_strictMono hU).monotone hq))
    have hA2 : (m (w p) : ℝ) ≤ selSeq m U t := by
      rw [← hnth p (by omega)]
      exact Nat.cast_le.2 (hm.mono ((Nat.nth_strictMono hU).monotone hp))
    calc (selSeq m U (t + 1) : ℝ) ≤ m (w (p + 1)) := hA1
      _ < A * m (w p) := hstep
      _ ≤ A * selSeq m U t := by gcongr
  have h1 := hL _ _ hrun
  have hlin : ∀ j, j ≤ k → i 0 + j ≤ i j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := hmono j (j + 1) (by omega) hj
      have := ih (by omega)
      omega
  have := hlin k le_rfl
  omega

lemma HSeq_iff_HSet (hm : ChainSeq m) (hU : U.Infinite) : HSeq (selSeq m U) ↔ HSet m U :=
  ⟨HSet_of_HSeq hm hU, HSeq_of_HSet hU⟩

end Bridge

section SetForms

variable {m : ℕ → ℕ}

/-- **Theorem F in set form** (TVGQ 17.3): for nonempty `U`, `dual(ξ_{m''U}) = Γ ↔ H(U)`. -/
theorem chains_F_set (hm : ChainSeq m) (U : Set ℕ) (hne : U.Nonempty) :
    (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (m '' U)) circTop ψ ↔ ψ ∈ Gam) ↔ HSet m U := by
  by_cases hfin : U.Finite
  · constructor
    · intro _; exact HSet_finite hfin
    · intro _ ψ
      exact xi_dual_of_finite (m '' U) (fun c ⟨u, _, hu⟩ => hu ▸ hm.pos u) (hne.image m)
        (hfin.image m) ψ
  · have hU : U.Infinite := hfin
    rw [← HSeq_iff_HSet hm hU, ← range_selSeq hU]
    exact chains_F_seq (selSeq_chain hm hU)

/-- **Theorem G in set form** (TVGQ 17.6): for `U ∋ 0` (so `1 ∈ m '' U`), `λ_{m''U}` is compatible iff `H(U)`. -/
theorem compat_iff_HSet (hm : ChainSeq m) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ m n)
    (hm0 : m 0 = 1) (U : Set ℕ) (h0 : 0 ∈ U) :
    (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (m '' U)).topology _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ↔ HSet m U := by
  by_cases hfin : U.Finite
  · constructor
    · intro _; exact HSet_finite hfin
    · intro _ χ
      exact tors_dual_finite (m '' U) (hfin.image m) ⟨0, h0, hm0⟩ χ
  · have hU : U.Infinite := hfin
    rw [← HSeq_iff_HSet hm hU, ← range_selSeq hU]
    refine chains_G_seq (selSeq_chain hm hU) ?_ ?_
    · intro N hN
      obtain ⟨n0, hn0⟩ := hnull N hN
      refine ⟨n0, fun n hn => hn0 _ ?_⟩
      exact hn.trans ((Nat.nth_strictMono hU).id_le n)
    · show m (Nat.nth (· ∈ U) 0) = 1
      rw [Nat.nth_zero_of_zero h0, hm0]

end SetForms

section Joins

/-- `ξ_{C₁} ∨ ξ_{C₂} = ξ_{C₁ ∪ C₂}` (the join is the finer topology, `⊓` in Mathlib's order). -/
theorem xi_inf_union (C₁ C₂ : Set ℕ) : xi C₁ ⊓ xi C₂ = xi (C₁ ∪ C₂) := by
  have hset : ∀ d ε, xiSet (C₁ ∪ C₂) d ε = xiSet C₁ d ε ∩ xiSet C₂ d ε := by
    intro d ε
    ext q
    simp only [xiSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
    constructor
    · intro h
      exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
    · rintro ⟨h1, h2⟩ c (hc | hc)
      · exact h1 c hc
      · exact h2 c hc
  apply le_antisymm
  · -- `ξ_{C₁} ⊓ ξ_{C₂}` is finer than `ξ_{C₁ ∪ C₂}`
    refine le_of_nhds_le_nhds (fun x => ?_)
    rw [@nhds_inf ℚ (xi C₁) (xi C₂) x]
    refine ((xiBasis (C₁ ∪ C₂)).nhds_hasBasis x).ge_iff.2 ?_
    rintro V ⟨d, hd, ε, hε, rfl⟩
    rw [hset, Set.image_inter (add_right_injective x)]
    refine Filter.inter_mem_inf ?_ ?_
    · exact ((xiBasis C₁).nhds_hasBasis x).mem_of_mem (xiSet_mem C₁ d hd ε hε)
    · exact ((xiBasis C₂).nhds_hasBasis x).mem_of_mem (xiSet_mem C₂ d hd ε hε)
  · -- `ξ_{C₁ ∪ C₂}` is finer than both
    refine le_inf ?_ ?_
    · refine le_of_nhds_le_nhds (fun x => ?_)
      refine ((xiBasis C₁).nhds_hasBasis x).ge_iff.2 ?_
      rintro V ⟨d, hd, ε, hε, rfl⟩
      have : (fun y => x + y) '' xiSet (C₁ ∪ C₂) d ε ⊆ (fun y => x + y) '' xiSet C₁ d ε :=
        Set.image_mono (by rw [hset]; exact Set.inter_subset_left)
      exact Filter.mem_of_superset
        (((xiBasis (C₁ ∪ C₂)).nhds_hasBasis x).mem_of_mem (xiSet_mem (C₁ ∪ C₂) d hd ε hε)) this
    · refine le_of_nhds_le_nhds (fun x => ?_)
      refine ((xiBasis C₂).nhds_hasBasis x).ge_iff.2 ?_
      rintro V ⟨d, hd, ε, hε, rfl⟩
      have : (fun y => x + y) '' xiSet (C₁ ∪ C₂) d ε ⊆ (fun y => x + y) '' xiSet C₂ d ε :=
        Set.image_mono (by rw [hset]; exact Set.inter_subset_right)
      exact Filter.mem_of_superset
        (((xiBasis (C₁ ∪ C₂)).nhds_hasBasis x).mem_of_mem (xiSet_mem (C₁ ∪ C₂) d hd ε hε)) this

/-- `λ_{C₁} ∨ λ_{C₂} = λ_{C₁ ∪ C₂}` on `ℚ/ℤ`. -/
theorem lam_inf_union (C₁ C₂ : Set ℕ) :
    (basisOf C₁).topology ⊓ (basisOf C₂).topology = (basisOf (C₁ ∪ C₂)).topology := by
  have hset : ∀ δ, obs (C₁ ∪ C₂) δ = obs C₁ δ ∩ obs C₂ δ := by
    intro δ
    ext x
    simp only [obs, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
    constructor
    · intro h
      exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
    · rintro ⟨h1, h2⟩ c (hc | hc)
      · exact h1 c hc
      · exact h2 c hc
  apply le_antisymm
  · refine le_of_nhds_le_nhds (fun x => ?_)
    rw [@nhds_inf TorsA ((basisOf C₁).topology) ((basisOf C₂).topology) x]
    refine ((basisOf (C₁ ∪ C₂)).nhds_hasBasis x).ge_iff.2 ?_
    rintro V ⟨δ, hδ, rfl⟩
    rw [hset, Set.image_inter (add_right_injective x)]
    refine Filter.inter_mem_inf ?_ ?_
    · exact ((basisOf C₁).nhds_hasBasis x).mem_of_mem (mem_basisOf hδ)
    · exact ((basisOf C₂).nhds_hasBasis x).mem_of_mem (mem_basisOf hδ)
  · refine le_inf ?_ ?_
    · refine le_of_nhds_le_nhds (fun x => ?_)
      refine ((basisOf C₁).nhds_hasBasis x).ge_iff.2 ?_
      rintro V ⟨δ, hδ, rfl⟩
      have : (fun y => x + y) '' obs (C₁ ∪ C₂) δ ⊆ (fun y => x + y) '' obs C₁ δ :=
        Set.image_mono (by rw [hset]; exact Set.inter_subset_left)
      exact Filter.mem_of_superset
        (((basisOf (C₁ ∪ C₂)).nhds_hasBasis x).mem_of_mem (mem_basisOf hδ)) this
    · refine le_of_nhds_le_nhds (fun x => ?_)
      refine ((basisOf C₂).nhds_hasBasis x).ge_iff.2 ?_
      rintro V ⟨δ, hδ, rfl⟩
      have : (fun y => x + y) '' obs (C₁ ∪ C₂) δ ⊆ (fun y => x + y) '' obs C₂ δ :=
        Set.image_mono (by rw [hset]; exact Set.inter_subset_right)
      exact Filter.mem_of_superset
        (((basisOf (C₁ ∪ C₂)).nhds_hasBasis x).mem_of_mem (mem_basisOf hδ)) this

variable {m : ℕ → ℕ}

/-- **Corollary 17.4 / D.4: no incompatible pair from subsets of one chain.**  For nonempty `S, T`, the join of
`ξ_{m''S}` and `ξ_{m''T}` is `ξ_{m''(S∪T)}`, and if both have full dual `Γ`, so does the join. -/
theorem Fjoin (hm : ChainSeq m) (S T : Set ℕ) (hS : S.Nonempty) (hT : T.Nonempty) :
    xi (m '' S) ⊓ xi (m '' T) = xi (m '' (S ∪ T)) ∧
      ((∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (m '' S)) circTop ψ ↔ ψ ∈ Gam) →
       (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (m '' T)) circTop ψ ↔ ψ ∈ Gam) →
       (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (m '' (S ∪ T))) circTop ψ ↔ ψ ∈ Gam)) := by
  refine ⟨by rw [Set.image_union]; exact xi_inf_union _ _, fun h1 h2 => ?_⟩
  exact (chains_F_set hm (S ∪ T) (hS.mono Set.subset_union_left)).2
    (HSet_union ((chains_F_set hm S hS).1 h1) ((chains_F_set hm T hT).1 h2))

/-- **Corollary 17.7 / D.7: the compact-union question inside one chain.**  Let `S, T` contain the index `0`
(so both selected sets contain `m 0 = 1`).  If `λ_{m''S}` and `λ_{m''T}` are compatible, then so is
`λ_{m''(S∪T)} = λ_{m''S} ∨ λ_{m''T}`.  Finite subsets are allowed. -/
theorem Gjoin (hm : ChainSeq m) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ m n) (hm0 : m 0 = 1)
    (S T : Set ℕ) (h0S : 0 ∈ S) (h0T : 0 ∈ T) :
    (basisOf (m '' S)).topology ⊓ (basisOf (m '' T)).topology = (basisOf (m '' (S ∪ T))).topology ∧
      ((∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (m '' S)).topology _ χ ↔
          ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) →
       (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (m '' T)).topology _ χ ↔
          ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) →
       (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (m '' (S ∪ T))).topology _ χ ↔
          ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ))) := by
  refine ⟨by rw [Set.image_union]; exact lam_inf_union _ _, fun h1 h2 => ?_⟩
  exact (compat_iff_HSet hm hnull hm0 (S ∪ T) (Or.inl h0S)).2
    (HSet_union ((compat_iff_HSet hm hnull hm0 S h0S).1 h1) ((compat_iff_HSet hm hnull hm0 T h0T).1 h2))

end Joins

end LeanCheck
