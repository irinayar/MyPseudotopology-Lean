import Mathlib
import LeanCheck.PGXi

/-!
# PGfour: a PG on the integers without a coreflection into the topological groups

`β` is the 2-adic topology of `ℤ`, `y n = 2 ^ (n ^ 2)`, the indices are split into the infinitely many columns
`{n | (Nat.unpair n).1 = j}`, and the ideal `I` consists of the sets contained in `F + A m r`, where `F` is finite and
`A m r` is the set of the sums `∑ c n * y n` with `c` supported in the first columns and `|c n| ≤ r * 2 ^ n`.

* `admissible` : `I` satisfies (I1)-(I5);
* `no_coarsest` : there is no coarsest group topology all of whose convergent filters converge for the PG of `β` and `I`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

noncomputable section

namespace PG.NoCore

/-- The terms. -/
def y (n : ℕ) : ℤ := 2 ^ (n ^ 2)

def col (n : ℕ) : ℕ := (Nat.unpair n).1

def val (c : ℕ →₀ ℤ) : ℤ := Finsupp.linearCombination ℤ y c

def A (m r : ℕ) : Set ℤ := {z | ∃ c : ℕ →₀ ℤ, (∀ n, c n ≠ 0 → col n ≤ m) ∧ (∀ n, |c n| ≤ r * 2 ^ n) ∧ val c = z}

def I : Set (Set ℤ) := {B | ∃ F : Set ℤ, F.Finite ∧ ∃ m r : ℕ, B ⊆ F + A m r}

theorem val_add (c d : ℕ →₀ ℤ) : val (c + d) = val c + val d := map_add _ _ _

theorem val_sub (c d : ℕ →₀ ℤ) : val (c - d) = val c - val d := map_sub _ _ _

theorem val_neg (c : ℕ →₀ ℤ) : val (-c) = -val c := map_neg _ _

theorem val_single (n : ℕ) (a : ℤ) : val (Finsupp.single n a) = a * y n := by
  rw [val, Finsupp.linearCombination_single, smul_eq_mul]

theorem A_mono {m m' r r' : ℕ} (hm : m ≤ m') (hr : r ≤ r') : A m r ⊆ A m' r' := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => le_trans (h1 n hn) hm, fun n => le_trans (h2 n) ?_, h3⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)

theorem A_add {m m' r r' : ℕ} : A m r + A m' r' ⊆ A (max m m') (r + r') := by
  rintro _ ⟨a, ⟨c, h1, h2, h3⟩, b, ⟨d, g1, g2, g3⟩, rfl⟩
  refine ⟨c + d, fun n hn => ?_, fun n => ?_, by rw [val_add, h3, g3]⟩
  · by_cases hc : c n = 0
    · have hd : d n ≠ 0 := fun h => hn (by rw [Finsupp.add_apply, hc, h, add_zero])
      exact le_trans (g1 n hd) (le_max_right _ _)
    · exact le_trans (h1 n hc) (le_max_left _ _)
  · rw [Finsupp.add_apply]
    refine le_trans (abs_add_le _ _) ?_
    push_cast
    rw [add_mul]
    exact add_le_add (h2 n) (g2 n)

theorem zero_mem_A (m r : ℕ) : (0 : ℤ) ∈ A m r :=
  ⟨0, fun n hn => absurd rfl hn, fun n => by simp, by simp [val]⟩

/-- Digits smaller than the gaps determine the sum. -/
theorem digits_zero (R : ℕ) (d : ℕ →₀ ℤ) (hlow : ∀ i, i ≤ R → d i = 0)
    (hsmall : ∀ i, R < i → |d i| < 2 ^ (2 * i + 1)) (h : val d = 0) : d = 0 := by
  classical
  by_contra hne
  have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hne
  set i := d.support.min' hs with hi
  have hiS : i ∈ d.support := d.support.min'_mem hs
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.1 hiS
  have hiR : R < i := by
    by_contra hle
    exact hdi (hlow i (not_lt.1 hle))
  have hsum : ∑ n ∈ d.support, d n * y n = 0 := by
    rw [← h, val, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun n _ => (smul_eq_mul _ _).symm
  rw [← Finset.sum_erase_add _ _ hiS] at hsum
  have hrest : (2 : ℤ) ^ ((i + 1) ^ 2) ∣ ∑ n ∈ d.support.erase i, d n * y n := by
    refine Finset.dvd_sum fun n hn => Dvd.dvd.mul_left ?_ _
    obtain ⟨hne', hnS⟩ := Finset.mem_erase.1 hn
    have hin : i < n := lt_of_le_of_ne (d.support.min'_le n hnS) (Ne.symm hne')
    exact pow_dvd_pow 2 (Nat.pow_le_pow_left hin 2)
  have hterm : (2 : ℤ) ^ ((i + 1) ^ 2) ∣ d i * y i := by
    have : d i * y i = -(∑ n ∈ d.support.erase i, d n * y n) := by linarith
    rw [this]
    exact hrest.neg_right
  have hsplit : (2 : ℤ) ^ ((i + 1) ^ 2) = 2 ^ (2 * i + 1) * 2 ^ (i ^ 2) := by
    rw [← pow_add]
    congr 1
    ring
  rw [hsplit, y] at hterm
  have h2 : (2 : ℤ) ^ (2 * i + 1) ∣ d i := Int.dvd_of_mul_dvd_mul_right (by positivity) hterm
  have h3 : (2 : ℤ) ^ (2 * i + 1) ∣ |d i| := (dvd_abs _ _).2 h2
  have h4 := Int.le_of_dvd (abs_pos.2 hdi) h3
  exact absurd (hsmall i hiR) (not_lt.2 h4)

/-- Only finitely many terms of the next column lie in `F + A m r`. -/
theorem few_terms (F : Set ℤ) (hF : F.Finite) (m r : ℕ) :
    {n | col n = m + 1 ∧ y n ∈ F + A m r}.Finite := by
  classical
  -- the cut-off
  set R := 2 * r + 3 with hR
  have hbound : ∀ i, R < i → 2 * ((r : ℤ) * 2 ^ i) + 1 < 2 ^ (2 * i + 1) := by
    intro i hi
    have h1 : (r : ℤ) < 2 ^ i := by
      have : r < 2 ^ i := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have h2 : (2 : ℤ) ^ (2 * i + 1) = 2 * (2 ^ i * 2 ^ i) := by
      rw [pow_succ, two_mul i, pow_add]
      ring
    have h3 : ((r : ℤ) + 1) * 2 ^ i ≤ 2 ^ i * 2 ^ i :=
      mul_le_mul_of_nonneg_right (Int.add_one_le_of_lt h1) (by positivity)
    have h4 : (2 : ℤ) ≤ 2 ^ i := by
      calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [h2]
    nlinarith
  by_contra hinf
  have hinf' : ({n | col n = m + 1 ∧ y n ∈ F + A m r} \ Iic R).Infinite :=
    Set.Infinite.sdiff hinf (finite_Iic R)
  have hch : ∀ n, n ∈ ({n | col n = m + 1 ∧ y n ∈ F + A m r} \ Iic R) →
      ∃ f ∈ F, ∃ c : ℕ →₀ ℤ, (∀ k, c k ≠ 0 → col k ≤ m) ∧ (∀ k, |c k| ≤ r * 2 ^ k) ∧ f + val c = y n := by
    rintro n ⟨⟨_, hn⟩, _⟩
    obtain ⟨f, hf, a, ⟨c, h1, h2, h3⟩, h⟩ := hn
    exact ⟨f, hf, c, h1, h2, by rw [h3]; exact h⟩
  choose! f hf c hc1 hc2 hc3 using hch
  -- the low part takes finitely many values
  let low : (ℕ →₀ ℤ) → (Fin (R + 1) → ℤ) := fun d i => d i
  have hmaps : MapsTo (fun n => (f n, low (c n))) ({n | col n = m + 1 ∧ y n ∈ F + A m r} \ Iic R)
      (F ×ˢ (Set.univ.pi fun i : Fin (R + 1) => Icc (-((r : ℤ) * 2 ^ (i : ℕ))) ((r : ℤ) * 2 ^ (i : ℕ)))) := by
    intro n hn
    refine ⟨hf n hn, fun i _ => ?_⟩
    exact abs_le.1 (hc2 n hn i)
  have hfin : (F ×ˢ (Set.univ.pi fun i : Fin (R + 1) =>
      Icc (-((r : ℤ) * 2 ^ (i : ℕ))) ((r : ℤ) * 2 ^ (i : ℕ)))).Finite :=
    hF.prod (Set.Finite.pi fun i => finite_Icc _ _)
  obtain ⟨n, hn, n', hn', hne, heq⟩ := hinf'.exists_ne_map_eq_of_mapsTo hmaps hfin
  have hf' : f n = f n' := (Prod.ext_iff.1 heq).1
  have hlow : ∀ i, i ≤ R → c n i = c n' i := fun i hi =>
    congrFun (Prod.ext_iff.1 heq).2 ⟨i, Nat.lt_succ_of_le hi⟩
  have hnR : R < n := not_le.1 hn.2
  have hnR' : R < n' := not_le.1 hn'.2
  set d : ℕ →₀ ℤ := c n - c n' - Finsupp.single n 1 + Finsupp.single n' 1 with hd
  have hval : val d = 0 := by
    rw [hd, val_add, val_sub, val_sub, val_single, val_single, one_mul, one_mul]
    have h1 := hc3 n hn
    have h2 := hc3 n' hn'
    rw [hf'] at h1
    linarith
  have hdlow : ∀ i, i ≤ R → d i = 0 := by
    intro i hi
    have h1 : n ≠ i := fun h => absurd hnR (not_lt.2 (h ▸ hi))
    have h2 : n' ≠ i := fun h => absurd hnR' (not_lt.2 (h ▸ hi))
    rw [hd]
    simp [hlow i hi, h1, h2]
  have hdsmall : ∀ i, R < i → |d i| < 2 ^ (2 * i + 1) := by
    intro i hi
    have hs : |(-(Finsupp.single n (1 : ℤ) i)) + Finsupp.single n' (1 : ℤ) i| ≤ 1 := by
      rw [Finsupp.single_apply, Finsupp.single_apply]
      by_cases h1 : n = i
      · have h2 : n' ≠ i := fun h => hne (h1.trans h.symm)
        simp [h1, h2]
      · by_cases h2 : n' = i <;> simp [h1, h2]
    have heq' : d i = (c n i - c n' i) + ((-(Finsupp.single n (1 : ℤ) i)) + Finsupp.single n' (1 : ℤ) i) := by
      rw [hd]
      simp only [Finsupp.add_apply, Finsupp.sub_apply]
      ring
    refine lt_of_le_of_lt ?_ (hbound i hi)
    rw [heq', two_mul]
    exact le_trans (abs_add_le _ _) (add_le_add
      (le_trans (abs_sub _ _) (add_le_add (hc2 n hn i) (hc2 n' hn' i))) hs)
  have hzero := digits_zero R d hdlow hdsmall hval
  have hcol : col n = m + 1 := hn.1.1
  have hcn : c n n = 0 := by
    by_contra h
    have := hc1 n hn n h
    omega
  have hcn' : c n' n = 0 := by
    by_contra h
    have := hc1 n' hn' n h
    omega
  have : d n = -1 := by
    rw [hd]
    simp [hcn, hcn', Ne.symm hne]
  rw [hzero, Finsupp.zero_apply] at this
  exact absurd this (by norm_num)

theorem column_infinite (j : ℕ) : {n | col n = j}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k => Nat.pair j k) (fun a b h => ?_) fun k => ?_
  · exact (Nat.pair_eq_pair.1 h).2
  · show (Nat.unpair (Nat.pair j k)).1 = j
    rw [Nat.unpair_pair]

theorem admissible : AdmIdeal I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S ⟨F, hF, m, r, h⟩ B hB
    exact ⟨F, hF, m, r, hB.trans h⟩
  · rintro S ⟨F, hF, m, r, h⟩ B ⟨F', hF', m', r', h'⟩
    refine ⟨F ∪ F', hF.union hF', max m m', max r r', union_subset ?_ ?_⟩
    · exact h.trans (add_subset_add subset_union_left (A_mono (le_max_left _ _) (le_max_left _ _)))
    · exact h'.trans (add_subset_add subset_union_right (A_mono (le_max_right _ _) (le_max_right _ _)))
  · intro x
    refine ⟨{x}, finite_singleton x, 0, 0, fun z hz => ⟨x, rfl, 0, zero_mem_A 0 0, ?_⟩⟩
    rw [mem_singleton_iff.1 hz]
    exact add_zero x
  · rintro ⟨F, hF, m, r, h⟩
    have h1 : {n | col n = m + 1} ⊆ {n | col n = m + 1 ∧ y n ∈ F + A m r} :=
      fun n hn => ⟨hn, h (mem_univ _)⟩
    exact column_infinite (m + 1) ((few_terms F hF m r).subset h1)
  · rintro S ⟨F, hF, m, r, h⟩ B ⟨F', hF', m', r', h'⟩
    refine ⟨F + F', hF.add hF', max m m', r + r', ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨f, hf, d, hd, rfl⟩ := h ha
    obtain ⟨f', hf', d', hd', rfl⟩ := h' hb
    exact ⟨f + f', add_mem_add hf hf', d + d', A_add (add_mem_add hd hd'), add_add_add_comm f f' d d'⟩
  · rintro S ⟨F, hF, m, r, h⟩
    refine ⟨-F, hF.neg, m, r, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨f, hf, a, ⟨c, h1, h2, h3⟩, rfl⟩ := h hs
    refine ⟨-f, by simpa using hf, -a, ⟨-c, fun n hn => h1 n (by simpa using hn),
      fun n => by simpa using h2 n, by rw [val_neg, h3]⟩, (neg_add f a).symm⟩

/-! ### The 2-adic topology and the column topologies -/

/-- The multiples of `2 ^ k`. -/
def mult (k : ℕ) : Set ℤ := {z | (2 : ℤ) ^ k ∣ z}

@[instance_reducible] def adicBasis : AddGroupFilterBasis ℤ :=
  addGroupFilterBasisOfComm (range mult) ⟨_, 0, rfl⟩
    (by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      refine ⟨mult (max a b), ⟨_, rfl⟩, fun z hz => ⟨?_, ?_⟩⟩
      · exact (pow_dvd_pow 2 (le_max_left a b)).trans hz
      · exact (pow_dvd_pow 2 (le_max_right a b)).trans hz)
    (by
      rintro _ ⟨a, rfl⟩
      exact dvd_zero _)
    (by
      rintro _ ⟨a, rfl⟩
      refine ⟨mult a, ⟨a, rfl⟩, ?_⟩
      rintro _ ⟨u, hu, v, hv, rfl⟩
      exact dvd_add hu hv)
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨mult a, ⟨a, rfl⟩, fun z hz => hz.neg_right⟩)

/-- The 2-adic topology. -/
@[instance_reducible] def adic : TopologicalSpace ℤ := adicBasis.topology

/-- The elements of the `k`-th neighbourhood of `0` for the column `j`. -/
def V (j k : ℕ) : Set ℤ :=
  {z | ∃ c : ℕ →₀ ℤ, (∀ n, c n ≠ 0 → col n = j ∧ k ≤ n) ∧ (∀ n, |c n| ≤ 2 ^ (n - k)) ∧ val c = z}

theorem zero_mem_V (j k : ℕ) : (0 : ℤ) ∈ V j k :=
  ⟨0, fun n hn => absurd rfl hn, fun n => by simp, by simp [val]⟩

theorem V_anti (j : ℕ) {k k' : ℕ} (h : k ≤ k') : V j k' ⊆ V j k := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => ⟨(h1 n hn).1, le_trans h (h1 n hn).2⟩, fun n => le_trans (h2 n) ?_, h3⟩
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_left h n)

theorem V_add (j k : ℕ) : V j (k + 1) + V j (k + 1) ⊆ V j k := by
  rintro _ ⟨a, ⟨c, h1, h2, h3⟩, b, ⟨d, g1, g2, g3⟩, rfl⟩
  have key : ∀ n, (c + d) n ≠ 0 → col n = j ∧ k + 1 ≤ n := by
    intro n hn
    by_cases hc : c n = 0
    · exact g1 n fun h => hn (by rw [Finsupp.add_apply, hc, h, add_zero])
    · exact h1 n hc
  refine ⟨c + d, fun n hn => ⟨(key n hn).1, le_trans (Nat.le_succ k) (key n hn).2⟩, fun n => ?_,
    by rw [val_add, h3, g3]⟩
  by_cases h0 : (c + d) n = 0
  · rw [h0, abs_zero]
    positivity
  · have hkn := (key n h0).2
    rw [Finsupp.add_apply]
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add (h2 n) (g2 n)) ?_)
    have e : n - k = n - (k + 1) + 1 := by omega
    rw [e, pow_succ]
    linarith

theorem V_neg (j k : ℕ) : ∀ z ∈ V j k, -z ∈ V j k := by
  rintro z ⟨c, h1, h2, h3⟩
  exact ⟨-c, fun n hn => h1 n (by simpa using hn), fun n => by simpa using h2 n, by rw [val_neg, h3]⟩

theorem V_dvd (j k : ℕ) : V j k ⊆ mult k := by
  rintro z ⟨c, h1, _, rfl⟩
  show (2 : ℤ) ^ k ∣ val c
  rw [val, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.dvd_sum fun n hn => ?_
  rw [smul_eq_mul]
  refine Dvd.dvd.mul_left (pow_dvd_pow 2 ?_) _
  have h := (h1 n (Finsupp.mem_support_iff.1 hn)).2
  exact le_trans h (Nat.le_self_pow two_ne_zero n)

theorem V_sub_A (j : ℕ) : V j 0 ⊆ A j 1 := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => (h1 n hn).1.le, fun n => ?_, h3⟩
  simpa using h2 n

@[instance_reducible] def colBasis (j : ℕ) : AddGroupFilterBasis ℤ :=
  addGroupFilterBasisOfComm (range (V j)) ⟨_, 0, rfl⟩
    (by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨V j (max a b), ⟨_, rfl⟩,
        subset_inter (V_anti j (le_max_left a b)) (V_anti j (le_max_right a b))⟩)
    (by
      rintro _ ⟨a, rfl⟩
      exact zero_mem_V j a)
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨V j (a + 1), ⟨_, rfl⟩, V_add j a⟩)
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨V j a, ⟨a, rfl⟩, fun z hz => V_neg j a z hz⟩)

/-- The group topology of the column `j`. -/
@[instance_reducible] def colTop (j : ℕ) : TopologicalSpace ℤ := (colBasis j).topology

theorem adic_group : @IsTopologicalAddGroup ℤ adic _ := adicBasis.isTopologicalAddGroup

theorem col_group (j : ℕ) : @IsTopologicalAddGroup ℤ (colTop j) _ := (colBasis j).isTopologicalAddGroup

theorem adic_nhds (x : ℤ) : (@nhds ℤ adic x).HasBasis (fun _ : ℕ => True)
    (fun k => (fun z => x + z) '' mult k) := by
  have h := adicBasis.nhds_hasBasis x
  refine h.to_hasBasis ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, trivial, subset_rfl⟩
  · intro k _
    exact ⟨mult k, ⟨k, rfl⟩, subset_rfl⟩

theorem col_nhds (j : ℕ) (x : ℤ) : (@nhds ℤ (colTop j) x).HasBasis (fun _ : ℕ => True)
    (fun k => (fun z => x + z) '' V j k) := by
  have h := (colBasis j).nhds_hasBasis x
  refine h.to_hasBasis ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, trivial, subset_rfl⟩
  · intro k _
    exact ⟨V j k, ⟨k, rfl⟩, subset_rfl⟩

theorem adic_t2 : @T2Space ℤ adic := by
  letI := adic
  haveI := adic_group
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ¬ (2 : ℤ) ^ k ∣ x := by
    refine ⟨x.natAbs, fun h => hx ?_⟩
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
    rw [Int.natAbs_pow]
    exact Nat.lt_two_pow_self
  refine ⟨mult k, ?_, hk⟩
  have := (adic_nhds 0).mem_of_mem (i := k) trivial
  simpa using this

/-- The column topologies are convergent for the PG. -/
theorem col_converges (j : ℕ) (x : ℤ) :
    @xi ℤ adic I (@nhds ℤ (colTop j) x) x := by
  letI := adic
  refine ⟨?_, ?_, {x} + A j 1, ⟨{x}, finite_singleton x, j, 1, subset_rfl⟩, ?_⟩
  · exact @nhds_neBot ℤ (colTop j) x
  · refine ((col_nhds j x).le_basis_iff (adic_nhds x)).2 fun k _ => ⟨k, trivial, ?_⟩
    exact image_mono (V_dvd j k)
  · refine (col_nhds j x).mem_iff.2 ⟨0, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact add_mem_add (mem_singleton x) (V_sub_A j hz)

/-- There is no coarsest group topology all of whose convergent filters converge for the PG. -/
theorem no_coarsest : ¬ ∃ σ : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ σ _ ∧
    (∀ x : ℤ, @xi ℤ adic I (@nhds ℤ σ x) x) ∧
    ∀ τ : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ τ _ →
      (∀ x : ℤ, @xi ℤ adic I (@nhds ℤ τ x) x) → τ ≤ σ := by
  rintro ⟨σ, _, hσ, hmin⟩
  obtain ⟨_, _, S, ⟨F, hF, m, r, hS⟩, hSn⟩ := hσ 0
  have hle : colTop (m + 1) ≤ σ := hmin _ (col_group (m + 1)) fun x => col_converges (m + 1) x
  have h1 : S ∈ @nhds ℤ (colTop (m + 1)) 0 := nhds_mono hle hSn
  obtain ⟨k, _, hk⟩ := (col_nhds (m + 1) 0).mem_iff.1 h1
  have hsub : {n | col n = m + 1} \ Iio k ⊆ {n | col n = m + 1 ∧ y n ∈ F + A m r} := by
    rintro n ⟨hn, hnk⟩
    refine ⟨hn, hS (hk ⟨y n, ?_, zero_add _⟩)⟩
    refine ⟨Finsupp.single n 1, fun i hi => ?_, fun i => ?_, by rw [val_single, one_mul]⟩
    · have : n = i := by
        by_contra h
        exact hi (Finsupp.single_eq_of_ne (Ne.symm h))
      subst this
      exact ⟨hn, not_lt.1 hnk⟩
    · by_cases h : n = i
      · subst h
        rw [Finsupp.single_eq_same, abs_one]
        exact one_le_pow₀ (by norm_num)
      · rw [Finsupp.single_eq_of_ne (Ne.symm h), abs_zero]
        positivity
  exact (column_infinite (m + 1)).sdiff (finite_Iio k) ((few_terms F hF m r).subset hsub)

end PG.NoCore
