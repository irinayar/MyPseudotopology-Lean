import Mathlib
import LeanCheck.PGFourCoreflection

/-!
# PGfour: on every infinite abelian group some PG of a topology and an ideal has no coreflection

`y : ℕ → G` is *sparse* if its terms are nonzero and, for each `r`, every relation `∑ d i • y i = 0` with
`|d i| ≤ r * 2 ^ i` and `d` vanishing up to a bound depending on `r` has all terms `d i • y i` equal to `0`.

* `exists_sparse` : every infinite abelian group has a sparse sequence;
* for a sparse `y`, `admissible` : the ideal `I y` of the sets contained in `F + A y m r` satisfies (I1)-(I5), and
  `top_t2` : the group topology `top y univ` is Hausdorff;
* `no_coarsest` : there is no coarsest group topology all of whose convergent filters converge for the PG;
* `every_infinite_group` : the conclusion for every infinite abelian group;
* `no_ideal_of_finite` : a finite abelian group carries no such ideal.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

noncomputable section

namespace PG.NoCoreAll

open PG.NoCore (col column_infinite)

variable {G : Type*} [AddCommGroup G]

def val (y : ℕ → G) : (ℕ →₀ ℤ) →ₗ[ℤ] G := Finsupp.linearCombination ℤ y

theorem val_single (y : ℕ → G) (n : ℕ) (a : ℤ) : val y (Finsupp.single n a) = a • y n := by
  rw [val, Finsupp.linearCombination_single]

theorem val_eq_sum (y : ℕ → G) (c : ℕ →₀ ℤ) : val y c = ∑ i ∈ c.support, c i • y i := by
  rw [val, Finsupp.linearCombination_apply, Finsupp.sum]

structure Sparse (y : ℕ → G) : Prop where
  ne : ∀ n, y n ≠ 0
  digits : ∀ r : ℕ, ∃ R : ℕ, ∀ d : ℕ →₀ ℤ, (∀ i, i ≤ R → d i = 0) → (∀ i, |d i| ≤ r * 2 ^ i) →
    val y d = 0 → ∀ i, d i • y i = 0

def A (y : ℕ → G) (m r : ℕ) : Set G :=
  {z | ∃ c : ℕ →₀ ℤ, (∀ n, c n ≠ 0 → col n ≤ m) ∧ (∀ n, |c n| ≤ r * 2 ^ n) ∧ val y c = z}

def I (y : ℕ → G) : Set (Set G) := {B | ∃ F : Set G, F.Finite ∧ ∃ m r : ℕ, B ⊆ F + A y m r}

variable {y : ℕ → G}

theorem A_mono {m m' r r' : ℕ} (hm : m ≤ m') (hr : r ≤ r') : A y m r ⊆ A y m' r' := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => le_trans (h1 n hn) hm, fun n => le_trans (h2 n) ?_, h3⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)

theorem A_add {m m' r r' : ℕ} : A y m r + A y m' r' ⊆ A y (max m m') (r + r') := by
  rintro _ ⟨a, ⟨c, h1, h2, h3⟩, b, ⟨d, g1, g2, g3⟩, rfl⟩
  refine ⟨c + d, fun n hn => ?_, fun n => ?_, by rw [map_add, h3, g3]⟩
  · by_cases hc : c n = 0
    · have hd : d n ≠ 0 := fun h => hn (by rw [Finsupp.add_apply, hc, h, add_zero])
      exact le_trans (g1 n hd) (le_max_right _ _)
    · exact le_trans (h1 n hc) (le_max_left _ _)
  · rw [Finsupp.add_apply]
    refine le_trans (abs_add_le _ _) ?_
    push_cast
    rw [add_mul]
    exact add_le_add (h2 n) (g2 n)

theorem zero_mem_A (m r : ℕ) : (0 : G) ∈ A y m r :=
  ⟨0, fun n hn => absurd rfl hn, fun n => by simp, map_zero _⟩

/-- Only finitely many terms of the next column lie in `F + A y m r`. -/
theorem few_terms (hy : Sparse y) (F : Set G) (hF : F.Finite) (m r : ℕ) :
    {n | col n = m + 1 ∧ y n ∈ F + A y m r}.Finite := by
  classical
  obtain ⟨R, hR⟩ := hy.digits (2 * r + 1)
  by_contra hinf
  have hinf' : ({n | col n = m + 1 ∧ y n ∈ F + A y m r} \ Iic R).Infinite :=
    Set.Infinite.sdiff hinf (finite_Iic R)
  have hch : ∀ n, n ∈ ({n | col n = m + 1 ∧ y n ∈ F + A y m r} \ Iic R) →
      ∃ f ∈ F, ∃ c : ℕ →₀ ℤ, (∀ k, c k ≠ 0 → col k ≤ m) ∧ (∀ k, |c k| ≤ r * 2 ^ k) ∧ f + val y c = y n := by
    rintro n ⟨⟨_, hn⟩, _⟩
    obtain ⟨f, hf, a, ⟨c, h1, h2, h3⟩, h⟩ := hn
    exact ⟨f, hf, c, h1, h2, by rw [h3]; exact h⟩
  choose! f hf c hc1 hc2 hc3 using hch
  let low : (ℕ →₀ ℤ) → (Fin (R + 1) → ℤ) := fun d i => d i
  have hmaps : MapsTo (fun n => (f n, low (c n))) ({n | col n = m + 1 ∧ y n ∈ F + A y m r} \ Iic R)
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
  have hval : val y d = 0 := by
    rw [hd, map_add, map_sub, map_sub, val_single, val_single, one_zsmul, one_zsmul]
    have h1 := hc3 n hn
    have h2 := hc3 n' hn'
    rw [hf'] at h1
    rw [← h1, ← h2]
    abel
  have hdlow : ∀ i, i ≤ R → d i = 0 := by
    intro i hi
    have h1 : n ≠ i := fun h => absurd hnR (not_lt.2 (h ▸ hi))
    have h2 : n' ≠ i := fun h => absurd hnR' (not_lt.2 (h ▸ hi))
    rw [hd]
    simp [hlow i hi, h1, h2]
  have hdbound : ∀ i, |d i| ≤ ((2 * r + 1 : ℕ) : ℤ) * 2 ^ i := by
    intro i
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
    have h1 : (1 : ℤ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have h2 : |d i| ≤ (r : ℤ) * 2 ^ i + (r : ℤ) * 2 ^ i + 1 := by
      rw [heq']
      exact le_trans (abs_add_le _ _) (add_le_add
        (le_trans (abs_sub _ _) (add_le_add (hc2 n hn i) (hc2 n' hn' i))) hs)
    refine le_trans h2 ?_
    push_cast
    nlinarith
  have hzero := hR d hdlow hdbound hval n
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
  rw [this, neg_one_zsmul, neg_eq_zero] at hzero
  exact hy.ne n hzero

theorem admissible (hy : Sparse y) : AdmIdeal (I y) := by
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
    have h1 : {n | col n = m + 1} ⊆ {n | col n = m + 1 ∧ y n ∈ F + A y m r} :=
      fun n hn => ⟨hn, h (mem_univ _)⟩
    exact column_infinite (m + 1) ((few_terms hy F hF m r).subset h1)
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
      fun n => by simpa using h2 n, by rw [map_neg, h3]⟩, (neg_add f a).symm⟩

/-! ### The topologies -/

def V (y : ℕ → G) (J : Set ℕ) (k : ℕ) : Set G :=
  {z | ∃ c : ℕ →₀ ℤ, (∀ n, c n ≠ 0 → n ∈ J ∧ k ≤ n) ∧ (∀ n, |c n| ≤ 2 ^ (n - k)) ∧ val y c = z}

theorem zero_mem_V (J : Set ℕ) (k : ℕ) : (0 : G) ∈ V y J k :=
  ⟨0, fun n hn => absurd rfl hn, fun n => by simp, map_zero _⟩

theorem V_anti (J : Set ℕ) {k k' : ℕ} (h : k ≤ k') : V y J k' ⊆ V y J k := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => ⟨(h1 n hn).1, le_trans h (h1 n hn).2⟩, fun n => le_trans (h2 n) ?_, h3⟩
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_left h n)

theorem V_set {J J' : Set ℕ} (h : J ⊆ J') (k : ℕ) : V y J k ⊆ V y J' k := by
  rintro z ⟨c, h1, h2, h3⟩
  exact ⟨c, fun n hn => ⟨h (h1 n hn).1, (h1 n hn).2⟩, h2, h3⟩

theorem V_add (J : Set ℕ) (k : ℕ) : V y J (k + 1) + V y J (k + 1) ⊆ V y J k := by
  rintro _ ⟨a, ⟨c, h1, h2, h3⟩, b, ⟨d, g1, g2, g3⟩, rfl⟩
  have key : ∀ n, (c + d) n ≠ 0 → n ∈ J ∧ k + 1 ≤ n := by
    intro n hn
    by_cases hc : c n = 0
    · exact g1 n fun h => hn (by rw [Finsupp.add_apply, hc, h, add_zero])
    · exact h1 n hc
  refine ⟨c + d, fun n hn => ⟨(key n hn).1, le_trans (Nat.le_succ k) (key n hn).2⟩, fun n => ?_,
    by rw [map_add, h3, g3]⟩
  by_cases h0 : (c + d) n = 0
  · rw [h0, abs_zero]
    positivity
  · have hkn := (key n h0).2
    rw [Finsupp.add_apply]
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add (h2 n) (g2 n)) ?_)
    have e : n - k = n - (k + 1) + 1 := by omega
    rw [e, pow_succ]
    linarith

theorem V_neg (J : Set ℕ) (k : ℕ) : ∀ z ∈ V y J k, -z ∈ V y J k := by
  rintro z ⟨c, h1, h2, h3⟩
  exact ⟨-c, fun n hn => h1 n (by simpa using hn), fun n => by simpa using h2 n, by rw [map_neg, h3]⟩

@[instance_reducible] def basis (y : ℕ → G) (J : Set ℕ) : AddGroupFilterBasis G :=
  addGroupFilterBasisOfComm (range (V y J)) ⟨_, 0, rfl⟩
    (by
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨V y J (max a b), ⟨_, rfl⟩,
        subset_inter (V_anti J (le_max_left a b)) (V_anti J (le_max_right a b))⟩)
    (by
      rintro _ ⟨a, rfl⟩
      exact zero_mem_V J a)
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨V y J (a + 1), ⟨_, rfl⟩, V_add J a⟩)
    (by
      rintro _ ⟨a, rfl⟩
      exact ⟨V y J a, ⟨a, rfl⟩, fun z hz => V_neg J a z hz⟩)

/-- The group topology with the base `V y J k`. -/
@[instance_reducible] def top (y : ℕ → G) (J : Set ℕ) : TopologicalSpace G := (basis y J).topology

theorem top_group (J : Set ℕ) : @IsTopologicalAddGroup G (top y J) _ := (basis y J).isTopologicalAddGroup

theorem top_nhds (J : Set ℕ) (x : G) : (@nhds G (top y J) x).HasBasis (fun _ : ℕ => True)
    (fun k => (fun z => x + z) '' V y J k) := by
  have h := (basis y J).nhds_hasBasis x
  refine h.to_hasBasis ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact ⟨k, trivial, subset_rfl⟩
  · intro k _
    exact ⟨V y J k, ⟨k, rfl⟩, subset_rfl⟩

theorem top_t2 (hy : Sparse y) : @T2Space G (top y univ) := by
  classical
  letI := top y univ
  have := top_group (y := y) univ
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hno
  have hall : ∀ k, x ∈ V y univ k := by
    intro k
    by_contra hk
    refine hno ⟨V y univ k, ?_, hk⟩
    have := (top_nhds (y := y) univ 0).mem_of_mem (i := k) trivial
    simpa using this
  obtain ⟨R, hR⟩ := hy.digits 1
  obtain ⟨c1, h1, h2, h3⟩ := hall (R + 1)
  set M := max (R + 1) (c1.support.sup id + 1) with hM
  obtain ⟨c2, g1, g2, g3⟩ := hall M
  have hdisj : ∀ i, c1 i ≠ 0 → c2 i = 0 := by
    intro i hi
    by_contra h
    have hle : i ≤ c1.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 hi)
    have := (g1 i h).2
    omega
  have hz := hR (c1 - c2) (fun i hi => by
      have e1 : c1 i = 0 := by
        by_contra h
        have := (h1 i h).2
        omega
      have e2 : c2 i = 0 := by
        by_contra h
        have := (g1 i h).2
        omega
      rw [Finsupp.sub_apply, e1, e2, sub_zero])
    (fun i => by
      have hp : ∀ k : ℕ, (2 : ℤ) ^ (i - k) ≤ ((1 : ℕ) : ℤ) * 2 ^ i := by
        intro k
        push_cast
        rw [one_mul]
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le i k)
      rw [Finsupp.sub_apply]
      by_cases hc : c1 i = 0
      · rw [hc, zero_sub, abs_neg]
        exact le_trans (g2 i) (hp M)
      · rw [hdisj i hc, sub_zero]
        exact le_trans (h2 i) (hp (R + 1)))
    (by rw [map_sub, h3, g3, sub_self])
  apply hx
  rw [← h3, val_eq_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finsupp.mem_support_iff.1 hi
  have := hz i
  rwa [Finsupp.sub_apply, hdisj i hi', sub_zero] at this

/-- The column topologies converge for the PG. -/
theorem col_converges (j : ℕ) (x : G) :
    @xi G (top y univ) (I y) (@nhds G (top y {n | col n = j}) x) x := by
  letI := top y univ
  refine ⟨?_, ?_, {x} + A y j 1, ⟨{x}, finite_singleton x, j, 1, subset_rfl⟩, ?_⟩
  · exact @nhds_neBot G (top y {n | col n = j}) x
  · refine ((top_nhds _ x).le_basis_iff (top_nhds univ x)).2 fun k _ => ⟨k, trivial, ?_⟩
    exact image_mono (V_set (subset_univ _) k)
  · refine (top_nhds _ x).mem_iff.2 ⟨0, trivial, ?_⟩
    rintro _ ⟨z, ⟨c, h1, h2, h3⟩, rfl⟩
    refine add_mem_add (mem_singleton x) ⟨c, fun n hn => (h1 n hn).1.le, fun n => ?_, h3⟩
    simpa using h2 n

/-- There is no coarsest group topology all of whose convergent filters converge for the PG. -/
theorem no_coarsest (hy : Sparse y) : ¬ ∃ σ : TopologicalSpace G, @IsTopologicalAddGroup G σ _ ∧
    (∀ x : G, @xi G (top y univ) (I y) (@nhds G σ x) x) ∧
    ∀ τ : TopologicalSpace G, @IsTopologicalAddGroup G τ _ →
      (∀ x : G, @xi G (top y univ) (I y) (@nhds G τ x) x) → τ ≤ σ := by
  rintro ⟨σ, _, hσ, hmin⟩
  obtain ⟨_, _, S, ⟨F, hF, m, r, hS⟩, hSn⟩ := hσ 0
  have hle : top y {n | col n = m + 1} ≤ σ :=
    hmin _ (top_group _) fun x => col_converges (m + 1) x
  have h1 : S ∈ @nhds G (top y {n | col n = m + 1}) 0 := nhds_mono hle hSn
  obtain ⟨k, _, hk⟩ := (top_nhds _ 0).mem_iff.1 h1
  have hsub : {n | col n = m + 1} \ Iio k ⊆ {n | col n = m + 1 ∧ y n ∈ F + A y m r} := by
    rintro n ⟨hn, hnk⟩
    refine ⟨hn, hS (hk ⟨y n, ?_, zero_add _⟩)⟩
    refine ⟨Finsupp.single n 1, fun i hi => ?_, fun i => ?_, by rw [val_single, one_zsmul]⟩
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
  exact (column_infinite (m + 1)).sdiff (finite_Iio k) ((few_terms hy F hF m r).subset hsub)

/-! ### Every infinite abelian group has a sparse sequence -/

/-- An element of infinite order. -/
theorem sparse_of_infinite_order (x : G) (hx : ¬ IsOfFinAddOrder x) :
    ∃ y : ℕ → G, Sparse y := by
  have hinj : Function.Injective fun n : ℤ => n • x := injective_zsmul_iff_not_isOfFinAddOrder.2 hx
  have h0 : ∀ a : ℤ, a • x = 0 → a = 0 := fun a ha => hinj (by simp [ha])
  refine ⟨fun n => (PG.NoCore.y n) • x, fun n h => ?_, fun r => ⟨r, fun d hlow hb hval i => ?_⟩⟩
  · have := h0 _ h
    exact pow_ne_zero _ two_ne_zero this
  · have hsum : val (fun n => (PG.NoCore.y n) • x) d = (PG.NoCore.val d) • x := by
      rw [val_eq_sum, PG.NoCore.val, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_smul]
    have hd : d = 0 := by
      refine PG.NoCore.digits_zero r d hlow (fun i hi => ?_) (h0 _ (hsum ▸ hval))
      refine lt_of_le_of_lt (hb i) ?_
      have h1 : r < 2 ^ i := lt_trans hi Nat.lt_two_pow_self
      have h2 : r * 2 ^ i < 2 ^ i * 2 ^ i := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      have h3 : (2 : ℕ) ^ i * 2 ^ i ≤ 2 ^ (2 * i + 1) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast lt_of_lt_of_le h2 h3
    rw [hd, Finsupp.zero_apply, zero_zsmul]

/-- Infinitely many elements of prime order in a torsion group. -/
theorem sparse_of_primes (htor : ∀ x : G, IsOfFinAddOrder x)
    (hP : {x : G | (addOrderOf x).Prime}.Infinite) : ∃ y : ℕ → G, Sparse y := by
  classical
  have hfin : ∀ l : List G, (AddSubgroup.closure {a | a ∈ l} : Set G).Finite := by
    intro l
    induction l with
    | nil =>
      refine (finite_singleton (0 : G)).subset fun x hx => ?_
      have : AddSubgroup.closure {a : G | a ∈ ([] : List G)} = ⊥ := by
        rw [AddSubgroup.closure_eq_bot_iff]
        intro y hy
        exact absurd hy List.not_mem_nil
      rw [this] at hx
      exact hx
    | cons b l ih =>
      have hz : (AddSubgroup.zmultiples b : Set G).Finite := by
        have h1 := (htor b).finite_zmultiples
        exact h1
      refine (hz.image2 (· + ·) ih).subset fun x hx => ?_
      have hle : AddSubgroup.closure {a : G | a ∈ b :: l}
          ≤ AddSubgroup.zmultiples b ⊔ AddSubgroup.closure {a : G | a ∈ l} := by
        rw [AddSubgroup.closure_le]
        intro y hy
        rcases List.mem_cons.1 hy with h | h
        · rw [h]
          exact AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples b)
        · exact AddSubgroup.mem_sup_right (AddSubgroup.subset_closure h)
      obtain ⟨u, hu, v, hv, huv⟩ := AddSubgroup.mem_sup.1 (hle hx)
      exact ⟨u, hu, v, hv, huv⟩
  have pick : ∀ l : List G, ∃ x : G, (addOrderOf x).Prime ∧ x ∉ AddSubgroup.closure {a | a ∈ l} := by
    intro l
    obtain ⟨x, hx, hxn⟩ := (hP.sdiff (hfin l)).nonempty
    exact ⟨x, hx, hxn⟩
  choose g hg hgn using pick
  let seq : ℕ → List G := fun n => Nat.rec [] (fun _ l => g l :: l) n
  let y : ℕ → G := fun n => g (seq n)
  have hseq : ∀ n, seq (n + 1) = y n :: seq n := fun n => rfl
  have hmem : ∀ n i, i < n → y i ∈ seq n := by
    intro n
    induction n with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      rw [hseq, List.mem_cons]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact Or.inr (ih i h)
      · exact Or.inl (by rw [h])
  have indep : ∀ n, ∀ d : ℕ →₀ ℤ, d.support ⊆ Finset.range n → val y d = 0 → ∀ i, d i • y i = 0 := by
    intro n
    induction n with
    | zero =>
      intro d hd _ i
      have : d = 0 := by
        rw [← Finsupp.support_eq_empty]
        exact Finset.subset_empty.1 (by simpa using hd)
      rw [this, Finsupp.zero_apply, zero_zsmul]
    | succ n ih =>
      intro d hd hval
      have hsplit : val y (d.erase n) + d n • y n = 0 := by
        rw [← val_single y n (d n), ← map_add, Finsupp.erase_add_single]
        exact hval
      have hsup : (d.erase n).support ⊆ Finset.range n := by
        intro i hi
        rw [Finsupp.support_erase, Finset.mem_erase] at hi
        have := Finset.mem_range.1 (hd hi.2)
        exact Finset.mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 this) hi.1)
      have hcl : val y (d.erase n) ∈ AddSubgroup.closure {a | a ∈ seq n} := by
        rw [val_eq_sum]
        refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
        exact AddSubgroup.subset_closure (hmem n i (Finset.mem_range.1 (hsup hi)))
      have hdn : d n • y n = 0 := by
        by_contra h
        have hp : (addOrderOf (y n)).Prime := hg (seq n)
        have h1 : d n • y n ∈ AddSubgroup.closure {a | a ∈ seq n} := by
          rw [eq_neg_of_add_eq_zero_right hsplit]
          exact AddSubgroup.neg_mem _ hcl
        have hnd : ¬ ((addOrderOf (y n) : ℤ) ∣ d n) := fun hdvd =>
          h (addOrderOf_dvd_iff_zsmul_eq_zero.1 hdvd)
        have hcop : IsCoprime (addOrderOf (y n) : ℤ) (d n) :=
          (Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hnd
        obtain ⟨a, b, hab⟩ := hcop
        have h2 : y n = b • (d n • y n) := by
          have h3 : (a * (addOrderOf (y n) : ℤ) + b * d n) • y n = y n := by
            rw [hab, one_zsmul]
          rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, addOrderOf_nsmul_eq_zero, zsmul_zero,
            zero_add] at h3
          exact h3.symm
        refine hgn (seq n) ?_
        show y n ∈ AddSubgroup.closure {a | a ∈ seq n}
        rw [h2]
        exact AddSubgroup.zsmul_mem _ h1 _
      intro i
      have hrest : val y (d.erase n) = 0 := by rwa [hdn, add_zero] at hsplit
      by_cases hin : i = n
      · rw [hin]
        exact hdn
      · have := ih (d.erase n) hsup hrest i
        rwa [Finsupp.erase_ne hin] at this
  refine ⟨y, fun n h => ?_, fun r => ⟨0, fun d _ _ hval i => ?_⟩⟩
  · have hp : (addOrderOf (y n)).Prime := hg (seq n)
    rw [h, addOrderOf_zero] at hp
    exact Nat.not_prime_one hp
  · exact indep (d.support.sup id + 1) d
      (fun j hj => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))) hval i

/-- A chain `p • w (k+1) = w k` with `w k` of order `p ^ (a + k)` gives a sparse sequence. -/
theorem sparse_of_chain (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (w : ℕ → G)
    (hord : ∀ k, addOrderOf (w k) = p ^ (a + k)) (hstep : ∀ k, p • w (k + 1) = w k) :
    ∃ y : ℕ → G, Sparse y := by
  classical
  have hdown : ∀ t k, p ^ t • w (k + t) = w k := by
    intro t
    induction t with
    | zero => intro k; simp
    | succ t ih =>
      intro k
      rw [pow_succ, mul_smul, ← add_assoc, hstep]
      exact ih k
  have hkill : ∀ k s, a + k ≤ s → p ^ s • w k = 0 := by
    intro k s h
    exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (by rw [hord]; exact pow_dvd_pow p h)
  refine ⟨fun n => w (n ^ 2), fun n h => ?_, fun r => ⟨r + a + 2, fun d hlow hb hval => ?_⟩⟩
  · have h1 := hord (n ^ 2)
    rw [h, addOrderOf_zero] at h1
    have : 1 < p ^ (a + n ^ 2) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  by_contra hno
  push Not at hno
  set T := d.support.filter (fun i => d i • w (i ^ 2) ≠ 0) with hT
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hno
    refine ⟨i, Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 fun h => hi ?_, hi⟩⟩
    rw [h, zero_zsmul]
  set N := T.max' hTne with hN
  have hNT : N ∈ T := T.max'_mem hTne
  obtain ⟨hNs, hNnz⟩ := Finset.mem_filter.1 hNT
  have hNR : r + a + 2 < N := by
    by_contra h
    exact (Finsupp.mem_support_iff.1 hNs) (hlow N (not_lt.1 h))
  set t := a + (N - 1) ^ 2 with ht
  have hsq : (N - 1) ^ 2 + (2 * N - 1) = N ^ 2 := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]
    have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
    rw [this]
    ring
  have hrel : ∑ i ∈ d.support, p ^ t • (d i • w (i ^ 2)) = 0 := by
    rw [← Finset.smul_sum, ← val_eq_sum (fun n => w (n ^ 2)), hval, smul_zero]
  have hothers : ∀ i ∈ d.support, i ≠ N → p ^ t • (d i • w (i ^ 2)) = 0 := by
    intro i hi hiN
    rcases lt_or_gt_of_ne hiN with h | h
    · have hle : a + i ^ 2 ≤ t := by
        have : i ^ 2 ≤ (N - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      rw [smul_comm, hkill _ _ hle, zsmul_zero]
    · have : d i • w (i ^ 2) = 0 := by
        by_contra hc
        have := T.le_max' i (Finset.mem_filter.2 ⟨hi, hc⟩)
        omega
      rw [this, smul_zero]
  rw [Finset.sum_eq_single_of_mem N hNs hothers] at hrel
  have hexp : N ^ 2 = (2 * N - 1 - a) + t := by omega
  have hrel' : d N • w (2 * N - 1 - a) = 0 := by
    rw [smul_comm, hexp, hdown] at hrel
    exact hrel
  have hdvd : (addOrderOf (w (2 * N - 1 - a)) : ℤ) ∣ d N := addOrderOf_dvd_iff_zsmul_eq_zero.2 hrel'
  rw [hord] at hdvd
  have hexp2 : a + (2 * N - 1 - a) = 2 * N - 1 := by omega
  rw [hexp2] at hdvd
  have hsmall : |d N| < (p ^ (2 * N - 1) : ℕ) := by
    refine lt_of_le_of_lt (hb N) ?_
    have h1 : r < 2 ^ (N - 1) := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : r * 2 ^ N < 2 ^ (2 * N - 1) := by
      have e : 2 ^ (2 * N - 1) = 2 ^ (N - 1) * 2 ^ N := by
        rw [← pow_add]
        congr 1
        omega
      rw [e]
      exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    have h3 : r * 2 ^ N < p ^ (2 * N - 1) := lt_of_lt_of_le h2 (Nat.pow_le_pow_left hp.two_le _)
    exact_mod_cast h3
  have hzero : d N = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd hsmall
  exact hNnz (by rw [hzero, zero_zsmul])

/-- A torsion group that is infinite and has only finitely many elements of prime order has such a chain. -/
theorem chain_of_finite_primes [Infinite G] (htor : ∀ x : G, IsOfFinAddOrder x)
    (hP : {x : G | (addOrderOf x).Prime}.Finite) : ∃ y : ℕ → G, Sparse y := by
  classical
  have hpos : ∀ x : G, 0 < addOrderOf x := fun x => (htor x).addOrderOf_pos
  let lev : G → ℕ := fun x => (addOrderOf x).primeFactorsList.length
  let par : G → G := fun x => (addOrderOf x).minFac • x
  have hne1 : ∀ x : G, ∀ n, lev x = n + 1 → addOrderOf x ≠ 1 := by
    intro x n h h1
    simp [lev, h1] at h
  have hordpar : ∀ x : G, addOrderOf x ≠ 1 → addOrderOf (par x) * (addOrderOf x).minFac = addOrderOf x := by
    intro x hx
    have hd : (addOrderOf x).minFac ∣ addOrderOf x := Nat.minFac_dvd _
    have hm : (addOrderOf x).minFac ≠ 0 := (Nat.minFac_pos _).ne'
    rw [show addOrderOf (par x) = addOrderOf x / (addOrderOf x).minFac from by
      rw [show par x = (addOrderOf x).minFac • x from rfl, addOrderOf_nsmul' x hm, Nat.gcd_eq_right hd]]
    exact Nat.div_mul_cancel hd
  have hlevpar : ∀ x : G, ∀ n, lev x = n + 1 → lev (par x) = n := by
    intro x n h
    have h1 := hne1 x n h
    have h2 := hordpar x h1
    have hq : (addOrderOf x).minFac.Prime := Nat.minFac_prime h1
    have h3 := Nat.perm_primeFactorsList_mul (hpos (par x)).ne' hq.ne_zero
    rw [h2, Nat.primeFactorsList_prime hq] at h3
    have h4 := h3.length_eq
    rw [List.length_append, List.length_singleton] at h4
    have : lev x = lev (par x) + 1 := h4
    omega
  -- levels are finite
  set Q : Set ℕ := addOrderOf '' {x : G | (addOrderOf x).Prime} with hQ
  have hQfin : Q.Finite := hP.image _
  have hroots : ∀ q ∈ Q, ∀ z : G, {x : G | q • x = z}.Finite := by
    rintro q ⟨g, hg, rfl⟩ z
    have hq : (addOrderOf g).Prime := hg
    rcases {x : G | addOrderOf g • x = z}.eq_empty_or_nonempty with h | ⟨x0, hx0⟩
    · rw [h]
      exact finite_empty
    refine ((hP.insert 0).image fun d => x0 + d).subset fun x hx => ?_
    refine ⟨x - x0, ?_, by abel⟩
    have h0 : addOrderOf g • (x - x0) = 0 := by
      rw [smul_sub, show addOrderOf g • x = z from hx, show addOrderOf g • x0 = z from hx0, sub_self]
    rcases (Nat.dvd_prime hq).1 (addOrderOf_dvd_of_nsmul_eq_zero h0) with h | h
    · exact Or.inl (AddMonoid.addOrderOf_eq_one_iff.1 h)
    · refine Or.inr ?_
      show (addOrderOf (x - x0)).Prime
      rw [h]
      exact hq
  have hminQ : ∀ x : G, addOrderOf x ≠ 1 → (addOrderOf x).minFac ∈ Q := by
    intro x hx
    set q := (addOrderOf x).minFac with hqd
    have hq : q.Prime := Nat.minFac_prime hx
    have hd : q ∣ addOrderOf x := Nat.minFac_dvd _
    have hk : addOrderOf x / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (hpos x) hd) hq.pos).ne'
    have h1 : addOrderOf ((addOrderOf x / q) • x) = q := by
      rw [addOrderOf_nsmul' x hk, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
        Nat.div_div_self hd (hpos x).ne']
    exact ⟨_, by show (addOrderOf ((addOrderOf x / q) • x)).Prime; rw [h1]; exact hq, h1⟩
  have hfinlev : ∀ n, {x : G | lev x = n}.Finite := by
    intro n
    induction n with
    | zero =>
      refine (finite_singleton (0 : G)).subset fun x hx => ?_
      have h0 : (addOrderOf x).primeFactorsList = [] := List.eq_nil_of_length_eq_zero hx
      rcases (Nat.primeFactorsList_eq_nil _).1 h0 with h | h
      · exact absurd h (hpos x).ne'
      · exact AddMonoid.addOrderOf_eq_one_iff.1 h
    | succ n ih =>
      have : {x : G | lev x = n + 1} ⊆ ⋃ z ∈ {x : G | lev x = n}, ⋃ q ∈ Q, {x : G | q • x = z} := by
        intro x hx
        refine mem_biUnion (x := par x) (hlevpar x n hx) (mem_biUnion (hminQ x (hne1 x n hx)) ?_)
        rfl
      exact (ih.biUnion fun z _ => hQfin.biUnion fun q hq => hroots q hq z).subset this
  have hnonempty : ∀ n, ∃ x : G, lev x = n := by
    by_contra h
    push Not at h
    obtain ⟨N, hN⟩ := h
    have hemp : ∀ k, ∀ x : G, lev x ≠ N + k := by
      intro k
      induction k with
      | zero => exact hN
      | succ k ih => exact fun x hx => ih (par x) (hlevpar x (N + k) hx)
    have : (univ : Set G) ⊆ ⋃ n ∈ Iio N, {x : G | lev x = n} := by
      intro x _
      refine mem_biUnion (x := lev x) ?_ rfl
      rw [mem_Iio]
      by_contra hlt
      exact hemp (lev x - N) x (by omega)
    exact infinite_univ (((finite_Iio N).biUnion fun n _ => hfinlev n).subset this)
  have hiter : ∀ m n, ∀ x : G, lev x = n + m → lev (par^[m] x) = n := by
    intro m
    induction m with
    | zero => exact fun n x h => by simpa using h
    | succ m ih =>
      intro n x h
      rw [Function.iterate_succ_apply]
      exact ih n (par x) (hlevpar x (n + m) (by omega))
  -- König's lemma
  let Deep : ℕ → G → Prop := fun n x => lev x = n ∧ ∀ m, ∃ w : G, lev w = n + m ∧ par^[m] w = x
  have h0 : Deep 0 0 := by
    refine ⟨by simp [lev], fun m => ?_⟩
    obtain ⟨w, hw⟩ := hnonempty (0 + m)
    have h1 := hiter m 0 w hw
    have h2 : (addOrderOf (par^[m] w)).primeFactorsList = [] := List.eq_nil_of_length_eq_zero h1
    rcases (Nat.primeFactorsList_eq_nil _).1 h2 with h | h
    · exact absurd h (hpos _).ne'
    · exact ⟨w, hw, AddMonoid.addOrderOf_eq_one_iff.1 h⟩
  have hchild : ∀ n x, Deep n x → ∃ z, Deep (n + 1) z ∧ par z = x := by
    intro n x hx
    by_contra hno
    have hbad : ∀ z : G, lev z = n + 1 → par z = x →
        ∃ m, ¬ ∃ w : G, lev w = n + 1 + m ∧ par^[m] w = z := by
      intro z hz hpz
      by_contra h
      push Not at h
      exact hno ⟨z, ⟨hz, h⟩, hpz⟩
    choose! mb hmb using hbad
    have hC : {z : G | lev z = n + 1 ∧ par z = x}.Finite := (hfinlev (n + 1)).subset fun z hz => hz.1
    obtain ⟨M, hM⟩ := (hC.image mb).bddAbove
    obtain ⟨w, hw, hwx⟩ := hx.2 (M + 1)
    set z := par^[M] w with hz
    have hz1 : lev z = n + 1 := hiter M (n + 1) w (by omega)
    have hz2 : par z = x := by
      rw [hz, ← Function.iterate_succ_apply' par]
      exact hwx
    have hle : mb z ≤ M := hM ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine hmb z hz1 hz2 ⟨par^[M - mb z] w, ?_, ?_⟩
    · exact hiter (M - mb z) (n + 1 + mb z) w (by omega)
    · rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hle]
  choose! next hnext hnextp using hchild
  let x : ℕ → G := fun n => Nat.rec (motive := fun _ => G) 0 (fun n z => next n z) n
  have hxD : ∀ n, Deep n (x n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact hnext n (x n) ih
  have hxp : ∀ n, par (x (n + 1)) = x n := fun n => hnextp n (x n) (hxD n)
  have hx1 : ∀ n, addOrderOf (x (n + 1)) ≠ 1 := fun n => hne1 _ n (hxD (n + 1)).1
  let q : ℕ → ℕ := fun n => (addOrderOf (x (n + 1))).minFac
  have hord : ∀ n, addOrderOf (x n) * q n = addOrderOf (x (n + 1)) := by
    intro n
    have := hordpar (x (n + 1)) (hx1 n)
    rwa [hxp n] at this
  have hqanti : Antitone q := antitone_nat_of_succ_le fun n => by
    refine Nat.minFac_le_of_dvd (Nat.minFac_prime (hx1 n)).two_le ?_
    exact (Nat.minFac_dvd _).trans (Dvd.intro _ (hord (n + 1)))
  -- the primes are eventually constant
  obtain ⟨N, hN⟩ : ∃ N, ∀ k, q (N + k) = q N := by
    have hex : ∃ v, ∃ n, q n = v := ⟨q 0, 0, rfl⟩
    obtain ⟨N, hN⟩ := Nat.find_spec hex
    refine ⟨N, fun k => le_antisymm (hqanti (Nat.le_add_right N k)) ?_⟩
    rw [hN]
    exact Nat.find_min' hex ⟨N + k, rfl⟩
  set p := q N with hp
  have hpp : p.Prime := Nat.minFac_prime (hx1 N)
  let z : ℕ → G := fun k => x (N + 1 + k)
  have hzstep : ∀ k, p • z (k + 1) = z k := by
    intro k
    have h1 := hxp (N + 1 + k)
    have h2 : (addOrderOf (x (N + 1 + k + 1))).minFac = p := hN (k + 1) ▸ by
      show q (N + 1 + k) = q (N + (k + 1))
      congr 1
      omega
    show p • x (N + 1 + (k + 1)) = x (N + 1 + k)
    rw [← add_assoc, ← h2]
    exact h1
  have hzord : ∀ k, addOrderOf (z k) = addOrderOf (z 0) * p ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hord (N + 1 + k)
      have h2 : q (N + 1 + k) = p := by
        rw [← hN (k + 1)]
        congr 1
        omega
      rw [h2] at h1
      show addOrderOf (x (N + 1 + (k + 1))) = _
      rw [← add_assoc, ← h1, pow_succ, ← mul_assoc]
      exact congrArg (· * p) ih
  set o := addOrderOf (z 0) with ho
  have ho0 : o ≠ 0 := (hpos _).ne'
  set a := o.factorization p with hadef
  set m := o / p ^ a with hm
  have hom : p ^ a * m = o := Nat.ordProj_mul_ordCompl_eq_self o p
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos p ho0).ne'
  have hpo : p ∣ o := by
    have h1 : o = addOrderOf (x (N + 1)) := rfl
    rw [h1]
    exact Nat.minFac_dvd _
  have ha : 1 ≤ a := (hpp.dvd_iff_one_le_factorization ho0).1 hpo
  refine sparse_of_chain p a hpp ha (fun k => m • z k) (fun k => ?_) (fun k => ?_)
  · rw [addOrderOf_nsmul' _ hm0, hzord k]
    have e : o * p ^ k = (p ^ (a + k)) * m := by
      rw [← hom, pow_add]
      ring
    rw [e, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · show p • (m • z (k + 1)) = m • z k
    rw [smul_comm, hzstep]

/-- Every infinite abelian group has a sparse sequence. -/
theorem exists_sparse (G : Type*) [AddCommGroup G] [Infinite G] : ∃ y : ℕ → G, Sparse y := by
  by_cases htor : ∀ x : G, IsOfFinAddOrder x
  · by_cases hP : {x : G | (addOrderOf x).Prime}.Finite
    · exact chain_of_finite_primes htor hP
    · exact sparse_of_primes htor hP
  · push Not at htor
    obtain ⟨x, hx⟩ := htor
    exact sparse_of_infinite_order x hx

/-- On every infinite abelian group there are a Hausdorff group topology `β` and an ideal `J` with (I1)-(I5) such that
there is no coarsest group topology all of whose convergent filters converge for the PG of `β` and `J`. -/
theorem every_infinite_group (G : Type*) [AddCommGroup G] [Infinite G] :
    ∃ (β : TopologicalSpace G) (J : Set (Set G)), @IsTopologicalAddGroup G β _ ∧ @T2Space G β ∧ AdmIdeal J ∧
      ¬ ∃ σ : TopologicalSpace G, @IsTopologicalAddGroup G σ _ ∧ (∀ x : G, @xi G β J (@nhds G σ x) x) ∧
        ∀ τ : TopologicalSpace G, @IsTopologicalAddGroup G τ _ → (∀ x : G, @xi G β J (@nhds G τ x) x) → τ ≤ σ := by
  obtain ⟨y, hy⟩ := exists_sparse G
  exact ⟨top y univ, I y, top_group univ, top_t2 hy, admissible hy, no_coarsest hy⟩

/-- A finite abelian group carries no ideal with (I1)-(I5). -/
theorem no_ideal_of_finite {G : Type*} [AddCommGroup G] [Finite G] (J : Set (Set G)) : ¬ AdmIdeal J := by
  intro h
  have key : ∀ s : Set G, s.Finite → s ∈ J := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => exact h.empty_mem
    | @insert a s _ _ ih =>
      rw [insert_eq]
      exact h.union _ (h.single a) _ ih
  exact h.proper (key univ finite_univ)

end PG.NoCoreAll
