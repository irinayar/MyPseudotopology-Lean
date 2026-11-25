import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGTwoGeneration
import LeanCheck.PGTwoReflection

/-!
# PGthree: pairwise non-isomorphic selective ultrafilters generate a Hausdorff PG (Lean check)

Scope. Section 3 of the third article (`PGthree.tex`), the parts that need no set-theoretic hypothesis.

* `IsSel u` : the ultrafilter `u` is nonprincipal and every function to `ℕ` is constant or injective on a member of `u`;
  `Iso u v` : `v` is the image of `u` under a permutation;
* `IsSel.pseudoInter`, `IsSel.injOn_of_finite_fibres` : Lemma 3.1; `iso_of_injOn` : an image under a map injective on a
  member is isomorphic;
* `separation` : Lemma 3.2; `tuples` : Lemma 3.3;
* `genFam_hausdorff` : Theorem 3.4: on an infinite countable abelian group with only finitely many solutions of
  `m • x = 0` for every `m ≥ 1`, pairwise non-isomorphic selective ultrafilters generate a PG in which the only null
  principal ultrafilter is `pure 0`;
* `mem_vic_iff_of_dense` : Proposition 3.5.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

namespace Sel

/-- Selective (Ramsey) ultrafilter. -/
def IsSel {α : Type*} (u : Ultrafilter α) : Prop :=
  (∀ a, u ≠ pure a) ∧ ∀ f : α → ℕ, (∃ c, {x | f x = c} ∈ u) ∨ ∃ C ∈ u, InjOn f C

/-- `v` is the image of `u` under a permutation. -/
def Iso {α : Type*} (u v : Ultrafilter α) : Prop := ∃ π : Equiv.Perm α, u.map π = v

theorem Iso.symm {α : Type*} {u v : Ultrafilter α} (h : Iso u v) : Iso v u := by
  obtain ⟨π, rfl⟩ := h
  refine ⟨π.symm, ?_⟩
  rw [Ultrafilter.map_map]
  have : (π.symm : α → α) ∘ (π : α → α) = id := by funext x; simp
  rw [this, Ultrafilter.map_id]

theorem Iso.trans {α : Type*} {u v w : Ultrafilter α} (h : Iso u v) (h' : Iso v w) : Iso u w := by
  obtain ⟨π, rfl⟩ := h
  obtain ⟨ρ, rfl⟩ := h'
  refine ⟨π.trans ρ, ?_⟩
  rw [Ultrafilter.map_map]
  rfl

/-- A nonprincipal ultrafilter contains no finite set. -/
theorem notMem_of_finite {α : Type*} {u : Ultrafilter α} (h : ∀ a, u ≠ pure a) {s : Set α} (hs : s.Finite) :
    s ∉ u := by
  intro hmem
  obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem hs hmem
  exact h a ha

theorem infinite_of_mem {α : Type*} {u : Ultrafilter α} (h : ∀ a, u ≠ pure a) {s : Set α} (hs : s ∈ u) :
    s.Infinite := fun hf => notMem_of_finite h hf hs

/-- Lemma 3.1(b). -/
theorem IsSel.injOn_of_finite_fibres {u : Ultrafilter ℕ} (hu : IsSel u) (h : ℕ → ℕ)
    (hfib : ∀ c, {x | h x = c}.Finite) : ∃ C ∈ u, InjOn h C := by
  rcases hu.2 h with ⟨c, hc⟩ | hC
  · exact absurd hc (notMem_of_finite hu.1 (hfib c))
  · exact hC

/-- Lemma 3.1(a). -/
theorem IsSel.pseudoInter {u : Ultrafilter ℕ} (hu : IsSel u) (B : ℕ → Set ℕ) (hB : ∀ m, B m ∈ u) :
    ∃ C ∈ u, ∀ m, (C \ B m).Finite := by
  classical
  set B' : ℕ → Set ℕ := fun m => ⋂ i ∈ Iic m, B i with hB'
  have hB'mem : ∀ m, B' m ∈ u := fun m => (Filter.biInter_mem (finite_Iic m)).2 (fun i _ => hB i)
  have hB'sub : ∀ m n, m ≤ n → B' n ⊆ B m := fun m n hmn x hx => mem_iInter₂.1 hx m hmn
  set f : ℕ → ℕ := fun x => ((Finset.range (x + 1)).filter (fun m => x ∈ B' m)).sup (fun m => m + 1) with hf
  have hfge : ∀ x m, m ≤ x → x ∈ B' m → m + 1 ≤ f x := by
    intro x m hm hx
    exact Finset.le_sup (f := fun m => m + 1)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hm), hx⟩)
  rcases hu.2 f with ⟨c, hc⟩ | ⟨C, hC, hinj⟩
  · exfalso
    have hcof : {x : ℕ | c ≤ x} ∈ u := by
      rcases u.mem_or_compl_mem {x : ℕ | c ≤ x} with h | h
      · exact h
      · refine absurd h (notMem_of_finite hu.1 ((finite_Iio c).subset (fun x hx => ?_)))
        simpa using hx
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ :=
      Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (u : Filter ℕ)) (Filter.inter_mem hc (hB'mem c)) hcof)
    have h1 := hfge x c hx3 hx2
    have h2 : f x = c := hx1
    omega
  · refine ⟨C, hC, fun m => ?_⟩
    have h1 : {x | x ∈ C ∧ f x ≤ m}.Finite := by
      refine Set.Finite.of_finite_image (f := f) ((finite_Iic m).subset ?_) (hinj.mono (fun x hx => hx.1))
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    refine (h1.union (finite_Iio m)).subset ?_
    rintro x ⟨hxC, hxB⟩
    by_cases hxm : x < m
    · exact Or.inr hxm
    left
    refine ⟨hxC, ?_⟩
    by_contra hlt
    have hne : ((Finset.range (x + 1)).filter (fun m => x ∈ B' m)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      apply hlt
      show ((Finset.range (x + 1)).filter (fun m => x ∈ B' m)).sup (fun m => m + 1) ≤ m
      rw [he]; simp
    obtain ⟨n, hn, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun m => m + 1)
    have hfx : f x = n + 1 := hsup
    have hmn : m ≤ n := by omega
    exact hxB (hB'sub m n hmn (Finset.mem_filter.1 hn).2)

/-- An infinite set of natural numbers contains two disjoint infinite sets that cover it. -/
theorem exists_halves {C : Set ℕ} (hC : C.Infinite) :
    ∃ C1 C2 : Set ℕ, C1.Infinite ∧ C2.Infinite ∧ Disjoint C1 C2 ∧ C1 ∪ C2 = C := by
  classical
  have hmono : StrictMono (Nat.nth (· ∈ C)) := Nat.nth_strictMono hC
  set C1 : Set ℕ := range (fun n => Nat.nth (· ∈ C) (2 * n)) with h1
  have hsub : C1 ⊆ C := by
    rintro _ ⟨n, rfl⟩
    exact Nat.nth_mem_of_infinite hC _
  refine ⟨C1, C \ C1, ?_, ?_, disjoint_sdiff_self_right, union_sdiff_cancel hsub⟩
  · exact infinite_range_of_injective (fun a b h => by
      have := hmono.injective h; omega)
  · have : (range (fun n => Nat.nth (· ∈ C) (2 * n + 1))).Infinite :=
      infinite_range_of_injective (fun a b h => by
        have := hmono.injective h; omega)
    refine this.mono ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Nat.nth_mem_of_infinite hC _, ?_⟩
    rintro ⟨m, hm⟩
    have := hmono.injective hm
    omega

/-- The image under a map injective on a member is isomorphic. -/
theorem iso_of_injOn {u : Ultrafilter ℕ} (hu : ∀ a, u ≠ pure a) (f : ℕ → ℕ) {C : Set ℕ} (hC : C ∈ u)
    (hinj : InjOn f C) : Iso u (u.map f) := by
  classical
  obtain ⟨C1, C2, h1, h2, hdis, hun⟩ := exists_halves (infinite_of_mem hu hC)
  -- a member `K` of `u` inside `C` whose complement in `C` is infinite
  obtain ⟨K, L, hK, hKC, hLC, hL, hKL⟩ : ∃ K L : Set ℕ, K ∈ u ∧ K ⊆ C ∧ L ⊆ C ∧ L.Infinite ∧ Disjoint K L := by
    have hCu : C1 ∪ C2 ∈ u := by rw [hun]; exact hC
    have s1 : C1 ⊆ C := hun ▸ subset_union_left
    have s2 : C2 ⊆ C := hun ▸ subset_union_right
    rcases Ultrafilter.union_mem_iff.1 hCu with h | h
    · exact ⟨C1, C2, h, s1, s2, h2, hdis⟩
    · exact ⟨C2, C1, h, s2, s1, h1, hdis.symm⟩
  have hKinf : K.Infinite := infinite_of_mem hu hK
  have hKcinf : (Kᶜ : Set ℕ).Infinite := hL.mono (fun x hx hxK => disjoint_left.1 hKL hxK hx)
  have hinjK : InjOn f K := hinj.mono hKC
  have hfKinf : (f '' K).Infinite := hKinf.image hinjK
  have hfKcinf : ((f '' K)ᶜ : Set ℕ).Infinite := by
    refine (hL.image (hinj.mono hLC)).mono ?_
    rintro _ ⟨x, hxL, rfl⟩ ⟨y, hyK, hxy⟩
    have : y = x := hinj (hKC hyK) (hLC hxL) hxy
    exact disjoint_left.1 hKL hyK (this ▸ hxL)
  have := hKcinf.to_subtype
  have := hfKcinf.to_subtype
  have e2 : (Kᶜ : Set ℕ) ≃ ((f '' K)ᶜ : Set ℕ) := by
    haveI : Denumerable (Kᶜ : Set ℕ) := Nat.Subtype.denumerable _
    haveI : Denumerable ((f '' K)ᶜ : Set ℕ) := Nat.Subtype.denumerable _
    exact (Denumerable.eqv _).trans (Denumerable.eqv _).symm
  let e1 : K ≃ (f '' K) := Equiv.Set.imageOfInjOn f K hinjK
  let π : Equiv.Perm ℕ :=
    (Equiv.Set.sumCompl K).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.Set.sumCompl (f '' K)))
  have hπ : ∀ x ∈ K, π x = f x := by
    intro x hx
    simp only [π, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hx, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.Set.sumCompl_apply_inl]
    rfl
  refine ⟨π, ?_⟩
  apply Ultrafilter.coe_injective
  show Filter.map π (u : Filter ℕ) = Filter.map f (u : Filter ℕ)
  exact Filter.map_congr (Filter.mem_of_superset hK (fun x hx => hπ x hx))

/-- Lemma 3.2: separation. -/
theorem separation {k : ℕ} (w : Fin k → Ultrafilter ℕ) (hw : ∀ j, IsSel (w j))
    (hiso : ∀ i j, i ≠ j → ¬ Iso (w i) (w j)) (f : ℕ → ℕ) (hf : Monotone f) (hfx : ∀ x, x ≤ f x) :
    ∃ B : Fin k → Set ℕ, (∀ j, B j ∈ w j) ∧ ∀ i j, ∀ x ∈ B i, ∀ y ∈ B j, x < y → f x < y := by
  classical
  let t : ℕ → ℕ := fun n => Nat.rec 0 (fun _ s => f s + 1) n
  have ht0 : t 0 = 0 := rfl
  have htsucc : ∀ m, t (m + 1) = f (t m) + 1 := fun m => rfl
  have htmono : StrictMono t := strictMono_nat_of_lt_succ (fun m => by
    rw [htsucc]; exact Nat.lt_succ_of_le (hfx _))
  have hex : ∀ x : ℕ, ∃ m : ℕ, x ≤ t m := fun x => ⟨x, htmono.id_le x⟩
  let h : ℕ → ℕ := fun x => sInf {m : ℕ | x ≤ t m}
  have hle : ∀ x, x ≤ t (h x) := fun x => Nat.sInf_mem (s := {m : ℕ | x ≤ t m}) (hex x)
  have hlt : ∀ x m, m < h x → t m < x := fun x m hm => by
    have h1 : m ∉ {m : ℕ | x ≤ t m} := Nat.notMem_of_lt_sInf hm
    exact Nat.lt_of_not_le h1
  have hhmono : Monotone h := fun a b hab => Nat.sInf_le (hab.trans (hle b))
  have hfib : ∀ c, {x | h x = c}.Finite := fun c => (finite_Iic (t c)).subset (fun x hx => by
    have h1 := hle x
    have h2 : h x = c := hx
    rw [h2] at h1
    exact h1)
  have hC : ∀ j, ∃ C ∈ w j, InjOn h C := fun j => (hw j).injOn_of_finite_fibres h hfib
  choose C hCmem hCinj using hC
  set p : Fin k → Ultrafilter ℕ := fun j => (w j).map h with hp
  have hwp : ∀ j, Iso (w j) (p j) := fun j => iso_of_injOn (hw j).1 h (hCmem j) (hCinj j)
  have hpfree : ∀ j a, p j ≠ pure a := by
    intro j a hja
    have h1 : ({a} : Set ℕ) ∈ p j := by rw [hja]; exact Set.mem_singleton a
    have h2 : {x | h x = a} ∈ w j := h1
    exact notMem_of_finite (hw j).1 (hfib a) h2
  have hne1 : ∀ i j, i ≠ j → p i ≠ p j := by
    intro i j hij he
    exact hiso i j hij ((hwp i).trans (he ▸ (hwp j).symm))
  have hne2 : ∀ i j, i ≠ j → (p i).map Nat.succ ≠ p j := by
    intro i j hij he
    have h1 : Iso (p i) ((p i).map Nat.succ) :=
      iso_of_injOn (hpfree i) Nat.succ (C := univ) Filter.univ_mem Nat.succ_injective.injOn
    exact hiso i j hij ((hwp i).trans (h1.trans (he ▸ (hwp j).symm)))
  -- separating sets for the images
  have hsep : ∀ i j, ∃ A B : Set ℕ, A ∈ p i ∧ B ∈ p j ∧ (i ≠ j → ∀ a ∈ A, ∀ b ∈ B, b ≠ a ∧ b ≠ a + 1) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, univ, Filter.univ_mem, Filter.univ_mem, fun h' => absurd hij h'⟩
    obtain ⟨S, hSj, hSi⟩ : ∃ S : Set ℕ, S ∈ p j ∧ Sᶜ ∈ p i := by
      by_contra hcon
      push Not at hcon
      apply hne1 j i (Ne.symm hij)
      refine Ultrafilter.coe_le_coe.1 (fun s hs => ?_)
      by_contra hsj
      have hc : sᶜ ∈ p j := Ultrafilter.compl_mem_iff_notMem.2 hsj
      have := hcon _ hc
      rw [compl_compl] at this
      exact this hs
    obtain ⟨T, hTj, hTi⟩ : ∃ T : Set ℕ, T ∈ p j ∧ Nat.succ ⁻¹' Tᶜ ∈ p i := by
      by_contra hcon
      push Not at hcon
      apply hne2 i j hij
      refine Ultrafilter.coe_le_coe.1 (fun s hs => ?_)
      show Nat.succ ⁻¹' s ∈ p i
      have : sᶜ ∉ p j := Ultrafilter.compl_notMem_iff.2 hs
      by_contra hsi
      have hc : Nat.succ ⁻¹' sᶜ ∈ p i := by
        rw [preimage_compl]
        exact Ultrafilter.compl_mem_iff_notMem.2 hsi
      have h2 : sᶜ ∈ p j := by
        by_contra h3
        have h4 : s ∈ p j := Ultrafilter.compl_notMem_iff.1 h3
        exact hcon s h4 hc
      exact this h2
    refine ⟨Sᶜ ∩ Nat.succ ⁻¹' Tᶜ, S ∩ T, Filter.inter_mem (f := (p i : Filter ℕ)) hSi hTi,
      Filter.inter_mem (f := (p j : Filter ℕ)) hSj hTj, fun _ a ha b hb => ⟨?_, ?_⟩⟩
    · intro e
      exact ha.1 (e ▸ hb.1)
    · intro e
      exact ha.2 (show Nat.succ a ∈ T by rw [Nat.succ_eq_add_one, ← e]; exact hb.2)
  choose A B hA hB hAB using hsep
  have hpar : ∀ j, ∃ P : Set ℕ, P ∈ p j ∧ ∀ a ∈ P, ∀ b ∈ P, a % 2 = b % 2 := by
    intro j
    rcases (p j).mem_or_compl_mem {n | n % 2 = 0} with h' | h'
    · exact ⟨_, h', fun a ha b hb => ha.trans hb.symm⟩
    · refine ⟨_, h', fun a ha b hb => ?_⟩
      have ha' : ¬ a % 2 = 0 := ha
      have hb' : ¬ b % 2 = 0 := hb
      omega
  choose P hP hPpar using hpar
  set M : Fin k → Set ℕ := fun i => P i ∩ ⋂ j, (A i j ∩ B j i) with hM
  have hMmem : ∀ i, M i ∈ p i := fun i =>
    Filter.inter_mem (f := (p i : Filter ℕ)) (hP i)
      (Filter.iInter_mem.2 (fun j => Filter.inter_mem (f := (p i : Filter ℕ)) (hA i j) (hB j i)))
  refine ⟨fun j => C j ∩ h ⁻¹' M j, fun j => Filter.inter_mem (f := (w j : Filter ℕ)) (hCmem j) (hMmem j), ?_⟩
  intro i j x hx y hy hxy
  have h1 : h x ≤ h y := hhmono hxy.le
  have hxM := hx.2
  have hyM := hy.2
  have h2 : h x + 2 ≤ h y := by
    by_cases hij : i = j
    · subst hij
      have hne : h x ≠ h y := fun e => hxy.ne (hCinj i hx.1 hy.1 e)
      have := hPpar i (h x) hxM.1 (h y) hyM.1
      omega
    · have hxA : h x ∈ A i j := (mem_iInter.1 hxM.2 j).1
      have hyB : h y ∈ B i j := (mem_iInter.1 hyM.2 i).2
      have := hAB i j hij (h x) hxA (h y) hyB
      omega
  have h3 : t (h x + 1) < y := hlt y (h x + 1) (by omega)
  rw [htsucc] at h3
  have h4 : f x ≤ f (t (h x)) := hf (hle x)
  omega

/-- `R` belongs to the iterated product of the ultrafilters `v 0, v 1, …`. -/
def Large : (r : ℕ) → (Fin r → Ultrafilter ℕ) → Set (Fin r → ℕ) → Prop
  | 0, _, R => Fin.elim0 ∈ R
  | r + 1, v, R => {x | Large r (fun i => v i.succ) {t | Fin.cons x t ∈ R}} ∈ v 0

/-- Lemma 3.3. -/
theorem tuples {k : ℕ} (w : Fin k → Ultrafilter ℕ) (hw : ∀ j, IsSel (w j))
    (hiso : ∀ i j, i ≠ j → ¬ Iso (w i) (w j)) :
    ∀ (r : ℕ) (σ : Fin r → Fin k) (R : Set (Fin r → ℕ)), ¬ Large r (fun i => w (σ i)) R →
      ∃ B : Fin k → Set ℕ, (∀ j, B j ∈ w j) ∧
        ∀ y : Fin r → ℕ, StrictMono y → (∀ i, y i ∈ B (σ i)) → y ∉ R := by
  classical
  intro r
  induction r with
  | zero =>
    intro σ R hR
    refine ⟨fun _ => univ, fun _ => Filter.univ_mem, fun y _ _ hy => hR ?_⟩
    show Fin.elim0 ∈ R
    have : y = Fin.elim0 := funext (fun i => i.elim0)
    rwa [this] at hy
  | succ r ih =>
    intro σ R hR
    set X : Set ℕ := {x | ¬ Large r (fun i => w (σ i.succ)) {t | Fin.cons x t ∈ R}} with hX
    have hXmem : X ∈ w (σ 0) := Ultrafilter.compl_mem_iff_notMem.2 hR
    have hBx : ∀ x, ∃ Bx : Fin k → Set ℕ, (∀ j, Bx j ∈ w j) ∧ (x ∈ X →
        ∀ y : Fin r → ℕ, StrictMono y → (∀ i, y i ∈ Bx (σ i.succ)) → y ∉ {t | Fin.cons x t ∈ R}) := by
      intro x
      by_cases hx : x ∈ X
      · obtain ⟨Bx, h1, h2⟩ := ih (fun i => σ i.succ) _ hx
        exact ⟨Bx, h1, fun _ => h2⟩
      · exact ⟨fun _ => univ, fun _ => Filter.univ_mem, fun h => absurd h hx⟩
    choose Bx hBxmem hBxprop using hBx
    have hC : ∀ j, ∃ C ∈ w j, ∀ x, (C \ Bx x j).Finite := fun j =>
      (hw j).pseudoInter (fun x => Bx x j) (fun x => hBxmem x j)
    choose C hCmem hCfin using hC
    let g : ℕ → ℕ := fun x => ∑ j, (hCfin j x).toFinset.sup id
    let f : ℕ → ℕ := fun x => x + ∑ x' ∈ Finset.range (x + 1), g x'
    have hfmono : Monotone f := fun a b hab =>
      Nat.add_le_add hab (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    have hfx : ∀ x, x ≤ f x := fun x => Nat.le_add_right _ _
    have hbound : ∀ j x x', x' ≤ x → ∀ y ∈ C j \ Bx x' j, y ≤ f x := by
      intro j x x' hx' y hy
      have h1 : y ≤ (hCfin j x').toFinset.sup id :=
        Finset.le_sup (f := id) ((hCfin j x').mem_toFinset.2 hy)
      have h2 : (hCfin j x').toFinset.sup id ≤ g x' :=
        Finset.single_le_sum (f := fun j => (hCfin j x').toFinset.sup id) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      have h3 : g x' ≤ ∑ x'' ∈ Finset.range (x + 1), g x'' :=
        Finset.single_le_sum (f := g) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
      exact (h1.trans (h2.trans h3)).trans (Nat.le_add_left _ _)
    obtain ⟨E, hEmem, hE⟩ := separation w hw hiso f hfmono hfx
    refine ⟨fun j => C j ∩ E j ∩ (if j = σ 0 then X else univ), fun j => ?_, ?_⟩
    · refine Filter.inter_mem (f := (w j : Filter ℕ)) (Filter.inter_mem (f := (w j : Filter ℕ)) (hCmem j) (hEmem j)) ?_
      split_ifs with h
      · rw [h]; exact hXmem
      · exact Filter.univ_mem
    · intro y hy hyB hyR
      have h0X : y 0 ∈ X := by
        have := (hyB 0).2
        simpa using this
      have htail : StrictMono (Fin.tail y) := fun a b hab => hy (Fin.succ_lt_succ_iff.2 hab)
      refine hBxprop (y 0) h0X (Fin.tail y) htail (fun i => ?_) ?_
      · have hlt : y 0 < y i.succ := hy (Fin.succ_pos i)
        have hfy : f (y 0) < y i.succ :=
          hE (σ 0) (σ i.succ) (y 0) (hyB 0).1.2 (y i.succ) (hyB i.succ).1.2 hlt
        by_contra hnot
        have := hbound (σ i.succ) (y 0) (y 0) le_rfl (y i.succ) ⟨(hyB i.succ).1.1, hnot⟩
        omega
      · show Fin.cons (y 0) (Fin.tail y) ∈ R
        rw [Fin.cons_self_tail]
        exact hyR

/-- Finitely many possible last coordinates for every choice of the earlier ones. -/
def FinLast {r : ℕ} (R : Set (Fin (r + 1) → ℕ)) : Prop := ∀ p : Fin r → ℕ, {z | Fin.snoc p z ∈ R}.Finite

theorem not_large_of_finLast : ∀ (r : ℕ) (v : Fin (r + 1) → Ultrafilter ℕ), (∀ i a, v i ≠ pure a) →
    ∀ R : Set (Fin (r + 1) → ℕ), FinLast R → ¬ Large (r + 1) v R := by
  intro r
  induction r with
  | zero =>
    intro v hv R hR h
    have h' : {x | Large 0 (fun i => v i.succ) {t | Fin.cons x t ∈ R}} ∈ v 0 := h
    refine notMem_of_finite (hv 0) ?_ h'
    refine (hR Fin.elim0).subset (fun x hx => ?_)
    have hx' : Fin.cons x Fin.elim0 ∈ R := hx
    show Fin.snoc Fin.elim0 x ∈ R
    have e : (Fin.snoc Fin.elim0 x : Fin 1 → ℕ) = Fin.cons x Fin.elim0 := by
      funext i
      have : i = 0 := Fin.fin_one_eq_zero i
      subst this
      simp [Fin.snoc]
    rwa [e]
  | succ r ih =>
    intro v hv R hR h
    have h' : {x | Large (r + 1) (fun i => v i.succ) {t | Fin.cons x t ∈ R}} ∈ v 0 := h
    have hempty : {x | Large (r + 1) (fun i => v i.succ) {t | Fin.cons x t ∈ R}} = ∅ := by
      refine eq_empty_of_forall_notMem (fun x hx => ?_)
      refine ih (fun i => v i.succ) (fun i a => hv _ a) _ (fun p => ?_) hx
      refine (hR (Fin.cons x p)).subset (fun z hz => ?_)
      have hz' : Fin.cons x (Fin.snoc p z) ∈ R := hz
      show Fin.snoc (Fin.cons x p) z ∈ R
      rwa [← Fin.cons_snoc_eq_snoc_cons]
    rw [hempty] at h'
    exact Ultrafilter.empty_notMem h'

section Group

variable {G : Type*} [AddCommGroup G]

/-- A representation of a member of the signed-sum closure. -/
def Rep (S : Set (Ultrafilter G)) (F : Filter G) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u : ι → Ultrafilter G) (c : ι → ℤ), (∀ i, u i ∈ S) ∧ (∀ i, c i = 1 ∨ c i = -1) ∧
    ∀ A : ι → Set G, (∀ i, A i ∈ u i) → {z | ∃ a : ι → G, (∀ i, a i ∈ A i) ∧ ∑ i, c i • a i = z} ∈ F

/-- The null filters generating the PG of a family of ultrafilters. -/
def ultraGen (S : Set (Ultrafilter G)) : Set (Filter G) := {F | ∃ u ∈ S, F = (u : Filter G)}

theorem rep_of_sumClosure (S : Set (Ultrafilter G)) {F : Filter G} (h : SumClosure (ultraGen S) F) : Rep S F := by
  induction h with
  | zero =>
    refine ⟨Fin 0, inferInstance, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun A _ => ?_⟩
    exact Filter.mem_pure.2 ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩
  | gen hF =>
    obtain ⟨u, hu, rfl⟩ := hF
    refine ⟨Unit, inferInstance, fun _ => u, fun _ => 1, fun _ => hu, fun _ => Or.inl rfl, fun A hA => ?_⟩
    refine Filter.mem_of_superset (hA ()) (fun z hz => ?_)
    exact ⟨fun _ => z, fun _ => hz, by simp⟩
  | neg hF =>
    obtain ⟨u, hu, rfl⟩ := hF
    refine ⟨Unit, inferInstance, fun _ => u, fun _ => -1, fun _ => hu, fun _ => Or.inr rfl, fun A hA => ?_⟩
    refine Filter.mem_map.2 (Filter.mem_of_superset (hA ()) (fun z hz => ?_))
    exact ⟨fun _ => z, fun _ => hz, by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨ι1, _, u1, c1, hu1, hc1, h1⟩ := ih1
    obtain ⟨ι2, _, u2, c2, hu2, hc2, h2⟩ := ih2
    refine ⟨ι1 ⊕ ι2, inferInstance, Sum.elim u1 u2, Sum.elim c1 c2, ?_, ?_, fun A hA => ?_⟩
    · rintro (i | i)
      · exact hu1 i
      · exact hu2 i
    · rintro (i | i)
      · exact hc1 i
      · exact hc2 i
    · refine Filter.mem_map₂_iff.2 ⟨_, h1 (fun i => A (Sum.inl i)) (fun i => hA (Sum.inl i)), _,
        h2 (fun i => A (Sum.inr i)) (fun i => hA (Sum.inr i)), ?_⟩
      rintro _ ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨Sum.elim a b, ?_, ?_⟩
      · rintro (i | i)
        · exact ha i
        · exact hb i
      · simp [Fintype.sum_sum_type]

/-- The key step: no finite signed sum of small members of the ultrafilters contains a given `g ≠ 0`. -/
theorem exists_avoiding [Countable G] [Infinite G] (htor : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite)
    {ι : Type} [Fintype ι] (u : ι → Ultrafilter G) (hsel : ∀ i, IsSel (u i))
    (hiso : ∀ i j, u i ≠ u j → ¬ Iso (u i) (u j)) (c : ι → ℤ) (hc : ∀ i, c i = 1 ∨ c i = -1) {g : G} (hg : g ≠ 0) :
    ∃ A : ι → Set G, (∀ i, A i ∈ u i) ∧ ∀ a : ι → G, (∀ i, a i ∈ A i) → ∑ i, c i • a i ≠ g := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    haveI := Encodable.ofCountable G
    haveI := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  -- the different ultrafilters, transported to `ℕ`
  set U : Finset (Ultrafilter G) := Finset.univ.image u with hU
  set k := U.card with hk
  let enum : Fin k ≃ U := U.equivFin.symm
  let w : Fin k → Ultrafilter ℕ := fun j => (enum j : Ultrafilter G).map e.symm
  have hmemU : ∀ j, ∃ i, u i = (enum j : Ultrafilter G) := fun j => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (enum j).2
    exact ⟨i, hi⟩
  have hback : ∀ j, (w j).map e = (enum j : Ultrafilter G) := by
    intro j
    show ((enum j : Ultrafilter G).map e.symm).map e = _
    rw [Ultrafilter.map_map]
    have : (e : ℕ → G) ∘ (e.symm : G → ℕ) = id := by funext x; simp
    rw [this, Ultrafilter.map_id]
  have hmemw : ∀ j (s : Set ℕ), s ∈ w j ↔ e.symm ⁻¹' s ∈ (enum j : Ultrafilter G) := fun j s => Iff.rfl
  have hwsel : ∀ j, IsSel (w j) := by
    intro j
    obtain ⟨i, hi⟩ := hmemU j
    have hs := hsel i
    rw [hi] at hs
    constructor
    · intro a ha
      apply hs.1 (e a)
      rw [← hback j, ha, Ultrafilter.map_pure]
    · intro f
      rcases hs.2 (fun x => f (e.symm x)) with ⟨m, hm⟩ | ⟨C, hC, hinj⟩
      · exact Or.inl ⟨m, hm⟩
      · refine Or.inr ⟨e ⁻¹' C, ?_, fun a ha b hb hab => ?_⟩
        · rw [hmemw]
          refine Filter.mem_of_superset hC (fun x hx => ?_)
          show e (e.symm x) ∈ C
          simpa using hx
        · have := hinj ha hb (by simpa using hab)
          exact e.injective this
  have hwiso : ∀ i j, i ≠ j → ¬ Iso (w i) (w j) := by
    intro i j hij ⟨π, hπ⟩
    obtain ⟨i', hi'⟩ := hmemU i
    obtain ⟨j', hj'⟩ := hmemU j
    have hne : u i' ≠ u j' := by
      rw [hi', hj']
      intro h
      exact hij (enum.injective (Subtype.ext h))
    refine hiso i' j' hne ⟨(e.symm.trans π).trans e, ?_⟩
    have h1 : ((e.symm.trans π).trans e : G → G) ∘ (e : ℕ → G) = (e : ℕ → G) ∘ (π : ℕ → ℕ) := by
      funext x; simp
    have h2 : (Ultrafilter.map e (w i)).map ((e.symm.trans π).trans e) = Ultrafilter.map e (w j) := by
      rw [← hπ, Ultrafilter.map_map, Ultrafilter.map_map]
      exact congrArg (fun f => Ultrafilter.map f (w i)) h1
    rw [hback i, hback j] at h2
    rw [hi', hj']
    exact h2
  -- all the equations
  set n := Fintype.card ι with hn
  let Idx := Σ r : Fin (n + 1), (Fin r.val → Fin k) × (Fin r.val → Finset.Icc (-(n : ℤ)) n)
  let Rel : (idx : Idx) → Set (Fin idx.1.val → ℕ) := fun idx =>
    {y | ∑ l, (idx.2.2 l : ℤ) • e (y l) = g}
  have hone : ∀ idx : Idx, ∃ B : Fin k → Set ℕ, (∀ j, B j ∈ w j) ∧ ((∀ l, (idx.2.2 l : ℤ) ≠ 0) →
      ∀ y : Fin idx.1.val → ℕ, StrictMono y → (∀ l, y l ∈ B (idx.2.1 l)) → y ∉ Rel idx) := by
    intro idx
    by_cases hnz : ∀ l, (idx.2.2 l : ℤ) ≠ 0
    swap
    · exact ⟨fun _ => univ, fun _ => Filter.univ_mem, fun h => absurd h hnz⟩
    have key : ∀ (r : ℕ) (σ : Fin r → Fin k) (d : Fin r → ℤ), (∀ l, d l ≠ 0) →
        ¬ Large r (fun l => w (σ l)) {y | ∑ l, d l • e (y l) = g} := by
      intro r σ d hd
      cases r with
      | zero =>
        intro h
        have h' : ∑ l : Fin 0, d l • e (Fin.elim0 l) = g := h
        simp at h'
        exact hg h'.symm
      | succ r =>
        refine not_large_of_finLast r _ (fun l a => (hwsel (σ l)).1 a) _ (fun p => ?_)
        set s : G := ∑ l : Fin r, d l.castSucc • e (p l) with hs
        have hm : 0 < (d (Fin.last r)).natAbs := Int.natAbs_pos.2 (hd _)
        have hfin : {x : G | d (Fin.last r) • x = g - s}.Finite := by
          by_cases hne : ∃ x₀ : G, d (Fin.last r) • x₀ = g - s
          swap
          · refine Set.Finite.subset finite_empty (fun x hx => hne ⟨x, hx⟩)
          obtain ⟨x₀, hx₀⟩ := hne
          refine ((htor _ hm).image (fun z => z + x₀)).subset (fun x hx => ?_)
          refine ⟨x - x₀, ?_, by simp⟩
          have h0 : d (Fin.last r) • (x - x₀) = 0 := by
            rw [smul_sub, show d (Fin.last r) • x = g - s from hx, hx₀, sub_self]
          show (d (Fin.last r)).natAbs • (x - x₀) = 0
          rcases Int.natAbs_eq (d (Fin.last r)) with h1 | h1
          · rw [h1, natCast_zsmul] at h0
            exact h0
          · rw [h1, neg_smul, neg_eq_zero, natCast_zsmul] at h0
            exact h0
        refine (hfin.preimage e.injective.injOn).subset (fun z hz => ?_)
        have hz' : ∑ l : Fin (r + 1), d l • e ((Fin.snoc p z : Fin (r + 1) → ℕ) l) = g := hz
        rw [Fin.sum_univ_castSucc] at hz'
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at hz'
        show d (Fin.last r) • e z = g - s
        rw [← hz', hs]
        abel
    obtain ⟨B, hB, hBprop⟩ := tuples w hwsel hwiso idx.1.val idx.2.1 (Rel idx) (key _ _ _ hnz)
    exact ⟨B, hB, fun _ => hBprop⟩
  choose Bidx hBidxmem hBidx using hone
  -- pairwise disjoint members
  have hdisj : ∀ i j : Fin k, ∃ D1 D2 : Set ℕ, D1 ∈ w i ∧ D2 ∈ w j ∧ (i ≠ j → Disjoint D1 D2) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, univ, Filter.univ_mem, Filter.univ_mem, fun h => absurd hij h⟩
    have hne : w j ≠ w i := by
      intro h
      apply hij
      have : (enum i : Ultrafilter G) = (enum j : Ultrafilter G) := by rw [← hback i, ← hback j, h]
      exact enum.injective (Subtype.ext this)
    obtain ⟨D, hDi, hDj⟩ : ∃ D : Set ℕ, D ∈ w i ∧ Dᶜ ∈ w j := by
      by_contra hcon
      push Not at hcon
      apply hne
      refine Ultrafilter.coe_le_coe.1 (fun s hs => ?_)
      by_contra hsj
      have hc' : sᶜ ∈ w j := Ultrafilter.compl_mem_iff_notMem.2 hsj
      exact hcon s hs hc'
    exact ⟨D, Dᶜ, hDi, hDj, fun _ => disjoint_compl_right⟩
  choose D1 D2 hD1 hD2 hD using hdisj
  set B : Fin k → Set ℕ := fun j => (⋂ idx : Idx, Bidx idx j) ∩ ⋂ i, (D1 j i ∩ D2 i j) with hBdef
  have hBmem : ∀ j, B j ∈ w j := fun j =>
    Filter.inter_mem (f := (w j : Filter ℕ)) (Filter.iInter_mem.2 (fun idx => hBidxmem idx j))
      (Filter.iInter_mem.2 (fun i => Filter.inter_mem (f := (w j : Filter ℕ)) (hD1 j i) (hD2 i j)))
  have hBdisj : ∀ i j (y : ℕ), y ∈ B i → y ∈ B j → i = j := by
    intro i j y hyi hyj
    by_contra hij
    have h1 : y ∈ D1 i j := (mem_iInter.1 hyi.2 j).1
    have h2 : y ∈ D2 i j := (mem_iInter.1 hyj.2 i).2
    exact disjoint_left.1 (hD i j hij) h1 h2
  have hjof : ∀ i, ∃ j : Fin k, (enum j : Ultrafilter G) = u i := fun i => by
    refine ⟨enum.symm ⟨u i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩, ?_⟩
    simp
  choose jof hjof' using hjof
  refine ⟨fun i => e.symm ⁻¹' B (jof i), fun i => ?_, fun a ha hsum => ?_⟩
  · have := hBmem (jof i)
    rw [hmemw, hjof'] at this
    exact this
  -- a solution would be one of the excluded ones
  set y : ι → ℕ := fun i => e.symm (a i) with hy
  set coef : ℕ → ℤ := fun v => ∑ i ∈ Finset.univ.filter (fun i => y i = v), c i with hcoef
  set Y : Finset ℕ := (Finset.univ.image y).filter (fun v => coef v ≠ 0) with hY
  have hYcard : Y.card ≤ n := (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp [hn]))
  have hsumY : ∑ v ∈ Y, coef v • e v = g := by
    have h1 : ∑ v ∈ Finset.univ.image y, coef v • e v = ∑ i, c i • a i := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := y) (t := Finset.univ.image y)
        (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i)) (fun i => c i • a i)]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [hcoef]
      simp only [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have : y i = v := (Finset.mem_filter.1 hi).2
      rw [← this, hy]
      simp
    rw [← hsum, ← h1, hY]
    refine Finset.sum_filter_of_ne (fun v _ hv => ?_)
    intro h0
    exact hv (by rw [h0, zero_smul])
  set r := Y.card with hr
  let ys : Fin r → ℕ := Y.orderEmbOfFin rfl
  have hysmono : StrictMono ys := (Y.orderEmbOfFin rfl).strictMono
  have hysmem : ∀ l, ys l ∈ Y := fun l => Y.orderEmbOfFin_mem rfl l
  have hσ : ∀ l, ∃ j, ys l ∈ B j := by
    intro l
    have h1 := (Finset.mem_filter.1 (hysmem l)).1
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h1
    exact ⟨jof i, hi ▸ ha i⟩
  choose σ hσ' using hσ
  have habs : ∀ v, coef v ∈ Finset.Icc (-(n : ℤ)) n := by
    intro v
    have h1 : |coef v| ≤ (n : ℤ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h2 : ∀ i ∈ Finset.univ.filter (fun i => y i = v), |c i| = 1 := by
        intro i _
        rcases hc i with h | h <;> simp [h]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (Finset.card_filter_le _ _).trans (le_of_eq (by simp [hn]))
    exact Finset.mem_Icc.2 (abs_le.1 h1)
  let idx : Idx := ⟨⟨r, Nat.lt_succ_of_le hYcard⟩, σ, fun l => ⟨coef (ys l), habs _⟩⟩
  have hnz : ∀ l, (idx.2.2 l : ℤ) ≠ 0 := fun l => (Finset.mem_filter.1 (hysmem l)).2
  refine hBidx idx hnz ys hysmono (fun l => ?_) ?_
  · exact mem_iInter.1 (hσ' l).1 idx
  · show ∑ l : Fin r, coef (ys l) • e (ys l) = g
    rw [← hsumY]
    have h1 : Finset.univ.image ys = Y := by
      apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, image_univ]
      exact Y.range_orderEmbOfFin rfl
    rw [← h1, Finset.sum_image (fun a _ b _ h => hysmono.injective h)]

/-- Theorem 3.4: in the PG generated by pairwise non-isomorphic selective ultrafilters the only null principal
ultrafilter is `pure 0`, so the PG is Hausdorff. -/
theorem genFam_hausdorff [Countable G] [Infinite G] (htor : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite)
    (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u) (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v) :
    ∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0 := by
  intro g hmem
  by_contra hg
  obtain ⟨F, hF, hle⟩ := hmem.2 (pure g) (le_of_eq (Ultrafilter.coe_pure g))
  obtain ⟨ι, _, u, c, hu, hc, hrep⟩ := rep_of_sumClosure S hF
  obtain ⟨A, hA, hav⟩ := exists_avoiding htor u (fun i => hsel _ (hu i))
    (fun i j h => hiso _ (hu i) _ (hu j) h) c hc hg
  have h1 := hle (hrep A hA)
  have h2 : g ∈ {z | ∃ a : ι → G, (∀ i, a i ∈ A i) ∧ ∑ i, c i • a i = z} := h1
  obtain ⟨a, ha, hsum⟩ := h2
  exact hav a ha hsum

/-- Every member of a representation contained in a subgroup. -/
theorem subgroup_mem_of_sumClosure (S : Set (Ultrafilter G)) (H : AddSubgroup G) (hH : ∀ u ∈ S, (H : Set G) ∈ u)
    {F : Filter G} (h : SumClosure (ultraGen S) F) : (H : Set G) ∈ F := by
  obtain ⟨ι, _, u, c, hu, _, hrep⟩ := rep_of_sumClosure S h
  refine Filter.mem_of_superset (hrep (fun _ => (H : Set G)) (fun i => hH _ (hu i))) ?_
  rintro z ⟨a, ha, rfl⟩
  exact AddSubgroup.sum_mem H (fun i _ => AddSubgroup.zsmul_mem H (ha i) _)

/-- Proposition 3.5: the vicinity filter when the ultrafilters are dense in an infinite subgroup `H`. -/
theorem mem_vic_iff_of_dense (S : Set (Ultrafilter G)) (H : AddSubgroup G) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a)
    (hH : ∀ u ∈ S, (H : Set G) ∈ u) (hdense : ∀ A ⊆ (H : Set G), A.Infinite → ∃ u ∈ S, A ∈ u)
    (hhaus : ∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0) (s : Set G) :
    s ∈ vic (genFam (ultraGen S)) ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite := by
  have hne : ∀ F ∈ ultraGen S, F.NeBot := by
    rintro F ⟨u, _, rfl⟩
    exact u.neBot
  constructor
  · intro hs
    refine ⟨vic_zero_mem (genFam_nullFamily _) hs, ?_⟩
    by_contra hinf
    obtain ⟨u, hu, hAu⟩ := hdense _ sdiff_subset hinf
    have h1 : (u : Filter G) ∈ genFam (ultraGen S) := subset_genFam hne ⟨u, hu, rfl⟩
    have h2 : s ∈ u := mem_vic.1 hs _ h1
    obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (u : Filter G)) hAu h2)
    exact hx1.2 hx2
  · rintro ⟨h0, hfin⟩
    rw [mem_vic]
    intro F hF
    rw [Filter.mem_iff_ultrafilter]
    intro V hVF
    obtain ⟨σ, hσ, hVσ⟩ := hF.2 V hVF
    have hHV : (H : Set G) ∈ V := hVσ (subgroup_mem_of_sumClosure S H hH hσ)
    by_cases hpr : ∃ a, V = pure a
    · obtain ⟨a, ha⟩ := hpr
      have h1 : (pure a : Filter G) ∈ genFam (ultraGen S) := by
        refine (genFam_nullFamily _).finer F hF _ ?_ inferInstance
        rw [← Ultrafilter.coe_pure, ← ha]
        exact hVF
      rw [ha, hhaus a h1]
      exact h0
    · push Not at hpr
      have h1 : ((H : Set G) \ s)ᶜ ∈ V := Ultrafilter.compl_mem_iff_notMem.2 (notMem_of_finite hpr hfin)
      refine Filter.mem_of_superset (Filter.inter_mem (f := (V : Filter G)) hHV h1) (fun x hx => ?_)
      by_contra hxs
      exact hx.2 ⟨hx.1, hxs⟩

end Group

end Sel

end PG
