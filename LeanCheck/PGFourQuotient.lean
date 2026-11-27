import Mathlib
import LeanCheck.PGXi
import LeanCheck.PGTwoQuotient
import LeanCheck.PGFourPretopEx

/-!
# PGfour: when is the quotient of the PG of a topology and an ideal again of this form?

`ξ` is the PG of the topology of `G` and an ideal `I` with (I1)-(I5), `N` a closed subgroup, `q : G → G ⧸ N`.
`quotC N (nullXi I)` is the family of filters converging to `0` in the final quotient, and `nullTarget N I` the family of
filters on `G ⧸ N` that contain the neighbourhoods of `0` and the image of a member of `I`.

* `quotient_eq_iff` : the two families are equal iff for every `A ∈ I` and every choice of neighbourhoods `U B` of `0`,
  one for each `B ∈ I`, finitely many of the sets `q (U B ∩ B)` cover the trace of a neighbourhood of `0` on `q A`;
* `quotient_eq_of_compact_add` : equality holds if `N ⊆ K + M` with `K ⊆ N` compact and `M ⊆ N` a member of `I`;
* `QuotEx` : a case with `N` compact (so equality holds) in which no single member of `I` serves for all neighbourhoods.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

namespace PG.Quot

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- The filters converging to `0` in `ξ`. -/
def nullXi (I : Set (Set G)) : Set (Filter G) := {F | xi I F 0}

/-- The filters converging to `0` in the PG of the quotient topology and the image ideal. -/
def nullTarget (N : AddSubgroup G) (I : Set (Set G)) : Set (Filter (G ⧸ N)) :=
  {H | H.NeBot ∧ H ≤ 𝓝 0 ∧ ∃ A ∈ I, (QuotientAddGroup.mk : G → G ⧸ N) '' A ∈ H}

variable {N : AddSubgroup G} {I : Set (Set G)}

theorem tendsto_mk_zero : Tendsto (QuotientAddGroup.mk : G → G ⧸ N) (𝓝 0) (𝓝 0) :=
  (QuotientAddGroup.continuous_mk).tendsto' _ _ rfl

theorem mk_image_nhds {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    (QuotientAddGroup.mk : G → G ⧸ N) '' U ∈ 𝓝 (0 : G ⧸ N) :=
  QuotientAddGroup.isOpenMap_coe.image_mem_nhds hU

theorem nullXi_nullFamily (hI : AdmIdeal I) : NullFamily (nullXi I) :=
  nullFamily_of_conv (isPGConv_xi hI)

/-- The quotient family is always contained in the target. -/
theorem quot_subset (hI : AdmIdeal I) : quotC N (nullXi I) ⊆ nullTarget N I := by
  have himg : ∀ F ∈ nullXi I, Filter.map (QuotientAddGroup.mk : G → G ⧸ N) F ∈ nullTarget N I := by
    rintro F ⟨hne, hle, A, hA, hAF⟩
    exact ⟨hne.map _, (map_mono hle).trans tendsto_mk_zero, A, hA, image_mem_map hAF⟩
  rintro H ⟨hne, hU⟩
  have key : ∀ W : Ultrafilter (G ⧸ N), (W : Filter (G ⧸ N)) ≤ H →
      (W : Filter (G ⧸ N)) ≤ 𝓝 0 ∧ ∃ A ∈ I, (QuotientAddGroup.mk : G → G ⧸ N) '' A ∈ W := by
    intro W hW
    obtain ⟨σ, hσ, hle⟩ := hU W hW
    obtain ⟨F0, hF0, rfl⟩ := sumClosure_mem N (nullXi_nullFamily hI) hσ
    obtain ⟨_, h1, A, hA, hAF⟩ := himg F0 hF0
    exact ⟨hle.trans h1, A, hA, hle hAF⟩
  refine ⟨hne, ?_, ?_⟩
  · rw [le_iff_ultrafilter]
    exact fun W hW => (key W hW).1
  · by_contra hno
    push Not at hno
    -- choose an ultrafilter finer than `H` avoiding all the images
    have hK : (H ⊓ ⨅ A : {A : Set G // A ∈ I}, 𝓟 ((QuotientAddGroup.mk : G → G ⧸ N) '' A.1)ᶜ).NeBot := by
      haveI : Nonempty {A : Set G // A ∈ I} := ⟨⟨∅, hI.empty_mem⟩⟩
      rw [inf_iInf]
      refine iInf_neBot_of_directed' ?_ fun A => ?_
      · intro A B
        refine ⟨⟨A.1 ∪ B.1, hI.union _ A.2 _ B.2⟩, ?_, ?_⟩
        · exact inf_le_inf_left _ (principal_mono.2 (compl_subset_compl.2 (image_mono subset_union_left)))
        · exact inf_le_inf_left _ (principal_mono.2 (compl_subset_compl.2 (image_mono subset_union_right)))
      · rw [inf_principal_neBot_iff]
        intro s hs
        by_contra hemp
        refine hno A.1 A.2 (mem_of_superset hs fun y hy => ?_)
        by_contra hyA
        exact hemp ⟨y, hy, hyA⟩
    obtain ⟨W, hW⟩ := Ultrafilter.exists_le (H ⊓ ⨅ A : {A : Set G // A ∈ I},
      𝓟 ((QuotientAddGroup.mk : G → G ⧸ N) '' A.1)ᶜ)
    obtain ⟨_, A, hA, hAW⟩ := key W (hW.trans inf_le_left)
    have : ((QuotientAddGroup.mk : G → G ⧸ N) '' A)ᶜ ∈ (W : Filter (G ⧸ N)) :=
      (hW.trans (inf_le_right.trans (iInf_le _ ⟨A, hA⟩))) (mem_principal_self _)
    have h3 := inter_mem hAW this
    rw [inter_compl_self] at h3
    exact Filter.empty_notMem _ h3

/-- To prove equality it suffices to lift every ultrafilter. -/
theorem eq_of_lift (hI : AdmIdeal I)
    (h : ∀ W : Ultrafilter (G ⧸ N), (W : Filter (G ⧸ N)) ≤ 𝓝 0 →
      ∀ A ∈ I, (QuotientAddGroup.mk : G → G ⧸ N) '' A ∈ W →
      ∃ F ∈ nullXi I, (W : Filter (G ⧸ N)) ≤ Filter.map (QuotientAddGroup.mk : G → G ⧸ N) F) :
    quotC N (nullXi I) = nullTarget N I := by
  refine Subset.antisymm (quot_subset hI) ?_
  rintro H ⟨hne, hle, A, hA, hAH⟩
  refine ⟨hne, fun W hW => ?_⟩
  obtain ⟨F, hF, hWF⟩ := h W (hW.trans hle) A hA (hW hAH)
  exact ⟨_, SumClosure.gen ⟨F, hF, rfl⟩, hWF⟩

/-- A member `B` of `I` all of whose small parts map into `W` gives the lift. -/
theorem lift_of_mem {W : Ultrafilter (G ⧸ N)} {B : Set G} (hB : B ∈ I)
    (h : ∀ U ∈ 𝓝 (0 : G), (QuotientAddGroup.mk : G → G ⧸ N) '' (U ∩ B) ∈ W) :
    ∃ F ∈ nullXi I, (W : Filter (G ⧸ N)) ≤ Filter.map (QuotientAddGroup.mk : G → G ⧸ N) F := by
  set F : Filter G := (𝓝 0 ⊓ 𝓟 B) ⊓ comap (QuotientAddGroup.mk : G → G ⧸ N) (W : Filter (G ⧸ N)) with hF
  have hmap : Filter.map (QuotientAddGroup.mk : G → G ⧸ N) F = (W : Filter (G ⧸ N)) := by
    rw [hF, Filter.push_pull]
    refine inf_eq_right.2 fun s hs => ?_
    rw [mem_map, mem_inf_principal] at hs
    refine mem_of_superset (h _ hs) ?_
    rintro _ ⟨x, ⟨hx, hxB⟩, rfl⟩
    exact hx hxB
  have hne : F.NeBot := by
    have : (Filter.map (QuotientAddGroup.mk : G → G ⧸ N) F).NeBot := by
      rw [hmap]
      infer_instance
    exact this.of_map
  exact ⟨F, ⟨hne, inf_le_left.trans inf_le_left, B, hB,
    mem_inf_of_left (mem_inf_of_right (mem_principal_self _))⟩, hmap.ge⟩

/-- The necessary and sufficient condition. -/
theorem quotient_eq_iff (hI : AdmIdeal I) :
    quotC N (nullXi I) = nullTarget N I ↔
      ∀ A ∈ I, ∀ U : Set G → Set G, (∀ B ∈ I, U B ∈ 𝓝 (0 : G)) →
        ∃ s : Finset (Set G), (∀ B ∈ s, B ∈ I) ∧ ∃ V ∈ 𝓝 (0 : G ⧸ N),
          V ∩ (QuotientAddGroup.mk : G → G ⧸ N) '' A
            ⊆ ⋃ B ∈ s, (QuotientAddGroup.mk : G → G ⧸ N) '' (U B ∩ B) := by
  classical
  constructor
  · intro heq A hA U hU
    by_contra hno
    let J := {s : Finset (Set G) // ∀ B ∈ s, B ∈ I}
    let K : J → Filter (G ⧸ N) := fun s => 𝓝 0 ⊓ 𝓟 ((QuotientAddGroup.mk : G → G ⧸ N) '' A \
      ⋃ B ∈ s.1, (QuotientAddGroup.mk : G → G ⧸ N) '' (U B ∩ B))
    haveI : Nonempty J := ⟨⟨∅, by simp⟩⟩
    have hKne : (⨅ s, K s).NeBot := by
      refine iInf_neBot_of_directed' ?_ fun s => ?_
      · intro s t
        have hst : ∀ B ∈ s.1 ∪ t.1, B ∈ I := fun B hB =>
          (Finset.mem_union.1 hB).elim (s.2 B) (t.2 B)
        refine ⟨⟨s.1 ∪ t.1, hst⟩, inf_le_inf_left _ (principal_mono.2 ?_),
          inf_le_inf_left _ (principal_mono.2 ?_)⟩
        · exact sdiff_subset_sdiff_right (biUnion_subset_biUnion_left
            (fun B hB => Finset.mem_union_left t.1 hB))
        · exact sdiff_subset_sdiff_right (biUnion_subset_biUnion_left
            (fun B hB => Finset.mem_union_right s.1 hB))
      · simp only [K]
        rw [inf_principal_neBot_iff]
        intro V hV
        by_contra hemp
        refine hno ⟨s.1, s.2, V, hV, fun y hy => ?_⟩
        by_contra hyU
        exact hemp ⟨y, hy.1, hy.2, hyU⟩
    obtain ⟨W, hW⟩ := Ultrafilter.exists_le (⨅ s, K s)
    have hW0 : (W : Filter (G ⧸ N)) ≤ 𝓝 0 := hW.trans ((iInf_le K ⟨∅, by simp⟩).trans inf_le_left)
    have hWA : (QuotientAddGroup.mk : G → G ⧸ N) '' A ∈ W :=
      (hW.trans ((iInf_le K ⟨∅, by simp⟩).trans inf_le_right)) (mem_principal.2 sdiff_subset)
    have htar : (W : Filter (G ⧸ N)) ∈ nullTarget N I := ⟨inferInstance, hW0, A, hA, hWA⟩
    rw [← heq] at htar
    obtain ⟨σ, hσ, hle⟩ := htar.2 W le_rfl
    obtain ⟨F0, ⟨_, hF1, B, hB, hBF⟩, rfl⟩ := sumClosure_mem N (nullXi_nullFamily hI) hσ
    have h1 : (QuotientAddGroup.mk : G → G ⧸ N) '' (U B ∩ B) ∈ (W : Filter (G ⧸ N)) :=
      hle (image_mem_map (inter_mem (hF1 (hU B hB)) hBF))
    have h2 : ((QuotientAddGroup.mk : G → G ⧸ N) '' (U B ∩ B))ᶜ ∈ (W : Filter (G ⧸ N)) := by
      have hs : ∀ C ∈ ({B} : Finset (Set G)), C ∈ I := fun C hC => by
        rw [Finset.mem_singleton.1 hC]
        exact hB
      refine (hW.trans ((iInf_le K ⟨{B}, hs⟩).trans inf_le_right)) (mem_principal.2 ?_)
      intro y hy hyB
      exact hy.2 (mem_biUnion (Finset.mem_singleton_self B) hyB)
    have h3 := inter_mem h1 h2
    rw [inter_compl_self] at h3
    exact Filter.empty_notMem _ h3
  · intro h
    refine eq_of_lift hI fun W hW0 A hA hAW => ?_
    have : ∃ B ∈ I, ∀ U ∈ 𝓝 (0 : G), (QuotientAddGroup.mk : G → G ⧸ N) '' (U ∩ B) ∈ W := by
      by_contra hno
      push Not at hno
      have hch : ∀ B : Set G, ∃ U ∈ 𝓝 (0 : G),
          B ∈ I → (QuotientAddGroup.mk : G → G ⧸ N) '' (U ∩ B) ∉ W := by
        intro B
        by_cases hB : B ∈ I
        · obtain ⟨U, hU, hUW⟩ := hno B hB
          exact ⟨U, hU, fun _ => hUW⟩
        · exact ⟨univ, univ_mem, fun h => absurd h hB⟩
      choose U hU hUW using hch
      obtain ⟨s, hs, V, hV, hsub⟩ := h A hA U fun B _ => hU B
      have h1 : (⋃ B ∈ s, (QuotientAddGroup.mk : G → G ⧸ N) '' (U B ∩ B)) ∈ W :=
        mem_of_superset (inter_mem (hW0 hV) hAW) hsub
      obtain ⟨B, hBs, hBW⟩ := (Ultrafilter.finite_biUnion_mem_iff s.finite_toSet).1 h1
      exact hUW B (hs B hBs) hBW
    obtain ⟨B, hB, hBW⟩ := this
    exact lift_of_mem hB hBW

/-- Equality holds if `N ⊆ K + M` with `K ⊆ N` compact and `M ⊆ N` in the ideal. -/
theorem quotient_eq_of_compact_add (hI : AdmIdeal I) {K M : Set G} (hK : IsCompact K) (hKN : K ⊆ N)
    (hM : M ∈ I) (hMN : M ⊆ N) (hN : (N : Set G) ⊆ K + M) :
    quotC N (nullXi I) = nullTarget N I := by
  refine eq_of_lift hI fun W hW0 A hA hAW => ?_
  set q : G → G ⧸ N := QuotientAddGroup.mk with hq
  -- an ultrafilter on `A` above `W`
  have hne : (comap q (W : Filter (G ⧸ N)) ⊓ 𝓟 A).NeBot := by
    rw [inf_principal_neBot_iff]
    intro s hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨y, hy1, x, hx, rfl⟩ := Filter.nonempty_of_mem (inter_mem ht hAW)
    exact ⟨x, hts hy1, hx⟩
  obtain ⟨u, hu⟩ := Ultrafilter.exists_le (comap q (W : Filter (G ⧸ N)) ⊓ 𝓟 A)
  have huA : A ∈ (u : Filter G) := (hu.trans inf_le_right) (mem_principal_self _)
  have huq : ∀ T ∈ (W : Filter (G ⧸ N)), q ⁻¹' T ∈ (u : Filter G) := fun T hT =>
    (hu.trans inf_le_left) (preimage_mem_comap hT)
  -- every neighbourhood of `0` plus `N` belongs to `u`
  have hPN : ∀ P ∈ 𝓝 (0 : G), P + K + M ∈ (u : Filter G) := by
    intro P hP
    refine mem_of_superset (huq _ (hW0 (mk_image_nhds hP))) ?_
    rintro x ⟨p, hp, hpx⟩
    have hmem : -p + x ∈ N := (QuotientAddGroup.eq).1 hpx
    obtain ⟨k, hk, m, hm, hkm⟩ := hN hmem
    refine ⟨p + k, add_mem_add hp hk, m, hm, ?_⟩
    have : p + k + m = p + (-p + x) := by
      rw [← hkm]
      abel
    simpa using this
  -- one point of `K` serves all neighbourhoods
  have hk : ∃ k ∈ K, ∀ P ∈ 𝓝 (0 : G), ({k} : Set G) + P + M ∈ (u : Filter G) := by
    by_contra hno
    push Not at hno
    choose! P hP hPu using hno
    have hhalf : ∀ k ∈ K, ∃ Q ∈ 𝓝 (0 : G), Q + Q ⊆ P k := by
      intro k hk
      obtain ⟨Q, hQo, hQ0, hQ⟩ := exists_open_nhds_zero_add_subset (hP k hk)
      exact ⟨Q, hQo.mem_nhds hQ0, hQ⟩
    choose! Q hQ hQP using hhalf
    have hcov : ∀ k ∈ K, (fun x => -k + x) ⁻¹' Q k ∈ 𝓝 k := by
      intro k hk
      have : Tendsto (fun x : G => -k + x) (𝓝 k) (𝓝 0) :=
        (continuous_const_add (-k)).tendsto' _ _ (neg_add_cancel k)
      exact this (hQ k hk)
    obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover _ hcov
    have hQ0 : (⋂ k ∈ t, Q k) ∈ 𝓝 (0 : G) := (biInter_finset_mem t).2 fun k hk => hQ k (htK k hk)
    have h1 := hPN _ hQ0
    have h2 : (⋂ k ∈ t, Q k) + K + M ⊆ ⋃ k ∈ t, ({k} : Set G) + P k + M := by
      rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, m, hm, rfl⟩
      obtain ⟨k, hkt, hbk⟩ := mem_iUnion₂.1 (ht hb)
      refine mem_biUnion hkt ⟨k + (-k + b + a), ⟨k, rfl, _, ?_, rfl⟩, m, hm, ?_⟩
      · exact hQP k (htK k hkt) (add_mem_add hbk (mem_iInter₂.1 ha k hkt))
      · show k + (-k + b + a) + m = a + b + m
        abel
    have h3 : (⋃ k ∈ t, ({k} : Set G) + P k + M) ∈ (u : Filter G) := mem_of_superset h1 h2
    obtain ⟨k, hkt, hku⟩ := (Ultrafilter.finite_biUnion_mem_iff t.finite_toSet).1 h3
    exact hPu k (htK k hkt) hku
  obtain ⟨k, hkK, hku⟩ := hk
  have hkN : k ∈ N := hKN hkK
  set S : Set G := A + {-k} + -M with hS
  have hSI : S ∈ I := by
    have h1 : A + {-k} ∈ I := hI.add A hA {-k} (hI.single _)
    have h2 : -M ∈ I := by
      have := hI.neg M hM
      rwa [image_neg_eq_neg] at this
    exact hI.add _ h1 _ h2
  refine lift_of_mem hSI fun P hP => ?_
  have hmemW : ∀ T ∈ (W : Filter (G ⧸ N)), (T ∩ q '' (P ∩ S)).Nonempty := by
    intro T hT
    obtain ⟨x, ⟨hxA, hxT⟩, hxk⟩ := Filter.nonempty_of_mem
      (inter_mem (inter_mem huA (huq T hT)) (hku P hP))
    obtain ⟨_, ⟨k', hk', p, hp, rfl⟩, m, hm, hsum⟩ := hxk
    have hsum' : k + p + m = x := by
      rw [← mem_singleton_iff.1 hk']
      exact hsum
    have hmN : m ∈ N := hMN hm
    have hpS : p ∈ S := by
      refine ⟨x + -k, add_mem_add hxA rfl, -m, ?_, ?_⟩
      · rwa [Set.mem_neg, neg_neg]
      · show x + -k + -m = p
        rw [← hsum']
        abel
    refine ⟨q x, hxT, p, ⟨hp, hpS⟩, ?_⟩
    rw [hq]
    refine (QuotientAddGroup.eq).2 ?_
    have : -p + x = k + m := by
      rw [← hsum']
      abel
    rw [this]
    exact N.add_mem hkN hmN
  rw [← Ultrafilter.mem_coe]
  by_contra hnot
  have hc : (q '' (P ∩ S))ᶜ ∈ (W : Filter (G ⧸ N)) := Ultrafilter.compl_mem_iff_notMem.2 hnot
  obtain ⟨y, hy1, hy2⟩ := hmemW _ hc
  exact hy1 hy2

end PG.Quot

/-! ### A case in which no single member of the ideal serves all neighbourhoods -/

namespace PG.QuotEx

open PG.PretopEx.Countably

noncomputable section

abbrev H := (ℕ × ℕ) →₀ ZMod 2
abbrev T := ℕ → ZMod 2

/-- The points `t j`, pairwise distinct. -/
def t (j : ℕ) : T := Pi.single j 1

theorem t_injective : Function.Injective t := by
  intro a b h
  by_contra hne
  have := congrFun h a
  rw [t, t, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
  exact one_ne_zero this

/-- The homomorphism with `φ (e (j, k)) = t j`. -/
def φ : H →ₗ[ZMod 2] T := Finsupp.linearCombination (ZMod 2) fun p : ℕ × ℕ => t p.1

def e (p : ℕ × ℕ) : H := Finsupp.single p 1

def gen : Set (H × T) := range fun p : ℕ × ℕ => (e p, t p.1)

/-- Sums of at most `m` generators. -/
def D : ℕ → Set (H × T)
  | 0 => {0}
  | m + 1 => D m ∪ (D m + gen)

def I : Set (Set (H × T)) := {B | ∃ F : Set (H × T), F.Finite ∧ ∃ m, B ⊆ F + D m}

theorem D_mono : Monotone D := monotone_nat_of_le_succ fun _ => subset_union_left

theorem zero_mem_D (m : ℕ) : (0 : H × T) ∈ D m := D_mono (Nat.zero_le m) rfl

theorem D_add (m n : ℕ) : D m + D n ⊆ D (m + n) := by
  induction n with
  | zero =>
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : b = 0 := hb
    simpa [this] using ha
  | succ n ih =>
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rcases hb with hb | ⟨c, hc, g, hg, rfl⟩
    · exact D_mono (Nat.add_le_add_left (Nat.le_succ n) m) (ih ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inr ⟨a + c, ih ⟨a, ha, c, hc, rfl⟩, g, hg, add_assoc a c g⟩

/-- All elements of `D m` lie on the graph of `φ`. -/
theorem D_graph (m : ℕ) : ∀ x ∈ D m, x.2 = φ x.1 := by
  induction m with
  | zero =>
    rintro x hx
    have : x = 0 := hx
    simp [this]
  | succ m ih =>
    rintro x (hx | ⟨a, ha, g, ⟨p, rfl⟩, rfl⟩)
    · exact ih x hx
    · have h1 : φ (e p) = t p.1 := by
        rw [φ, e, Finsupp.linearCombination_single, one_smul]
      show a.2 + t p.1 = φ (a.1 + e p)
      rw [map_add, h1, ih a ha]

/-- The supports of the first coordinates of `D m` are bounded. -/
theorem D_card (m : ℕ) : ∀ x ∈ D m, x.1.support.card ≤ m := by
  classical
  induction m with
  | zero =>
    rintro x hx
    have : x = 0 := hx
    simp [this]
  | succ m ih =>
    rintro x (hx | ⟨a, ha, g, ⟨p, rfl⟩, rfl⟩)
    · exact le_trans (ih x hx) (Nat.le_succ m)
    · refine le_trans (Finset.card_le_card Finsupp.support_add) (le_trans (Finset.card_union_le _ _) ?_)
      refine Nat.add_le_add (ih a ha) ?_
      exact le_trans (Finset.card_le_card Finsupp.support_single_subset) (by simp)

theorem neg_eq (x : H × T) : -x = x := by
  have h2 : ∀ a : ZMod 2, -a = a := by decide
  refine Prod.ext ?_ ?_
  · ext p
    exact h2 _
  · funext j
    exact h2 _

theorem admissible : AdmIdeal I := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨F, hF, m, h⟩ B hB
    exact ⟨F, hF, m, hB.trans h⟩
  · rintro A ⟨F, hF, m, h⟩ B ⟨F', hF', n, h'⟩
    refine ⟨F ∪ F', hF.union hF', max m n, union_subset ?_ ?_⟩
    · exact h.trans (add_subset_add subset_union_left (D_mono (le_max_left m n)))
    · exact h'.trans (add_subset_add subset_union_right (D_mono (le_max_right m n)))
  · intro x
    refine ⟨{x}, finite_singleton x, 0, fun y hy => ⟨x, rfl, 0, rfl, ?_⟩⟩
    rw [mem_singleton_iff.1 hy]
    exact add_zero x
  · rintro ⟨F, hF, m, h⟩
    obtain ⟨n, hn⟩ : ∃ n, ∀ f ∈ F, f.1.support.card ≤ n := by
      obtain ⟨n, hn⟩ := (hF.image fun f : H × T => f.1.support.card).bddAbove
      exact ⟨n, fun f hf => hn ⟨f, hf, rfl⟩⟩
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq (ℕ × ℕ) (n + m + 1)
    let x : H := Finsupp.indicator s fun _ _ => 1
    have hx : x.support = s := by
      ext p
      by_cases hp : p ∈ s <;> simp [x, Finsupp.indicator_apply, hp]
    obtain ⟨f, hf, d, hd, hfd⟩ := h (mem_univ (x, (0 : T)))
    have h1 : x = f.1 + d.1 := (congrArg Prod.fst hfd).symm
    have h2 : x.support.card ≤ n + m := by
      rw [h1]
      exact le_trans (Finset.card_le_card Finsupp.support_add)
        (le_trans (Finset.card_union_le _ _) (Nat.add_le_add (hn f hf) (D_card m d hd)))
    rw [hx, hs] at h2
    omega
  · rintro A ⟨F, hF, m, h⟩ B ⟨F', hF', n, h'⟩
    refine ⟨F + F', hF.add hF', m + n, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨f, hf, d, hd, rfl⟩ := h ha
    obtain ⟨f', hf', d', hd', rfl⟩ := h' hb
    exact ⟨f + f', add_mem_add hf hf', d + d', D_add m n (add_mem_add hd hd'),
      add_add_add_comm f f' d d'⟩
  · rintro A ⟨F, hF, m, h⟩
    refine ⟨F, hF, m, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    simpa [neg_eq] using h ha

/-- The subgroup `{0} × T`, which is compact. -/
def N : AddSubgroup (H × T) := (AddMonoidHom.fst H T).ker

theorem N_compact : IsCompact (N : Set (H × T)) := by
  have : (N : Set (H × T)) = ({0} : Set H) ×ˢ (univ : Set T) := by
    ext x
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  rw [this]
  exact isCompact_singleton.prod isCompact_univ

/-- Equality of the two families holds, since `N` is compact. -/
theorem equal : PG.quotC N (PG.Quot.nullXi I) = PG.Quot.nullTarget N I := by
  refine PG.Quot.quotient_eq_of_compact_add admissible (K := (N : Set (H × T))) (M := {0}) N_compact
    subset_rfl (admissible.single 0) (by simp [N.zero_mem]) ?_
  intro x hx
  exact ⟨x, hx, 0, rfl, add_zero x⟩

/-- No single member of `I` serves all neighbourhoods of `0`. -/
theorem no_single : ∀ B ∈ I, ∃ U ∈ 𝓝 (0 : H × T), ∀ V ∈ 𝓝 (0 : (H × T) ⧸ N),
    ¬ V ∩ (QuotientAddGroup.mk : H × T → (H × T) ⧸ N) '' gen
        ⊆ (QuotientAddGroup.mk : H × T → (H × T) ⧸ N) '' (U ∩ B) := by
  classical
  rintro B ⟨F, hF, m, hB⟩
  set P : Set T := (fun f : H × T => f.2 - φ f.1) '' F with hP
  have hPfin : P.Finite := hF.image _
  -- a column whose point is far from all corrections
  obtain ⟨j, hj⟩ : ∃ j, ∀ p ∈ P, t j + p ≠ 0 := by
    have : (t ⁻¹' ((fun p => -p) '' P)).Finite := (hPfin.image _).preimage t_injective.injOn
    obtain ⟨j, hj⟩ := this.exists_notMem
    refine ⟨j, fun p hp h => hj ⟨p, hp, ?_⟩⟩
    exact neg_eq_of_add_eq_zero_left h
  set W : Set T := ((fun p => t j + p) '' P)ᶜ with hW
  have hW0 : W ∈ 𝓝 (0 : T) := by
    refine (hPfin.image _).isClosed.isOpen_compl.mem_nhds ?_
    rintro ⟨p, hp, h⟩
    exact hj p hp h
  refine ⟨univ ×ˢ W, prod_mem_nhds univ_mem hW0, fun V hV hsub => ?_⟩
  -- points of the column near `0`
  have h1 : (fun x : H => (QuotientAddGroup.mk (x, (0 : T)) : (H × T) ⧸ N)) ⁻¹' V ∈ 𝓝 (0 : H) := by
    have hc : Continuous fun x : H => (QuotientAddGroup.mk (x, (0 : T)) : (H × T) ⧸ N) :=
      QuotientAddGroup.continuous_mk.comp (continuous_id.prodMk continuous_const)
    exact (hc.tendsto' 0 0 rfl) hV
  obtain ⟨E, hE⟩ := (mem_nhds_zero _).1 h1
  obtain ⟨k, hk⟩ : ∃ k, (j, k) ∉ E := by
    have : ((fun k => (j, k)) ⁻¹' (E : Set (ℕ × ℕ))).Finite :=
      E.finite_toSet.preimage (Prod.mk_right_injective j).injOn
    exact this.exists_notMem
  have hmk : ∀ x y : H × T, x.1 = y.1 → (QuotientAddGroup.mk x : (H × T) ⧸ N) = QuotientAddGroup.mk y := by
    intro x y h
    refine (QuotientAddGroup.eq).2 ?_
    show (AddMonoidHom.fst H T) (-x + y) = 0
    simp [h]
  have hV1 : (QuotientAddGroup.mk (e (j, k), t j) : (H × T) ⧸ N) ∈ V := by
    have : (QuotientAddGroup.mk (e (j, k), (0 : T)) : (H × T) ⧸ N) ∈ V := by
      refine hE (e (j, k)) fun i hi => ?_
      exact Finsupp.single_eq_of_ne fun h => hk (h ▸ hi)
    rwa [hmk (e (j, k), t j) (e (j, k), 0) rfl]
  obtain ⟨b, ⟨hbU, hbB⟩, hb⟩ := hsub ⟨hV1, (e (j, k), t j), ⟨(j, k), rfl⟩, rfl⟩
  have hb1 : b.1 = e (j, k) := by
    have h := (QuotientAddGroup.eq).1 hb
    have h' : -b.1 + e (j, k) = 0 := h
    exact neg_add_eq_zero.1 h'
  obtain ⟨f, hf, d, hd, hfd⟩ := hB hbB
  have hfd1 : f.1 + d.1 = b.1 := congrArg Prod.fst hfd
  have hfd2 : f.2 + d.2 = b.2 := congrArg Prod.snd hfd
  have hb2 : b.2 = t j + (f.2 - φ f.1) := by
    have h3 : φ (e (j, k)) = t j := by
      rw [φ, e, Finsupp.linearCombination_single, one_smul]
    have h4 : d.1 = e (j, k) - f.1 := by
      rw [← hb1, ← hfd1]
      abel
    rw [← hfd2, D_graph m d hd, h4, map_sub, h3]
    abel
  exact hbU.2 ⟨f.2 - φ f.1, ⟨f, hf, rfl⟩, hb2.symm⟩

end

end PG.QuotEx
