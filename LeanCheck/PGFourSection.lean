import Mathlib
import LeanCheck.PGThreeGroups

/-!
# PGfour: an ultrafilter without a coreflection when a quotient has an infinite direct sum

* `lifted_no_coreflection` : the construction of the third article with the ultrafilters on a group `G` and the
  combinatorics read through a homomorphism `p` from `G` to a direct sum;
* `bog_rank` : in a countably infinite abelian group with a finitely generated subgroup with torsion quotient there is
  an idempotent ultrafilter `q` such that the complement of every subgroup of infinite index belongs to `q`, and
  `E + E - E - E` is a Bohr neighbourhood of `0` for every `E ∈ q`;
* `no_coreflection_of_quotient` : if a quotient of the abelian group `G` has an infinite sequence of independent nonzero
  elements, some nonprincipal ultrafilter on `G` generates a PG with unique limits and no coarsest symmetric halvable
  null filter containing `0` in its members;
* `no_coreflection_rat` : this applies to the rationals.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Section4

open Sel PG.Idem PG.Words PG.Bohr PG.One PG.Groups

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

/-! ### The construction read through a homomorphism -/

section Lifted

variable {G : Type} [AddCommGroup G]
variable (C : ℕ → Type) [∀ i, AddCommGroup (C i)] (p : G →+ FSum C)
variable (supp : ∀ i, C i → Finset ℕ) (Q : ℕ → Ultrafilter G) (N : ℕ → Filter G)
  (hsupp0 : ∀ i, supp i 0 = ∅)
  (hsupp1 : ∀ i (z : C i), z ≠ 0 → (supp i z).Nonempty)
  (hwin : ∀ i (L : ℕ) (ε : Fin L → ℤ) (a : Fin L → C i), (∀ l, ε l = 1 ∨ ε l = -1) → ∀ t,
    t ∈ supp i (∑ l, ε l • a l) → ∃ l, ∃ s ∈ supp i (a l), s ≤ t ∧ t ≤ s + L)
  (hQ : ∀ i, Q i + Q i = Q i)
  (habove : ∀ i K, {x : G | (∀ j, j ≠ i → compS C j (p x) = 0) ∧ compS C i (p x) ≠ 0 ∧
    ∀ s ∈ supp i (compS C i (p x)), K < s} ∈ Q i)
  (hN : ∀ i, IsNbhdFilter (N i))
  (hQN : ∀ i, (Q i : Filter G) ≤ N i)
  (hbog : ∀ i, ∀ E ∈ Q i, dsum E ∈ N i)

include habove in
theorem lifted_Ss_mem : ∀ n j : ℕ, p ⁻¹' Ss C supp j n ∈ chain Q j n
  | 0, j => by
    rw [chain]
    refine Filter.mem_of_superset (habove j 0) (fun t ht => ?_)
    refine ⟨fun i => ?_, fun i h1 h2 => by omega⟩
    by_cases h : i = j
    · subst h
      exact ⟨fun _ => by omega, fun _ => ht.2.1⟩
    · exact ⟨fun h' => absurd (ht.1 i h) h', fun h' => absurd (by omega : i = j) h⟩
  | n + 1, j => by
    rw [chain, PG.Idem.mem_add]
    refine Filter.mem_of_superset (lifted_Ss_mem n (j + 1)) (fun y hy => ?_)
    rw [mem_setOf_eq]
    have hy' : p y ∈ Ss C supp (j + 1) n := hy
    obtain ⟨M0, hM0⟩ := compS_fin C (p y)
    set M : ℕ := (Finset.range M0).sup (fun i => (supp i (compS C i (p y))).sup id) with hM
    have hyj : compS C j (p y) = 0 := by
      by_contra h
      have := (hy'.1 j).1 h
      omega
    refine Filter.mem_of_superset (habove j M) (fun t ht => ?_)
    have hj : compS C j (p (y + t)) = compS C j (p t) := by
      rw [map_add, map_add, hyj, zero_add]
    have hne : ∀ i, i ≠ j → compS C i (p (y + t)) = compS C i (p y) := by
      intro i h
      rw [map_add, map_add, ht.1 i h, add_zero]
    show p (y + t) ∈ Ss C supp j (n + 1)
    refine ⟨fun i => ?_, fun i h1 h2 s hs t' ht' => ?_⟩
    · by_cases h : i = j
      · subst h
        rw [hj]
        exact ⟨fun _ => by omega, fun _ => ht.2.1⟩
      · rw [hne i h, hy'.1 i]
        omega
    · have hne1 : i + 1 ≠ j := by omega
      rw [hne (i + 1) hne1] at ht'
      by_cases h : i = j
      · subst h
        rw [hj] at hs
        have hi1 : i + 1 < M0 := by
          by_contra hge
          have h3 : compS C (i + 1) (p y) = 0 := hM0 _ (not_lt.1 hge)
          exact ((hy'.1 (i + 1)).2 ⟨le_rfl, by omega⟩) h3
        have h4 : t' ≤ M := le_trans (Finset.le_sup (f := id) ht')
          (Finset.le_sup (f := fun i => (supp i (compS C i (p y))).sup id) (Finset.mem_range.2 hi1))
        exact lt_of_le_of_lt h4 (ht.2.2 s hs)
      · rw [hne i h] at hs
        exact hy'.2 i (by omega) (by omega) s hs t' ht'

include habove in
theorem lifted_As_mem : p ⁻¹' As C supp ∈ chainLim Q := by
  rw [mem_chainLim]
  refine Filter.mem_of_superset Filter.univ_mem (fun n _ => ?_)
  exact Filter.mem_of_superset (lifted_Ss_mem C p supp Q habove n 0)
    (preimage_mono (subset_iUnion (fun n => Ss C supp 0 n) n))

include habove in
theorem lifted_free (a : G) : chainLim Q ≠ pure a := by
  intro h
  have h1 : ∀ m, {x : G | compS C m (p x) ≠ 0} ∈ chainLim Q := by
    intro m
    rw [mem_chainLim]
    refine Filter.mem_of_superset (Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop m)) (fun n hn => ?_)
    have hn' : m ≤ n := hn
    refine Filter.mem_of_superset (lifted_Ss_mem C p supp Q habove n 0) (fun x hx => ?_)
    have hx' : p x ∈ Ss C supp 0 n := hx
    exact (hx'.1 m).2 ⟨Nat.zero_le _, by omega⟩
  obtain ⟨M, hM⟩ := compS_fin C (p a)
  have h3 := h1 M
  rw [h] at h3
  have h4 : compS C M (p a) ≠ 0 := h3
  exact h4 (hM M le_rfl)

/-- Signed sums of `L` elements of `A`. -/
def sums (A : Set G) (L : ℕ) : Set G :=
  {y | ∃ ε : Fin L → ℤ, ∃ a : Fin L → G, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, a l ∈ A) ∧ ∑ l, ε l • a l = y}

theorem sums_of_sumClosure (u : Ultrafilter G) {A : Set G} (hA : A ∈ u) {σ : Filter G}
    (h : SumClosure (ultraGen {u}) σ) : ∃ L, sums A L ∈ σ := by
  have hgen : ∀ F : Filter G, F ∈ ultraGen {u} → A ∈ F := by
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

include hQ hN hQN hbog in
theorem lifted_null (i : ℕ) : N i ∈ genFam (ultraGen {chainLim Q}) := by
  have hgen : SumClosure (ultraGen {chainLim Q}) (chainLim Q : Filter G) := SumClosure.gen ⟨_, rfl, rfl⟩
  obtain ⟨τ, hτs, hQτ⟩ : ∃ τ : Filter G, SumClosure (ultraGen {chainLim Q}) τ ∧ (Q i : Filter G) ≤ τ :=
    ⟨_, SumClosure.add (tri_sumClosure hgen i) (sumClosure_neg (tri_sumClosure hgen (i + 1))),
      Q_le_chainLim Q (fun k => schur_of_idempotent (hQ k)) i⟩
  have hne : (N i).NeBot := Filter.NeBot.mono (Q i).neBot (hQN i)
  refine mem_genFam_of_le (SumClosure.add (SumClosure.add hτs hτs) (sumClosure_neg (SumClosure.add hτs hτs))) ?_
  intro s hs
  obtain ⟨t1, ht1, t2, ht2, h⟩ := Filter.mem_map₂_iff.1 hs
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_map₂_iff.1 ht1
  obtain ⟨C', hC', D, hD, hCD⟩ := Filter.mem_map₂_iff.1 (Filter.mem_map.1 ht2)
  have ht : A ∩ B ∩ C' ∩ D ∈ τ := Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC') hD
  have hE : A ∩ B ∩ C' ∩ D ∈ Q i := hQτ ht
  refine Filter.mem_of_superset (hbog i _ hE) (fun z hz => ?_)
  obtain ⟨a, ma, b, mb, c, mc, d, md, e⟩ := hz
  have e' : z = (a + b) + -(c + d) := by
    rw [e]
    abel
  rw [e']
  refine h (mem_image2_of_mem (hAB (mem_image2_of_mem ma.1.1.1 mb.1.1.2)) ?_)
  have h1 : c + d ∈ (fun x : G => -x) ⁻¹' t2 := hCD (mem_image2_of_mem mc.1.2 md.2)
  exact h1

include hQ habove hN hQN in
theorem lifted_meets (N0 : Filter G) (hN0 : IsNbhdFilter N0) (hmax : ∀ i, N i ≤ N0)
    (s : Set G) (hs : s ∈ N0) (m : ℕ) : (s ∩ p ⁻¹' Is C supp m).Nonempty := by
  classical
  obtain ⟨t, ht, hsum⟩ := sum_halve hN0 m s hs
  have hpick : ∀ i M : ℕ, ∃ z : G, z ∈ t ∧ (∀ j, j ≠ i → compS C j (p z) = 0) ∧ compS C i (p z) ≠ 0 ∧
      ∀ r ∈ supp i (compS C i (p z)), M < r := by
    intro i M
    have h2 : t ∈ Q i := hQN i (hmax i ht)
    obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h2 (habove i M))
    exact ⟨z, hz1, hz2⟩
  choose pick hpickt hpicko hpick0 hpickA using hpick
  let M : ℕ → ℕ := fun i => Nat.rec 0 (fun k Mk => max Mk ((supp k (compS C k (p (pick k (Mk + m))))).sup id)) i
  let z : ℕ → G := fun i => pick i (M i + m)
  have hMsucc : ∀ i, M (i + 1) = max (M i) ((supp i (compS C i (p (z i)))).sup id) := fun i => rfl
  have hMmono : Monotone M := monotone_nat_of_le_succ (fun i => by rw [hMsucc]; exact le_max_left _ _)
  have horder : ∀ i j, i < j → ∀ a ∈ supp i (compS C i (p (z i))), ∀ b ∈ supp j (compS C j (p (z j))),
      a + m < b := by
    intro i j hij a ha b hb
    have h1 : a ≤ M (i + 1) := by
      rw [hMsucc]
      exact le_trans (Finset.le_sup (f := id) ha) (le_max_right _ _)
    have h2 : M (i + 1) ≤ M j := hMmono hij
    have h3 : M j + m < b := hpickA j (M j + m) b hb
    omega
  set y : G := ∑ i : Fin m, z (i : ℕ) with hy
  have hpy : ∀ k, compS C k (p y) = ∑ i : Fin m, compS C k (p (z (i : ℕ))) := by
    intro k
    rw [hy, map_sum, map_sum]
  have hylt : ∀ k, k < m → compS C k (p y) = compS C k (p (z k)) := by
    intro k hk
    rw [hpy, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
    · intro b _ hb
      exact hpicko b _ k (fun h : k = (b : ℕ) => hb (Fin.ext h.symm))
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hyge : ∀ k, ¬ k < m → compS C k (p y) = 0 := by
    intro k hk
    rw [hpy]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    exact hpicko b _ k (fun h : k = (b : ℕ) => hk (by rw [h]; exact b.2))
  refine ⟨y, hsum _ (fun i => hpickt i (M i + m)), ?_⟩
  show p y ∈ Is C supp m
  refine ⟨fun k => ?_, fun i j hij hj a ha b hb => ?_⟩
  · by_cases hk : k < m
    · rw [hylt k hk]
      exact ⟨fun _ => hk, fun _ => hpick0 k (M k + m)⟩
    · rw [hyge k hk]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hk⟩
  · rw [hylt i (hij.trans hj)] at ha
    rw [hylt j hj] at hb
    exact horder i j hij a ha b hb

include hQ in
theorem lifted_lam : ∀ n j : ℕ, lam (chain Q j n) = 0
  | 0, j => lam_idempotent (hQ j)
  | n + 1, j => by
    rw [chain, lam_add, lifted_lam n (j + 1), lam_idempotent (hQ j), add_zero]

include hQ in
theorem lifted_hausdorff (g : G) (hg : (pure g : Filter G) ∈ genFam (ultraGen {chainLim Q})) : g = 0 := by
  have hlam : lam (chainLim Q) = 0 := by
    refine lam_eq ?_
    refine tendsto_nhds.2 (fun W hW h0 => ?_)
    show iota ⁻¹' W ∈ chainLim Q
    rw [mem_chainLim]
    refine Filter.mem_of_superset Filter.univ_mem (fun n _ => ?_)
    have h1 := lim_lam (chain Q 0 n)
    rw [lifted_lam Q hQ n 0] at h1
    exact h1 (hW.mem_nhds h0)
  have h1 : iota g ∈ K (ultraGen {chainLim Q}) := iota_mem_K _ g hg
  have h2 : K (ultraGen {chainLim Q}) ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 (fun b hb => ?_)
    obtain ⟨v, hv, rfl⟩ := L_ultraGen _ hb
    rw [mem_singleton_iff.1 hv, hlam]
    exact (⊥ : AddSubgroup (Circles G)).zero_mem
  have h3 : iota g = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact iota_injective (h3.trans (map_zero iota).symm)

include hsupp0 hsupp1 hwin hQ habove hN hQN hbog in
theorem lifted_no_coreflection :
    ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
      (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen {u}) → g = 0) ∧
      ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
        ∀ M : Filter G, IsNbhdFilter M → M ∈ genFam (ultraGen {u}) → M ≤ N0 := by
  refine ⟨chainLim Q, lifted_free C p supp Q habove, lifted_hausdorff Q hQ, ?_⟩
  rintro ⟨N0, ⟨hN0, hN0C⟩, hmax⟩
  have hC : NullFamily (genFam (ultraGen {chainLim Q})) := genFam_nullFamily _
  set J : ℕ → Set G := fun k => ⋃ m, ⋃ (_ : k ≤ m), p ⁻¹' Is C supp m with hJ
  have hJanti : Antitone J := by
    intro k k' h x hx
    simp only [hJ, mem_iUnion] at hx ⊢
    obtain ⟨m, hm, hx⟩ := hx
    exact ⟨m, h.trans hm, hx⟩
  have hne : ∀ k, (N0 ⊓ 𝓟 (J k)).NeBot := by
    intro k
    rw [inf_principal_neBot_iff]
    intro s hs
    obtain ⟨y, hy1, hy2⟩ := lifted_meets C p supp Q N hQ habove hN hQN N0 hN0
      (fun i => hmax _ (hN i) (lifted_null Q N hQ hN hQN hbog i)) s hs k
    exact ⟨y, hy1, mem_iUnion₂.2 ⟨k, le_rfl, hy2⟩⟩
  have hdir : Directed (· ≥ ·) (fun k => N0 ⊓ 𝓟 (J k)) :=
    Antitone.directed_ge (fun k k' h => inf_le_inf_left _ (principal_mono.2 (hJanti h)))
  have hinf : (⨅ k, N0 ⊓ 𝓟 (J k)).NeBot := iInf_neBot_of_directed' hdir hne
  set r : Ultrafilter G := Ultrafilter.of (⨅ k, N0 ⊓ 𝓟 (J k)) with hr
  have hrle : ∀ k, (r : Filter G) ≤ N0 ⊓ 𝓟 (J k) := fun k => (Ultrafilter.of_le _).trans (iInf_le _ k)
  have hrC : (r : Filter G) ∈ genFam (ultraGen {chainLim Q}) :=
    hC.finer _ hN0C _ ((hrle 0).trans inf_le_left) r.neBot
  obtain ⟨σ, hσ, hrσ⟩ := hrC.2 r le_rfl
  obtain ⟨L, hL⟩ := sums_of_sumClosure (chainLim Q) (lifted_As_mem C p supp Q habove) hσ
  have h1 : sums (p ⁻¹' As C supp) L ∈ (r : Filter G) := hrσ hL
  have h3 : J (L + 1) ∈ (r : Filter G) := (hrle (L + 1)).trans inf_le_right (mem_principal_self _)
  obtain ⟨y, hy1, hy2⟩ := Ultrafilter.nonempty_of_mem (f := r) (Filter.inter_mem h1 h3)
  simp only [hJ, mem_iUnion] at hy2
  obtain ⟨m, hm, hI⟩ := hy2
  have hpy : p y ∈ ns C supp L := by
    obtain ⟨ε, a, hε, ha, hs⟩ := hy1
    refine ⟨ε, fun l => p (a l), hε, ha, ?_⟩
    rw [← hs, map_sum]
    exact Finset.sum_congr rfl (fun l _ => (map_zsmul p _ _).symm)
  exact ns_disjoint_Is C supp hsupp0 hsupp1 hwin (by omega) (p y) hpy hI

end Lifted

/-! ### Bogolyubov's lemma in a countable abelian group of finite rank -/

noncomputable section

theorem chart (A : Type) [AddCommGroup A] [AddGroup.FG A] :
    ∃ (m : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Fintype T) (_ : DecidableEq T),
      Nonempty (A ≃+ (Fin m → ℤ) × T) := by
  classical
  obtain ⟨m, ι, _, q, hq, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  have : ∀ i, NeZero (q i ^ e i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  have : Fintype (DirectSum ι fun i => ZMod (q i ^ e i)) :=
    inferInstanceAs (Fintype (Π₀ i, ZMod (q i ^ e i)))
  exact ⟨m, DirectSum ι fun i => ZMod (q i ^ e i), inferInstance, this, Classical.decEq _,
    ⟨f.trans (AddEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin m)).toAddEquiv (AddEquiv.refl _))⟩⟩

theorem bog_rank {H : Type} [AddCommGroup H] [Countable H] [Infinite H] (S : Finset H)
    (hS : ∀ x : H, ∃ k : ℕ, 0 < k ∧ k • x ∈ AddSubgroup.closure (S : Set H)) :
    ∃ q : Ultrafilter H, q + q = q ∧ (∀ W : AddSubgroup H, ¬ W.FiniteIndex → (W : Set H)ᶜ ∈ q) ∧
      ∀ E ∈ q, dsum E ∈ comap (iota (G := H)) (𝓝 0) := by
  classical
  obtain ⟨h, hsurj⟩ := exists_surjective_nat H
  set Kn : ℕ → AddSubgroup H := fun n => AddSubgroup.closure ((S : Set H) ∪ h '' Iic n) with hKn
  have hmem : ∀ j n, j ≤ n → h j ∈ Kn n := fun j n hjn =>
    AddSubgroup.subset_closure (Or.inr ⟨j, hjn, rfl⟩)
  have hSle : ∀ n, AddSubgroup.closure (S : Set H) ≤ Kn n := fun n =>
    AddSubgroup.closure_mono subset_union_left
  have hmono : ∀ m n, m ≤ n → Kn m ≤ Kn n := fun m n hmn =>
    AddSubgroup.closure_mono (union_subset_union_right _ (image_mono (Iic_subset_Iic.2 hmn)))
  have hfg : ∀ n, AddGroup.FG (Kn n) := by
    intro n
    have hfin : ((S : Set H) ∪ h '' Iic n).Finite := S.finite_toSet.union ((finite_Iic n).image h)
    have : Finite ((S : Set H) ∪ h '' Iic n : Set H) := hfin.to_subtype
    exact AddGroup.closure_finite_fg _
  have hch := fun n => @chart (Kn n) _ (hfg n)
  choose m T iT fT dT he using hch
  have e : ∀ n, Kn n ≃+ (Fin (m n) → ℤ) × T n := fun n => (he n).some
  -- the rank is bounded
  have hrank : ∀ n, m n ≤ S.card := by
    intro n
    set f : Kn n →+ (Fin (m n) → ℤ) := (AddMonoidHom.fst _ _).comp (e n).toAddMonoidHom with hf
    set w : Finset (Fin (m n) → ℤ) := S.attach.image (fun s => f ⟨s.1, hSle n (AddSubgroup.subset_closure s.2)⟩)
      with hw
    have hspan : ∀ y (hy : y ∈ AddSubgroup.closure (S : Set H)),
        f ⟨y, hSle n hy⟩ ∈ Submodule.span ℤ (w : Set (Fin (m n) → ℤ)) := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        rw [hw]
        exact Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
      | zero =>
        have : (⟨0, hSle n (zero_mem _)⟩ : Kn n) = 0 := rfl
        rw [this, map_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        have : (⟨x + y, hSle n (add_mem hx hy)⟩ : Kn n) = ⟨x, hSle n hx⟩ + ⟨y, hSle n hy⟩ := rfl
        rw [this, map_add]
        exact add_mem ihx ihy
      | neg x hx ih =>
        have : (⟨-x, hSle n (neg_mem hx)⟩ : Kn n) = -⟨x, hSle n hx⟩ := rfl
        rw [this, map_neg]
        exact neg_mem ih
    have hk : ∀ i : Fin (m n), ∃ k : ℕ, 0 < k ∧
        (k : ℤ) • (Pi.single i 1 : Fin (m n) → ℤ) ∈ Submodule.span ℤ (w : Set (Fin (m n) → ℤ)) := by
      intro i
      set x : Kn n := (e n).symm (Pi.single i 1, 0) with hx
      obtain ⟨k, hk0, hkS⟩ := hS (x : H)
      refine ⟨k, hk0, ?_⟩
      have h1 := hspan _ hkS
      have h2 : (⟨k • (x : H), hSle n hkS⟩ : Kn n) = k • x := Subtype.ext (by simp)
      have h3 : f x = Pi.single i 1 := by
        show ((e n) x).1 = _
        rw [hx, AddEquiv.apply_symm_apply]
      rw [h2, map_nsmul, h3] at h1
      rwa [natCast_zsmul]
    choose k hk0 hk using hk
    have hind : LinearIndependent ℤ (fun i : Fin (m n) => (k i : ℤ) • (Pi.single i 1 : Fin (m n) → ℤ)) := by
      refine Fintype.linearIndependent_iff.2 (fun c hc j => ?_)
      have h1 := congrFun hc j
      rw [Finset.sum_apply, Finset.sum_eq_single j] at h1
      · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h1
        have h2 : (k j : ℤ) ≠ 0 := by exact_mod_cast (hk0 j).ne'
        exact (mul_eq_zero.1 h1).resolve_right h2
      · intro i _ hij
        simp [Pi.single_eq_of_ne (Ne.symm hij)]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    have h1 := linearIndependent_le_span' (R := ℤ) _ hind (w : Set (Fin (m n) → ℤ))
      (by
        rintro _ ⟨i, rfl⟩
        exact hk i)
    rw [Cardinal.mk_fintype, Nat.cast_le, Fintype.card_fin] at h1
    simp only [Finset.coe_sort_coe, Fintype.card_coe] at h1
    exact h1.trans (le_trans Finset.card_image_le (by rw [Finset.card_attach]))
  -- the boxes
  set co : ∀ n, H → (Fin (m n) → ℤ) := fun n x => if hx : x ∈ Kn n then (e n ⟨x, hx⟩).1 else 0 with hco
  set B : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup (fun j => Finset.univ.sup (fun i => (co n (h j) i).natAbs))
    with hB
  set M : ℕ → ℕ := fun n => (n + 1) * (S.card + 1) * (B n + 1) with hM
  set box : ℕ → ℕ → Finset H := fun n R =>
    ((Fintype.piFinset (fun _ : Fin (m n) => Finset.Icc (-(R : ℤ)) R)) ×ˢ (Finset.univ : Finset (T n))).image
      (fun v => (((e n).symm v : Kn n) : H)) with hbox
  have box_card : ∀ n R, (box n R).card = (2 * R + 1) ^ m n * Fintype.card (T n) := by
    intro n R
    rw [hbox]
    dsimp only
    rw [Finset.card_image_of_injective _ (fun a b hab => (e n).symm.injective (Subtype.ext hab)),
      Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc, Finset.card_univ]
    congr 2
    omega
  have box_mem : ∀ n R x, x ∈ box n R ↔ ∃ hx : x ∈ Kn n, ∀ i, -(R : ℤ) ≤ (e n ⟨x, hx⟩).1 i ∧ (e n ⟨x, hx⟩).1 i ≤ R := by
    intro n R x
    rw [hbox]
    dsimp only
    rw [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((e n).symm v).2, fun i => ?_⟩
      have h1 : (⟨(((e n).symm v : Kn n) : H), ((e n).symm v).2⟩ : Kn n) = (e n).symm v := rfl
      rw [h1, AddEquiv.apply_symm_apply]
      exact Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_product.1 hv).1 i)
    · rintro ⟨hx, hb⟩
      refine ⟨e n ⟨x, hx⟩, Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 (fun i => Finset.mem_Icc.2 (hb i)),
        Finset.mem_univ _⟩, ?_⟩
      rw [AddEquiv.symm_apply_apply]
  have hco_le : ∀ n j, j ≤ n → ∀ i, (co n (h j) i).natAbs ≤ B n := by
    intro n j hj i
    rw [hB]
    refine le_trans ?_ (Finset.le_sup (f := fun j => Finset.univ.sup (fun i => (co n (h j) i).natAbs))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
    exact Finset.le_sup (f := fun i => (co n (h j) i).natAbs) (Finset.mem_univ i)
  have hcoe : ∀ n x (hx : x ∈ Kn n), (e n ⟨x, hx⟩).1 = co n x := by
    intro n x hx
    simp only [hco, dif_pos hx]
  have hBM : ∀ n, B n ≤ M n := by
    intro n
    rw [hM]
    have h1 : 1 ≤ (n + 1) * (S.card + 1) :=
      Nat.one_le_iff_ne_zero.2 (mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _))
    exact le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ h1)
  set F : ℕ → Finset H := fun n => box n (M n) with hF
  have hmemF : ∀ n j, j ≤ n → h j ∈ F n := by
    intro n j hj
    refine (box_mem _ _ _).2 ⟨hmem j n hj, fun i => ?_⟩
    rw [hcoe]
    have h1 : (co n (h j) i).natAbs ≤ M n := (hco_le n j hj i).trans (hBM n)
    omega
  have hFne : ∀ n, (F n).Nonempty := fun n => ⟨_, hmemF n 0 (Nat.zero_le _)⟩
  have hFpos : ∀ n, (0 : ℝ) < (F n).card := fun n => by exact_mod_cast (hFne n).card_pos
  have hgrow : ∀ M0 : ℕ, ∃ N, ∀ n, N ≤ n → M0 < (F n).card := by
    intro M0
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq H (M0 + 1)
    choose idx hidx using hsurj
    refine ⟨s.sup idx, fun n hn => ?_⟩
    have h1 : s ⊆ F n := by
      intro x hx
      rw [← hidx x]
      exact hmemF n _ (le_trans (Finset.le_sup (f := idx) hx) hn)
    have h2 := Finset.card_le_card h1
    omega
  -- the boundary of the boxes is small
  have hbdry : ∀ a : H, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (((F n).filter (fun x => a + x ∉ F n)).card : ℝ) ≤ ε * (F n).card := by
    intro a ε hε
    obtain ⟨j, rfl⟩ := hsurj a
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop (max j N)] with n hn
    have hjn : j ≤ n := le_trans (le_max_left _ _) hn
    have hNn : N ≤ n := le_trans (le_max_right _ _) hn
    have hBMn := hBM n
    set R : ℕ := M n - B n with hR
    have hsub : (F n).filter (fun x => h j + x ∉ F n) ⊆ F n \ box n R := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, fun hin => hx.2 ?_⟩
      obtain ⟨hxK, hxb⟩ := (box_mem _ _ _).1 hin
      have haK := hmem j n hjn
      refine (box_mem _ _ _).2 ⟨add_mem haK hxK, fun i => ?_⟩
      have h1 : (⟨h j + x, add_mem haK hxK⟩ : Kn n) = ⟨h j, haK⟩ + ⟨x, hxK⟩ := rfl
      rw [h1, map_add, Prod.fst_add, Pi.add_apply, hcoe n (h j) haK]
      have h2 := hco_le n j hjn i
      have h3 := hxb i
      omega
    have hinner : box n R ⊆ F n := by
      intro x hx
      obtain ⟨hxK, hxb⟩ := (box_mem _ _ _).1 hx
      refine (box_mem _ _ _).2 ⟨hxK, fun i => ?_⟩
      have h3 := hxb i
      omega
    have h1 : (((F n).filter (fun x => h j + x ∉ F n)).card : ℝ) ≤ (F n).card - (box n R).card := by
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset hinner] at h2
      have h3 := Finset.card_le_card hinner
      rw [← Nat.cast_sub h3]
      exact_mod_cast h2
    refine h1.trans ?_
    have hFc : ((F n).card : ℝ) = (2 * (M n : ℝ) + 1) ^ m n * Fintype.card (T n) := by
      rw [hF]
      dsimp only
      rw [box_card]
      push_cast
      ring
    have hRc : ((box n R).card : ℝ) = (2 * (M n : ℝ) - 2 * B n + 1) ^ m n * Fintype.card (T n) := by
      rw [box_card]
      push_cast [hR, Nat.cast_sub hBMn]
      ring
    set P : ℝ := 2 * (M n : ℝ) + 1 with hP
    have hP0 : 0 < P := by
      have := Nat.cast_nonneg (α := ℝ) (M n)
      rw [hP]
      linarith
    set t : ℝ := -(2 * (B n : ℝ)) / P with ht
    have htge : -2 ≤ t := by
      rw [ht, le_div_iff₀ hP0, hP]
      have : (B n : ℝ) ≤ M n := by exact_mod_cast hBMn
      linarith
    have hbern := one_add_mul_le_pow htge (m n)
    have hQ : 2 * (M n : ℝ) - 2 * B n + 1 = P * (1 + t) := by
      rw [ht]
      field_simp
      rw [hP]
      ring
    have hkey : (m n : ℝ) * (2 * (B n : ℝ)) / P ≤ ε := by
      have h2 : (m n : ℝ) ≤ S.card := by exact_mod_cast hrank n
      have h3 : (M n : ℝ) = ((n : ℝ) + 1) * ((S.card : ℝ) + 1) * ((B n : ℝ) + 1) := by
        rw [hM]
        push_cast
        ring
      have h4 : 1 / ε < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hNn
        linarith
      have h5 : 1 < ((n : ℝ) + 1) * ε := by
        rwa [div_lt_iff₀ hε] at h4
      rw [div_le_iff₀ hP0, hP, h3]
      have hS0 : (0 : ℝ) ≤ (S.card : ℝ) + 1 := add_nonneg (Nat.cast_nonneg _) zero_le_one
      have hB0 : (0 : ℝ) ≤ (B n : ℝ) := Nat.cast_nonneg _
      have h6 : (m n : ℝ) * (2 * (B n : ℝ)) ≤ 2 * ((S.card : ℝ) + 1) * ((B n : ℝ) + 1) := by
        have := mul_le_mul (le_trans h2 (le_add_of_nonneg_right zero_le_one))
          (le_add_of_nonneg_right zero_le_one : (B n : ℝ) ≤ B n + 1) hB0 hS0
        nlinarith
      have h7 : (0 : ℝ) ≤ 2 * ((S.card : ℝ) + 1) * ((B n : ℝ) + 1) :=
        mul_nonneg (mul_nonneg zero_le_two hS0) (add_nonneg hB0 zero_le_one)
      nlinarith [mul_le_mul_of_nonneg_right h5.le h7]
    rw [hFc, hRc, hQ, mul_pow]
    have h8 : P ^ m n * (Fintype.card (T n) : ℝ) - P ^ m n * (1 + t) ^ m n * Fintype.card (T n)
        = (1 - (1 + t) ^ m n) * (P ^ m n * Fintype.card (T n)) := by ring
    rw [h8]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg hP0.le _) (Nat.cast_nonneg _))
    have h9 : -((m n : ℝ) * t) = (m n : ℝ) * (2 * (B n : ℝ)) / P := by
      rw [ht]
      ring
    linarith
  have htrans : ∀ (a : H) (s : Set H), DenseF F ((fun z => a + z) ⁻¹' s) → DenseF F s := by
    intro a s ⟨α, hα, Hd⟩
    refine ⟨α / 2, half_pos hα, fun N => ?_⟩
    obtain ⟨N1, hN1⟩ := mem_atTop_sets.1 (hbdry a (α / 2) (half_pos hα))
    obtain ⟨n, hn, h1⟩ := Hd (max N N1)
    refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
    have h2 : (((F n).filter (fun x => a + x ∉ F n)).card : ℝ) ≤ α / 2 * (F n).card :=
      hN1 n (le_trans (le_max_right _ _) hn)
    have h3 : cntF F ((fun z => a + z) ⁻¹' s) n ≤ cntF F s n + ((F n).filter (fun x => a + x ∉ F n)).card := by
      unfold cntF
      refine le_trans (Finset.card_le_card (t := ((F n).filter (fun x => x ∈ (fun z => a + z) ⁻¹' s ∧ a + x ∈ F n))
        ∪ ((F n).filter (fun x => a + x ∉ F n))) (fun x hx => ?_)) (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_le_card_of_injOn (fun x => a + x) (fun x hx => ?_)
          (fun x _ y _ hxy => add_left_cancel hxy)) _))
      · rw [Finset.mem_filter] at hx
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        by_cases hax : a + x ∈ F n
        · exact Or.inl ⟨hx.1, hx.2, hax⟩
        · exact Or.inr ⟨hx.1, hax⟩
      · rw [Finset.coe_filter] at hx ⊢
        exact ⟨hx.2.2, hx.2.1⟩
    have h4 : (cntF F ((fun z => a + z) ⁻¹' s) n : ℝ) ≤ cntF F s n + ((F n).filter (fun x => a + x ∉ F n)).card := by
      exact_mod_cast h3
    linarith
  obtain ⟨q, hq, hd⟩ := exists_idem_dense F hFne hgrow htrans
  refine ⟨q, hq, fun W hW => ?_, fun E hE => ?_⟩
  · refine Ultrafilter.compl_mem_iff_notMem.2 (fun hWq => ?_)
    obtain ⟨α, hα, Hd⟩ := hd _ hWq
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / α)
    have hinf : Infinite (H ⧸ W) := by
      refine not_finite_iff_infinite.1 (fun hfin => hW ?_)
      exact AddSubgroup.finiteIndex_of_finite_quotient
    set a : Fin k → H := fun i => (Infinite.natEmbedding (H ⧸ W) (i : ℕ)).out with ha
    have hacos : ∀ i, ((a i : H) : H ⧸ W) = Infinite.natEmbedding (H ⧸ W) (i : ℕ) := fun i =>
      QuotientAddGroup.out_eq' _
    have hev : ∀ᶠ n in atTop, ∀ i : Fin k,
        (((F n).filter (fun x => a i + x ∉ F n)).card : ℝ) ≤ α / 2 * (F n).card :=
      eventually_all.2 (fun i => hbdry (a i) (α / 2) (half_pos hα))
    obtain ⟨N1, hN1⟩ := mem_atTop_sets.1 hev
    obtain ⟨n, hn, h1⟩ := Hd N1
    set P : Fin k → Finset H := fun i =>
      (F n).filter (fun y => ∃ x ∈ (F n).filter (fun x => x ∈ (W : Set H)), a i + x = y) with hPdef
    have hPcard : ∀ i, α / 2 * (F n).card ≤ ((P i).card : ℝ) := by
      intro i
      have h2 := hN1 n hn i
      have h3 : cntF F (W : Set H) n ≤ (P i).card + ((F n).filter (fun x => a i + x ∉ F n)).card := by
        unfold cntF
        refine le_trans (Finset.card_le_card (t := ((F n).filter (fun x => x ∈ (W : Set H) ∧ a i + x ∈ F n))
          ∪ ((F n).filter (fun x => a i + x ∉ F n))) (fun x hx => ?_)) (le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add_right (Finset.card_le_card_of_injOn (fun x => a i + x) (fun x hx => ?_)
            (fun x _ y _ hxy => add_left_cancel hxy)) _))
        · rw [Finset.mem_filter] at hx
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          by_cases hax : a i + x ∈ F n
          · exact Or.inl ⟨hx.1, hx.2, hax⟩
          · exact Or.inr ⟨hx.1, hax⟩
        · rw [Finset.coe_filter] at hx
          rw [hPdef, Finset.coe_filter]
          exact ⟨hx.2.2, x, Finset.mem_filter.2 ⟨hx.1, hx.2.1⟩, rfl⟩
      have h4 : (cntF F (W : Set H) n : ℝ) ≤ (P i).card + ((F n).filter (fun x => a i + x ∉ F n)).card := by
        exact_mod_cast h3
      linarith
    have hdisj : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint P := by
      intro i _ j _ hij
      refine Finset.disjoint_left.2 (fun y hyi hyj => hij ?_)
      obtain ⟨x, hx, rfl⟩ := (Finset.mem_filter.1 hyi).2
      obtain ⟨x', hx', hxx⟩ := (Finset.mem_filter.1 hyj).2
      have hxW : x ∈ W := (Finset.mem_filter.1 hx).2
      have hx'W : x' ∈ W := (Finset.mem_filter.1 hx').2
      have h2 : ((a i : H) : H ⧸ W) = ((a j : H) : H ⧸ W) := by
        have h3 := congrArg (fun z : H => (z : H ⧸ W)) hxx
        simp only [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2 hxW,
          (QuotientAddGroup.eq_zero_iff _).2 hx'W, add_zero] at h3
        exact h3.symm
      rw [hacos, hacos] at h2
      exact Fin.ext ((Infinite.natEmbedding (H ⧸ W)).injective h2)
    have h5 : (Finset.univ.biUnion P).card ≤ (F n).card :=
      Finset.card_le_card (Finset.biUnion_subset.2 (fun i _ => Finset.filter_subset _ _))
    rw [Finset.card_biUnion hdisj] at h5
    have h6 : ∑ _i : Fin k, α / 2 * ((F n).card : ℝ) ≤ ∑ i, ((P i).card : ℝ) :=
      Finset.sum_le_sum (fun i _ => hPcard i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h6
    have h7 : (∑ i, ((P i).card : ℝ)) ≤ (F n).card := by exact_mod_cast h5
    have h8 : 2 < (k : ℝ) * α := by rwa [div_lt_iff₀ hα] at hk
    have h9 := hFpos n
    nlinarith
  · obtain ⟨α, hα, Hd⟩ := hd E hE
    set good : Set ℕ := {n | α * (F n).card ≤ (cntF F E n : ℝ)} with hgood
    have hinf : good.Infinite := by
      refine Set.infinite_of_forall_exists_gt (fun N => ?_)
      obtain ⟨n, hn, h1⟩ := Hd (N + 1)
      exact ⟨n, h1, by omega⟩
    have : ∀ n, NeZero (8 * M n + 1) := fun n => ⟨Nat.succ_ne_zero _⟩
    let ρ : ∀ n, H → (Fin (m n) → ZMod (8 * M n + 1)) × T n := fun n x =>
      if hx : x ∈ Kn n then (fun i => (((e n ⟨x, hx⟩).1 i : ℤ) : ZMod (8 * M n + 1)), (e n ⟨x, hx⟩).2) else 0
    have hρ : ∀ n x (hx : x ∈ Kn n), ρ n x =
        (fun i => (((e n ⟨x, hx⟩).1 i : ℤ) : ZMod (8 * M n + 1)), (e n ⟨x, hx⟩).2) := fun n x hx => dif_pos hx
    have hρadd : ∀ n x y, x ∈ Kn n → y ∈ Kn n → ρ n (x + y) = ρ n x + ρ n y := by
      intro n x y hx hy
      rw [hρ n x hx, hρ n y hy, hρ n (x + y) (add_mem hx hy)]
      have h1 : (⟨x + y, add_mem hx hy⟩ : Kn n) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [h1, map_add]
      refine Prod.ext (funext (fun i => ?_)) rfl
      simp
    have hρneg : ∀ n x, x ∈ Kn n → ρ n (-x) = -ρ n x := by
      intro n x hx
      have h0 : ρ n 0 = 0 := by
        rw [hρ n 0 (zero_mem _)]
        have h1 : (⟨0, zero_mem _⟩ : Kn n) = 0 := rfl
        rw [h1, map_zero]
        refine Prod.ext (funext (fun i => ?_)) rfl
        simp
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← hρadd n _ _ (neg_mem hx) hx, neg_add_cancel, h0]
    have hcongr : ∀ n x y (hx : x ∈ Kn n) (hy : y ∈ Kn n), ρ n x = ρ n y →
        (∀ i, |(e n ⟨x, hx⟩).1 i - (e n ⟨y, hy⟩).1 i| < 8 * (M n : ℤ) + 1) → x = y := by
      intro n x y hx hy hxy hsmall
      rw [hρ n x hx, hρ n y hy, Prod.mk.injEq] at hxy
      have h1 : e n ⟨x, hx⟩ = e n ⟨y, hy⟩ := by
        refine Prod.ext (funext (fun i => ?_)) hxy.2
        have h2 : ((((e n ⟨x, hx⟩).1 i - (e n ⟨y, hy⟩).1 i : ℤ)) : ZMod (8 * M n + 1)) = 0 := by
          rw [Int.cast_sub, sub_eq_zero]
          exact congrFun hxy.1 i
        have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
        refine sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h3 ?_)
        push_cast
        exact hsmall i
      exact congrArg Subtype.val ((e n).injective h1)
    set D : ∀ n, Finset ((Fin (m n) → ZMod (8 * M n + 1)) × T n) := fun n =>
      ((F n).filter (fun x => x ∈ E)).image (ρ n) with hD
    refine bohr_of_levels (fun n => (Fin (m n) → ZMod (8 * M n + 1)) × T n) ρ D good hinf (α / 4 ^ S.card)
      (div_pos hα (pow_pos four_pos _)) (fun n hn => ?_) (fun z z' => ?_) (dsum E) (fun z => ?_)
    · have hcard : (D n).card = cntF F E n := by
        rw [hD]
        dsimp only
        unfold cntF
        refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
        obtain ⟨hxK, hxb⟩ := (box_mem _ _ _).1 (Finset.mem_filter.1 hx).1
        obtain ⟨hyK, hyb⟩ := (box_mem _ _ _).1 (Finset.mem_filter.1 hy).1
        refine hcongr n x y hxK hyK hxy (fun i => ?_)
        have h1 := hxb i
        have h2 := hyb i
        rw [abs_lt]
        omega
      rw [hcard]
      have h1 : Fintype.card ((Fin (m n) → ZMod (8 * M n + 1)) × T n) ≤ 4 ^ S.card * (F n).card := by
        have h2 : (F n).card = (2 * M n + 1) ^ m n * Fintype.card (T n) := box_card n (M n)
        have h5 : (8 * M n + 1) ^ m n ≤ 4 ^ S.card * (2 * M n + 1) ^ m n := by
          refine le_trans (Nat.pow_le_pow_left (show 8 * M n + 1 ≤ 4 * (2 * M n + 1) by omega) _) ?_
          rw [mul_pow]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hrank n))
        rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, h2]
        exact le_trans (Nat.mul_le_mul_right (Fintype.card (T n)) h5) (le_of_eq (mul_assoc _ _ _))
      have h3 : (Fintype.card ((Fin (m n) → ZMod (8 * M n + 1)) × T n) : ℝ) ≤ 4 ^ S.card * (F n).card := by
        exact_mod_cast h1
      have h4 : α / 4 ^ S.card * (4 ^ S.card * ((F n).card : ℝ)) = α * (F n).card := by
        rw [← mul_assoc, div_mul_cancel₀ α (pow_ne_zero S.card (four_ne_zero (α := ℝ)))]
      exact le_trans (mul_le_mul_of_nonneg_left h3 (div_pos hα (pow_pos four_pos _)).le) (h4.le.trans hn)
    · obtain ⟨j, rfl⟩ := hsurj z
      obtain ⟨j', rfl⟩ := hsurj z'
      filter_upwards [eventually_ge_atTop (max j j')] with n hn
      exact hρadd n _ _ (hmem j n (le_trans (le_max_left _ _) hn)) (hmem j' n (le_trans (le_max_right _ _) hn))
    · obtain ⟨j, rfl⟩ := hsurj z
      filter_upwards [eventually_ge_atTop j] with n hn
      rintro ⟨a, ha, b, hb, c, hc, d, hdd, heq⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.1 hdd
      rw [Finset.mem_filter] at ha' hb' hc' hd'
      obtain ⟨haK, hab⟩ := (box_mem _ _ _).1 ha'.1
      obtain ⟨hbK, hbb⟩ := (box_mem _ _ _).1 hb'.1
      obtain ⟨hcK, hcb⟩ := (box_mem _ _ _).1 hc'.1
      obtain ⟨hdK, hdb⟩ := (box_mem _ _ _).1 hd'.1
      have hzK := hmem j n hn
      have hwK : a' + b' + -c' + -d' ∈ Kn n := add_mem (add_mem (add_mem haK hbK) (neg_mem hcK)) (neg_mem hdK)
      have hρw : ρ n (h j) = ρ n (a' + b' + -c' + -d') := by
        rw [heq, hρadd n _ _ (add_mem (add_mem haK hbK) (neg_mem hcK)) (neg_mem hdK),
          hρadd n _ _ (add_mem haK hbK) (neg_mem hcK), hρadd n _ _ haK hbK, hρneg n _ hcK, hρneg n _ hdK,
          sub_eq_add_neg, sub_eq_add_neg]
      have hz : h j = a' + b' + -c' + -d' := by
        refine hcongr n _ _ hzK hwK hρw (fun i => ?_)
        have h1 : (⟨a' + b' + -c' + -d', hwK⟩ : Kn n) = ⟨a', haK⟩ + ⟨b', hbK⟩ + -⟨c', hcK⟩ + -⟨d', hdK⟩ := rfl
        rw [h1, map_add, map_add, map_add, map_neg, map_neg, hcoe n (h j) hzK]
        simp only [Prod.fst_add, Prod.fst_neg, Pi.add_apply, Pi.neg_apply]
        have h2 := hco_le n j hn i
        have h3 := hBM n
        have h4 := hab i
        have h5 := hbb i
        have h6 := hcb i
        have h7 := hdb i
        rw [abs_lt]
        omega
      refine ⟨a', ha'.2, b', hb'.2, c', hc'.2, d', hd'.2, ?_⟩
      rw [hz]
      abel


end

/-! ### Every group with a quotient that has an infinite sequence of independent nonzero elements -/

/-- The conclusion: a nonprincipal ultrafilter whose PG has unique limits and no coarsest filter of the kind
considered. -/
def NoCoref (G : Type) [AddCommGroup G] : Prop :=
  ∃ u : Ultrafilter G, (∀ a, u ≠ pure a) ∧
    (∀ x : G, (pure x : Filter G) ∈ genFam (ultraGen {u}) → x = 0) ∧
    ¬ ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen {u})) ∧
      ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen {u}) → N ≤ N0

/-- Without an infinite sequence of independent nonzero elements there is a finite set with torsion quotient. -/
theorem finite_rank_of_no_indep {G : Type} [AddCommGroup G]
    (hfree : ¬ ∃ x : ℕ → G, (∀ k, x k ≠ 0) ∧ IndepSeq x) :
    ∃ S : Finset G, ∀ x : G, ∃ k : ℕ, 0 < k ∧ k • x ∈ AddSubgroup.closure (S : Set G) := by
  classical
  by_contra hno
  push Not at hno
  choose f hf using hno
  let s : ℕ → Finset G := fun n => Nat.rec ∅ (fun _ t => insert (f t) t) n
  have hs : ∀ n, s (n + 1) = insert (f (s n)) (s n) := fun n => rfl
  have hsmono : ∀ j n, j < n → f (s j) ∈ s n := by
    intro j n hjn
    induction n with
    | zero => omega
    | succ n ih =>
      rw [hs]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with h | h
      · exact Finset.mem_insert_of_mem (ih h)
      · rw [h]
        exact Finset.mem_insert_self _ _
  have hne : ∀ n, f (s n) ≠ 0 := by
    intro n h
    refine hf (s n) 1 one_pos ?_
    rw [one_smul, h]
    exact zero_mem _
  refine hfree ⟨fun n => f (s n), hne, fun t c hc k hk => ?_⟩
  suffices h : ∀ j ∈ t, c j = 0 by rw [h k hk, zero_smul]
  by_contra hex
  push Not at hex
  have htne : (t.filter (fun j => c j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hcj⟩ := hex
    exact ⟨j, Finset.mem_filter.2 ⟨hj, hcj⟩⟩
  set n := (t.filter (fun j => c j ≠ 0)).max' htne with hn
  have hnmem := Finset.mem_filter.1 ((t.filter (fun j => c j ≠ 0)).max'_mem htne)
  have hsum : ∑ j ∈ t.erase n, c j • f (s j) + c n • f (s n) = 0 := by
    rw [Finset.sum_erase_add _ _ hnmem.1]
    exact hc
  have hrest : ∑ j ∈ t.erase n, c j • f (s j) ∈ AddSubgroup.closure (SetLike.coe (s n)) := by
    refine AddSubgroup.sum_mem _ (fun j hj => ?_)
    obtain ⟨hjn, hjt⟩ := Finset.mem_erase.1 hj
    by_cases hcj : c j = 0
    · rw [hcj, zero_smul]
      exact zero_mem _
    · have h1 : j ≤ n := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hjt, hcj⟩)
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hsmono j n (lt_of_le_of_ne h1 hjn))) _
  have hlast : c n • f (s n) ∈ AddSubgroup.closure (SetLike.coe (s n)) := by
    have e : c n • f (s n) = -(∑ j ∈ t.erase n, c j • f (s j)) := eq_neg_of_add_eq_zero_right hsum
    rw [e]
    exact neg_mem hrest
  have habs : (c n).natAbs • f (s n) ∈ AddSubgroup.closure (SetLike.coe (s n)) := by
    rcases Int.natAbs_eq (c n) with h | h
    · rw [h, natCast_zsmul] at hlast
      exact hlast
    · rw [h, neg_zsmul, natCast_zsmul] at hlast
      simpa using neg_mem hlast
  exact hf (s n) _ (Int.natAbs_pos.2 hnmem.2) habs

/-- The main case: independent elements of prime orders in a quotient of a group of finite rank. -/
theorem case_quot {G : Type} [AddCommGroup G] (Z : AddSubgroup G) (S : Finset G)
    (hS : ∀ x : G, ∃ k : ℕ, 0 < k ∧ k • x ∈ AddSubgroup.closure (S : Set G))
    (p : ℕ → ℕ) [hp : ∀ k, Fact (p k).Prime] (g : ℕ → G ⧸ Z) (hg : IndepSeq g) (h0 : ∀ k, g k ≠ 0)
    (hord : ∀ k, p k • g k = 0) : NoCoref G := by
  classical
  have hP : ∀ i k : ℕ, Fact (p (Nat.pair i k)).Prime := fun i k => hp _
  have hNZ : ∀ i k : ℕ, NeZero (p (Nat.pair i k)) := fun i k => ⟨(hp _).out.ne_zero⟩
  let C : ℕ → Type := fun i => Tor (fun k => p (Nat.pair i k))
  have hz : ∀ i k : ℕ, (zmultiplesHom (G ⧸ Z) (g (Nat.pair i k))) (p (Nat.pair i k) : ℤ) = 0 := by
    intro i k
    rw [zmultiplesHom_apply, natCast_zsmul]
    exact hord _
  let ℓ : ∀ i k : ℕ, ZMod (p (Nat.pair i k)) →+ G ⧸ Z := fun i k =>
    ZMod.lift (p (Nat.pair i k)) ⟨zmultiplesHom (G ⧸ Z) (g (Nat.pair i k)), hz i k⟩
  have hℓ : ∀ i k (x : ZMod (p (Nat.pair i k))), ℓ i k x = (x.cast : ℤ) • g (Nat.pair i k) := by
    intro i k x
    conv_lhs => rw [← ZMod.intCast_zmod_cast x]
    show ZMod.lift (p (Nat.pair i k)) ⟨zmultiplesHom (G ⧸ Z) (g (Nat.pair i k)), hz i k⟩ ((x.cast : ℤ) : ZMod _) = _
    rw [ZMod.lift_coe]
    rfl
  have hℓ1 : ∀ i k, ℓ i k 1 = g (Nat.pair i k) := by
    intro i k
    have h1 : ℓ i k ((1 : ℤ) : ZMod (p (Nat.pair i k))) = (1 : ℤ) • g (Nat.pair i k) := by
      show ZMod.lift (p (Nat.pair i k)) ⟨zmultiplesHom (G ⧸ Z) (g (Nat.pair i k)), hz i k⟩ ((1 : ℤ) : ZMod _) = _
      rw [ZMod.lift_coe]
      rfl
    rwa [Int.cast_one, one_smul] at h1
  let φ : ∀ i : ℕ, C i →+ G ⧸ Z := fun i => DFinsupp.sumAddHom (ℓ i)
  set Φ : FSum C →+ G ⧸ Z := sumHom C φ with hΦ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨N, hN⟩ := x.2
    rw [hΦ, sumHom_eq _ _ x N hN] at hx
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
    set T : Finset ℕ := (Finset.range N ×ˢ Finset.range M).image (fun r => Nat.pair r.1 r.2) with hT
    have hinj' : Set.InjOn (fun r : ℕ × ℕ => Nat.pair r.1 r.2) (Finset.range N ×ˢ Finset.range M : Finset (ℕ × ℕ)) := by
      intro r _ r' _ h
      have h1 := congrArg Nat.unpair h
      simp only [Nat.unpair_pair] at h1
      exact h1
    have hsum : ∑ n ∈ T, c n • g n = 0 := by
      rw [hT, Finset.sum_image hinj', Finset.sum_product, ← hx]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hφ i (Finset.mem_range.1 hi)]
      exact Finset.sum_congr rfl (fun k _ => hcpair i k)
    refine Subtype.ext (funext (fun i => ?_))
    by_cases hi : i < N
    · refine DFinsupp.ext (fun k => ?_)
      show (x.1 i) k = 0
      by_cases hk : k < M
      · have h1 := hg T c hsum (Nat.pair i k)
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
  -- the value of `Φ` on a summand
  have hΦinc : ∀ i (z : C i), Φ (incS C i z) = φ i z := by
    intro i z
    have hv : ∀ j, i + 1 ≤ j → (incS C i z).1 j = 0 := fun j hj => comp_inc_ne C j i (by omega) z
    rw [hΦ, sumHom_eq C φ (incS C i z) (i + 1) hv, Finset.sum_eq_single i]
    · exact congrArg (φ i) (comp_inc_same C i z)
    · intro j _ hji
      have h1 : (incS C i z).1 j = 0 := comp_inc_ne C j i (Ne.symm hji) z
      rw [h1, map_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_self i)) h
  -- the lifts and the subgroups
  set lift : ℕ → G := fun n => (g n).out with hlift
  have hlift' : ∀ n, QuotientAddGroup.mk' Z (lift n) = g n := fun n => QuotientAddGroup.out_eq' _
  set H : ℕ → AddSubgroup G := fun i => AddSubgroup.closure (range (fun k => lift (Nat.pair i k))) with hH
  have hgenH : ∀ i k, lift (Nat.pair i k) ∈ H i := fun i k => AddSubgroup.subset_closure ⟨k, rfl⟩
  have hsingle : ∀ i k, φ i (DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k 1) = g (Nat.pair i k) := by
    intro i k
    exact (DFinsupp.sumAddHom_single (ℓ i) k 1).trans (hℓ1 i k)
  have hlands : ∀ i x, x ∈ H i → ∃ z : C i, Φ (incS C i z) = QuotientAddGroup.mk' Z x := by
    intro i x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      refine ⟨DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k 1, ?_⟩
      rw [hΦinc, hsingle, hlift']
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
    | add y z _ _ ihy ihz =>
      obtain ⟨a, ha⟩ := ihy
      obtain ⟨b, hb⟩ := ihz
      exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
    | neg y _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨-a, by rw [map_neg, map_neg, map_neg, ha]⟩
  have hincinj : ∀ i, Function.Injective (fun z : C i => Φ (incS C i z)) := by
    intro i a b hab
    have h1 := congrArg (compS C i) (hinj hab)
    rwa [comp_inc_same, comp_inc_same] at h1
  choose ψf hψf using fun i (x : H i) => hlands i x.1 x.2
  let ψ : ∀ i, H i →+ C i := fun i => AddMonoidHom.mk' (ψf i) (fun x y => by
    apply hincinj i
    show Φ (incS C i (ψf i (x + y))) = Φ (incS C i (ψf i x + ψf i y))
    rw [map_add (incS C i), map_add Φ, hψf, hψf, hψf, ← map_add]
    rfl)
  have hψ : ∀ i (x : H i), Φ (incS C i (ψ i x)) = QuotientAddGroup.mk' Z x.1 := fun i x => hψf i x
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i
    have hs1 : ∀ k, ψ i ⟨lift (Nat.pair i k), hgenH i k⟩
        = DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k 1 := by
      intro k
      apply hincinj i
      show Φ (incS C i _) = Φ (incS C i _)
      rw [hψ, hΦinc i (DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k 1), hsingle, hlift']
    have hs2 : ∀ k (a : ZMod (p (Nat.pair i k))),
        DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k a ∈ (ψ i).range := by
      intro k a
      refine ⟨(a.cast : ℤ) • ⟨lift (Nat.pair i k), hgenH i k⟩, ?_⟩
      rw [map_zsmul, hs1]
      refine (map_zsmul (DFinsupp.singleAddHom (fun k => ZMod (p (Nat.pair i k))) k) (a.cast : ℤ) 1).symm.trans ?_
      refine congrArg (DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k) ?_
      show (a.cast : ℤ) • (1 : ZMod (p (Nat.pair i k))) = a
      rw [zsmul_one, ZMod.intCast_zmod_cast]
    intro z
    have : z ∈ (ψ i).range := by
      induction z using DFinsupp.induction with
      | h0 => exact zero_mem _
      | ha k a f _ _ ih => exact add_mem (hs2 k a) ih
    exact this
  -- properties of the subgroups
  have hcount : ∀ i, Countable (H i) := by
    intro i
    have hsub : H i ≤ (Finsupp.linearCombination ℤ (fun k => lift (Nat.pair i k))).toAddMonoidHom.range := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨Finsupp.single k 1, by simp⟩
    have : Countable (Finsupp.linearCombination ℤ (fun k => lift (Nat.pair i k))).toAddMonoidHom.range :=
      Set.countable_range _ |>.to_subtype
    exact Function.Injective.countable (AddSubgroup.inclusion_injective hsub)
  have hCinf : ∀ i, Infinite (C i) := by
    intro i
    refine Infinite.of_injective (fun k => DFinsupp.single (β := fun k => ZMod (p (Nat.pair i k))) k 1)
      (fun a b hab => ?_)
    by_contra hne
    have h1 := congrArg (fun z : C i => z a) hab
    have : Fact (1 < p (Nat.pair i a)) := ⟨(hp _).out.one_lt⟩
    have h2 : (1 : ZMod (p (Nat.pair i a))) = 0 :=
      (DFinsupp.single_eq_same (β := fun k => ZMod (p (Nat.pair i k)))).symm.trans
        (h1.trans (DFinsupp.single_eq_of_ne (β := fun k => ZMod (p (Nat.pair i k))) hne))
    exact one_ne_zero h2
  have hHinf : ∀ i, Infinite (H i) := fun i => by
    have := hCinf i
    exact Infinite.of_surjective _ (hψsurj i)
  have hHrank : ∀ i, ∃ T : Finset (H i), ∀ x : H i, ∃ k : ℕ, 0 < k ∧ k • x ∈ AddSubgroup.closure (T : Set (H i)) := by
    intro i
    set M : AddSubgroup G := AddSubgroup.closure (S : Set G) ⊓ H i with hM
    have hMfg : M.FG := by
      have h1 : (AddSubgroup.closure (S : Set G)).FG := (AddSubgroup.fg_iff _).2 ⟨_, rfl, S.finite_toSet⟩
      have h2 : (AddSubgroup.toIntSubmodule (AddSubgroup.closure (S : Set G))).FG :=
        (Submodule.fg_iff_addSubgroup_fg _).2 h1
      have h3 : (AddSubgroup.toIntSubmodule M).FG := by
        have := isNoetherian_of_fg_of_noetherian _ h2
        have hle : AddSubgroup.toIntSubmodule M ≤ AddSubgroup.toIntSubmodule (AddSubgroup.closure (S : Set G)) :=
          fun x hx => hx.1
        have h4 := IsNoetherian.noetherian (Submodule.comap (AddSubgroup.toIntSubmodule
          (AddSubgroup.closure (S : Set G))).subtype (AddSubgroup.toIntSubmodule M))
        have h5 := Submodule.FG.map (AddSubgroup.toIntSubmodule (AddSubgroup.closure (S : Set G))).subtype h4
        rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h5
      exact (Submodule.fg_iff_addSubgroup_fg _).1 h3
    obtain ⟨U0, hT0, hU0⟩ := (AddSubgroup.fg_iff M).1 hMfg
    set T0 : Finset G := hU0.toFinset with hT0def
    have hT0c : AddSubgroup.closure (T0 : Set G) = M := by rw [hT0def, hU0.coe_toFinset]; exact hT0
    have hT0H : ∀ t ∈ T0, t ∈ H i := by
      intro t ht
      have h1 : t ∈ M := by
        rw [← hT0c]
        exact AddSubgroup.subset_closure ht
      exact h1.2
    refine ⟨T0.attach.image (fun t => (⟨t.1, hT0H t.1 t.2⟩ : H i)), fun x => ?_⟩
    obtain ⟨k, hk0, hk⟩ := hS x.1
    refine ⟨k, hk0, ?_⟩
    set T := T0.attach.image (fun t => (⟨t.1, hT0H t.1 t.2⟩ : H i)) with hT
    have hmap : (AddSubgroup.closure (T : Set (H i))).map (H i).subtype = M := by
      rw [AddMonoidHom.map_closure, ← hT0c]
      congr 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hz
        exact t.2
      · intro hy
        exact ⟨⟨y, hT0H y hy⟩, Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
    have h1 : ((k • x : H i) : G) ∈ M := by
      rw [AddSubgroup.coe_nsmul]
      exact ⟨hk, AddSubgroup.nsmul_mem _ x.2 _⟩
    rw [← hmap] at h1
    obtain ⟨w, hw, hwx⟩ := h1
    have e : w = k • x := Subtype.ext hwx
    rwa [e] at hw
  -- the ultrafilters
  have hbogH : ∀ i, ∃ q : Ultrafilter (H i), q + q = q ∧
      (∀ W : AddSubgroup (H i), ¬ W.FiniteIndex → (W : Set (H i))ᶜ ∈ q) ∧
      ∀ E ∈ q, dsum E ∈ comap (iota (G := H i)) (𝓝 0) := by
    intro i
    have := hcount i
    have := hHinf i
    obtain ⟨T, hT⟩ := hHrank i
    exact bog_rank T hT
  choose q hq hqinf hqbog using hbogH
  -- the group in which the construction takes place
  set B : AddSubgroup G := Φ.range.comap (QuotientAddGroup.mk' Z) with hB
  have hHB : ∀ i, H i ≤ B := by
    intro i x hx
    obtain ⟨z, hz⟩ := hlands i x hx
    exact ⟨incS C i z, hz⟩
  set eΦ := AddMonoidHom.ofInjective hinj with heΦ
  set π : B →+ Φ.range := ((QuotientAddGroup.mk' Z).comp B.subtype).codRestrict Φ.range (fun x => x.2) with hπ
  set pB : B →+ FSum C := eΦ.symm.toAddMonoidHom.comp π with hpB
  have hΦpB : ∀ x : B, Φ (pB x) = QuotientAddGroup.mk' Z x.1 := by
    intro x
    have h1 : eΦ (pB x) = π x := eΦ.apply_symm_apply (π x)
    exact congrArg Subtype.val h1
  set incl : ∀ i, H i →+ B := fun i => AddSubgroup.inclusion (hHB i) with hincl
  have hpincl : ∀ i (x : H i), pB (incl i x) = incS C i (ψ i x) := by
    intro i x
    apply hinj
    rw [hΦpB, hψ]
    rfl
  set Q : ℕ → Ultrafilter B := fun i => (q i).map (incl i) with hQdef
  set N : ℕ → Filter B := fun i => Filter.map (incl i) (comap (iota (G := H i)) (𝓝 0)) with hNdef
  have hQidem : ∀ i, Q i + Q i = Q i := by
    intro i
    have h := map_add_hom (incl i) (q i) (q i)
    rw [hq] at h
    exact h.symm
  have hNnbhd : ∀ i, IsNbhdFilter (N i) := fun i => map_nbhd _ (comap_iota_nbhd _)
  have hQN : ∀ i, (Q i : Filter B) ≤ N i := by
    intro i
    have h := lim_lam (q i)
    rw [lam_idempotent (hq i)] at h
    exact Filter.map_mono (tendsto_iff_comap.1 h)
  have hbogB : ∀ i, ∀ E ∈ Q i, dsum E ∈ N i := by
    intro i E hE
    have hE' : (incl i) ⁻¹' E ∈ q i := Ultrafilter.mem_map.1 hE
    refine Filter.mem_map.2 (Filter.mem_of_superset (hqbog i _ hE') (fun z hz => ?_))
    obtain ⟨a, ha, b, hb, c, hc, d, hd, e⟩ := hz
    exact ⟨incl i a, ha, incl i b, hb, incl i c, hc, incl i d, hd, by rw [e, map_sub, map_sub, map_add]⟩
  have habove : ∀ i K, {x : B | (∀ j, j ≠ i → compS C j (pB x) = 0) ∧ compS C i (pB x) ≠ 0 ∧
      ∀ s ∈ (compS C i (pB x)).support, K < s} ∈ Q i := by
    intro i K
    rw [hQdef]
    refine Ultrafilter.mem_map.2 ?_
    have hker : ((ψ i).ker : Set (H i))ᶜ ∈ q i := by
      refine hqinf i _ (fun hfin => ?_)
      have := hCinf i
      have h1 : Finite (H i ⧸ (ψ i).ker) := AddSubgroup.finite_quotient_of_finiteIndex
      have h2 : Finite (C i) :=
        Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivOfSurjective (ψ i) (hψsurj i)).toEquiv
      exact not_finite (C i)
    let red : C i →+ (∀ s : Fin (K + 1), ZMod (p (Nat.pair i s))) :=
      { toFun := fun z s => z (s : ℕ)
        map_zero' := rfl
        map_add' := fun a b => funext (fun s => DFinsupp.add_apply a b (s : ℕ)) }
    have : ∀ s : Fin (K + 1), Finite (ZMod (p (Nat.pair i s))) := fun s => by
      have := hNZ i s
      exact Finite.of_fintype _
    have hfi : ((red.comp (ψ i)).ker).FiniteIndex := inferInstance
    have h2 := idem_mem_finiteIndex (q i) (hq i) (red.comp (ψ i)).ker
    refine Filter.mem_of_superset (Filter.inter_mem hker h2) (fun x hx => ?_)
    rw [mem_preimage, mem_setOf_eq, hpincl]
    refine ⟨fun j hj => comp_inc_ne C j i (Ne.symm hj) _, ?_, fun s hs => ?_⟩
    · rw [comp_inc_same]
      exact hx.1
    · rw [comp_inc_same] at hs
      by_contra hsK
      have h3 : red (ψ i x) = 0 := hx.2
      have h4 := congrFun h3 ⟨s, Nat.lt_succ_of_le (not_lt.1 hsK)⟩
      exact DFinsupp.mem_support_iff.1 hs h4
  have hres := lifted_no_coreflection C pB (fun i z => z.support) Q N (fun i => DFinsupp.support_zero)
    (fun i z hz => Finset.nonempty_iff_ne_empty.2 (fun h => hz (DFinsupp.support_eq_empty.1 h)))
    (fun i L ε a _ t ht => by
      have h1 : (∑ l, ε l • a l) t ≠ 0 := DFinsupp.mem_support_iff.1 ht
      rw [DFinsupp.finsetSum_apply] at h1
      obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      refine ⟨l, t, DFinsupp.mem_support_iff.2 (fun h => hl ?_), le_rfl, Nat.le_add_right _ _⟩
      rw [DFinsupp.smul_apply, h, smul_zero])
    hQidem habove hNnbhd hQN hbogB
  exact transfer B.subtype Subtype.val_injective hres

/-- If a quotient of `G` has an infinite sequence of independent nonzero elements, some nonprincipal ultrafilter on `G`
generates a PG with unique limits and no coarsest group topology of the kind considered. -/
theorem no_coreflection_of_quotient {G : Type} [AddCommGroup G] (Z : AddSubgroup G) (g : ℕ → G ⧸ Z)
    (h0 : ∀ k, g k ≠ 0) (hg : IndepSeq g) : NoCoref G := by
  classical
  by_cases hfree : ∃ x : ℕ → G, (∀ k, x k ≠ 0) ∧ IndepSeq x
  · obtain ⟨x, hx0, hx⟩ := hfree
    exact no_coreflection_of_independent x hx0 hx
  obtain ⟨S, hS⟩ := finite_rank_of_no_indep hfree
  have hfin : {k | addOrderOf (g k) ≠ 0}.Infinite := by
    by_contra hf
    have hinf : {k | addOrderOf (g k) = 0}.Infinite := by
      have h1 := (Set.not_infinite.1 hf).infinite_compl
      refine h1.mono (fun k hk => ?_)
      exact not_not.1 hk
    set σ : ℕ → ℕ := fun n => Nat.nth (fun k => addOrderOf (g k) = 0) n with hσ
    have hσinj : Function.Injective σ := (Nat.nth_strictMono hinf).injective
    have hσmem : ∀ n, addOrderOf (g (σ n)) = 0 := fun n => Nat.nth_mem_of_infinite hinf n
    have hind := indep_comp hg σ hσinj (fun _ => 1)
    simp only [one_smul] at hind
    refine hfree ⟨fun n => (g (σ n)).out, fun n h => h0 (σ n) ?_, fun t c hc k hk => ?_⟩
    · have h1 : (((g (σ n)).out : G) : G ⧸ Z) = g (σ n) := QuotientAddGroup.out_eq' _
      have h' : (g (σ n)).out = 0 := h
      rw [← h1, h']
      rfl
    · have h1 : ∑ j ∈ t, c j • g (σ j) = 0 := by
        have h2 := congrArg (QuotientAddGroup.mk' Z) hc
        rw [map_sum, map_zero] at h2
        refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) h2
        rw [map_zsmul]
        exact congrArg (c j • ·) (QuotientAddGroup.out_eq' (g (σ j))).symm
      have h3 := hind t c h1 k hk
      have h4 : (addOrderOf (g (σ k)) : ℤ) ∣ c k := addOrderOf_dvd_iff_zsmul_eq_zero.2 h3
      rw [hσmem, Nat.cast_zero] at h4
      rw [zero_dvd_iff.1 h4, zero_smul]
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
  refine case_quot Z S hS p (fun n => m n • g (σ n)) hind (fun n h => ?_) (fun n => ?_)
  · have h1 : addOrderOf (g (σ n)) ∣ m n := addOrderOf_dvd_iff_nsmul_eq_zero.2 h
    have h2 : 0 < m n := by
      refine Nat.pos_of_ne_zero (fun h3 => hσmem n ?_)
      rw [← hpm n, h3, mul_zero]
    have h4 : m n < addOrderOf (g (σ n)) := by
      rw [← hpm n]
      exact lt_mul_of_one_lt_left h2 (Nat.Prime.one_lt (this n).out)
    exact absurd (Nat.le_of_dvd h2 h1) (not_le.2 h4)
  · rw [← mul_nsmul', hpm, addOrderOf_nsmul_eq_zero]

/-- The rationals: some nonprincipal ultrafilter on `ℚ` generates a PG without a coreflection. -/
theorem no_coreflection_rat : NoCoref ℚ := by
  classical
  set P : ℕ → ℕ := fun k => Nat.nth Nat.Prime k with hP
  have hPp : ∀ k, (P k).Prime := fun k => Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hPinj : Function.Injective P := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
  set Z : AddSubgroup ℚ := AddSubgroup.zmultiples 1 with hZ
  have hZmem : ∀ x : ℚ, x ∈ Z ↔ ∃ n : ℤ, (n : ℚ) = x := by
    intro x
    rw [hZ, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, zsmul_one]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, zsmul_one]⟩
  set g : ℕ → ℚ ⧸ Z := fun k => QuotientAddGroup.mk' Z (1 / (P k : ℚ)) with hg
  have hPne : ∀ k, (P k : ℚ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hPp k).ne_zero
  refine no_coreflection_of_quotient Z g (fun k h => ?_) (fun s c hc k hk => ?_)
  · have h1 : (1 / (P k : ℚ)) ∈ Z := (QuotientAddGroup.eq_zero_iff _).1 h
    obtain ⟨n, hn⟩ := (hZmem _).1 h1
    have h2 : (n : ℚ) * P k = 1 := by
      rw [hn, one_div, inv_mul_cancel₀ (hPne k)]
    have h3 : n * (P k : ℤ) = 1 := by exact_mod_cast h2
    have h4 : (P k : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact h3.symm⟩
    have h5 := Int.le_of_dvd one_pos h4
    have h6 := (hPp k).one_lt
    omega
  · have h1 : (∑ j ∈ s, (c j : ℚ) / (P j : ℚ)) ∈ Z := by
      refine (QuotientAddGroup.eq_zero_iff _).1 ?_
      refine Eq.trans ?_ hc
      show QuotientAddGroup.mk' Z (∑ j ∈ s, (c j : ℚ) / (P j : ℚ)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hg]
      dsimp only
      rw [← map_zsmul, zsmul_eq_mul, mul_one_div]
    obtain ⟨n, hn⟩ := (hZmem _).1 h1
    have h2 : (n : ℚ) * ∏ j ∈ s, (P j : ℚ) = ∑ j ∈ s, (c j : ℚ) * ∏ i ∈ s.erase j, (P i : ℚ) := by
      rw [hn, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← Finset.mul_prod_erase s (fun i => (P i : ℚ)) hj, ← mul_assoc, div_mul_cancel₀ _ (hPne j)]
    have h3 : n * ∏ j ∈ s, (P j : ℤ) = ∑ j ∈ s, c j * ∏ i ∈ s.erase j, (P i : ℤ) := by exact_mod_cast h2
    have h4 : (P k : ℤ) ∣ c k * ∏ i ∈ s.erase k, (P i : ℤ) := by
      have h5 : (P k : ℤ) ∣ n * ∏ j ∈ s, (P j : ℤ) :=
        Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun j => (P j : ℤ)) hk) _
      rw [h3, ← Finset.sum_erase_add _ _ hk] at h5
      have h6 : (P k : ℤ) ∣ ∑ j ∈ s.erase k, c j * ∏ i ∈ s.erase j, (P i : ℤ) := by
        refine Finset.dvd_sum (fun j hj => Dvd.dvd.mul_left ?_ _)
        refine Finset.dvd_prod_of_mem (fun i => (P i : ℤ)) (Finset.mem_erase.2 ⟨?_, hk⟩)
        exact Ne.symm (Finset.mem_erase.1 hj).1
      exact (dvd_add_right h6).1 h5
    have hpr : Prime (P k : ℤ) := Nat.prime_iff_prime_int.1 (hPp k)
    have h7 : (P k : ℤ) ∣ c k := by
      refine (hpr.dvd_or_dvd h4).resolve_right (fun h => ?_)
      obtain ⟨i, hi, hdvd⟩ := hpr.exists_mem_finset_dvd h
      have h8 : P k ∣ P i := by exact_mod_cast hdvd
      have h9 := (Nat.prime_dvd_prime_iff_eq (hPp k) (hPp i)).1 h8
      exact (Finset.mem_erase.1 hi).1 (hPinj h9).symm
    obtain ⟨d, hd⟩ := h7
    have h10 : (P k : ℤ) • g k = 0 := by
      rw [hg]
      dsimp only
      rw [← map_zsmul]
      refine (QuotientAddGroup.eq_zero_iff _).2 ((hZmem _).2 ⟨1, ?_⟩)
      rw [zsmul_eq_mul, Int.cast_natCast, mul_one_div, div_self (hPne k), Int.cast_one]
    rw [hd, mul_comm, mul_smul, h10, smul_zero]

end Section4

end PG
