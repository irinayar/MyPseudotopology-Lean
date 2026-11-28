import Mathlib
import LeanCheck.PGXi

/-!
# PGfour: the group topologies above and below, and the case of a normed space

`β` is a group topology of an abelian group, `I` a family with (I1)-(I5), `xi I` the convergence of the pair.

* `le_gammaTop_iff`, `gamma_finest` : if `B 0, B 1, …` are symmetric, contain `0`, satisfy `B n + B n ⊆ B (n + 1)`,
  belong to `I` and cover `I` cofinally, then the sets `⋃ n, (V 0 ∩ B 0) + … + (V (n-1) ∩ B (n-1))`, with `V i`
  neighbourhoods of `0` for `β`, are a base at `0` of the finest group topology in which every filter that converges
  for `xi I` converges.
* `coarsest_of_multiples` : a criterion for a group topology to be the coarsest one all of whose convergent filters
  converge for `xi I`.
* `norm_coarsest` : for a normed space, a coarser group topology and the bounded sets, that coarsest one is the norm
  topology.
* `norm_pretop_iff`, `xi_eq_norm` : if `β` is moreover invariant under the scalar multiplications, then the intersection
  of the null filters has a bounded member iff `β` agrees with the norm on the unit ball at `0`, and then `xi I` is the
  norm convergence;
* `eq_normTop` : for a vector space topology that agreement means that it is the norm topology.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

namespace PG.Mixed

variable {G : Type*} [AddCommGroup G]

/-!
Every statement names its topologies, `β` being the base one. A topology bound in a statement would otherwise be
picked as the instance and silently replace the base topology.
-/

theorem nhds_translate (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) (x : G) :
    @nhds G τ x = Filter.map (fun z => x + z) (@nhds G τ 0) := by
  letI := τ
  haveI := hτ
  exact (map_add_left_nhds_zero x).symm

theorem shift_mem (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) (x : G) {V : Set G}
    (hV : V ∈ @nhds G τ 0) : (fun y => y + -x) ⁻¹' V ∈ @nhds G τ x := by
  letI := τ
  haveI := hτ
  have hc : Continuous fun y : G => y + -x := continuous_id.add continuous_const
  exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)

theorem unshift_mem (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) (x : G) {W : Set G}
    (hW : W ∈ @nhds G τ x) : (fun w => x + w) ⁻¹' W ∈ @nhds G τ 0 := by
  letI := τ
  haveI := hτ
  have hc : Continuous fun w : G => x + w := continuous_const.add continuous_id
  exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)

theorem neg_mem_nhds_zero (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) {V : Set G}
    (hV : V ∈ @nhds G τ 0) : (fun x => -x) ⁻¹' V ∈ @nhds G τ 0 := by
  letI := τ
  haveI := hτ
  exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)

theorem half_mem (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) {T : Set G}
    (hT : T ∈ @nhds G τ 0) : ∃ U ∈ @nhds G τ 0, ∀ a ∈ U, ∀ b ∈ U, a + b ∈ T := by
  letI := τ
  haveI := hτ
  exact exists_nhds_zero_half hT

theorem nsmul_mem_nhds_zero (τ : TopologicalSpace G) (hτ : @IsTopologicalAddGroup G τ _) (k : ℕ) {U : Set G}
    (hU : U ∈ @nhds G τ 0) : (fun x : G => k • x) ⁻¹' U ∈ @nhds G τ 0 := by
  letI := τ
  haveI := hτ
  exact (continuous_nsmul k).continuousAt.preimage_mem_nhds (by rw [nsmul_zero]; exact hU)

/-- The filters that converge for `xi I` converge for `σ` exactly when `σ` is coarser than `β` on the members of `I`
at `0`. -/
theorem conv_iff (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) {I : Set (Set G)} (hI : AdmIdeal I)
    (σ : TopologicalSpace G) (hσ : @IsTopologicalAddGroup G σ _) :
    (∀ (F : Filter G) (x : G), @xi G β I F x → F ≤ @nhds G σ x) ↔
      ∀ W ∈ @nhds G σ 0, ∀ A ∈ I, ∃ V ∈ @nhds G β 0, V ∩ A ⊆ W := by
  constructor
  · intro h W hW A hA
    have hmem : W ∈ @nhds G β 0 ⊓ 𝓟 A := by
      rcases (@nhds G β 0 ⊓ 𝓟 A).eq_or_neBot with hb | hne
      · rw [hb]
        exact mem_bot
      · exact h _ 0 ⟨hne, inf_le_left, A, hA, mem_inf_of_right (mem_principal_self A)⟩ hW
    refine ⟨{y | y ∈ A → y ∈ W}, mem_inf_principal.1 hmem, fun y hy => hy.1 hy.2⟩
  · intro h F x hF W hW
    obtain ⟨_, hFx, A, hA, hAF⟩ := hF
    have hAx : Set.image2 (· + ·) A {-x} ∈ I := hI.add A hA {-x} (hI.single _)
    obtain ⟨V, hV, hVW⟩ := h _ (unshift_mem σ hσ x hW) _ hAx
    refine mem_of_superset (inter_mem (hFx (shift_mem β hβ x hV)) hAF) ?_
    rintro y ⟨hy1, hy2⟩
    have h2 : y + -x ∈ V ∩ Set.image2 (· + ·) A {-x} := ⟨hy1, y, hy2, -x, rfl, rfl⟩
    have h3 : x + (y + -x) ∈ W := hVW h2
    have e : x + (y + -x) = y := by abel
    rwa [e] at h3

/-! ### The finest group topology -/

/-- The sum `(V 0 ∩ B 0) + … + (V (n-1) ∩ B (n-1))`. -/
def S (B V : ℕ → Set G) : ℕ → Set G
  | 0 => {0}
  | n + 1 => S B V n + (V n ∩ B n)

def Gam (B V : ℕ → Set G) : Set G := ⋃ n, S B V n

/-- The assumptions on the generators. -/
structure Gens (B : ℕ → Set G) : Prop where
  zero : ∀ n, (0 : G) ∈ B n
  neg : ∀ n, ∀ x ∈ B n, -x ∈ B n
  add : ∀ n, B n + B n ⊆ B (n + 1)

theorem Gens.mono {B : ℕ → Set G} (hB : Gens B) : Monotone B := by
  refine monotone_nat_of_le_succ fun n x hx => hB.add n ?_
  exact ⟨x, hx, 0, hB.zero n, add_zero x⟩

theorem S_mono_V {B V W : ℕ → Set G} (h : ∀ i, V i ⊆ W i) : ∀ n, S B V n ⊆ S B W n
  | 0 => subset_rfl
  | n + 1 => add_subset_add (S_mono_V h n) (inter_subset_inter_left _ (h n))

theorem Gam_mono {B V W : ℕ → Set G} (h : ∀ i, V i ⊆ W i) : Gam B V ⊆ Gam B W :=
  iUnion_mono fun n => S_mono_V h n

theorem S_mono_n {B V : ℕ → Set G} (hB : Gens B) (h0 : ∀ i, (0 : G) ∈ V i) : Monotone (S B V) := by
  refine monotone_nat_of_le_succ fun n x hx => ?_
  exact ⟨x, hx, 0, ⟨h0 n, hB.zero n⟩, add_zero x⟩

theorem zero_mem_Gam (B V : ℕ → Set G) : (0 : G) ∈ Gam B V :=
  mem_iUnion.2 ⟨0, rfl⟩

theorem S_double {B V W : ℕ → Set G} (hB : Gens B) (h1 : ∀ n, W n ⊆ V (2 * n)) (h2 : ∀ n, W n ⊆ V (2 * n + 1)) :
    ∀ n, S B W n + S B W n ⊆ S B V (2 * n)
  | 0 => by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    show a + b = 0
    rw [mem_singleton_iff.1 ha, mem_singleton_iff.1 hb, add_zero]
  | n + 1 => by
    rintro _ ⟨_, ⟨a, ha, u, hu, rfl⟩, _, ⟨b, hb, v, hv, rfl⟩, rfl⟩
    have hab : a + b ∈ S B V (2 * n) := S_double hB h1 h2 n (add_mem_add ha hb)
    have hu' : u ∈ V (2 * n) ∩ B (2 * n) := ⟨h1 n hu.1, hB.mono (by omega) hu.2⟩
    have hv' : v ∈ V (2 * n + 1) ∩ B (2 * n + 1) := ⟨h2 n hv.1, hB.mono (by omega) hv.2⟩
    have h3 : a + b + u + v ∈ S B V (2 * n + 1 + 1) := add_mem_add (add_mem_add hab hu') hv'
    have e : a + u + (b + v) = a + b + u + v := by abel
    show a + u + (b + v) ∈ S B V (2 * n + 1 + 1)
    rw [e]
    exact h3

theorem S_neg {B V W : ℕ → Set G} (hB : Gens B) (h1 : ∀ n, W n ⊆ V n) (h2 : ∀ n, ∀ x ∈ W n, -x ∈ V n) :
    ∀ n, ∀ x ∈ S B W n, -x ∈ S B V n
  | 0, x, hx => by
    show -x = 0
    rw [mem_singleton_iff.1 hx, neg_zero]
  | n + 1, _, ⟨a, ha, u, hu, rfl⟩ => by
    have hu' : -u ∈ V n ∩ B n := ⟨h2 n u hu.1, hB.neg n u hu.2⟩
    have h3 : -a + -u ∈ S B V (n + 1) := add_mem_add (S_neg hB h1 h2 n a ha) hu'
    show -(a + u) ∈ S B V (n + 1)
    rw [neg_add]
    exact h3

def sets (β : TopologicalSpace G) (B : ℕ → Set G) : Set (Set G) :=
  {T | ∃ V : ℕ → Set G, (∀ i, V i ∈ @nhds G β 0) ∧ T = Gam B V}

@[instance_reducible] def gammaBasis (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (B : ℕ → Set G)
    (hB : Gens B) : AddGroupFilterBasis G :=
  addGroupFilterBasisOfComm (sets β B) ⟨_, fun _ => univ, fun _ => (@nhds G β 0).univ_sets, rfl⟩
    (by
      rintro _ _ ⟨V, hV, rfl⟩ ⟨W, hW, rfl⟩
      refine ⟨_, ⟨fun i => V i ∩ W i, fun i => inter_mem (hV i) (hW i), rfl⟩, subset_inter ?_ ?_⟩
      · exact Gam_mono fun i => inter_subset_left
      · exact Gam_mono fun i => inter_subset_right)
    (by
      rintro _ ⟨V, _, rfl⟩
      exact zero_mem_Gam B V)
    (by
      rintro _ ⟨V, hV, rfl⟩
      set W : ℕ → Set G := fun n => V (2 * n) ∩ V (2 * n + 1) with hWdef
      have hW : ∀ i, W i ∈ @nhds G β 0 := fun i => inter_mem (hV _) (hV _)
      have h0 : ∀ i, (0 : G) ∈ W i := fun i => @mem_of_mem_nhds G β _ _ (hW i)
      refine ⟨_, ⟨W, hW, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 ha
      obtain ⟨m, hm⟩ := mem_iUnion.1 hb
      have ha' : a ∈ S B W (max n m) := S_mono_n hB h0 (le_max_left n m) hn
      have hb' : b ∈ S B W (max n m) := S_mono_n hB h0 (le_max_right n m) hm
      exact mem_iUnion.2 ⟨_, S_double hB (fun _ => inter_subset_left) (fun _ => inter_subset_right) _
        (add_mem_add ha' hb')⟩)
    (by
      rintro _ ⟨V, hV, rfl⟩
      set W : ℕ → Set G := fun n => V n ∩ (fun x => -x) ⁻¹' V n with hWdef
      have hW : ∀ i, W i ∈ @nhds G β 0 := fun i => inter_mem (hV i) (neg_mem_nhds_zero β hβ (hV i))
      refine ⟨_, ⟨W, hW, rfl⟩, fun x hx => ?_⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨n, S_neg hB (W := W) (fun _ => inter_subset_left) (fun _ y hy => hy.2) n x hn⟩)

/-- The group topology with the base `Gam B V` at `0`. -/
@[instance_reducible] def gammaTop (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (B : ℕ → Set G)
    (hB : Gens B) : TopologicalSpace G :=
  (gammaBasis β hβ B hB).topology

theorem gamma_group (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (B : ℕ → Set G) (hB : Gens B) :
    @IsTopologicalAddGroup G (gammaTop β hβ B hB) _ :=
  (gammaBasis β hβ B hB).isTopologicalAddGroup

theorem gamma_nhds_zero (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (B : ℕ → Set G)
    (hB : Gens B) :
    (@nhds G (gammaTop β hβ B hB) 0).HasBasis (fun V : ℕ → Set G => ∀ i, V i ∈ @nhds G β 0) (Gam B) := by
  have h := (gammaBasis β hβ B hB).nhds_zero_hasBasis
  refine h.to_hasBasis ?_ ?_
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨V, hV, subset_rfl⟩
  · intro V hV
    exact ⟨Gam B V, ⟨V, hV, rfl⟩, subset_rfl⟩

/-- A group topology is coarser than `gammaTop` iff it is coarser than `β` on each `B n` at `0`. -/
theorem le_gammaTop_iff (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (B : ℕ → Set G)
    (hB : Gens B) (σ : TopologicalSpace G) (hσ : @IsTopologicalAddGroup G σ _) :
    gammaTop β hβ B hB ≤ σ ↔ ∀ W ∈ @nhds G σ 0, ∀ n, ∃ V ∈ @nhds G β 0, V ∩ B n ⊆ W := by
  constructor
  · intro h W hW n
    obtain ⟨V, hV, hVW⟩ := (gamma_nhds_zero β hβ B hB).mem_iff.1 (nhds_mono h hW)
    refine ⟨V n, hV n, fun x hx => hVW (mem_iUnion.2 ⟨n + 1, ?_⟩)⟩
    have h0 : (0 : G) ∈ S B V n :=
      S_mono_n hB (fun i => @mem_of_mem_nhds G β _ _ (hV i)) (Nat.zero_le n) (rfl : (0 : G) ∈ S B V 0)
    exact ⟨0, h0, x, hx, zero_add x⟩
  · intro h
    have key : @nhds G (gammaTop β hβ B hB) 0 ≤ @nhds G σ 0 := by
      intro W hW
      have half : ∀ T : {T : Set G // T ∈ @nhds G σ 0}, ∃ U : {U : Set G // U ∈ @nhds G σ 0},
          ∀ a ∈ U.1, ∀ b ∈ U.1, a + b ∈ T.1 := by
        intro T
        obtain ⟨U, hU, hUT⟩ := half_mem σ hσ T.2
        exact ⟨⟨U, hU⟩, hUT⟩
      choose f hf using half
      let w : ℕ → {T : Set G // T ∈ @nhds G σ 0} := fun n => Nat.rec ⟨W, hW⟩ (fun _ T => f T) n
      have hw : ∀ n, ∀ a ∈ (w (n + 1)).1, ∀ b ∈ (w (n + 1)).1, a + b ∈ (w n).1 := fun n => hf (w n)
      have h0 : ∀ n, (0 : G) ∈ (w n).1 := fun n => @mem_of_mem_nhds G σ _ _ (w n).2
      choose V hV hVw using fun n => h (w (n + 1)).1 (w (n + 1)).2 n
      have step : ∀ n, ∀ a ∈ S B V n, ∀ b ∈ (w n).1, a + b ∈ W := by
        intro n
        induction n with
        | zero =>
          intro a ha b hb
          rw [mem_singleton_iff.1 ha, zero_add]
          exact hb
        | succ n ih =>
          rintro _ ⟨a, ha, u, hu, rfl⟩ b hb
          have h1 : u + b ∈ (w n).1 := hw n u (hVw n hu) b hb
          have e : a + u + b = a + (u + b) := add_assoc a u b
          show a + u + b ∈ W
          rw [e]
          exact ih a ha _ h1
      refine (gamma_nhds_zero β hβ B hB).mem_iff.2 ⟨V, hV, fun x hx => ?_⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      simpa using step n x hn 0 (h0 n)
    refine le_of_nhds_le_nhds fun x => ?_
    rw [nhds_translate _ (gamma_group β hβ B hB) x, nhds_translate σ hσ x]
    exact Filter.map_mono key

/-- `gammaTop` is the finest group topology in which every filter that converges for `xi I` converges. -/
theorem gamma_finest (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) {I : Set (Set G)}
    (hI : AdmIdeal I) (B : ℕ → Set G) (hB : Gens B) (hmem : ∀ n, B n ∈ I) (hcof : ∀ A ∈ I, ∃ n, A ⊆ B n) :
    (∀ (F : Filter G) (x : G), @xi G β I F x → F ≤ @nhds G (gammaTop β hβ B hB) x) ∧
      ∀ σ : TopologicalSpace G, @IsTopologicalAddGroup G σ _ →
        (∀ (F : Filter G) (x : G), @xi G β I F x → F ≤ @nhds G σ x) → gammaTop β hβ B hB ≤ σ := by
  constructor
  · rw [conv_iff β hβ hI _ (gamma_group β hβ B hB)]
    intro W hW A hA
    obtain ⟨n, hn⟩ := hcof A hA
    obtain ⟨V, hV, hVW⟩ := (le_gammaTop_iff β hβ B hB _ (gamma_group β hβ B hB)).1 le_rfl W hW n
    exact ⟨V, hV, (inter_subset_inter_right _ hn).trans hVW⟩
  · intro σ hσ h
    rw [conv_iff β hβ hI σ hσ] at h
    exact (le_gammaTop_iff β hβ B hB σ hσ).2 fun W hW n => h W hW _ (hmem n)

/-! ### The coarsest group topology below -/

/-- If the bounded multiples control `ν`, then every group topology all of whose convergent filters converge for
`xi I` (over the base topology `β`) is finer than `ν`. -/
theorem coarsest_of_multiples (β : TopologicalSpace G) {I : Set (Set G)} (ν : TopologicalSpace G)
    (hν : @IsTopologicalAddGroup G ν _)
    (hpow : ∀ A ∈ I, ∀ W ∈ @nhds G ν 0, ∃ n : ℕ, {x : G | ∀ k : ℕ, 1 ≤ k → k ≤ n → k • x ∈ A} ⊆ W)
    (σ : TopologicalSpace G) (hσ : @IsTopologicalAddGroup G σ _)
    (hσI : ∀ x : G, @xi G β I (@nhds G σ x) x) : σ ≤ ν := by
  have key : @nhds G σ 0 ≤ @nhds G ν 0 := by
    intro W hW
    obtain ⟨_, _, U, hU, hUn⟩ := hσI 0
    obtain ⟨n, hn⟩ := hpow U hU W hW
    have h1 : (⋂ k ∈ Finset.Icc 1 n, (fun x : G => k • x) ⁻¹' U) ∈ @nhds G σ 0 :=
      (biInter_finset_mem _).2 fun k _ => nsmul_mem_nhds_zero σ hσ k hUn
    refine mem_of_superset h1 fun x hx => hn fun k hk1 hk2 => ?_
    exact mem_iInter₂.1 hx k (Finset.mem_Icc.2 ⟨hk1, hk2⟩)
  refine le_of_nhds_le_nhds fun x => ?_
  rw [nhds_translate σ hσ x, nhds_translate ν hν x]
  exact Filter.map_mono key

/-! ### Normed spaces -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm topology. It is named, because a second topology on `E` in the context would otherwise be preferred. -/
@[reducible] def normTop (E : Type*) [NormedAddCommGroup E] : TopologicalSpace E := inferInstance

theorem normTop_group (E : Type*) [NormedAddCommGroup E] : @IsTopologicalAddGroup E (normTop E) _ :=
  inferInstanceAs (IsTopologicalAddGroup E)

/-- The bounded sets. -/
def bdd (E : Type*) [NormedAddCommGroup E] : Set (Set E) := {A | ∃ r : ℝ, ∀ a ∈ A, ‖a‖ ≤ r}

theorem bdd_adm [Nontrivial E] : AdmIdeal (bdd E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨r, hr⟩ C hC
    exact ⟨r, fun c hc => hr c (hC hc)⟩
  · rintro A ⟨r, hr⟩ C ⟨s, hs⟩
    refine ⟨max r s, fun a ha => ?_⟩
    rcases ha with ha | ha
    · exact le_trans (hr a ha) (le_max_left _ _)
    · exact le_trans (hs a ha) (le_max_right _ _)
  · intro x
    exact ⟨‖x‖, fun a ha => by rw [mem_singleton_iff.1 ha]⟩
  · rintro ⟨r, hr⟩
    obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E r
    exact absurd (hr x (mem_univ x)) (not_le.2 hx)
  · rintro A ⟨r, hr⟩ C ⟨s, hs⟩
    refine ⟨r + s, ?_⟩
    rintro _ ⟨a, ha, c, hc, rfl⟩
    exact le_trans (norm_add_le a c) (add_le_add (hr a ha) (hs c hc))
  · rintro A ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    show ‖-a‖ ≤ r
    rw [norm_neg]
    exact hr a ha

/-- The norm topology is below the PG of a coarser topology and the bounded sets. -/
theorem norm_below (β : TopologicalSpace E) (hβ : normTop E ≤ β) (x : E) :
    @xi E β (bdd E) (@nhds E (normTop E) x) x := by
  have hball : Metric.closedBall x 1 ∈ @nhds E (normTop E) x := Metric.closedBall_mem_nhds x one_pos
  have hne : (@nhds E (normTop E) x).NeBot := @nhds_neBot E (normTop E) x
  refine ⟨hne, nhds_mono hβ, Metric.closedBall x 1, ⟨‖x‖ + 1, fun a ha => ?_⟩, hball⟩
  have h : ‖a - x‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_eq_norm] at ha
  have h2 := norm_le_norm_add_norm_sub' a x
  linarith

/-- Every group topology below the PG is finer than the norm topology. -/
theorem norm_coarsest (β : TopologicalSpace E) (σ : TopologicalSpace E) (hσ : @IsTopologicalAddGroup E σ _)
    (hσI : ∀ x : E, @xi E β (bdd E) (@nhds E σ x) x) : σ ≤ normTop E := by
  refine coarsest_of_multiples (G := E) β (I := bdd E) (normTop E) (normTop_group E) ?_ σ hσ hσI
  rintro A ⟨r, hr⟩ W hW
  obtain ⟨ε, hε, hεW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  obtain ⟨n, hn⟩ := exists_nat_gt (max r 0 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (le_max_right r 0) hε.le) hn
    exact_mod_cast this
  refine ⟨n, fun x hx => hεW ?_⟩
  have h1 : ‖n • x‖ ≤ r := hr _ (hx n hn0 le_rfl)
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at h1
  have h2 : max r 0 < n * ε := (div_lt_iff₀ hε).1 hn
  have h3 : (n : ℝ) * ‖x‖ ≤ n * ε := le_trans h1 (le_trans (le_max_left r 0) h2.le)
  have h4 : ‖x‖ ≤ ε := le_of_mul_le_mul_left h3 (by exact_mod_cast hn0)
  simpa using h4

/-- For a linear topology the PG is pretopological at `0` only if it agrees with the norm on the unit ball. -/
theorem norm_pretop_iff (β : TopologicalSpace E)
    (hsmul : ∀ c : ℝ, @Continuous E E β β fun x => c • x) :
    (∃ r : ℝ, ∀ s : ℝ, ∃ V ∈ @nhds E β 0, ∀ x ∈ V, ‖x‖ ≤ s → ‖x‖ ≤ r) ↔
      ∀ ε > 0, ∃ V ∈ @nhds E β 0, ∀ x ∈ V, ‖x‖ ≤ 1 → ‖x‖ ≤ ε := by
  letI := β
  have scale : ∀ (c : ℝ), ∀ V ∈ 𝓝 (0 : E), (fun x : E => c • x) ⁻¹' V ∈ 𝓝 (0 : E) := fun c V hV =>
    (hsmul c).continuousAt.preimage_mem_nhds (by rw [smul_zero]; exact hV)
  constructor
  · rintro ⟨r, hr⟩ ε hε
    set s : ℝ := (max r 1) / ε with hs
    have hs0 : 0 < s := div_pos (lt_of_lt_of_le one_pos (le_max_right r 1)) hε
    obtain ⟨V, hV, h⟩ := hr s
    refine ⟨_, scale s V hV, fun x hx hx1 => ?_⟩
    have h1 : ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hs0.le]
    have h2 : ‖s • x‖ ≤ r := h _ hx (by rw [h1]; exact mul_le_of_le_one_right hs0.le hx1)
    have h3 : s * ‖x‖ ≤ s * ε := by
      rw [← h1]
      refine le_trans h2 (le_trans (le_max_left r 1) (le_of_eq ?_))
      rw [hs, div_mul_cancel₀ _ hε.ne']
    exact le_of_mul_le_mul_left h3 hs0
  · intro h
    refine ⟨1, fun s => ?_⟩
    rcases le_or_gt s 0 with hs | hs
    · exact ⟨univ, univ_mem, fun x _ hx => le_trans hx (le_trans hs zero_le_one)⟩
    · obtain ⟨V, hV, hV'⟩ := h (1 / s) (one_div_pos.2 hs)
      refine ⟨_, scale s⁻¹ V hV, fun x hx hxs => ?_⟩
      have h1 : ‖s⁻¹ • x‖ = s⁻¹ * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      have h2 : ‖s⁻¹ • x‖ ≤ 1 / s := hV' _ hx (by
        rw [h1, inv_mul_eq_div, div_le_one hs]
        exact hxs)
      rw [h1, inv_mul_eq_div] at h2
      exact (div_le_div_iff_of_pos_right hs).1 h2

/-- If the topology agrees with the norm on the unit ball at `0`, then the PG is the norm convergence. -/
theorem xi_eq_norm (β : TopologicalSpace E) (hg : @IsTopologicalAddGroup E β _)
    (hsmul : ∀ c : ℝ, @Continuous E E β β fun x => c • x)
    (hβ : normTop E ≤ β)
    (h : ∀ ε > 0, ∃ V ∈ @nhds E β 0, ∀ x ∈ V, ‖x‖ ≤ 1 → ‖x‖ ≤ ε) (F : Filter E) [F.NeBot] (x : E) :
    @xi E β (bdd E) F x ↔ F ≤ @nhds E (normTop E) x := by
  constructor
  · rintro ⟨_, hFx, A, ⟨r, hr⟩, hAF⟩
    have hbasis : (@nhds E (normTop E) x).HasBasis (fun ε : ℝ => 0 < ε) (Metric.closedBall x) :=
      Metric.nhds_basis_closedBall
    refine hbasis.ge_iff.2 fun ε hε => ?_
    set s : ℝ := max (r + ‖x‖) 1 with hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨V, hV, hV'⟩ := h (ε / s) (div_pos hε hs0)
    have h1 : (fun y : E => s⁻¹ • (y + -x)) ⁻¹' V ∈ @nhds E β x := by
      letI := β
      haveI := hg
      have hc : Continuous fun y : E => s⁻¹ • (y + -x) :=
        (hsmul s⁻¹).comp (continuous_id.add continuous_const)
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
    refine mem_of_superset (inter_mem (hFx h1) hAF) ?_
    rintro y ⟨hy, hyA⟩
    have hn : ‖s⁻¹ • (y + -x)‖ = ‖y - x‖ / s := by
      rw [← sub_eq_add_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), inv_mul_eq_div]
    have hb : ‖y - x‖ ≤ s :=
      le_trans (norm_sub_le y x) (le_trans (add_le_add (hr y hyA) le_rfl) (le_max_left _ _))
    have h2 := hV' _ hy (by rw [hn, div_le_one hs0]; exact hb)
    rw [hn] at h2
    have h3 := (div_le_div_iff_of_pos_right hs0).1 h2
    rwa [Metric.mem_closedBall, dist_eq_norm]
  · intro hF
    have h1 := norm_below β hβ x
    obtain ⟨_, h2, A, hA, hAF⟩ := h1
    exact ⟨inferInstance, hF.trans h2, A, hA, hF hAF⟩

/-- For a vector space topology that is coarser than the norm and agrees with it on the unit ball at `0`, the topology
is the norm topology. -/
theorem eq_normTop (β : TopologicalSpace E) (hg : @IsTopologicalAddGroup E β _)
    (hsm : @ContinuousSMul ℝ E _ _ β) (hβ : normTop E ≤ β)
    (h : ∀ ε > 0, ∃ V ∈ @nhds E β 0, ∀ x ∈ V, ‖x‖ ≤ 1 → ‖x‖ ≤ ε) : β = normTop E := by
  refine le_antisymm ?_ hβ
  obtain ⟨V, hV, hV'⟩ := h (1 / 2) (by norm_num)
  have hbal : ∃ W ∈ @nhds E β 0, Balanced ℝ W ∧ W ⊆ V := by
    letI := β
    haveI := hg
    haveI := hsm
    obtain ⟨W, ⟨hW, hWb⟩, hWV⟩ := (nhds_basis_balanced ℝ E).mem_iff.1 hV
    exact ⟨W, hW, hWb, hWV⟩
  obtain ⟨W, hW, hWb, hWV⟩ := hbal
  have hbd : ∀ x ∈ W, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hV' x (hWV hx) hx1
    · exfalso
      have hpos : 0 < ‖x‖ := lt_trans one_pos (not_le.1 hx1)
      have hmem : ‖x‖⁻¹ • x ∈ W := by
        refine hWb.smul_mem ?_ hx
        rw [norm_inv, norm_norm]
        exact inv_le_one_of_one_le₀ (not_le.1 hx1).le
      have hn : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      have h2 := hV' _ (hWV hmem) hn.le
      rw [hn] at h2
      norm_num at h2
  have h0 : ∀ T ∈ @nhds E (normTop E) 0, T ∈ @nhds E β 0 := by
    intro T hT
    have hbasis : (@nhds E (normTop E) 0).HasBasis (fun ε : ℝ => 0 < ε) (Metric.closedBall 0) :=
      Metric.nhds_basis_closedBall
    obtain ⟨ε, hε, hεT⟩ := hbasis.mem_iff.1 hT
    have h1 : (fun x : E => (2 * ε)⁻¹ • x) ⁻¹' W ∈ @nhds E β 0 := by
      letI := β
      haveI := hsm
      have hc : Continuous fun x : E => (2 * ε)⁻¹ • x := continuous_id.const_smul _
      exact hc.continuousAt.preimage_mem_nhds (by rw [smul_zero]; exact hW)
    refine mem_of_superset h1 (fun x hx => hεT ?_)
    have h2 := hbd _ hx
    have h3 : 0 < (2 * ε)⁻¹ := inv_pos.2 (by linarith)
    rw [norm_smul, Real.norm_of_nonneg h3.le, inv_mul_eq_div, div_le_iff₀ (by linarith : 0 < 2 * ε)] at h2
    rw [mem_closedBall_zero_iff]
    linarith
  refine le_of_nhds_le_nhds fun x => ?_
  have hn : @IsTopologicalAddGroup E (normTop E) _ := normTop_group E
  rw [PG.Mixed.nhds_translate β hg x, PG.Mixed.nhds_translate (normTop E) hn x]
  exact Filter.map_mono h0

end Normed

end PG.Mixed
