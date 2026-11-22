import Mathlib
import LeanCheck.PGXi

/-!
# PG: the finest group topology as a trace (Lean check)

Scope. Theorem `PG_v10` (`tau_sub = tau_G`) in abstract form. Let `G` be an abelian group with a uniform group
topology `σ` (T0), `K` a uniform abelian group, `e : G →+ K` an injective homomorphism, and `A k ⊆ G` an increasing
sequence of sets with union `G`. Put `E k = closure (e '' A k)`.

* `exists_extension` : if for every `σ`-neighbourhood `U` of `0` there is a neighbourhood `W` of `0` in `K` with
  `x, y ∈ A` and `e x - e y ∈ W` implying `x - y ∈ U`, then the map `e x ↦ x` extends to a continuous map from
  `closure (e '' A)` to the Raikov completion of `G`;
* `huc_of_sub` : the hypothesis holds if `A - A ⊆ A'` and `A'` is continuous at `0` for the trace of `K`;
* `trace_open` : under these hypotheses for all `A k`, every `σ`-open set `V` is the preimage under `e` of a set
  `W ⊆ K` whose trace on every `E k` is open in `E k` (that is, `V` is open in the trace of the direct limit
  topology of `⋃ E k`).

Neither compactness of `K` nor closedness of the sets `A k` is used.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Uniformity

namespace PG

section completion

set_option linter.unusedSectionVars false

variable {G K : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
  [AddCommGroup K] [UniformSpace K] [IsUniformAddGroup K]

/-- Uniform continuity of a map from a subset of `K` to `G`, in group terms. -/
theorem uniformContinuous_of_group {S : Set K} (g : S → G)
    (h : ∀ U ∈ 𝓝 (0 : G), ∃ W ∈ 𝓝 (0 : K), ∀ y z : S, (z : K) - (y : K) ∈ W → g z - g y ∈ U) :
    UniformContinuous g := by
  unfold UniformContinuous
  rw [uniformity_eq_comap_nhds_zero G, tendsto_comap_iff]
  intro U hU
  obtain ⟨W, hW, hWU⟩ := h U hU
  rw [mem_map]
  have h1 : {q : K × K | q.2 - q.1 ∈ W} ∈ 𝓤 K := by
    rw [uniformity_eq_comap_nhds_zero K]
    exact ⟨W, hW, fun q hq => hq⟩
  have h2 : {q : S × S | ((q.2 : K) - (q.1 : K)) ∈ W} ∈ 𝓤 S := by
    rw [uniformity_subtype]
    exact ⟨_, h1, fun q hq => hq⟩
  filter_upwards [h2] with q hq
  exact hWU q.1 q.2 hq

/-- The hypothesis of `exists_extension` follows from `A - A ⊆ A'` and continuity of the inclusion of `A'`. -/
theorem huc_of_sub (e : G →+ K) {A A' : Set G} (hdiff : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ A')
    (hcont : ∀ U ∈ 𝓝 (0 : G), ∃ W ∈ 𝓝 (0 : K), ∀ x ∈ A', e x ∈ W → x ∈ U) :
    ∀ U ∈ 𝓝 (0 : G), ∃ W ∈ 𝓝 (0 : K), ∀ x ∈ A, ∀ y ∈ A, e x - e y ∈ W → x - y ∈ U := by
  intro U hU
  obtain ⟨W, hW, hWU⟩ := hcont U hU
  refine ⟨W, hW, fun x hx y hy hxy => hWU _ (hdiff x hx y hy) ?_⟩
  rw [map_sub]
  exact hxy

variable [T0Space G]

/-- Extension of `e x ↦ x` from `e '' A` to its closure, into the Raikov completion of `G`. -/
theorem exists_extension (e : G →+ K) (hinj : Function.Injective e) (A : Set G)
    (huc : ∀ U ∈ 𝓝 (0 : G), ∃ W ∈ 𝓝 (0 : K), ∀ x ∈ A, ∀ y ∈ A, e x - e y ∈ W → x - y ∈ U) :
    ∃ ψ : closure (e '' A) → UniformSpace.Completion G, Continuous ψ ∧
      ∀ x ∈ A, ∀ h : e x ∈ closure (e '' A), ψ ⟨e x, h⟩ = (x : UniformSpace.Completion G) := by
  classical
  let β : Type _ := ↥(e '' A)
  let α : Type _ := ↥(closure (e '' A))
  let emb : β → α := Set.inclusion subset_closure
  have hind : IsUniformInducing emb := by
    refine ⟨?_⟩
    rw [uniformity_subtype, uniformity_subtype, comap_comap]
    rfl
  have hdense : DenseRange emb := by
    intro z
    rw [mem_closure_iff_nhds]
    intro t ht
    have hz := z.2
    rw [mem_closure_iff_nhds] at hz
    rw [nhds_subtype_eq_comap] at ht
    obtain ⟨s, hs, hst⟩ := mem_comap.1 ht
    obtain ⟨y, hys, hyA⟩ := hz s hs
    exact ⟨emb ⟨y, hyA⟩, hst hys, ⟨y, hyA⟩, rfl⟩
  let π : K → G := Function.invFun e
  have hπ : ∀ x : G, π (e x) = x := Function.leftInverse_invFun hinj
  let g : β → G := fun y => π y.1
  have hg : UniformContinuous g := by
    refine uniformContinuous_of_group g ?_
    intro U hU
    obtain ⟨W, hW, hWU⟩ := huc U hU
    refine ⟨W, hW, ?_⟩
    rintro ⟨_, y, hy, rfl⟩ ⟨_, z, hz, rfl⟩ hzy
    simp only [g, hπ]
    exact hWU z hz y hy hzy
  let f : β → UniformSpace.Completion G := fun y => (g y : UniformSpace.Completion G)
  have hf : UniformContinuous f :=
    (UniformSpace.Completion.uniformContinuous_coe G).comp hg
  have di := hind.isDenseInducing hdense
  refine ⟨IsDenseInducing.extend di f, (uniformContinuous_uniformly_extend hind hdense hf).continuous, ?_⟩
  intro x hx h
  have := uniformly_extend_of_ind hind hdense hf ⟨e x, ⟨x, hx, rfl⟩⟩
  simpa [f, g, hπ, emb] using this

/-- The inclusion of a set into its closure has dense range. -/
theorem denseRange_inclusion_closure (S : Set K) :
    DenseRange (Set.inclusion (subset_closure : S ⊆ closure S)) := by
  intro z
  rw [mem_closure_iff_nhds]
  intro t ht
  have hz := z.2
  rw [mem_closure_iff_nhds] at hz
  rw [nhds_subtype_eq_comap] at ht
  obtain ⟨s, hs, hst⟩ := mem_comap.1 ht
  obtain ⟨y, hys, hyA⟩ := hz s hs
  exact ⟨Set.inclusion subset_closure ⟨y, hyA⟩, hst hys, ⟨y, hyA⟩, rfl⟩

/-- Compatibility of the extensions at two levels. -/
theorem extension_compat (e : G →+ K) {A B : Set G} (hAB : A ⊆ B)
    {ψA : closure (e '' A) → UniformSpace.Completion G} (hA : Continuous ψA)
    (hAv : ∀ x ∈ A, ∀ h : e x ∈ closure (e '' A), ψA ⟨e x, h⟩ = (x : UniformSpace.Completion G))
    {ψB : closure (e '' B) → UniformSpace.Completion G} (hB : Continuous ψB)
    (hBv : ∀ x ∈ B, ∀ h : e x ∈ closure (e '' B), ψB ⟨e x, h⟩ = (x : UniformSpace.Completion G))
    (z : K) (hz : z ∈ closure (e '' A)) (hz' : z ∈ closure (e '' B)) :
    ψA ⟨z, hz⟩ = ψB ⟨z, hz'⟩ := by
  have hsub : closure (e '' A) ⊆ closure (e '' B) := closure_mono (image_mono hAB)
  let j : closure (e '' A) → closure (e '' B) := Set.inclusion hsub
  have hj : Continuous j := continuous_inclusion hsub
  have hd := denseRange_inclusion_closure (e '' A)
  have heq : ψA = ψB ∘ j := by
    refine hd.equalizer hA (hB.comp hj) ?_
    funext y
    obtain ⟨_, x, hx, rfl⟩ := y
    simp only [Function.comp_apply]
    have h1 := hAv x hx (subset_closure ⟨x, hx, rfl⟩)
    have h2 := hBv x (hAB hx) (subset_closure ⟨x, hAB hx, rfl⟩)
    simp [j, Set.inclusion, h1, h2]
  have := congrFun heq ⟨z, hz⟩
  simpa [j, Set.inclusion] using this

/-- Main abstract statement: every open set of `G` is the preimage of a set of `K` whose trace on every
`closure (e '' A k)` is open there (a set open in the direct limit topology of the union). -/
theorem trace_open (e : G →+ K) (hinj : Function.Injective e) (A : ℕ → Set G)
    (hmono : Monotone A) (hexh : ∀ x : G, ∃ k, x ∈ A k)
    (huc : ∀ k, ∀ U ∈ 𝓝 (0 : G), ∃ W ∈ 𝓝 (0 : K),
      ∀ x ∈ A k, ∀ y ∈ A k, e x - e y ∈ W → x - y ∈ U)
    {V : Set G} (hV : IsOpen V) :
    ∃ W : Set K, (∀ k, ∃ O : Set K, IsOpen O ∧
        W ∩ closure (e '' A k) = O ∩ closure (e '' A k)) ∧ e ⁻¹' W = V := by
  choose ψ hψc hψv using fun k => exists_extension e hinj (A k) (huc k)
  have compat : ∀ k m, k ≤ m → ∀ (z : K) (hz : z ∈ closure (e '' A k))
      (hz' : z ∈ closure (e '' A m)), ψ k ⟨z, hz⟩ = ψ m ⟨z, hz'⟩ :=
    fun k m hkm z hz hz' =>
      extension_compat e (hmono hkm) (hψc k) (hψv k) (hψc m) (hψv m) z hz hz'
  obtain ⟨t, ht, hVt⟩ := (UniformSpace.Completion.isDenseInducing_coe (α := G)).isInducing.isOpen_iff.1 hV
  refine ⟨{z | ∃ k, ∃ h : z ∈ closure (e '' A k), ψ k ⟨z, h⟩ ∈ t}, ?_, ?_⟩
  · intro m
    have hP : IsOpen (ψ m ⁻¹' t) := ht.preimage (hψc m)
    obtain ⟨O, hO, hOP⟩ := isOpen_induced_iff.1 hP
    refine ⟨O, hO, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨k, h, hk⟩, hzE⟩
      refine ⟨?_, hzE⟩
      have hzP : (⟨z, hzE⟩ : closure (e '' A m)) ∈ ψ m ⁻¹' t := by
        rcases le_total k m with hkm | hmk
        · rw [mem_preimage, ← compat k m hkm z h hzE]; exact hk
        · rw [mem_preimage, compat m k hmk z hzE h]; exact hk
      rw [← hOP] at hzP
      exact hzP
    · rintro ⟨hzO, hzE⟩
      refine ⟨⟨m, hzE, ?_⟩, hzE⟩
      have : (⟨z, hzE⟩ : closure (e '' A m)) ∈ Subtype.val ⁻¹' O := hzO
      rw [hOP] at this
      exact this
  · rw [← hVt]
    ext x
    constructor
    · rintro ⟨k, h, hk⟩
      obtain ⟨k', hk'⟩ := hexh x
      have hn : e x ∈ closure (e '' A (max k k')) := subset_closure ⟨x, hmono (le_max_right k k') hk', rfl⟩
      have h1 := compat k (max k k') (le_max_left k k') (e x) h hn
      have h2 := hψv (max k k') x (hmono (le_max_right k k') hk') hn
      rw [mem_preimage]
      rw [h1, h2] at hk
      exact hk
    · intro hx
      obtain ⟨k, hk⟩ := hexh x
      have h : e x ∈ closure (e '' A k) := subset_closure ⟨x, hk, rfl⟩
      refine ⟨k, h, ?_⟩
      rw [hψv k x hk h]
      exact hx

end completion

section contains

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H]

/-- Let `N x` be the neighbourhood filters of a second topology on `H` (given abstractly, to avoid a clash of
instances) that contains the convergence `ξ_{β,I}` (every filter converging for `ξ` converges, `F ≤ N x`). Then for
`A ∈ I` the inclusion of `A` with the trace of `β` into the second topology is continuous at every point: every
`U ∈ N x` contains `W ∩ A` for some `β`-neighbourhood `W` of `x`. -/
theorem trace_cont_of_contains {I : Set (Set H)} (hI : AdmIdeal I) (N : H → Filter H)
    (hσ : ∀ (F : Filter H) (x : H), xi I F x → F ≤ N x)
    {A : Set H} (hA : A ∈ I) (x : H) {U : Set H} (hU : U ∈ N x) :
    ∃ W ∈ 𝓝 x, ∀ y ∈ A, y ∈ W → y ∈ U := by
  by_contra hcon
  push_neg at hcon
  have hne : (𝓝 x ⊓ 𝓟 (A \ U)).NeBot := by
    rw [inf_principal_neBot_iff]
    intro W hW
    obtain ⟨y, hyA, hyW, hyU⟩ := hcon W hW
    exact ⟨y, hyW, hyA, hyU⟩
  have hxi : xi I (𝓝 x ⊓ 𝓟 (A \ U)) x :=
    ⟨hne, inf_le_left, A \ U, hI.sub A hA _ Set.sdiff_subset,mem_inf_of_right (mem_principal_self _)⟩
  have h1 : U ∈ 𝓝 x ⊓ 𝓟 (A \ U) := hσ _ x hxi hU
  have h2 : A \ U ∈ 𝓝 x ⊓ 𝓟 (A \ U) := mem_inf_of_right (mem_principal_self _)
  have h3 : (∅ : Set H) ∈ 𝓝 x ⊓ 𝓟 (A \ U) := by
    have := inter_mem h1 h2
    have e : U ∩ (A \ U) = ∅ := by ext y; simp +contextual
    rwa [e] at this
  exact hne.ne (empty_mem_iff_bot.1 h3)

end contains

end PG
