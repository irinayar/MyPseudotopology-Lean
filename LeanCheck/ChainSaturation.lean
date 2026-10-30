import LeanCheck.ChainTransferQ

/-!
# Rational scalar saturation (Theorem `saturation` of TVGQ-v7)

Let `G` be a `ℚ`-vector space and `H` a set of characters of `G` invariant under rational rescaling of arguments.
For a group topology `η` on `G` let `η_n` be the pullback of `η` under `x ↦ x/n!`, and `η^[ℚ] = ⋁ η_n`
(Mathlib: `⨅ n, η_n`, since `⊓` is the join of topologies).  We prove:

* `η = η₀ ⊆ η₁ ⊆ η₂ ⊆ …` (in Mathlib's order `η_{n+1} ≤ η_n`), and `η ⊆ η^[ℚ]`;
* `η^[ℚ]` is a group topology; Hausdorff and locally quasi-convex when `η` is; every rational dilation is
  continuous; its continuous characters are exactly `H` when those of `η` are;
* `η^[ℚ]` is the least rational-scalar-continuous group topology containing `η`;
* consequently `𝒞_ℚ(H)` has a greatest member iff `ℒ(H)` does, and maximal members of `ℒ(H)` are rational-scalar
  continuous (Corollary `mackey-equivalence`).
-/

namespace LeanCheck

open Filter Topology

section Saturation

variable {G : Type*} [AddCommGroup G] [Module ℚ G]

/-- Multiplication by the rational `q`. -/
def mq (q : ℚ) : G →+ G where
  toFun x := q • x
  map_zero' := smul_zero q
  map_add' x y := smul_add q x y

lemma mq_apply (q : ℚ) (x : G) : mq q x = q • x := rfl

/-- `η_n`: the pullback of `η` under `x ↦ x / n!`. -/
def satn (η : TopologicalSpace G) (n : ℕ) : TopologicalSpace G :=
  TopologicalSpace.induced (mq (1 / (n.factorial : ℚ)) : G → G) η

/-- `η^[ℚ] = ⋁_n η_n`. -/
def sat (η : TopologicalSpace G) : TopologicalSpace G := ⨅ n : ℕ, satn η n

lemma satn_zero (η : TopologicalSpace G) : satn η 0 = η := by
  have : (mq (1 / ((0 : ℕ).factorial : ℚ)) : G → G) = id := by
    funext x; simp [mq_apply]
  unfold satn; rw [this, induced_id]

lemma mq_cont (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (m : ℕ) :
    Continuous[η, η] (mq (m : ℚ) : G → G) := by
  letI := η
  haveI := hη
  have : (mq (m : ℚ) : G → G) = fun x => m • x := by
    funext x; simp [mq_apply, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact continuous_nsmul m

/-- `η_{n+1} ≤ η_n` (i.e. `η_n ⊆ η_{n+1}` as families of open sets). -/
lemma satn_succ_le (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (n : ℕ) :
    satn η (n + 1) ≤ satn η n := by
  have hcomp : (mq (1 / (n.factorial : ℚ)) : G → G) =
      (mq ((n + 1 : ℕ) : ℚ) : G → G) ∘ (mq (1 / ((n + 1).factorial : ℚ)) : G → G) := by
    funext x
    simp only [Function.comp, mq_apply, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have h1 : η ≤ TopologicalSpace.induced (mq ((n + 1 : ℕ) : ℚ) : G → G) η :=
    continuous_iff_le_induced.mp (mq_cont η hη (n + 1))
  unfold satn
  rw [hcomp, ← induced_compose]
  exact induced_mono h1

lemma satn_anti (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) :
    Antitone (satn η) := antitone_nat_of_succ_le (satn_succ_le η hη)

lemma sat_le_satn (η : TopologicalSpace G) (n : ℕ) : sat η ≤ satn η n := iInf_le _ n

/-- `η ⊆ η^[ℚ]`. -/
lemma sat_le (η : TopologicalSpace G) : sat η ≤ η := by
  have := sat_le_satn η 0
  rwa [satn_zero] at this

lemma satn_group (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (n : ℕ) :
    @IsTopologicalAddGroup G (satn η n) _ := by
  letI := η
  haveI := hη
  exact isTopologicalAddGroup_induced _

lemma sat_group (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) :
    @IsTopologicalAddGroup G (sat η) _ := by
  unfold sat
  exact isTopologicalAddGroup_iInf (fun n => satn_group η hη n)

lemma sat_t2 (η : TopologicalSpace G) (h : @T2Space G η) : @T2Space G (sat η) := by
  have hc : Continuous[sat η, η] (id : G → G) :=
    continuous_iff_le_induced.mpr (by rw [induced_id]; exact sat_le η)
  exact @T2Space.of_injective_continuous G G (sat η) η h id Function.injective_id hc

lemma sat_lqc (η : TopologicalSpace G) (h : LocQC η) : LocQC (sat η) :=
  lqc_iInf _ (fun n => lqc_induced _ _ h)

/-- Every rational dilation is `η^[ℚ]`-continuous. -/
theorem sat_rat_cont (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (q : ℚ) :
    Continuous[sat η, sat η] (mq q : G → G) := by
  unfold sat
  refine continuous_iInf_rng.2 (fun n => ?_)
  unfold satn
  rw [continuous_induced_rng]
  -- choose `k` with `n! * den ∣ k!`
  obtain ⟨t, ht⟩ : (n.factorial * q.den) ∣ (n.factorial * q.den).factorial :=
    Nat.dvd_factorial (Nat.mul_pos (Nat.factorial_pos n) q.den_pos) le_rfl
  set k := n.factorial * q.den with hk
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      have := Nat.factorial_pos k
      rw [ht, h0] at this
      simp at this
    · exact h0
  have hfun : ((mq (1 / (n.factorial : ℚ)) : G → G) ∘ (mq q : G → G)) =
      fun x => ((q.num * t : ℤ)) • (mq (1 / (k.factorial : ℚ)) : G → G) x := by
    funext x
    simp only [Function.comp, mq_apply]
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 1
    have hk0 : (k.factorial : ℚ) = n.factorial * q.den * t := by
      rw [ht, hk]; push_cast; ring
    rw [hk0]
    have hn0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    have hq : q = q.num / q.den := (Rat.num_div_den q).symm
    conv_lhs => rw [hq]
    push_cast
    field_simp
  rw [hfun]
  have hc : Continuous[sat η, η] (mq (1 / (k.factorial : ℚ)) : G → G) :=
    continuous_le_dom (sat_le_satn η k) continuous_induced_dom
  have hz : Continuous[η, η] (fun y : G => ((q.num * t : ℤ)) • y) := by
    letI := η
    haveI := hη
    exact continuous_zsmul _
  exact @Continuous.comp G G G (sat η) η η _ _ hz hc

/-- **Leastness**: `η^[ℚ]` is the least rational-scalar-continuous group topology containing `η`
(every such `τ` with `τ ≤ η`, i.e. `η ⊆ τ`, satisfies `τ ≤ η^[ℚ]`). -/
theorem sat_least (η τ : TopologicalSpace G) (hτ : ∀ q : ℚ, Continuous[τ, τ] (mq q : G → G))
    (hle : τ ≤ η) : τ ≤ sat η := by
  refine le_iInf (fun n => ?_)
  unfold satn
  rw [← continuous_iff_le_induced]
  have hid : Continuous[τ, η] (id : G → G) :=
    continuous_iff_le_induced.mpr (by rw [@induced_id G η]; exact hle)
  have h := @Continuous.comp G G G τ τ η (mq (1 / (n.factorial : ℚ)) : G → G) (id : G → G) hid (hτ _)
  exact h

variable (H : Set (G →+ Circ))

/-- Rational invariance of the character set. -/
def RatInv : Prop := ∀ χ ∈ H, ∀ q : ℚ, χ.comp (mq q) ∈ H

lemma comp_mq_inv (χ : G →+ Circ) (q : ℚ) (hq : q ≠ 0) : (χ.comp (mq q)).comp (mq (1 / q)) = χ := by
  ext x
  simp [mq_apply, smul_smul, hq]

/-- Each `η_n` has the same dual `H`. -/
theorem satn_dual (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (hH : RatInv H)
    (hdual : ∀ χ : G →+ Circ, @Continuous G Circ η circTop χ ↔ χ ∈ H) (n : ℕ) (χ : G →+ Circ) :
    @Continuous G Circ (satn η n) circTop χ ↔ χ ∈ H := by
  have hN : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hid : (χ.comp (mq (n.factorial : ℚ))).comp (mq (1 / (n.factorial : ℚ))) = χ :=
    comp_mq_inv χ _ hN
  have hdom : Continuous[satn η n, η] (mq (1 / (n.factorial : ℚ)) : G → G) := continuous_induced_dom
  have hup : Continuous[η, satn η n] (mq (n.factorial : ℚ) : G → G) := by
    unfold satn
    rw [continuous_induced_rng]
    have : ((mq (1 / (n.factorial : ℚ)) : G → G) ∘ (mq (n.factorial : ℚ) : G → G)) = id := by
      funext x; simp [mq_apply, smul_smul, hN]
    rw [this]
    exact @continuous_id G η
  constructor
  · intro h
    have h1 : @Continuous G Circ η circTop (χ.comp (mq (n.factorial : ℚ))) :=
      by
        have := @Continuous.comp G G Circ η (satn η n) circTop (mq (n.factorial : ℚ) : G → G)
          (χ : G → Circ) h hup
        exact this
    have h2 := (hdual _).mp h1
    rw [← hid]
    exact hH _ h2 _
  · intro h
    have h1 := hH χ h (n.factorial : ℚ)
    have h2 : @Continuous G Circ η circTop (χ.comp (mq (n.factorial : ℚ))) := (hdual _).mpr h1
    rw [← hid]
    have := @Continuous.comp G G Circ (satn η n) η circTop (mq (1 / (n.factorial : ℚ)) : G → G) (χ.comp (mq (n.factorial : ℚ)) : G → Circ) h2 hdom
    exact this

/-- The dual of `η^[ℚ]` is exactly `H`. -/
theorem sat_dual (η : TopologicalSpace G) (hη : @IsTopologicalAddGroup G η _) (hH : RatInv H)
    (hdual : ∀ χ : G →+ Circ, @Continuous G Circ η circTop χ ↔ χ ∈ H) (χ : G →+ Circ) :
    @Continuous G Circ (sat η) circTop χ ↔ χ ∈ H := by
  constructor
  · intro hχ
    have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
      rw [map_zero]
      exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds G (sat η) 0 :=
      (@Continuous.continuousAt G Circ (sat η) circTop χ 0 hχ) hS
    unfold sat at hpre
    rw [nhds_iInf] at hpre
    obtain ⟨I, hI, V, hV, -, hs⟩ := Filter.mem_iInf'.mp hpre
    obtain ⟨M, hM⟩ := hI.bddAbove
    have hVM : ∀ n ∈ I, V n ∈ @nhds G (satn η M) 0 := fun n hn =>
      (nhds_mono (satn_anti η hη (hM hn))) (hV n)
    have hW : (⋂ n ∈ I, V n) ∈ @nhds G (satn η M) 0 := (Filter.biInter_mem hI).2 hVM
    have hsmall : ∀ x ∈ (⋂ n ∈ I, V n), ‖χ x‖ < 1 / 4 := by
      intro x hx
      have : x ∈ χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} := by rw [hs.1]; exact hx
      exact this
    have hcont : @Continuous G Circ (satn η M) circTop χ := by
      letI : TopologicalSpace G := satn η M
      haveI : IsTopologicalAddGroup G := satn_group η hη M
      exact continuous_of_quarter_gen χ hW hsmall
    exact (satn_dual H η hη hH hdual M χ).mp hcont
  · intro h
    exact continuous_le_dom (sat_le η) ((hdual χ).mpr h)

/-- Classes `ℒ(H)`: Hausdorff locally quasi-convex group topologies with full character set `H`. -/
def Lcls : Set (TopologicalSpace G) :=
  {τ | @IsTopologicalAddGroup G τ _ ∧ @T2Space G τ ∧ LocQC τ ∧
    ∀ χ : G →+ Circ, @Continuous G Circ τ circTop χ ↔ χ ∈ H}

/-- Classes `𝒞_ℚ(H)`: the members of `ℒ(H)` with all rational dilations continuous. -/
def Ccls : Set (TopologicalSpace G) :=
  {τ | τ ∈ Lcls H ∧ ∀ q : ℚ, Continuous[τ, τ] (mq q : G → G)}

/-- **Rational scalar saturation theorem.**  For `η ∈ ℒ(H)` with `H` rationally invariant:
`η^[ℚ] ∈ 𝒞_ℚ(H)`, `η ⊆ η^[ℚ]`, and `η^[ℚ]` is the least rational-scalar-continuous group topology containing `η`. -/
theorem saturation (hH : RatInv H) (η : TopologicalSpace G) (hη : η ∈ Lcls H) :
    sat η ∈ Ccls H ∧ sat η ≤ η ∧
      ∀ τ : TopologicalSpace G, @IsTopologicalAddGroup G τ _ → (∀ q : ℚ, Continuous[τ, τ] (mq q : G → G)) →
        τ ≤ η → τ ≤ sat η := by
  obtain ⟨hg, ht2, hl, hd⟩ := hη
  refine ⟨⟨⟨sat_group η hg, sat_t2 η ht2, sat_lqc η hl, sat_dual H η hg hH hd⟩, sat_rat_cont η hg⟩,
    sat_le η, fun τ _ hτ hle => sat_least η τ hτ hle⟩

/-- **Corollary (equivalence with the unrestricted Mackey question).**  `𝒞_ℚ(H)` has a greatest member iff
`ℒ(H)` does, and then the two coincide; every maximal member of `ℒ(H)` already lies in `𝒞_ℚ(H)`. -/
theorem mackey_equivalence (hH : RatInv H) :
    (∀ μ : TopologicalSpace G, (μ ∈ Ccls H ∧ ∀ τ ∈ Ccls H, μ ≤ τ) ↔ (μ ∈ Lcls H ∧ ∀ τ ∈ Lcls H, μ ≤ τ)) ∧
    (∀ τ : TopologicalSpace G, τ ∈ Lcls H → (∀ τ' ∈ Lcls H, τ' ≤ τ → τ ≤ τ') → τ ∈ Ccls H) := by
  constructor
  · intro μ
    constructor
    · rintro ⟨hμ, hgr⟩
      refine ⟨hμ.1, fun η hη => ?_⟩
      obtain ⟨hs, hle, -⟩ := saturation H hH η hη
      exact (hgr _ hs).trans hle
    · rintro ⟨hμ, hgr⟩
      obtain ⟨hs, hle, -⟩ := saturation H hH μ hμ
      have h1 : μ ≤ sat μ := hgr _ hs.1
      have h2 : μ = sat μ := le_antisymm h1 hle
      have hμC : μ ∈ Ccls H := by rw [h2]; exact hs
      exact ⟨hμC, fun τ hτ => hgr τ hτ.1⟩
  · intro τ hτ hmax
    obtain ⟨hs, hle, -⟩ := saturation H hH τ hτ
    have h1 : τ ≤ sat τ := hmax _ hs.1 hle
    have h2 : τ = sat τ := le_antisymm h1 hle
    rw [h2]; exact hs

end Saturation

/-! ### Application to the dual pair `(ℝ, H_{f,ℚ})` -/

/-- `H_{f,ℚ} = { x ↦ p(c x + r f(x)) }`. -/
def Hq (f : ℝ →+ ℚ) : Set (ℝ →+ Circ) :=
  {χ | ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x}

lemma mq_real (q : ℚ) : (mq q : ℝ → ℝ) = fun x => (q : ℝ) * x := by
  funext x; simp [mq_apply, Rat.smul_def]

/-- `H_{f,ℚ}` is invariant under rational rescaling of arguments. -/
theorem Hq_ratInv (f : ℝ →+ ℚ) : RatInv (Hq f) := by
  rintro χ ⟨c, r, h⟩ q
  refine ⟨c * q, r * q, fun x => ?_⟩
  have h1 : (χ.comp (mq q)) x = χ ((q : ℝ) * x) := by
    show χ (mq q x) = _
    rw [show mq q x = (q : ℝ) * x from congrFun (mq_real q) x]
  rw [h1, h ((q : ℝ) * x)]
  unfold chiH
  have e1 : f ((r : ℝ) * ((q : ℝ) * x)) = r * q * f x := by
    rw [← mul_assoc, ← Rat.cast_mul, f_ratmul]
  have e2 : f (((r * q : ℚ) : ℝ) * x) = r * q * f x := f_ratmul f (r * q) x
  rw [e1, e2]
  congr 1
  push_cast; ring

/-- **No Mackey topology for `(ℝ, H_{f,ℚ})`.**  Neither `ℒ(H_{f,ℚ})` nor `𝒞_ℚ(H_{f,ℚ})` has a greatest member:
two members of the class have a join with an extra continuous character. -/
theorem no_greatest_compatible_Q (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    (¬ ∃ μ : TopologicalSpace ℝ, μ ∈ Lcls (Hq f) ∧ ∀ τ ∈ Lcls (Hq f), μ ≤ τ) ∧
    (¬ ∃ μ : TopologicalSpace ℝ, μ ∈ Ccls (Hq f) ∧ ∀ τ ∈ Ccls (Hq f), μ ≤ τ) := by
  obtain ⟨T₁, T₂, hg1, hg2, ht1, ht2, hl1, hl2, -, -, hs1, hs2, hd1, hd2, φ, hφ, hφne⟩ :=
    transfer_capstone_Q f u hu
  have hL1 : T₁ ∈ Lcls (Hq f) := ⟨hg1, ht1, hl1, hd1⟩
  have hL2 : T₂ ∈ Lcls (Hq f) := ⟨hg2, ht2, hl2, hd2⟩
  have hC1 : T₁ ∈ Ccls (Hq f) := ⟨hL1, fun q => by rw [mq_real]; exact hs1 q⟩
  have hC2 : T₂ ∈ Ccls (Hq f) := ⟨hL2, fun q => by rw [mq_real]; exact hs2 q⟩
  have first : ¬ ∃ μ : TopologicalSpace ℝ, μ ∈ Lcls (Hq f) ∧ ∀ τ ∈ Lcls (Hq f), μ ≤ τ := by
    rintro ⟨μ, hμ, hgr⟩
    have hle : μ ≤ T₁ ⊓ T₂ := le_inf (hgr _ hL1) (hgr _ hL2)
    have hcont : @Continuous ℝ Circ μ circTop φ := continuous_le_dom hle hφ
    exact hφne ((hμ.2.2.2 φ).mp hcont)
  refine ⟨first, ?_⟩
  rintro ⟨μ, hμ, hgr⟩
  exact first ⟨μ, ((mackey_equivalence (Hq f) (Hq_ratInv f)).1 μ).mp ⟨hμ, hgr⟩⟩

end LeanCheck
