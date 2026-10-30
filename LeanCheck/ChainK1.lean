import LeanCheck.ChainH1
import LeanCheck.ChainE4

/-!
# Two disjoint rational subspaces with all finite scalar patterns
(HamelCharactersTVG_v18 Lemma 17.4 `lem:patterns`)

There are rational subspaces `E, F ⊂ ℝ` with `E ∩ F = {0}` such that for every finite nonempty `A ⊂ ℝ ∖ {0}` there are nonzero `u, v`
with `A u ⊂ E` and `A v ⊂ F`.  Proof by transfinite recursion along the initial ordinal of the continuum.
-/

namespace LeanCheck

open Cardinal Ordinal Set

section Index

/-- The initial well-order of the continuum. -/
abbrev II : Type := (Cardinal.continuum.ord).ToType

lemma card_II : #II = 𝔠 := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]

lemma ord_II : Cardinal.ord #II = typeLT II := by
  rw [card_II, Ordinal.type_toType]

lemma card_Iio_lt (i : II) : #(Iio i) < 𝔠 := by
  have := Cardinal.mk_Iio_lt i ord_II
  rwa [card_II] at this

/-- An enumeration of all finite subsets of `ℝ` by `II`. -/
noncomputable def enumF : II ≃ Finset ℝ :=
  (Cardinal.eq.1 (by
    rw [card_II, Cardinal.mk_finset_of_infinite, Cardinal.mk_real])).some

end Index

section Cardinality

lemma card_span_le (S : Set ℝ) : #(Submodule.span ℚ S) ≤ max ℵ₀ #S := by
  by_cases hS : S.Nonempty
  · haveI : Nonempty S := hS.to_subtype
    have hsurj : Function.Surjective
        (fun f : S →₀ ℚ => (⟨Finsupp.linearCombination ℚ (fun s : S => (s : ℝ)) f, by
          rw [Finsupp.linearCombination_apply]
          exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span s.2))⟩ :
            Submodule.span ℚ S)) := by
      rintro ⟨x, hx⟩
      have : x ∈ LinearMap.range (Finsupp.linearCombination ℚ (fun s : S => (s : ℝ))) := by
        rw [Finsupp.range_linearCombination]
        simpa [Subtype.range_coe] using hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, Subtype.ext hf⟩
    calc #(Submodule.span ℚ S) ≤ #(S →₀ ℚ) := mk_le_of_surjective hsurj
      _ = max #S ℵ₀ := by
          rw [Cardinal.mk_finsupp_lift_of_infinite' S ℚ]
          simp [mk_eq_aleph0 ℚ]
      _ = max ℵ₀ #S := max_comm _ _
  · have : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hS
    subst this
    simp

lemma card_span_lt {S : Set ℝ} (hS : #S < 𝔠) : #(Submodule.span ℚ S) < 𝔠 := by
  refine lt_of_le_of_lt (card_span_le S) ?_
  exact max_lt (lt_of_lt_of_le Cardinal.aleph0_lt_continuum le_rfl) hS

end Cardinality

section Choice

/-- The rational span of a finite set. -/
noncomputable def VA (A : Finset ℝ) : Submodule ℚ ℝ := Submodule.span ℚ (A : Set ℝ)

lemma VA_countable (A : Finset ℝ) : ((VA A : Submodule ℚ ℝ) : Set ℝ).Countable := by
  haveI : Countable (A : Set ℝ) := A.finite_toSet.countable.to_subtype
  have h1 : Countable (Submodule.span ℚ (Set.range (Subtype.val : ↥(A : Set ℝ) → ℝ))) := inferInstance
  rw [Subtype.range_coe] at h1
  exact Set.countable_coe_iff.1 h1

/-- Multiplication of a subspace by a scalar. -/
noncomputable def mulSub (u : ℝ) (V : Submodule ℚ ℝ) : Submodule ℚ ℝ := V.map (LinearMap.mulLeft ℚ u)

lemma mem_mulSub {u : ℝ} {V : Submodule ℚ ℝ} {x : ℝ} : x ∈ mulSub u V ↔ ∃ w ∈ V, u * w = x := by
  unfold mulSub
  rw [Submodule.mem_map]
  rfl

lemma mulSub_countable (u : ℝ) {V : Submodule ℚ ℝ} (hV : (V : Set ℝ).Countable) :
    ((mulSub u V : Submodule ℚ ℝ) : Set ℝ).Countable := by
  have : ((mulSub u V : Submodule ℚ ℝ) : Set ℝ) ⊆ (fun w => u * w) '' (V : Set ℝ) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_mulSub.1 hx
    exact ⟨w, hw, rfl⟩
  exact (hV.image _).mono this

/-- A scalar `u ≠ 0` with `u V ∩ L = {0}`, when `L` is small and `V` is countable. -/
lemma exists_scalar (L V : Submodule ℚ ℝ) (hL : #L < 𝔠) (hV : (V : Set ℝ).Countable) :
    ∃ u : ℝ, u ≠ 0 ∧ ∀ w ∈ V, w ≠ 0 → u * w ∉ L := by
  by_contra hcon
  push_neg at hcon
  let V' : Type := {w : ℝ // w ∈ V ∧ w ≠ 0}
  haveI : Countable V' := (hV.mono (fun w hw => hw.1)).to_subtype
  let f : V' × L → ℝ := fun p => (p.2 : ℝ) / (p.1 : ℝ)
  have hcover : (Set.univ : Set ℝ) ⊆ insert 0 (Set.range f) := by
    intro u _
    by_cases hu : u = 0
    · exact Or.inl hu
    · obtain ⟨w, hwV, hw0, hwL⟩ := hcon u hu
      right
      refine ⟨(⟨w, hwV, hw0⟩, ⟨u * w, hwL⟩), ?_⟩
      show u * w / w = u
      field_simp
  have h1 : #ℝ ≤ #(↥(insert (0 : ℝ) (Set.range f) : Set ℝ)) := by
    calc #ℝ = #(Set.univ : Set ℝ) := mk_univ.symm
      _ ≤ _ := mk_le_mk_of_subset hcover
  have h2 : #(↥(insert (0 : ℝ) (Set.range f) : Set ℝ)) ≤ #(Set.range f) + 1 := mk_insert_le
  have h3 : #(Set.range f) ≤ #V' * #L := by
    calc #(Set.range f) ≤ #(V' × L) := mk_range_le
      _ = #V' * #L := by rw [mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  have h4 : #V' * #L < 𝔠 := by
    refine mul_lt_of_lt Cardinal.aleph0_le_continuum ?_ hL
    exact lt_of_le_of_lt (Cardinal.mk_le_aleph0) Cardinal.aleph0_lt_continuum
  have h5 : #(Set.range f) + 1 < 𝔠 := by
    refine Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum (lt_of_le_of_lt h3 h4) ?_
    exact lt_of_lt_of_le Cardinal.one_lt_aleph0 Cardinal.aleph0_le_continuum
  have := lt_of_le_of_lt (h1.trans h2) h5
  rw [Cardinal.mk_real] at this
  exact lt_irrefl _ this

lemma card_sup_lt {L W : Submodule ℚ ℝ} (hL : #L < 𝔠) (hW : (W : Set ℝ).Countable) : #(↥(L ⊔ W)) < 𝔠 := by
  haveI : Countable W := hW.to_subtype
  have hsurj : Function.Surjective (fun p : L × W => (⟨(p.1 : ℝ) + p.2, Submodule.add_mem_sup p.1.2 p.2.2⟩ : ↥(L ⊔ W))) := by
    rintro ⟨x, hx⟩
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨l, hl⟩, ⟨w, hw⟩), rfl⟩
  calc #(↥(L ⊔ W)) ≤ #(L × W) := mk_le_of_surjective hsurj
    _ = #L * #W := by rw [mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    _ < 𝔠 := mul_lt_of_lt Cardinal.aleph0_le_continuum hL
          (lt_of_le_of_lt Cardinal.mk_le_aleph0 Cardinal.aleph0_lt_continuum)

/-- The choice property of the pair `(u, v)` at a stage with previously selected space `L`. -/
def Good (L : Submodule ℚ ℝ) (A : Finset ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ (∀ w ∈ VA A, w ≠ 0 → p.1 * w ∉ L) ∧
    (∀ w ∈ VA A, w ≠ 0 → p.2 * w ∉ L ⊔ mulSub p.1 (VA A))

lemma exists_good (L : Submodule ℚ ℝ) (A : Finset ℝ) (hL : #L < 𝔠) : ∃ p, Good L A p := by
  obtain ⟨u, hu0, hu⟩ := exists_scalar L (VA A) hL (VA_countable A)
  have hW := mulSub_countable u (VA_countable A)
  obtain ⟨v, hv0, hv⟩ := exists_scalar (L ⊔ mulSub u (VA A)) (VA A) (card_sup_lt hL hW) (VA_countable A)
  exact ⟨(u, v), hu0, hv0, hu, hv⟩

open Classical in
/-- The choice function of the recursion. -/
noncomputable def pick (L : Submodule ℚ ℝ) (A : Finset ℝ) : ℝ × ℝ :=
  if h : ∃ p, Good L A p then h.choose else (0, 0)

lemma pick_good (L : Submodule ℚ ℝ) (A : Finset ℝ) (hL : #L < 𝔠) : Good L A (pick L A) := by
  have h := exists_good L A hL
  unfold pick
  rw [dif_pos h]
  exact h.choose_spec

end Choice

section Recursion

/-- The transfinite sequence of pairs `(u_α, v_α)`. -/
noncomputable def gS : II → ℝ × ℝ :=
  WellFounded.fix (r := (· < ·)) wellFounded_lt (fun α rec =>
    pick ((⨆ β : Iio α, mulSub (rec β.1 β.2).1 (VA (enumF β.1))) ⊔
      (⨆ β : Iio α, mulSub (rec β.1 β.2).2 (VA (enumF β.1)))) (enumF α))

noncomputable def Ec (β : II) : Submodule ℚ ℝ := mulSub (gS β).1 (VA (enumF β))
noncomputable def Fc (β : II) : Submodule ℚ ℝ := mulSub (gS β).2 (VA (enumF β))
noncomputable def Eb (α : II) : Submodule ℚ ℝ := ⨆ β : Iio α, Ec β.1
noncomputable def Fb (α : II) : Submodule ℚ ℝ := ⨆ β : Iio α, Fc β.1

lemma gS_eq (α : II) : gS α = pick (Eb α ⊔ Fb α) (enumF α) := by
  unfold gS
  rw [WellFounded.fix_eq]
  rfl

lemma Ec_countable (β : II) : ((Ec β : Submodule ℚ ℝ) : Set ℝ).Countable :=
  mulSub_countable _ (VA_countable _)

lemma Fc_countable (β : II) : ((Fc β : Submodule ℚ ℝ) : Set ℝ).Countable :=
  mulSub_countable _ (VA_countable _)

lemma card_EbFb (α : II) : #(↥(Eb α ⊔ Fb α)) < 𝔠 := by
  let S : Set ℝ := ⋃ β : Iio α, (((Ec β.1 : Submodule ℚ ℝ) : Set ℝ) ∪ ((Fc β.1 : Submodule ℚ ℝ) : Set ℝ))
  have hle : Eb α ⊔ Fb α ≤ Submodule.span ℚ S := by
    refine sup_le (iSup_le fun β => ?_) (iSup_le fun β => ?_)
    · intro x hx
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨β, Or.inl hx⟩)
    · intro x hx
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨β, Or.inr hx⟩)
  have hS : #S < 𝔠 := by
    calc #S ≤ #(Iio α) * ⨆ β : Iio α, #(↥(((Ec β.1 : Submodule ℚ ℝ) : Set ℝ) ∪ ((Fc β.1 : Submodule ℚ ℝ) : Set ℝ))) :=
          mk_iUnion_le _
      _ ≤ #(Iio α) * ℵ₀ := by
          refine mul_le_mul' le_rfl (ciSup_le' fun β => ?_)
          haveI := ((Ec_countable β.1).union (Fc_countable β.1)).to_subtype
          exact Cardinal.mk_le_aleph0
      _ < 𝔠 := mul_lt_of_lt Cardinal.aleph0_le_continuum (card_Iio_lt α) Cardinal.aleph0_lt_continuum
  exact lt_of_le_of_lt (mk_le_mk_of_subset (SetLike.coe_subset_coe.2 hle)) (card_span_lt hS)

lemma gS_good (α : II) : Good (Eb α ⊔ Fb α) (enumF α) (gS α) := by
  rw [gS_eq]
  exact pick_good _ _ (card_EbFb α)

end Recursion

section Disjoint

noncomputable def Ele (α : II) : Submodule ℚ ℝ := ⨆ β : Iic α, Ec β.1
noncomputable def Fle (α : II) : Submodule ℚ ℝ := ⨆ β : Iic α, Fc β.1

lemma Ele_mono {α β : II} (h : α ≤ β) : Ele α ≤ Ele β :=
  iSup_le fun γ => le_iSup (fun δ : Iic β => Ec δ.1) ⟨γ.1, le_trans γ.2 h⟩

lemma Fle_mono {α β : II} (h : α ≤ β) : Fle α ≤ Fle β :=
  iSup_le fun γ => le_iSup (fun δ : Iic β => Fc δ.1) ⟨γ.1, le_trans γ.2 h⟩

lemma Ele_eq (α : II) : Ele α = Eb α ⊔ Ec α := by
  apply le_antisymm
  · refine iSup_le fun β => ?_
    rcases lt_or_eq_of_le (Set.mem_Iic.1 β.2) with h | h
    · exact le_sup_of_le_left (le_iSup (fun γ : Iio α => Ec γ.1) ⟨β.1, h⟩)
    · have : β.1 = α := h
      rw [this]; exact le_sup_right
  · exact sup_le (iSup_le fun β => le_iSup (fun γ : Iic α => Ec γ.1) ⟨β.1, Set.mem_Iic.2 (le_of_lt β.2)⟩)
      (le_iSup (fun γ : Iic α => Ec γ.1) ⟨α, Set.mem_Iic.2 le_rfl⟩)

lemma Fle_eq (α : II) : Fle α = Fb α ⊔ Fc α := by
  apply le_antisymm
  · refine iSup_le fun β => ?_
    rcases lt_or_eq_of_le (Set.mem_Iic.1 β.2) with h | h
    · exact le_sup_of_le_left (le_iSup (fun γ : Iio α => Fc γ.1) ⟨β.1, h⟩)
    · have : β.1 = α := h
      rw [this]; exact le_sup_right
  · exact sup_le (iSup_le fun β => le_iSup (fun γ : Iic α => Fc γ.1) ⟨β.1, Set.mem_Iic.2 (le_of_lt β.2)⟩)
      (le_iSup (fun γ : Iic α => Fc γ.1) ⟨α, Set.mem_Iic.2 le_rfl⟩)

/-- Membership in a supremum over a set of stages: zero, or in `Ele β` for some stage `β` of the set. -/
lemma mem_iSup_Ec (T : Set II) {x : ℝ} (hx : x ∈ ⨆ β : T, Ec β.1) : x = 0 ∨ ∃ β ∈ T, x ∈ Ele β := by
  refine Submodule.iSup_induction (fun β : T => Ec β.1) hx (motive := fun x => x = 0 ∨ ∃ β ∈ T, x ∈ Ele β)
    (fun β y hy => Or.inr ⟨β.1, β.2, le_iSup (fun γ : Iic β.1 => Ec γ.1) ⟨β.1, Set.mem_Iic.2 le_rfl⟩ hy⟩)
    (Or.inl rfl) ?_
  rintro y z (hy | ⟨β1, hβ1, hy⟩) (hz | ⟨β2, hβ2, hz⟩)
  · left; rw [hy, hz, add_zero]
  · right; exact ⟨β2, hβ2, by rw [hy, zero_add]; exact hz⟩
  · right; exact ⟨β1, hβ1, by rw [hz, add_zero]; exact hy⟩
  · right
    rcases le_total β1 β2 with h | h
    · exact ⟨β2, hβ2, Submodule.add_mem _ (Ele_mono h hy) hz⟩
    · exact ⟨β1, hβ1, Submodule.add_mem _ hy (Ele_mono h hz)⟩

lemma mem_iSup_Fc (T : Set II) {x : ℝ} (hx : x ∈ ⨆ β : T, Fc β.1) : x = 0 ∨ ∃ β ∈ T, x ∈ Fle β := by
  refine Submodule.iSup_induction (fun β : T => Fc β.1) hx (motive := fun x => x = 0 ∨ ∃ β ∈ T, x ∈ Fle β)
    (fun β y hy => Or.inr ⟨β.1, β.2, le_iSup (fun γ : Iic β.1 => Fc γ.1) ⟨β.1, Set.mem_Iic.2 le_rfl⟩ hy⟩)
    (Or.inl rfl) ?_
  rintro y z (hy | ⟨β1, hβ1, hy⟩) (hz | ⟨β2, hβ2, hz⟩)
  · left; rw [hy, hz, add_zero]
  · right; exact ⟨β2, hβ2, by rw [hy, zero_add]; exact hz⟩
  · right; exact ⟨β1, hβ1, by rw [hz, add_zero]; exact hy⟩
  · right
    rcases le_total β1 β2 with h | h
    · exact ⟨β2, hβ2, Submodule.add_mem _ (Fle_mono h hy) hz⟩
    · exact ⟨β1, hβ1, Submodule.add_mem _ hy (Fle_mono h hz)⟩

lemma Ele_inf_Fle (α : II) : Ele α ⊓ Fle α = ⊥ := by
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    have hdisj : Eb α ⊓ Fb α = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxE, hxF⟩
      rw [Submodule.mem_bot]
      rcases mem_iSup_Ec (Iio α) hxE with h0 | ⟨β1, hβ1, hE⟩
      · exact h0
      rcases mem_iSup_Fc (Iio α) hxF with h0 | ⟨β2, hβ2, hF⟩
      · exact h0
      rcases le_total β1 β2 with h | h
      · have : x ∈ Ele β2 ⊓ Fle β2 := ⟨Ele_mono h hE, hF⟩
        rw [IH β2 hβ2] at this; exact this
      · have : x ∈ Ele β1 ⊓ Fle β1 := ⟨hE, Fle_mono h hF⟩
        rw [IH β1 hβ1] at this; exact this
    obtain ⟨hu0, hv0, hu, hv⟩ := gS_good α
    have hA : ∀ w ∈ VA (enumF α), w ≠ 0 → (gS α).1 * w ∉ Eb α ⊔ Fb α := hu
    have haL : ∀ a ∈ Ec α, a ∈ Eb α ⊔ Fb α → a = 0 := by
      intro a ha hL
      obtain ⟨w, hw, rfl⟩ := mem_mulSub.1 ha
      by_contra hne
      have hw0 : w ≠ 0 := fun h => hne (by rw [h, mul_zero])
      exact hA w hw hw0 hL
    have hbL : ∀ b ∈ Fc α, b ∈ (Eb α ⊔ Fb α) ⊔ Ec α → b = 0 := by
      intro b hb hL
      obtain ⟨w, hw, rfl⟩ := mem_mulSub.1 hb
      by_contra hne
      have hw0 : w ≠ 0 := fun h => hne (by rw [h, mul_zero])
      exact hv w hw hw0 hL
    rw [Ele_eq, Fle_eq, eq_bot_iff]
    rintro x ⟨hxE, hxF⟩
    rw [Submodule.mem_bot]
    obtain ⟨e, he, a, ha, rfl⟩ := Submodule.mem_sup.1 hxE
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.1 hxF
    have hbmem : b ∈ (Eb α ⊔ Fb α) ⊔ Ec α := by
      have : b = e + a - f := by rw [← hfb]; abel
      rw [this]
      refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left he)
      · exact Submodule.mem_sup_right ha
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right hf)
    have hb0 : b = 0 := hbL b hb hbmem
    rw [hb0, add_zero] at hfb
    have hxFb : e + a ∈ Fb α := by rw [← hfb]; exact hf
    have ha' : a ∈ Eb α ⊔ Fb α := by
      have : a = (e + a) - e := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hxFb) (Submodule.mem_sup_left he)
    have ha0 : a = 0 := haL a ha ha'
    rw [ha0, add_zero] at hxFb ⊢
    have : e ∈ Eb α ⊓ Fb α := ⟨he, hxFb⟩
    rw [hdisj] at this
    exact this

end Disjoint

/-- **Lemma 17.4.**  There are rational subspaces `E, F ⊂ ℝ` with `E ∩ F = {0}` such that for every finite `A ⊂ ℝ` there are
nonzero `u, v` with `a u ∈ E` and `a v ∈ F` for all `a ∈ A`. -/
theorem exists_patterns :
    ∃ E F : Submodule ℚ ℝ, E ⊓ F = ⊥ ∧ ∀ A : Finset ℝ,
      (∃ u : ℝ, u ≠ 0 ∧ ∀ a ∈ A, a * u ∈ E) ∧ (∃ v : ℝ, v ≠ 0 ∧ ∀ a ∈ A, a * v ∈ F) := by
  refine ⟨⨆ β : II, Ec β, ⨆ β : II, Fc β, ?_, fun A => ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxE, hxF⟩
    rw [Submodule.mem_bot]
    have hE : x ∈ ⨆ β : (Set.univ : Set II), Ec β.1 := by
      refine (iSup_le fun β => ?_ : (⨆ β : II, Ec β) ≤ ⨆ β : (Set.univ : Set II), Ec β.1) hxE
      exact le_iSup (fun γ : (Set.univ : Set II) => Ec γ.1) ⟨β, Set.mem_univ β⟩
    have hF : x ∈ ⨆ β : (Set.univ : Set II), Fc β.1 := by
      refine (iSup_le fun β => ?_ : (⨆ β : II, Fc β) ≤ ⨆ β : (Set.univ : Set II), Fc β.1) hxF
      exact le_iSup (fun γ : (Set.univ : Set II) => Fc γ.1) ⟨β, Set.mem_univ β⟩
    rcases mem_iSup_Ec Set.univ hE with h0 | ⟨β1, -, h1⟩
    · exact h0
    rcases mem_iSup_Fc Set.univ hF with h0 | ⟨β2, -, h2⟩
    · exact h0
    rcases le_total β1 β2 with h | h
    · have : x ∈ Ele β2 ⊓ Fle β2 := ⟨Ele_mono h h1, h2⟩
      rw [Ele_inf_Fle] at this; exact this
    · have : x ∈ Ele β1 ⊓ Fle β1 := ⟨h1, Fle_mono h h2⟩
      rw [Ele_inf_Fle] at this; exact this
  · set α := enumF.symm A with hα
    have hA : enumF α = A := by simp [hα]
    obtain ⟨hu0, hv0, -, -⟩ := gS_good α
    refine ⟨⟨(gS α).1, hu0, fun a ha => ?_⟩, ⟨(gS α).2, hv0, fun a ha => ?_⟩⟩
    · have hmem : (gS α).1 * a ∈ Ec α := by
        refine mem_mulSub.2 ⟨a, ?_, rfl⟩
        rw [← hA] at ha
        exact Submodule.subset_span ha
      rw [mul_comm]
      exact le_iSup (fun β : II => Ec β) α hmem
    · have hmem : (gS α).2 * a ∈ Fc α := by
        refine mem_mulSub.2 ⟨a, ?_, rfl⟩
        rw [← hA] at ha
        exact Submodule.subset_span ha
      rw [mul_comm]
      exact le_iSup (fun β : II => Fc β) α hmem

end LeanCheck
