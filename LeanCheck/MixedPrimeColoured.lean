import LeanCheck.MixedPrimeBasics
import LeanCheck.MixedPrimeRadii

/-!
# TVGaddmore_v17: coloured difference sets (Proposition "coloured")

For scale sets `S2, S3` (the two chains), `S = S2 ∪ S3`, and `p > 0`:
`U ε = {k | Pn S2 k < ε}`, `V ε = {k | Pn S3 k < ε}`, `D ε = (U ε - U ε) ∩ (V ε - V ε)`.
* `B ε ⊆ D ε ⊆ B (2 ε)`;
* `D ε ⊆ pℤ` iff the sets `T ε r = {u - v | u ∈ U ε, v ∈ V ε, u ≡ r}` are pairwise disjoint;
* `pℤ` is `P`-open (contains a ball of `Pn S`) iff these sets are pairwise disjoint for some `ε > 0`.
-/

namespace LeanCheck
namespace MixedPrime

lemma Pn_zero (S : Set ℕ) : Pn S 0 = 0 := by
  unfold Pn
  simp [nrm]

lemma Pn_neg (S : Set ℕ) (k : ℤ) : Pn S (-k) = Pn S k := by
  unfold Pn
  congr 1; ext q
  have : (((-k : ℤ) : ℝ) / q) = -((k : ℝ) / q) := by push_cast; ring
  rw [this, nrm_neg]

lemma Pn_add_le {S : Set ℕ} (hS : S.Nonempty) (k l : ℤ) : Pn S (k + l) ≤ Pn S k + Pn S l := by
  apply Pn_le hS
  intro q hq
  have : (((k + l : ℤ) : ℝ) / q) = (k : ℝ) / q + (l : ℝ) / q := by push_cast; ring
  rw [this]
  exact (nrm_add_le _ _).trans (add_le_add (le_Pn hq k) (le_Pn hq l))

lemma Pn_sub_le {S : Set ℕ} (hS : S.Nonempty) (k l : ℤ) : Pn S (k - l) ≤ Pn S k + Pn S l := by
  have := Pn_add_le hS k (-l)
  rwa [Pn_neg, ← sub_eq_add_neg] at this

lemma Pn_union_le {S2 S3 : Set ℕ} (h : (S2 ∪ S3).Nonempty) (k : ℤ) :
    Pn (S2 ∪ S3) k ≤ max (Pn S2 k) (Pn S3 k) := by
  apply Pn_le h
  intro q hq
  rcases hq with hq | hq
  · exact (le_Pn hq k).trans (le_max_left _ _)
  · exact (le_Pn hq k).trans (le_max_right _ _)

section coloured
variable (S2 S3 : Set ℕ)

/-- The one-prime balls. -/
def Uset (ε : ℝ) : Set ℤ := {k | Pn S2 k < ε}
def Vset (ε : ℝ) : Set ℤ := {k | Pn S3 k < ε}
/-- The mixed ball. -/
def Bset (ε : ℝ) : Set ℤ := {k | Pn (S2 ∪ S3) k < ε}
/-- Coloured difference set `D ε = (U-U) ∩ (V-V)`. -/
def Dset (ε : ℝ) : Set ℤ :=
  {g | (∃ u ∈ Uset S2 ε, ∃ u' ∈ Uset S2 ε, g = u - u') ∧ (∃ v ∈ Vset S3 ε, ∃ v' ∈ Vset S3 ε, g = v - v')}
/-- `T ε r p = {u - v : u ∈ U ε, v ∈ V ε, u ≡ r (mod p)}`. -/
def Tset (p : ℕ) (ε : ℝ) (r : ℤ) : Set ℤ :=
  {t | ∃ u ∈ Uset S2 ε, ∃ v ∈ Vset S3 ε, u % (p : ℤ) = r ∧ t = u - v}

variable {S2 S3}

lemma B_subset_D (hS2 : S2 ⊆ S2 ∪ S3) {ε : ℝ} (hε : 0 < ε) :
    Bset S2 S3 ε ⊆ Dset S2 S3 ε := by
  intro k hk
  have h2 : Pn S2 k < ε := lt_of_le_of_lt (Pn_mono Set.subset_union_left k) hk
  have h3 : Pn S3 k < ε := lt_of_le_of_lt (Pn_mono Set.subset_union_right k) hk
  have z2 : (0 : ℤ) ∈ Uset S2 ε := by simp [Uset, Pn_zero, hε]
  have z3 : (0 : ℤ) ∈ Vset S3 ε := by simp [Vset, Pn_zero, hε]
  exact ⟨⟨k, h2, 0, z2, by ring⟩, ⟨k, h3, 0, z3, by ring⟩⟩

lemma D_subset_B2 (h2 : S2.Nonempty) (h3 : S3.Nonempty) (ε : ℝ) :
    Dset S2 S3 ε ⊆ Bset S2 S3 (2 * ε) := by
  rintro g ⟨⟨u, hu, u', hu', rfl⟩, ⟨v, hv, v', hv', hg⟩⟩
  have hn : (S2 ∪ S3).Nonempty := h2.mono Set.subset_union_left
  have a2 : Pn S2 (u - u') < 2 * ε := by
    have := Pn_sub_le h2 u u'
    simp only [Uset, Set.mem_setOf_eq] at hu hu'
    linarith
  have a3 : Pn S3 (u - u') < 2 * ε := by
    rw [hg]
    have := Pn_sub_le h3 v v'
    simp only [Vset, Set.mem_setOf_eq] at hv hv'
    linarith
  show Pn (S2 ∪ S3) (u - u') < 2 * ε
  exact lt_of_le_of_lt (Pn_union_le hn _) (max_lt a2 a3)

theorem D_subset_iff_disjoint {p : ℕ} (hp : 0 < p) (ε : ℝ) :
    (∀ g ∈ Dset S2 S3 ε, (p : ℤ) ∣ g) ↔
      ∀ r r' : ℤ, r ≠ r' → Disjoint (Tset S2 S3 p ε r) (Tset S2 S3 p ε r') := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro hD r r' hrr'
    rw [Set.disjoint_left]
    rintro t ⟨u, hu, v, hv, hur, rfl⟩ ⟨u', hu', v', hv', hur', hEq⟩
    apply hrr'
    have hg : u - u' = v - v' := by linarith
    have hmem : u - u' ∈ Dset S2 S3 ε := ⟨⟨u, hu, u', hu', rfl⟩, ⟨v, hv, v', hv', hg⟩⟩
    have := hD _ hmem
    rw [← hur, ← hur']
    exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp this)
  · intro hdisj g ⟨⟨u, hu, u', hu', hg1⟩, ⟨v, hv, v', hv', hg2⟩⟩
    by_contra hnd
    have hne : u % (p : ℤ) ≠ u' % (p : ℤ) := by
      intro h
      apply hnd
      rw [hg1]
      exact dvd_sub_comm.mp (Int.modEq_iff_dvd.mp h)
    have hmem1 : u - v ∈ Tset S2 S3 p ε (u % p) := ⟨u, hu, v, hv, rfl, rfl⟩
    have hmem2 : u - v ∈ Tset S2 S3 p ε (u' % p) := ⟨u', hu', v', hv', rfl, by linarith⟩
    exact Set.disjoint_left.mp (hdisj _ _ hne) hmem1 hmem2

/-- `pℤ` contains a ball of the mixed metric iff the coloured sets are disjoint for some radius. -/
theorem open_iff_disjoint (h2 : S2.Nonempty) (h3 : S3.Nonempty) {p : ℕ} (hp : 0 < p) :
    (∃ ε > 0, ∀ k : ℤ, Pn (S2 ∪ S3) k < ε → (p : ℤ) ∣ k) ↔
      ∃ ε > 0, ∀ r r' : ℤ, r ≠ r' → Disjoint (Tset S2 S3 p ε r) (Tset S2 S3 p ε r') := by
  constructor
  · rintro ⟨ε, hε, hk⟩
    refine ⟨ε / 2, by positivity, ?_⟩
    rw [← D_subset_iff_disjoint hp]
    intro g hg
    have := D_subset_B2 h2 h3 (ε / 2) hg
    have h' : Pn (S2 ∪ S3) g < ε := by
      have : (2 : ℝ) * (ε / 2) = ε := by ring
      simpa [Bset, this] using ‹g ∈ Bset S2 S3 (2 * (ε / 2))›
    exact hk g h'
  · rintro ⟨ε, hε, hd⟩
    refine ⟨ε, hε, fun k hk => ?_⟩
    have := (D_subset_iff_disjoint hp ε).mpr hd
    exact this k (B_subset_D Set.subset_union_left hε hk)

end coloured

end MixedPrime
end LeanCheck
