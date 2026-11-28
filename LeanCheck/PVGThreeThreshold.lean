import LeanCheck.PVGThreeShadow
import LeanCheck.PVGThreeCover

/-!
# PVGthree: one construction, rigid or not according to the block size

The construction of `PVGThreeShadow`, keeping only the pairs `(i, n)` with `n % nu i ≠ i % nu i`.
With `nu` constant the sequence is rigid (`rig_const`); with `nu i` the largest power of two below `i` it is
not rigid (`not_rig_grow`). In both cases `dim_H A(δ) = 1`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

namespace Blocks

def r (i : ℕ) : ℕ := 4 ^ (i + 1)

def Mx (i : ℕ) : ℕ := r i * (r i + 1)

/-- A modulus for every index. -/
class Md where
  nu : ℕ → ℕ
  two : ∀ i, 2 ≤ nu i

variable [S0 : Md]

/-- `(n² - M_i)² + i` for `n > r_i` with `n % nu i ≠ i % nu i`. -/
def S : Set ℕ := {c | ∃ i n, r i < n ∧ n % Md.nu i ≠ i % Md.nu i ∧ c = (n ^ 2 - Mx i) ^ 2 + i}

lemma r_gt (i : ℕ) : i + 1 < r i := Nat.lt_pow_self (by norm_num)

lemma r_mono : StrictMono r := fun _ _ h => Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma Mx_mono : StrictMono Mx := fun a b h => by
  have h1 := r_mono h
  exact Nat.mul_lt_mul_of_lt_of_lt h1 (by omega)

lemma D_ge {i n : ℕ} (h : r i < n) : Mx i + r i + 1 ≤ n ^ 2 := by
  have h1 : (r i + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : (r i + 1) ^ 2 = Mx i + r i + 1 := by unfold Mx; ring
  omega

lemma code_sqrt {i n : ℕ} (h : r i < n) :
    Nat.sqrt ((n ^ 2 - Mx i) ^ 2 + i) = n ^ 2 - Mx i := by
  have h1 := D_ge h
  have h2 := r_gt i
  exact Nat.sqrt_add_eq' _ (by omega)

lemma S_infinite : S.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun c => ?_
  have h2 := Md.two 0
  set n := Md.nu 0 * (r 0 + Mx 0 + c + 1) + 1 with hn
  have hbig : r 0 + Mx 0 + c + 1 ≤ n := by
    have : r 0 + Mx 0 + c + 1 ≤ Md.nu 0 * (r 0 + Mx 0 + c + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h : r 0 < n := by omega
  have hk : n % Md.nu 0 ≠ 0 % Md.nu 0 := by
    rw [hn, Nat.mul_add_mod, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < Md.nu 0)]
    exact one_ne_zero
  refine ⟨(n ^ 2 - Mx 0) ^ 2 + 0, ⟨0, n, h, hk, rfl⟩, ?_⟩
  have h1 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  have h3 : n ^ 2 - Mx 0 ≤ (n ^ 2 - Mx 0) ^ 2 := Nat.le_self_pow two_ne_zero _
  omega

noncomputable def e (k : ℕ) : ℕ := Nat.nth (· ∈ S) k

lemma e_mono : StrictMono e := Nat.nth_strictMono S_infinite

lemma e_mem (k : ℕ) : e k ∈ S := Nat.nth_mem_of_infinite S_infinite k

lemma e_surj {c : ℕ} (hc : c ∈ S) : ∃ k, e k = c := by
  classical
  exact ⟨Nat.count (· ∈ S) c, Nat.nth_count hc⟩

noncomputable def D (k : ℕ) : ℕ := Nat.sqrt (e k)

noncomputable def I (k : ℕ) : ℕ := e k - D k ^ 2

noncomputable def nn (k : ℕ) : ℕ := Nat.sqrt (D k + Mx (I k))

lemma spec (k : ℕ) : r (I k) < nn k ∧ nn k ^ 2 = D k + Mx (I k) ∧ e k = D k ^ 2 + I k := by
  obtain ⟨i, n, hn, _, he⟩ := e_mem k
  have hD : D k = n ^ 2 - Mx i := by
    unfold D
    rw [he]
    exact code_sqrt hn
  have hI : I k = i := by
    unfold I
    rw [hD, he]
    omega
  have h1 := D_ge hn
  have h2 : D k + Mx i = n ^ 2 := by omega
  have h3 : nn k = n := by
    unfold nn
    rw [hI, h2, Nat.sqrt_eq']
  refine ⟨by rw [hI, h3]; exact hn, by rw [h3, hI]; omega, by rw [hD, hI, he]⟩

lemma kept (k : ℕ) : nn k % Md.nu (I k) ≠ I k % Md.nu (I k) := by
  obtain ⟨i, n, hn, hk, he⟩ := e_mem k
  have hD : D k = n ^ 2 - Mx i := by
    unfold D
    rw [he]
    exact code_sqrt hn
  have hI : I k = i := by
    unfold I
    rw [hD, he]
    omega
  have h1 := D_ge hn
  have h2 : D k + Mx i = n ^ 2 := by omega
  have h3 : nn k = n := by
    unfold nn
    rw [hI, h2, Nat.sqrt_eq']
  rw [h3, hI]
  exact hk

lemma D_gt (k : ℕ) : r (I k) + 1 ≤ D k := by
  have h := spec k
  have h1 := D_ge h.1
  omega

lemma nn_le (k : ℕ) : nn k ≤ D k + 1 := by
  have h := spec k
  have h1 := D_gt k
  refine (Nat.pow_le_pow_iff_left (n := 2) two_ne_zero).1 ?_
  rw [h.2.1]
  have h2 : Mx (I k) ≤ D k * D k := by
    unfold Mx
    exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : (D k + 1) ^ 2 = D k * D k + 2 * D k + 1 := by ring
  omega

lemma D_mono : Monotone D := fun _ _ h => Nat.sqrt_le_sqrt (e_mono.monotone h)

noncomputable def m : ℕ → ℕ
  | 0 => 8 * D 0 + 16
  | k + 1 => 2 * m k + 8 * D (k + 1) + 2 ^ (k + 1) + 16

lemma m_succ (k : ℕ) : m (k + 1) = 2 * m k + 8 * D (k + 1) + 2 ^ (k + 1) + 16 := by rw [m]

lemma m_zero : m 0 = 8 * D 0 + 16 := by rw [m]

lemma m_ge (k : ℕ) : 8 * D k + 15 ≤ m k := by
  cases k with
  | zero => rw [m_zero]; exact Nat.add_le_add_left (by norm_num) _
  | succ k =>
    rw [m_succ]
    exact Nat.add_le_add (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) (by norm_num)

lemma m_pow (k : ℕ) : 2 ^ k ≤ m k := by
  cases k with
  | zero => rw [m_zero]; exact le_trans (by norm_num) (Nat.le_add_left 16 _)
  | succ k =>
    rw [m_succ]
    exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)

lemma m_step (k : ℕ) : 2 * m k + 16 ≤ m (k + 1) := by
  rw [m_succ]
  exact Nat.add_le_add_right (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) _

noncomputable def L (k : ℕ) : ℕ := m k ^ 2 - D k

lemma D_lt_m (k : ℕ) : D k < m k := by
  have := m_ge k
  omega

lemma L_add (k : ℕ) : L k + D k = m k ^ 2 :=
  Nat.sub_add_cancel ((D_lt_m k).le.trans (Nat.le_self_pow two_ne_zero _))

lemma L_lower (k : ℕ) : m k ^ 2 < L k + m k := by
  rw [← L_add]
  exact Nat.add_lt_add_left (D_lt_m k) _

lemma L_mono : StrictMono L := strictMono_nat_of_lt_succ fun k => by
  have h1 := L_add k
  have h2 := L_lower (k + 1)
  have h3 := m_step k
  have h7 : m k ^ 2 + m (k + 1) ≤ m (k + 1) ^ 2 := by
    have h8 := Nat.mul_le_mul_left (m (k + 1)) h3
    nlinarith
  omega

lemma L_two : 2 ≤ L 0 := by
  have h1 := L_lower 0
  have h2 := m_ge 0
  have h3 : 2 * m 0 ≤ m 0 ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

lemma sqrt_L (k : ℕ) : Nat.sqrt (L k) = m k - 1 := by
  have h1 := L_add k
  have h2 := m_ge k
  have h3 := D_gt k
  obtain ⟨c, hc⟩ : ∃ c, m k = c + 1 := ⟨m k - 1, by omega⟩
  have h4 : m k ^ 2 = c ^ 2 + 2 * c + 1 := by rw [hc]; ring
  have e1 : L k = c ^ 2 + (2 * c + 1 - D k) := by omega
  rw [e1, hc, Nat.add_sub_cancel]
  exact Nat.sqrt_add_eq' _ (by omega)

lemma upper_gap (k : ℕ) : (Nat.sqrt (L k) + 1) ^ 2 - L k = D k := by
  have h1 := L_add k
  have h2 := m_ge k
  rw [sqrt_L, Nat.sub_add_cancel (by omega : 1 ≤ m k)]
  omega

lemma lower_gap : Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_id
  have h1 := L_add k
  have h2 := m_ge k
  have h3 : k < 2 ^ k := Nat.lt_two_pow_self
  have h5 := m_pow k
  have h6 := D_lt_m k
  rw [sqrt_L]
  obtain ⟨c, hc⟩ : ∃ c, m k = c + 1 := ⟨m k - 1, by omega⟩
  have h4 : m k ^ 2 = c ^ 2 + 2 * c + 1 := by rw [hc]; ring
  rw [hc, Nat.add_sub_cancel]
  simp only [id]
  omega

lemma gaps : ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1) := by
  intro G
  refine ⟨G, ?_⟩
  have h1 := L_add G
  have h2 := L_lower (G + 1)
  have h3 : 2 * m G + 2 ^ (G + 1) + 16 ≤ m (G + 1) := by
    rw [m_succ]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_right _ _) _) _
  have h4 : G + 1 < 2 ^ (G + 1) := Nat.lt_two_pow_self
  have h5 := m_ge G
  have h6 : (m G + G + 1) * m (G + 1) + m (G + 1) ≤ m (G + 1) ^ 2 := by
    rw [sq, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have h7 : m G ^ 2 + G ≤ (m G + G + 1) * m (G + 1) := by
    have h8 : m G * m G + G ≤ (m G + G + 1) * m G := by
      have : G ≤ (G + 1) * m G := le_trans (Nat.le_succ G) (Nat.le_mul_of_pos_right _ (by omega))
      calc m G * m G + G ≤ m G * m G + (G + 1) * m G := Nat.add_le_add_left this _
        _ = (m G + G + 1) * m G := by ring
    rw [sq]
    exact h8.trans (Nat.mul_le_mul_left _ (by omega))
  omega

lemma far : ∀ h : ℕ, ∀ᶠ i in atTop, ∀ k, Mx i + h ≤ L k ∨ L k < Mx i := by
  intro h
  filter_upwards [eventually_ge_atTop (2 * h)] with i hi k
  rcases lt_or_ge (L k) (Mx i) with hlt | hge
  · exact Or.inr hlt
  refine Or.inl ?_
  have h1 := L_add k
  have h2 := m_ge k
  have h3 := r_gt i
  have hrm : r i < m k := by
    by_contra hc
    have h4 : m k ^ 2 ≤ r i ^ 2 := Nat.pow_le_pow_left (not_lt.1 hc) 2
    have h5 : Mx i = r i ^ 2 + r i := by unfold Mx; ring
    have := L_lower k
    omega
  have h6 : Mx i + m k ≤ m k ^ 2 := by
    have h7 : Mx i ≤ (m k - 1) * m k := by
      unfold Mx
      exact Nat.mul_le_mul (by omega) (by omega)
    have h8 : (m k - 1) * m k + m k = m k ^ 2 := by
      rw [sq, ← Nat.succ_mul]
      congr 1
      omega
    omega
  omega

/-! ### Counting -/

lemma count_D (x : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, D k ≤ x) :
    s.card ≤ (Nat.log 2 x + 1) * (Nat.sqrt x + 2) := by
  have hmap : ∀ k ∈ s, (I k, nn k - r (I k)) ∈
      Finset.range (Nat.log 2 x + 1) ×ˢ Finset.range (Nat.sqrt x + 2) := by
    intro k hk
    have hx := hs k hk
    have h1 := D_gt k
    have h2 := spec k
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have h3 : 2 ^ I k ≤ x := by
        have h4 : 2 ^ I k ≤ r (I k) := by
          unfold r
          exact (Nat.pow_le_pow_right two_pos (Nat.le_succ _)).trans (Nat.pow_le_pow_left (by norm_num) _)
        omega
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two h3)
    · by_contra hc
      have h3 : r (I k) + Nat.sqrt x + 2 ≤ nn k := by omega
      have h4 : (r (I k) + Nat.sqrt x + 2) ^ 2 ≤ nn k ^ 2 := Nat.pow_le_pow_left h3 2
      have h5 : x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' x
      have h6 : (Nat.sqrt x + 1) ^ 2 + r (I k) ^ 2 + r (I k) ≤ (r (I k) + Nat.sqrt x + 2) ^ 2 := by
        have h7 : (r (I k) + Nat.sqrt x + 2) ^ 2 =
            (Nat.sqrt x + 1) ^ 2 + r (I k) ^ 2 + r (I k) +
              (2 * r (I k) * Nat.sqrt x + 3 * r (I k) + 2 * Nat.sqrt x + 3) := by ring
        omega
      have h8 : Mx (I k) = r (I k) ^ 2 + r (I k) := by unfold Mx; ring
      omega
  refine (Finset.card_le_card_of_injOn (fun k => (I k, nn k - r (I k))) hmap ?_).trans (le_of_eq ?_)
  · intro a _ b _ hab
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hab
    have ha := spec a
    have hb := spec b
    have h3 : nn a = nn b := by
      have e1 := ha.1
      have e2 := hb.1
      rw [h1] at h2 e1
      omega
    have h4 : D a = D b := by
      have e1 := ha.2.1
      have e2 := hb.2.1
      rw [h3, h1] at e1
      omega
    refine e_mono.injective ?_
    rw [ha.2.2, hb.2.2, h4, h1]
  · rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- `D_k` is at least about `k^2 / (log k)^2`. -/
lemma index_le (k : ℕ) : k + 1 ≤ (Nat.log 2 (D k) + 1) * (Nat.sqrt (D k) + 2) := by
  have h := count_D (D k) (Finset.range (k + 1)) fun j hj =>
    D_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  rwa [Finset.card_range] at h

/-! ### The coefficients -/

noncomputable def w (k : ℕ) : ℕ := Nat.log 2 (nn k)

lemma w_top : Tendsto w atTop atTop := by
  refine tendsto_atTop.2 fun t => ?_
  have h : ∀ᶠ k : ℕ in atTop, 2 ^ t ≤ nn k := by
    set B := 2 ^ t with hB
    refine eventually_atTop.2 ⟨(B ^ 2) ^ 2 + B + 1, fun k hk => ?_⟩
    by_contra hc
    have h1 := spec k
    have h2 : D k ≤ B ^ 2 := by
      have h3 : nn k ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h4 : I k < B := by
      have := r_gt (I k)
      have := h1.1
      omega
    have h5 : e k ≤ (B ^ 2) ^ 2 + B := by
      rw [h1.2.2]
      exact Nat.add_le_add (Nat.pow_le_pow_left h2 2) h4.le
    have h6 : k ≤ e k := e_mono.id_le k
    omega
  exact h.mono fun k hk => Nat.le_log_of_pow_le one_lt_two hk

/-- The forced zero digits: those seen by `δ`, and the squares. -/
def Z : Set ℕ := {j | ∃ k s t : ℕ, 1 ≤ t ∧ t ≤ w k ∧ j + 1 + L k = s ^ 2 + t} ∪ {j | ∃ s, j = s ^ 2}

lemma w_le (k : ℕ) : w k ≤ nn k := Nat.log_le_self 2 _

open Classical in
lemma count_Z (N : ℕ) : Nat.count (fun j => j ∈ Z) N ≤
    (Nat.sqrt N + 1) + ((Nat.log 2 N + 1) * (Nat.sqrt N + 2)) * Nat.log 2 (N + 1) +
      ((Nat.log 2 N + 1) * (Nat.sqrt N + 1)) * Nat.log 2 N := by
  classical
  set sq : Finset ℕ := (Finset.range (Nat.sqrt N + 1)).image (fun s => s ^ 2) with hsq
  set KA : Finset ℕ := (Finset.range ((Nat.log 2 N + 1) * (Nat.sqrt N + 2) + 1)).filter (fun k => D k ≤ N) with hKA
  set A : Finset ℕ := KA.biUnion fun k => (Finset.Icc 1 (Nat.log 2 (N + 1))).image fun t => D k + t - 1 with hAdef
  set KB : Finset ℕ := (Finset.range (Nat.log 2 N + 1)).filter (fun k => m k < N) with hKB
  set B : Finset ℕ := KB.biUnion fun k => (Finset.Ioc (m k) (m k + Nat.sqrt N + 1)).biUnion fun s =>
    (Finset.Icc 1 (Nat.log 2 N)).image fun t => s ^ 2 + t - 1 - L k with hBdef
  have hsub : (Finset.range N).filter (fun j => j ∈ Z) ⊆ sq ∪ A ∪ B := by
    intro j hj
    obtain ⟨hjN, hjZ⟩ := Finset.mem_filter.1 hj
    have hjN' := Finset.mem_range.1 hjN
    rcases hjZ with ⟨k, s, t, ht1, ht2, heq⟩ | ⟨s, hs⟩
    swap
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨s, ?_, hs.symm⟩))
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_sqrt'.2 (by omega)))
    have h1 := L_add k
    have h2 := m_ge k
    have h3 := D_gt k
    have h4 := nn_le k
    have h5 := w_le k
    have htm : t ≤ D k + 1 := by omega
    rcases lt_trichotomy s (m k) with hs | hs | hs
    · exfalso
      have h6 : (s + 1) ^ 2 ≤ m k ^ 2 := Nat.pow_le_pow_left hs 2
      have h7 : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
      have h8 : s ^ 2 + 2 * m k ≤ m k ^ 2 + 1 := by
        obtain ⟨c, hc⟩ : ∃ c, m k = c + 1 := ⟨m k - 1, by omega⟩
        have h9 : s ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h10 : m k ^ 2 = c ^ 2 + 2 * c + 1 := by rw [hc]; ring
        omega
      omega
    · have e1 : j + 1 = D k + t := by rw [hs] at heq; omega
      have hDN : D k ≤ N := by omega
      have hkc : k + 1 ≤ (Nat.log 2 N + 1) * (Nat.sqrt N + 2) := by
        refine (index_le k).trans (Nat.mul_le_mul (Nat.add_le_add_right (Nat.log_mono_right hDN) 1)
          (Nat.add_le_add_right (Nat.sqrt_le_sqrt hDN) 2))
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [hAdef, Finset.mem_biUnion]
      refine ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hDN⟩,
        Finset.mem_image.2 ⟨t, Finset.mem_Icc.2 ⟨ht1, ?_⟩, by omega⟩⟩
      exact ht2.trans (Nat.log_mono_right (by omega))
    · have h6 : (m k + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs 2
      have h7 : (m k + 1) ^ 2 = m k ^ 2 + 2 * m k + 1 := by ring
      have hmN : 2 * m k < N := by omega
      have h8 : 2 ^ k ≤ N := by
        have := m_pow k
        omega
      have h9 : s ≤ m k + Nat.sqrt N + 1 := by
        by_contra hc
        have h10 : (m k + (Nat.sqrt N + 1)) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h11 : N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
        have h12 : m k ^ 2 + (Nat.sqrt N + 1) ^ 2 ≤ (m k + (Nat.sqrt N + 1)) ^ 2 := by
          have h13 : (m k + (Nat.sqrt N + 1)) ^ 2 =
              m k ^ 2 + (Nat.sqrt N + 1) ^ 2 + 2 * m k * (Nat.sqrt N + 1) := by ring
          omega
        omega
      refine Finset.mem_union_right _ ?_
      rw [hBdef, Finset.mem_biUnion]
      refine ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2
        (Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two h8)), by omega⟩, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨s, Finset.mem_Ioc.2 ⟨hs, h9⟩, Finset.mem_image.2 ⟨t, Finset.mem_Icc.2 ⟨ht1, ?_⟩, by omega⟩⟩
      have h14 : nn k ≤ N := by omega
      exact ht2.trans (Nat.log_mono_right h14)
  rw [Nat.count_eq_card_filter_range]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)) ?_))
  · exact Finset.card_image_le.trans (Finset.card_range _).le
  · have hKAc : KA.card ≤ (Nat.log 2 N + 1) * (Nat.sqrt N + 2) :=
      count_D N KA fun k hk => (Finset.mem_filter.1 hk).2
    refine (Finset.card_biUnion_le_card_mul _ _ (Nat.log 2 (N + 1)) fun k _ => ?_).trans
      (Nat.mul_le_mul_right _ hKAc)
    exact Finset.card_image_le.trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
  · have hKBc : KB.card ≤ Nat.log 2 N + 1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    refine (Finset.card_biUnion_le_card_mul _ _ ((Nat.sqrt N + 1) * Nat.log 2 N) fun k _ => ?_).trans ?_
    · refine (Finset.card_biUnion_le_card_mul _ _ (Nat.log 2 N) fun s _ => ?_).trans (le_of_eq ?_)
      · exact Finset.card_image_le.trans (by rw [Nat.card_Icc, Nat.add_sub_cancel])
      · rw [Nat.card_Ioc]
        congr 1
        omega
    · rw [mul_assoc]
      exact Nat.mul_le_mul_right _ hKBc

open Classical in
lemma small_Z (c : ℝ) (hc : 0 < c) : ∀ᶠ N : ℕ in atTop, (Nat.count (fun j => j ∈ Z) N : ℝ) ≤ c * N := by
  have hlog : ∀ᶠ N : ℕ in atTop, (Real.log N) ^ 2 ≤ c / 100 * Real.sqrt N := by
    have h1 : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x ^ ((1 : ℝ) / 2) :=
      isLittleO_log_rpow_rpow_atTop 2 (by norm_num) |>.congr_left (fun x => by norm_num [Real.rpow_two])
    have h2 := (h1.comp_tendsto tendsto_natCast_atTop_atTop).def (show 0 < c / 100 by positivity)
    filter_upwards [h2] with N hN
    simp only [Function.comp] at hN
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.sqrt_eq_rpow] at hN
    exact hN
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlog, hlog1, eventually_ge_atTop 4] with N h1 h2 h4
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast h4
  set q := Real.sqrt N with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q * q = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hq2 : 2 ≤ q := by
    have : Real.sqrt 4 ≤ q := Real.sqrt_le_sqrt hN4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at this
  have hsq : (Nat.sqrt N : ℝ) ≤ q := Real.nat_sqrt_le_real_sqrt
  have hl2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogb : ∀ M : ℕ, 1 ≤ M → M ≤ 2 * N → (Nat.log 2 M : ℝ) ≤ 3 * Real.log N := by
    intro M hM hMN
    have h5 : (2 : ℝ) ^ Nat.log 2 M ≤ M := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0)
    have h6 := Real.log_le_log (by positivity) (h5.trans (show (M : ℝ) ≤ 2 * N by exact_mod_cast hMN))
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h6
    have h7 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
    have h8 : (0 : ℝ) ≤ Nat.log 2 M := Nat.cast_nonneg _
    nlinarith
  have ha := hlogb N (by omega) (by omega)
  have hb := hlogb (N + 1) (by omega) (by omega)
  have hcount := count_Z N
  have hR : (Nat.count (fun j => j ∈ Z) N : ℝ) ≤
      (q + 1) + ((3 * Real.log N + 1) * (q + 2)) * (3 * Real.log N) +
        ((3 * Real.log N + 1) * (q + 1)) * (3 * Real.log N) := by
    refine le_trans (Nat.cast_le.2 hcount) ?_
    push_cast
    have ha0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ Nat.log 2 (N + 1) := Nat.cast_nonneg _
    have hs0 : (0 : ℝ) ≤ Nat.sqrt N := Nat.cast_nonneg _
    gcongr
  have hl := Real.log N
  have h3 : (q + 1) + ((3 * Real.log N + 1) * (q + 2)) * (3 * Real.log N) +
      ((3 * Real.log N + 1) * (q + 1)) * (3 * Real.log N) ≤ 60 * (Real.log N) ^ 2 * q := by
    have h4' : Real.log N ≤ (Real.log N) ^ 2 := by nlinarith
    have h5 : (3 * Real.log N + 1) * (3 * Real.log N) ≤ 12 * (Real.log N) ^ 2 := by nlinarith
    have h6 : ((3 * Real.log N + 1) * (q + 2)) * (3 * Real.log N) ≤ 12 * (Real.log N) ^ 2 * (2 * q) := by
      have e : ((3 * Real.log N + 1) * (q + 2)) * (3 * Real.log N) =
          ((3 * Real.log N + 1) * (3 * Real.log N)) * (q + 2) := by ring
      rw [e]
      exact mul_le_mul h5 (by linarith) (by linarith) (by positivity)
    have h7 : ((3 * Real.log N + 1) * (q + 1)) * (3 * Real.log N) ≤ 12 * (Real.log N) ^ 2 * (2 * q) := by
      have e : ((3 * Real.log N + 1) * (q + 1)) * (3 * Real.log N) =
          ((3 * Real.log N + 1) * (3 * Real.log N)) * (q + 1) := by ring
      rw [e]
      exact mul_le_mul h5 (by linarith) (by linarith) (by positivity)
    have h8 : q + 1 ≤ 2 * ((Real.log N) ^ 2 * q) := by
      have h9 : (1 : ℝ) ≤ (Real.log N) ^ 2 := by nlinarith
      have h10 : q ≤ (Real.log N) ^ 2 * q := le_mul_of_one_le_left hq0 h9
      linarith
    nlinarith
  refine hR.trans (h3.trans ?_)
  have h11 := mul_le_mul_of_nonneg_right h1 hq0
  have h12 : c / 100 * q * q = c / 100 * N := by rw [mul_assoc, hqq]
  have h13 : (0 : ℝ) ≤ c * N := by positivity
  nlinarith

lemma after_Z (j0 : ℕ) : ∃ j1 ∈ Z, j0 < j1 ∧ j1 ≤ j0 + 2 * Nat.sqrt (j0 + 5) + 1 := by
  refine ⟨(Nat.sqrt j0 + 1) ^ 2, Or.inr ⟨_, rfl⟩, Nat.lt_succ_sqrt' j0, ?_⟩
  have h1 : Nat.sqrt j0 ^ 2 ≤ j0 := Nat.sqrt_le' j0
  have h2 : Nat.sqrt j0 ≤ Nat.sqrt (j0 + 5) := Nat.sqrt_le_sqrt (by omega)
  have h3 : (Nat.sqrt j0 + 1) ^ 2 = Nat.sqrt j0 ^ 2 + 2 * Nat.sqrt j0 + 1 := by ring
  omega

lemma coeff (d : ℕ → Fin 2) (hd : ∀ j ∈ Z, d j = 0) : InA (dyseq L) sT (Real.ofDigits d) := by
  intro ε hε
  have h1 : Tendsto (fun v : ℕ => ((2 : ℝ)⁻¹) ^ v) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [w_top.eventually (h1.eventually (Iio_mem_nhds hε))] with k hk s
  refine le_trans ?_ (le_of_lt hk)
  have e1 : sT s = (2 : ℝ) ^ ((s + 1) ^ 2) := rfl
  rw [e1, inv_pow]
  have hzero : ∀ j t, 1 ≤ t → t ≤ w k → j + 1 + L k = (s + 1) ^ 2 + t → d j = 0 :=
    fun j t ht1 ht2 h => hd j (Or.inl ⟨k, s + 1, t, ht1, ht2, h⟩)
  unfold dyseq
  rcases le_or_gt (L k) ((s + 1) ^ 2) with hle | hlt
  · obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨z, hz⟩ := shift_digits d a
    have e2 : Real.ofDigits d * ((2 : ℝ) ^ L k)⁻¹ * 2 ^ ((s + 1) ^ 2) =
        Real.ofDigits (fun i => d (i + a)) - ((-z : ℤ) : ℝ) := by
      have e3 : Real.ofDigits d * ((2 : ℝ) ^ L k)⁻¹ * 2 ^ ((s + 1) ^ 2) = 2 ^ a * Real.ofDigits d := by
        rw [ha, pow_add]
        field_simp
      rw [e3, hz]
      push_cast
      ring
    rw [e2, dint_sub_int]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (Real.ofDigits_nonneg _)]
    refine ofDigits_le_of_zero _ (w k) fun i hi => ?_
    exact hzero (i + a) (i + 1) (by omega) (by omega) (by omega)
  · obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hlt.le
    have e2 : Real.ofDigits d * ((2 : ℝ) ^ L k)⁻¹ * 2 ^ ((s + 1) ^ 2) = Real.ofDigits d * ((2 : ℝ) ^ g)⁻¹ := by
      rw [hg, pow_add]
      field_simp
    rw [e2]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (mul_nonneg (Real.ofDigits_nonneg _) (by positivity))]
    have h2 : Real.ofDigits d ≤ ((2 : ℝ) ^ (w k - g))⁻¹ := by
      refine ofDigits_le_of_zero _ _ fun j hj => ?_
      exact hzero j (j + 1 + g) (by omega) (by omega) (by omega)
    have h3 : (2 : ℝ) ^ w k ≤ 2 ^ (w k - g) * 2 ^ g := by
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
    refine (mul_le_mul_of_nonneg_right h2 (by positivity)).trans ?_
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) h3

lemma dimH_coeff : dimH {a | InA (dyseq L) sT a} = 1 :=
  Dim.dimH_one Z small_Z after_Z _ coeff


/-! ### Dyadic rationals are coefficients -/

lemma dyadic_coeff (z j : ℕ) : InA (dyseq L) sT ((z : ℝ) / 2 ^ j) := by
  intro ε hε
  have h1 : Tendsto (fun v : ℕ => (z : ℝ) * ((2 : ℝ)⁻¹) ^ v) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul (z : ℝ)
    rwa [mul_zero] at this
  obtain ⟨v, hv⟩ := eventually_atTop.1 (h1.eventually_le_const hε)
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (w_top.eventually (eventually_ge_atTop (j + v + 1)))
  refine eventually_atTop.2 ⟨max k0 (2 ^ (j + v + 1)), fun k hk s => ?_⟩
  have hsm : sT s = (2 : ℝ) ^ ((s + 1) ^ 2) := rfl
  have e1 : (z : ℝ) / 2 ^ j * dyseq L k * sT s = (z : ℝ) * 2 ^ ((s + 1) ^ 2) / 2 ^ (j + L k) := by
    rw [hsm, pow_add]
    unfold dyseq
    field_simp
  rw [e1]
  rcases le_or_gt (j + L k) ((s + 1) ^ 2) with hle | hlt
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have e2 : (z : ℝ) * 2 ^ ((s + 1) ^ 2) / 2 ^ (j + L k) = (((z : ℤ) * 2 ^ d : ℤ) : ℝ) := by
      rw [hd, pow_add]
      push_cast
      field_simp
    rw [e2, dint_intZ]
    exact hε.le
  · -- the exponent is negative, and by more than `v`
    have hgap : (s + 1) ^ 2 + v ≤ j + L k := by
      have h2 := L_add k
      have h3 := m_ge k
      have h4 := D_gt k
      have h5 := m_pow k
      have h6 : 2 ^ (j + v + 1) ≤ m k := by
        have : k < 2 ^ k := Nat.lt_two_pow_self
        exact le_trans (le_trans (le_max_right _ _) (le_trans hk this.le)) h5
      have h7 : j + v < 2 ^ (j + v + 1) := lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self
      rcases lt_trichotomy (s + 1) (m k) with h8 | h8 | h8
      · have h9 : (s + 1) ^ 2 + (2 * m k - 1) ≤ m k ^ 2 := by
          obtain ⟨c, hc⟩ : ∃ c, m k = c + 1 := ⟨m k - 1, by omega⟩
          have h10 : (s + 1) ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h11 : m k ^ 2 = c ^ 2 + 2 * c + 1 := by rw [hc]; ring
          omega
        omega
      · exfalso
        rw [h8] at hlt
        have h9 : j < D k := by
          have h10 : j + v + 1 ≤ D k := by
            have h11 : j + v + 1 ≤ w k := hk0 k (le_trans (le_max_left _ _) hk)
            have h12 : w k ≤ nn k := w_le k
            have h13 := nn_le k
            have h14 : w k ≤ D k := by
              have h15 : Nat.log 2 (nn k) < nn k := by
                refine Nat.log_lt_self 2 ?_
                have := (spec k).1
                omega
              unfold w
              omega
            omega
          omega
        omega
      · have h9 : m k ^ 2 + 2 * m k + 1 ≤ (s + 1) ^ 2 := by
          have h10 : (m k + 1) ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left h8 2
          have h11 : (m k + 1) ^ 2 = m k ^ 2 + 2 * m k + 1 := by ring
          omega
        have h12 : j < 2 * m k := by omega
        omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlt.le
    have hdv : v ≤ d := by omega
    have e2 : (z : ℝ) * 2 ^ ((s + 1) ^ 2) / 2 ^ (j + L k) = (z : ℝ) * ((2 : ℝ)⁻¹) ^ d := by
      rw [hd, pow_add, inv_pow]
      field_simp
    rw [e2]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    exact hv d hdv

/-! ### Growing blocks: not rigid -/

lemma Mx_gap {a b : ℕ} (h : a < b) : Mx a + 4 * b + 4 ≤ Mx b := by
  have h1 : 4 * r a ≤ r b := by
    unfold r
    have : 4 ^ (a + 1 + 1) ≤ 4 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    omega
  have h2 := r_gt a
  have h3 := r_gt b
  have h4 : Mx a = r a * r a + r a := by unfold Mx; ring
  have h5 : Mx b = r b * r b + r b := by unfold Mx; ring
  have h6 : (4 * r a) * (4 * r a) ≤ r b * r b := Nat.mul_le_mul h1 h1
  have h7 : r a ≤ r a * r a := Nat.le_mul_of_pos_left _ (by omega)
  have h8 : 4 * b + 4 ≤ r b * r b := by
    have : r b * 4 ≤ r b * r b := Nat.mul_le_mul_left _ (by
      have : (4 : ℕ) ^ 1 ≤ 4 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold r
      omega)
    omega
  have h9 : (4 * r a) * (4 * r a) = 16 * (r a * r a) := by ring
  omega

lemma Mx_big (i : ℕ) : i + 2 ≤ Mx i := by
  have h1 := r_gt i
  have h2 : Mx i = r i * r i + r i := by unfold Mx; ring
  have h3 : 1 ≤ r i * r i := Nat.mul_pos (by omega) (by omega)
  omega

/-- A pair that is kept puts a window of width one on the position `M_i - 1`. -/
lemma window_of_kept (i n : ℕ) (hn : r i < n + 1) (hk : (n + 1) % Md.nu i ≠ i % Md.nu i) :
    ∃ k m q : ℕ, n < m ∧ q + (n + 1) ^ 2 = (m + 1) ^ 2 + (Mx i - 1) ∧ L k ≤ q + 1 ∧ q < L k := by
  have hc : ((n + 1) ^ 2 - Mx i) ^ 2 + i ∈ S := ⟨i, n + 1, hn, hk, rfl⟩
  obtain ⟨k, hk'⟩ := e_surj hc
  have hD : D k = (n + 1) ^ 2 - Mx i := by
    unfold D
    rw [hk']
    exact code_sqrt hn
  have h1 := D_ge hn
  have h2 := L_add k
  have h3 := m_ge k
  have h4 := D_gt k
  have h5 := Mx_big i
  have h6 : n + 1 ≤ D k + 1 := by
    have hI : I k = i := by
      unfold I
      rw [hD, hk']
      omega
    have h7 : nn k = n + 1 := by
      unfold nn
      rw [hI, hD, Nat.sub_add_cancel (by omega), Nat.sqrt_eq']
    have := nn_le k
    omega
  have hm1 : 1 ≤ m k := by omega
  refine ⟨k, m k - 1, L k - 1, by omega, ?_, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hm1]
    have h8 : D k ≤ L k := by
      have h9 : 2 * m k ≤ m k ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  · omega
  · have h9 : 2 * m k ≤ m k ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

omit S0 in
/-- The moduli of the growing example: the largest power of two below the index. -/
def grow : Md := ⟨fun i => max 2 (2 ^ Nat.log 2 i), fun _ => le_max_left _ _⟩

omit S0 in
lemma not_rig_grow : letI := grow; ¬ Rig (dyseq L) := by
  letI := grow
  set P : ℕ → Finset ℕ := fun c => (Finset.Ico (2 ^ (c + 1)) (2 ^ (c + 2))).image fun i => Mx i - 1 with hP
  have hmem : ∀ c p, p ∈ P c → ∃ i, 2 ^ (c + 1) ≤ i ∧ i < 2 ^ (c + 2) ∧ p = Mx i - 1 := by
    intro c p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨i, (Finset.mem_Ico.1 hi).1, (Finset.mem_Ico.1 hi).2, rfl⟩
  have hsepM : ∀ i j : ℕ, Mx i - 1 < Mx j - 1 → Mx i - 1 + 2 ≤ Mx j - 1 := by
    intro i j h
    have hij : i < j := by
      by_contra hc
      have := Mx_mono.monotone (not_lt.1 hc)
      omega
    have := Mx_gap hij
    have := Mx_big i
    omega
  have hbig : ∀ c : ℕ, c < 2 ^ (c + 1) := fun c => lt_trans (Nat.lt_succ_self c) Nat.lt_two_pow_self
  refine not_rig_of_covers L L_mono 1 P ?_ ?_ ?_ ?_ ?_
  · intro c c' p hp q hq hpq
    obtain ⟨i, _, _, rfl⟩ := hmem c p hp
    obtain ⟨j, _, _, rfl⟩ := hmem c' q hq
    exact hsepM i j hpq
  · intro c c' hcc p hp q hq
    obtain ⟨i, _, h2, rfl⟩ := hmem c p hp
    obtain ⟨j, h3, _, rfl⟩ := hmem c' q hq
    have hij : i < j := lt_of_lt_of_le h2 (le_trans (Nat.pow_le_pow_right two_pos (by omega)) h3)
    have := Mx_gap hij
    have := Mx_big i
    omega
  · intro B
    filter_upwards [eventually_ge_atTop B] with c hc p hp
    obtain ⟨i, h1, _, rfl⟩ := hmem c p hp
    have := Mx_big i
    have := hbig c
    omega
  · intro g
    filter_upwards [(tendsto_atTop_mono (fun c => (hbig c).le) tendsto_id).eventually
      (eventually_ge_atTop 0), eventually_atTop.1 (far (g + 1)) |>.elim fun i0 hi0 =>
        (eventually_ge_atTop i0).mono fun c hc => (show ∀ i, 2 ^ (c + 1) ≤ i → ∀ k, Mx i + (g + 1) ≤ L k ∨ L k < Mx i
          from fun i hi k => hi0 i (le_trans hc (le_trans (hbig c).le hi)) k)] with c _ hc p hp k h1 h2
    obtain ⟨i, h3, _, rfl⟩ := hmem c p hp
    have := Mx_big i
    rcases hc i h3 k with h4 | h4 <;> omega
  · filter_upwards [eventually_ge_atTop 4] with c hc hcov
    obtain ⟨E, hE1, hE2, hE3⟩ := hcov
    have hcardP : c < (Finset.Ico (2 ^ (c + 1)) (2 ^ (c + 2))).card := by
      rw [Nat.card_Ico]
      have h1 : 2 ^ (c + 2) = 2 ^ (c + 1) + 2 ^ (c + 1) := by rw [pow_succ]; omega
      have := hbig c
      omega
    have hch : ∀ i ∈ Finset.Ico (2 ^ (c + 1)) (2 ^ (c + 2)), ∃ e ∈ E, Mx i - 1 ∈ e := fun i hi =>
      hE3 _ (Finset.mem_image_of_mem _ hi)
    choose! f hf1 hf2 using hch
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (lt_of_le_of_lt hE1 hcardP) hf1
    obtain ⟨n, hn⟩ := hE2 _ (hf1 i hi)
    have hres : ∀ t ∈ Finset.Ico (2 ^ (c + 1)) (2 ^ (c + 2)), Mx t - 1 ∈ f i →
        (n + 1) % 2 ^ (c + 1) = t % 2 ^ (c + 1) := by
      intro t ht htm
      obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.1 ht
      obtain ⟨h1, h2⟩ := hn _ htm
      have hnu : Md.nu t = 2 ^ (c + 1) := by
        show max 2 (2 ^ Nat.log 2 t) = _
        rw [Nat.log_eq_of_pow_le_of_lt_pow ht1 ht2]
        exact max_eq_right (le_trans (by norm_num) (Nat.pow_le_pow_right two_pos (Nat.le_add_left 1 c)))
      have hrt : r t < n + 1 := by
        by_contra hcon
        have h3 : (n + 1) ^ 2 ≤ r t ^ 2 := Nat.pow_le_pow_left (not_lt.1 hcon) 2
        have h4 : Mx t = r t ^ 2 + r t := by unfold Mx; ring
        have h5 := r_gt t
        have h6 := Mx_big t
        have := hbig c
        have h7 : c + 2 < r t := by omega
        omega
      by_contra hne
      obtain ⟨k, m, q, hnm, hbal, hlo, hhi⟩ := window_of_kept t n hrt (by rw [hnu]; exact hne)
      exact h2 k m q hnm hbal hlo hhi
    have h1 := hres i hi (hf2 i hi)
    have h2 := hres j hj (heq ▸ hf2 j hj)
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    have h3 : i % 2 ^ (c + 1) = i - 2 ^ (c + 1) := by
      rw [Nat.mod_eq_sub_mod hi1, Nat.mod_eq_of_lt]
      have h4 : 2 ^ (c + 2) = 2 ^ (c + 1) + 2 ^ (c + 1) := by rw [pow_succ]; omega
      omega
    have h4 : j % 2 ^ (c + 1) = j - 2 ^ (c + 1) := by
      rw [Nat.mod_eq_sub_mod hj1, Nat.mod_eq_of_lt]
      have h5 : 2 ^ (c + 2) = 2 ^ (c + 1) + 2 ^ (c + 1) := by rw [pow_succ]; omega
      omega
    exact hij (by omega)

/-! ### Constant blocks: rigid -/

omit S0 in
lemma eventually_log_small (A : ℕ) : ∃ u0 : ℕ, ∀ u, u0 ≤ u → A * (Nat.log 2 (u ^ 32) + 1) * (A * u) < u ^ 8 := by
  refine ⟨A * A * 64 + 2, fun u hu => ?_⟩
  have hu2 : 2 ≤ u := by omega
  have hlog : Nat.log 2 (u ^ 32) + 1 ≤ 64 * u := by
    have h1 : Nat.log 2 (u ^ 32) < 32 * u + 1 := by
      refine Nat.log_lt_of_lt_pow (by positivity) ?_
      have h2 : u ≤ 2 ^ u := (Nat.lt_two_pow_self).le
      have h3 : u ^ 32 ≤ 2 ^ (32 * u) := by
        rw [mul_comm, pow_mul]
        exact Nat.pow_le_pow_left h2 32
      exact lt_of_le_of_lt h3 (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self _))
    omega
  have h4 : A * (Nat.log 2 (u ^ 32) + 1) * (A * u) ≤ (A * A * 64) * u ^ 2 := by
    refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlog)).trans (le_of_eq ?_)
    ring
  have h5 : (A * A * 64) * u ^ 2 < u * u ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have h6 : u * u ^ 2 ≤ u ^ 8 := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

lemma rig_const (N : ℕ) (hN : ∀ i, Md.nu i = N) : Rig (dyseq L) := by
  classical
  have hN2 : 2 ≤ N := (hN 0) ▸ Md.two 0
  -- the class of a position: the residue of the first index whose `M` is not below it
  have hex : ∀ p : ℕ, ∃ i, p ≤ Mx i := fun p => ⟨p, le_trans (by omega) (Mx_big p)⟩
  set t0 : ℕ → ℕ := fun p => Nat.find (hex p) with ht0
  refine rig_of_classes L L_mono dyadic_coeff N fun h => ?_
  refine ⟨Mx h + 1, fun p => ⟨t0 p % N, Nat.mod_lt _ (by omega)⟩, fun P hP1 _ hPcol N0 => ?_⟩
  rcases P.eq_empty_or_nonempty with h0 | ⟨p0, hp0⟩
  · exact ⟨N0, le_rfl, fun p hp => by rw [h0] at hp; simp at hp⟩
  set j := t0 p0 % N with hj
  have hcol : ∀ p ∈ P, t0 p % N = j := fun p hp => by
    have := hPcol p hp p0 hp0
    exact Fin.mk.inj this
  -- a position just below `M_t` has class `t`
  have hband : ∀ p ∈ P, ∀ t s : ℕ, s ≤ h → p + s = Mx t → t0 p = t := by
    intro p hp t s hs heq
    have h1 : p ≤ Mx t := by omega
    refine (Nat.find_eq_iff (hex p)).2 ⟨h1, fun i hi hle => ?_⟩
    have h2 := Mx_gap hi
    have h3 := hP1 p hp
    have h4 : h < t := by
      by_contra hc
      have := Mx_mono.monotone (not_lt.1 hc)
      omega
    omega
  -- the exceptional shifts are few
  obtain ⟨C', hC'1, hC'⟩ := card_divisors_pow_le 32 (by norm_num)
  set Pm := P.sup id with hPm
  set A := 4 * (P.card + 1) * (h + 1) * (C' + 1) * N * 8 with hA
  obtain ⟨u0, hu0⟩ := eventually_log_small A
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ : ∃ u, u0 ≤ u ∧ 2 * (N0 + h + Pm + 2) ≤ u ∧ 4 * N ≤ u ∧ 2 ≤ u :=
    ⟨u0 + 2 * (N0 + h + Pm + 2) + 4 * N + 2, by omega, by omega, by omega, by omega⟩
  set U := u ^ 8 with hU
  have huU : u ≤ U := Nat.le_self_pow (by norm_num) u
  set D0 := C' * u with hD0
  have hdiv : ∀ M, M ≤ U ^ 4 → M.divisors.card ≤ D0 := by
    intro M hM
    rcases eq_or_ne M 0 with h1 | h1
    · simp [h1]
    refine (Nat.pow_le_pow_iff_left (n := 32) (by norm_num)).1 ?_
    refine (hC' M h1).trans ?_
    have e1 : U ^ 4 = u ^ 32 := by rw [hU, ← pow_mul]
    rw [hD0, mul_pow]
    exact Nat.mul_le_mul (Nat.le_self_pow (by norm_num) C') (e1 ▸ hM)
  -- solutions of `a^2 + x = b^2 + y` in `a`
  set sol : ℕ → ℕ → Finset ℕ := fun x y => (Finset.Icc 1 U).filter fun a => ∃ b, a ^ 2 + x = b ^ 2 + y with hsol
  have hsolcard : ∀ x y, x ≠ y → x ≤ U ^ 4 → y ≤ U ^ 4 → (sol x y).card ≤ D0 := by
    intro x y hxy hx hy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · -- `a^2 = b^2 + (y - x)`: count the values of `b`
      have h1 : (sol x y).card ≤ ((Finset.Icc 0 U).filter fun b => ∃ a, b < a ∧ a ^ 2 = b ^ 2 + (y - x)).card := by
        refine Finset.card_le_card_of_injOn (fun a => Nat.sqrt (a ^ 2 - (y - x))) (fun a ha => ?_) ?_
        · obtain ⟨hI, b, hb⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
          have e1 : a ^ 2 = b ^ 2 + (y - x) := by omega
          have e2 : Nat.sqrt (a ^ 2 - (y - x)) = b := by
            rw [e1, Nat.add_sub_cancel, Nat.sqrt_eq']
          have hba : b < a := (Nat.pow_lt_pow_iff_left two_ne_zero).1 (by omega)
          refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.zero_le _, ?_⟩, a, ?_, ?_⟩)
          · simp only
            rw [e2]
            have := (Finset.mem_Icc.1 hI).2
            omega
          · simp only; rw [e2]; exact hba
          · simp only; rw [e2]; exact e1
        · intro a1 h1 a2 h2 heq
          obtain ⟨_, b1, hb1⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 h1)
          obtain ⟨_, b2, hb2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 h2)
          have f1 : Nat.sqrt (a1 ^ 2 - (y - x)) = b1 := by
            rw [show a1 ^ 2 - (y - x) = b1 ^ 2 by omega, Nat.sqrt_eq']
          have f2 : Nat.sqrt (a2 ^ 2 - (y - x)) = b2 := by
            rw [show a2 ^ 2 - (y - x) = b2 ^ 2 by omega, Nat.sqrt_eq']
          simp only at heq
          rw [f1, f2] at heq
          refine (Nat.pow_left_injective two_ne_zero) ?_
          simp only
          rw [heq] at hb1
          omega
      refine h1.trans ?_
      have h2 : ((Finset.Icc 0 U).filter fun b => ∃ a, b < a ∧ a ^ 2 = b ^ 2 + (y - x)).card ≤ (y - x).divisors.card := by
        refine Finset.card_le_card_of_injOn (fun b => Nat.sqrt (b ^ 2 + (y - x)) - b) (fun b hb => ?_) ?_
        · obtain ⟨_, a, hab, ha⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
          have e1 : Nat.sqrt (b ^ 2 + (y - x)) = a := by rw [← ha, Nat.sqrt_eq']
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab.le
          have e2 : y - x = d * (d + 2 * b) := by
            have : a ^ 2 = b ^ 2 + d * (d + 2 * b) := by rw [hd]; ring
            omega
          refine Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨?_, by omega⟩)
          show Nat.sqrt (b ^ 2 + (y - x)) - b ∣ y - x
          rw [e1, show a - b = d by omega]
          exact ⟨_, e2⟩
        · intro b1 h1 b2 h2 heq
          obtain ⟨_, a1, hab1, ha1⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 h1)
          obtain ⟨_, a2, hab2, ha2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 h2)
          have f1 : Nat.sqrt (b1 ^ 2 + (y - x)) = a1 := by rw [← ha1, Nat.sqrt_eq']
          have f2 : Nat.sqrt (b2 ^ 2 + (y - x)) = a2 := by rw [← ha2, Nat.sqrt_eq']
          simp only at heq
          rw [f1, f2] at heq
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab1.le
          have hd2 : a2 = b2 + d := by omega
          have e1 : a1 ^ 2 = b1 ^ 2 + d * (d + 2 * b1) := by rw [hd]; ring
          have e2 : a2 ^ 2 = b2 ^ 2 + d * (d + 2 * b2) := by rw [hd2]; ring
          have hd0 : 0 < d := by omega
          have e3 : d * (d + 2 * b1) = d * (d + 2 * b2) := by omega
          have := Nat.eq_of_mul_eq_mul_left hd0 e3
          omega
      exact h2.trans (hdiv _ (by omega))
    · -- `b^2 = a^2 + (x - y)`
      have h1 : sol x y ⊆ (Finset.Icc 1 U).filter fun a => ∃ b, a < b ∧ b ^ 2 = a ^ 2 + (x - y) := by
        intro a ha
        obtain ⟨hI, b, hb⟩ := Finset.mem_filter.1 ha
        have e1 : b ^ 2 = a ^ 2 + (x - y) := by omega
        exact Finset.mem_filter.2 ⟨hI, b, (Nat.pow_lt_pow_iff_left two_ne_zero).1 (by omega), e1⟩
      exact (Finset.card_le_card h1).trans ((card_sqdiff_le U _).trans (hdiv _ (by omega)))
  -- the bad shifts
  set lg := Nat.log 2 (u ^ 32) + 1 with hlg
  set B1 : Finset ℕ := P.biUnion fun p => (Finset.range lg).biUnion fun t => (Finset.range (h + 1)).biUnion fun s =>
    if Mx t ≠ p + s ∧ Mx t ≤ U ^ 4 ∧ p + s ≤ U ^ 4 then sol (Mx t) (p + s) else ∅ with hB1
  set B2 : Finset ℕ := P.biUnion fun p => (Finset.range lg).biUnion fun k => (Finset.range (h + 1)).biUnion fun s =>
    if L k ≠ p + s ∧ L k ≤ U ^ 4 ∧ p + s ≤ U ^ 4 then sol (L k) (p + s) else ∅ with hB2
  have hthree : ∀ f : ℕ → ℕ → ℕ → Finset ℕ, (∀ p t s, (f p t s).card ≤ D0) →
      (P.biUnion fun p => (Finset.range lg).biUnion fun t => (Finset.range (h + 1)).biUnion fun s => f p t s).card ≤
        P.card * (lg * ((h + 1) * D0)) := by
    intro f hf
    refine Finset.card_biUnion_le_card_mul _ _ _ fun p _ => ?_
    refine (Finset.card_biUnion_le_card_mul _ _ ((h + 1) * D0) fun t _ => ?_).trans
      (le_of_eq (by rw [Finset.card_range]))
    exact (Finset.card_biUnion_le_card_mul _ _ D0 fun s _ => hf p t s).trans (le_of_eq (by rw [Finset.card_range]))
  have hite : ∀ x y : ℕ, (if x ≠ y ∧ x ≤ U ^ 4 ∧ y ≤ U ^ 4 then sol x y else ∅).card ≤ D0 := by
    intro x y
    split_ifs with hc
    · exact hsolcard x y hc.1 hc.2.1 hc.2.2
    · simp
  have hBad : (B1 ∪ B2).card ≤ 2 * (P.card * (lg * ((h + 1) * D0))) := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [two_mul]
    exact Nat.add_le_add (hthree _ fun p t s => hite _ _) (hthree _ fun p k s => hite _ _)
  have hAsmall : 4 * N * (B1 ∪ B2).card < U := by
    have h1 := hu0 u hu1
    have h2 : 4 * N * (2 * (P.card * (lg * ((h + 1) * D0)))) ≤ A * lg * (A * u) := by
      have h3 : 4 * N * (2 * (P.card * (h + 1) * C')) ≤ A := by
        have h4 : P.card * (h + 1) * C' ≤ (P.card + 1) * (h + 1) * (C' + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.le_succ _)
        calc 4 * N * (2 * (P.card * (h + 1) * C')) = 8 * N * (P.card * (h + 1) * C') := by ring
          _ ≤ 32 * N * ((P.card + 1) * (h + 1) * (C' + 1)) := Nat.mul_le_mul (by omega) h4
          _ = A := by rw [hA]; ring
      have h5 : 1 ≤ A := by
        rw [hA]
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _))
          (Nat.succ_pos _)) (Nat.succ_pos _)) (by omega)) (by norm_num)
      calc 4 * N * (2 * (P.card * (lg * ((h + 1) * D0))))
          = (4 * N * (2 * (P.card * (h + 1) * C'))) * (lg * u) := by rw [hD0]; ring
        _ ≤ A * (lg * u) := Nat.mul_le_mul_right _ h3
        _ ≤ A * (lg * (A * u)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ h5))
        _ = A * lg * (A * u) := (mul_assoc _ _ _).symm
    exact lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left _ hBad) h2) h1
  -- a shift in the right residue class that is not bad
  have hjN : j < N := Nat.mod_lt _ (by omega)
  set q0 := U / (2 * N) with hq0
  set R : Finset ℕ := (Finset.Ioo q0 (U / N)).image (fun q => N * q + j) with hR
  have hq03 : 3 ≤ q0 := by
    rw [hq0, Nat.le_div_iff_mul_le (by omega)]
    have h1 : u * u ≤ U := by
      rw [hU, ← sq]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 3 * (2 * N) ≤ u * u := by
      calc 3 * (2 * N) ≤ 2 * (4 * N) := by omega
        _ ≤ u * u := Nat.mul_le_mul hu4 hu3
    omega
  have h2q : 2 * q0 ≤ U / N := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.div_mul_le_self U (2 * N)
    rw [← hq0] at this
    calc 2 * q0 * N = q0 * (2 * N) := by ring
      _ ≤ U := this
  have hRcard : (B1 ∪ B2).card < R.card := by
    have h1 : R.card = U / N - q0 - 1 := by
      rw [hR, Finset.card_image_of_injective _ (fun a b hab => ?_), Nat.card_Ioo]
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < N) (Nat.add_right_cancel hab)
    have h2 : U < 2 * N * (q0 + 1) := by
      rw [hq0]
      exact Nat.lt_mul_div_succ U (by omega)
    have h3 : 4 * N * (B1 ∪ B2).card < 2 * N * (q0 + 1) := lt_trans hAsmall h2
    have h4 : 2 * (B1 ∪ B2).card < q0 + 1 := by
      refine Nat.lt_of_mul_lt_mul_left (a := 2 * N) ?_
      calc 2 * N * (2 * (B1 ∪ B2).card) = 4 * N * (B1 ∪ B2).card := by ring
        _ < 2 * N * (q0 + 1) := h3
    omega
  obtain ⟨a, haR, haB⟩ := Finset.exists_mem_notMem_of_card_lt_card hRcard
  obtain ⟨qa, hqa, rfl⟩ := Finset.mem_image.1 haR
  obtain ⟨hqlo, hqhi⟩ := Finset.mem_Ioo.1 hqa
  set a := N * qa + j with ha
  have haU : a ≤ U := by
    have h1 : N * (qa + 1) ≤ U := by
      have h2 : qa + 1 ≤ U / N := hqhi
      exact le_trans (Nat.mul_le_mul_left _ h2) (Nat.mul_div_le U N)
    have h3 : N * (qa + 1) = N * qa + N := by ring
    omega
  have halo : U / 2 < a := by
    have h1 : N * (q0 + 1) ≤ N * qa := Nat.mul_le_mul_left _ hqlo
    have h2 : U < 2 * N * (q0 + 1) := by
      rw [hq0]
      exact Nat.lt_mul_div_succ U (by omega)
    have h3 : 2 * N * (q0 + 1) = 2 * (N * (q0 + 1)) := by ring
    omega
  have habig : N0 + h + Pm + 2 ≤ a := by omega
  have hamod : a % N = j := by
    rw [ha, Nat.mul_add_mod, Nat.mod_eq_of_lt hjN]
  have ha1 : 1 ≤ a := by omega
  refine ⟨a - 1, by omega, fun p hp k m' q hnm hbal hlo hhi => ?_⟩
  rw [Nat.sub_add_cancel ha1] at hbal
  set b := m' + 1 with hb
  have hab : a < b := by omega
  have hpPm : p ≤ Pm := Finset.le_sup (f := id) hp
  obtain ⟨s, hs⟩ : ∃ s, L k = q + s := ⟨L k - q, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hsh : s ≤ h := by omega
  have hmain : a ^ 2 + L k = b ^ 2 + (p + s) := by omega
  have hLk := L_add k
  have hmk := m_ge k
  have hpsU : p + s ≤ U := by omega
  have haU2 : a ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left haU 2
  have hU1 : 1 ≤ U := by omega
  have hU4 : U ≤ U ^ 4 := Nat.le_self_pow (by norm_num) U
  have hU24 : U ^ 2 ≤ U ^ 4 := Nat.pow_le_pow_right hU1 (by norm_num)
  have hpsU4 : p + s ≤ U ^ 4 := le_trans hpsU hU4
  have hu16 : U ^ 2 ≤ u ^ 32 := by
    rw [hU, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlog : ∀ i : ℕ, 2 ^ i ≤ U ^ 2 → i < lg := fun i hi =>
    Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two (le_trans hi hu16))
  rcases lt_trichotomy b (m k) with hbm | hbm | hbm
  · -- below the square above `L k`: only small shifts
    have h1 : b ^ 2 + (2 * m k - 1) ≤ m k ^ 2 := by
      obtain ⟨c, hc⟩ : ∃ c, m k = c + 1 := ⟨m k - 1, by omega⟩
      have h2 : b ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h3 : m k ^ 2 = c ^ 2 + 2 * c + 1 := by rw [hc]; ring
      omega
    omega
  · -- the square above `L k`
    have e1 : a ^ 2 = D k + (p + s) := by
      rw [hbm] at hmain
      omega
    have hsp := spec k
    have hD := D_gt k
    have e2 : a ^ 2 + Mx (I k) = nn k ^ 2 + (p + s) := by
      have := hsp.2.1
      omega
    by_cases hMx : Mx (I k) = p + s
    · have e3 : a = nn k := Nat.pow_left_injective two_ne_zero (show a ^ 2 = nn k ^ 2 by omega)
      have e4 : t0 p = I k := hband p hp (I k) s hsh (by omega)
      have e5 := kept k
      rw [hN, ← e3, hamod, ← e4, hcol p hp] at e5
      exact e5 rfl
    · have hDU : D k ≤ U ^ 2 := by omega
      have hr : r (I k) < U ^ 2 := by omega
      have ht : I k < lg := by
        refine hlog _ (le_trans ?_ hr.le)
        unfold r
        exact (Nat.pow_le_pow_right two_pos (Nat.le_succ _)).trans (Nat.pow_le_pow_left (by norm_num) _)
      have hMxU : Mx (I k) ≤ U ^ 4 := by
        have h1 : Mx (I k) ≤ D k * D k := by
          unfold Mx
          exact Nat.mul_le_mul (by omega) (by omega)
        refine le_trans h1 ?_
        have e : U ^ 4 = U ^ 2 * U ^ 2 := by rw [← pow_add]
        rw [e]
        exact Nat.mul_le_mul hDU hDU
      refine haB (Finset.mem_union_left _ ?_)
      rw [hB1, Finset.mem_biUnion]
      refine ⟨p, hp, Finset.mem_biUnion.2 ⟨I k, Finset.mem_range.2 ht, Finset.mem_biUnion.2
        ⟨s, Finset.mem_range.2 (by omega), ?_⟩⟩⟩
      rw [if_pos ⟨hMx, hMxU, hpsU4⟩]
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨ha1, haU⟩, nn k, e2⟩
  · -- above the square above `L k`
    have h1 : m k ^ 2 + 2 * m k + 1 ≤ b ^ 2 := by
      have h2 : (m k + 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hbm 2
      have h3 : (m k + 1) ^ 2 = m k ^ 2 + 2 * m k + 1 := by ring
      omega
    have h4 : m k < U ^ 2 := by omega
    have hk : k < lg := hlog _ ((m_pow k).trans h4.le)
    have hLkU : L k ≤ U ^ 4 := by
      have h5 : m k ^ 2 ≤ (U ^ 2) ^ 2 := Nat.pow_le_pow_left h4.le 2
      have e : (U ^ 2) ^ 2 = U ^ 4 := by rw [← pow_mul]
      omega
    have hne : L k ≠ p + s := by
      intro h5
      have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab two_ne_zero
      omega
    refine haB (Finset.mem_union_right _ ?_)
    rw [hB2, Finset.mem_biUnion]
    refine ⟨p, hp, Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, Finset.mem_biUnion.2
      ⟨s, Finset.mem_range.2 (by omega), ?_⟩⟩⟩
    rw [if_pos ⟨hne, hLkU, hpsU4⟩]
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨ha1, haU⟩, b, hmain⟩

omit S0 in
/-- The constant moduli. -/
def const (N : ℕ) (hN : 2 ≤ N) : Md := ⟨fun _ => N, fun _ => hN⟩

end Blocks

/-- **Blocks of bounded size give rigidity, growing blocks do not.** -/
theorem exists_threshold :
    (∀ N : ℕ, 2 ≤ N → ∃ L : ℕ → ℕ, StrictMono L ∧ Rig (dyseq L) ∧ dimH {a | InA (dyseq L) sT a} = 1) ∧
      ∃ L : ℕ → ℕ, StrictMono L ∧ ¬ Rig (dyseq L) ∧ dimH {a | InA (dyseq L) sT a} = 1 := by
  refine ⟨fun N hN => ?_, ?_⟩
  · letI := Blocks.const N hN
    exact ⟨Blocks.L, Blocks.L_mono, Blocks.rig_const N (fun _ => rfl), Blocks.dimH_coeff⟩
  · letI := Blocks.grow
    exact ⟨Blocks.L, Blocks.L_mono, Blocks.not_rig_grow, Blocks.dimH_coeff⟩

end Three
end PVG
