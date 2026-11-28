import LeanCheck.PVGThreeClassify
import LeanCheck.PVGThreeGeneral
import LeanCheck.PVGThreeDimension

/-!
# PVGthree: a sequence with many coefficients that is not rigid

* `not_rig_of_dominated`: if every coefficient of `δ_k = 2^(-L_k)` is a coefficient of `2^(-M_i)` and the
  `L_k` avoid long stretches above the `M_i`, then `δ` is not rigid.
* `exists_not_rig_dimH`: there is such a sequence whose set of coefficients has Hausdorff dimension `1`,
  with `L_k - c^2 → ∞` (`c = Nat.sqrt L_k`) and with `(c+1)^2 - L_k` at least about `k^2 / (log k)^2`.

So `δ` need not be rigid when `A(δ)` is uncountable, and the exponent `2` in `rig_iff_of_upper_gap` cannot
be lowered. Sequences are indexed from `0`; `sT n = 2^((n+1)^2)`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

/-! ## The obstruction -/

theorem not_rig_of_dominated (L M : ℕ → ℕ) (hM : StrictMono M)
    (hA : ∀ a : ℝ, InA (dyseq L) sT a → InA (dyseq M) sT a)
    (hfar : ∀ h : ℕ, ∀ᶠ i in atTop, ∀ k, M i + h ≤ L k ∨ L k < M i) : ¬ Rig (dyseq L) := by
  intro hrig
  set y := dyseq M with hy
  have hypos : ∀ i, 0 < y i := fun i => by
    rw [hy]
    unfold dyseq
    positivity
  have hy0 : Tendsto y atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ => ((2 : ℝ)⁻¹) ^ i) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    refine squeeze_zero (fun i => (hypos i).le) (fun i => ?_) h1
    rw [hy, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (hM.id_le i))
  have hy1 : ∀ i, |y i| ≤ 1 := fun i => by
    rw [abs_of_pos (hypos i), hy]
    unfold dyseq
    exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hs := serves_gam y hy0 hy1 (fun i => (hypos i).ne')
  set x : ℕ → ℝ := fun i => 2 ^ (M i - 1) with hx
  have hxU : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ k, dint (dyseq L k * x i) ≤ ε := by
    intro ε hε
    obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [hfar h, eventually_ge_atTop 1] with i hi hi1 k
    have hMi : 1 ≤ M i := le_trans hi1 (hM.id_le i)
    rcases hi k with hk | hk
    · refine (dint_le_abs _).trans (le_trans ?_ hh.le)
      rw [dyseq_mul, hx, abs_of_pos (by positivity), div_le_iff₀ (by positivity), one_div, inv_pow,
        inv_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show L k ≤ M i - 1 by omega)
      have e : dyseq L k * x i = (((2 : ℤ) ^ d : ℤ) : ℝ) := by
        rw [hx]
        unfold dyseq
        simp only
        rw [hd, pow_add]
        push_cast
        field_simp
      rw [e, dint_intZ]
      exact hε.le
  have hW : {z : ℝ | ∀ j, dint (y j * z) ≤ 1 / 16} ∈ @nhds ℝ (gamTop y) 0 :=
    (mem_nhds_gam y _).2 ⟨univ, univ_mem, 1 / 16, by norm_num, fun z _ h => h⟩
  obtain ⟨ε, hε, F, hF⟩ := hrig (gamTop y) (gam_group _) (gam_coarser_euclid _ 1 hy1 0)
    (fun a ha => hs.2.2.2.2 a (hA a ha)) _ hW
  obtain ⟨i0, hi0⟩ := eventually_atTop.1 ((hxU ε hε).and (eventually_ge_atTop 1))
  have hcov : ∀ n : ℕ, ∃ g : F, ∀ j, dint (y j * (x (i0 + n) - g.1)) ≤ 1 / 16 := by
    intro n
    obtain ⟨g, hg, h⟩ := hF (x (i0 + n)) ((hi0 _ (Nat.le_add_right _ _)).1)
    exact ⟨⟨g, hg⟩, h⟩
  choose g hg using hcov
  obtain ⟨n1, n2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → False := by
    intro a b hab he
    set i := i0 + a with hi
    set j := i0 + b with hj
    have hij : i < j := by omega
    have h1 := hg a j
    have h2 := hg b j
    rw [← he] at h2
    have h3 : dint (y j * x j - y j * x i) ≤ 1 / 8 := by
      have e : y j * x j - y j * x i =
          y j * (x (i0 + b) - (g a).1) - y j * (x (i0 + a) - (g a).1) := by
        rw [← hi, ← hj]
        ring
      rw [e]
      exact (dint_sub_le _ _).trans (by linarith)
    have hMi : 1 ≤ M i := le_trans (hi0 i (by omega)).2 (hM.id_le i)
    have hMij : M i < M j := hM hij
    have hMj : 1 ≤ M j := by omega
    have h4 : y j * x j = 1 / 2 := by
      rw [hy, hx]
      unfold dyseq
      simp only
      have e : (2 : ℝ) ^ M j = 2 ^ (M j - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [e]
      field_simp
    have h5 : dint (y j * x i) ≤ 1 / 4 := by
      refine (dint_le_abs _).trans ?_
      rw [abs_of_pos (mul_pos (hypos j) (by rw [hx]; positivity)), hy, dyseq_mul, hx,
        div_le_iff₀ (by positivity)]
      have e : (2 : ℝ) ^ M j = 2 ^ (M i - 1) * 2 ^ (M j - (M i - 1)) := by
        rw [← pow_add]
        congr 1
        omega
      have h6 : (4 : ℝ) ≤ 2 ^ (M j - (M i - 1)) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (M j - (M i - 1)) := pow_le_pow_right₀ one_le_two (by omega)
      have h7 : (0 : ℝ) < 2 ^ (M i - 1) := by positivity
      rw [e]
      nlinarith
    have h6 := dint_add_le' (y j * x j - y j * x i) (y j * x i)
    rw [sub_add_cancel] at h6
    have h7 : dint (y j * x j) = 1 / 2 := by rw [h4, dint_half]
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact key n1 n2 h heq
  · exact key n2 n1 h heq.symm

/-! ## The example -/

namespace Shadow

def r (i : ℕ) : ℕ := 4 ^ (i + 1)

def Mx (i : ℕ) : ℕ := r i * (r i + 1)

/-- `(n² - M_i)² + i` for `n > r_i`. -/
def S : Set ℕ := {c | ∃ i n, r i < n ∧ c = (n ^ 2 - Mx i) ^ 2 + i}

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
  set n := r 0 + Mx 0 + c + 1 with hn
  have h : r 0 < n := by omega
  refine ⟨(n ^ 2 - Mx 0) ^ 2 + 0, ⟨0, n, h, rfl⟩, ?_⟩
  have h1 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  have h2 : n ^ 2 - Mx 0 ≤ (n ^ 2 - Mx 0) ^ 2 := Nat.le_self_pow two_ne_zero _
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
  obtain ⟨i, n, hn, he⟩ := e_mem k
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

/-- Every coefficient of `δ` is a coefficient of the sequence `2^(-M_i)`. -/
lemma dominated (a : ℝ) (ha : InA (dyseq L) sT a) : InA (dyseq Mx) sT a := by
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ha ε hε)
  have h1 : ∀ᶠ i : ℕ in atTop, |a| * ((2 : ℝ)⁻¹) ^ r i ≤ ε := by
    have h2 : Tendsto (fun i : ℕ => |a| * ((2 : ℝ)⁻¹) ^ r i) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).comp
        r_mono.tendsto_atTop).const_mul |a|
      rwa [mul_zero] at this
    exact h2.eventually_le_const hε
  filter_upwards [h1, eventually_gt_atTop ((Finset.range K).sup I)] with i hi hiK n
  rcases le_or_gt (n + 1) (r i) with hn | hn
  · refine (dint_le_abs _).trans (le_trans ?_ hi)
    have h3 : (n + 1) ^ 2 + r i ≤ Mx i := by
      have h4 : (n + 1) ^ 2 ≤ r i ^ 2 := Nat.pow_le_pow_left hn 2
      have h5 : Mx i = r i ^ 2 + r i := by unfold Mx; ring
      omega
    have e1 : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := rfl
    rw [e1, abs_mul, abs_mul, abs_of_pos (show 0 < dyseq Mx i by unfold dyseq; positivity),
      abs_of_pos (show (0 : ℝ) < 2 ^ ((n + 1) ^ 2) by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    unfold dyseq
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity), inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity),
      ← pow_add]
    exact pow_le_pow_right₀ one_le_two h3
  · have hc : ((n + 1) ^ 2 - Mx i) ^ 2 + i ∈ S := ⟨i, n + 1, hn, rfl⟩
    obtain ⟨k, hk⟩ := e_surj hc
    have hD : D k = (n + 1) ^ 2 - Mx i := by
      unfold D
      rw [hk]
      exact code_sqrt hn
    have hI : I k = i := by
      unfold I
      rw [hD, hk]
      omega
    have hkK : K ≤ k := by
      by_contra h
      have := Finset.le_sup (f := I) (Finset.mem_range.2 (not_le.1 h))
      omega
    have hm1 : 1 ≤ m k := by have := m_ge k; omega
    have h6 := hK k hkK (m k - 1)
    have e1 : a * dyseq L k * sT (m k - 1) = a * dyseq Mx i * sT n := by
      have e2 : sT (m k - 1) = (2 : ℝ) ^ (m k ^ 2) := by
        show (2 : ℝ) ^ ((m k - 1 + 1) ^ 2) = _
        rw [Nat.sub_add_cancel hm1]
      have e3 : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := rfl
      have h7 := D_ge hn
      have h8 : m k ^ 2 + Mx i = L k + (n + 1) ^ 2 := by
        have := L_add k
        omega
      rw [e2, e3]
      unfold dyseq
      rw [mul_assoc, mul_assoc]
      congr 1
      rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity), ← pow_add,
        ← pow_add]
      congr 1
      omega
    rwa [e1] at h6

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

lemma not_rig : ¬ Rig (dyseq L) := not_rig_of_dominated L Mx Mx_mono dominated far

end Shadow

/-- **A sequence with a set of coefficients of dimension one that is not rigid.** -/
theorem exists_not_rig_dimH : ∃ L : ℕ → ℕ, StrictMono L ∧ 2 ≤ L 0 ∧ (∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1)) ∧
    Tendsto (fun k => L k - Nat.sqrt (L k) ^ 2) atTop atTop ∧
    (∀ k, k + 1 ≤ (Nat.log 2 ((Nat.sqrt (L k) + 1) ^ 2 - L k) + 1) *
      (Nat.sqrt ((Nat.sqrt (L k) + 1) ^ 2 - L k) + 2)) ∧
    dimH {a | InA (dyseq L) sT a} = 1 ∧ ¬ Rig (dyseq L) := by
  refine ⟨Shadow.L, Shadow.L_mono, Shadow.L_two, Shadow.gaps, Shadow.lower_gap, fun k => ?_,
    Shadow.dimH_coeff, Shadow.not_rig⟩
  rw [Shadow.upper_gap]
  exact Shadow.index_le k

end Three
end PVG
