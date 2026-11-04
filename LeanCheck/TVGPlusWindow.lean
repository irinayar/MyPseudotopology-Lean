import Mathlib
import LeanCheck.TVGPlusSearchLeast
import LeanCheck.TVGWindowDef

/-!
# TVGplus: soundness of the sorted CRT window search

`window_none`: if `windowCheck` holds, no `k ∈ [1, X]` lies in the shifted ball of radius `1/m`.  The proof shows
that every such `k` is produced by the sweep (`window_complete`) and then fails at an explicit coordinate.
`least_of_window` adds a membership certificate and gives the least positive element.
-/

namespace LeanCheck
namespace TVGSearch

open MixedPrime

lemma mergeF_mem : ∀ (f : ℕ) (a b : List (ℕ × ℕ)) (x : ℕ × ℕ), x ∈ a ∨ x ∈ b → x ∈ mergeF f a b := by
  intro f
  induction f with
  | zero => intro a b x h; simpa [mergeF] using h
  | succ f ih =>
    intro a b x h
    cases a with
    | nil => simpa [mergeF] using h
    | cons x0 xs =>
      cases b with
      | nil => simpa [mergeF] using h
      | cons y0 ys =>
        by_cases hle : x0.1 ≤ y0.1
        · simp only [mergeF, hle, if_true]
          rcases h with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inl h))
          · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inr h))
        · simp only [mergeF, hle, if_false]
          rcases h with h | h
          · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inl h))
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inr h))

lemma msortF_mem : ∀ (f : ℕ) (l : List (ℕ × ℕ)) (x : ℕ × ℕ), x ∈ l → x ∈ msortF f l := by
  intro f
  induction f with
  | zero => intro l x h; simpa [msortF] using h
  | succ f ih =>
    intro l x h
    by_cases hl : l.length ≤ 1
    · simpa [msortF, hl] using h
    · simp only [msortF, hl, if_false]
      apply mergeF_mem
      have : x ∈ l.take (l.length / 2) ∨ x ∈ l.drop (l.length / 2) := by
        rw [← List.mem_append, List.take_append_drop]; exact h
      rcases this with h1 | h1
      · exact Or.inl (ih _ _ h1)
      · exact Or.inr (ih _ _ h1)

lemma sortedB_pw : ∀ l : List (ℕ × ℕ), sortedB l = true → List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) l := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons x t ih =>
    intro h
    cases t with
    | nil => exact List.pairwise_singleton _ _
    | cons y t' =>
      simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
      have hy := ih h.2
      refine List.pairwise_cons.2 ⟨?_, hy⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz'
      · exact h.1
      · exact le_trans h.1 ((List.pairwise_cons.1 hy).1 z hz')

lemma takeWhile_mem_sorted : ∀ (ys : List (ℕ × ℕ)) (hi : ℕ) (x : ℕ × ℕ),
    List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) ys → x ∈ ys → x.1 ≤ hi →
    x ∈ ys.takeWhile (fun p => decide (p.1 ≤ hi)) := by
  intro ys hi x
  induction ys with
  | nil => intro _ h; simp at h
  | cons z zs ih =>
    intro hpw hx hxh
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [List.takeWhile, hxh]
    · have hz : z.1 ≤ x.1 := (List.pairwise_cons.1 hpw).1 x hx'
      have hzh : z.1 ≤ hi := le_trans hz hxh
      simp only [List.takeWhile, decide_eq_true_eq, hzh, if_true]
      exact List.mem_cons_of_mem _ (ih (List.pairwise_cons.1 hpw).2 hx' hxh)

lemma window_mem : ∀ (C : List (ℕ × ℕ)) (lo hi : ℕ) (x : ℕ × ℕ),
    List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) C → x ∈ C → lo ≤ x.1 → x.1 ≤ hi →
    x ∈ (C.dropWhile (fun p => decide (p.1 < lo))).takeWhile (fun p => decide (p.1 ≤ hi)) := by
  intro C lo hi x
  induction C with
  | nil => intro _ h; simp at h
  | cons y ys ih =>
    intro hpw hx hlo hhi
    by_cases hy : y.1 < lo
    · have hxy : x ≠ y := by
        intro h; rw [h] at hlo; omega
      have hx' : x ∈ ys := (List.mem_cons.1 hx).resolve_left hxy
      simp only [List.dropWhile, decide_eq_true_eq, hy, if_true]
      exact ih (List.pairwise_cons.1 hpw).2 hx' hlo hhi
    · simp only [List.dropWhile, decide_eq_true_eq, hy, if_false]
      exact takeWhile_mem_sorted _ hi x hpw hx hhi

lemma dropWhile_comp {α : Type} (p q : α → Bool) (h : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.dropWhile q).dropWhile p = l.dropWhile p := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hq : q a = true
    · simp [List.dropWhile, hq, h a hq, ih]
    · simp [List.dropWhile, hq]

lemma sweep_complete (P X : ℕ) (C : List (ℕ × ℕ)) (hC : List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) C) :
    ∀ (SR rest : List (ℕ × ℕ)) (v0 : ℕ),
      List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) SR → (∀ a ∈ SR, v0 ≤ a.1) →
      rest = C.dropWhile (fun p => decide (p.1 < v0)) →
      ∀ v r, (v, r) ∈ SR → ∀ x ∈ C, v ≤ x.1 → x.1 ≤ v + (X - r) / P → r ≤ X → 1 ≤ r + P * (x.1 - v) →
        r + P * (x.1 - v) ∈ sweep P X rest SR := by
  intro SR
  induction SR with
  | nil => intro rest v0 _ _ _ v r h; simp at h
  | cons a tl ih =>
    intro rest v0 hpw hv0 hrest v r hvr x hx hvx hxh hrX hpos
    obtain ⟨v1, r1⟩ := a
    have hv01 : v0 ≤ v1 := hv0 (v1, r1) List.mem_cons_self
    have hrest' : rest.dropWhile (fun p => decide (p.1 < v1)) = C.dropWhile (fun p => decide (p.1 < v1)) := by
      rw [hrest]
      apply dropWhile_comp
      intro a ha
      simp only [decide_eq_true_eq] at ha ⊢
      omega
    simp only [sweep]
    rw [hrest']
    rcases List.mem_cons.1 hvr with heq | hmem
    · obtain ⟨hv, hr⟩ := Prod.mk.inj heq
      subst hv
      subst hr
      apply List.mem_append_left
      simp only [hrX, if_true]
      rw [List.mem_filterMap]
      refine ⟨x, window_mem C v (v + (X - r) / P) x hC hx hvx hxh, ?_⟩
      simp [hpos]
    · apply List.mem_append_right
      exact ih (C.dropWhile (fun p => decide (p.1 < v1))) v1 (List.pairwise_cons.1 hpw).2
        (List.pairwise_cons.1 hpw).1 rfl v r hmem x hx hvx hxh hrX hpos

lemma dropWhile_zero : ∀ l : List (ℕ × ℕ), l.dropWhile (fun p => decide (p.1 < 0)) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.dropWhile]

lemma window_complete {p q sq m n2 n3 Pinv X : ℕ} (TP : List ℕ) (hq : 2 ≤ q) (hn3 : 1 ≤ n3)
    (hsetup : searchSetup p q n2 n3 Pinv X = true)
    (hSR : sortedB (sortedRL TP (q ^ (n3 * n3)) Pinv) = true)
    (hC : sortedB (doubled (q ^ (n3 * n3)) (sortedU q sq m n3 (q ^ (n3 * n3)) Pinv)) = true)
    {k : ℕ} (hk1 : 1 ≤ k) (hkX : k ≤ X)
    (h2 : k % p ^ (n2 * n2) ∈ TP) (h3 : k % q ^ (n3 * n3) ∈ tree q sq m n3) :
    k ∈ sweep (p ^ (n2 * n2)) X (doubled (q ^ (n3 * n3)) (sortedU q sq m n3 (q ^ (n3 * n3)) Pinv))
      (sortedRL TP (q ^ (n3 * n3)) Pinv) := by
  obtain ⟨hX, hPinv⟩ := searchSetup_spec hsetup
  generalize hPdef : p ^ (n2 * n2) = P at *
  generalize hQdef : q ^ (n3 * n3) = Q at *
  have hQ2 : 2 ≤ Q := by
    rw [← hQdef]
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (n3 * n3) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hQpos : 0 < Q := by omega
  have hPpos : 0 < P := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h] at hX
    simp at hX
  obtain ⟨t, ht⟩ : ∃ t, t = k / P := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = k % P := ⟨_, rfl⟩
  have hkeq : r + P * t = k := by rw [hr, ht]; exact Nat.mod_add_div k P
  have htlt : t < Q := by
    rw [ht]
    apply (Nat.div_lt_iff_lt_mul hPpos).2
    calc k ≤ X := hkX
      _ < P * Q := hX
      _ = Q * P := mul_comm _ _
  have hPinv1 : (P * Pinv) % Q = 1 := by rw [hPinv]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨v, hv⟩ : ∃ v, v = (r * Pinv) % Q := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = ((k % Q) * Pinv) % Q := ⟨_, rfl⟩
  have e1 : (k * Pinv) % Q = u := by
    rw [hu, Nat.mul_mod k Pinv Q, Nat.mul_mod (k % Q) Pinv Q, Nat.mod_mod]
  have e2 : (k * Pinv) % Q = (v + t) % Q := by
    have hk' : k * Pinv = r * Pinv + t * (P * Pinv) := by
      calc k * Pinv = (r + P * t) * Pinv := by rw [hkeq]
        _ = r * Pinv + t * (P * Pinv) := by ring
    have hB : (t * (P * Pinv)) % Q = t := by
      rw [Nat.mul_mod, hPinv1, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt htlt]
    rw [hk', Nat.add_mod, hB, hv]
  have hut : u = (v + t) % Q := by rw [← e1, e2]
  have hvlt : v < Q := by rw [hv]; exact Nat.mod_lt _ hQpos
  have hrtree : r ∈ TP := by rw [hr]; exact h2
  have hvr : (v, r) ∈ sortedRL TP Q Pinv := by
    unfold sortedRL
    apply msortF_mem
    rw [List.mem_map]
    exact ⟨r, hrtree, by rw [hv]⟩
  have huS : (u, k % Q) ∈ sortedU q sq m n3 Q Pinv := by
    unfold sortedU
    apply msortF_mem
    rw [List.mem_map]
    exact ⟨k % Q, h3, by rw [hu]⟩
  obtain ⟨x, hxC, hx1⟩ : ∃ x ∈ doubled Q (sortedU q sq m n3 Q Pinv), x.1 = v + t := by
    by_cases hvt : v + t < Q
    · refine ⟨(u, k % Q), ?_, ?_⟩
      · unfold doubled; exact List.mem_append_left _ huS
      · show u = v + t
        rw [hut]; exact Nat.mod_eq_of_lt hvt
    · refine ⟨(u + Q, k % Q), ?_, ?_⟩
      · unfold doubled
        apply List.mem_append_right
        rw [List.mem_map]
        exact ⟨(u, k % Q), huS, rfl⟩
      · show u + Q = v + t
        have h1 : (v + t) % Q = v + t - Q := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hut, h1]
        omega
  have hCpw := sortedB_pw _ hC
  have hSRpw := sortedB_pw _ hSR
  have hmain := sweep_complete P X _ hCpw (sortedRL TP Q Pinv)
    (doubled Q (sortedU q sq m n3 Q Pinv)) 0 hSRpw (fun a _ => Nat.zero_le _) (dropWhile_zero _).symm
    v r hvr x hxC (by rw [hx1]; omega)
    (by
      rw [hx1]
      have h' : t * P ≤ X - r := by
        have : t * P = P * t := mul_comm _ _
        omega
      have := (Nat.le_div_iff_mul_le hPpos).2 h'
      omega)
    (by omega)
    (by rw [hx1, Nat.add_sub_cancel_left]; omega)
  rw [hx1, Nat.add_sub_cancel_left, hkeq] at hmain
  exact hmain

theorem window_none {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {m n2 n3 Pinv X N : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsp : sp ≤ 1) (hsq : sq ≤ 1) (hrest : ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hm : 0 < m) (hn2 : 1 ≤ n2) (hn3 : 1 ≤ n3)
    (hsetup : searchSetup p q n2 n3 Pinv X = true)
    (hcheck : windowCheck p q sp sq rest m n2 n3 Pinv X N = true) :
    ∀ k : ℕ, 1 ≤ k → k ≤ X → ¬ ShiftedIn ((p, sp) :: (q, sq) :: rest) m k := by
  unfold windowCheck windowCheckAux at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨⟨hSR, hC⟩, hall⟩ := hcheck
  intro k hk1 hkX hball
  have hp' : Pn (sqScales p) ((k : ℤ) - sp) < 1 / (m : ℝ) := hball (p, sp) (by simp)
  have hq' : Pn (sqScales q) ((k : ℤ) - sq) < 1 / (m : ℝ) := hball (q, sq) (by simp)
  have hgp := goodUpTo_of_inBall hp hm (show sp ≤ k by omega) hp' n2
  have hgq := goodUpTo_of_inBall hq hm (show sq ≤ k by omega) hq' n3
  have h2 := tree_complete hp hsp n2 k hgp
  have h3 := tree_complete hq hsq n3 k hgq
  have hmem := window_complete (tree p sp m n2) hq hn3 hsetup hSR hC hk1 hkX h2 h3
  have hf := hall k hmem
  have hts : ∀ t ∈ (p, sp, n2 + 1) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1)),
      2 ≤ t.1 ∧ t.2.1 ≤ 1 ∧ 1 ≤ t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨u, hu, rfl⟩
    · exact ⟨hp, hsp, by show 1 ≤ n2 + 1; omega⟩
    · exact ⟨hq, hsq, by show 1 ≤ n3 + 1; omega⟩
    · exact ⟨(hrest u hu).1, (hrest u hu).2, le_refl _⟩
  obtain ⟨t, htm, hnot⟩ := failsAny_spec hts hm hk1 hf
  apply hnot
  simp only [List.mem_cons, List.mem_map] at htm
  rcases htm with rfl | rfl | ⟨u, hu, rfl⟩
  · exact hp'
  · exact hq'
  · exact hball u (by simp [hu])

theorem least_of_window {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {lo hi u X n2 n3 Pinv N ca cb Nm : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : sp ≤ 1 ∧ sq ≤ 1 ∧ ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hn : 1 ≤ n2 ∧ 1 ≤ n3) (hlohi : 0 < lo ∧ lo ≤ hi) (hX : X + 1 = u) (hu : 1 ≤ u)
    (hsetup : searchSetup p q n2 n3 Pinv X = true)
    (hcheck : windowCheck p q sp sq rest lo n2 n3 Pinv X N = true)
    (hc : ca * hi < cb ∧ 0 < cb)
    (hmem : memAll ((p, sp) :: (q, sq) :: rest) u ca cb Nm = true) :
    LeastOn ((p, sp) :: (q, sq) :: rest) lo hi u := by
  have hl : ∀ t ∈ (p, sp) :: (q, sq) :: rest, 2 ≤ t.1 ∧ t.2 ≤ 1 := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨hp, hs.1⟩
    · exact ⟨hq, hs.2.1⟩
    · exact hs.2.2 t ht
  have hmem' := memAll_spec hl hu hc.2 hmem
  have hnone := window_none hp hq hs.1 hs.2.1 hs.2.2 hlohi.1 hn.1 hn.2 hsetup hcheck
  refine ⟨hu, fun m h1 h2 => ⟨?_, ?_⟩⟩
  · intro t ht
    have hcb' : (0 : ℝ) < cb := by exact_mod_cast hc.2
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlt : (ca : ℝ) / cb < 1 / (m : ℝ) := by
      rw [div_lt_div_iff₀ hcb' hm']
      have : ((ca * hi : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc.1
      have hmh : (m : ℝ) ≤ hi := by exact_mod_cast h2
      have hca : (0 : ℝ) ≤ ca := by positivity
      push_cast at this
      nlinarith
    exact lt_of_le_of_lt (hmem' t ht) hlt
  · intro k hk1 hku hball
    exact hnone k hk1 (by omega) (ShiftedIn_mono hlohi.1 h1 hball)

lemma lift_mem {p s m n : ℕ} (hp : 2 ≤ p) (hs : s ≤ 1) {L : List ℕ} {k : ℕ}
    (hr : k % p ^ (n * n) ∈ L) (hg : good p s m (n + 1) k = true) :
    k % p ^ ((n + 1) * (n + 1)) ∈ lift p s m n L := by
  have hdvd : p ^ (n * n) ∣ p ^ ((n + 1) * (n + 1)) := pow_dvd_pow p (by nlinarith)
  have hQpos : 0 < p ^ ((n + 1) * (n + 1)) := pow_pos (by omega) _
  have hxlt : k % p ^ ((n + 1) * (n + 1)) < p ^ ((n + 1) * (n + 1)) := Nat.mod_lt _ hQpos
  have hxr : (k % p ^ ((n + 1) * (n + 1))) % p ^ (n * n) = k % p ^ (n * n) :=
    Nat.mod_mod_of_dvd _ hdvd
  have hgood : good p s m (n + 1) (k % p ^ ((n + 1) * (n + 1))) = true := by
    rw [good_mod hp (by omega) hs]; exact hg
  have hxeq : (k % p ^ ((n + 1) * (n + 1))) % p ^ (n * n)
      + p ^ (n * n) * ((k % p ^ ((n + 1) * (n + 1))) / p ^ (n * n)) = k % p ^ ((n + 1) * (n + 1)) :=
    Nat.mod_add_div _ _
  have hlt : (k % p ^ ((n + 1) * (n + 1))) / p ^ (n * n) < p ^ ((n + 1) * (n + 1)) / p ^ (n * n) :=
    Nat.div_lt_div_of_lt_of_dvd hdvd hxlt
  unfold lift
  refine List.mem_flatMap.2 ⟨(k % p ^ ((n + 1) * (n + 1))) % p ^ (n * n), by rw [hxr]; exact hr, ?_⟩
  refine List.mem_filter.2 ⟨List.mem_map.2 ⟨(k % p ^ ((n + 1) * (n + 1))) / p ^ (n * n),
    List.mem_range.2 hlt, hxeq⟩, ?_⟩
  exact hgood

/-- Nothing in `[1, X]` with level-`n1` residue in `[lo, hi)` lies in the ball. -/
def NoneSlice (p q sp sq : ℕ) (rest : List (ℕ × ℕ)) (m n1 X lo hi : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ X → lo ≤ k % p ^ (n1 * n1) → k % p ^ (n1 * n1) < hi →
    ¬ ShiftedIn ((p, sp) :: (q, sq) :: rest) m k

lemma NoneSlice_trans {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {m n1 X a b c : ℕ}
    (h1 : NoneSlice p q sp sq rest m n1 X a b) (h2 : NoneSlice p q sp sq rest m n1 X b c) :
    NoneSlice p q sp sq rest m n1 X a c := by
  intro k hk1 hkX hlo hhi
  by_cases hb : k % p ^ (n1 * n1) < b
  · exact h1 k hk1 hkX hlo hb
  · exact h2 k hk1 hkX (by omega) hhi

theorem slice_none {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {m n1 n3 Pinv X N lo hi : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsp : sp ≤ 1) (hsq : sq ≤ 1) (hrest : ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hm : 0 < m) (hn3 : 1 ≤ n3)
    (hsetup : searchSetup p q (n1 + 1) n3 Pinv X = true)
    (hcheck : windowSliceCheck p q sp sq rest m n1 n3 Pinv X N lo hi = true) :
    NoneSlice p q sp sq rest m n1 X lo hi := by
  unfold windowSliceCheck windowCheckAux at hcheck
  simp only [Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨⟨hSR, hC⟩, hall⟩ := hcheck
  intro k hk1 hkX hlo hhi hball
  have hp' : Pn (sqScales p) ((k : ℤ) - sp) < 1 / (m : ℝ) := hball (p, sp) (by simp)
  have hq' : Pn (sqScales q) ((k : ℤ) - sq) < 1 / (m : ℝ) := hball (q, sq) (by simp)
  have hgp := goodUpTo_of_inBall hp hm (show sp ≤ k by omega) hp' (n1 + 1)
  have hgq := goodUpTo_of_inBall hq hm (show sq ≤ k by omega) hq' n3
  simp only [goodUpTo, Bool.and_eq_true] at hgp
  have h5 := tree_complete hp hsp n1 k hgp.1
  have h5' : k % p ^ (n1 * n1) ∈ (tree p sp m n1).filter (fun r => decide (lo ≤ r ∧ r < hi)) :=
    List.mem_filter.2 ⟨h5, by simp [hlo, hhi]⟩
  have h2 : k % p ^ ((n1 + 1) * (n1 + 1)) ∈ liftSlice p sp m n1 lo hi :=
    lift_mem hp hsp h5' hgp.2
  have h3 := tree_complete hq hsq n3 k hgq
  have hmem := window_complete (liftSlice p sp m n1 lo hi) hq hn3 hsetup hSR hC hk1 hkX h2 h3
  have hf := hall k hmem
  have hts : ∀ t ∈ (p, sp, n1 + 2) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1)),
      2 ≤ t.1 ∧ t.2.1 ≤ 1 ∧ 1 ≤ t.2.2 := by
    intro t ht
    simp only [List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨u, hu, rfl⟩
    · exact ⟨hp, hsp, by show 1 ≤ n1 + 2; omega⟩
    · exact ⟨hq, hsq, by show 1 ≤ n3 + 1; omega⟩
    · exact ⟨(hrest u hu).1, (hrest u hu).2, le_refl _⟩
  obtain ⟨t, htm, hnot⟩ := failsAny_spec hts hm hk1 hf
  apply hnot
  simp only [List.mem_cons, List.mem_map] at htm
  rcases htm with rfl | rfl | ⟨u, hu, rfl⟩
  · exact hp'
  · exact hq'
  · exact hball u (by simp [hu])

theorem least_of_slices {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {lo hi u X n1 : ℕ}
    {ca cb Nm : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : sp ≤ 1 ∧ sq ≤ 1 ∧ ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hlohi : 0 < lo ∧ lo ≤ hi) (hX : X + 1 = u) (hu : 1 ≤ u)
    (hnone : NoneSlice p q sp sq rest lo n1 X 0 (p ^ (n1 * n1)))
    (hc : ca * hi < cb ∧ 0 < cb)
    (hmem : memAll ((p, sp) :: (q, sq) :: rest) u ca cb Nm = true) :
    LeastOn ((p, sp) :: (q, sq) :: rest) lo hi u := by
  have hl : ∀ t ∈ (p, sp) :: (q, sq) :: rest, 2 ≤ t.1 ∧ t.2 ≤ 1 := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨hp, hs.1⟩
    · exact ⟨hq, hs.2.1⟩
    · exact hs.2.2 t ht
  have hmem' := memAll_spec hl hu hc.2 hmem
  have hpos : 0 < p ^ (n1 * n1) := pow_pos (by omega) _
  refine ⟨hu, fun m h1 h2 => ⟨?_, ?_⟩⟩
  · intro t ht
    have hcb' : (0 : ℝ) < cb := by exact_mod_cast hc.2
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlt : (ca : ℝ) / cb < 1 / (m : ℝ) := by
      rw [div_lt_div_iff₀ hcb' hm']
      have : ((ca * hi : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc.1
      have hmh : (m : ℝ) ≤ hi := by exact_mod_cast h2
      have hca : (0 : ℝ) ≤ ca := by positivity
      push_cast at this
      nlinarith
    exact lt_of_le_of_lt (hmem' t ht) hlt
  · intro k hk1 hku hball
    exact hnone k hk1 (by omega) (Nat.zero_le _) (Nat.mod_lt _ hpos)
      (ShiftedIn_mono hlohi.1 h1 hball)

#print axioms slice_none
#print axioms least_of_slices
#print axioms window_none
#print axioms least_of_window

end TVGSearch
end LeanCheck
