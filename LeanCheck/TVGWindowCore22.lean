import LeanCheck.TVGWindowDef
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Decide
namespace LeanCheck.TVGSearch.WindowCore22
open LeanCheck.TVGSearch
local notation "ℕ" => Nat
theorem good_mod {p s m n k : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) (hs : s ≤ 1) :
    good p s m n (k % p ^ (n * n)) = good p s m n k := by
  unfold good
  have hQ : 2 ≤ p ^ (n * n) := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (Nat.pow_one p).symm
      _ ≤ p ^ (n * n) := Nat.pow_le_pow_right (by omega) (show 1 * 1 ≤ n * n from Nat.mul_le_mul hn hn)
  have key : ∀ (Q k s : ℕ), s ≤ Q → idist (k % Q + Q - s) Q = idist (k + Q - s) Q := by
    intro Q k s hsQ
    have h1 : k % Q + Q - s = k % Q + (Q - s) := by omega
    have h2 : k + Q - s = k + (Q - s) := by omega
    unfold idist
    rw [h1, h2, Nat.mod_add_mod]
  rw [key _ _ _ (by omega)]

theorem tree_complete {p s m : ℕ} (hp : 2 ≤ p) (hs : s ≤ 1) :
    ∀ n k, goodUpTo p s m n k = true → k % p ^ (n * n) ∈ tree p s m n := by
  intro n
  induction n with
  | zero => intro k _; simp [tree, Nat.mod_one]
  | succ n ih =>
    intro k hk
    simp only [goodUpTo, Bool.and_eq_true] at hk
    have hr := ih k hk.1
    let x := k % p ^ ((n + 1) * (n + 1))
    have hx : x = k % p ^ ((n + 1) * (n + 1)) := rfl
    have hdvd : p ^ (n * n) ∣ p ^ ((n + 1) * (n + 1)) :=
      Nat.pow_dvd_pow p (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))
    have hQpos : 0 < p ^ ((n + 1) * (n + 1)) := Nat.pow_pos (by omega)
    have hxlt : x < p ^ ((n + 1) * (n + 1)) := Nat.mod_lt _ hQpos
    have hxr : x % p ^ (n * n) = k % p ^ (n * n) := Nat.mod_mod_of_dvd _ hdvd
    have hgood : good p s m (n + 1) x = true := by
      rw [hx, good_mod hp (by omega) hs]; exact hk.2
    have hxeq : x % p ^ (n * n) + p ^ (n * n) * (x / p ^ (n * n)) = x := Nat.mod_add_div x _
    have hlt : x / p ^ (n * n) < p ^ ((n + 1) * (n + 1)) / p ^ (n * n) :=
      Nat.div_lt_div_of_lt_of_dvd hdvd hxlt
    unfold tree lift
    refine List.mem_flatMap.2 ⟨x % p ^ (n * n), by rw [hxr]; exact hr, ?_⟩
    refine List.mem_filter.2 ⟨List.mem_map.2 ⟨x / p ^ (n * n), List.mem_range.2 hlt, hxeq⟩, ?_⟩
    exact hgood

/-- Chinese remainder step: `k < P * Q`, `P * Pinv ≡ 1 (mod Q)`. -/
theorem searchSetup_spec {p q n2 n3 Pinv X : ℕ} (h : searchSetup p q n2 n3 Pinv X = true) :
    X < p ^ (n2 * n2) * q ^ (n3 * n3) ∧ (p ^ (n2 * n2) * Pinv) % q ^ (n3 * n3) = 1 % q ^ (n3 * n3) := by
  unfold searchSetup at h
  simpa using h

theorem mergeF_mem : ∀ (f : ℕ) (a b : List (ℕ × ℕ)) (x : ℕ × ℕ), x ∈ a ∨ x ∈ b → x ∈ mergeF f a b := by
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
        · simp only [mergeF, hle, ite_true]
          rcases h with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inl h))
          · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inr h))
        · simp only [mergeF, hle, ite_false]
          rcases h with h | h
          · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inl h))
          · rcases List.mem_cons.1 h with rfl | h
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih _ _ _ (Or.inr h))

theorem msortF_mem : ∀ (f : ℕ) (l : List (ℕ × ℕ)) (x : ℕ × ℕ), x ∈ l → x ∈ msortF f l := by
  intro f
  induction f with
  | zero => intro l x h; simpa [msortF] using h
  | succ f ih =>
    intro l x h
    by_cases hl : l.length ≤ 1
    · simpa [msortF, hl] using h
    · simp only [msortF, hl, ite_false]
      apply mergeF_mem
      have : x ∈ l.take (l.length / 2) ∨ x ∈ l.drop (l.length / 2) := by
        rw [← List.mem_append, List.take_append_drop]; exact h
      rcases this with h1 | h1
      · exact Or.inl (ih _ _ h1)
      · exact Or.inr (ih _ _ h1)

theorem sortedB_pw : ∀ l : List (ℕ × ℕ), sortedB l = true → List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) l := by
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
      · exact Nat.le_trans h.1 ((List.pairwise_cons.1 hy).1 z hz')

theorem takeWhile_mem_sorted : ∀ (ys : List (ℕ × ℕ)) (hi : ℕ) (x : ℕ × ℕ),
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
      have hzh : z.1 ≤ hi := Nat.le_trans hz hxh
      simp only [List.takeWhile, hzh]
      exact List.mem_cons_of_mem _ (ih (List.pairwise_cons.1 hpw).2 hx' hxh)

theorem window_mem : ∀ (C : List (ℕ × ℕ)) (lo hi : ℕ) (x : ℕ × ℕ),
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
      simp only [List.dropWhile, hy]
      exact ih (List.pairwise_cons.1 hpw).2 hx' hlo hhi
    · simp only [List.dropWhile, hy]
      exact takeWhile_mem_sorted _ hi x hpw hx hhi

theorem dropWhile_comp {α : Type} (p q : α → Bool) (h : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.dropWhile q).dropWhile p = l.dropWhile p := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hq : q a = true
    · simp [List.dropWhile, hq, h a hq, ih]
    · simp [List.dropWhile, hq]

theorem sweep_complete (P X : ℕ) (C : List (ℕ × ℕ)) (hC : List.Pairwise (fun a b : ℕ × ℕ => a.1 ≤ b.1) C) :
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
      simp only [hrX, ite_true]
      rw [List.mem_filterMap]
      refine ⟨x, window_mem C v (v + (X - r) / P) x hC hx hvx hxh, ?_⟩
      simp [hpos]
    · apply List.mem_append_right
      exact ih (C.dropWhile (fun p => decide (p.1 < v1))) v1 (List.pairwise_cons.1 hpw).2
        (List.pairwise_cons.1 hpw).1 rfl v r hmem x hx hvx hxh hrX hpos

theorem dropWhile_zero : ∀ l : List (ℕ × ℕ), l.dropWhile (fun p => decide (p.1 < 0)) = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.dropWhile]

theorem window_complete {p q sq m n2 n3 Pinv X : ℕ} (TP : List ℕ) (hq : 2 ≤ q) (hn3 : 1 ≤ n3)
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
      _ = q ^ 1 := (Nat.pow_one q).symm
      _ ≤ q ^ (n3 * n3) := Nat.pow_le_pow_right (by omega) (show 1 * 1 ≤ n3 * n3 from Nat.mul_le_mul hn3 hn3)
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
      _ = Q * P := Nat.mul_comm _ _
  have hPinv1 : (P * Pinv) % Q = 1 := by rw [hPinv]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨v, hv⟩ : ∃ v, v = (r * Pinv) % Q := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = ((k % Q) * Pinv) % Q := ⟨_, rfl⟩
  have e1 : (k * Pinv) % Q = u := by
    rw [hu, Nat.mul_mod k Pinv Q, Nat.mul_mod (k % Q) Pinv Q, Nat.mod_mod]
  have e2 : (k * Pinv) % Q = (v + t) % Q := by
    have hk' : k * Pinv = r * Pinv + t * (P * Pinv) := by
      calc k * Pinv = (r + P * t) * Pinv := by rw [hkeq]
        _ = r * Pinv + t * (P * Pinv) := by rw [Nat.add_mul, Nat.mul_comm P t, Nat.mul_assoc t P Pinv]
    have hB : (t * (P * Pinv)) % Q = t := by
      rw [Nat.mul_mod, hPinv1, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt htlt]
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
        have : t * P = P * t := Nat.mul_comm _ _
        omega
      have := (Nat.le_div_iff_mul_le hPpos).2 h'
      omega)
    (by omega)
    (by rw [hx1, Nat.add_sub_cancel_left]; omega)
  rw [hx1, Nat.add_sub_cancel_left, hkeq] at hmain
  exact hmain
theorem lift_mem {p s m n : ℕ} (hp : 2 ≤ p) (hs : s ≤ 1) {L : List ℕ} {k : ℕ}
    (hr : k % p ^ (n * n) ∈ L) (hg : good p s m (n + 1) k = true) :
    k % p ^ ((n + 1) * (n + 1)) ∈ lift p s m n L := by
  have hdvd : p ^ (n * n) ∣ p ^ ((n + 1) * (n + 1)) := Nat.pow_dvd_pow p (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))
  have hQpos : 0 < p ^ ((n + 1) * (n + 1)) := Nat.pow_pos (by omega)
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





theorem triple22_no_failed_coordinate {k : Nat}
    (h : ∀ n, 1 ≤ n →
      good 2 1 22 n k = true ∧ good 3 0 22 n k = true ∧ good 5 0 22 n k = true) :
    failsAny [(2, 1, 6), (3, 0, 5), (5, 0, 1)] 22 6 k = false := by
  have noFail {p s start : Nat} (hs : 1 ≤ start)
      (hg : ∀ n, 1 ≤ n → good p s 22 n k = true) :
      failsFrom p s 22 start 6 k = false := by
    unfold failsFrom
    rw [List.any_eq_false]
    intro j _
    rw [hg (start + j) (by omega)]
    decide
  simp [failsAny,
    noFail (p := 2) (s := 1) (start := 6) (by decide) (fun n hn => (h n hn).1),
    noFail (p := 3) (s := 0) (start := 5) (by decide) (fun n hn => (h n hn).2.1),
    noFail (p := 5) (s := 0) (start := 1) (by decide) (fun n hn => (h n hn).2.2)]


set_option maxHeartbeats 0 in
private theorem full_check :
    windowSliceCheck 2 3 1 0 [(5, 0)] 22 4 4 14148104
      1111607529308144 6 0 65536 = true := by decide +native

theorem triple22_no_smaller_integer {k : Nat}
    (hk : 1 ≤ k) (hbound : k < 1111607529308145)
    (h : ∀ n, 1 ≤ n →
      good 2 1 22 n k = true ∧ good 3 0 22 n k = true ∧ good 5 0 22 n k = true) :
    False := by
  have hp : goodUpTo 2 1 22 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).1, (h 2 (by decide)).1,
      (h 3 (by decide)).1, (h 4 (by decide)).1]
  have hq : goodUpTo 3 0 22 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).2.1, (h 2 (by decide)).2.1,
      (h 3 (by decide)).2.1, (h 4 (by decide)).2.1]
  have hr := tree_complete (by decide) (by decide) 4 k hp
  have hr' : k % 2 ^ (4 * 4) ∈ (tree 2 1 22 4).filter
      (fun r => decide (0 ≤ r ∧ r < 65536)) :=
    List.mem_filter.2 ⟨hr, by simp [show k % 65536 < 65536 from Nat.mod_lt _ (by decide)]⟩
  have h2 : k % 2 ^ (5 * 5) ∈ liftSlice 2 1 22 4 0 65536 :=
    lift_mem (by decide) (by decide) hr' (h 5 (by decide)).1
  have h3 := tree_complete (by decide) (by decide) 4 k hq
  have check := full_check
  unfold windowSliceCheck windowCheckAux at check
  simp only [Bool.and_eq_true, List.all_eq_true] at check
  obtain ⟨⟨hSR, hC⟩, hall⟩ := check
  have hc := window_complete (p := 2) (q := 3) (sq := 0) (m := 22)
    (n2 := 5) (n3 := 4) (Pinv := 14148104) (X := 1111607529308144)
    (liftSlice 2 1 22 4 0 65536) (by decide) (by decide) (by decide)
    hSR hC hk (Nat.le_of_lt_succ hbound) h2 h3
  have hf : failsAny [(2, 1, 6), (3, 0, 5), (5, 0, 1)] 22 6 k = true := hall k hc
  rw [triple22_no_failed_coordinate h] at hf
  exact Bool.noConfusion hf

#print axioms triple22_no_smaller_integer
end LeanCheck.TVGSearch.WindowCore22





