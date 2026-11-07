import LeanCheck.TVGShiftedJump

/-!
# TVGplus: exact membership certificates for shifted witnesses (m = 627 to 904)

Formal counterpart of the exact norm checks of `TVGplus_v23` (witnesses for `627 ≤ m ≤ 682`) and of the
Codex notes of 6 November 2026 (12:58, 15:13, 19:03: witnesses for `m` up to 714, 703 and 904).

Shifted problem: `k ∈ Wsh {2} {3} δ` means `P_2(k - 1) < δ` and `P_3(k) < δ`, with
`P_p = Pn (sqScales p)`, `P_p(x) = sup_{n ≥ 1} ‖x / p^(n²)‖`.

`CertOK p k num den N` is a decidable certificate for `P_p(k) ≤ num / den`:
for `1 ≤ n ≤ N` the nearest integer `m = ⌊(2k + q)/(2q)⌋`, `q = p^(n²)`, satisfies
`|k - m q| · den ≤ num · q`, and the tail `n > N` is covered by `|k| · den ≤ num · p^((N+1)²)`.
`Pn_sq_le` turns a certificate into the bound, `mem_Wsh_of_cert` into membership for all `m ≤ mmax`
(the radii `1/m`), using `num · mmax < den`.

Every theorem below states **membership only**: the witness lies in the shifted ball for each
listed `m`. The minimality of these witnesses (the exclusion searches, up to `10^44` with millions
of jumps) is not part of this file and was computed outside Lean.
-/

namespace LeanCheck
namespace ShiftedCert

open LeanCheck.MixedPrime LeanCheck.TVGPlus LeanCheck.ShiftedJump

/-- Decidable certificate for `P_p(k) ≤ num / den`. -/
def CertOK (p : ℕ) (k : ℤ) (num den N : ℕ) : Prop :=
  0 < den ∧
  (∀ n ∈ Finset.Icc 1 N,
    |k - ((2 * k + (p : ℤ) ^ (n ^ 2)) / (2 * (p : ℤ) ^ (n ^ 2))) * (p : ℤ) ^ (n ^ 2)| * (den : ℤ)
      ≤ (num : ℤ) * (p : ℤ) ^ (n ^ 2)) ∧
  |k| * (den : ℤ) ≤ (num : ℤ) * (p : ℤ) ^ ((N + 1) ^ 2)

instance (p : ℕ) (k : ℤ) (num den N : ℕ) : Decidable (CertOK p k num den N) := by
  unfold CertOK; infer_instance

lemma nrm_le_of_int {k q m : ℤ} (hq : 0 < q) {num den : ℕ} (hden : 0 < den)
    (h : |k - m * q| * (den : ℤ) ≤ (num : ℤ) * q) :
    nrm ((k : ℝ) / (q : ℝ)) ≤ (num : ℝ) / den := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  rw [nrm_eq]
  refine (round_le _ m).trans ?_
  have e : (k : ℝ) / q - m = ((k - m * q : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hq', div_le_div_iff₀ hq' hden']
  have : (|(k - m * q : ℤ)| : ℤ) * den ≤ num * q := h
  have h2 : ((|(k - m * q : ℤ)| : ℤ) : ℝ) * den ≤ (num : ℝ) * q := by exact_mod_cast this
  push_cast at h2 ⊢
  linarith

/-- A certificate gives the bound `P_p(k) ≤ num / den`. -/
lemma Pn_sq_le {p : ℕ} (hp : 2 ≤ p) {k : ℤ} {num den N : ℕ} (h : CertOK p k num den N) :
    Pn (sqScales p) k ≤ (num : ℝ) / den := by
  obtain ⟨hden, hcert, htail⟩ := h
  apply Pn_le (S := sqScales p) (sq_nonempty p)
  intro q hq
  obtain ⟨n, hn, rfl⟩ := hq
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  have hpz : (0 : ℤ) < (p : ℤ) ^ (n ^ 2) := by positivity
  by_cases hle : n ≤ N
  · have := hcert n (Finset.mem_Icc.2 ⟨hn, hle⟩)
    have h1 := nrm_le_of_int (k := k) (q := (p : ℤ) ^ (n ^ 2))
      (m := (2 * k + (p : ℤ) ^ (n ^ 2)) / (2 * (p : ℤ) ^ (n ^ 2))) hpz hden this
    simpa [Nat.cast_pow] using h1
  · have hle := not_le.1 hle
    have hQ : p ^ ((N + 1) ^ 2) ≤ p ^ (n ^ 2) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hQpos : 0 < p ^ ((N + 1) ^ 2) := pow_pos (by omega) _
    have h1 := nrm_big k hQpos hQ
    refine h1.trans ?_
    have hQr : (0 : ℝ) < ((p ^ ((N + 1) ^ 2) : ℕ) : ℝ) := by exact_mod_cast hQpos
    rw [div_le_div_iff₀ hQr hden']
    have h2 : (|k| : ℤ) * den ≤ num * ((p : ℤ) ^ ((N + 1) ^ 2)) := htail
    have h3 : (((|k| : ℤ) : ℝ)) * den ≤ (num : ℝ) * (((p : ℤ) ^ ((N + 1) ^ 2) : ℤ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h3 ⊢
    linarith

/-- A pair of certificates for `P_2(k-1)` and `P_3(k)` gives membership in the shifted ball at every
radius `1/m`, `1 ≤ m ≤ mmax`, provided `num · mmax < den` for both bounds. -/
theorem mem_Wsh_of_cert (k : ℤ) (n2 d2 N2 n3 d3 N3 mmax : ℕ)
    (h2 : CertOK 2 (k - 1) n2 d2 N2) (h3 : CertOK 3 k n3 d3 N3)
    (hl2 : n2 * mmax < d2) (hl3 : n3 * mmax < d3) :
    ∀ m : ℕ, 1 ≤ m → m ≤ mmax → k ∈ Wsh {2} {3} (1 / (m : ℝ)) := by
  intro m hm hmm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd2 : (0 : ℝ) < d2 := by exact_mod_cast h2.1
  have hd3 : (0 : ℝ) < d3 := by exact_mod_cast h3.1
  have hmr : (m : ℝ) ≤ mmax := by exact_mod_cast hmm
  have b2 := Pn_sq_le (by norm_num) h2
  have b3 := Pn_sq_le (by norm_num) h3
  have l2 : (n2 : ℝ) / d2 < 1 / m := by
    rw [div_lt_div_iff₀ hd2 hm']
    have : ((n2 * mmax : ℕ) : ℝ) < d2 := by exact_mod_cast hl2
    push_cast at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n2]
  have l3 : (n3 : ℝ) / d3 < 1 / m := by
    rw [div_lt_div_iff₀ hd3 hm']
    have : ((n3 * mmax : ℕ) : ℝ) < d3 := by exact_mod_cast hl3
    push_cast at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n3]
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact lt_of_le_of_lt b2 l2
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact lt_of_le_of_lt b3 l3

/-- from the forward minimum for 627 <= m <= 664: `P_2(k-1) = 29118195635835356762107 / 19342813113834066795298816`, `P_3(k) = 27873669177178869687616193384188 / 22528399544939174411840147874772641`; both are `< 1/664`. -/
theorem fwd627_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 664 → (66907291982889809579769849953882135494393857 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (66907291982889809579769849953882135494393857 : ℤ) 29118195635835356762107 19342813113834066795298816 12 27873669177178869687616193384188 22528399544939174411840147874772641 9 664 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- forward and least absolute height, 665 <= m <= 682: `P_2(k-1) = 24577 / 16777216`, `P_3(k) = 54677 / 43046721`; both are `< 1/682`. -/
theorem fwd665_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 682 → (178421516210482934465929494559209061458378753 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (178421516210482934465929494559209061458378753 : ℤ) 24577 16777216 12 54677 43046721 9 682 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- reflection 1-b of the least positive reversed witness, 665 <= m <= 682: `P_2(k-1) = 12287 / 8388608`, `P_3(k) = 20411 / 14348907`; both are `< 1/682`. -/
theorem rev665_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 682 → (-223014257629644121148604218508658631111606271 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-223014257629644121148604218508658631111606271 : ℤ) 12287 8388608 12 20411 14348907 9 682 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- forward and least absolute height, 683 <= m <= 714: `P_2(k-1) = 929663332837921263569147124498431 / 664613997892457936451903530140172288`, `P_3(k) = 1 / 729`; both are `< 1/714`. -/
theorem fwd683_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 714 → (223038646310390834811416967750970593196900353 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (223038646310390834811416967750970593196900353 : ℤ) 929663332837921263569147124498431 664613997892457936451903530140172288 12 1 729 9 714 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- reflection 1-b of the least positive reversed witness, 683 <= m <= 703: `P_2(k-1) = 1 / 1024`, `P_3(k) = 17271976710784373 / 12157665459056928801`; both are `< 1/703`. -/
theorem rev683_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 703 → (-245323044659160427845920760406465283677487103 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-245323044659160427845920760406465283677487103 : ℤ) 1 1024 12 17271976710784373 12157665459056928801 9 703 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- signed minimizing witness, 715 <= m <= 904: `P_2(k-1) = 87609327641937274902415361 / 79228162514264337593543950336`, `P_3(k) = 4433792579 / 7625597484987`; both are `< 1/904`. -/
theorem sgn715_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 904 → (-267606999048097958924495329266879805341564927 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-267606999048097958924495329266879805341564927 : ℤ) 87609327641937274902415361 79228162514264337593543950336 12 4433792579 7625597484987 9 904 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

end ShiftedCert
end LeanCheck
