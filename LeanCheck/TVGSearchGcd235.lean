import LeanCheck.TVGPlusCertRows

set_option maxHeartbeats 0

namespace LeanCheck
namespace TVGPlus

lemma primes_235' : ∀ p ∈ ({2, 3, 5} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- `S = {2,3,5}`, radius `1/5`, `D = 30`, witnesses [1950, 3090] (all at most 3000000000). -/
theorem gcd235_5 :
    GcdStmt {2, 3, 5} 5 (fun p => if p = 2 then 1 else if p = 3 then 1 else 1) [1950, 3090] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 5) (fun p => if p = 2 then 1 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 98 512 3 (by norm_num) (by norm_num) [1950, 3090]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_5_le : ∀ k ∈ [1950, 3090], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/6`, `D = 30`, witnesses [3090, 3150] (all at most 3000000000). -/
theorem gcd235_6 :
    GcdStmt {2, 3, 5} 6 (fun p => if p = 2 then 1 else if p = 3 then 1 else 1) [3090, 3150] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 6) (fun p => if p = 2 then 1 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 3150 19683 3 (by norm_num) (by norm_num) [3090, 3150]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_6_le : ∀ k ∈ [3090, 3150], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/7`, `D = 30`, witnesses [138750, 198210] (all at most 3000000000). -/
theorem gcd235_7 :
    GcdStmt {2, 3, 5} 7 (fun p => if p = 2 then 1 else if p = 3 then 1 else 1) [138750, 198210] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 7) (fun p => if p = 2 then 1 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 85 625 4 (by norm_num) (by norm_num) [138750, 198210]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_7_le : ∀ k ∈ [138750, 198210], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/8`, `D = 240`, witnesses [1970640, 2027520, 3797520] (all at most 3000000000). -/
theorem gcd235_8 :
    GcdStmt {2, 3, 5} 8 (fun p => if p = 2 then 2 else if p = 3 then 1 else 1) [1970640, 2027520, 3797520] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 8) (fun p => if p = 2 then 2 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 2340 19683 4 (by norm_num) (by norm_num) [1970640, 2027520, 3797520]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_8_le : ∀ k ∈ [1970640, 2027520, 3797520], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/9`, `D = 240`, witnesses [130675680, 167838720, 168169440, 169866240, 300814320] (all at most 3000000000). -/
theorem gcd235_9 :
    GcdStmt {2, 3, 5} 9 (fun p => if p = 2 then 2 else if p = 3 then 1 else 1) [130675680, 167838720, 168169440, 169866240, 300814320] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 9) (fun p => if p = 2 then 2 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 2112 19683 5 (by norm_num) (by norm_num) [130675680, 167838720, 168169440, 169866240, 300814320]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_9_le : ∀ k ∈ [130675680, 167838720, 168169440, 169866240, 300814320], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/10`, `D = 240`, witnesses [169866240, 300814320] (all at most 3000000000). -/
theorem gcd235_10 :
    GcdStmt {2, 3, 5} 10 (fun p => if p = 2 then 2 else if p = 3 then 1 else 1) [169866240, 300814320] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 10) (fun p => if p = 2 then 2 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 1950 19683 5 (by norm_num) (by norm_num) [169866240, 300814320]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_10_le : ∀ k ∈ [169866240, 300814320], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/11`, `D = 240`, witnesses [300814320, 433713120] (all at most 3000000000). -/
theorem gcd235_11 :
    GcdStmt {2, 3, 5} 11 (fun p => if p = 2 then 2 else if p = 3 then 1 else 1) [300814320, 433713120] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 11) (fun p => if p = 2 then 2 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 1785 19683 5 (by norm_num) (by norm_num) [300814320, 433713120]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_11_le : ∀ k ∈ [300814320, 433713120], k ≤ 3000000000 := by decide

/-- `S = {2,3,5}`, radius `1/12`, `D = 240`, witnesses [601551840, 1507856880] (all at most 3000000000). -/
theorem gcd235_12 :
    GcdStmt {2, 3, 5} 12 (fun p => if p = 2 then 2 else if p = 3 then 1 else 1) [601551840, 1507856880] :=
  gcd_cert (S := {2, 3, 5}) primes_235' (den := 12) (fun p => if p = 2 then 2 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 6 81 5 (by norm_num) (by norm_num) [601551840, 1507856880]
    (by decide +kernel) (by decide +kernel)

theorem gcd235_12_le : ∀ k ∈ [601551840, 1507856880], k ≤ 3000000000 := by decide

end TVGPlus
end LeanCheck
