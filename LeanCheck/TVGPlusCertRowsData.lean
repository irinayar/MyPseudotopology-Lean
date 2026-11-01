import LeanCheck.TVGPlusCertRows

/-!
# TVGplus: the five rows of the table of exact finite certificates

Each theorem `row_i` instantiates `gcd_cert`: the listed integers lie in the ball, their gcd is the universal
divisor `D`, hence (i) `D` divides every element of the ball and (ii) every common divisor of the ball divides `D`.
-/

namespace LeanCheck
namespace TVGPlus

lemma primes_235 : ∀ p ∈ ({2, 3, 5} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- Row 1: `S = {2, 3}`, radius `1/5`, `D = 6`, witnesses [66, 78]. -/
theorem row_1 :
    GcdStmt {2, 3} 5 (fun p => if p = 2 then 1 else 1) [66, 78] :=
  gcd_cert (S := {2, 3}) primes_23 (den := 5) (fun p => if p = 2 then 1 else 1)
    (by norm_num) (by decide) 5 27 6 (by norm_num) (by norm_num) [66, 78]
    (by decide +kernel) (by decide +kernel)

/-- Row 2: `S = {2, 3}`, radius `1/8`, `D = 48`, witnesses [480, 1056, 57840]. -/
theorem row_2 :
    GcdStmt {2, 3} 8 (fun p => if p = 2 then 2 else 1) [480, 1056, 57840] :=
  gcd_cert (S := {2, 3}) primes_23 (den := 8) (fun p => if p = 2 then 2 else 1)
    (by norm_num) (by decide) 481 4096 6 (by norm_num) (by norm_num) [480, 1056, 57840]
    (by decide +kernel) (by decide +kernel)

/-- Row 3: `S = {2, 3}`, radius `1/10`, `D = 48`, witnesses [480, 1056, 59376]. -/
theorem row_3 :
    GcdStmt {2, 3} 10 (fun p => if p = 2 then 2 else 1) [480, 1056, 59376] :=
  gcd_cert (S := {2, 3}) primes_23 (den := 10) (fun p => if p = 2 then 2 else 1)
    (by norm_num) (by decide) 385 4096 6 (by norm_num) (by norm_num) [480, 1056, 59376]
    (by decide +kernel) (by decide +kernel)

/-- Row 4: `S = {2, 3}`, radius `1/27`, `D = 1296`, witnesses [787968, 1180656]. -/
theorem row_4 :
    GcdStmt {2, 3} 27 (fun p => if p = 2 then 2 else 2) [787968, 1180656] :=
  gcd_cert (S := {2, 3}) primes_23 (den := 27) (fun p => if p = 2 then 2 else 2)
    (by norm_num) (by decide) 73791 2097152 6 (by norm_num) (by norm_num) [787968, 1180656]
    (by decide +kernel) (by decide +kernel)

/-- Row 5: `S = {2, 3, 5}`, radius `1/5`, `D = 30`, witnesses [1950, 3090]. -/
theorem row_5 :
    GcdStmt {2, 3, 5} 5 (fun p => if p = 2 then 1 else if p = 3 then 1 else 1) [1950, 3090] :=
  gcd_cert (S := {2, 3, 5}) primes_235 (den := 5) (fun p => if p = 2 then 1 else if p = 3 then 1 else 1)
    (by norm_num) (by decide) 49 256 6 (by norm_num) (by norm_num) [1950, 3090]
    (by decide +kernel) (by decide +kernel)

#print axioms row_1
#print axioms row_5

end TVGPlus
end LeanCheck
