import LeanCheck.TwoPrimesFejer
import LeanCheck.TwoPrimesUnimodal
import LeanCheck.TwoPrimesCutBall

/-!
# Axiom report for TwoPrimesFejer, TwoPrimesUnimodal, TwoPrimesCutBall

Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.TwoPrimes.eq_of_modEq_of_mem_Icc
#print axioms LeanCheck.TwoPrimes.card_congr_pairs
#print axioms LeanCheck.TwoPrimes.unimodal_sum_le_integral_add_max
#print axioms LeanCheck.TwoPrimes.cluster_mid_card_le_one
#print axioms LeanCheck.TwoPrimes.cut_count_bounds
