import LeanCheck.TVGShiftedCert

/-!
# TVGplus: membership certificates for the lattice-reduction witnesses (m up to 5272)

Formal counterpart of the exact norm checks of the Codex note of 7 November 2026, 10:27 (audited by
Claude, 7 November): signed witnesses from the exact-rational lattice reduction, valid for the radii
`1/m` with `m` up to `990`, `1100`, `2114`, `2790` and `5272`.

`k ∈ Wsh {2} {3} δ` means `P_2(k - 1) < δ` and `P_3(k) < δ`, with `P_p = Pn (sqScales p)`. The certificates
use `CertOK` and `mem_Wsh_of_cert` of `TVGShiftedCert` (decidable, checked with `decide +kernel`).

These theorems are **membership statements only**: no minimality is claimed for these witnesses (the note
claims none), and the lattice-reduction search itself was computed outside Lean.
-/

namespace LeanCheck
namespace ShiftedCert

open LeanCheck.MixedPrime LeanCheck.TVGPlus LeanCheck.ShiftedJump

/-- signed witness from the exact-rational lattice reduction, 905 <= m <= 990: `P_2(k-1) = 22515128248780302922673350423205298319361 / 22300745198530623141535718272648361505980416`, `P_3(k) = 39365 / 43046721`; both are `< 1/990`. -/
theorem wit990_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 990 → (-5237266385854161081084648196260170729042365521068031 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-5237266385854161081084648196260170729042365521068031 : ℤ) 22515128248780302922673350423205298319361 22300745198530623141535718272648361505980416 13 39365 43046721 10 990 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- signed witness from the lattice reduction, m <= 1100: `P_2(k-1) = 30870233085 / 35184372088832`, `P_3(k) = 6930519895 / 7625597484987`; both are `< 1/1100`. -/
theorem wit1100_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 1100 → (-272376503938727098283040312347078210852019853412270079 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-272376503938727098283040312347078210852019853412270079 : ℤ) 30870233085 35184372088832 13 6930519895 7625597484987 10 1100 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- signed witness from the lattice reduction, m <= 2114: `P_2(k-1) = 16642973695 / 35184372088832`, `P_3(k) = 1 / 2187`; both are `< 1/2114`. -/
theorem wit2114_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 2114 → (-7809819341125605095274215063741174399601859353929596391221362687 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-7809819341125605095274215063741174399601859353929596391221362687 : ℤ) 16642973695 35184372088832 14 1 2187 11 2114 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- signed witness from the lattice reduction, m <= 2790: `P_2(k-1) = 3902335650103341869058812191510052863 / 10889035741470030830827987437816582766592`, `P_3(k) = 2682066899077518485135911891 / 10301051460877537453973547267843`; both are `< 1/2790`. -/
theorem wit2790_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 2790 → (-7634248104597266061823111224917440282646761781466539168379823935245516799 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-7634248104597266061823111224917440282646761781466539168379823935245516799 : ℤ) 3902335650103341869058812191510052863 10889035741470030830827987437816582766592 15 2682066899077518485135911891 10301051460877537453973547267843 12 2790 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

/-- signed witness from the lattice reduction, m <= 5272: `P_2(k-1) = 39012834762154542189570845173781609999294436301705711058945 / 205688069665150755269371147819668813122841983204197482918576128`, `P_3(k) = 531443 / 3486784401`; both are `< 1/5272`. -/
theorem wit5272_mem : ∀ m : ℕ, 1 ≤ m → m ≤ 5272 → (-3279399153231259550800930850710373986260418241510503641872065858591061934285791533150725210111 : ℤ) ∈ Wsh {2} {3} (1 / (m : ℝ)) :=
  mem_Wsh_of_cert (-3279399153231259550800930850710373986260418241510503641872065858591061934285791533150725210111 : ℤ) 39012834762154542189570845173781609999294436301705711058945 205688069665150755269371147819668813122841983204197482918576128 17 531443 3486784401 14 5272 (by decide +kernel) (by decide +kernel)
    (by norm_num) (by norm_num)

end ShiftedCert
end LeanCheck
