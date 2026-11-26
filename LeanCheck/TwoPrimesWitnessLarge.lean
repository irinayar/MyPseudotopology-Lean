import LeanCheck.TwoPrimesWitness

/-!
# One explicit unit-target witness at a very small radius, and the rounding step behind it

* `rounding`: if the rows of a nonsingular integer matrix lie in the congruence lattice of the
  weights `w` modulo `u`, then every residue has a representation `Σ d j * w j` with
  `2 |d j| ≤ Σ i |B i j|`.
* `unit_witness_large`: an explicit integer `witness` with about 3032 decimal digits satisfies
  `P₃(witness) < 1/D` and `P₂(witness - 1) < 1/D` for `D = 1.7 * 10^18`, with `|witness| < 2^10071`.

The integer was obtained by rounding in a lattice basis of dimension 124.  Its verification here
does not depend on how it was found.  Minimality is not claimed.
-/

namespace TwoPrimesWitnessLarge

open TwoPrimesWitness Matrix

/-- Rounding in a basis of a sublattice of the congruence lattice. -/
theorem rounding {h : ℕ} (B : Matrix (Fin h) (Fin h) ℤ) (w z : Fin h → ℤ) (u c : ℤ)
    (hrow : ∀ i, u ∣ ∑ j, B i j * w j) (hdet : B.det ≠ 0) (hz : u ∣ (∑ j, z j * w j) - c) :
    ∃ d : Fin h → ℤ, u ∣ (∑ j, d j * w j) - c ∧ ∀ j, 2 * |d j| ≤ ∑ i, |B i j| := by
  classical
  set B' : Matrix (Fin h) (Fin h) ℚ := B.map (Int.castRingHom ℚ) with hB'
  have hdet' : IsUnit B'.det := by
    have e : B'.det = ((B.det : ℤ) : ℚ) := by
      rw [hB']
      exact ((Int.castRingHom ℚ).map_det B).symm
    rw [e, isUnit_iff_ne_zero]
    exact_mod_cast hdet
  set x : Fin h → ℚ := Matrix.vecMul (fun j => (z j : ℚ)) B'⁻¹ with hx
  have hxB : Matrix.vecMul x B' = fun j => (z j : ℚ) := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul B' hdet', Matrix.vecMul_one]
  set n : Fin h → ℤ := fun i => round (x i) with hn
  refine ⟨fun j => z j - ∑ i, n i * B i j, ?_, fun j => ?_⟩
  · have e : (∑ j, (z j - ∑ i, n i * B i j) * w j) - c
        = ((∑ j, z j * w j) - c) - ∑ i, n i * ∑ j, B i j * w j := by
      have e2 : ∑ j, (∑ i, n i * B i j) * w j = ∑ i, n i * ∑ j, B i j * w j := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [e2]; ring
    rw [e]
    exact dvd_sub hz (Finset.dvd_sum (fun i _ => Dvd.dvd.mul_left (hrow i) _))
  · have hzj : (z j : ℚ) = ∑ i, x i * (B i j : ℚ) := by
      have := congrFun hxB j
      simp only [Matrix.vecMul, dotProduct, hB', Matrix.map_apply, eq_intCast] at this
      exact this.symm
    have key : (((z j - ∑ i, n i * B i j : ℤ)) : ℚ) = ∑ i, (x i - n i) * (B i j : ℚ) := by
      push_cast
      rw [hzj, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have bound : 2 * |(((z j - ∑ i, n i * B i j : ℤ)) : ℚ)| ≤ ∑ i, |(B i j : ℚ)| := by
      rw [key]
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul, ← mul_assoc]
      have h1 : |x i - n i| ≤ 1 / 2 := abs_sub_round (x i)
      have h2 : 2 * |x i - n i| ≤ 1 := by linarith
      calc 2 * |x i - n i| * |(B i j : ℚ)| ≤ 1 * |(B i j : ℚ)| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = |(B i j : ℚ)| := one_mul _
    exact_mod_cast bound

/-- The absolute value of the witness. -/
def witnessAbs : ℕ :=
  43209707160749956645433869096894990668984640724749557900900298488796609112683690802901367296640895298933809787578512560391266227369869137603427542948043816345047564046549846770587913857262339035033064552502697044616138240606220279937180485543667222945490876352842427319746580585581955651923758797309094258475159515810973925534714795418089586740709884324261934528341786842383905987711543351685567422389419351885298468761859421652453092016695760348776410277423800457837278918488095464262369864323744349979821059127942666846953114412664422602183012980265469285857617104259473514590294666159438244087277263862952857013815333525498302989903732822590289706452791650681934257197984409040868714101170062514957212340758044925271756442081609122573257565866641394863186835463531071310087537062834300082421905259247444371542917219324398747707795595615064012723177091812399747596013314155499695014838446451834890593772426640739989017258447908274166263456046549497316998475100298818479253365421837466578455566648879033738735097858684607053074912981787483659996166321988839587215473772066415866640147250884518205273598412917776172422669323809943887852656498408933231685318350499254758368505744069973790296689245415373341745822553271270582139017400762918626360814391993197014418702788406774927742740749905664893288012654386234459835200699997223094932357013278347672059528768617231653323895442387990662918683418147433320165240350435854704850447944729266062017869653690960061265293923639060631230729551733716649221206696133266451318165814742737998891785478006657090263380154326681183505397854540100472414829117092030423134033693319601959814095361153436780177228870968538595981044579742375215867376383165577136146058120213240718145316146285277322608630064949671072469229432289875776119963494102126395349233316523930033303289693638409011954342626902941899264444524278576427333009222144117437158200223516984569815255367089099819575070182206930976131846616835887347715513807009606615631157442036307001470476087803661395514352040341905567278395032697637193307999255628282644683601284255425837893814227884461857359148385837705392184623335574077853848026296990880179378140230826432596031522071366609771077970207236379009386729575674234154019499339065896371098096504420555011264099735664504641454270604334144517717920370466704915458945209657037721922053459640982091695209958025119560181208744470282844148368888229977365547162597198909079712242558104980833842311185175549486246348950405509098920962170034494746423936113466641853899944899678515968038653582253482921591242478912282695636188153884852726954945704163734291374123145932055078152834300820661568223302411568252609376501249011795834388083900562325766198016408409111589327436652539586918649414059651421879297779916649976835237101259094061615873150623183473870537282192337311109684404292178775718990725501185462226090605868129474539688524783844782317028044251478240429362441188632698932921362130774588769126202361535812577102389617350757225727250020493613269525334332267017839618179376000441764116692991

/-- The witness. -/
def witness : ℤ := -(witnessAbs : ℤ)

/-- The radius parameter. -/
def D : ℕ := 1700000000000000000

theorem check_three : check 3 D witnessAbs 80 = true := by decide +kernel

theorem check_two : check 2 D (witnessAbs + 1) 100 = true := by decide +kernel

theorem witness_bound : witnessAbs < 2 ^ 10071 := by decide +kernel

/-- **An explicit unit-target witness** at the radius `1/D`, `D = 1.7 * 10^18`. -/
theorem unit_witness_large :
    Small 3 D witness ∧ Small 2 D (witness - 1) ∧ witness.natAbs < 2 ^ 10071 := by
  have h0 : witness.natAbs = witnessAbs := by simp [witness]
  have h1 : (witness - 1).natAbs = witnessAbs + 1 := by unfold witness; omega
  refine ⟨small_of_check (by norm_num) h0 check_three,
    small_of_check (by norm_num) h1 check_two, ?_⟩
  rw [h0]; exact witness_bound

end TwoPrimesWitnessLarge
