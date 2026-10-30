# Analytic joint-approximation formalization progress

The complete analytic joint-approximation theorem is **not yet formalized**.
The following two modules are new checked components. No new axiom, `sorry`, or
assumption that JA holds has been inserted to stand in for a missing proof.

## New checked components

| Declaration | Exact contribution and limitation |
|---|---|
| `cosine_series_summable` | Absolute summability of a nonnegative coefficient family implies summability after multiplication by bounded cosine phases. |
| `cosine_series_center_max` | The resulting infinite cosine series is bounded above by its value at zero. This extends the earlier finite-sum check, but does not itself construct the cascade Fourier representation. |
| `product_bound_with_exceptions` | A finite product is at most `B^K * exp C` if at most K exceptional factors are bounded by B and the remaining nonnegative excesses have sum at most C. The actual cascade must still be shown to satisfy those hypotheses. |
| `one_sub_sum_le_product` | For errors in [0,1], `1-sum e` is a lower bound for the product of `1-e`. |
| `product_lower_half` | The preceding product is at least 1/2 when the error sum is at most 1/2. |
| `relative_mass_product_bounds` | Relative factors between `1-e` and `1+e`, with a total error budget at most 1/2, have product between 1/2 and `exp(1/2)`. The concrete lift errors and their summability remain to be connected. |
| `geometric_sum_le_two` | A depth-independent geometric sum bound when the ratio lies in [0,1/2]. |
| `paired_geometric_sum` | A bound of `4*C` for even-length sums with the stated geometric majorants on each pair. |
| `paired_geometric_prefix` | The same bound for arbitrary finite prefixes of a nonnegative sequence. The actual cubic tail coefficients still need those majorants. |
| `square_level_gap` | The numerical spacing inequality for square levels with a base logarithm at least 1/4. No merged prime-period sequence or number-theoretic separation is assumed proved by this lemma. |
| `two_colour_three_level_span` | A same-colour gap condition forces a three-level span bound for two colours. Constructing and checking the actual merged square-power enumeration remains separate. |
| `finite_cover_of_bounded_packing` | A symmetric irreflexive relation whose finite separated sets have bounded cardinality admits a finite dominating set. This checks the finite maximal-packing argument; it neither proves the required arithmetic packing bound nor the compact-quotient criterion. |
| `finite_translation_orthogonality` | Exact finite cyclic-character bilinear orthogonality: summing the product of opposite-phase Fourier amplitudes cancels off-diagonal terms. The spatial lift formula, conjugate/norm-square specialization, normalization, and the complete averaged-cascade construction still require formal links. |

The first twelve declarations are in namespace `LeanCheck.MixedPrimeAnalytic`;
the last is in `LeanCheck.MixedPrimeAveraging`.

## Still required for a complete proof

1. Define the actual quartic periodic windows, finite spectral kernels, and normalized convolutions. Prove their positivity, means, Parseval normalization, second-difference estimates and cubic tails.
2. Connect the existing abstract far-field recursion and the new paired geometric estimates to these concrete kernels and the actual merged square-power levels.
3. Formalize the required Matveev lower bound for a nonzero linear form involving two fixed prime logarithms and a rational coefficient of varying height. A search of the installed Mathlib NumberTheory sources found no theorem by that name or the searched logarithmic-form/Baker terms. Coprime nonvanishing is already checked, but is not the quantitative lower bound.
4. Establish the uniform bounds for deep separated and close levels, count the boundedly many terminal exceptions, and prove summability uniformly over the selected periods. The new product lemma completes the final multiplication only after these estimates are available.
5. Prove the concrete finite random-translation averaging identity, lift-sum estimates and positive mass bounds, buffered-height selection, the weighted-energy/spectral-window inequality and support constraints.
6. Connect energy to a packing bound and the new finite-cover lemma. Formalize the quotient completeness/compactness and character-separation argument used to turn covers at every precision into JA. General compact abelian character separation is another substantial library dependency; finite abelian Pontryagin duality in Mathlib is not by itself the required theorem.
7. Prove the actual quantified statement `forall delta > 0, exists k : Int, P3 k < delta and P2 (k-1) < delta`, then feed it to the existing checked splitting implication.

These missing results are not postulated as axioms. They remain explicit work, and
no theorem named or advertised as a complete proof of JA has been added.

## Verification record

Both full module sources were independently checked with the installed Lean 4.35.0
compiler against the existing D-drive Mathlib build cache, without copying `.lake`
or downloading packages. Final module checks succeeded, and all 13 printed axiom
reports contain only `propext`, `Classical.choice`, `Quot.sound`.
Compiler logs and source hashes are saved outside the repository in the project
`tmp/ja_lean_formalization` directory. The aggregate imports were updated, but a full
rebuild of the complete historical library was not performed in this task.

These checked additions extend the earlier repository snapshot. The original
D-drive Lean source tree is unchanged. The article cites a fixed repository commit
and states the limits of this partial formalization.
