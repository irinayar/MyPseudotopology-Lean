# TwoPrimesII: computational supplement

Programs and their output for the article

I. Yaroshevskaya, *Energy Criteria and Exact Certificates for Two Prime-Square Metrics*.

Throughout, `P_p(k) = sup_{n >= 1} || k / p^(n^2) ||`.

This folder uses two items of the supplement of the first article, in `../TwoPrimes_supplement`:
the program `programs/crtpq` (exact collision energy) and the certificate matrix in `basis124`.

## What these computations establish

* The tables are **computer-assisted evidence**. They are not proofs of the asymptotic claims,
  and the radii in them are far below the ranges of the theorems.
* **Exact** below means integer arithmetic. **Floating** means double precision, without a
  rigorous error bound.
* The Lean modules of the repository are separate; these programs are not formally verified.

## Programs

| Program | Computes | Where in the article | Arithmetic |
|---|---|---|---|
| `../TwoPrimes_supplement/programs/crtpq` | exact energy `C` at the heights `X = Dv` | table of far-apart heights | exact |
| `programs/unbal` | `J_A`, `J_B`, the model energy and the bound `Gamma_D`; heights with `v >= 20Du` for `{2,3}` up to `D = 10^200` | same table; the paragraph on large radii | heights exact, bounds floating |
| `programs/kappa` | the collision quantity `kappa` as a Fourier sum (optionally by direct counting) | table of `kappa` | floating |
| `programs/kappaD` | the weighted quantity `kappa_D` and the two-sided bounds for the energy | table of the weighted quantity | floating |
| `scripts/direct_kappaD.pl` | `kappa_D` by direct counting, one case | check of `kappaD` | floating |
| `programs/morem` `energy` | the two balls listed from the definition, energy by a Fourier transform | table of heights with more top clusters; the example without the cap | floating transform, results rounded to integers |
| `programs/morem` `kappa` | block averages and `kappa_M` on formal digit products | the paragraph on longer blocks | floating |
| `programs/morem` `qp` | conductor masses of one digit set against direct counting | check of the closed formula | floating |
| `programs/morem` `cert` | recomputation of the three low-conductor certificates | table of certificates | exact |
| `programs/witness17` | explicit witnesses from the 124-dimensional matrix, with exact checks of the uniform bounds | the section on the short basis | witnesses and the lines marked `exact` are exact |
| `programs/gencert` | the data file of the Lean module `TwoPrimesBasisData` from the matrix | formal verification | exact |

The program which found the 124-dimensional matrix is not part of this supplement. Nothing here
depends on how the matrix was found: its properties are checked.

## Running

Needs the .NET SDK 9 (the programs target .NET 8 and 9) and Perl. From this folder:

```sh
bash scripts/run_all.sh
```

This rewrites `outputs/`. It needs less than 1 GB of memory and a few minutes on a desktop
machine. Single runs, for example:

```sh
dotnet run -c Release --project programs/kappaD -- 2 3 40 4 6        # p q D s t
dotnet run -c Release --project programs/morem -- energy 2 101 7 1 4 7 20 40 70
```

In the arguments `p q D s t`, `s` and `t` are the numbers of lower levels of `q` and of `p`,
so that `u = q^(s^2)` and `v = p^(t^2)`.

## Files in `outputs/`

| File | Content |
|---|---|
| `far_exact.txt`, `far_model.txt` | the ten rows of the table of far-apart heights |
| `large_D.txt` | heights and `Gamma_D` at large radii |
| `kappaD.txt`, `kappaD_direct.txt` | weighted quantity and bounds |
| `kappa.txt` | table of `kappa` |
| `energy_multi.txt` | heights with more top clusters, and without the cap |
| `kappa_M.txt`, `conductor_masses.txt` | formal digit products |
| `lowcond_certificates.txt` | the three certificates |
| `witness.txt`, `witness_unit.txt` | explicit witnesses; the integer for target 1 |
| `gencert.txt` | summary of the Lean data generator |

The generator also writes `outputs/TwoPrimesBasisData.lean`, which is not stored here: apart from
the header comment it equals `LeanCheck/TwoPrimesBasisData.lean`.
