#!/bin/bash
# Reruns every computation of this folder and writes the results to outputs/.
# Run from anywhere:  bash scripts/run_all.sh
# Needs the .NET SDK 9 (the programs target .NET 8 and 9) and Perl.
# Memory below 1 GB; a few minutes in all on a desktop machine.
set -e
cd "$(dirname "$0")/.."
FIRST=../TwoPrimes_supplement
CERT=$FIRST/basis124/joint_gmp_float_D1000000000000000_s80_t101_h124.json
mkdir -p outputs
run() { local proj="$1"; shift; dotnet run -c Release --project "$proj" -- "$@" | tr -d '\r'; }

# Table "far": exact energy C (program crtpq of the first supplement), model energy and Gamma_D
# columns of the first list: p q D n m X   (n = level of q, m = level of p)
ROWS="2 11 7 X234881024
2 13 10 X335544320
2 13 11 X369098752
2 13 14 X469762048
2 13 17 X570425344
3 13 11 X473513931
3 13 14 X602654094
3 13 15 X645700815
5 13 8 X15625000
5 13 11 X21484375"
: > outputs/far_exact.txt
echo "$ROWS" | while read p q D X; do X=${X#X}
  PB=$p PT=$q run $FIRST/programs/crtpq $D $X 0 0 | grep -E '^(D=|C=)' >> outputs/far_exact.txt
done
: > outputs/far_model.txt
echo "p q D n m X : J_A J_B Ccont Gamma_D C_model" >> outputs/far_model.txt
while read p q D n m X; do
  echo "$p $q $D $n $m $X : $(run programs/unbal at $p $q $D $n $m $X)" >> outputs/far_model.txt
done <<'ROWS2'
2 11 7 3 6 234881024
2 13 10 3 6 335544320
2 13 11 3 6 369098752
2 13 14 3 6 469762048
2 13 17 3 6 570425344
3 13 11 3 5 473513931
3 13 14 3 5 602654094
3 13 15 3 5 645700815
5 13 8 3 4 15625000
5 13 11 3 4 21484375
ROWS2

# Heights with far-apart steps at large radii, for {2,3}. Each D is first raised to the next
# integer prime to 6; the label shows the argument as given.
: > outputs/large_D.txt
for x in 3.4 4.0; do
  echo "# x = $x" >> outputs/large_D.txt
  run programs/unbal 2 3 20 $x 1000 1000001 1000000007 1e15 1e30 1e60 1e100 1e200 >> outputs/large_D.txt
done

# Table "weighted" and the two-sided bounds: kappaD p q D s t
: > outputs/kappaD.txt
for a in "2 11 7 2 5" "2 13 10 2 5" "2 13 11 2 5" "2 13 14 2 5" "2 13 17 2 5" "3 13 11 2 4" "3 13 14 2 4" "3 13 15 2 4" \
         "5 13 8 2 3" "5 13 11 2 3" "2 3 8 3 5" "2 3 20 3 5" "2 3 80 4 7" "2 3 40 4 6" "2 3 8 4 5" "2 5 8 3 5"; do
  run programs/kappaD $a >> outputs/kappaD.txt
done
perl scripts/direct_kappaD.pl 2 13 17 2 5 | tr -d '\r' > outputs/kappaD_direct.txt

# Table "kappa": kappa p q D s t [direct]
: > outputs/kappa.txt
for a in "2 3 8 3 5 direct" "2 3 20 3 5 direct" "2 3 8 4 6" "2 3 20 4 6" "2 3 80 4 7" "2 3 160 4 8" "2 5 8 3 5 direct" \
         "2 7 20 3 6" "3 5 20 3 5" "3 7 20 3 5" "2 3 40 4 6" "2 3 8 4 5"; do
  run programs/kappa $a >> outputs/kappa.txt
done

# Table "multi" and the example without the cap: morem energy p q D s t M...
: > outputs/energy_multi.txt
run programs/morem energy 2 101 7 1 4 7 20 40 70      >> outputs/energy_multi.txt
run programs/morem energy 3 101 7 1 3 7 30 100 200 300 >> outputs/energy_multi.txt
run programs/morem energy 2 53 9 1 4 9 20 40 70       >> outputs/energy_multi.txt

# Block averages and kappa_M on formal digit products, and the conductor masses
: > outputs/kappa_M.txt
run programs/morem kappa 2 3 20 3 5 640 >> outputs/kappa_M.txt
run programs/morem kappa 2 3 40 3 5 320 >> outputs/kappa_M.txt
run programs/morem kappa 2 3 8 3 5 320  >> outputs/kappa_M.txt
run programs/morem kappa 2 5 8 3 5 160  >> outputs/kappa_M.txt
run programs/morem kappa 2 3 20 3 4 320 >> outputs/kappa_M.txt
: > outputs/conductor_masses.txt
for a in "3 8 4" "3 20 4" "5 8 3" "2 7 5"; do run programs/morem qp $a >> outputs/conductor_masses.txt; done

# Recomputation of the three low-conductor certificates and of the elementary bound
run programs/morem cert > outputs/lowcond_certificates.txt

# Explicit witnesses from the 124-dimensional certificate, and the data of the Lean module
run programs/witness17 "$PWD/$CERT" "$PWD/outputs/witness_unit.txt" > outputs/witness.txt
run programs/gencert "$PWD/$CERT" "$PWD/outputs/TwoPrimesBasisData.lean" > outputs/gencert.txt
echo done
