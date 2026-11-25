use strict; use warnings; use Math::BigInt;
sub ln { my $x = shift; my $s = $x->bstr; my $len = length $s; my $lead = substr($s,0,15); return log($lead) + ($len-15 > 0 ? ($len-15)*log(10) : 0) - (($len<15)? 0:0); }
sub lg { my $x = Math::BigInt->new(shift); my $s = $x->bstr; my $l = length $s; return $l <= 15 ? log($s) : log(substr($s,0,15)) + ($l-15)*log(10); }
for my $ms ('8','16','32','64','1000','10000','1000000','100000000','1000000000000') {
  my $m = Math::BigInt->new($ms);
  my %a; for my $p (2,3) { my $a=0; while (Math::BigInt->new($p)->bpow(2*$a+1) <= $m) { $a++ } $a{$p}=$a; }
  my $D = Math::BigInt->new(2)->bpow($a{2}**2)->bmul(Math::BigInt->new(3)->bpow($a{3}**2));
  my ($bestO, $bestN, $infoO, $infoN);
  for my $r2 ($a{2}..$a{2}+45) { for my $r3 ($a{3}..$a{3}+45) {
    my $d = ($r2-$a{2})+($r3-$a{3});
    my $p2 = Math::BigInt->new(2)->bpow(($r2+1)**2); my $p3 = Math::BigInt->new(3)->bpow(($r3+1)**2);
    my $No = $D->copy->bmul(($m*2)->bpow($d)); 
    if (2*$m*$No < $p2 && 2*$m*$No < $p3) { if (!defined $bestO || $No < $bestO) { $bestO=$No; $infoO="($a{2},$a{3},$r2,$r3,$d)"; } }
    my $Nn = $D->copy->bmul($m->copy->bpow($d));
    if ($m*$Nn < $p2 && $m*$Nn < $p3) { if (!defined $bestN || $Nn < $bestN) { $bestN=$Nn; $infoN="($a{2},$a{3},$r2,$r3,$d)"; } }
  } }
  my $lo = lg($bestO); my $ln = lg($bestN); my $lm = lg($m);
  printf "m=%s old %s lnN=%.2f ratio=%.2f | new %s lnN=%.2f ratio=%.2f | diff %.2f\n", $ms, $infoO, $lo, $lo/($lm*$lm), $infoN, $ln, $ln/($lm*$lm), $lo-$ln;
}
