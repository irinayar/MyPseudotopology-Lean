use strict; use warnings;
# direct count of kappa_D = u * P( y+z+M v = y'+z' mod u ),  P(M=m) ~ (D-|m|)^2 ; usage: p q D s t
my ($p,$q,$D,$s,$t) = @ARGV; my $u = $q**($s*$s); my $v = $p**($t*$t);
sub residues { my ($b,$levels)=@_; my @c = (0) x $u; $c[0]=1;
  for my $n (1..$levels) { my $J = int($b**(2*$n-1)/$D); next unless $J; my $w = $b**(($n-1)*($n-1)) % $u; my @d = (0) x $u;
    for my $r (0..$u-1) { next unless $c[$r]; for my $j (-$J..$J) { $d[($r+$j*$w) % $u] += $c[$r]/(2*$J+1); } } @c=@d; }
  return @c; }
my @y = residues($q,$s); my @z = residues($p,$t);
my @nzy = grep { $y[$_] } 0..$u-1; my @sum = (0) x $u;
for my $r (0..$u-1) { next unless $z[$r]; for my $a (@nzy) { $sum[($r+$a)%$u] += $z[$r]*$y[$a]; } }
my ($num,$den)=(0,0);
for my $m (-($D-1)..($D-1)) { my $w=($D-abs($m))**2; my $sh = ($m*$v) % $u; my $c=0; $c += $sum[$_]*$sum[($_+$sh)%$u] for 0..$u-1; $num += $w*$c; $den += $w; }
printf "p=$p q=$q D=$D u=$u direct kappa_D=%.6f\n", $u*$num/$den;
