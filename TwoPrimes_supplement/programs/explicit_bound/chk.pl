use strict; use warnings; use Math::BigInt;
# m=8: D=2^4*3^1=48, retained (p,n): (2,3),(2,4),(3,2),(3,3); arcs m=8; M=8^4
my ($m,$D)=(8,48); my @co=([2,3],[2,4],[3,2],[3,3]); my $M=$m**4; my %seen; my $found;
for my $j (0..$M) { my @rec; for my $c (@co) { my $q=Math::BigInt->new($c->[0])->bpow($c->[1]**2); my $r=($D*$j)%$q; push @rec, int($r*$m/$q); }
  my $key=join(",",@rec); if (exists $seen{$key}) { $found=[$seen{$key},$j]; last } $seen{$key}=$j; }
my ($j,$jp)=@$found; my $k=$D*($jp-$j); print "collision j=$j j'=$jp k=$k N=",$D*$M,"\n";
my $maxv=0; for my $p (2,3) { for my $n (1..12) { my $q=Math::BigInt->new($p)->bpow($n*$n); my $r=Math::BigInt->new($k)->bmod($q)->numify; $r = $q->numify-$r if $r > $q->numify/2; my $v=$r/$q->numify; $maxv=$v if $v>$maxv; } }
printf "P_{2,3}(k) over n<=12 = %.6f (< 1/8 = 0.125: %s)\n", $maxv, ($maxv<0.125?"yes":"NO");
