#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Add header/footer to generate a PVS file whose name is given in cmd line
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $output = "";
GetOptions( "o=s" => \$output );
if ($output eq "") {
    die "You should specify the output with option \"-o FILE\".\n";
}

open(my $out, ">", $output) or die "Can't open $output: $!\n";

my $theo = $output;
$theo =~ s|^(?:.*/)?(.*)\.pvs$|$1|;

################################################################

print $out "$theo : THEORY
BEGIN
"; print $out '
IMPORTING trig@atan,
          lnexp@ln_exp,
          interval_arith@interval

%|- * : PROOF
%|- (metit :timeout 180)
%|- QED

%|- *_TCC* : PROOF
%|- (else (finalize (subtype-tcc)) (metit))
%|- QED

';

while (<>) { print $out $_; }

print $out "
END $theo
";

################################################################

close $out;

# We must put the most greedy proof script (i.e., *_TCC* or so) before
# any other proof script.
