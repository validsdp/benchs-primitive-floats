#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Add header/footer to generate a .hl file whose name is given in cmd line
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $output = "";
GetOptions( "o=s" => \$output );
if ($output eq "") {
    die "You should specify the output with option \"-o FILE\".\n";
}

open(my $out, ">", $output) or die "Can't open $output: $!\n";

################################################################

print $out "open M_verifier_main;;\n\n";

while (<>) {
    s/default_params 5 MT23;;/default_params 6 MT23;;/; # HARD-CODED ADAPTATION
    print $out $_;
}

################################################################

close $out;
