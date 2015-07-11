#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;
use Env qw(HOLLIGHT_DIR);

# Add header/footer to generate a .hl file whose name is given in cmd line
# Author: Erik Martin-Dorel, 2014

if (! defined $HOLLIGHT_DIR) {
    die "Error: the environment variable HOLLIGHT_DIR is undefined.\n";
}

Getopt::Long::Configure( "bundling" );
my $output = "";
GetOptions( "o=s" => \$output );
if ($output eq "") {
    die "You should specify the output with option \"-o FILE\".\n";
}

open(my $out, ">", $output) or die "Can't open $output: $!\n";

################################################################

print $out "#use \"$HOLLIGHT_DIR/hol.ml\";;\n";
print $out "#use \"$HOLLIGHT_DIR/Examples/sos.ml\";;\n\n";

while (<>) {
    print $out $_;
}

################################################################

close $out;
