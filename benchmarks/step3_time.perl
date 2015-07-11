#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse Coq output, Compute total CPU time (user+sys) & Print CSV data
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $auxfile = "";
GetOptions( "f=s" => \$auxfile );
if ($auxfile eq "") {
    die "You should specify the auxiliary Coq source file with option \"-f FILE\".\n";
}

### Get the name of lemmas

open(my $aux, "<", $auxfile) or die "Can't open $auxfile: $!\n";

my $input = do { local $/; <$aux> };

close $aux;

my @lemmas = ();
if (my ($lemmas) = ($input =~ m/Check \(([0-9A-Za-z_,\s]+?)\)\./s)) {
    (@lemmas) = ($lemmas =~ m/([0-9A-Za-z_]+)/g);
} else {
    die "Error: Cannot find command \"Check\" with arguments in $auxfile\n";
}

### Get the timings

$input = do { local $/; <> };

my (@times) = ($input =~ m/Finished transaction in (.+?)\)/g);

if ((scalar @times) != (scalar @lemmas)) {
    die ("Error: there are " . (scalar @times) . " timing(s) and "
         . (scalar @lemmas) . " lemma(s).\n");
}

## Print the timings

my $theo = $auxfile;
$theo =~ s|^(?:.*/)?(.*)\.v$|$1|;

print "\"$theo.v\"\n";
print "\"Lemma\",\"Coq CPU time (s)\",\"Coq outputted time\"\n";

for (my $n = 0; $n <= $#lemmas; $n++) {
    my $lem = $lemmas[$n];
    my $str = $times[$n] . ")";
    my $t = 0.0;
    if ($str =~ /^.*\(([.0-9e-]+?)u,([.0-9e-]+?)s\)/) {
        $t = $1 + $2;
    } else {
        die "Match failed for \"$str\" (n=$n).\n";
    }
    print "\"$lem\",$t,\"$str\"\n";
}
print "\n";
