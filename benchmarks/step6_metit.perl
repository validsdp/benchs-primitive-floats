#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse PVS+MetiTarski's output & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $title = "";
GetOptions( "title=s" => \$title );
if ($title eq "") {
    die "You should specify the title with \"--title=TITLE\".\n";
}

print "\"$title\"\n";
print "\"Lemma\",\"MetiTarski CPU time (s)\",\"Status\"\n";

my $input = do { local $/; <> };

my (@parts) = $input =~ m/SZS status (GaveUp|Timeout|Theorem) for.+\/([0-9A-Za-z_]+)\.tptp\s+(?:Processor time limit exceeded\.\s*)?Processor time:\s*([0-9.]+)\s*=/g;

for (my $i = 0; 3*$i+2 <= $#parts; $i++) {
    my ($status, $pvs_lemma, $time) = @parts[3*$i..3*$i+2];

    if ($status eq "Theorem") {
        print "\"$pvs_lemma\",$time,\"$status\"\n";
    } elsif ($status eq "Timeout") {
        print "\"$pvs_lemma\",\"TIMEOUT\",\"$status ($time)\"\n";
    } else {
        print "\"$pvs_lemma\",\"FAILED\",\"$status ($time)\"\n";
    }
}
print "\n";
