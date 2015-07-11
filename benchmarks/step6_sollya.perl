#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse Sollya's output & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $title = "";
GetOptions( "title=s" => \$title );
if ($title eq "") {
    die "You should specify the title with \"--title=TITLE\".\n";
}

print "\"$title\"\n";
print "\"Lemma\",\"Sollya CPU time (s)\",\"Status\"\n";

my $input = do { local $/; <> };

my (@parts) = $input =~ m/Lemma ([0-9A-Za-z_]+):\s*(true|false)\s*([0-9.e-]+)/g;

for (my $i = 0; 3*$i+2 <= $#parts; $i++) {
    my ($lemma, $status, $time) = @parts[3*$i..3*$i+2];
    if ($status eq "true") {
        print "\"$lemma\",$time,\"$status\"\n";
    } else {
        print "\"$lemma\",\"FAILED\",\"$status ($time)\"\n";
    }
}
print "\n";
