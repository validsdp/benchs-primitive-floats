#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse Coq output, Compute total CPU time & Print CSV data
# Author: Erik Martin-Dorel, 2014

### Get the timings

my (@times) = ();

my $next = 1;
my $lem = '';

print "\"Lemma\",\"Coq CPU time (s)\",\"Coq outputted time\"\n";

while (<>) {
    if ($next == 1) {
        chomp;
        $lem = $_;
        $next = 0;
    } else {
        chomp;
        my $str = '';
        if (m/Finished transaction in (.+?)\)/) {
            $str = $1 . ')';
        } else {
            die "Match failed for \"$_\".\n";
        }
        my $t = 0.0;
        # if ($str =~ /^.*\(([.0-9e-]+?)u,([.0-9e-]+?)s\)/) {
        #     $t = $1 + $2;
        # }
        if ($str =~ /^.*([.0-9e-]+?) secs/) {
            $t = $1;
        } else {
            die "Match failed for \"$str\".";
        }
        print "\"$lem\",$t,\"$str\"\n";
        $next = 1;
    }
}
