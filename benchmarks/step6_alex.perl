#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse HOL-Light/Alexey's output & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $title = "";
GetOptions( "title=s" => \$title );
if ($title eq "") {
    die "You should specify the title with \"--title=TITLE\".\n";
}

print "\"$title\"\n";
print "\"Lemma\",\"HL-Alex CPU time (s)\",\"HL-Alex verif time or Exception\"\n";

my $input = do { local $/; <> };

my (@parts) = split(m/val ([0-9A-Za-z_]+) : term =\s*/s, $input);

# Assert exists k : N, (scalar @parts) = 1 + 2 * k
# Ignore $parts[0]

if (scalar @parts <= 2) { warn "No input found.\n"; exit 0 }

my $num = $#parts / 2;

for (my $k = 0; $k < $num; $k++) {
    my ($lemma, $rest) = @parts[1+2*$k .. 2+2*$k];

    if ($rest =~ m/Exception:\s*(.*)\.\s*#/s) {
        my $exc = $1;
        if ($exc =~ m/Failure\s+"([^"]+)"/s) {
            $exc = "Failure ($1)";
        } else {
            $exc = "Exception."
        }
        print "\"$lemma\",\"FAILED\",\"$exc\"\n";
    } else {
        if ($rest =~ m/total_time =\s*([.0-9]+);.*formal_verification_time =\s*([.0-9]+);/s) {
            my ($total, $verif) = ($1, $2);
            print "\"$lemma\",$total,$verif\n";
        }
        else {
            die "Match failed for \"$rest\" (k=$k).\n";
        }
    }
}
print "\n";
