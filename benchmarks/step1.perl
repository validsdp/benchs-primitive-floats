#!/usr/bin/env perl
use strict;
use warnings;

# Get the name of lemmas, Add a final "Check" command & Do some tests
# Author: Erik Martin-Dorel, 2014

my @vernac = qw(Fact Proposition Remark Lemma Theorem Corollary);
my $vernac = join("|", @vernac);

my $input = do { local $/; <> };

# Old code:
# my (@ex_lemma) = $input =~ m/\s+(?:$vernac)\s+([0-9A-Za-z_]+)/g;

my @split = split(/\s+(?:$vernac)\s+([0-9A-Za-z_]+)/, $input);

# Name of lemmas:
my @ex_lemma = ();

# Lemmas that have been manually split, namely if the "body" contains "\/"
# or the *custom* tactic "case_Rle":
my @mark_as_split = ();

# Processing @split:
for (my $i = 1; $i <= $#split; $i+=2) {
    push(@ex_lemma, $split[$i]);
    # FIXME: Update this condition if need be:
    if ($split[$i+1] =~ m,\\/|case_Rle,) {
        push(@mark_as_split, $split[$i]);
    }
}

my (@ex_time) = $input =~ m/\s+(Time)\s+/g;
if ($#ex_lemma != $#ex_time) {
    die "Error: There should be exactly " . (scalar @ex_lemma)
        . " occurrence(s) of Time (one per lemma).\n";
}

my @novernac = qw(Check Print About Locate Eval Compute);
my $novernac = join("|", @novernac);
if ($input =~ m/\s+(?:$novernac)\s+/) {
    die "Error: the commands $novernac are forbidden.\n";
}

print "\nCheck (" . join(", ", @ex_lemma) . ").\n";

print "\n(* __Split__ (" . join(", ", @mark_as_split) . "). *)\n";

# LIMITATION 1: vernacular commands between comments are not ignored
# FIXME 1: Remove comments before processing the file (or reject them)
# FIXME 2: Improve the regex used for @ex_lemma
