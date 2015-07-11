#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse HOL-Light/REAL_SOS output & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
#OLD# my $t0file = "";
my $t1file = "";
my $auxfile = "";
GetOptions( #OLD# "t0=s" => \$t0file ,
            "t1=s" => \$t1file , "f=s" => \$auxfile );
#OLD# if ($t0file eq "") {
#OLD# die "You must specify a reference time file with option \"--t0 FILE\".\n";
#OLD# }
if ($t1file eq "") {
    die "You must specify an individual time file with option \"--t1 FILE\".\n";
}
if ($auxfile eq "") {
    die "You should specify the auxiliary Coq source file with option \"-f FILE\".\n";
}

my $title = $t1file;
$title =~ s|^(?:.*/)?(.*)\.time$|$1|;

sub get_coq_lemmas {
    my $filename = shift;
    open(my $file, "<", $filename) or die "Can't open $filename: $!\n";
    my $input = do { local $/; <$file> };
    my @lemmas = ();
    if (my ($lemmas) = ($input =~ m/Check \(([0-9A-Za-z_,\s]+?)\)\./s)) {
        (@lemmas) = ($lemmas =~ m/([0-9A-Za-z_]+)/g);
        return @lemmas;
    } else {
        die "Error: Cannot find command \"Check\" with arguments in $filename\n";
    }
}

sub get_cpu_time {
    my $filename = shift;
    open my $file, "<", $filename or die "Can't open $filename: $!\n";

    my $input = do { local $/; <$file> };

    my $tim = 0.0;
    if (my ($tu, $ts, $status) = ($input =~ m/User time \(seconds\):\s+([0-9.]+)\s*.*System time \(seconds\):\s+([0-9.]+)\s*.*Exit status:\s+([0-9]+)/s)) {
        $tim = $tu + $ts;
        close $file;
        return ($tim, $status);
    } else {
        die "Match failed with $filename.\n";
    }
}

print "\"$title\"\n";
print "\"Lemma\",\"HL-SOS CPU time (s)\",\"Detail\"\n";

my @lemmas = get_coq_lemmas $auxfile;
if (scalar @lemmas < 1) { die "No theorem found in $auxfile.\n" }
if (scalar @lemmas > 1) { die "More than one theorem found in $auxfile.\n" }
my $lemma = $lemmas[0];

my ($t1, $status1) = get_cpu_time $t1file;
#OLD# my ($t0, $status0) = get_cpu_time $t0file;
#OLD# my $global_time = $t1 - $t0;

#OLD# if ($status0 != 0) { die "Exit status should be 0 in $t0file.\n" }
if ($status1 == 0) {
    my $input = do { local $/; <> };
    my (@parts) = split(m/val ([0-9A-Za-z_]+) : term =\s*/s, $input);
    # Assert exists k : N, (scalar @parts) = 1 + 2 * k
    # Ignore $parts[0]
    #OLD# if (scalar @parts <= 2) { warn "No input found.\n"; exit 0 }
    my $num = $#parts / 2;
    if ($num > 1) { die "More than one theorem found in STDIN.\n" }

    for (my $k = 0; $k < $num; $k++) {
        my ($discard, $rest) = @parts[1+2*$k .. 2+2*$k];
        if ($rest =~ m/CPU time [0-9A-Za-z()]+:\s*([.0-9]+)\s+.*: thm =/s) {
            my $hol_time = $1;
            print "\"$lemma\",$hol_time,\"(total: $t1)\"\n";
        }
        else {
            warn "HOL Light timing not found for lemma $lemma.\n";
            print "\"$lemma\",\"FAILED\",\"(total: $t1 => ?)\"\n";
        }
    }
} elsif ($status1 == 124) { # HARD-CODED
    print "\"$lemma\",\"TIMEOUT\",\"(total: $t1 => timeout)\"\n";
} else {
    print "\"$lemma\",\"FAILED\",\"(total: $t1 => exit status $status1)\"\n";
}
print "\n";
