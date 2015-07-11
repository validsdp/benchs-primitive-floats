#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

################ same as step6_nlc_nocoq_1.perl

# Parse NLCertify output for one lemma & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

# Typically, (the last two lines of) standard input will match either
# Inequality XXX verified
# Total time: N.NN seconds
# or
# Failed to verify the inequality XXX
# Total time: N.NN seconds

Getopt::Long::Configure( "bundling" );
my $t1file = "";
GetOptions( "t1=s" => \$t1file );
if ($t1file eq "") {
    die "You must specify an individual time file with option \"--t1 FILE\".\n";
}

my $title = $t1file;
$title =~ s|^(?:.*/)?(.*)\.time$|$1|;
my $lemma = $title;
$lemma =~ s|(.*)_nlc_(?:no)?coq$|$1|;

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
print "\"Lemma\",\"NLCertify CPU time (s)\",\"Detail\"\n";

my ($t1, $status1) = get_cpu_time $t1file;

if ($status1 == 0) {
    my $input = do { local $/; <> };

    if ($input =~ m/Inequality ([0-9A-Za-z_]+) verified\s*Total time: ([0-9.]+) seconds/) {
        my ($ineq, $disp) = ($1, $2); # NORMALLY, $ineq and $lemma are the same
        print "\"$ineq\",$t1,\"(real: $disp)\"\n";
    } elsif ($input =~ m/Failed to verify the inequality ([0-9A-Za-z_]+)\s*Total time: ([0-9.]+) seconds/) {
        my ($ineq, $disp) = ($1, $2); # NORMALLY, $ineq and $lemma are the same
        print "\"$ineq\",\"FAILED\",\"(real: $disp) (total: $t1)\"\n";
    } else {
        die "Error: cannot find NLCertify's verification claim in STDIN.\n";
    }
} elsif ($status1 == 124) { # HARD-CODED
    print "\"$lemma\",\"TIMEOUT\",\"(total: $t1 => timeout)\"\n";
} else {
    print "\"$lemma\",\"FAILED\",\"(total: $t1 => exit status $status1)\"\n";
}
print "\n";
