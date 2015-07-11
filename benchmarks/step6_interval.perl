#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse PVS+Interval's output & Print CSV data, including timings
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my $auxfile = "";
GetOptions( "f=s" => \$auxfile );
if ($auxfile eq "") {
    die "You should specify the auxiliary log file with option \"-f FILE\".\n";
}

# Get the lemmas that raised a timeout

open(my $aux, "<", $auxfile) or die "Can't open $auxfile: $!\n";

my @timeouts = ();

my $boo = 0;
while (<$aux>) {
    next unless m/Apply timed out|proved in/;
    # ASSUME these patterns are alone (only one such pattern per line)
    if (m/Apply timed out/) {
        $boo++;
    } elsif (my ($lemma) = m/\.([0-9A-Za-z_]+) unproved in/) {
        if ($boo == 1) {
            push(@timeouts, $lemma);
            $boo = 0;
        } elsif ($boo > 1) {
            die "Error: $boo (>1) timeouts registered when looking at $lemma.\n"
        }
        # else: the unproved lemma did not involve any timeout.
    } elsif (my ($lemma2) = m/\.([0-9A-Za-z_]+) proved in/) {
        if ($boo > 0) {
            die "Error: $lemma2 seems proved despite a timeout.\n"
        }
    }
}

close $aux;

sub chk_timeout {
    my $lemma = shift;
    if ( grep { $lemma eq $_ } @timeouts ) {
        return 1;
    } else {
        return 0;
    }
}

my $input = do { local $/; <> };

my (@array) = ($input =~ m/Proof summary for theory ([0-9A-Za-z_]+)\s+(.*?)\s+Theory totals:/gs);

for (my $n = 0; 2*$n+1 <= $#array; $n++) {
    my ($theo, $rest) = @array[2*$n..2*$n+1];

    print "\"$theo.pvs\"\n";
    print "\"Lemma\",\"Interval CPU time (s)\",\"Status\"\n";

    my (@parts) = $rest =~ m/([0-9A-Za-z_]+)\.+([a-zA-Z]+(?: - [a-zA-Z]+)?)\s+[^(]+\(\s*([a-z\/0-9.-]+)\s*[^)]*\)/gs;

    for (my $i = 0; 3*$i+2 <= $#parts; $i++) {
        my ($pvs_lemma, $status, $time) = @parts[3*$i..3*$i+2];
        my $time2 = "";
        my $status2 = "";
        if ($status =~ m/proved/) {
            if ($time =~ /^[.0-9]+$/) {
                $time2 = $time;
            } else {
                $time2 = "\"$time\"";
            }
            $status2 = $status;
        } else {
            $time2 = (chk_timeout($pvs_lemma)) ? "\"TIMEOUT\"" : "\"FAILED\"";
            $status2 = "$status ($time)";
        }
        print "\"$pvs_lemma\",$time2,\"$status2\"\n";
    }
    print "\n";
}
