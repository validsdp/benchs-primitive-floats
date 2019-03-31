#!/usr/bin/env perl
# -*- coding: utf-8-unix; -*-
# Copyright (c) 2014, 2018-2019  Erik Martin-Dorel
# Parse Coq output, Compute total CPU time (user+sys) & Print TeX data
use strict;
use warnings;
use Data::Dumper;

if ($#ARGV < 0) {
    warn "Usage:\n\n\$ $0 tac_mat0200_1.log tac_mat0200_1.log ... > tac_benchs.tex\n";
    die "\nNote: please follow the file name convention above.\n";
}

my $expected_times_per_file = 1;

# The following 2 hashes have this structure : mat->num->time
my %res_emul = ();
my %res_prim = ();
my @mats = ();
my @nums = ();

sub push_if_new {
    my $ref_array = shift;
    my $item = shift;
    if (! grep {$_ eq $item} @$ref_array) {
	push @$ref_array, $item
    }
}

sub parse_log {
    my $f_log = shift;
    open(my $fd_log, '<', $f_log) or die "Can't open $f_log: $!\n";
    my $input = do { local $/; <> }; # Perl slurp
    close $fd_log;
    my (@trans) = ($input =~ m/Finished transaction in (.+) \(successful\)/g);
    return (@trans);
}

sub parse_args {
    my @args = @_;
    foreach my $f_log (@args) {
	my ($prim, $mat, $num) =
	    ($f_log =~ m/tac_([0-9A-Za-z]+)_([0-9A-Za-z]+)_([0-9]+).log/);
	my @trans = parse_log($f_log);
	my @times = map {
	    my $str = $_;
	    my $t = 0.0;
	    if ($str =~ /^.*\(([.0-9e-]+?)u,([.0-9e-]+?)s\)/) {
		$t = $1 + $2;
	    } else {
		die "Match failed for '$str' in '$f_log'.\n";
	    }
	} (@trans);
	if ((scalar @times) != $expected_times_per_file) {
	    die ("Error: there are only " . (scalar @trans)
		 . " successful timing(s) in '$f_log'.\n");
	}
	push_if_new(\@mats, $mat);
	push_if_new(\@nums, $num);
	if ($prim eq "prim") {
	    $res_prim{$mat}{$num} = $times[0];
	} else {
	    $res_emul{$mat}{$num} = $times[0];
	}
    }
}

sub moy_pm {
    my @times = @_;
    my $den = (scalar @times);
    die "Error: can't get the average of an empty array.\n" if $den < 1;
    my $sum = 0.0;
    foreach my $tim (@times) {
	$sum += $tim;
    }
    my $moy = $sum / $den;
    my $pm = 0.0;
    foreach my $tim (@times) {
	my $tmp = abs(($tim - $moy) / $moy);
	$pm = $tmp if $tmp > $pm;
    }
    return ($moy, '$\pm$' . sprintf("%.1f", 100 * $pm) . '\%');
}

sub header {
    print("\\documentclass[a4paper]{article}
\\usepackage[utf8]{inputenc}
\\usepackage[T1]{fontenc}
\\usepackage[landscape]{geometry}
\\usepackage{multirow}
\\usepackage{booktabs}
\\usepackage{underscore}
\\begin{document}

\\begin{table}
\\begin{center}
\\begin{tabular}{l|c|c|r}
\\toprule
Source & Emulated floats & Primitive floats & Speedup \\\\
\\midrule\n");
}

sub footer {
    my $num_max = (scalar @nums);
    print("\\bottomrule
\\end{tabular}
\\end{center}
\\caption{\\label{fig:indivops}Proof time for the reflexive tactic posdef_check using \\texttt{vm_compute}. Each timing is measured $num_max times. The table indicates the corresponding average and relative error among the $num_max samples.}
\\end{table}
\\end{document}\n");
}

sub main {
    parse_args(@ARGV);

    # print Dumper(\%res_emul, \%res_prim);

    @mats = sort {$a cmp $b} @mats;

    header();

    foreach my $mat (@mats) {
        my $hash = $res_emul{$mat};
        my (@t1) = moy_pm(values %$hash);

        $hash = $res_prim{$mat};
        my (@t2) = moy_pm(values %$hash);

        my $str1 = sprintf("%.3f", $t1[0]) . 's ' . $t1[1];

        my $str2 = sprintf("%.3f", $t2[0]) . 's ' . $t2[1];

        my $tn1 = $t1[0];
        my $tn2 = $t2[0];
        my $speedup = '';
        if ($tn1 > 0.0 && $tn2 > 0.0) {
            $speedup = sprintf("%.1f", $tn1 / $tn2) . "x";
        }

        print "$mat & $str1 & $str2 & $speedup \\\\\n";
    }

    footer();
}

main();

# Local Variables:
# compile-command: "./tac_coqlog2tex.pl output/*.log > tac_benchs.tex"
# End:
