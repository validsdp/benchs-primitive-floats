#!/usr/bin/env perl
# -*- coding: utf-8-unix; -*-
# Copyright (c) 2014, 2018  Erik Martin-Dorel
# Parse Coq output, Compute total CPU time (user+sys) & Print TeX data
use strict;
use warnings;
use Data::Dumper;

if ($#ARGV < 0) {
    warn "Usage:\n\n\$ $0 test_mat0200_none_1.log test_mat0200_add_1.log ... > benchs.tex\n";
    die "\nNote: please follow the file name convention above.\n";
}

my $expected_times_per_file = 1;

# The following 2 hashes have this structure : ops->mat->num->time
my %res_emul = ();
my %res_prim = ();
my @ops = ();
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
	my ($prim, $mat, $op, $num) =
	    ($f_log =~ m/test_([0-9A-Za-z]+)_([0-9A-Za-z]+)_([0-9A-Za-z]+)_([0-9]+).log/);
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
	push_if_new(\@ops, $op);
	push_if_new(\@mats, $mat);
	push_if_new(\@nums, $num);
	if ($prim eq "prim") {
	    $res_prim{$op}{$mat}{$num} = $times[0];
	} else {
	    $res_emul{$op}{$mat}{$num} = $times[0];
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
\\begin{tabular}{ll|cc|cc|r}
\\toprule
\\multirow{2}{*}{Op} & \\multirow{2}{*}{Source}
  & \\multicolumn{2}{c|}{Emulated floats}
  & \\multicolumn{2}{c|}{Primitive floats}
  & \\multirow{2}{*}{Speedup} \\\\
& & CPU times (Op\$\\times2 -\$Op) & Op time
  & CPU times (Op\$\\times1001 -\$Op) & Op time
  & \\\\
\\midrule\n");
}

sub footer {
    my $num_max = (scalar @nums);
    print("\\bottomrule
\\end{tabular}
\\end{center}
\\caption{\\label{fig:indivops}Computation time for individual operations obtained by subtracting the CPU time of a normal execution from that of a modified execution where the specified operation is computed twice (resp. 1001 times). Each timing is measured $num_max times. The table indicates the corresponding average and relative error among the $num_max samples (using \\texttt{vm_compute}).}
\\end{table}
\\end{document}\n");
}

sub main {
    parse_args(@ARGV);

    # print Dumper(\%res_emul, \%res_prim);

    @mats = sort {$a cmp $b} @mats;

    @ops = sort {$a eq 'none' ? 1 : $b eq 'none' ? -1 : $a cmp $b} @ops;
    my $none = pop(@ops);
    die "Last element of @ops is not 'none'\n" if $none ne 'none';

    header();

    foreach my $op (@ops) {
	foreach my $mat (@mats) {
	    my $hash = $res_emul{$op}{$mat};
	    my (@t1) = moy_pm(values %$hash);

	    $hash = $res_emul{'none'}{$mat};
	    my (@n1) = moy_pm(values %$hash);

	    $hash = $res_prim{$op}{$mat};
	    my (@t2) = moy_pm(values %$hash);

	    $hash = $res_prim{'none'}{$mat};
	    my (@n2) = moy_pm(values %$hash);

	    my $str1 = sprintf("%.3f", $t1[0]) . $t1[1]
		. " \$-\$ " . sprintf("%.3f", $n1[0]) . $n1[1];

	    my $str2 = sprintf("%.3f", $t2[0]) . $t2[1]
		. " \$-\$ " . sprintf("%.3f", $n2[0]) . $n2[1];

	    my $tn1 = $t1[0] - $n1[0];
	    my $tn2 = ($t2[0] - $n2[0]) / 1000.0;
	    my $speedup = '';
	    if ($tn1 > 0.0 && $tn2 > 0.0) {
		$speedup = sprintf("%.1f", $tn1 / $tn2) . "x";
	    }
	    $tn1 = sprintf("%.3f", $tn1) . 's';
	    $tn2 = sprintf("%.3f", $tn2) . 's';

	    print "$op & $mat & $str1 & $tn1 & $str2 & $tn2 & $speedup \\\\\n";
	}
    }

    footer();
}

main();

# Local Variables:
# compile-command: "./coqlog2tex.pl output/*.log > benchs.tex"
# End:
