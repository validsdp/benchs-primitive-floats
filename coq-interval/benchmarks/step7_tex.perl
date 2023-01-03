#!/usr/bin/env perl
use strict;
use warnings;
use Getopt::Long;

# Parse results & Generate a LaTeX tabular
# Author: Erik Martin-Dorel, 2014

Getopt::Long::Configure( "bundling" );
my @aux_coq;
my @csv_coq;
my @csv_metit;
my @csv_intvl;
my @csv_bern;
my @csv_sos;
my @csv_alex;
my @csv_nlc_nocoq;
my @csv_nlc_coq;
my @csv_sollya;
GetOptions("aux-coq=s" => \@aux_coq,
           "coq=s" => \@csv_coq,
           "metit=s" => \@csv_metit,
           "interval=s" => \@csv_intvl,
           "bern=s" => \@csv_bern,
           "hl-sos=s" => \@csv_sos,
           "hl-alex=s" => \@csv_alex,
           "nlc-coq=s" => \@csv_nlc_coq,
           "nlc-nocoq=s" => \@csv_nlc_nocoq,
           "sollya=s" => \@csv_sollya)
    or die("Error in command line arguments.\n");

sub csv_split {
    # inspired from http://stackoverflow.com/a/3068793
    # FIXME: Handle repeated quotes inside quoted text
    my $line = shift;
    my $sep = (shift or ',');
    return () unless $line;
    my @cells;
    # $line =~ s/\r?\n$//;
    chomp $line;
    my $re = qr/(?:^|$sep)(?:"([^"]*)"|([^$sep]*))/;
    while($line =~ /$re/g) {
        my $value = defined $1 ? $1 : $2;
        push @cells, (defined $value ? $value : '');
    }
    return @cells;
}

sub get_tim {
    my $filename = shift;
    my @tim = @_;
    open my $file, "<", $filename or die "Can't open $filename: $!\n";
    my $first = <$file>;
    if ($first =~ m/,/) {
        close $file;
        die "The 1st line of $filename should not contain any comma.\n";
    }
    my $second = <$file>;
    if (! ($second =~ m/\(s\)/)) {
        close $file;
        die "The 2nd line of $filename should contain the string \"(s)\".\n";
    }
    while (my $line = <$file>) {
        my (@parts) = csv_split($line);
        if (scalar @parts >= 2) {
            push @tim, (@parts[0..1]);
        }
    }
    close $file;
    return @tim;
}

sub get_tim_full {
    my @files = @_;
    my @tim = ();
    foreach my $fil (@files) {
        @tim = get_tim($fil, @tim);
    }
    return @tim;
}

my @lem_midrule = ();
# gathers the name of the first lemma of each Coq file

sub get_tim_full_and_prepare_midrule {
    my @files = @_;
    my @tim = ();
    my ($cur_idx, $cur_lem) = (0, "");
    foreach my $fil (@files) {
        @tim = get_tim($fil, @tim);
        $cur_lem=$tim[$cur_idx];
        $cur_idx=scalar(@tim);
        push @lem_midrule, $cur_lem;
    }
    return @tim;
}

sub get_coq_mark {
    my $filename = shift;
    my @mark = @_;
    open my $file, "<", $filename or die "Can't open $filename: $!\n";

    my $input = do { local $/; <$file> };

    close $file;

    my @lemmas = ();
    if (my ($lemmas) = ($input =~ m/__Split__ \(([0-9A-Za-z_,\s]*?)\)\./s)) {
        (@lemmas) = ($lemmas =~ m/([0-9A-Za-z_]+)/g);
    } else {
        die "Error: Cannot find pseudo-command \"__Split__\" with arguments in $filename\n";
    }

    push @mark, @lemmas;
    return @mark;
}

# Very similar to sub get_tim_full:
sub get_coq_mark_full {
    my @files = @_;
    my @mark = ();
    foreach my $fil (@files) {
        @mark = get_coq_mark($fil, @mark);
    }
    return @mark;
}

# The following sub is just a validation function w.r.t duplicates
sub chk_get_hash {
    my @t = @_;
    if ($#t % 2 == 0) {
        die "Error: Odd number of elements in hash assignment...\n";
    }
    my %h;
    for (my $i = 0; 1+2*$i <= $#t; $i++) {
        if (exists $h{$t[2*$i]}) {
            die "Duplicated row: $t[2*$i]\n";
        } else {
            $h{$t[2*$i]} = $t[1+2*$i];
        }
    }
    return %h;
}

sub get_half {
    my @t = @_;
    my @res = ();
    for (my $i = 0; 2*$i <= $#t; $i++) {
        push @res, $t[2*$i];
    }
    return @res;
}

my @coq_mark = get_coq_mark_full(@aux_coq);
my @tim_coq = get_tim_full_and_prepare_midrule(@csv_coq);
my %t_coq = chk_get_hash(@tim_coq);
# Better than doing "my @lem = sort( {$a cmp $b} keys(%t_coq) );":
my @lem = get_half(@tim_coq);

my %t_nlc_nocoq = chk_get_hash(get_tim_full(@csv_nlc_nocoq));
my %t_nlc_coq = chk_get_hash(get_tim_full(@csv_nlc_coq));
my %t_sollya = chk_get_hash(get_tim_full(@csv_sollya));
my %t_metit = chk_get_hash(get_tim_full(@csv_metit));
my %t_intvl = chk_get_hash(get_tim_full(@csv_intvl));
my %t_bern = chk_get_hash(get_tim_full(@csv_bern));
my %t_sos = chk_get_hash(get_tim_full(@csv_sos));
my %t_alex = chk_get_hash(get_tim_full(@csv_alex));

### Special strings:
my $re_failed = qr/FAILED/;
my $re_timeout = qr/TIMEOUT/;
# for input
my ($na, $fail, $timeout) = ("-", "Failed", "Timeout"); # for output

sub mark_as_split {
    my $str = shift;
    # return "(" . $str . ")";
    return ($str . '$^{\star}$');
}

sub chk_get_fl {
    my $t = shift;
    if (! (defined $t)) {
        return $na;
    } elsif ($t =~ $re_failed) {
        return $fail;
    } elsif ($t =~ $re_timeout) {
        return $timeout;
    } else {
        # FIXME: Update the format if need be:
        return sprintf("%.2f", $t);
    }
}

sub coq_chk_get_fl {
    my $k = shift;
    if ( grep { $k eq $_ } @coq_mark ) {
        return mark_as_split(chk_get_fl($t_coq{$k}));
    } else {
        return chk_get_fl($t_coq{$k});
    }
}

sub alex_chk_get_fl {
    my $k = shift;
    if (exists $t_alex{$k}) {
        return chk_get_fl ($t_alex{$k});
    }
    if (! (exists $t_alex{"${k}__1"})) {
        return $na;
    }
    my $num = 1;
    # FIXME: Increase the upper bound for $i if need be:
    my $max = 9;
    for (my $i = 2; $i <= $max; $i++) {
        if (! (exists $t_alex{"${k}__$i"})) {
            $num = $i - 1; last;
        }
    }
    if ($num == 1) {
        die "Error: incorrect number of sub-lemmas ${k}__* found, stopped";
        # EITHER there is only one lemma ${k}__1
        # OR you should increase the number $max above
    }
    my @str = map({ "${k}__$_" } (1..$num));
    my @tim = @t_alex{@str};
    my $total = 0.0;
    my ($nb_fail, $nb_timeout) = (0, 0);
    foreach my $t (@tim) {
        if ($t =~ $re_failed) {
            $nb_fail++;
        } elsif ($t =~ $re_timeout) {
            $nb_timeout++;
        } else {
            $total = $total + $t;
        }
    }
    if ($nb_fail > 0) {
        return ($fail); # no mark_as_split
    } elsif ($nb_timeout > 0) {
        return ($timeout); # no mark_as_split
    }
    return mark_as_split(chk_get_fl($total));
}

sub nlc_nocoq_chk_get_fl { # FIXME: Refactor as it is like alex_chk_get_fl
    my $k = shift;
    if (exists $t_nlc_nocoq{$k}) {
        return chk_get_fl ($t_nlc_nocoq{$k});
    }
    if (! (exists $t_nlc_nocoq{"${k}__1"})) {
        return $na;
    }
    my $num = 1;
    # FIXME: Increase the upper bound for $i if need be:
    my $max = 9;
    for (my $i = 2; $i <= $max; $i++) {
        if (! (exists $t_nlc_nocoq{"${k}__$i"})) {
            $num = $i - 1; last;
        }
    }
    if ($num == 1) {
        die "Error: incorrect number of sub-lemmas ${k}__* found, stopped";
        # EITHER there is only one lemma ${k}__1
        # OR you should increase the number $max above
    }
    my @str = map({ "${k}__$_" } (1..$num));
    my @tim = @t_nlc_nocoq{@str};
    my $total = 0.0;
    my ($nb_fail, $nb_timeout) = (0, 0);
    foreach my $t (@tim) {
        if ($t =~ $re_failed) {
            $nb_fail++;
        } elsif ($t =~ $re_timeout) {
            $nb_timeout++;
        } else {
            $total = $total + $t;
        }
    }
    if ($nb_fail > 0) {
        return ($fail); # no mark_as_split
    } elsif ($nb_timeout > 0) {
        return ($timeout); # no mark_as_split
    }
    return mark_as_split(chk_get_fl($total));
}

sub nlc_coq_chk_get_fl { # FIXME: Refactor as it is like alex_chk_get_fl
    my $k = shift;
    if (exists $t_nlc_coq{$k}) {
        return chk_get_fl ($t_nlc_coq{$k});
    }
    if (! (exists $t_nlc_coq{"${k}__1"})) {
        return $na;
    }
    my $num = 1;
    # FIXME: Increase the upper bound for $i if need be:
    my $max = 9;
    for (my $i = 2; $i <= $max; $i++) {
        if (! (exists $t_nlc_coq{"${k}__$i"})) {
            $num = $i - 1; last;
        }
    }
    if ($num == 1) {
        die "Error: incorrect number of sub-lemmas ${k}__* found, stopped";
        # EITHER there is only one lemma ${k}__1
        # OR you should increase the number $max above
    }
    my @str = map({ "${k}__$_" } (1..$num));
    my @tim = @t_nlc_coq{@str};
    my $total = 0.0;
    my ($nb_fail, $nb_timeout) = (0, 0);
    foreach my $t (@tim) {
        if ($t =~ $re_failed) {
            $nb_fail++;
        } elsif ($t =~ $re_timeout) {
            $nb_timeout++;
        } else {
            $total = $total + $t;
        }
    }
    if ($nb_fail > 0) {
        return ($fail); # no mark_as_split
    } elsif ($nb_timeout > 0) {
        return ($timeout); # no mark_as_split
    }
    return mark_as_split(chk_get_fl($total));
}

my %h = ();
foreach my $k (@lem) {
    $h{$k}{coq}=coq_chk_get_fl($k);
    $h{$k}{metit}=chk_get_fl($t_metit{$k});
    $h{$k}{sollya}=chk_get_fl($t_sollya{$k});
    $h{$k}{intvl}=chk_get_fl($t_intvl{$k});
    $h{$k}{bern}=chk_get_fl($t_bern{$k});
    $h{$k}{sos}=chk_get_fl($t_sos{$k});
    $h{$k}{alex} = alex_chk_get_fl($k);
    $h{$k}{nlc_nocoq} = nlc_nocoq_chk_get_fl($k);
    $h{$k}{nlc_coq} = nlc_coq_chk_get_fl($k);
}

# warn join(",", @csv_coq), "\n";
# warn join(",", @csv_metit), "\n";
# warn join(",", @csv_intvl), "\n";
# warn join(",", @csv_bern), "\n";
# warn join(",", @csv_sos), "\n";
# warn join(",", @csv_alex), "\n";
### For debugging
# use Data::Dumper;
# print Dumper( \%h );

print '%%% BEGIN OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE
% \\usepackage{calc}
% \\usepackage{rotating}
% \\usepackage{array}
% \\usepackage{booktabs}
% \\newcolumntype{R}[1]{>{\\begin{turn}{90}\\begin{minipage}{#1}}l%
% <{\\end{minipage}\\end{turn}}%
% }
% \\newcommand{\\col}[1]{\\multicolumn{1}{R{\\widthof{(partly verified)\\,}}}{#1}}
%%% END OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE

\\begingroup
\\setlength\\tabcolsep{3pt} % 6pt by default
\\begin{tabular}{llllllllll}
\\toprule
Problems & \\col{CoqInterval} & \\col{Sollya} & \\col{MetiTarski} & \\col{NLCertify\\\\(not verified)} & \\col{NLCertify\\\\(partly verified)} & \\col{PVS/interval} & \\col{HOL Light/\\\\\\texttt{verify\\_ineq}} & \\col{PVS/Bernstein} & \\col{HOL Light/\\\\\\texttt{REAL\\_SOS}} \\\\
';
foreach my $k (@lem) {
    if ( grep { $k eq $_ } @lem_midrule ) {
        print '\\midrule',"\n";
    }
    print "$k & $h{$k}{coq} & $h{$k}{sollya} & $h{$k}{metit} & $h{$k}{nlc_nocoq} & $h{$k}{nlc_coq} & $h{$k}{intvl} & $h{$k}{alex} & $h{$k}{bern} & $h{$k}{sos} \\\\\n";
}
print '\bottomrule
\end{tabular}
\endgroup
';
