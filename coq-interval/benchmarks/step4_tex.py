#!/usr/bin/env python3
import csv
import sys

# dictionary {"filename.v": "tabular-caption"}
configs = {"coqintvl_bigz_int63_prec53.v": [0, "452-bigz-prec53"],
           "coqintvl_bigz_int63_prec30.v": [1, "452-bigz-prec30"],
           "coqintvl_primfloat.v": [2, "452-primfloat"],
           "coqintvl_bigz_int63_prec53_native.v": [3, "452-bigz-prec53-native"],
           "coqintvl_bigz_int63_prec30_native.v": [4, "452-bigz-prec30-native"],
           "coqintvl_primfloat_native.v": [5, "452-primfloat-native"]}

filenames = sorted(list(configs.keys()), key=(lambda x: configs[x]))


nrows = 34


def get_full_filename(filename):
    return "output/" + filename + ".out.csv"


def get_map(filename):
    res = {}
    first_row = None
    with open(get_full_filename(filename), mode='r') as csv_file:
        csv_reader = csv.reader(csv_file)
        # Hack: extract the first row which gathers the column titles
        first_row = next(csv_reader)

        for row in csv_reader:
            res[row[0]] = row[1]  # Note: only keep the row 1
    return (first_row, res)


def get_title(filename):
    return configs[filename][1]


def main():

    print("""
\\documentclass[a4paper,10pt]{article}
%%% BEGIN OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE
\\usepackage{calc}
\\usepackage{rotating}
\\usepackage{array}
\\usepackage{booktabs}
\\usepackage{tikz}
\\newcolumntype{R}[1]{>{\\begin{turn}{90}\\begin{minipage}{#1}}l%
<{\\end{minipage}\\end{turn}}%
}
\\newcommand{\\col}[1]{\\multicolumn{1}{R{\\widthof{(partly verified)\\,}}}{#1}}
\\newcommand{\\colz}[1]{\\multicolumn{1}{R{\\widthof{\\,}}}{#1}}

\\usetikzlibrary{calc,fit,intersections,shapes,calc}

\\newcommand{\\loglog}[5][]{
  \\pgfmathparse{int(#3-1)}\\let\\Xmax\\pgfmathresult
  \\foreach \\ee in{#2,...,\\Xmax}{
    \\foreach \\x in {2,3,4,5,6,7,8,9}{
      \\draw[very thin,color=white!70!gray] ({log10(\\x)+\\ee},#4) -- ({log10(\\x)+\\ee},#5);
    }
  }
  \\pgfmathparse{int(#5-1)}\\let\\Ymax\\pgfmathresult
  \\foreach \\yy in  {#4,...,\\Ymax}{
    \\foreach \\x in {2,3,4,5,6,7,8,9}{
      \\draw[very thin,color=white!70!gray] (#2,{log10(\\x)+\\yy}) -- (#3,{log10(\\x)+\\yy});
    }
  }
  \\foreach \\ee in{#2,...,\\Xmax}{
    \\draw[very thin,color=white!15!gray] (\\ee,#4)node[below,color=black]{$10^{\\ee}$} -- ({\\ee},#5);
  }
  \\draw[very thin,color=white!15!gray] ({#3},#4)node[name=TextX,below,color=black]{$10^{#3}$} -- ({#3},#5);
  \\foreach \\yy in  {#4,...,\\Ymax}{
    \\draw[very thin,color=white!15!gray] ({#2},\\yy)node[name=TextY,left,color=black]{$10^{\\yy}$} -- ({#3},\\yy);
  }
  \\draw[very thin,color=white!15!gray] ({#2},#5)node[name=TextY,left,color=black]{$10^{#3}$} -- ({#3},#5);
  % \\node[  above of= TextY,node distance=0.6em,right] { \\Unity};
  % \\node[ right]at (#3,#4){ \\Unitx};
}

%%% END OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE

\\pagestyle{empty}
\\thispagestyle{empty}
\\title{Benchs Coq 8.15 + coq-interval 4.5.2}

\\begin{document}
\\maketitle

\\begin{tikzpicture}[scale=0.95]
  \\loglog{-3}{3}{-3}{3}
  \\draw[->] (-3.1, -3) -- (3.1, -3) node[right] {prec53-vm (s)};
  \\draw[->] (-3, -3.1) -- (-3, 3.1) node[above] {hardware-vm (s)};
  \\draw[very thin, color=gray] (-3, -3) -- (3, 3);
  \\draw[very thin, color=gray] (-2, -3) -- (3, 2) node [right] {$\\times 10$};
  \\draw[very thin, color=gray] (-1.699, -3) -- (3, 1.699) node [right] {$\\times 20$};
  \\path plot [mark=x] file {big53-primfloat.table};
\\end{tikzpicture}\\\\
Comparison of proof times between hardware and emulated
  53-bit floating-point arithmetic using \\texttt{vm\\_compute}. The
  graph uses a log-log scale, so diagonals represent equivalent
  speedups. Out of the 101 examples, 4 proofs fail with hardware
  numbers due to the pessimistic outward rounding. The corresponding points
  appear at the top of the graph.

\\begin{tikzpicture}[scale=0.95]
  \\loglog{-3}{3}{-3}{3}
  \\draw[->] (-3.1, -3) -- (3.1, -3) node[right] {prec53-vm (s)};
  \\draw[->] (-3, -3.1) -- (-3, 3.1) node[above] {prec30-vm (s)};
  \\draw[very thin, color=gray] (-3, -3) -- (3, 3);
  \\draw[very thin, color=gray] (-2.6990, -3) -- (3, 2.6990) node [right] {$\\times 2$};
  \\path plot [mark=x] file {big53-big30.table};
\\end{tikzpicture}\\\\
Comparison of proof times between emulated 53-bit and 30-bit
  floating-point arithmetic using \\texttt{vm\\_compute}. Out of the 101
  examples, 14 proofs fail with the reduced precision.

\\begin{tikzpicture}[scale=0.95]
  \\loglog{-3}{3}{-3}{3}
  \\draw[->] (-3.1, -3) -- (3.1, -3) node[right] {prec53-vm (s)};
  \\draw[->] (-3, -3.1) -- (-3, 3.1) node[above] {prec53-native (s)};
  \\draw[very thin, color=gray] (-3, -3) -- (3, 3);
  \\draw[very thin, color=gray] (-2.5229, -3) -- (3, 2.5229) node [right] {$\\times 3$};
  \\path plot [mark=x] file {big53-big53-native.table};
\\end{tikzpicture}\\\\
Comparison of proof times for emulated 53-bit
  floating-point arithmetic between \\texttt{vm\\_compute} and
  \\texttt{native\\_compute}.

\\begin{tikzpicture}[scale=0.95]
  \\loglog{-3}{3}{-3}{3}
  \\draw[->] (-3.1, -3) -- (3.1, -3) node[right] {hardware-vm (s)};
  \\draw[->] (-3, -3.1) -- (-3, 3.1) node[above] {hardware-native (s)};
  \\draw[very thin, color=gray] (-3, -3) -- (3, 3);
  \\draw[very thin, color=gray] (-2.5229, -3) -- (3, 2.5229) node [right] {$\\times 3$};
  \\path plot [mark=x] file {primfloat-primfloat-native.table};
\\end{tikzpicture}\\\\
Comparison of proof times for hardware floating-point
  arithmetic between \\texttt{vm\\_compute} and
  \\texttt{native\\_compute}. The 4 proofs that fail in both cases
  appear as a cluster at the top right of the graph.

\\begin{tikzpicture}[scale=0.95]
  \\loglog{-3}{3}{-3}{3}
  \\draw[->] (-3.1, -3) -- (3.1, -3) node[right] {prec53-native (s)};
  \\draw[->] (-3, -3.1) -- (-3, 3.1) node[above] {hardware-native (s)};
  \\draw[very thin, color=gray] (-3, -3) -- (3, 3);
  \\draw[very thin, color=gray] (-2, -3) -- (3, 2) node [right] {$\\times 10$};
  \\draw[very thin, color=gray] (-1.699, -3) -- (3, 1.699) node [right] {$\\times 20$};
  \\path plot [mark=x] file {big53-native-primfloat-native.table};
\\end{tikzpicture}\\\\
Comparison of proof times between hardware and 53-bit
  emulated floating-point arithmetic using
  \\texttt{native\\_compute}. The 4 proofs that fail with hardware
  numbers appear as a cluster at the top of the graph.

""", end='')

    def emit_end():
        print("""\\bottomrule
\\end{tabular}
\\endgroup
""")

    res = {}
    # Hack: extract the first rows which gather the column titles
    first_rows = {}
    for f in filenames:
        first_row, mapf = get_map(f)
        first_rows[f] = first_row
        for p in mapf.keys():
            if p not in res:
                res[p] = {}
            res[p][f] = mapf[p]

    i = 0
    problems = sorted(list(res.keys()))

    def error(message):
        print(message, file=sys.stderr)
        exit(1)

    def check_same(dic):
        cur = None
        for f in dic.keys():
            if cur and dic[f] != cur:
                error('The first row (%a) of file %s is different from other files' % (cur, f))
            else:
                cur = dic[f]
        return cur

    columns = check_same(first_rows)
    col0 = columns[0]
    col1 = columns[1] # Note: only keep the row 1

    basefile = filenames[0]

    def emit_start():
        print("""\\begingroup
\\setlength\\tabcolsep{3pt} % 6pt by default
\\hspace{-3em}\\begin{tabular}{l|lllll|llllll}
\\toprule
Problems """, end='')

        for f in filenames:
            if f == basefile:
                print(' & \\col{%s}' % get_title(f), end='')
            else:
                print(' & \\col{%s} &' % get_title(f), end='')

        print(" \\\\")
        ### BEGIN Hack duplication
        print(col0.replace('_', '\\_'), end='')

        # Shorten col1
        col1prime = col1.replace("Coq CPU ", "")

        for f in filenames:
            if f == basefile:
                print(" & %s" % col1prime, end='')
            else:
                print(" & %s & \\colz{speedup}" % col1prime, end='')
        print(""" \\\\
\\midrule""")
        ### END Hack duplication

    emit_start()
    for p in problems:
        i += 1
        print(p.replace('_', '\\_'), end='')
        basefile_value_fl = float(res[p][basefile]) # assuming it is found
        for f in filenames:
            if f in res[p]:
                value = res[p][f]
                ratio = "{:.1f}x".format(basefile_value_fl / float(value))
            else:
                value = "N/A"
                ratio = ""
            if f == basefile:
                print(" & %s" % value, end='')
            else:
                print(" & %s & %s" % (value, ratio), end='')
        print(""" \\\\
\\midrule""")

        if i % nrows == 0:
            emit_end()
            emit_start()

    emit_end()  # may lead to a last empty tabular

    print("""
\\end{document}
""")


main()
