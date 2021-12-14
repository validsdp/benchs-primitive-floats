#!/usr/bin/env python3
import csv
import sys

# dictionary {"filename.v": "tabular-caption"}
configs = {"coqintvl_bigz_int63_prec53.v": [0, "431-bigz-prec53"],
           "coqintvl_bigz_int63.v": [1, "431-bigz-int63"],
           "coqintvl_dev_primfloat.v": [2, "431-primfloat"]}

filenames = sorted(list(configs.keys()), key=(lambda x: configs[x]))


nrows = 20


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
\\documentclass[a4paper,landscape,10pt]{article}
%%% BEGIN OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE
\\usepackage{calc}
\\usepackage{rotating}
\\usepackage{array}
\\usepackage{booktabs}
\\newcolumntype{R}[1]{>{\\begin{turn}{90}\\begin{minipage}{#1}}l%
<{\\end{minipage}\\end{turn}}%
}
\\newcommand{\\col}[1]{\\multicolumn{1}{R{\\widthof{(partly verified)\\,}}}{#1}}
%%% END OF SECTION TO BE ADDED INTO THE LATEX PREAMBLE

\\pagestyle{empty}
\\thispagestyle{empty}
\\title{Benchs Coq 8.14 + coq-interval 4.3.1}
\\begin{document}
\\maketitle
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

    def emit_start():
        print("""\\begingroup
\\setlength\\tabcolsep{3pt} % 6pt by default
\\begin{tabular}{llllll}
\\toprule
Problems """, end='')

        for f in filenames:
            print(' & \\col{%s}' % get_title(f), end='')

        print(" \\\\")
        ### BEGIN Hack duplication
        print(col0.replace('_', '\\_'), end='')
        for f in filenames:
            print(" & %s" % col1, end='')
        print(""" \\\\
\\midrule""")
        ### END Hack duplication

    emit_start()
    for p in problems:
        i += 1
        print(p.replace('_', '\\_'), end='')
        for f in filenames:
            print(" & %s" % res[p][f], end='')
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
