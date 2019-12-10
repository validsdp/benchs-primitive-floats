#!/usr/bin/env python3
import csv

configs = {"coqintvl_stable_bigz_int31.v": "stable-bigz-int31",
           "coqintvl_stable_bigz_int63.v": "stable-bigz-int63",
#           "coqintvl_dev_bigz_int63_coq810.v": "dev-bigz-int63-coq810",
#           "coqintvl_dev_bigz_int63_coq811.v": "dev-bigz-int63-coq811",
           "coqintvl_dev_primfloat.v": "dev-primfloat"}

filenames = list(configs.keys())


def get_full_filename(filename):
    return "output/" + filename + ".out.csv"


def get_map(filename):
    res = {}
    with open(get_full_filename(filename), mode='r') as csv_file:
        csv_reader = csv.reader(csv_file)
        for row in csv_reader:
            res[row[0]] = row[1]
    return res

def get_title(filename):
    return configs[filename]

def main():

    print("""
\\documentclass{article}
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

\\begin{document}

\\begingroup
\\setlength\\tabcolsep{3pt} % 6pt by default
\\begin{tabular}{llllllllll}
\\toprule
Problems """, end='')
    
    for f in filenames:
        print(' & \\col{%s}' % get_title(f), end='')
    
    print(" \\\\")
    
    res = {}
    
    for f in filenames:
        mapf = get_map(f)
        for p in mapf.keys():
            if p not in res:
                res[p] = {}
            res[p][f] = mapf[p]

    problems = sorted(list(res.keys()))
    for p in problems:
        print(p.replace('_', '\\_'), end='')
        for f in filenames:
            print(" & %s" % res[p][f], end = '')
        print(""" \\\\
\\midrule""")
    
    print("""\\bottomrule
\\end{tabular}
\\endgroup

\\end{document}
""")


main()
