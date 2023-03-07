#!/usr/bin/env python3
# Script authors: Erik Martin-Dorel, Pierre Roux
# (script adapted from "step4_tex.py")
import csv
import sys
import math

# dictionary {"filename.v": "tabular-caption"}
configs = {"coqintvl_bigz_int63_prec53.v": [0, "452-bigz-prec53"],
           "coqintvl_bigz_int63_prec30.v": [1, "452-bigz-prec30"],
           "coqintvl_primfloat.v": [2, "452-primfloat"],
           "coqintvl_bigz_int63_prec53_native.v": [3, "452-bigz-prec53-native"],
           "coqintvl_bigz_int63_prec30_native.v": [4, "452-bigz-prec30-native"],
           "coqintvl_primfloat_native.v": [5, "452-primfloat-native"]}

filenames = sorted(list(configs.keys()), key=(lambda x: configs[x]))

def usage():
    sys.stderr.write("Require a single argument among:\n\
      big53-primfloat.table\n\
      big53-big30.table\n\
      big53-big53-native.table\n\
      primfloat-primfloat-native.table\n\
      big53-native-primfloat-native.table\n")
    exit(1)

if (len(sys.argv) != 2): usage()

if sys.argv[1] == "big53-primfloat.table":
    value_x = "coqintvl_bigz_int63_prec53.v"
    value_y = "coqintvl_primfloat.v"
elif sys.argv[1] == "big53-big30.table":
    value_x = "coqintvl_bigz_int63_prec53.v"
    value_y = "coqintvl_bigz_int63_prec30.v"
elif sys.argv[1] == "big53-big53-native.table":
    value_x = "coqintvl_bigz_int63_prec53.v"
    value_y = "coqintvl_bigz_int63_prec53_native.v"
elif sys.argv[1] == "primfloat-primfloat-native.table":
    value_x = "coqintvl_primfloat.v"
    value_y = "coqintvl_primfloat_native.v"
elif sys.argv[1] == "big53-native-primfloat-native.table":
    value_x = "coqintvl_bigz_int63_prec53_native.v"
    value_y = "coqintvl_primfloat_native.v"
else: usage()


overflow = 3.1


def get_full_filename(filename):
    return "output/" + filename + ".out.csv"


def get_map(filename):
    res = {}
    with open(get_full_filename(filename), mode='r') as csv_file:
        csv_reader = csv.reader(csv_file)
        next(csv_reader)

        for row in csv_reader:
            res[row[0]] = row[1]  # Note: only keep the row 1
    return res


def main():

    res = {}
    for f in filenames:
        mapf = get_map(f)
        for p in mapf.keys():
            if p not in res:
                res[p] = {}
            res[p][f] = mapf[p]

    problems = sorted(list(res.keys()))

    basefile = filenames[0]

    minx = 0
    maxx = 0
    miny = 0
    maxy = 0
    for p in problems:
        basefile_value_fl = float(res[p][basefile]) # assuming it is found
        if value_x in res[p]:
            vx = math.log(float(res[p][value_x]), 10)
        else:
            vx = overflow
        if value_y in res[p]:
            vy = math.log(float(res[p][value_y]), 10)
        else:
            vy = overflow
        minx = min(minx, vx)
        maxx = max(maxx, vx)
        miny = min(miny, vy)
        maxy = max(maxy, vy)

        print("%f %f # %s" % (vx, vy, p))

    print("# min %f %f" % (minx, miny))
    print("# max %f %f" % (maxx, maxy))


main()
