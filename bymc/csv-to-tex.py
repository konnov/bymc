#!/usr/bin/python
#
# Generate a LaTeX table out of CSV

import csv
import re
import sys

def spec_format(field_name, val):
    if val == "yes":
        return "\\checkmark"
    elif val == "no":
        return "\\xmark"
    elif val == "maybe":
        return "\\textbf{?}"
    elif field_name.find("Time") >= 0:
        if val.find("seconds") >= 0:
            return val.replace("seconds", "sec.")
        else:
            return "%s sec." % val
    elif field_name.find("Mem") >= 0:
        return "%s MB" % val
    elif val.isdigit() and int(val) > 1000000:
        return "$%d \\cdot 10^6$" % (int(val) / 1000000)
    elif val.isdigit() and int(val) > 1000:
        return "$%d \\cdot 10^3$" % (int(val) / 1000)
    else:
        return str(val)


if len(sys.argv) <= 2:
    print "Use: %s csv-file column1,column2,column3" % sys.argv[0]
    sys.exit(1)

columns = sys.argv[2].split(",")

out = open("table.tex", 'w+')
out.write("\\begin{table*}\n")
out.write(" \\begin{center}\n")
with open(sys.argv[1], 'rb') as csvfile:
    num = 0
    reader = csv.reader(csvfile, delimiter=',', quotechar='"')
    fields = None
    for row in reader:
        if num == 0:
            out.write("  \\begin{tabular}{%s}\n" % ("l" * (1 + len(row))))
            out.write("   \\hline\n")
            out.write('\\textbf{\#} & ')
            out.write(' & '.join(['\\textbf{\scriptsize{%s}}' % c for c in columns]))
            out.write(' \\\\' + "\n")
            fields = row
            for c in columns:
                if c not in fields:
                    raise BaseException("No column %s found" % c)
        else:
            kv = {}
            for i, r in enumerate(row):
                try:
                    kv[fields[i]] = r
                except IndexError:
                    print "No field number %i in: %s" %\
                            (i, "|".join([str(r) for r in fields]))

            out.write("   \\hline\n")
            out.write('\\textbf{%d} & ' % num)
            out.write(' & '.join(['%s' % spec_format(c, kv[c]) for c in columns]))
            out.write(' \\\\' + "\n")

        num += 1

out.write("   \\hline\n")
out.write("  \\end{tabular}\n")
out.write(" \\end{center}\n")
out.write("\\end{table*}\n")
out.close()
