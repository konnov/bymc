#!/usr/bin/python
#
# Convert verdict.txt to a CSV file with a header 

import sys

fin = sys.stdin
columns = set()
rows = []

line = fin.readline()
while line:
    line = line[:-1]
    fields = line.split("|")
    row = {}
    for f in fields:
        if f.strip() != "":
            k, v = f.split("=")
            row[k] = v
            columns.add(k)

    rows.append(row)
    line = fin.readline()

cols = list(columns)
cols.sort()
print ",".join(cols)

for r in rows:
    lst = []
    for c in cols:
        if r.has_key(c):
            lst.append(r[c])
        else:
            lst.append("")

    print ",".join(lst)

