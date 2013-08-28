#!/usr/bin/python
#
# Print line number before every line.
# It works like nl and cat -n, which are missing in busybox distributions.
#
# Igor Konnov, 2013

import sys

if len(sys.argv) == 1:
    fin = sys.stdin
else:
    fin = open(sys.argv[1], 'r')

num = 1
try:
    for l in fin:
        sys.stdout.write("%6d  %s" % (num, l))
        num += 1
finally:
    fin.close()
