#!/usr/bin/python
#
# Print line number before every line.
# It works like nl and cat -n, which are missing in busybox distributions.
# An additional second argument limits the number of lines.
#
# Igor Konnov, 2013

import getopt
import sys

def usage(exitcode):
    print "Use: %s [-n limit] filename" % sys.argv[0]
    sys.exit(exitcode)


try:
    opts, args = getopt.getopt(sys.argv[1:], "hn:")
except getopt.GetoptError as err:
    print str(err)
    usage(2)

limit = 0

for o, a in opts:
    if o == "-h":
        usage(1)
    elif o == "-n":
        limit = int(a)
    else:
        usage(3)


if len(args) == 0:
    fin = sys.stdin
else:
    fin = open(args[0], 'r')

num = 1
try:
    for l in fin:
        if num > limit and limit != 0:
            sys.stdout.write("[...]\n")
            break

        sys.stdout.write("%6d  %s" % (num, l))
        num += 1
finally:
    fin.close()
