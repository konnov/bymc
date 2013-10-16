#!/usr/bin/python

import sys

f = open("yices.log", "r")
pushes = 0
pops = 0
level = 0
for l in f:
    if l.strip() == '(push)':
        pushes += 1
        level += 1
        print "pushes = %d" % pushes
    elif l.strip() == '(pop)':
        level -= 1
        pops += 1

    if level < 0:
        sys.stdout.write(l)
        raise Exception("Context stack is exhausted")
else:
    f.close()


print "pushes = %d, pops = %d, level = %d" % (pushes, pops, level)

