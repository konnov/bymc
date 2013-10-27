#!/usr/bin/python

import os
import sys

filename = sys.argv[1]
prefix, _ = os.path.splitext(os.path.basename(filename))

test_no = 1
f = open(filename, "r")
out = None
eva = None
try:
    for l in f:
        if l.find('BEGIN-TEST') != -1:
            out = open('%s-%d.test' % (prefix, test_no), 'w+')
            out.write('testsource=%s\n' % filename)
            eva = open('%s-%d.eval' % (prefix, test_no), 'w+')
            eva.write('set -e\n')
        elif l.find('END-TEST') != -1:
            out.close()
            out = None
            eva.close()
            eva = None
            test_no += 1
        elif l.find('EXPECT') != -1:
            pos = l.find('EXPECT')
            eva.write(l[pos + len('EXPECT') :])
        elif out != None:
            out.write(l)
finally:
    f.close()
