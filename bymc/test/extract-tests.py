#!/usr/bin/python

import os
import sys

filename = sys.argv[1]
prefix, _ = os.path.splitext(os.path.basename(filename))

test_no = 1
f = open(filename, "r")
out = None
eva = None
disabled = False
try:
    for l in f:
        if l.find('BEGIN-TEST') != -1:
            out = open('%s-%d.test' % (prefix, test_no), 'w+')
            out.write('testsource=%s\n' % filename)
            eva = open('%s-%d.eval' % (prefix, test_no), 'w+')
            eva.write('set -e\n')
        elif l.find('DISABLED-TEST') != -1:
            disabled = True
            out = open('%s-%d.test' % (prefix, test_no), 'w+')
            eva = open('%s-%d.eval' % (prefix, test_no), 'w+')
            eva.write("echo 'DISABLED. Failed, in order to keep you warned.' && exit 101")
        elif l.find('END-TEST') != -1:
            out.close()
            eva.close()
            out = None
            eva = None
            test_no += 1
            disabled = False
        elif l.find('EXPECT') != -1:
            pos = l.find('EXPECT')
            if not disabled:
                eva.write(l[pos + len('EXPECT') :])
        elif out != None:
            if not disabled:
                out.write(l)
finally:
    f.close()
