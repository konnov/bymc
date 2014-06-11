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
            name = l[l.rfind('BEGIN-TEST') + len('BEGIN-TEST') :].strip()
            out = open('%s-%d-%s.test' % (prefix, test_no, name), 'w+')
            out.write('testsource=%s\n' % filename)
            eva = open('%s-%d-%s.eval' % (prefix, test_no, name), 'w+')
            eva.write('set -e\n')
        elif l.find('SKIP-TEST') != -1:
            name = l[l.rfind('SKIP-TEST') + len('SKIP-TEST') :].strip()
            disabled = True
            out = open('%s-%d-%s.test' % (prefix, test_no, name), 'w+')
            eva = open('%s-%d-%s.eval' % (prefix, test_no, name), 'w+')
            eva.write("echo 'SKIP. Failed, in order to keep you warned.' && exit 101")
        elif l.find('TODO-TEST') != -1:
            name = l[l.rfind('TODO-TEST') + len('TODO-TEST') :].strip()
            disabled = True
            out = open('%s-%d-%s.test' % (prefix, test_no, name), 'w+')
            eva = open('%s-%d-%s.eval' % (prefix, test_no, name), 'w+')
            eva.write("echo 'TODO. Failed, in order to keep you warned.' && exit 102")
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
