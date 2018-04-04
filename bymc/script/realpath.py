#!/usr/bin/env python
#
# a portable version of readlink -f (should work with Linux and MacOS)
import os
import sys

print os.path.realpath(sys.argv[1])
