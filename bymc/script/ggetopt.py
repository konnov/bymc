#!/usr/bin/env python
#
# A simple and portable implementation of GNU getopt in python.
# This is needed to run our scripts both in Linux and MacOSX.
#
# This script implements the POSIXLY_CORRECY version of getopt.
#
# Igor Konnov, 2018

from getopt import getopt, GetoptError
import sys

def convert_longopt(long_opt):
    if long_opt.endswith(":"):
        return long_opt[:-1] + "="
    else:
        return long_opt


if __name__ == "__main__":
    opts = []
    long_opts = []
    name = sys.argv[0]
    args = sys.argv[1:]
    left = args
    while left != []:
        arg = left.pop(0)
        if arg in ["-o", "--options"]:
            # short options
            opts = left.pop(0)
        elif arg in ["-l", "--long", "--longoptions"]:
            # long options
            lopts = left.pop(0).split(",")
            long_opts = [convert_longopt(o) for o in lopts]
        elif arg in ["-n", "--name"]:
            # name to use
            name = left.pop(0)
        else:
            # POSIXLY_CORRECT: the first non-option argument stops the search
            left = [arg] + left if arg != "--" else left
            break

    if opts == [] and long_opts == []:
        print "%s: missing optstring argument" % name
        sys.exit(1)
    
    # whatever is left is the arguments to getopt
    try:
        opt_vals, trailing = getopt(left, opts, long_opts)   
        for opt, val in opt_vals:
            sys.stdout.write(" %s" % opt)
            if val:
                sys.stdout.write(" '%s'" % val)

        sys.stdout.write(" --")
        for val in trailing:
            sys.stdout.write(" '%s'" % val)

        print ""
    except GetoptError as err:
        print >>sys.stderr, "%s: %s" % (name, err.msg)
        sys.exit(1)

