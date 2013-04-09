#!/usr/bin/python
#
# Generate scheduler-like behavior to explore the efficiency of
# counter abstraction in NuSMV
#
# Igor Konnov, 2013

num_procs = 70
dsize = 5

def gen_spec(fo):
    fo.write('CTLSPEC NAME reach1 := AG (k%d = %d -> k0 >= 0)\n'
            % (num_procs - 1, 1))
    fo.write('LTLSPEC NAME live := G (k%d = %d -> F G (k%d = %d))\n'
            % (0, 1, num_procs - 1, dsize - 1))


def gen_mono(filename):
    fo = open(filename, 'w+')
    fo.write('MODULE main\n')
    fo.write('VAR\n')
    for i in range(num_procs):
        fo.write('  k%d: {%s};\n'
                % (i, ", ".join([str(d) for d in range(dsize)])))

#    fo.write('IVAR\n')
#    fo.write('  idx: {%s};\n' % ", ".join([str(i) for i in range(0, num_procs)]))
    fo.write('INIT\n')
    fo.write('  k0=%d & %s\n'
            % (dsize - 1,
               " & ".join(['k%d = 0' % i for i in range(1, num_procs)])))
    fo.write('TRANS\n')
    fo.write('  %s\n'
        % " & ".join(["next(k%d) = k%d" % (j, j)
            for j in range(num_procs)]))
    for i in range(num_procs - 2):
        keep = " & ".join(["next(k%d) = k%d" % (j, j)
            for j in range(0, num_procs) if j not in [i, i + 1, i + 2]])
        for x in range(1, dsize):
            for y in range(0, dsize - 1):
                # dec/inc
                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
                    % (i, x, i+1, y, i, x - 1, i+1, y + 1, i+2, i+2, keep))
                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
                    % (i, x, i+2, y, i, x - 1, i+2, y + 1, i+1, i+1, keep))
                # eq/inc
                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
                    % (i, x, i+1, y, i, x, i+1, y + 1, i+2, i+2, keep))
                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
                    % (i, x, i+2, y, i, x, i+2, y + 1, i+1, i+1, keep))
                # dec/eq
#                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
#                    % (i, x, i+1, y, i, x - 1, i+1, y, i+2, i+2, keep))
#                fo.write('  | (k%d = %d & k%d = %d & next(k%d) = %d & next(k%d) = %d & next(k%d)=k%d & %s)\n'
#                    % (i, x, i+2, y, i, x - 1, i+2, y, i+1, i+1, keep))

    gen_spec(fo)        

    fo.close()

def gen_cluster(filename):
    fo = open(filename, 'w+')
    fo.write('MODULE main\n')
    fo.write('IVAR\n')
    fo.write('  from: {%s};\n' % ", ".join([str(i) for i in range(num_procs)]))
    fo.write('  to: {%s};\n' % ", ".join([str(i) for i in range(num_procs)]))
    fo.write('VAR\n')
    for i in range(num_procs):
        fo.write('  k%d: {%s};\n'
                % (i, ", ".join([str(d) for d in range(dsize)])))
    for i in range(num_procs - 2):
        if i > 0:
            p1 = "k%d" % (i - 1)
        else:
            p1 = "0"
        if i > 1:
            p2 = "k%d" % (i - 2)
        else:
            p2 = "0"
        fo.write('  ktr%d: KTR%d(from, to, %s, %s, k%d);\n' \
                % (i, i, p1, p2, i))

    fo.write('INIT\n')
    fo.write('  k0=%d & %s\n'
            % (dsize - 1,
               " & ".join(['k%d = 0' % i for i in range(1, num_procs)])))

    gen_spec(fo)        

    def mk(i):
        fo.write('MODULE KTR%d(f, t, p1, p2, k)\n' % i)
        fo.write('  ASSIGN\n')
        fo.write('   next(k) :=\n')
        fo.write('    case\n')
        for x in range(1, dsize):
            if i < num_procs - 1:
                fo.write('      f = %d & t = %d & k = %d : {%d, %d};\n' \
                        % (i, i + 1, x, x - 1, x))
            if i < num_procs - 2:
                fo.write('      f = %d & t = %d & k = %d : {%d, %d};\n' \
                        % (i, i + 2, x, x - 1, x))
        for x in range(0, dsize - 1):
            if 1 <= i:
                fo.write('      f = %d & t = %d & p1 > 0 & k = %d : %d;\n' \
                        % (i - 1, i, x, x + 1))
            if 2 <= i:
                fo.write('      f = %d & t = %d & p2 > 0 & k = %d : %d;\n' \
                        % (i - 2, i, x, x + 1))

        fo.write('      TRUE : k;\n')
        fo.write('    esac;\n')

    for i in range(num_procs):
        mk(i)

    fo.close()


if __name__ == '__main__':
    gen_mono('mono.smv')
    gen_cluster('cluster.smv')
