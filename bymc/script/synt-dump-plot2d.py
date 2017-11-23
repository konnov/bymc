#!/usr/bin/python
#
# Plot iteratively the solution space dumped by syntpa-schema
# with the flag -O synt.dump.vectors=var1,var2,...
#
# This plot expects data to track only two variables, i.e.,
# we can draw only 2D plots.
#
# Igor Konnov, 2017

import sys

from collections import defaultdict

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d import art3d


def read_dump(filename):
    data = []
    with open(filename, 'r+') as f:
        one_set = []
        for line in iter(f):
            if line.startswith("----"):
                if one_set != []:
                    data.append(one_set) # flush the data set
                one_set = []
            else:
                vec = []
                for assign in line.split(","):
                    (k, v) = assign.split("=")
                    vec.append(int(v))

                if len(vec) != 2:
                    raise Exception("Cannot draw %d-dimensional vectors" % len(vec))

                one_set.append(vec)
        else:
            if one_set != []:
                data.append(one_set) # flush the data set

    return data


# main
if __name__ == "__main__":
    if len(sys.argv) > 2:
        print "Use: %s synt-dump.txt" % sys.argv[0]
        sys.exit(1)

    data = read_dump(sys.argv[1])
    min_tuple = 3 * [100000]
    max_tuple = 3 * [-100000]
    for one_set in data:
        for vec in one_set:
            for (i, v) in enumerate(vec):
                if min_tuple[i] > v:
                    min_tuple[i] = v
                if max_tuple[i] < v:
                    max_tuple[i] = v

    # since we are using histograms, just stream all the data
    def up_gen(gen):
        data_x, data_y = [], []
        for one_set in data[:gen]:
            for vec in one_set:
                data_x.append(vec[0])
                data_y.append(vec[1])

        return data_x, data_y

    def leads_up_gen(gen):
        data_x, data_y = [], []
        for one_set in data[:gen]:
            if one_set != []:
                vec = one_set[0]
                data_x.append(vec[0])
                data_y.append(vec[1])

        return data_x, data_y

    # prepare some coordinates
    #coords = np.indices(tuple(max_tuple))
    for i in range(1, len(data) + 1):
        #i = len(data)
        fig = plt.figure()
        ax = fig.gca()
        ax.tick_params(axis='both', which='major', labelsize=18)
        data_x, data_y = up_gen(i)
        x_range = np.arange(min(data_x), max(data_x) + 2.0)
        plt.xticks(x_range) # show all ticks
        y_range = np.arange(min(data_y), max(data_y) + 2.0)
        plt.yticks(y_range) # show all ticks
        #ax.grid(True)
        # move things a bit for a histogram
        x_range = x_range -.5
        y_range = y_range -.5
        # plot the excluded areas as a heat map
        ax.hist2d(data_x, data_y, cmap='viridis',
                bins=[x_range, y_range], vmin=0.0)
        # plot the support solutions
        data_x, data_y = leads_up_gen(i)
        ax.plot(data_x, data_y, "r*", ms=20)
        fig.savefig('heat%d.png' % i)
        fig.savefig('heat%d.pdf' % i)

