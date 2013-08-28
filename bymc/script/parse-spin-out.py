#!/usr/bin/python
#
# parse the Spin output
#
# Igor Konnov, 2012

import re
import sys

def match(re_text, line):
    return re.compile(re_text).match(line)

def parse(f):
    data = {}
    data["10:Result"] = "ERROR"

    line = f.readline()
    while line:
        line = line[:-1] # remove the trailing \n

        m = match('^.*State-vector\s+(\d+)\s+byte, depth reached\s+(\d+),\s+errors:\s+(\d+)', line)
        if m:
            data['19:VectorSize'] = m.group(1)
            data['16:Depth'] = m.group(2)
            if int(m.group(3)) > 0:
                data["10:Result"] = "FAILED"
            elif data["10:Result"] == "ERROR":
                data["10:Result"] = "SUCCESS"
        m = match('pan: reached -DMEMLIM bound', line)
        if m:
            data["10:Result"] = "OUT OF MEMORY"
        m = match('pan: out of memory', line)
        if m:
            data["10:Result"] = "OUT OF MEMORY"
        m = match('error: max search depth too small', line)
        if m:
            data["10:Result"] = "DEPTH TOO SMALL"
        m = match('^\s*(\S+)\s+states,\s+stored\s*\((\S+)\s+visited\)', line)
        if m:
            data['11:Visited'] = m.group(2)
            data['12:Stored'] = m.group(1)
        m = match('^\s*(\S+)\s+states,\s+stored', line)
        if m:
            data['11:Visited'] = m.group(1)
            data['12:Stored'] = m.group(1)
        m = match('^\s*(\S+) states, matched', line)
        if m:
            data['17:Matched'] = m.group(1)
        m = match('^\s*(\S+) transitions', line)
        if m:
            data['13:Transitions'] = m.group(1)
        m = match('^\s*hash conflicts:\s*(\S+) \(resolved\)', line)
        if m:
            data['18:Conflicts'] = m.group(1)
        m = match('^\s*(\d+\.\d+).*memory usage', line)
        if m:
            data['15:SpinMemory'] = m.group(1)
        m = match('^\s*(\d+\.\d+).*total actual memory usage', line)
        if m:
            data['15:SpinMemory'] = m.group(1)
        m = match('^pan:\s+elapsed\s+time\s+(.*)', line)
        if m:
            data['14:SpinTime'] = m.group(1)

        line = f.readline()

    return data


f = open(sys.argv[1], 'r')
try:
    data = parse(f)
finally:
    f.close()

l = ["%s=%s" % (k, v) for k, v in data.items()]
print "|".join(l)
