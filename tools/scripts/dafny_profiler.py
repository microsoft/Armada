#!/usr/bin/python

import sys
import os
import subprocess
import re

def docmd(*cmd):
    print "cmd:", " ".join(cmd)
    subprocess.call(cmd)

def process_log():
    fd_in = open("z3.log", "r")
    fd_out = open("profile.log", "w")
    counts = {}
    for line in fd_in.readlines():
        m = re.search(r'^\[mk\-quant\]\s+#\d*\s+([^\s]+)\s', line)
        if m:
            pattern = m.group(1)
            if pattern in counts:
                counts[pattern] = counts[pattern] + 1
            else:
                counts[pattern] = 1
    patterns = list(counts.items())
    patterns = sorted(patterns, key=lambda kv : kv[1], reverse=True)
    for item in patterns:
        (key, value) = item
        fd_out.write("%d\t%s\n" % (value, key))
    fd_in.close()
    fd_out.close()
    print "*** For profile output, see profile.log ***"
    
def main(args):
    (thisprog,dfyfile,procname) = args
    boogieFile = dfyfile.replace(".dfy", ".bpl")
    escapedProcName = procname.replace("_", "__")
    docmd("/e/Apps/Dafny/Binaries/dafny.exe", "/timeLimit:1", "/noVerify", "/arith:5", "/compile:0", "/print:%s" % boogieFile, dfyfile)

    boogieFileHandle = open(boogieFile, 'r')
    mangledProcName = ''
    mangledCheckFormedName = ''
    for line in boogieFileHandle:
        m = re.search(r'^procedure\s*({:[^}]*}\s*)*(Impl[^\(]+)', line)
	if m:
            procedureName = m.group(2)
            if len(procedureName) > len(escapedProcName) and procedureName[len(procedureName)-len(escapedProcName)-1:] == "." + escapedProcName:
                mangledProcName = procedureName
                break
        m = re.search(r'^procedure\s*({:[^}]*}\s*)*(CheckWellformed[^\(]+)', line)
	if m:
            procedureName = m.group(2)
            if len(procedureName) > len(escapedProcName) and procedureName[len(procedureName)-len(escapedProcName)-1:] == "." + escapedProcName:
                mangledCheckFormedName = procedureName
    boogieFileHandle.close()
    if len(mangledProcName) == 0:
        mangledProcName = mangledCheckFormedName
        if len(mangledCheckFormedName) == 0:
            print 'Could not find implementation or check-formedness procedure with substring %s in %s' % (escapedProcName, boogieFile)
            sys.exit(-1)
        else:
            print 'Warning:  Could not find implementation procedure with substring %s, so using check-formedness procedure' % (escapedProcName)
            
    z3log = "z3.log"
    if (os.path.exists(z3log)):
        os.unlink(z3log)
    docmd("/e/Apps/Boogie/Binaries/boogie.exe", "/z3opt:nlsat.randomize=false", "/z3opt:smt.arith.nl=false", "/z3opt:pi.warnings=true", "/z3opt:trace=true", "/timeLimit:30", "/proc:%s" % mangledProcName, "/trace", boogieFile)

if __name__ == '__main__':
    main(sys.argv)
    process_log()
