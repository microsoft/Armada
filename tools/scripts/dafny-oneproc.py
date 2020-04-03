#!/usr/bin/python

import sys
import os
import subprocess
import re
import datetime
os.environ["PATH"] = "tools/Dafny:"+os.environ["PATH"]

def docmd(*cmd):
    print "cmd:", " ".join(cmd)
    subprocess.call(cmd)
    
def main():
    (thisprog,dfyfile,procname) = sys.argv
    boogieFile = dfyfile.replace(".dfy", ".bpl")
    escapedProcName = procname.replace("_", "__")
    docmd("dafny.exe", "/timeLimit:1", "/allowGlobals", "/noVerify", "/print:%s" % boogieFile, dfyfile)

    boogieFileHandle = open(boogieFile, 'r')
    mangledProcName = ''
    for line in boogieFileHandle:
        m = re.search(r'^procedure\s*({:[^}]+}\s*)*(Impl[^\(]+)', line)
	if m:
            procedureName = m.group(2)
            if len(procedureName) > len(escapedProcName):
                suffix = procedureName[len(procedureName) - len(escapedProcName) - 1:]
                if suffix == '.' + escapedProcName:
                    mangledProcName = procedureName
                    break
    boogieFileHandle.close()
    if len(mangledProcName) == 0:
        print 'Could not find procedure ending in .%s in %s' % (escapedProcName, boogieFile)
        sys.exit(-1)

    start_time = datetime.datetime.now()
    docmd("dafny.exe", "/allowGlobals", "/allocated:1", "/proverWarnings:1", "/compile:0", "/noCheating:1", "/arith:5", "/timeLimit:30", "/proc:%s" % mangledProcName, dfyfile)
    end_time = datetime.datetime.now()
    docmd("rm", boogieFile)
    print 'Boogie time was %s sec' % ((end_time - start_time).total_seconds())

main()
