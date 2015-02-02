import re
import sys

srcStartTag = sys.argv[1]
srcEndTag = sys.argv[2]
destStartTag = sys.argv[3]
destEndTag = sys.argv[4]
srcFile = open(sys.argv[5], "r")
destFile = open(sys.argv[6], "r")

# Gather source lines
def extractLines(startTag, endTag, file):
    ret = []
    start = False
    for line in file:
        if re.search(startTag, line): 
            start = True
        
        if re.search(endTag, line):
            start = False

        if start == True:
            ret.append(line)
    return ret

def getParts(topTag, bottomTag, file):
    topLines = []
    bottomLines = []
    top = True
    bottom = False
    for line in file:
        if re.search(topTag, line): 
            topLines.append(line)
            top = False
        
        if re.search(bottomTag, line):
            bottom = True

        if top:
            topLines.append(line)
            
        if bottom:
            bottomLines.append(line)    

    return topLines, bottomLines

srcLines = extractLines(srcStartTag, srcEndTag, srcFile)
topLines, bottomLines = getParts(destStartTag, destEndTag, destFile)

lines = topLines + srcLines + bottomLines

for line in lines:
    print(line, end='', flush=True)

