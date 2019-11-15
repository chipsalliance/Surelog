#!/usr/bin/env python3

import os, time
from pathlib import Path
 
def getListOfFiles(dirName):
    listOfFile = os.listdir(dirName)
    allFiles = list()
    for entry in listOfFile:
        fullPath = os.path.join(dirName, entry)
        if os.path.isdir(fullPath):
            allFiles = allFiles + getListOfFiles(fullPath)
        else:
            if Path(fullPath).suffix==".status":
                allFiles.append(fullPath)
                
    return allFiles        
 
 
def main():
    listOfFiles = getListOfFiles('.')
    listOfFiles.sort()
    testsuits = list()
    casenumber = dict()
    errors = dict()
    failures = dict()
    total_errors = 0
    total_failures = 0
    min_start_time = time.time()
    max_end_time = 0
    for elem in listOfFiles :
        st = elem.split('/')
        testsuit = st[1]
        testcase = st[-1].replace('.status','')
        if (testsuit not in testsuits):
            testsuits.append(testsuit)
            casenumber[testsuit] = 0
            errors[testsuit] = 0
            failures[testsuit] = 0
        casenumber[testsuit] += 1
        status = open(elem, 'r').read().strip()
        min_start_time = min(min_start_time, os.path.getmtime(os.path.join(os.path.dirname(elem),'.start')))
        max_end_time = max(max_end_time, os.path.getmtime(os.path.join(os.path.dirname(elem),'.stamp')))
        if (status=='ERROR'):
            errors[testsuit] += 1
            total_errors += 1
        if (status=='FAIL'):
            failures[testsuit] += 1
            total_failures += 1
    # Creating report
    with open("report.xml", "w") as f:
        print('<?xml version="1.0" encoding="UTF-8"?>', file=f)
        print('<testsuites disabled="0" errors="%d" failures="%d" tests="%d" time="%d">' % (total_errors, total_failures, len(listOfFiles), max_end_time - min_start_time), file=f)
        for suite in testsuits:
            print('    <testsuite disabled="0" errors="%d" failures="%d" name="%s" skipped="0" tests="%d" time="%d">' % (errors[suite], failures[suite], suite, casenumber[suite], 0), file=f)        
            for elem in listOfFiles :
                st = elem.split('/')
                testsuit = st[1]
                if (testsuit != suite):
                    continue
                testcase = st[-1].replace('.status','')
                casenumber[testsuit] += 1
                status = open(elem, 'r').read().strip()
                print('        <testcase classname="%s.%s" name="%s" status="%s" time="%d">' % (testsuit, st[2].replace('.status',''), testcase, status, 
                    os.path.getmtime(os.path.join(os.path.dirname(elem),'.stamp')) - os.path.getmtime(os.path.join(os.path.dirname(elem),'.start'))), file=f)
                if (status=='ERROR'):
                    print('            <error message="%s" type="%s"/>' % (status, status), file=f)
                if (status=='FAIL'):
                    print('            <failure message="%s" type="%s"/>' % (status, status), file=f)
                    file_tb = os.path.join(os.path.dirname(elem),'testbench.log')
                    file_re = os.path.join(os.path.dirname(elem),'result.log')
                    file_ys = os.path.join(os.path.dirname(elem),'yosys.log')
                    if (os.path.isfile(file_tb)):
                        print('<system-out>', end="", file=f)
                        with open(file_tb, "r") as logf:
                            for line in logf:
                                print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
                        print('</system-out>', file=f)
                    elif (os.path.isfile(file_re)):
                        print('<system-out>', end="", file=f)
                        with open(file_re, "r") as logf:
                            for line in logf:
                                print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
                        print('</system-out>', file=f)
                    elif (os.path.isfile(file_ys)):
                        print('<system-out>', end="", file=f)
                        with open(file_ys, "r") as logf:
                            for line in logf:
                                print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
                        print('</system-out>', file=f)
                print('        </testcase>', file=f)
            
            print('    </testsuite>', file=f)

        print('</testsuites>', file=f)
if __name__ == '__main__':
    main()
