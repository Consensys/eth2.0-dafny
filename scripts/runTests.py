
#!/usr/bin/python

import sys
import os
import shutil

import time
import fileinput
import re
import argparse
import subprocess
import pickle
# from prettytable import PrettyTable # Install via: easy_install PrettyTable

import glob

def compile_and_run_dafny(dafny_filename):
  executable = "dafny"
  args  = [] 
  args += ["/noVerify"]
  args += ["/compile:4"]  # compile in memory and ignore verif.
  args += ["/nologo"]
  args += ["/env:0"]
  args += [dafny_filename]
  subprocess.run([executable] + args, shell=False)


def process_dir(root_dir):
    print(root_dir)
    # list files ending with .tests.dfy
    x = [os.path.join(os.getcwd(),f) for f in os.scandir(root_dir) if f.is_file() and f.name.endswith('.dfy')]
    for f in x:
        compile_and_run_dafny(f)
    # process the sub directories
    x = [os.path.join(os.getcwd(),f) for f in os.scandir(root_dir) if f.is_dir() and not f.name.startswith('.')]
    for d in x: 
            process_dir(d)

def main(srcDir):
    process_dir(srcDir)

if (__name__=="__main__"):
    main(sys.argv[1])
