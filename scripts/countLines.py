#!/usr/bin/python

# Credit IronFleet code base

import sys
import os
import shutil

import time
import fileinput
import re
import argparse
import subprocess
import pickle
from prettytable import PrettyTable # Install via: easy_install PrettyTable

class DafnyFile:
  def __init__(self, filename, verify_time):
    self.filename = filename.replace('\\', '/')
    self.verify_time = verify_time
    self.spec = 0
    self.impl = 0
    self.proof = 0

  def __repr__(self):
    return f"{self.filename} {self.verify_time} secs {self.spec} spec {self.impl} impl {self.proof} proof"

  def is_spec(self):
    return self.filename.endswith(".s.dfy")

def parse_nubuild(nubuild_output_file):
  dafny_files = []
  with open(nubuild_output_file, "r") as nubuild_output:
    for line in nubuild_output:
      if result := re.search(
          "DafnyVerifyOneVerb\(#\d+,(.*),\) Success\s+([.0-9]+)s", line):
        filename = result.group(1)
        time = result.group(2)
        dfile = DafnyFile(filename, time)
        dafny_files += [dfile]

  return dafny_files

def run_dafny(iron_base, show_ghost, dafny_filename, tmp_filename):
#   executable = iron_base + "/tools/Dafny/Dafny.exe"
  executable = "dafny"
  args  = []
  args += ["/rprint:-"]
  args += ["/noAutoReq"]
  args += ["/noVerify"]
  args += ["/nologo"]
  args += ["/env:0"]
  args += ["/printMode:NoIncludes"] if show_ghost else ["/printMode:NoGhost"]
  args += [dafny_filename]

  with open(tmp_filename, "w") as tmp_file:
    #print [executable] + args
    subprocess.call([executable] + args, shell=False, stdout=tmp_file)

# Remove detritus from running Dafny
def clean_dafny_output(filename):
  with open(filename, "r") as file:
    clean = "".join(line + "\n" for line in file
                    if not line.startswith("Dafny program verifier finished"))
  with open(filename, "w") as file:
    file.write(clean)

def run_sloccount(iron_base, tmp_dir):
#   executable = "sloccount"
#   args  = [] 
#   args += ["--details"]
#   args += [tmp_dir]

  executable = "csh_count"
  args = []
#   args += ["/"] 
  args +=  [tmp_dir] 

#   executable = "ls"
#   args = ["-al"]  

  tab = PrettyTable(["Filename", "#LoC"])
  tab.align["Filename"] = "l"
  tab.align["#LoC"] = "r"

  sloc = -1
  totalLoc = 0

#   linesInFile = subprocess.checkoutput(["cat", ])
#   print ([executable] + args)
  output = subprocess.check_output([executable] + args)  #shell=True,
#   print(output)
#   print(output.stderr)
  output = output.decode("utf-8")
  for line in output.split('\n'):
    if result := re.search("(\d+)\s+tmp/(\S+)", line):
      sloc = result.group(1)
      filename = result.group(2)
      totalLoc += int(sloc)
      tab.add_row([filename, sloc])

      print(filename, sloc)

  if sloc == -1:
    raise Exception("Failed to find sloccount result!")
  tab.add_row(["", ""])
  tab.add_row(["Total ", totalLoc])
  print(tab)
  return totalLoc

def compute_sloc(iron_base, show_ghost, dafny_file, tmp_dir):
  tmp_file = tmp_dir + dafny_file
#   print(tmp_file)
  run_dafny(iron_base, show_ghost, dafny_file, tmp_file)
  clean_dafny_output(tmp_file)
#   sloc = run_sloccount(iron_base, tmp_dir)
#   print("--", sloc)
#   os.remove(tmp_file)
#   sloc = 0
  return 0

def collect_line_counts(iron_base, dafny_files):
  tmp_dir = "tmp/"

  if not os.path.exists(tmp_dir):
    os.makedirs(tmp_dir)

  for f in dafny_files:
    print(f"Processing {f.filename}")
    ghost_sloc = compute_sloc(iron_base, True, f.filename, tmp_dir)

  run_sloccount("", "tmp/*.*")
  shutil.rmtree("tmp")


    # if f.is_spec():
    #   f.spec = ghost_sloc
    #   f.verify_time = 0
    # else:
    #   impl_sloc = compute_sloc(iron_base, False, f.filename, tmp_dir)
    #   f.impl = impl_sloc
    #   f.proof = ghost_sloc - impl_sloc

def define_categories():
  return {
      'src/Dafny/Distributed/Impl/LiveSHT':
      'kv_impl',
      'src/Dafny/Distributed/Impl/SHT':
      'kv_impl',
      'src/Dafny/Distributed/Impl/Paxos':
      'rsl_impl',
      'src/Dafny/Distributed/Common':
      'Common Libraries',
      'src/Dafny/Distributed/Impl/Common':
      'Common Libraries',
      'src/Dafny/Distributed/Protocol/Common':
      'Common Libraries',
      'src/Dafny/Libraries':
      'Common Libraries',
      'src/Dafny/Drivers':
      'Common Libraries',
      'src/Dafny/Distributed/Common/Logic/Temporal':
      'TLA Library',
      'src/Dafny/Distributed/Common/Logic/Temporal/Temporal.s.dfy':
      'Temporal Logic',
      'src/Dafny/Distributed/Common/Logic/Temporal/Time.s.dfy':
      'Temporal Logic',
      'src/Dafny/Distributed/Protocol/Paxos/Common':
      'rsl_proto',
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL':
      'rsl_proto',
      'src/Dafny/Distributed/Protocol/SHT':
      'kv_proto',
      'src/Dafny/Distributed/Protocol/LiveSHT/Scheduler.i.dfy':
      'kv_proto',
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/DirectRefinement':
      'rsl_refine',
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/CommonProof':
      'rsl_refine',  #'src/Dafny/Distributed/Protocol/Paxos/RSL/': 'rsl_refine',\
      #'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/RefinementProof': 'rsl_refine',\
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/LivenessProof':
      'rsl_live',
      'src/Dafny/Distributed/Protocol/SHT/InvProof.i.dfy':
      'kv_refine',
      'src/Dafny/Distributed/Protocol/SHT/InvDefs.i.dfy':
      'kv_refine',
      'src/Dafny/Distributed/Protocol/SHT/Refinement.i.dfy':
      'kv_refine',
      'src/Dafny/Distributed/Protocol/SHT/RefinementProof.i.dfy':
      'kv_refine',
      'src/Dafny/Distributed/Protocol/LiveSHT/':
      'kv_refine',
      'src/Dafny/Distributed/Protocol/LiveSHT/CommonProof':
      'kv_live',
      'src/Dafny/Distributed/Protocol/LiveSHT/LivenessProof':
      'kv_live',
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/StateMachine.s.dfy':
      'rsl_spec',
      'src/Dafny/Distributed/Protocol/Paxos/LiveRSL/DirectRefinement/StateMachine.i.dfy':
      'rsl_spec',
      'src/Dafny/Distributed/Protocol/SHT/HT.s.dfy':
      'kv_spec',
      'src/Dafny/Distributed/Common/Native/Io.s.dfy':
      'IO/Native Interface',
      'src/Dafny/Distributed/Common/Native/NativeTypes.s.dfy':
      'IO/Native Interface',
      'src/Dafny/Distributed/Protocol/Common/Liveness/Environment.s.dfy':
      'IO/Native Interface',
      'src/Dafny/Distributed/Protocol/Common/Liveness/EnvironmentSynchrony.s.dfy':
      'IO/Native Interface',
      'src/Dafny/Distributed/Protocol/Common/NodeIdentity.s.dfy':
      'IO/Native Interface',
  }

def categorize_files(dafny_files):
  categorized_files = {}
  dir_categories = define_categories()

  for dfile in dafny_files:
    best_match_prefix = ""
    best_match_cat = "Unknown"
    for prefix in dir_categories.keys():
      if dfile.filename.startswith(prefix) and len(prefix) > len(best_match_prefix):
        best_match_prefix = prefix
        best_match_cat = dir_categories[prefix]
    if best_match_cat not in categorized_files:
      categorized_files[best_match_cat] = [dfile]
    else:
      categorized_files[best_match_cat] += [dfile]

  for cat in sorted(categorized_files.keys()):
    print
    print (cat)
    print ("-----------------------------")
    for f in categorized_files[cat]:
      print (f)

  return categorized_files

class SubTable:
  def __init__(self, name, row_names, allow_impl):
    self.name = name
    self.rows = row_names
    self.allow_impl = allow_impl

def amt(string, pos='c'):
  return "--" if int(string) == 0 else string

def define_labels():
  return {
      'rsl_spec': "IronRSL",
      'kv_spec': "IronKV",
      'rsl_proto': "IronRSL Protocol",
      'rsl_refine': "\hspace{11mm}Refinement",
      'rsl_live': "\hspace{11mm}Liveness",
      'kv_proto': "IronKV Protocol",
      'kv_refine': "\hspace{10mm}Refinement",
      'kv_live': "\hspace{10mm}Liveness",
      'rsl_impl': "IronRSL",
      'kv_impl': "IronKV",
  }

def table_label(key):
  labels = define_labels()
  return labels[key] if key in labels else key

def build_table(categorized_files, latex_file):
  spec = SubTable("High-Level Spec", ['rsl_spec', 'kv_spec', 'Temporal Logic'], allow_impl=False)
  protocol = SubTable("Distributed Protocol", \
                      ['rsl_proto', \
                       'rsl_refine', \
                       'rsl_live', \
                       'kv_proto', \
                       'kv_refine', \
                       'kv_live',\
                       'TLA Library', \
                     ], allow_impl=False)
  impl = SubTable("Implementation", \
                  ['IO/Native Interface', 'Common Libraries', 'rsl_impl', 'kv_impl'], \
                  allow_impl=True)

  tables = [spec, protocol, impl]

  latex  = ""
#  latex += r"\begin{tabular}{" + "\n"
#  latex += r"@{}" + "\n"
#  latex += r"*{1}{>{\raggedright\arraybackslash}b{.16\textwidth}}  @{ } % " + "\n"
#  latex += r"*{1}{>{\raggedleft\arraybackslash}b{.05\textwidth}}  @{ } % Spec" + "\n"
#  latex += r"*{1}{>{\raggedleft\arraybackslash}b{.05\textwidth}}  @{ }  % Impl" + "\n"
#  latex += r"*{1}{>{\raggedleft\arraybackslash}b{.05\textwidth}}  @{ }   % Proof" + "\n"
#  latex += r"*{1}{>{\raggedleft\arraybackslash}b{.001\textwidth}}  @{ }   % dummy" + "\n"
#  latex += r"*{1}{>{\raggedleft\arraybackslash}b{.09\textwidth}} @{ }  % time to verify " + "\n"
#  latex += r"@{}" + "\n"
#  latex += r"}" + "\n"
#  latex += r"& \multicolumn{1}{c}{\textbf{Spec}} & \multicolumn{1}{c}{\textbf{Impl}} & \multicolumn{1}{c}{\textbf{Proof}} & & \multicolumn{1}{c}{\textbf{Time to Verify}}\\" + "\n"
#  latex += r"& \multicolumn{3}{c}{(source lines of code)} & & \multicolumn{1}{c}{(minutes)}\\" + "\n"
#  latex += "\n"
#  latex += r"\midrule" + "\n\n"

  total_spec_sloc = 0
  total_impl_sloc = 0
  total_proof_sloc = 0
  total_verify = 0

  for subtable in tables:
    print
    print (subtable.name)
    latex += "\\textbf{%s:} &&&& \\\\\n" % (subtable.name)
    tab = PrettyTable(["Category", "Spec", "Impl", "Proof", "Time To Verify"])
    for row in subtable.rows:
      spec_sloc = 0
      impl_sloc = 0
      proof_sloc = 0
      verify = 0
      for file in categorized_files[row]:
        if file.filename.startswith('src/Dafny/Libraries/') or file.filename.startswith('src/Dafny/Drivers/'): 
          # Temporary hack, since we have a bunch of legacy .s files that really should be .i
          proof_sloc += file.spec + file.proof
          impl_sloc += file.impl
        elif file.filename.endswith("DirectRefinement/StateMachine.i.dfy")\
          or file.filename.endswith("Assumptions.i.dfy")\
          or file.filename.endswith("Protocol/SHT/Refinement.i.dfy"):
          # Temporary hack for files that should be a .s
          spec_sloc += file.spec + file.proof + file.impl
          verify -= float(file.verify_time)
        else:
          spec_sloc += file.spec
          proof_sloc += file.proof
          impl_sloc += file.impl
        verify += float(file.verify_time)
      if not(subtable.allow_impl):
        proof_sloc += impl_sloc
        impl_sloc = 0
      # Temporary hack due to failure of spec discovery
      if subtable.name == "High-Level Spec":
        verify = 0
      row_label = table_label(row)
      verify_min = verify / 60
      tab.add_row([row_label, spec_sloc, impl_sloc, proof_sloc, verify_min])
      latex += "%s & %s & %s & %s && %s \\\\\n" % (row_label, amt(spec_sloc,'l'), amt(impl_sloc,'c'), amt(proof_sloc,'r'), amt(int(verify_min)))

      total_spec_sloc += spec_sloc
      total_impl_sloc += impl_sloc
      total_proof_sloc += proof_sloc
      total_verify += verify

    print (tab)
    print
    latex += "\\midrule\n"
  latex += "Total & %s & %s & %s && %s \\\\\n" % (total_spec_sloc, total_impl_sloc, total_proof_sloc, int(total_verify/60))
#  latex += "\\bottomrule\n"
#  latex += "\\end{tabular}\n"

  print
  print (latex)
  with open(latex_file, "w") as latex_out:
    latex_out.write(latex)


def main():
  parser = argparse.ArgumentParser(description='Compute Dafny line counts')
  parser.add_argument('-r', '--root', help="Iron root directory", required=True)
#   parser.add_argument('-n', '--nubuild', help="Output from running ./bin_tools/NuBuild/NuBuild.exe BatchDafny src/Dafny/Distributed/apps.dfy.batch", required=True)
  parser.add_argument('-c', '--cache', help="Use the specified file for caching per-file line counts", required=False)
#   parser.add_argument('-l', '--latex', help="File for the LaTeX table", required=True)
  args = parser.parse_args()

#  roots = [ \
#    "src/Dafny/Distributed/Protocol/SHT/RefinementProof.i.dfy",\
#    "src/Dafny/Distributed/Protocol/LiveSHT/SHTLemmas.i.dfy",\
#    "src/Dafny/Distributed/Impl/LiveSHT/Main.i.dfy",\
#    "src/Dafny/Distributed/Protocol/Paxos/LiveRSL/RefinementProof/DistributedSystemLemmas.i.dfy",\
#    "src/Dafny/Distributed/Protocol/Paxos/LiveRSL/LivenessProof/LivenessProof.i.dfy",\
#    "src/Dafny/Distributed/Impl/Paxos/LiveRSL/Main.i.dfy",\
#    ]

  files = None
  if args.cache is None or not os.path.exists(args.cache):
    # files = parse_nubuild(args.nubuild)
    files = [DafnyFile('/Users/franck/development/eth2.0-dafny/src/dafny/ssz/BitListSeDes.dfy', 0)]
    collect_line_counts(args.root, files)
    pickler = open(args.cache, "w")
    pickle.dump(files, pickler)
  else:
    pickler = open(args.cache, "r")
    files = pickle.load(pickler)
  pickler.close()
  cats = categorize_files(files)
  build_table(cats, args.latex)

if (__name__=="__main__"):
  #compute_sloc('', False, 'BitListSeDes.dfy', "tmp/")
  arr_txt = [DafnyFile(x,0) for x in os.listdir(".") if x.endswith(".dfy")]
  collect_line_counts("",arr_txt)