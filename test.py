import os
from subprocess import PIPE, run

in_dir = './instances/inputs/'
myouts_dir = './instances/myouts/'
outs_dir = './instances/outputs/'
in_ext = '.wps'
myout_ext = '.myout'
out_ext = '.out'
executable = './src/project.py'
checker = './wps-checker'


class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


for entry in os.scandir(in_dir):
    filename = os.path.splitext(entry.name)[0]
    print(filename, end=' ', flush=True)
    os.system('python3 ' + executable + ' < ' + in_dir + filename +
              in_ext + ' > ' + myouts_dir + filename + myout_ext)
    f1 = open(myouts_dir + filename + myout_ext)
    f2 = open(outs_dir + filename + out_ext)
    lines = f1.readlines()
    f2_lines = f2.readlines()
    if lines[0].strip() == 'UNSAT':
        if f2_lines[0].strip() == 'UNSAT':
            print('\tOK UNSAT')
        else:
            print('\tFAIL')
    else:
        output = run(checker + " " + in_dir+filename+in_ext + " " + myouts_dir+filename +
                     myout_ext, stdout=PIPE, stderr=PIPE, universal_newlines=True, shell=True)
        res = output.stdout.strip()
        if lines[0].strip() == f2_lines[0].strip():
            print("\t" + res + ' OPTIMAL')
        else:
            print("\t" + res + 'NON OPTIMAL')
    f2.close()
    f1.close()
