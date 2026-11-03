#!/usr/bin/env python3
"""From smbrta.json to checked theorems, in one run.

  1. prepare the files outside the repository (tools/setup.py)
  2. build this repository
  3. check the emulator against the nestest log
  4. generate the private proof files (they embed the ROM)
  5. build the private project: this is where Lean checks the theorems
  6. list the theorems

usage: python3 prove.py [--config smbrta.json]
The build command is `lake build`; set SMBRTA_BUILD to use another one.
Step 5 takes about 20 minutes.
"""
import os, re, shlex, subprocess, sys, time
repo = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(repo, 'tools'))
import smbrta_config

def run(title, cmd, cwd=repo):
    print(f'\n== {title}\n$ {" ".join(cmd)}', flush=True)
    t = time.time()
    r = subprocess.run(cmd, cwd=cwd)
    if r.returncode != 0:
        sys.exit(f'FAILED: {title} (exit {r.returncode})')
    print(f'   ok ({time.time() - t:.0f} s)', flush=True)

def main():
    args = sys.argv[1:]
    cfgarg = args if args[:1] == ['--config'] and len(args) == 2 else []
    if cfgarg: os.environ['SMBRTA_CONFIG'] = os.path.abspath(cfgarg[1])
    path = smbrta_config.load(cfgarg[1] if cfgarg else None)
    build = shlex.split(os.environ.get('SMBRTA_BUILD', 'lake build'))
    exe = os.path.join(repo, '.lake', 'build', 'bin', 'smbrta')
    project = path('proofProject')

    run('1. prepare the files outside the repository', [sys.executable, os.path.join(repo, 'tools', 'setup.py')] + cfgarg)
    run('2. build this repository', build)
    run('3. check the emulator (nestest)', [exe, 'nestest'])
    run('4. generate the private proof files', [exe, 'gen-rom'])
    run('   ', [exe, 'gen-proofs'])
    run('5. build the private project (Lean checks the theorems; about 20 minutes)', build, cwd=project)

    print('\n== 6. theorems checked by Lean')
    pdir = os.path.join(project, 'Proof')
    for f in sorted(os.listdir(pdir)):
        if not f.endswith('.lean'): continue
        for name, stmt in re.findall(r'^theorem (\S+) : (.+?) :=', open(os.path.join(pdir, f)).read(), re.M):
            print(f'   {name} : {stmt}')
    print('\nall done')

main()
