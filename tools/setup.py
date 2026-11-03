#!/usr/bin/env python3
"""Prepare everything outside the repository from the paths in smbrta.json.

1. check the ROM (`rom`) by its MD5,
2. download the disassembly (`disasm`) if it is missing, and check its SHA-256,
3. make the private Lean project (`proofProject`): lakefile.toml, lean-toolchain, Proof/,
4. fetch the test data (`nestestRom`, `nestestLog`, `miniRom`),
5. make the symbol file (`syms`).
Every step is skipped when its result is already there and correct.
usage: setup.py [--config smbrta.json]
"""
import hashlib, os, shutil, subprocess, sys, urllib.request
here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(here)
sys.path.insert(0, here)
import smbrta_config
import functools
print = functools.partial(print, flush=True)

ROM_MD5 = '8e3630186e35d477231bf8fd50e54cdd'            # headerless PRG+CHR
DISASM_URL = ('https://gist.githubusercontent.com/1wErt3r/4048722/raw/'
              '7e8e9777a53a2f94fd968e79c891445a97a8ddde/SMBDIS.ASM')
DISASM_SHA256 = 'e5c17c42783f430029ab90aa37c73d51c2c320898e533b3ff196dad38c50ae42'

def lakefile(project):
    rel = os.path.relpath(repo, project)
    return f'''name = "proof"
defaultTargets = ["Proof"]

# the public Lean project (this file was written by tools/setup.py)
[[require]]
name = "smbrta"
path = "{rel}"

# generated proofs that embed the ROM: keep them private
[[lean_lib]]
name = "Proof"
globs = ["Proof.+"]
'''

def main():
    args = sys.argv[1:]
    cfg = args[1] if args[:1] == ['--config'] and len(args) == 2 else None
    print('config:', smbrta_config.find(cfg))
    path = smbrta_config.load(cfg)

    rom = path('rom')
    if not os.path.exists(rom): sys.exit(f'1. ROM: {rom} not found; put a Super Mario Bros. (JU) ROM there')
    got = hashlib.md5(open(rom, 'rb').read()[16:]).hexdigest()
    if got != ROM_MD5: sys.exit(f'1. ROM: {rom}: MD5 of PRG+CHR is {got}, expected {ROM_MD5}')
    print('1. ROM ok:', rom)

    asm = path('disasm')
    if not os.path.exists(asm):
        os.makedirs(os.path.dirname(asm), exist_ok=True)
        urllib.request.urlretrieve(DISASM_URL, asm)
        print('   downloaded', asm)
    h = hashlib.sha256(open(asm, 'rb').read()).hexdigest()
    print('2. disassembly', 'ok:' if h == DISASM_SHA256 else f'differs from the tested one (sha256 {h}):', asm)

    project = path('proofProject')
    os.makedirs(os.path.join(project, 'Proof'), exist_ok=True)
    lf = os.path.join(project, 'lakefile.toml')
    want = lakefile(project)
    if not os.path.exists(lf) or open(lf).read() != want:
        if os.path.exists(lf): shutil.copy(lf, lf + '.bak'); print('   old lakefile.toml saved as lakefile.toml.bak')
        open(lf, 'w').write(want)
    shutil.copy(os.path.join(repo, 'lean-toolchain'), os.path.join(project, 'lean-toolchain'))
    print('3. private Lean project ok:', project)

    if all(os.path.exists(path(k)) for k in ['nestestRom', 'nestestLog', 'miniRom']):
        print('4. test data ok')
    else:
        subprocess.run([sys.executable, os.path.join(here, 'fetch_testdata.py')] + args, check=True)
        print('4. test data fetched')

    subprocess.run([sys.executable, os.path.join(here, 'extract_syms.py')] + args, check=True)
    print('5. symbol file ok:', path('syms'))

main()
