#!/usr/bin/env python3
"""A separate place to work in, so that several workers do not touch each other's files.

new NAME       make `worktrees/NAME` beside smbrta.json: this repository as it is now, with its
               uncommitted changes and its build files, and a copy of the private project
list           the places, and how many files each has changed
status NAME    the files changed in that place since `new`
diff NAME      those changes as a patch
apply NAME     apply them to this repository's files (`--check`: only try). Nothing is staged, and
               if one part does not apply, nothing changes
remove NAME    delete the place. It refuses while there are changes not applied (`--force`)

In the place, build and check as usual:  cd worktrees/NAME/git && leanman build
It makes no commit and no branch. Only the repository's changes come back: the private project
in the place is generated again by `gen-proofs`. Files of the ROM stay where they are: the place's
smbrta.json points to them.
usage: worktree.py [--config smbrta.json] COMMAND [NAME] [--check] [--force]
"""
import functools, json, os, re, shutil, subprocess, sys, tempfile
here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(here)
sys.path.insert(0, here)
import smbrta_config
print = functools.partial(print, flush=True)

def git(*args, cwd=repo, env=None, inp=None):
    r = subprocess.run(['git', *args], cwd=cwd, env=env, input=inp, capture_output=True)
    if r.returncode != 0:
        sys.exit(f'git {" ".join(args)}: {r.stderr.decode(errors="replace").strip()}')
    return r.stdout

def tree(w):
    """the tree of the files in `w` as they are, by a temporary index: no staging and no commit"""
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, GIT_INDEX_FILE=os.path.join(d, 'index'))
        git('read-tree', 'HEAD', cwd=w, env=env)
        git('add', '-A', cwd=w, env=env)
        return git('write-tree', cwd=w, env=env).decode().strip()

def inside(path, base, what):
    rel = os.path.relpath(path, base)
    if rel.startswith(os.pardir):
        sys.exit(f'{what} ({path}) is not under {base}: its relative path would not hold in a place')
    return rel

class Place:
    def __init__(self, base, name):
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name): sys.exit(f'bad name: {name}')
        self.name = name
        self.dir = os.path.join(base, 'worktrees', name)
        self.git = os.path.join(self.dir, inside(repo, base, 'the repository'))
    def need(self):
        if not os.path.isdir(self.dir): sys.exit(f'no place {self.name}')
        return self
    def read(self, f):
        p = os.path.join(self.dir, f)
        return open(p).read().strip() if os.path.exists(p) else None
    def write(self, f, s):
        open(os.path.join(self.dir, f), 'w').write(s + '\n')
    def base(self): return self.read('base-tree')
    def now(self): return tree(self.git)
    def patch(self): return git('diff', '--binary', self.base(), self.now(), cwd=self.git)
    def names(self):
        return [n for n in git('diff', '--name-only', '-z', self.base(), self.now(), cwd=self.git).decode().split('\0') if n]

def new(cfg, base, name):
    p = Place(base, name)
    if os.path.exists(p.dir): sys.exit(f'{p.dir} exists')
    proof = cfg('proofProject')
    relproof = inside(proof, base, 'proofProject')
    os.makedirs(p.dir)
    git('worktree', 'add', '--detach', p.git, 'HEAD')
    # the build files are of the files as they are now, so the uncommitted changes come too
    changed = git('diff', '--name-only', '-z', 'HEAD').decode().split('\0')
    changed += git('ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')
    n = 0
    for f in filter(None, changed):
        src, dst = os.path.join(repo, f), os.path.join(p.git, f)
        if os.path.exists(src):
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)
        elif os.path.exists(dst):
            os.remove(dst)
        n += 1
    lake = os.path.join(repo, '.lake')
    if os.path.isdir(lake): shutil.copytree(lake, os.path.join(p.git, '.lake'), symlinks=True)
    shutil.copytree(proof, os.path.join(p.dir, relproof), symlinks=True)
    # the place's config: what is copied stays relative, the rest points to where it is
    src = smbrta_config.find(CONFIG)
    data = json.load(open(src))
    out = {}
    for k, v in data.items():
        if k.startswith('_'): out[k] = v; continue
        abs_ = cfg(k)
        under = os.path.relpath(abs_, proof)
        out[k] = os.path.relpath(abs_, base) if not under.startswith(os.pardir) else abs_
    json.dump(out, open(os.path.join(p.dir, smbrta_config.NAME), 'w'), indent=2)
    p.write('base-tree', p.now())
    print(f'made {p.dir}: {n} uncommitted files came with it')
    print(f'  cd {p.git} && leanman build')

def listing(base):
    d = os.path.join(base, 'worktrees')
    for name in sorted(os.listdir(d)) if os.path.isdir(d) else []:
        p = Place(base, name)
        now = p.now()
        state = 'applied' if now == p.read('applied-tree') else f'{len(p.names())} files changed'
        print(f'{name}: {state}')

def status(p):
    sys.stdout.write(git('diff', '--stat', p.base(), p.now(), cwd=p.git).decode())

def apply_(p, check):
    patch, now = p.patch(), p.now()
    if not patch: print('no changes'); return
    r = subprocess.run(['git', 'apply', '--whitespace=nowarn'] + (['--check'] if check else []), cwd=repo, input=patch, capture_output=True)
    if r.returncode != 0:
        sys.exit('does not apply, nothing changed:\n' + r.stderr.decode(errors='replace').strip())
    if check: print(f'applies: {len(p.names())} files'); return
    p.write('applied-tree', now)
    print(f'applied {len(p.names())} files; nothing is staged')

def remove(p, force):
    now = p.now()
    if now not in (p.base(), p.read('applied-tree')) and not force:
        sys.exit(f'{p.name} has changes that are not applied (apply it, or --force):\n  ' + '\n  '.join(p.names()))
    git('worktree', 'remove', '--force', p.git)
    shutil.rmtree(p.dir)
    print(f'removed {p.dir}')

CONFIG = None

def main():
    global CONFIG
    args = sys.argv[1:]
    if args[:1] == ['--config']:
        if len(args) < 2: sys.exit(__doc__)
        CONFIG = args[1]; args = args[2:]
    flags = {a for a in args if a.startswith('--')}
    args = [a for a in args if not a.startswith('--')]
    if flags - {'--check', '--force'} or not args: sys.exit(__doc__)
    if os.path.isfile(os.path.join(repo, '.git')):
        sys.exit('this is a place: run the tool from the main repository')
    cfg = smbrta_config.load(CONFIG)
    base = os.path.dirname(smbrta_config.find(CONFIG))
    match args:
        case ['new', name]: new(cfg, base, name)
        case ['list']: listing(base)
        case ['status', name]: status(Place(base, name).need())
        case ['diff', name]: sys.stdout.buffer.write(Place(base, name).need().patch())
        case ['apply', name]: apply_(Place(base, name).need(), '--check' in flags)
        case ['remove', name]: remove(Place(base, name).need(), '--force' in flags)
        case _: sys.exit(__doc__)

main()
