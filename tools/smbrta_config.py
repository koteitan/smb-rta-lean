"""Find and read smbrta.json (the same rules as Config.lean).

Order: the given path, else $SMBRTA_CONFIG, else the first smbrta.json in the current
directory or one of its parents. Relative paths are relative to the config file's directory.
"""
import json, os, sys

NAME = 'smbrta.json'

def find(explicit=None):
    if explicit: return os.path.abspath(explicit)
    if os.environ.get('SMBRTA_CONFIG'): return os.path.abspath(os.environ['SMBRTA_CONFIG'])
    d = os.getcwd()
    while True:
        f = os.path.join(d, NAME)
        if os.path.exists(f): return f
        p = os.path.dirname(d)
        if p == d: sys.exit(f'no {NAME} found (copy smbrta-tmpl.json to a parent directory)')
        d = p

def load(explicit=None):
    f = find(explicit)
    data = json.load(open(f))
    base = os.path.dirname(f)
    def path(key):
        if key not in data: sys.exit(f'{f}: key "{key}" missing')
        p = data[key]
        return p if os.path.isabs(p) else os.path.normpath(os.path.join(base, p))
    return path
