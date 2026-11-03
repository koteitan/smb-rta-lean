#!/usr/bin/env python3
"""Download the nestest CPU test (ROM + log) and build the homemade test cartridge.
Destinations: the `nestestRom`, `nestestLog` and `miniRom` entries of smbrta.json.
usage: fetch_testdata.py [--config smbrta.json]"""
import os, subprocess, sys, urllib.request
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, here)
import smbrta_config
args = sys.argv[1:]
path = smbrta_config.load(args[1] if args[:1] == ['--config'] and len(args) == 2 else None)
for key, url in [('nestestRom', 'https://www.qmtpro.com/~nes/misc/nestest.nes'),
                 ('nestestLog', 'https://www.qmtpro.com/~nes/misc/nestest.log')]:
    dst = path(key)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    urllib.request.urlretrieve(url, dst)
    print('wrote', dst)
dst = path('miniRom')
os.makedirs(os.path.dirname(dst), exist_ok=True)
subprocess.run([sys.executable, os.path.join(here, 'make_mini_rom.py'), dst], check=True)
print('wrote', dst)
