#!/usr/bin/env python3
"""Extract symbol addresses for the Lean model from a ROM and a disassembly.

Both inputs stay outside the repository. The disassembly gives names: `Name = value`
lines (RAM variables, constants) and code labels. Code label addresses are found by
walking the disassembly from `.org` and adding the length of each instruction and data
directive; every instruction is checked against the ROM (its opcode byte must be the one
of the mnemonic and addressing mode at that address), so a wrong length is caught.

usage: extract_syms.py [--config smbrta.json]
       extract_syms.py ROM.nes DISASM.ASM SYMBOLS.txt OUT.syms
With no file arguments, the ROM, the disassembly and the output are the `rom`, `disasm` and
`syms` entries of smbrta.json, and SYMBOLS.txt is `smb-symbols.txt` next to this script.

SYMBOLS.txt has one `key=spec` per line (`#` comments). A spec is
  Name                  the value of a name (RAM variable, constant, or code label)
  index:Table:Entry     position of Entry in the `.dw` list that follows label Table
  byte:Label+N          the ROM byte at the address of Label plus N
The output has one `key value` (decimal) per line. It contains values taken from the
ROM, so keep it out of any public repository.
"""
import os, re, sys

# the tested disassembly: gist 1wErt3r/4048722, SMBDIS.ASM, 751389 bytes
DISASM_SHA256 = 'e5c17c42783f430029ab90aa37c73d51c2c320898e533b3ff196dad38c50ae42'

OPS = {  # mnemonic -> {mode: opcode}
}
def op(m, **modes):
    OPS[m] = modes
op('adc', imm=0x69, zp=0x65, zpx=0x75, abs=0x6D, absx=0x7D, absy=0x79, indx=0x61, indy=0x71)
op('and', imm=0x29, zp=0x25, zpx=0x35, abs=0x2D, absx=0x3D, absy=0x39, indx=0x21, indy=0x31)
op('asl', acc=0x0A, zp=0x06, zpx=0x16, abs=0x0E, absx=0x1E)
op('bit', zp=0x24, abs=0x2C)
for m, o in [('bpl', 0x10), ('bmi', 0x30), ('bvc', 0x50), ('bvs', 0x70), ('bcc', 0x90),
             ('bcs', 0xB0), ('bne', 0xD0), ('beq', 0xF0)]:
    op(m, rel=o)
op('brk', imp=0x00)
op('cmp', imm=0xC9, zp=0xC5, zpx=0xD5, abs=0xCD, absx=0xDD, absy=0xD9, indx=0xC1, indy=0xD1)
op('cpx', imm=0xE0, zp=0xE4, abs=0xEC)
op('cpy', imm=0xC0, zp=0xC4, abs=0xCC)
op('dec', zp=0xC6, zpx=0xD6, abs=0xCE, absx=0xDE)
op('eor', imm=0x49, zp=0x45, zpx=0x55, abs=0x4D, absx=0x5D, absy=0x59, indx=0x41, indy=0x51)
for m, o in [('clc', 0x18), ('sec', 0x38), ('cli', 0x58), ('sei', 0x78), ('clv', 0xB8), ('cld', 0xD8),
             ('sed', 0xF8), ('dex', 0xCA), ('dey', 0x88), ('inx', 0xE8), ('iny', 0xC8), ('nop', 0xEA),
             ('pha', 0x48), ('php', 0x08), ('pla', 0x68), ('plp', 0x28), ('rti', 0x40), ('rts', 0x60),
             ('tax', 0xAA), ('tay', 0xA8), ('tsx', 0xBA), ('txa', 0x8A), ('txs', 0x9A), ('tya', 0x98)]:
    op(m, imp=o)
op('inc', zp=0xE6, zpx=0xF6, abs=0xEE, absx=0xFE)
op('jmp', abs=0x4C, ind=0x6C)
op('jsr', abs=0x20)
op('lda', imm=0xA9, zp=0xA5, zpx=0xB5, abs=0xAD, absx=0xBD, absy=0xB9, indx=0xA1, indy=0xB1)
op('ldx', imm=0xA2, zp=0xA6, zpy=0xB6, abs=0xAE, absy=0xBE)
op('ldy', imm=0xA0, zp=0xA4, zpx=0xB4, abs=0xAC, absx=0xBC)
op('lsr', acc=0x4A, zp=0x46, zpx=0x56, abs=0x4E, absx=0x5E)
op('ora', imm=0x09, zp=0x05, zpx=0x15, abs=0x0D, absx=0x1D, absy=0x19, indx=0x01, indy=0x11)
op('rol', acc=0x2A, zp=0x26, zpx=0x36, abs=0x2E, absx=0x3E)
op('ror', acc=0x6A, zp=0x66, zpx=0x76, abs=0x6E, absx=0x7E)
op('sbc', imm=0xE9, zp=0xE5, zpx=0xF5, abs=0xED, absx=0xFD, absy=0xF9, indx=0xE1, indy=0xF1)
op('sta', zp=0x85, zpx=0x95, abs=0x8D, absx=0x9D, absy=0x99, indx=0x81, indy=0x91)
op('stx', zp=0x86, zpy=0x96, abs=0x8E)
op('sty', zp=0x84, zpx=0x94, abs=0x8C)
LEN = {'imp': 1, 'acc': 1, 'imm': 2, 'zp': 2, 'zpx': 2, 'zpy': 2, 'rel': 2, 'indx': 2, 'indy': 2,
       'abs': 3, 'absx': 3, 'absy': 3, 'ind': 3}

def strip(line):
    # remove a comment, but not a ';' inside a string
    out, q = '', False
    for ch in line:
        if ch == '"': q = not q
        if ch == ';' and not q: break
        out += ch
    return out.rstrip()

def number(tok):
    if tok.startswith('$'): return int(tok[1:], 16)
    if tok.startswith('%'): return int(tok[1:], 2)
    return int(tok)

def evaluate(expr, syms, labels_unknown_big=True):
    """Evaluate an operand expression. Unknown names (forward labels) give None."""
    expr = expr.strip()
    lo = hi = False
    if expr.startswith('<'): lo, expr = True, expr[1:]
    elif expr.startswith('>'): hi, expr = True, expr[1:]
    toks = re.findall(r'\$[0-9A-Fa-f]+|%[01]+|\d+|[A-Za-z_][A-Za-z0-9_]*|[-+*/()]', expr)
    py = ''
    for t in toks:
        if re.match(r'[A-Za-z_]', t):
            if t not in syms: return None
            py += str(syms[t])
        elif t[0] in '$%' or t[0].isdigit():
            py += str(number(t))
        else:
            py += t if t != '/' else '//'
    v = eval(py)
    if lo: v &= 0xFF
    if hi: v = (v >> 8) & 0xFF
    return v

def parse(asm_lines):
    """yield (lineno, label or None, mnemonic/directive or None, operand)"""
    for n, raw in enumerate(asm_lines, 1):
        line = strip(raw)
        if not line.strip(): continue
        m = re.match(r'^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)$', line.strip())
        if m:
            yield n, None, '=', (m.group(1), m.group(2)); continue
        label = None
        m = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_]*):(.*)$', line)
        if m:
            label, line = m.group(1), m.group(2)
        line = line.strip()
        if not line:
            yield n, label, None, None; continue
        parts = line.split(None, 1)
        yield n, label, parts[0].lower(), (parts[1].strip() if len(parts) > 1 else '')

def mode_of(mn, operand, syms):
    o = operand.replace(' ', '')
    modes = OPS[mn]
    if o == '' or o.lower() == 'a':
        return ('acc' if 'acc' in modes else 'imp'), None
    if o.startswith('#'): return 'imm', o[1:]
    if 'rel' in modes: return 'rel', o
    m = re.match(r'^\((.+)\),y$', o, re.I)
    if m: return 'indy', m.group(1)
    m = re.match(r'^\((.+),x\)$', o, re.I)
    if m: return 'indx', m.group(1)
    m = re.match(r'^\((.+)\)$', o)
    if m: return 'ind', m.group(1)
    idx = None
    m = re.match(r'^(.+),([xy])$', o, re.I)
    if m: o, idx = m.group(1), m.group(2).lower()
    v = evaluate(o, syms)
    small = v is not None and v < 0x100
    if idx is None:
        return ('zp' if small and 'zp' in modes else 'abs'), o
    zpm, absm = ('zpx', 'absx') if idx == 'x' else ('zpy', 'absy')
    return (zpm if small and zpm in modes else absm), o

def data_len(directive, operand):
    items = []
    cur, q = '', False
    for ch in operand:
        if ch == '"': q = not q
        if ch == ',' and not q:
            items.append(cur); cur = ''
        else: cur += ch
    items.append(cur)
    n = 0
    for it in items:
        it = it.strip()
        if not it: continue
        if it.startswith('"'): n += len(it.strip('"'))
        else: n += 1 if directive == '.db' else 2
    return n

def main():
    args = sys.argv[1:]
    if len(args) == 4:
        rom_path, asm_path, sym_path, out_syms = args
    else:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import smbrta_config
        path = smbrta_config.load(args[1] if args[:1] == ['--config'] and len(args) == 2 else None)
        rom_path, asm_path, out_syms = path('rom'), path('disasm'), path('syms')
        sym_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'smb-symbols.txt')
    import hashlib
    h = hashlib.sha256(open(asm_path, 'rb').read()).hexdigest()
    if h != DISASM_SHA256:
        print(f'warning: {asm_path} is not the tested SMBDIS.ASM (sha256 {h}); continuing, the ROM check below still applies')
    rom = open(rom_path, 'rb').read()
    prg = rom[16:16 + rom[4] * 16384]
    lines = open(asm_path, encoding='latin1').read().splitlines()
    syms = {}
    for _, _, d, opnd in parse(lines):
        if d == '=':
            v = evaluate(opnd[1], syms)
            if v is not None: syms[opnd[0]] = v
    # pass: walk addresses
    pc = None
    labels = {}
    tables = {}          # label -> list of .dw entries that follow it
    last_label = None
    checked = bad = 0
    for n, label, d, opnd in parse(lines):
        if d == '=': continue
        if label is not None and pc is not None:
            labels[label] = pc
            last_label = label
        if d is None: continue
        if d == '.org': pc = number(opnd.strip()); continue
        if d in ('.index', '.mem'): continue
        if d == '.dw' and last_label is not None:
            tables.setdefault(last_label, []).extend(x.strip() for x in opnd.split(',') if x.strip())
        if d in ('.db', '.dw'): pc += data_len(d, opnd); continue
        if d not in OPS: sys.exit(f'line {n}: unknown {d}')
        mode, _ = mode_of(d, opnd, {**syms, **labels})
        code = OPS[d][mode]
        off = pc - 0x8000
        if 0 <= off < len(prg):
            checked += 1
            if prg[off] != code:
                bad += 1
                if bad <= 5: print(f'line {n}: ${pc:04X} {d} {opnd}: ROM has {prg[off]:02X}, expected {code:02X}')
        pc += LEN[mode]
    print(f'instructions checked against the ROM: {checked}, mismatches: {bad}')
    if bad: sys.exit(1)
    print(f'end address ${pc:04X} (expected $10000)')
    if pc != 0x10000: sys.exit(1)
    allsyms = {**syms, **labels}
    out = []
    for raw in open(sym_path):
        line = raw.split('#')[0].strip()
        if not line: continue
        key, spec = (x.strip() for x in line.split('=', 1)) if '=' in line else (line, line)
        if spec.startswith('index:'):
            _, table, entry = spec.split(':')
            entries = tables.get(table)
            if not entries or entry not in entries: sys.exit(f'{key}: {entry} not in table {table}')
            v = entries.index(entry)
        elif spec.startswith('byte:'):
            name, _, k = spec[5:].partition('+')
            if name not in labels: sys.exit(f'{key}: unknown label {name}')
            v = prg[labels[name] + int(k or 0) - 0x8000]
        else:
            if spec not in allsyms: sys.exit(f'{key}: unknown name {spec}')
            v = allsyms[spec]
        out.append((key, v))
    with open(out_syms, 'w') as f:
        for key, v in out: f.write(f'{key} {v}\n')
    print(f'wrote {len(out)} symbols to {out_syms}')

main()
