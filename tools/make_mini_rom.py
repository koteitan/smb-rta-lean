#!/usr/bin/env python3
"""Build a tiny NROM test cartridge (our own code, no Nintendo data).

reset: wait 2 vblanks, clear $00-$03, enable NMI, then `JMP *`.
nmi:   inc $00 (frame counter); read controller 1 into $01 (bit-reversed);
       add $01 to the 16-bit sum $02/$03; burn ~5000 cycles; rti.
"""
import sys

code = bytes.fromhex(
    "78 D8 A2FF 9A"            # C000 sei cld ldx #$FF txs
    "2C0220 10FB"              # C005 bit $2002 / bpl C005
    "2C0220 10FB"              # C00A bit $2002 / bpl C00A
    "A900 8500 8501 8502 8503" # C00F lda #0, sta $00..$03
    "A980 8D0020"              # C019 lda #$80, sta $2000
    "4C1EC0"                   # C01E jmp C01E
    # nmi C021
    "E600"                     # inc $00
    "A901 8D1640 A900 8D1640"  # strobe controller
    "A208"                     # ldx #8
    "AD1640 4A 2601 CA D0F7"   # C02F lda $4016 / lsr / rol $01 / dex / bne C02F
    "A501 18 6502 8502 9002 E603"  # sum += $01
    "A204 A000 88 D0FD CA D0F8"    # busy loop
    "40"                       # C04D rti
)
prg = bytearray(16384)
prg[0:len(code)] = code
prg[0x3FFA:0x4000] = bytes([0x21, 0xC0, 0x00, 0xC0, 0x4D, 0xC0])
header = b"NES\x1a" + bytes([1, 0, 0, 0]) + bytes(8)
open(sys.argv[1], "wb").write(header + prg)
