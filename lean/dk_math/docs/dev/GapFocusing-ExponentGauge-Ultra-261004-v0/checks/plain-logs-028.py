"""Normalize completed compiler logs without altering axiom names or exit evidence."""
from pathlib import Path
base=Path(__file__).resolve().parent.parent
translation={0x2115:'Nat',0x2124:'Int',0x211d:'Real',0x2200:'forall ',0x2203:'exists ',0x2208:' in ',0x2209:' notin ',0x2264:' <= ',0x2265:' >= ',0x2192:' -> ',0x2194:' iff ',0x2227:' and ',0x2228:' or ',0x2205:'empty',0x00ac:'not ',0x2139:'INFO',0x2716:'FAIL',0x26a0:'WARNING'}
for p in (base/'logs').glob('*028*.txt'):
 s=p.read_text()
 s=''.join(translation.get(ord(c),c if ord(c)<128 else '[U+%04X]'%ord(c)) for c in s)
 s=s.replace(chr(92),' setminus ')
 p.write_text(s)
print('Completed checkpoint 028 text logs normalized to ASCII.')
