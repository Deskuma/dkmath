"""Inventory the live sources introduced by the 016 through 024 implementation commits."""
from pathlib import Path
import subprocess,re
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
rows=[]
history=subprocess.check_output(['git','log','-45','--format=%H%x09%s'],cwd=root,text=True)
for line in history.splitlines():
 commit,subject=line.split('\t',1)
 m=re.match(r'impl: (0(?:1[6-9]|2[0-4]))\b',subject)
 if not m:continue
 paths=subprocess.check_output(['git','show','--format=','--name-only',commit],cwd=root,text=True).splitlines()
 for path in paths:
  if path.startswith('lean/dk_math/DkMath/NumberTheory/Legendre/') and path.endswith('.lean'):
   local=path.removeprefix('lean/dk_math/')
   if not (root/local).exists():continue
   text=(root/local).read_text()
   decls=re.findall(r'^(?:@\[[^\n]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_.]+)',text,re.M)
   imports=re.findall(r'^import (\S+)',text,re.M)
   rows.append((m.group(1),local,len(decls),imports))
rows.sort()
lines=['Live historical source inventory for checkpoints 016 through 024.','Headers, imports and named public declaration inventory; no extra existence provider inferred.','']
lines+=[' | '.join([i,path,str(count),','.join(imports)]) for i,path,count,imports in rows]
(base/'logs/prior-source-index-025.txt').write_text('\n'.join(lines)+'\n')
print('Source rows:',len(rows),'Unique files:',len({r[1] for r in rows}))
print('\n'.join(i+' '+path+' '+str(count) for i,path,count,_ in rows))
