"""Focused, facade, root and axiom checks with retained exit and elapsed evidence."""
from pathlib import Path
import os, subprocess, sys, time, json
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
targets={
 'focused':['DkMath.NumberTheory.Legendre.SquareShellPrimePower','DkMath.NumberTheory.Legendre.SquareShellVonMangoldt','DkMath.NumberTheory.Legendre.SquareShellPrimePowerGauge','DkMathTest.NumberTheory.SquareShellPrimePowerCalibration'],
 'facade':['DkMath.NumberTheory.Legendre'],
 'root':['DkMath'],
 'axiom-audit':['DkMathTest.NumberTheory.SquareShellPrimePowerAxiomAudit']}
env=dict(os.environ,LEAN_NUM_THREADS='2')
for label in sys.argv[1:]:
 cmd=['lake','build',*targets[label]]
 start=time.monotonic()
 with (base/f'logs/{label}-026.txt').open('w') as out:
  p=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 record=dict(command=cmd,LEAN_NUM_THREADS=2,exit_code=p.returncode,elapsed_seconds=round(time.monotonic()-start,3))
 (base/f'logs/performance-{label}-026.json').write_text(json.dumps(record,indent=2)+'\n')
 print(label+' '+json.dumps(record),flush=True)
 if p.returncode:sys.exit(p.returncode)
