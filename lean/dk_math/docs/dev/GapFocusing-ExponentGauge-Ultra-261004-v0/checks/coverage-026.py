"""Generate complete named public coverage for all three new production modules."""
from pathlib import Path
import re,json
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
prod=['DkMath/NumberTheory/Legendre/'+n+'.lean' for n in ['SquareShellPrimePower','SquareShellVonMangoldt','SquareShellPrimePowerGauge']]
tests=['DkMathTest/NumberTheory/SquareShellPrimePowerCalibration.lean']
pattern=re.compile(r'^(?:@\[[^\n]+\]\s*)?(?:(?:noncomputable|protected)\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_.]+)',re.M)
rows=[]
for name in prod+tests:
    prefix='DkMath.NumberTheory.Legendre' if name in prod else name[:-5].replace('/','.')
    declarations=pattern.findall((root/name).read_text())
    rows.append(dict(file=name,declarations=[prefix+'.'+d for d in declarations]))
header=(root/prod[0]).read_text().split('import ')[0]
s=header+'import DkMathTest.NumberTheory.SquareShellPrimePowerCalibration\n\n#print "file: DkMathTest.NumberTheory.SquareShellPrimePowerAxiomAudit"\n\n'
for row in rows:
    s+='-- Complete named public coverage of '+row['file']+'\n'
    s+='\n'.join('#print axioms '+d for d in row['declarations'])+'\n\n'
(root/'DkMathTest/NumberTheory/SquareShellPrimePowerAxiomAudit.lean').write_text(s.rstrip()+'\n')
data=dict(scope='All named public declarations in three new production modules and one calibration module',
    production_count=sum(len(r['declarations']) for r in rows[:3]),
    calibration_count=len(rows[3]['declarations']),total=sum(len(r['declarations']) for r in rows),modules=rows)
(base/'logs/declaration-coverage-026.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in data.items() if k!='modules'},indent=2))
