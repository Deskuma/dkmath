"""Print all public declarations in the changed production surface and new calibration."""
from pathlib import Path
import re,json,subprocess
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
prod=['DkMath/NumberTheory/Legendre/GnomonCofactorWindow.lean']
tests=['DkMathTest/NumberTheory/GnomonCofactorWindowCalibration.lean']
pattern=re.compile(r'^(?:@\[[^\n]+\]\s*)?(?:(?:noncomputable|protected)\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_.]+)',re.M)
rows=[]
for name in prod+tests:
    prefix='DkMath.NumberTheory.Legendre' if '/Legendre/' in name else 'DkMath.NumberTheory'
    if name in tests:prefix=name[:-5].replace('/','.')
    declarations=pattern.findall((root/name).read_text())
    old=subprocess.run(['git','show','HEAD:lean/dk_math/'+name],capture_output=True,text=True)
    oldnames=set(pattern.findall(old.stdout)) if old.returncode==0 else set()
    rows.append(dict(file=name,declarations=[prefix+'.'+d for d in declarations],
        new=[prefix+'.'+d for d in declarations if d not in oldnames]))
header=(root/prod[0]).read_text().split('import ')[0]
s=header+'import DkMathTest.NumberTheory.GnomonCofactorWindowCalibration\n\n#print "file: DkMathTest.NumberTheory.GnomonCofactorWindowAxiomAudit"\n\n'
for row in rows:
    s+='-- Complete named public coverage of '+row['file']+'\n'
    s+='\n'.join('#print axioms '+d for d in row['declarations'])+'\n\n'
(root/'DkMathTest/NumberTheory/GnomonCofactorWindowAxiomAudit.lean').write_text(s.rstrip()+'\n')
data=dict(scope='All named public declarations in the new production module and the new calibration module',
    production_count=sum(len(r['declarations']) for r in rows[:1]),
    new_production_count=sum(len(r['new']) for r in rows[:1]),
    calibration_count=len(rows[1]['declarations']),total=sum(len(r['declarations']) for r in rows),modules=rows)
(base/'logs/declaration-coverage-030.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in data.items() if k!='modules'},indent=2))
