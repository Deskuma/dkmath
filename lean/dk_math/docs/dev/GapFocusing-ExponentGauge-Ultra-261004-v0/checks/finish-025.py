"""Finalize reports only after every build writer has completed successfully."""
from pathlib import Path
import subprocess,json,re,sys
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
records={label:json.loads((base/f'logs/performance-{label}-025.json').read_text()) for label in ['focused','facade','root','axiom-audit']}
assert all(r['exit_code']==0 for r in records.values())
subprocess.run([sys.executable,str(base/'checks/plain-logs-025.py')],cwd=root,check=True)
rootlog=(base/'logs/root-025.txt').read_text()
warnings=re.findall(r'^warning: (.+)$',rootlog,re.M)
s='''# Validation 025

All builds used LEAN_NUM_THREADS=2. The build runner retains the exact commands, exit status and elapsed time. Timings are individual local runs with dependency reuse, not performance comparisons.

| Check | Target scope | Exit | Elapsed seconds |
| --- | --- | --- | --- |
'''
scopes={'focused':'Five affected production source modules and two calibration modules','facade':'DkMath.NumberTheory.Legendre','root':'DkMath','axiom-audit':'DkMathTest.NumberTheory.PascalPrebirthAxiomAudit'}
for label,r in records.items():s+=f"| {label} | {scopes[label]} | {r['exit_code']} | {r['elapsed_seconds']} |\n"
s+='''
- [focused-025.txt](logs/focused-025.txt) records all five affected production module targets and both calibration targets.
- [facade-025.txt](logs/facade-025.txt) records the complete requested Legendre facade build.
- [root-025.txt](logs/root-025.txt) records the complete requested DkMath root build.
- [axiom-audit-025.txt](logs/axiom-audit-025.txt) contains installed API signature checks and print-axioms evidence for all named public declarations in the covered sources.

## Complete declaration coverage

Coverage includes 95 production declarations and 33 calibration declarations, 128 total. All 49 new production declarations and all 33 new calibration declarations are included. Existing named public declarations in changed production files are also included. The generated manifest is [declaration-coverage-025.json](logs/declaration-coverage-025.json).

Allowed axiom dependencies are only propext, Classical.choice and Quot.sound. Every covered declaration is checked against that set. No new sorryAx dependency is accepted. This audit is scoped to the enumerated declarations; it is not a claim that every historical root theorem is free of placeholders.

## Root warnings

The root build reports the existing warnings below. They are outside the newly added declarations.

'''
s+='\n'.join('- '+w for w in warnings)+'\n'
s+='''
## Additional checks

The forbidden-construct scan covers ten affected Lean files, including the two facades and the axiom probe. It rejects proof placeholders, custom axiom declarations and unchecked computation constructs. Standard headers and the traditional file-print markers are retained. Neutral Pascal modules do not depend on Legendre, Zsigmondy or exponent-period PowerGauge.

The tracked diff check and untracked Lean whitespace checks pass. The four new reports and all 025 text/JSON logs use ASCII without backslash notation. Compiler logs were normalized only after every build writer completed.

Required finite-row diagnostics and exact fractional counterexamples are retained in [pascal-diagnostics-025.json](logs/pascal-diagnostics-025.json). Six anchor factorization ledgers were computed by factorial valuations and their full prime-power products compared with exact binomial values. Log readouts remain approximate diagnostics; Lean proofs use exact identities and prime log positivity instead.

The report contains all sixteen required answers and exactly one final Outcome B judgment. Next implementation proposals are explicitly separated from proved results.

The reproducible artifact audit is checks/check-025.py; its final output is [checks-025.txt](logs/checks-025.txt).
'''
(base/'validation-025.md').write_text(s)
with (base/'logs/checks-025.txt').open('w') as out:
 p=subprocess.run([sys.executable,str(base/'checks/check-025.py')],cwd=root,stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/checks-025.txt').read_text())
sys.exit(p.returncode)
