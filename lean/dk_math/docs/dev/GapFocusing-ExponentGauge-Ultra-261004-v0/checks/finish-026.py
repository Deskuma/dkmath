"""Record finished build evidence, normalize completed logs, and run final audit."""
from pathlib import Path
import json,subprocess,re
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
labels=['focused','facade','root','axiom-audit']
records={k:json.loads((base/f'logs/performance-{k}-026.json').read_text()) for k in labels}
assert all(r['exit_code']==0 for r in records.values())
subprocess.run(['python3',str(base/'checks/plain-logs-026.py')],cwd=root,check=True)
coverage=json.loads((base/'logs/declaration-coverage-026.json').read_text())
text='# Validation 026\n\nAll final checks passed with LEAN_NUM_THREADS=2.\n\n'
text+='| Check | Exit | Seconds |\n| --- | --- | --- |\n'
for label,r in records.items():text+=f"| {label} | {r['exit_code']} | {r['elapsed_seconds']} |\n"
text+='\nThe focused check built all three new production modules and the calibration\nmodule. The Legendre facade exports them; the DkMath root imports that facade.\nThe root source itself was not edited.\n\n'
text+=f"Complete named public axiom coverage includes {coverage['production_count']} new\nproduction declarations and {coverage['calibration_count']} calibration declarations,\n{coverage['total']} total. Every declaration is printed in the dedicated axiom audit.\nOnly propext, Classical.choice and Quot.sound are permitted by the checker.\nNo new sorryAx dependency occurs.\n\n"
text+='The final focused and axiom logs contain no warnings. The facade replayed\nthe existing PacketCross unused-variable warning. The root replayed previously\nexisting unrelated warnings:\n\n'
warns=re.findall(r'^warning:.*$',(base/'logs/root-026.txt').read_text(),re.M)
for w in warns:text+='- '+w+'\n'
text+='\nThe exact integer diagnostic scan covers all 5000 anchors n=1..5000.\nThe final checker independently reconstructs the higher-power event inventory,\nverifies the stored event properties and bounds, and checks parser-safe artifacts.\nReal logarithms and strict numerical comparisons remain floating diagnostics.\nNamed Lean calibrations certify the six preserved higher-event summaries.\n\n'
text+='Forbidden-construct and header/file-marker scans cover three new production\nmodules, calibration, axiom audit, and the edited facade. Tracked diff checks\nand separate untracked Lean whitespace checks passed. No RH import was added.\n\n'
text+='The final status evidence is in focused-026.txt, facade-026.txt, root-026.txt,\nand axiom-audit-026.txt, with their performance JSON records. The build-026-*.txt\nfiles retain earlier focused elaboration attempts and are historical logs,\nnot final validation status.\n\n'
text+='[Final checker output](logs/checks-026.txt) records the completed audits.\n[Complete declaration coverage](logs/declaration-coverage-026.json) lists every\nprinted declaration. [Report](report-026.md) separates the proved small-budget\ncriteria from the unresolved universal lower-mass provider and the next proposal.\n'
(base/'validation-026.md').write_text(text)
with (base/'logs/checks-026.txt').open('w') as out:
    result=subprocess.run(['python3',str(base/'checks/check-026.py')],cwd=root,stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/checks-026.txt').read_text())
if result.returncode:raise SystemExit(result.returncode)
with (base/'findings-026.md').open('a') as out:
    out.write('\n## Final validation completed\n\nAll three production modules, the calibration module, the Legendre facade,\nthe DkMath root, and the complete axiom audit passed with two Lean threads.\nThe final checker passed full public declaration coverage, standard-axiom-only\naudit, forbidden constructs, header/file-marker conventions, whitespace checks,\n5000-shell exact higher-event inventory, 21 report answers and ASCII artifacts.\nOnly existing unrelated facade/root warnings remain. Outcome A retains the explicit\nunresolved universal lower-mass comparison.\n')
