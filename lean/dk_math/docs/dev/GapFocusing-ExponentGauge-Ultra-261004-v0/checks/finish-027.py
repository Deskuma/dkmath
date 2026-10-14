"""Finalize reports from actual process telemetry and run the checkpoint audit."""
from pathlib import Path
import json,subprocess,re
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
labels=['focused','facade','root','axiom-audit']
records={k:json.loads((base/f'logs/performance-{k}-027.json').read_text()) for k in labels}
assert all(r['exit_code']==0 for r in records.values())
subprocess.run(['python3',str(base/'checks/plain-logs-027.py')],cwd=root,check=True)
coverage=json.loads((base/'logs/declaration-coverage-027.json').read_text())
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n'
table+='| --- | --- | --- | --- | --- | --- | --- |\n'
for k,r in records.items():
    table+=f"| {k} | {r['exit_code']} | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
peak=max(r['maximum_resident_set_kbytes'] for r in records.values())
telemetry='All four final builds were measured with /usr/bin/time -v and\nLEAN_NUM_THREADS=2. The requested process metrics are:\n\n'+table
telemetry+=f"\nThe largest reported peak RSS was {peak} kbytes, about {peak/1048576:.3f} GiB.\n"
telemetry+='Major page faults and reported swap counts were zero in all four measurements.\nMinor faults are reported separately in the table. GNU time measures the Lake\ninvocation and waited descendants; these are process measurements, not total\nconcurrent host memory or a complete machine-wide swap monitor. Cache replay\nand actual compilation are both present. The final focused run rebuilt Gauge\nand both the inherited 026 and new 027 calibrations after the module doc edit.\n\n'
telemetry+='[Telemetry and validation](validation-027.md) retains the raw output and\nstructured records. The measurements do not give an upper bound for every\nfuture repository build.\n'
p=base/'report-027.md';s=p.read_text()
a=s.index('## 16. Build RSS and paging telemetry');b=s.index('## 17. Actual OOM evidence',a)
s=s[:a]+'## 16. Build RSS and paging telemetry\n\n'+telemetry+'\n'+s[b:]
s=s.replace('GnomonPascalCell.gnomonPascalCell_mul_factorial','Legendre.gnomonPascalCell_mul_factorial').replace('CentralBinomialWallisLowerR_le_choose','centralBinomialWallisLowerR_le_choose')
p.write_text(s)
validation='# Validation 027\n\nAll final measured builds passed with LEAN_NUM_THREADS=2.\n\n'+table+'\n'
validation+=f"Full named public axiom coverage includes {coverage['production_count']} production\ndeclarations ({coverage['new_production_count']} newly added) in both changed production\nmodules and {coverage['calibration_count']} new calibration declarations, {coverage['total']} total.\nOnly propext, Classical.choice and Quot.sound are permitted by the complete\nchecker; no new sorryAx dependencies occur.\n\n"
validation+='The focused target set is OddReciprocal, SquareShellPrimePowerGauge, and\nSquareShellReciprocalCalibration. The existing SquareShellPrimePowerCalibration\nwas rebuilt as a dependency and passed. The Legendre facade and DkMath root\nwere built in full. Their source files were not changed: the existing Gauge\nimport exports this extension and its neutral dependency.\n\n'
validation+='The final focused and axiom logs contain no warnings. The facade replayed\nthe existing PacketCross unused-variable warning. Existing unrelated root\nwarnings were replayed:\n\n'
for w in re.findall(r'^warning:.*$',(base/'logs/root-027.txt').read_text(),re.M):validation+='- '+w+'\n'
validation+='\n## Process telemetry\n\n'+telemetry+'\n'
for k in labels:validation+=f"- [{k} raw telemetry](logs/telemetry-{k}-027.txt), [structured record](logs/performance-{k}-027.json), [build log](logs/{k}-027.txt).\n"
validation+='\nAll process exits were zero; no killed process, timeout, manual termination,\nor actual OOM failure occurred. The two-thread choice follows the checkpoint\nsetup and is not an OOM diagnosis. Reported swap count zero is a GNU time\nfield, rather than a separate global swap-usage measurement.\n\n'
validation+='## Audits and artifacts\n\nThe final checker covers all named public declarations in both changed\nproduction sources and the new calibration, unified headers and immediate\nfile markers, forbidden constructs, dependency direction, tracked and untracked\nLean whitespace, the 5000-shell diagnostic extension, exact rational sums,\n20 report answers, the next-frontier proposal and parser-safe ASCII artifacts.\nThe neutral OddReciprocal module imports no Legendre, RH or L-series module.\nNo RH or L-series import was added to Gauge.\n\n'
validation+='All real logarithm diagnostics and strict numerical comparisons are explicitly\napproximate and were not used as theorem premises. Structural kernel examples\ncover the requested multiple and high-depth patterns and large preserved anchors.\nThe source inventory was written before production changes.\n\n'
validation+='[Final checker output](logs/checks-027.txt) records the completed audits.\n[Declaration coverage](logs/declaration-coverage-027.json) lists every printed\ndeclaration. The build-027-*.txt files retain exploratory focused elaborations;\nthe final four labeled logs and telemetry records carry current build status.\n'
(base/'validation-027.md').write_text(validation)
p=base/'findings-027.md';s=p.read_text();heading='\n## Final memory telemetry and validation\n'
s=s.split(heading)[0]+heading+'\n'
s+=f"All four final measured builds exited zero with two Lean threads. The peak\nreported RSS was {peak} kbytes ({peak/1048576:.3f} GiB); all major page faults and\nreported swap counts were zero. Minor faults and each build duration are retained\nin validation-027.md. No process was killed, timed out, manually terminated, or\nobserved to fail from OOM. The focused run rebuilt Gauge and both calibration\nmodules, so it includes actual proof compilation as well as cache replay.\n\n"
s+='The complete public axiom output and telemetry records are available. The\nfinal route judgment is Outcome A: reciprocal reindex and harmonic compression\nclose and materially sharpen the finite correction frontier, while the universal\nstrict lower-mass comparison remains unresolved. The proposed 028 divisor-shell\nidentity and any useful lower-divisor cancellation bound are not implemented.\n'
p.write_text(s)
with (base/'logs/checks-027.txt').open('w') as out:
    result=subprocess.run(['python3',str(base/'checks/check-027.py')],cwd=root,stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/checks-027.txt').read_text())
if result.returncode:raise SystemExit(result.returncode)
