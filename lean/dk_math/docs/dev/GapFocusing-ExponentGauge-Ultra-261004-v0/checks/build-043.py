"""Retain process telemetry for the final focused, facade, root and axiom builds."""
from pathlib import Path
import os,subprocess,sys,time,json,re,unicodedata
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
targets={
    'focused':['DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit','DkMathTest.FLT.Seven.DepthFourReconstructionCalibration'],
    'facade':['DkMath.FLT.Seven'],'root':['DkMath'],
    'axiom-audit':['DkMathTest.FLT.Seven.DepthFourReconstructionAxiomAudit']}
env=dict(os.environ)
env.pop('LEAN_NUM_THREADS',None)
keys={'maximum_resident_set_kbytes':'Maximum resident set size (kbytes)',
    'major_page_faults':'Major (requiring I/O) page faults',
    'minor_page_faults':'Minor (reclaiming a frame) page faults','swap_count':'Swaps'}
for label in sys.argv[1:]:
    cmd=['lake','build',*targets[label]]
    telemetry=base/f'logs/telemetry-{label}-043.txt'
    measured=['/usr/bin/time','-v','-o',str(telemetry),'--',*cmd]
    start=time.monotonic()
    with (base/f'logs/{label}-043.txt').open('w') as out:
        result=subprocess.run(measured,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
    raw=telemetry.read_text();stats={}
    for name,key in keys.items():
        match=re.search(re.escape(key)+r':\s*(\d+)',raw)
        assert match,(name,raw)
        stats[name]=int(match[1])
    record=dict(command=cmd,measurement_command=measured,LEAN_NUM_THREADS=None,LEAN_NUM_THREADS_in_environment=False,
        exit_code=result.returncode,elapsed_seconds=round(time.monotonic()-start,3),
        telemetry_scope='GNU time resource usage of Lake invocation including waited descendants',**stats,
        failure_classification='none' if result.returncode==0 else 'requires explicit investigation; not assumed OOM')
    (base/f'logs/performance-{label}-043.json').write_text(json.dumps(record,indent=2)+'\n')
    for artifact in [telemetry,base/f'logs/{label}-043.txt']:
        plain=unicodedata.normalize('NFKD',artifact.read_text()).encode('ascii','ignore').decode()
        artifact.write_text(plain.replace(chr(92),' slash '))
    print(label+' '+json.dumps(record),flush=True)
    if result.returncode:raise SystemExit(result.returncode)
