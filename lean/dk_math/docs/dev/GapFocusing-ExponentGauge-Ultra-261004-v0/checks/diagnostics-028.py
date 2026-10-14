"""Exact independent finite carry reconstruction; floats never enter Lean proofs."""
from pathlib import Path
from array import array
from collections import Counter
import argparse,json,math,time,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=5000);args=ap.parse_args()
base=Path(__file__).resolve().parent.parent
limit=args.limit;topmax=limit*limit+2*limit;start=time.monotonic()
spf=array('I',[0])*(topmax+1)
for p in range(2,math.isqrt(topmax)+1):
    if not spf[p]:
        for m in range(p*p,topmax+1,p):
            if not spf[m]:spf[m]=p
print('sieve ready',round(time.monotonic()-start,2),flush=True)
def factors(m):
    out=[]
    while m>1:
        p=spf[m] or m;a=0
        while m%p==0:m//=p;a+=1
        out.append((p,a))
    return out
def prime_deltas(labels):
    # Lossless prefix-sum encoding. Each decoded label is also its base, depth 1.
    prev=0;out=[]
    for q in labels:out.append(q-prev);prev=q
    return out
anchors={3,5,11,19,29,297,1031};anchorrows=[];firstcollision=None
fact=Counter();maxfiber=0;maxfiberrow=None;ratios=[];failed=[]
path=base/'logs/diagnostics-028.jsonl'
with path.open('w') as out:
    for n in range(1,limit+1):
        b=n*n;w=2*n;t=b+w
        for m in (w-1,w):
            for p,a in factors(m):fact[p]+=a
        shell=Counter();events={};higher=[];vm=[];images={};shelllog=[]
        # Route A: factor every positive shell integer, enumerate its power divisors.
        for m in range(b+1,t+1):
            fac=factors(m);shelllog.append(math.log(m))
            if len(fac)==1:
                p,a=fac[0];vm.append(math.log(p))
                if a>1:higher.append([m,p,a])
            for p,a in fac:
                shell[p]+=a;q=1
                for depth in range(1,a+1):
                    q*=p
                    if q<=b and q<=b%q+w%q:
                        events[q]=(p,depth)
        # Route B: floor carries on prime powers, without using event memberships.
        independent={};highfloor=Counter()
        for p in shell:
            q=p;a=1
            while q<=t:
                floor=t//q-b//q-w//q
                phase=int(q<=b%q+w%q)
                assert floor==phase and phase in (0,1),(n,q)
                if q<=b and floor:independent[q]=(p,a)
                if b<q and floor and a>1:highfloor[p]+=1
                q*=p;a+=1
        assert events==independent,(n,'carrier reconstruction')
        old=Counter({p:a-fact[p] for p,a in shell.items() if p<=b and a>fact[p]})
        # Direct factorial valuations of choose, independently of shell valuations.
        choose=Counter()
        for p in shell:
            q=p;v=0
            while q<=t:v+=t//q-b//q-w//q;q*=p
            assert v==shell[p]-fact[p],(n,p,'choose height')
            if v:choose[p]=v
        low=Counter(p for p,a in events.values());hi=Counter(p for q,p,a in higher)
        assert hi==highfloor
        # Central and old identities require n>=3; n=1,2 are recorded separately.
        oldok=(old==low+hi)
        vmheight=Counter(p for p in shell if spf[p]==0 and b<p<=t)
        vmheight+=hi
        centralok=(choose==low+vmheight)
        if n>=3:assert oldok and centralok,(n,'ledger identity')
        small=sorted(q for q in events if q<=w);large=sorted(q for q in events if w<q)
        fibers={}
        for q in large:
            m=q*(b//q+1);p,a=events[q]
            assert b<m<=t and m%q==0 and m+q>t and m-q<=b
            assert b//q+1<n if n>=3 else True
            fibers.setdefault(m,[]).append([q,p,a])
            # All same-image large labels share a prime base (diagnostic, not premise).
        assert all(len({p for q,p,a in f})==1 for f in fibers.values())
        hist=Counter(len(f) for f in fibers.values());mf=max(hist,default=0)
        if mf>maxfiber:maxfiber=mf;maxfiberrow=n
        if firstcollision is None and mf>1:
            m=min(m for m,f in fibers.items() if len(f)>1)
            firstcollision=dict(n=n,multiple=m,labels=fibers[m])
        k=math.fsum(math.log(p) for p,a in events.values())
        sm=math.fsum(math.log(events[q][0]) for q in small)
        lm=math.fsum(math.log(events[q][0]) for q in large)
        oldmass=math.fsum(a*math.log(p) for p,a in old.items())
        highermass=math.fsum(math.log(p) for q,p,a in higher)
        vmmass=math.fsum(vm)
        logcell=math.fsum(a*math.log(p) for p,a in choose.items())
        productlog=math.fsum(shelllog)
        assert abs(logcell+math.lgamma(w+1)-productlog)<1e-7
        if n>=3:
            assert abs(oldmass-highermass-k)<1e-8
            assert abs(logcell-vmmass-k)<1e-8
        L=t.bit_length() # actual cutoff below uses next square
        L=((n+1)**2).bit_length()-1
        budget=math.log(t)*math.log(L) if L else 0.
        if n>=3 and not k+budget<logcell:failed.append(n)
        row=dict(n=n,base=b,width=w,top=t,low_event_count=len(events),
            prime_label_deltas=prime_deltas(sorted(q for q,(p,a) in events.items() if a==1)),
            higher_labels=[[q,*events[q]] for q in sorted(events) if events[q][1]>1],
            small_count=len(small),large_count=len(large),low_mass_approx=k,
            small_mass_approx=sm,large_mass_approx=lm,old_Pascal_budget_approx=oldmass,
            higher_correction_approx=highermass,shell_VM_approx=vmmass,log_cell_approx=logcell,
            log_log_budget_approx=budget,old_integer_ledger_equal=oldok,
            central_integer_ledger_equal=centralok,independent_carrier_equal=True,
            max_large_fiber=mf,large_image_count=len(fibers),
            large_fiber_histogram=sorted(hist.items()),
            unique_multiple_rule='d*(base//d+1)',
            old_log_residual_approx=oldmass-highermass-k,
            central_log_residual_approx=logcell-vmmass-k)
        out.write(json.dumps(row,separators=(',',':'))+'\n')
        if n in anchors:
            anchorrows.append(dict(row,events=[[q,*events[q]] for q in sorted(events)],
                small_labels=small,large_labels=large,
                large_multiple_distribution=[[m,f] for m,f in sorted(fibers.items())]))
        if n>=3 and k:ratios.append((sm/k,n))
        if n%250==0:print('n',n,'seconds',round(time.monotonic()-start,1),flush=True)
summary=dict(limit=limit,format='One ASCII JSON object per n; prefix sums of prime_label_deltas decode prime labels, base=label and depth=1. higher_labels explicitly store label, base and depth. Unique images are exactly reconstructible from the rule; the histogram records their full multiplicity distribution.',
    exact_scope='All n independently reconstructed by shell divisor enumeration and prime-power floor carries. Choose heights independently checked by factorial floor valuations. Required ledgers checked for n>=3.',
    floating_scope='All logarithms and strict comparisons are diagnostics only.',
    data_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),first_collision=firstcollision,
    maximum_fiber=dict(count=maxfiber,n=maxfiberrow),failed_log_log_provider_approx=failed,
    max_small_mass_fraction=dict(zip(('fraction','n'),max(ratios))),
    min_small_mass_fraction=dict(zip(('fraction','n'),min(ratios))),
    elapsed_seconds=round(time.monotonic()-start,3),anchors=anchorrows)
(base/'logs/diagnostics-summary-028.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='anchors'}),flush=True)
