"""Render the checked 029 report without assuming a global budget gain."""
from pathlib import Path
import json,subprocess,sys
base=Path(__file__).resolve().parent.parent
coverage=json.loads((base/'logs/declaration-coverage-029.json').read_text())
data=json.loads((base/'logs/diagnostics-029.json').read_text())
metrics=[]
for label in ['focused','facade','root','axiom-audit']:
    r=json.loads((base/f'logs/performance-{label}-029.json').read_text());assert r['exit_code']==0
    metrics.append((label,r))
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n| --- | --- | --- | --- | --- | --- | --- |\n'
for label,r in metrics:
    table+=f"| {label} | {r['exit_code']} | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
anchors='| n | large labels | targets | exact large mass approx | cutoff cap approx | singleton prime share |\n| --- | --- | --- | --- | --- | --- |\n'
for r in data['anchors']:
    anchors+=f"| {r['n']} | {r['labels']} | {r['targets']} | {r['exact_weight_approx']:.6f} | {r['cutoff_budget_approx']:.6f} | {100*r['singleton_prime_fraction_approx']:.3f}% |\n"
names='\n'.join('- '+d.rsplit('.',1)[1] for d in coverage['modules'][0]['declarations'])
report='''# Report 029 - Exact same-base fibers and the remaining singleton frontier

Same-base large-carry fibers are proved to be consecutive exponent intervals.
Their cardinal and von Mangoldt weight have exact cutoff/valuation formulas.
The cutoff-only bound is consumed by the 028 ledger and a conditional prime
provider. It supplies no universal strict improvement to the old budget.
In fact its envelope is always at least the exact old budget.

## Production surface and exact declarations

Added [GnomonCarryFiber](../../../DkMath/NumberTheory/Legendre/GnomonCarryFiber.lean),
with 18 public declarations, three definitions and fifteen theorems.
The [Legendre facade](../../../DkMath/NumberTheory/Legendre.lean) imports it after
focused validation. The existing 025-028 production modules were reused without
source edits. The new module has one import, GnomonDivisorCarry; it imports no
facade or analytic prime-distribution receiver.

DECLARATIONS

[Source inventory](source-inventory-029.md) and [findings](findings-029.md) retain
the audit and the route decisions. [Kernel calibration](../../../DkMathTest/NumberTheory/GnomonCarryFiberCalibration.lean)
and [axiom audit](../../../DkMathTest/NumberTheory/GnomonCarryFiberAxiomAudit.lean)
cover the finite examples and all named new declarations.

## What the fiber actually is

Write base=n^2, width=2*n, top=base+width. For prime p, n>=3 and
SquareCell n y, the finite exponent fiber F(n,p,y) contains the a in
Icc(1,Nat.log p(base)) such that width<p^a and p^a divides y.
The route theorem proves this is exactly the set of exponents whose old large
carry label p^a has canonical next-shell-multiple y. It is not an independent
superset of allowed exponents or the set of higher powers lying in the shell.

Let L=Nat.log p(width), U=Nat.log p(base), and v=y.factorization p.
The strongest exact result is

 F(n,p,y) = Icc(L+1,min(U,v))
 card F = min(U,v)-L
 sum over a in F of Lambda(p^a) = (min(U,v)-L)*log(p).

Cardinal subtraction is natural subtraction, including empty fibers. Log(p)
here is the real natural logarithm; Nat.log p is the integer exponent cutoff.
The exact interval means every intermediate exponent occurs. There is no
parity restriction: the low labels at n=11 include depths 5 and 6, and n=5
has depth 4. Higher shell-power odd-depth results from 026 do not transfer to
old divisors of shell integers.

The cutoff-only finite upper bound is card F<=U-L, removing the width reserve
from the ordinary valuation range. The valuation-aware exact formula can be
strictly smaller. Reciprocal exponent mass is inappropriate for this ledger:
each label carries log(p) once, irrespective of depth.

## Collision classification and counterexamples

For two large prime-power labels in the same shell target, the prime bases
coincide under the explicit n>=3 hypotheses. The 028 distinct-base exclusion
is reused: coprime labels of size greater than width would have product greater
than top while dividing y. The new canonical pair carrier is the finite image
of d mapped to (d.minFac,nextShellMultiple(d)). Its target projection is
injective, so there is one common prime base per occupied target. Labels can
still have multiple consecutive depths.

The smallest large-label collision is the inherited n=11 target 128, labels
32=2^5 and 64=2^6. Its fiber is exactly {5,6}; one base log per target would
undercount it by log(2). This invalid weighted bound is kernel refuted.

The statement fails if both labels are not required to be large. The smallest
positive-anchor mixed-base example is n=7, target 51, labels 3 and 17.
Both are old binary carries, but label 3 is small. Their prime bases differ.
The example and absence of earlier mixed-base pairs at n=1..6 are kernel
certified. An initial exploratory guess n=8 with labels 5 and 13 at target 65
was a valid later example; the full diagnostic scan corrected its minimality
before the final certificates were written.

The first cutoff slack is n=6, p=2, target 48. Here L=3, U=5 and v=4;
the actual fiber is {4}, whereas the cutoff permits two exponents. Its exact
mass is log(2), strictly less than the cutoff 2*log(2), proved symbolically.
At n=2896, p=2 and target 8388608, the exact fiber is Icc(13,22), with ten
labels. A complete kernel certificate now fixes this maximum-range example.
No theorem of uniformly bounded length or unbounded length for all anchors
is inferred from this finite observation.

## Insertion into the 028 ledger and failure mode

Let C(n) be gnomonLargeCarryFiberBudget: sum over occupied canonical targets
of (U-L)*log(p). Exact regrouping gives

 K_large(n) = sum over occupied targets of (min(U,v)-L)*log(p)
 K_large(n) <= C(n)
 oldBudget(n) <= higher(n)+K_small(n)+C(n).

The envelope theorem and its exact excess prove

 higher+K_small+C = oldBudget+(C-K_large).

The excess is nonnegative. Thus valuation truncation sharpens the proposed
cutoff cap, sometimes strictly, but only recovers the actual large mass.
It does not make oldBudget smaller, remove a legitimate carry weight, or
supply an independent estimate of occupied-image prime weights.
A smaller number of occupied targets cannot by itself replace multiplicity:
the n=11 and ten-label examples forbid treating them as one weight each.

The new conditional provider accepts
 K_small+C+log-log higher budget<log(cell)
and feeds the proved band-wise 028 consumer. Because C>=K_large, this condition
is at least as strong as the 028 low-carry/log-log condition, and implies it.
No universal strict inequality is proved. The finite geometry uses no analytic
prime-distribution input, PNT, RH, or short-interval Chebyshev estimate.

## Diagnostics and kernel evidence

[Diagnostics](logs/diagnostics-029.json) reuse the exact 028 event inventory with
its SHA-256 digest. All 4998 anchors n=3..5000 are reconstructed by grouped
labels, the cutoff/valuation interval, and direct power-divisibility scans.
Every exponent set and integer cardinal agrees. Log weights, envelope ratios,
strict conditions and the displayed numbers are floating diagnostics only.
The range was retained rather than enlarged as a substitute for a theorem.

ANCHOR_TABLE

The worst cutoff/exact-large-mass ratio is approximately 1.079630 at n=12;
there are equalities already at n=3 and 5. The exact formula removes all
cutoff slack, but it equals the original mass. At 297 the cutoff excess is
approximately 18.224010; at 1031 it is approximately 43.044348. The inherited
higher correction is zero at both anchors, so their old budgets still equal
the total low carry mass, not the proposed cutoff envelope.

The newly proved large-base subset theorem states that p>width forces F to
be a subset of {1}, for every target. Such occupied fibers are singletons;
the cutoff is already exactly one, so exponent compression has no effect.
These singleton prime labels account for approximately 99.334 percent of large
mass at 297, 99.457 percent at 1031 and 99.892 percent at 5000. Over the finite
range their share is at least approximately 68.580 percent, with minimum n=4.
The remaining repeated-power labels are a small part of the mass at the larger
anchors. This is diagnostic evidence of the obstruction, not a universal
percentage theorem.

The cutoff provider comparison passed numerically at all retained anchors.
It remains an explicit hypothesis in Lean. Kernel checks include exact fibers
at 5,6,11,297,1031,2896, their symbolic weights, an empty fiber, the mixed-base
counterexample and the invalid one-log-per-target bound. No large real-log
inequality was evaluated by a computation oracle.

## Validation and axioms

All 18 new production and 14 calibration declarations, total 32, are covered
by print axioms. Only propext, Classical.choice and Quot.sound occur.
No new sorryAx dependency, sorry, admit, axiom, native_decide, unsafe or
implemented_by appears. Headers and immediate file print markers follow the
project convention. Tracked and untracked Lean whitespace and parser-safe
ASCII report/log artifacts pass the checker.

TELEMETRY_TABLE

Final builds use LEAN_NUM_THREADS=2 and /usr/bin/time -v. The final focused invocation rebuilt the new production and calibration
after a comment-only cleanup; imported dependencies were replayed.
These are Lake and waited-descendant process metrics, not total host usage.
No OOM, process kill, timeout or manual termination was observed. Reported major
faults and swaps are zero. The facade retains the existing PacketCross warning;
the root also replays five existing unrelated sorry warnings. New declarations
have no dependency on those sorry axioms.
[Validation details](validation-029.md) and [check output](logs/check-029.txt)
retain commands, metrics and audit scope.

## Next natural frontier and implementation proposal

The result identifies a concrete obstruction: occupied singleton prime fibers
with p>2*n dominate, and they have no exponent multiplicity to compress.
The next research inequality should bound their weighted occupied-image mass
independently of the carry inventory. Do not iterate a tighter same-base
cardinality bound on this singleton sector.

A precise receiver for a future investigation is the finite cofactor-window
prime weight

 Q(n) = sum over k in Icc(2,n-1) of
   sum over prime p with p>width and base/k<p<=top/k of log(p).

For a large old prime label, y=p*k has 2<=k<n by oldness and the proved small
cofactor theorem. Conversely, each indicated prime p and cofactor k produces
an old large prime target; uniqueness of its shell multiple prevents repeated
counting. Thus Q is the relevant weighted occupancy quantity, not a new source
of lower-shell mass by itself.

The single next theorem to seek is a useful bound Q(n)<=U(n) with U independent
of carry events and occupied targets. Implement it only after a candidate U
survives exact diagnostics; its required acceptance comparison is
 K_small+K_repeated_power+U+log-log budget<log(cell).
A quotient-window identity alone would be another coordinate change and is
insufficient. No useful such U was proved or selected here, and no long
instruction-030 architecture is predesigned. The narrow implementation proposal
is to audit existing finite quotient-window bounds against this singleton
weight, then add one upper-bound theorem and its 028 consumer if justified.

Outcome B - EXACT SAME-BASE FIBERS WITHOUT A UNIVERSAL STRICT BUDGET GAIN
'''
(base/'report-029.md').write_text(report.replace('DECLARATIONS',names).replace('ANCHOR_TABLE',anchors.rstrip()).replace('TELEMETRY_TABLE',table.rstrip()))
validation='''# Validation 029

All final measured commands used LEAN_NUM_THREADS=2 and exited successfully.

- focused: lake build DkMath.NumberTheory.Legendre.GnomonCarryFiber DkMathTest.NumberTheory.GnomonCarryFiberCalibration
- facade: lake build DkMath.NumberTheory.Legendre
- root: lake build DkMath
- axiom: lake build DkMathTest.NumberTheory.GnomonCarryFiberAxiomAudit

'''+table+'''
The final focused run rebuilt the new production and calibration after a
comment-only cleanup and replayed imported dependencies. GNU time metrics cover Lake and
waited descendants, not total host memory. Raw text and structured telemetry
remain in logs with suffix 029. No observed OOM, kill or timeout occurred.

Complete coverage is 18 production and 14 calibration declarations, total 32.
The dynamic producer checks the entire new module and calibration. The audit
accepts only standard logical axioms and no sorryAx dependencies. No forbidden
proof construct or reversed facade dependency was introduced. All three new
Lean files and the changed facade have the standard header and file marker.
Both tracked and untracked Lean whitespace are checked.

Exact bounded diagnostics reuse the hashed 028 inventory, n=3..5000. Every
same-base exponent fiber is compared with an independently computed cutoff
and valuation interval and direct power divisibility. Singleton prime weights
are reconstructed from the original prime-label delta stream. Logs and strict
provider tests are floating diagnostics, not proof premises. Mandatory earlier
anchor data, ten-exponent collision, first cutoff slack and the smallest mixed
base counterexample remain represented.

Kernel calibration fixes finite exponent carriers, exact symbolic weights,
strict slack at the first example, the mixed-base counterexample and the failure
of one log per target. No large transcendental computation is kernel evaluated.
The existing PacketCross facade warning and five unrelated root sorry warnings
remain. Neither contributes a sorry axiom to the new declaration audit.

Reproduction scripts: coverage-029.py, build-029.py, diagnostics-029.py,
plain-logs-029.py, finish-029.py and check-029.py under checks. The final checker
prints its scope and results in logs/check-029.txt.
'''
(base/'validation-029.md').write_text(validation)
p=base/'findings-029.md';s=p.read_text().split('## Final diagnostics')[0]
s+='''## Final diagnostics and route judgment

All same-base exponent fibers through n=5000 match both direct divisibility
and the exact cutoff/valuation interval. The first cutoff slack is n=6,
p=2 and target 48. The first large collision is n=11; the largest recorded
fiber has ten labels at n=2896 and is now kernel certified. Dropping the
large-label restriction first permits mixed prime bases at n=7, labels 3 and
17 with target 51; the earlier exploratory n=8 guess was corrected.

The cutoff envelope is everywhere at least the exact old budget, with exact
excess C-K_large. It therefore supplies no universal strict old-budget gain.
Large prime-base singleton fibers dominate the measured mass at 297/1031,
and a production subset theorem proves those bases have only depth one.
Outcome B is selected. The next natural frontier is an independent weighted
bound for their cofactor-window prime occupancy; no candidate useful U or
full instruction-030 architecture is manufactured.

## Final validation

Focused, facade, root and complete axiom builds pass with two Lean threads.
All 18 production and 14 calibration declarations have only standard logical
axioms. Existing root warnings remain outside the new dependency surface.
Headers, file markers, forbidden-token scans, whitespace, source digests and
ASCII artifacts are checked. Resource metrics are retained in validation-029.
'''
p.write_text(s)
subprocess.run([sys.executable,str(base/'checks/plain-logs-029.py')],check=True)
with (base/'logs/check-029.txt').open('w') as out:
    result=subprocess.run([sys.executable,str(base/'checks/check-029.py')],stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/check-029.txt').read_text())
raise SystemExit(result.returncode)
