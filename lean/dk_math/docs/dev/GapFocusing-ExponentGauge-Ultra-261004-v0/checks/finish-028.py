"""Render the checkpoint closeout from measured builds and exact diagnostics."""
from pathlib import Path
import json,subprocess,sys
base=Path(__file__).resolve().parent.parent
summary=json.loads((base/'logs/diagnostics-summary-028.json').read_text())
coverage=json.loads((base/'logs/declaration-coverage-028.json').read_text())
measure=[]
for label in ['focused','facade','root','axiom-audit']:
    r=json.loads((base/f'logs/performance-{label}-028.json').read_text());assert r['exit_code']==0
    measure.append((label,r))
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n| --- | --- | --- | --- | --- | --- | --- |\n'
for label,r in measure:
    table+=f"| {label} | {r['exit_code']} | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
anchor='| n | low labels | small | large | low mass approx | VM approx | log cell approx | maximum fiber |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n'
for r in summary['anchors']:
    anchor+=f"| {r['n']} | {r['low_event_count']} | {r['small_count']} | {r['large_count']} | {r['low_mass_approx']:.6f} | {r['shell_VM_approx']:.6f} | {r['log_cell_approx']:.6f} | {r['max_large_fiber']} |\n"
report='''# Report 028 - Divisor incidence and binary carry cancellation

The required finite bridges and cancellation identities are proved for n>=3:

 log(cell) = shell VM + low carry mass
 old Pascal budget = higher correction + low carry mass.

This is an exact coordinate for the existing frontier. No new universal upper
bound on total carry mass or universal shell lower provider is obtained.
Individual large labels have unique shell multiples, but their map is not
injective. Colliding large prime-power labels necessarily have the same base.

Production and validation surface:

- [Neutral DivisorIncidence](../../../DkMath/NumberTheory/DivisorIncidence.lean)
- [GnomonDivisorCarry](../../../DkMath/NumberTheory/Legendre/GnomonDivisorCarry.lean)
- [Updated facade](../../../DkMath/NumberTheory/Legendre.lean)
- [Kernel calibration](../../../DkMathTest/NumberTheory/GnomonDivisorCarryCalibration.lean)
- [Complete axiom audit](../../../DkMathTest/NumberTheory/GnomonDivisorCarryAxiomAudit.lean)
- [Source inventory](source-inventory-028.md), [findings](findings-028.md), [validation](validation-028.md).

Write base=n^2, width=2*n and top=base+width. All divisions in counts are
natural divisions, and every displayed logarithm is a natural logarithm.

## 1. Exact shell multiple-count function

GnomonShellMultipleCount, spelled gnomonShellMultipleCount in Lean, is
 top/d-base/d as a Nat subtraction. Its total value at d=0 is zero.
Arithmetic counting statements explicitly assume d>0.

## 2. Exact counting proof

Yes. gnomonShellMultipleCount_eq_card identifies this number with the card
of (Icc(base+1,top)).filter(d divides m). The neutral prefix proof reuses
Nat.Ioc_filter_dvd_card_eq_div; subtraction of nested finite prefix carriers
proves the arbitrary-shell count. There is no floating count or heuristic.

## 3. Finite divisor-incidence transpose

Yes. sum_shell_divisors_eq_floor handles an arbitrary real weight. Positive
m has exactly the divisors in Icc(1,top) that divide m. Finset.sum_comm and
the exact filter card yield the weighted floor sum. gnomonShell_divisor_incidence
instantiates this with von Mangoldt, in the requested n>=1 domain.

## 4. Exact log shell-product identity

Yes. vonMangoldt_sum expands every log(m). Real.log_prod applies because all
shell factors are positive. gnomonShell_log_prod_eq_divisor_mass retains the
full divisor interval through top and every multiplicity. The neutral theorem
also covers empty shells; no estimate of psi is imported into this argument.

## 5. Cell/factorial to VM/lower-divisor bridge

Yes. gnomonPascalCell_mul_factorial_eq_shell_prod reindexes the existing product.
Logs first give log(cell)+log(width factorial)=sum_shell log(m). For n>=3,
each base<d<=top has top<2*d and multiple count one. Splitting the full
carrier proves the required
 gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass.
The lower mass is nonnegative but no smallness estimate is inferred.

## 6. Generic factorial floor identity

Yes. log_factorial_eq_floor states
 log(N factorial)=sum over Icc(1,N) of (N/d)*Lambda(d), including N=0.
Its proof is the neutral base-zero incidence result and the factorial product.
log_factorial_eq_floor_cutoff allows any B>=N, since all extra quotients vanish.
No second proof through factorization was added.

## 7. Exact binary carry bit

For d>0, gnomonLowDivisorCarryBit n d is one exactly when
 d<=base%d+width%d, and zero otherwise. The total zero-divisor convention is
zero. The binary and at-most-one theorems include that convention.

## 8. Multiple count decomposition

Yes. gnomonShellMultipleCount_eq_div_add_carry states
 multipleCount=width/d+carryBit for d>0, directly from Nat.add_div and natural
subtraction cancellation. Explicit Nat casts prevent replacing floor quotients
by real division.

## 9. Exact remainder-phase condition

Yes. The positive-divisor one iff and zero iff theorems state the crossing
predicate and its strict reverse. This is a single Nat bit API; no parallel
Bool coordinate or redundant valuation framework was introduced.

## 10. Next-multiple gap

nextMultipleGap(base,d) is d-base%d for d>0 and zero for d=0. If the boundary
is aligned, its gap is d, because the next multiple is strictly later.
Carry one iff gap<=width%d is proved. If d>width, width%d=width, so it is
exactly gap<=width. No square endpoint or next-square point is included.

## 11. Lower mass equals factorial log plus carry mass

Yes. gnomonPascalLowerDivisorMass_eq_factorial_add_carry uses width<=base
for n>=3, the extended factorial cutoff, and the pointwise floor decomposition.
All uniform factorial contribution is exposed before cancellation.

## 12. Central cancellation

Yes. gnomonPascalCell_log_eq_shellVM_add_lowCarryMass cancels the common
factorial log over the reals. The resulting residual is exactly binary
lower-prime-power phase mass. This equality alone asserts no lower bound.

## 13. Exact old Pascal comparison

Yes. gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass is subtraction-free.
It combines the existing old plus birth and VM equals birth plus higher
identities with the central theorem. Thus K is precisely the old budget with
the already-small higher correction removed; it is not independent information.

## 14. Prime-power event support

Yes. gnomonPascalLowCarryEvents filters Icc(1,base) by IsPrimePow and bit one.
Exact membership and low mass equals sum of Lambda on these events are proved.
Each label p^a has weight log(p), justified symbolically by vonMangoldt_apply_pow.
The bit does not retain full valuation height; distinct powers remain labels.

## 15. Agreement with choose carries

The pointwise prime-power theorem uses the same predicate as
GnomonPascalCell_factorization_carries, spelled gnomonPascalCell_factorization_carries
in Lean, after commuting the two remainders. The sum-level old comparison
accounts exactly for old labels plus higher shell powers. No additional
per-prime old-height theorem was forced. In diagnostics, every prime-coordinate
choose height was independently reconstructed by factorial floor valuations.

## 16. Small/large band decomposition

The two finite carriers filter the low events at d<=width and width<d.
Their masses sum exactly to K and feed a band-wise conditional margin provider.
Small labels keep width%d; large labels use the full width and a unique grid
hit. In the scan n=3..5000, small mass is at most 45.2681 percent of K, at n=3,
and as low as 4.9460 percent, at n=4576. The large band dominates in this finite
range; this is diagnostic evidence, not a universal theorem about dominance.

## 17. Unique large shell multiple and cofactor

Yes. gnomonNextShellMultiple n d=d*(base/d+1). The packet proves SquareCell
membership and divisibility under d>width and bit one. The uniqueness theorem
quantifies all other divisible shell integers. The cofactor base/d+1<n is
proved for every n>=3 and d>width, even before imposing the event predicate.
The distinct-base exclusion theorem shows two large prime-power divisors of
one shell integer share a prime base: otherwise their coprime product exceeds
top while dividing that integer. This does not exclude same-base chains.

## 18. Failure of label-map injectivity

No. The smallest positive-anchor collision is n=11:
 32=2^5 and 64=2^6 both map to 128.
The exact carrier memberships, images and failure of InjOn are kernel checked.
A finite kernel certificate proves all earlier positive anchors 1..10 have
injective large-label maps. General collision iff shared divisible shell
integer is proved. The largest finite multiplicity is ten at n=2896; its image
2^23 has old large labels 2^13 through 2^22. This latter complete scan result
is an integer diagnostic, not a newly added kernel certificate.

## 19. Relation of the conditional prime criteria

The carry/log-log criterion is proved exactly equivalent to
 log-log budget<shell VM, namely the existing 027 sufficient condition.
It implies the old strict criterion, but its equivalence to that old criterion
is not proved. Algebraically it requires
 birth mass>log-log budget-higher correction,
whereas oldBudget<log(cell) requires only birth mass>0. The margin difference
is nonnegative by 027. Replacing the upper budget by the exact higher correction
gives a proved exact equivalence with the old criterion. No actual anchor
counterexample to the fixed log-log converse is asserted; no converse provider
or universal strict inequality was proved.

The generic consumer also accepts K<=B and B+margin<log(cell), concluding
margin<VM. Multiplicative growth gives (base+1)^width<=cell*width factorial,
and its log form gives width*log(base+1)<=log(cell)+log(width factorial).
Any derived VM bound must still subtract K. Product growth alone supplies no
shell-prime theorem.

## 20. Diagnostics and the 297/1031 anchors

[Full data](logs/diagnostics-028.jsonl) record all n=1..5000; the
[summary](logs/diagnostics-summary-028.json) gives explicit mandatory-anchor
labels, bases, depths and complete large-image distributions. Prime labels
are losslessly encoded by prefix-summed positive deltas; each decoded prime
has base equal to its label and depth one. Higher-power triples explicitly
record label, base and depth. The image rule reconstructs every shell multiple;
each row also records its exact multiplicity histogram and maximum.

Route A factors every shell integer and enumerates its prime-power divisors.
Route B reconstructs all binary power carries by floor division. Candidate
prime support is complete because a carry implies a positive shell multiple
count. Choose heights are separately checked through factorial floor sums.
Both integer ledger identities hold at every n>=3. The n=1 central flag is
false outside this domain; n=2 happens to satisfy it. All logs, residuals and
strict-provider flags are explicitly floating diagnostics. The old Pascal
budget here is the actual valuation budget, not the 026 log-count upper budget.

ANCHOR_TABLE

At 297, K=old budget approximately 3049.641111 and higher correction is zero.
The large mass is approximately 2832.887744; all 338 large images are distinct.
At 1031, K=old budget approximately 12716.333826 and correction is again zero.
The large mass is approximately 11833.466270, with 1160 labels on 1158 images.
The largest fiber there has three labels. Empty higher correction therefore
never means empty old carry mass. The mandatory anchors are all retained.

Kernel calibration proves complete carriers at 3,5,11 and selected small/large
packets at 297 and 1031, including every requested coordinate and universal
unique-multiple statements for large labels. Inherited complete higher-empty
certificates at 19,297,1031 yield symbolic zero-correction ledger identities.
No large real-log inequality is kernel evaluated. The floating log-log provider
comparison passed all n=3..5000; this is not universal evidence.

## 21. New bound, build evidence and remaining frontier

No new universal upper bound on total K was proved. Binary support, unique
multiples, small cofactors and same-base collisions are structural theorems.
The unresolved strict estimate is K+log-log budget<log(cell) for all relevant
anchors, equivalently the unresolved 027 shell VM lower comparison. No Legendre,
PNT, RH, or short-interval Chebyshev theorem is asserted.

All 57 new public production declarations and 32 new calibration declarations
are included in the 89-declaration axiom audit. Only propext, Classical.choice
and Quot.sound occur; there are no new sorryAx dependencies or forbidden proof
constructs. The neutral module has no application or RH dependency. Facade
export was added after focused validation passed.

TELEMETRY_TABLE

All four final invocations used LEAN_NUM_THREADS=2 and /usr/bin/time -v.
The final focused invocation replayed already compiled targets; its RSS is
therefore not a clean-compilation peak. Facade, root and axiom outputs retain
their actual compile/replay evidence. These are Lake and waited-descendant
process metrics, not total host memory. No observed OOM, kill, timeout or manual
termination occurred. Major faults and reported swaps were zero.
The facade retains the pre-existing PacketCross unused-variable warning.
Root additionally replays five pre-existing sorry warnings in unrelated files;
none is in the new declarations' dependency audit.

## 22. Exactly one theorem proposed for instruction 029

Attempt the large-band common-base fiber-cap theorem:

 K_large(n) <= sum over occupied large shell images m of
   (Nat.log p_m(base)-Nat.log p_m(width))*log(p_m), for n>=3.

Here p_m is the unique prime base of the large labels mapping to m, well-defined
by the proved distinct-base exclusion. The natural-logarithm notation log(p_m)
and the integer cutoff Nat.log p_m are deliberately different. The right weight
uses only the anchor, the prime base and the occupied image; it does not use
carry bits or actual image valuation height. It is an upper bound on possible
same-base powers, rather than another equality renaming K.

Implementation proposal: define the occupied image and choose its common base;
show each fiber's exponents inject into Icc(Nat.log p_m(width)+1,
Nat.log p_m(base)); count that finite interval and multiply by the nonnegative
base log; sum the fiber bounds. Existing unique-multiple and common-base
lemmas discharge geometry. Keep the image itself explicit instead of silently
assuming its card is the label count.

[Candidate diagnostics](logs/fiber-cap-028.json) show cap/large mass from
1 to approximately 1.079630 over n=3..5000. At 297 the ratio is approximately
1.006433, at 1031 approximately 1.003638, and at 5000 approximately 1.000935.
It accommodates the ten-label chain at 2896. These are diagnostic values only;
this proposed bound is not implemented in 028. Even proving it will still
require control of the occupied-image prime weights before it becomes a global
provider. No claim is made that this cap alone solves the strict margin.

Outcome B - BINARY CARRY MASS IS AN EXACT RECOORDINATION OF THE OLD FRONTIER
'''
(base/'report-028.md').write_text(report.replace('ANCHOR_TABLE',anchor.rstrip()).replace('TELEMETRY_TABLE',table.rstrip()))
validation='''# Validation 028

Final measured commands use LEAN_NUM_THREADS=2. All completed successfully.

- focused: lake build DkMath.NumberTheory.DivisorIncidence DkMath.NumberTheory.Legendre.GnomonDivisorCarry DkMathTest.NumberTheory.GnomonDivisorCarryCalibration
- facade: lake build DkMath.NumberTheory.Legendre
- root: lake build DkMath
- axiom: lake build DkMathTest.NumberTheory.GnomonDivisorCarryAxiomAudit

'''+table+'''
GNU time reports Lake and waited-descendant process usage. The final focused
command replayed cached targets; it is not a fresh-compilation RSS measure.
Raw telemetry and structured performance records are in logs with suffix 028.
No OOM, kill, timeout or manual termination was observed. Reported major faults
and swaps are zero; minor faults are retained above.

The complete named surface is 57 new production and 32 new calibration
declarations, total 89. Axiom coverage is dynamically generated by
checks/coverage-028.py. Only standard logical axioms are allowed by the checker;
no sorryAx or forbidden proof construct is accepted. The neutral dependency
firewall, all four new Lean headers, facade header, immediate file markers,
tracked and untracked whitespace, and parser-safe artifacts are audited.

Diagnostics cover n=1..5000. Shell-divisor enumeration is independently compared
with binary floor carries; factorial valuations independently check choose
heights. Integer ledgers are checked in the required domain n>=3. The lossless
prime-label delta stream plus higher-power triples preserves every event label,
base and depth. Image distributions are reconstructed by the unique image rule.
The checker compares VM and correction with the inherited 026 inventory, and
checks the full 5000-row digest. Float values are never Lean proof premises.

Kernel certificates cover full small carriers, the smallest collision and all
earlier positive anchors, selected packets at 297/1031, and inherited complete
higher-empty carriers. No transcendental inequality is decided computationally.

The facade retains its existing PacketCross warning. The root retains five
existing unrelated sorry warnings; the new declaration audit excludes their
axiom dependencies. Focused and axiom builds introduce no warning.

Reproduction scripts: checks/diagnostics-028.py, checks/fiber-cap-028.py,
checks/coverage-028.py, checks/build-028.py, checks/plain-logs-028.py,
checks/finish-028.py and checks/check-028.py. The latter prints the final audit
results to logs/check-028.txt when invoked by finish.
'''
(base/'validation-028.md').write_text(validation)
p=base/'findings-028.md';s=p.read_text().split('## Final diagnostics and route judgment')[0]
s+='''## Final diagnostics and route judgment

All 5000 positive anchors were reconstructed. In the proved n>=3 domain,
all carrier and integer ledger checks passed. Smallest collision is n=11,
32 and 64 mapping to 128. Maximum large-image multiplicity is ten at n=2896.
Same-image large prime-power labels have a common prime base, proved in Lean.
Small mass is at most 45.2681 percent in the finite provider-domain scan.
At 297 and 1031 the higher correction is zero while K is large and positive.

Outcome B is the final judgment: the exact coordinate closes, but no new total
carry upper provider is proved. The single 029 candidate is the common-base
fiber cap described in report-028; its diagnostic envelope over large mass is
between one and approximately 1.079630. It remains unimplemented and needs
image-weight control to become a global provider.

## Final validation

All four measured LEAN_NUM_THREADS=2 builds passed. Complete axiom coverage
includes 57 production and 32 calibration declarations. The new surface has
only standard logical axioms. Existing root warnings remain outside it.
Telemetry and parser-safe source/diagnostic audits are retained in validation-028
and logs/check-028.txt.
'''
p.write_text(s)
subprocess.run([sys.executable,str(base/'checks/plain-logs-028.py')],check=True)
with (base/'logs/check-028.txt').open('w') as out:
    result=subprocess.run([sys.executable,str(base/'checks/check-028.py')],stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/check-028.txt').read_text())
raise SystemExit(result.returncode)
