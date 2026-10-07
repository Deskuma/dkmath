"""Render the checked factor-pair report, exact scope and build telemetry."""
from pathlib import Path
import json,subprocess,sys,re
base=Path(__file__).resolve().parent.parent
coverage=json.loads((base/'logs/declaration-coverage-032.json').read_text())
data=json.loads((base/'logs/diagnostics-032.json').read_text())
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n| --- | --- | --- | --- | --- | --- | --- |\n'
for label in ['focused','facade','root','axiom-audit']:
    r=json.loads((base/f'logs/performance-{label}-032.json').read_text());assert r['exit_code']==0
    table+=f"| {label} | 0 | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
anchors='| n | E approx | F approx | L approx | E-L approx | Corrected consumer margin approx |\n| --- | --- | --- | --- | --- | --- |\n'
for r in data['anchors']:
    if r['n'] in [3,7,9,12,29,31,32,33,297,1031,5000]:
        anchors+=f"| {r['n']} | {r['error_approx']:.6f} | {r['factor_pair_budget_approx']:.6f} | {r['square_lower_mass_approx']:.6f} | {r['remaining_error_approx']:.6f} | {r['consumer_margin_approx']:.6f} |\n"
report='''# Report 032 - Least-factor cover and oriented composite correction

The surviving composites have a canonical least-factor normal form, and an
independent endpoint factor-pair overcover now bounds their total error E.
Its upper-bound direction is important: E<=F implies V-F<=Q, so F cannot be
subtracted to improve an upper singleton envelope. A sparse diagonal lower
witness L<=E supplies a valid correction instead. The resulting envelope
Q<=U<=W recovers the failed 031 consumer at n=29, but fails at n=31; both
claims are kernel checked. This is Outcome B, without global closure or a
new prime-existence range beyond the exact ledger.

## Implementation and source scope

Added [GnomonCofactorLeastFactor](../../../DkMath/NumberTheory/Legendre/GnomonCofactorLeastFactor.lean)
and one export in the [Legendre facade](../../../DkMath/NumberTheory/Legendre.lean).
The new module has 20 public declarations: five definitions and 15 theorems.
Its sole direct import is GnomonCofactorSieve. Earlier production modules are
reused without source edits. Unified headers and immediate file print markers
are retained. No general sieve hierarchy, new wheel type, PNT, RH or unproved
short-interval assumption is introduced.

[Source inventory](source-inventory-032.md) records the inspected Mathlib
minFac, quotient, coprime, square-root and finite-sum APIs, and explains why
the older active-support rough-factorization receiver is not the same carrier.
[Findings](findings-032.md) records the bound orientation and chosen correction.
[Calibration](../../../DkMathTest/NumberTheory/GnomonCofactorLeastFactorCalibration.lean)
and [axiom audit](../../../DkMathTest/NumberTheory/GnomonCofactorLeastFactorAxiomAudit.lean)
retain the named kernel checks and complete public dependency evidence.

## Exact least-factor normal form

For the 030 window write A=max(n^2/k,2*n), B=(n^2+2*n)/k, using natural
floor division. Let M be finitePrimeBasisProduct S. If q survives its
031 coprime carrier and is nonprime, then q>1 and, with r=minFac(q), m=q/r,

 r is prime, q=r*m, r<=m, r^2<=B,
 gcd(r,M)=gcd(m,M)=1,
 A/r<m<=B/r,
 every prime divisor of m is at least r.

The strict lower quotient endpoint is exact because r>0 and q=r*m. The
square bound gives r<=sqrt(B). Product reconstruction proves the canonical
map q -> (r,m) injective in each window, so least-factor fibers are disjoint
and the canonical indexing is exact. These facts are structural routing, not
a distribution bound by themselves.

For a prime basis S, r is not a member of S. If S covers every prime at most
c, then r>c, proved separately. It is incorrect for an arbitrary finite basis
to say r exceeds its maximum: kernel calibration with S={2,5} and q=9 at
n=4,k=2 gives r=3. No complete initial-prime coverage is silently assumed.

## One independent factor-pair error bound

Define the finite cover P(n,k,S) using only endpoint and factor tests:

 2<=r<=sqrt(B), r prime, gcd(r,M)=1,
 max(r,A/r+1)<=m<=B/r, gcd(m,M)=1.

The key relaxation omits the requirement that every prime divisor of m be
at least r. No q.minFac, actual cofactor-prime carrier Q or carry-event
membership occurs in this definition. The complementary interval handles
reversed/empty windows without signed cardinal assumptions.

Every canonical pair lies in P. Every covering product is a surviving
composite, because r>=2, m>=r and both factors avoid the wheel. However
different covering pairs can have the same product. Define the independent
finite weighted bound

 F(n,S) = sum over k in Icc(2,n-1), pairs (r,m) in P of log(r*m).

Canonical injection, sum_image and nonnegative extra weights prove E<=F,
retaining the outer window indexing. This is an overcover inequality, not
merely the exact canonical factorization sum. At n=32,k=2, q=539 has the
pairs (7,77) and (11,49), both kernel checked, while minFac(539)=7. The
second pair is noncanonical and repeats log(539). Diagnostics find F-E is
exactly log(539) at n=32. No universal optimality of F is asserted.

This is the strongest independent upper error estimate formalized here.
It is a finite endpoint factor-pair weight, not an asymptotic or closed-form
short-interval estimate. Exact evaluation of the relaxed cover can still be
costly; no claim of analytic closure or general efficient estimation follows.

## Upper-error orientation and the valid correction

From V=Q+E and E<=F, the proved consequence is

 V-F <= Q.

The reverse inequality needed for an upper singleton bound does not follow.
Treating F as removable mass would undercharge Q whenever F>E, as the
539 duplicate demonstrates. A smaller upper bound for E alone does not
make V smaller or establish a stronger old-ledger consumer.

To obtain a correct upper-envelope improvement, use diagonal products r*r
inside P as certainly-composite witnesses. Their distinct product image is
taken separately in each window. Define L as its log weight. This carrier
contains no composite predicate, minFac test, carry event or Q oracle.
Inclusion into the actual composite carrier proves

 L<=E.

Only this lower certified composite mass is deleted. With the 031 W=min(G,V),
the single corrected singleton envelope and its exact error are

 U=min(W,V-L),          Q<=U<=W<=G,
 U-Q=min(W-Q,E-L).

For the first inequality n>=3 and the existing admissible prime-basis cutoff
are required. U<=W is unconditional. Since L>=0, this cap is also
min(G,V-L); the equivalent logarithmic product form is used in calibration.
The F bound is not used with the wrong sign in this definition.

## Structural calibration: 9, 12 and 29

At n=9, q=49 routes through (r,m)=(7,7). The full cover consists of this
single pair in k=2, with all other covers empty. Both F and L equal log(49),
kernel proved; inherited E=log(49) then proves U=Q at this anchor. This is
consistent with the old carry weight being log(7), a different quantity.

At n=12, q=77 routes through (7,11) and is absent from the diagonal witness
carrier, kernel checked. Diagnostics give E=log(49)+log(77), L=log(49),
so the nonsquare error log(77) remains. The fixed wheel has not been enlarged.

At n=29 the complete canonical triples (q,r,m) are kernel checked:

| k | Canonical triples |
| --- | --- |
| 2 | (427,7,61), (437,19,23) |
| 3 | (287,7,41), (289,17,17), (299,13,23) |
| 4 | (217,7,31), (221,13,17) |
| 5 | (169,13,13) |
| 6 | (143,11,13) |
| 7 | (121,11,11) |
| 11 | (77,7,11) |

All other canonical fibers are empty. The cover has 11 pairs at this anchor
and the diagonal products are 289,169,121. The square product 289*169*121
is kernel certified. L is about 15.592116, leaving E-L about 43.581353,
below the exact-ledger margin about 54.147116. The corrected consumer margin
is about 10.565763, whereas the 031 consumer was below zero.

Kernel integer comparison proves residualProduct*sieveProduct <
cell*squareProduct. Log monotonicity and log-product identities prove the
strict corrected consumer. This is a genuine finite improvement over 031,
while the exact old ledger already covers this case.

The former n=7 recovery is preserved by U<=W, with its strict consumer kernel
checked. At n=3, U=W, kernel checked, refuting strict improvement at every
admissible n. Diagonal deletion does not remove the nonsquare composites.

## Effect on the 028-031 budget and counterexample

Write S_small, R and H for the unchanged small carry, repeated carry and
higher shell correction. The exact old ledger remains

 oldBudget=H+S_small+R+Q.

The new exact substitution and strict consumer are

 S_small+R+U+H=oldBudget+(U-Q),
 S_small+R+U+H<log(cell) -> exists a prime in SquareCell.

Every residual term is retained. Because U>=Q, the new envelope is at least
the exact ledger. It cannot establish a range unavailable from that ledger
merely by replacing Q with an upper bound. The local n=29 recovery is not
Outcome A under the instruction's exact-ledger comparison criterion.

At n=31, E is about 87.407516 and L about 9.925689. The remaining 77.481826
exceeds the old-ledger margin 69.023587, giving a corrected margin about
-8.458239. Kernel arithmetic certifies both cell<residual*geometricProduct
and cell*squareProduct<residual*sieveProduct; symbolic logarithms prove
log(cell)<S_small+R+U+H. Thus even the corrected fixed-basis consumer does
not hold universally. No universal failure threshold is inferred.

## Independent bounded diagnostics

[Diagnostics](logs/diagnostics-032.json) contains 300 rows: every n=3..300,
plus 1031 and 5000. It independently enumerates endpoint factor pairs and
canonical composites, preserving multiplicity, and checks exact integer
carriers against prime/coprime tests. A hash links the retained 031 source.
The ANCHORCOUNT anchor windows are reconstructed and checked independently by the
artifact audit. All log weights and margins in this file are floating
comparisons only, never proof premises.

ANCHORS

The corrected consumer passes numerically at 3..30,32,33. The first numeric
failure is 31; failure at 31 is kernel proved, while minimality among earlier
margins remains diagnostic. The later passes again exclude a claimed monotone
threshold. At n=5000, L is only about 140.702 against E about 181266.258,
and F is about 284403.302. The cover duplication and remaining nonsquare
mass are substantial. No claim that every elementary factor method fails
follows from these bounded observations.

## Validation

All final focused, facade, root and complete public axiom builds passed with
LEAN_NUM_THREADS=2. Focused and axiom builds emit no warnings. Facade/root
replay the existing PacketCross unused-variable warning. Root additionally
replays five inherited sorry warnings in unrelated modules, whose sources
were not edited. No repository-wide absence-of-sorry claim is made.

METRICS

GNU time records Lake and waited descendants; RSS is process telemetry, not
a sum of concurrently allocated memory. No build memory failure or swap
occurred. All COUNT public declarations have only propext, Classical.choice
and Quot.sound; no sorryAx is present in this checked scope. Private
calibration helpers are covered transitively by named public checks. Exact
large-product checks use scoped recursion/heartbeat allowances with explicit
comments, and the proved fast_choose identity for binomial computation.
No native evaluation axiom is used. Headers, file markers, forbidden
constructs, whitespace, source digest, finite diagnostics and ASCII/link
artifact audits passed. Exact evidence is in [validation](validation-032.md).

## Next natural frontier and implementation proposal

The next useful quantitative target is a lower bound D<=E for distinct
certainly-composite products large enough to delete most nonsquare mass,
or an independent upper bound for the remaining prime weight itself.
It must close

 min(W-Q,E-D) < log(cell)-oldBudget.

An upper bound on E has a different orientation and does not close this
margin on its own. Diagonal deletion proves the orientation can be used
correctly, but is too sparse at the retained large anchors.

A bounded next investigation could select off-diagonal factor witnesses
with an explicitly proved collision bound or distinct-product injection,
and compare their lower weight against the nonsquare residual at 12,29,31,
32 and the large anchors. The 539 double representation must remain a
regression case: a raw sum of factor-pair weights cannot be subtracted as
though the products were distinct. Endpoint errors and outer window indices
must remain explicit. Only a provider independent of Q and carry membership,
with a useful total margin, should be promoted.

Taking the complete product image simply recovers the exact composite
carrier, while complete factor-test sieving recovers Q. Either is exact
classification, not an independent distribution estimate. No theorem that
all finite elementary routes require analytic prime-distribution input has
been proved. The investigated route still lacks effective weighted
short-window control. No later checkpoint architecture is prescribed.

Outcome B - FACTOR-PAIR ERROR BOUND AND CERTIFIED SQUARE DELETION WITHOUT GLOBAL CLOSURE
'''.replace('ANCHORS',anchors.rstrip()).replace('METRICS',table.rstrip()).replace('ANCHORCOUNT',str(len(data['anchors']))).replace('COUNT',str(coverage['total']))
(base/'report-032.md').write_text(report)
warnings=[]
for label in ['facade','root']:
    found=re.findall(r'^warning:.*$',(base/f'logs/{label}-032.txt').read_text(),re.M)
    warnings.append(label+': '+str(len(found))+' inherited warnings.\n'+'\n'.join('- '+w for w in found))
validation='''# Validation 032 - Final checked scope

Commands run from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorLeastFactor DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorLeastFactorAxiomAudit

METRICS

All exits are zero. GNU time records Lake and waited descendants, with no
build memory failure. Changes comprise the new production module, calibration,
axiom audit and one facade import. Earlier production modules have no diff.
All PROD production and CAL named calibration declarations are covered;
only propext, Classical.choice and Quot.sound occur, with no sorryAx.
Private calibration helpers are covered transitively. Focused and axiom logs
have no warnings. Inherited warnings are recorded below; root success is not
a repository-wide no-sorry certificate.

WARNINGS

Kernel checks include canonical routing of 49 and 77, all canonical triples
at 29, a noninitial-basis cutoff counterexample, duplicate cover at 32, the
exact cover/error lower witness at 9, corrected exactness at 9, preservation
of the 7 consumer, equality at 3, exact integer products and symbolic-log
consumer recovery at 29 and failure at 31. Minimality of the numeric failure
at 31 is not kernel claimed. Scoped recursion/heartbeat budgets for large
products are documented. Binomial evaluation uses the proved fast_choose
identity, without native_decide or added axioms.

Independent diagnostics cover every n=3..300 plus 1031 and 5000, totaling
300 rows, with ANCHORCOUNT retained anchor reconstructions. The 031 source digest,
canonical quotient restrictions, exact factor pairs and squares, duplicates,
weighted identities and floating-only consumer comparisons are audited.
The artifact check additionally covers public axiom names, forbidden
constructs, import direction, headers, immediate file markers, whitespace,
Markdown links and ASCII logs. Results are scoped to these checks.

Evidence: [focused](logs/focused-032.txt), [facade](logs/facade-032.txt),
[root](logs/root-032.txt), [axioms](logs/axiom-audit-032.txt),
[coverage](logs/declaration-coverage-032.json), [diagnostics](logs/diagnostics-032.json),
[artifact audit](logs/artifact-check-032.txt).

Outcome B - finite factor bound and local square correction; no global closure.
'''.replace('METRICS',table.rstrip()).replace('WARNINGS','\n\n'.join(warnings)).replace('PROD',str(coverage['production_count'])).replace('CAL',str(coverage['calibration_count'])).replace('ANCHORCOUNT',str(len(data['anchors'])))
(base/'validation-032.md').write_text(validation)
p=base/'findings-032.md';s=p.read_text().split('\n## Final validation\n')[0]
p.write_text(s+'''\n## Final validation

Focused, facade, root and complete public axiom builds passed with two Lean
threads. No new warning or sorryAx dependency occurs in the new public surface.
Kernel checks certify the local recovery at 29 and residual failure at 31.
All inherited root warnings are scoped in validation. Outcome B: independent
factor-pair error bound and certified square deletion, without global closure.
''')
subprocess.run([sys.executable,str(base/'checks/plain-logs-032.py')],check=True)
with (base/'logs/artifact-check-032.txt').open('w') as out:
    result=subprocess.run([sys.executable,str(base/'checks/check-032.py')],stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/artifact-check-032.txt').read_text(),end='')
raise SystemExit(result.returncode)
