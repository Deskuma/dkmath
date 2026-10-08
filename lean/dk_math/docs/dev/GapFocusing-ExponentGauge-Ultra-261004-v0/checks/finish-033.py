"""Render checked distinct-semiprime results and final scoped validation."""
from pathlib import Path
import json,subprocess,sys,re
base=Path(__file__).resolve().parent.parent
coverage=json.loads((base/'logs/declaration-coverage-033.json').read_text())
data=json.loads((base/'logs/diagnostics-033.json').read_text())
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n| --- | --- | --- | --- | --- | --- | --- |\n'
for label in ['focused','facade','root','axiom-audit']:
    r=json.loads((base/f'logs/performance-{label}-033.json').read_text());assert r['exit_code']==0
    table+=f"| {label} | 0 | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
anchors='| n | E approx | D approx | E-D approx | Saving over 032 approx | New consumer margin approx |\n| --- | --- | --- | --- | --- | --- |\n'
for r in data['anchors']:
    if r['n'] in [3,9,12,29,31,32,210,297,1031,5000]:
        anchors+=f"| {r['n']} | {r['error_approx']:.6f} | {r['semiprime_mass_approx']:.6f} | {r['remaining_error_approx']:.6f} | {r['improvement_over032_approx']:.6f} | {r['consumer_margin_approx']:.6f} |\n"
report='''# Report 033 - Distinct semiprime composite correction

An independent endpoint carrier of ordered prime-factor products now supplies
a collision-safe lower composite mass D. It includes the 032 square witness
and admits off-diagonal semiprimes such as 77. The corrected envelope improves
032 and recovers the strict consumer at n=31, kernel checked. At n=32 it still
leaves 343 and 539. Larger retained diagnostics leave substantial residual
error, with the first numeric failure at 210. No universal strict budget gain
or new unconditional prime-existence range beyond the exact ledger is proved.
The result is Outcome B.

## Implementation and existing receivers

Added [GnomonCofactorSemiprime](../../../DkMath/NumberTheory/Legendre/GnomonCofactorSemiprime.lean)
and one import in the [Legendre facade](../../../DkMath/NumberTheory/Legendre.lean).
The module has 15 public declarations: four definitions and eleven theorems,
plus one private pair-facts helper. Its sole direct import is
GnomonCofactorLeastFactor. Earlier production modules are reused without edits.
Unified copyright/import headers and the immediate file print markers remain.
No new general sieve hierarchy or analytic hypothesis is introduced.

[Source inventory](source-inventory-033.md) records the inspected internal
upperPairs, PairOverlap, roughPairs, factor-cover and prime-divisibility APIs.
The old strict-pair/support-wave receivers exclude squares or impose different
active-support carriers. The 032 factor cover already supplies the required
endpoint geometry, so a thin prime-complement filter is the chosen extension.
[Findings](findings-033.md) records the mathematical scope and remaining issue.

[Calibration](../../../DkMathTest/NumberTheory/GnomonCofactorSemiprimeCalibration.lean)
contains ten named public kernel checks. The
[axiom audit](../../../DkMathTest/NumberTheory/GnomonCofactorSemiprimeAxiomAudit.lean)
covers all 25 new public declarations. The private helper is audited
transitively through the public product-injectivity and inclusion results.

## Actual collision-safe carrier

For each k in Icc(2,n-1), write A=max(n^2/k,2*n), B=(n^2+2*n)/k,
using natural floor division, and M=finitePrimeBasisProduct S.
The chosen pair carrier filters the 032 factor cover by primality of its
complementary factor. Thus its pairs satisfy

 2<=r<=sqrt(B), r prime, s prime, r<=s,
 gcd(r,M)=gcd(s,M)=1, A/r<s<=B/r.

Equivalently, the endpoint product lies in A<r*s<=B. The diagonal r=s is
included. This definition uses only endpoints, the finite wheel and factor
primality. It uses neither minFac of target q, the actual singleton-prime
carrier Q, the target composite filter nor carry-event membership. Complete
factorization of each surviving target is not used to construct the witness.
Factor primality is the permitted finite witness condition, not a query about
whether a target belongs to Q.

For equal products of two pairs, the first prime of one divides one of the
other pair's primes. Prime divisibility forces equality of those factors.
If it is the same orientation, positive cancellation identifies the second
factors. In the swapped orientation, both order inequalities force the same
ordered pair. This proves the product map injective, including the square
case. No assumption of collision-free raw composite complements is made.

The witness carrier is the product image of these pairs. The sum_image theorem,
using the proved injection, identifies its log sum with the pair-log sum.
The image makes distinct-product semantics explicit even before that equality
is used. Both factors are nonunits and avoid the wheel, so every product is
an actual surviving composite. Existing 032 product membership proves this
without a new target classification predicate.

## Certified lower mass and exact remaining excess

Let D be the sum of log(q) over this product image, accumulated over all
cofactor windows with the same outer indexing as E. Inclusion and nonnegative
composite weights prove D<=E. Every 032 diagonal pair has prime second factor,
so its square product belongs to the new witness carrier. Therefore

 L<=D<=E.

Squares are included in D once; L is not added again. The independent witness
is more than the old square carrier and is not defined by the exact composite
inventory. It remains incomplete for higher-composite products.

Write U for the 032 envelope and define one new envelope

 Z=min(U,V-D).

Under n>=3 and the existing admissible finite prime-basis cutoff, the kernel
proves

 Q<=Z<=U<=W<=G,
 Z-Q=min(U-Q,E-D).

Z<=U itself is unconditional. The error identity is exact, not a numerical
premise. D is a lower witness, so subtracting it has the right inequality
direction; the 032 upper error bound F is not subtracted. The cap retains
all earlier valid envelopes. No optimality claim is made.

## Required calibration points and collision regression

At n=9, (7,7) and its product 49 are admitted. At n=12, (7,11) and its
product 77 are admitted safely. These memberships are kernel checked.
A complete finite carrier check proves the witness equals the actual composite
carrier in every window at each n in {9,12,29,31}. Consequently D=E and Z=Q
at those four anchors, kernel proved. This equality is a finite calibration
result, not the definition of D or a universal classification theorem.

At n=29 all eleven composites from the 032 canonical table are products of
two primes. The new witness deletes all their weight, including the three
squares 289,169,121. The square-only remaining excess about 43.581353 is
removed, giving the exact-ledger margin about 54.147116. The earlier kernel
consumer at 29 is preserved by Z<=U.

At n=31 all sixteen surviving composites are semiprime witnesses. The 032
square correction left error about 77.481826 and failed with margin about
-8.458239. The new excess is zero and the margin is about 69.023587.
Exact integer comparison proves residualProduct*sieveProduct <
cell*semiprimeProduct; logarithmic monotonicity and log-product identities
prove the strict new consumer. Together with the inherited 032 failure,
this proves Z(31)<U(31), not merely a positive numerical saving.

At n=32 the old raw factor pairs (7,77) and (11,49) still represent 539.
Both are excluded from the new pair carrier because their complementary
factors are composite. Kernel checks also prove 539 is absent from the
semiprime product image. Thus it is not subtracted once or twice. The cube
343=7^3 is likewise not semiprime. A complete kernel residual-carrier check
fixes {539} in k=2 and {343} in k=3, with every other residual window empty.
Their remaining log weight is log(539)+log(343), about 12.127446.
Diagnostics show the new margin at 32 is about 50.511638; the weight reading
agrees with this exact residual carrier. No large numerical inequality is
used as a Lean premise.

At n=3, Z=U is kernel checked, ruling out strict gain at every admissible n.
The n=7 recovery is also retained through the proved chain of upper bounds.

## Effect on the exact 028-032 ledger

All small carry, repeated carry and higher-shell terms remain unchanged.
The inherited identity is oldBudget=H+S_small+R+Q. The new exact insertion is

 S_small+R+Z+H=oldBudget+(Z-Q).

The consumer requires S_small+R+Z+H<log(cell), with n>=3 and an admissible
basis, and then proves a prime exists in SquareCell. Since Q<=Z, the new
envelope is still at least the exact old ledger. Recovering n=31 improves
032's independent envelope, while the exact ledger already covers that case.
It therefore does not satisfy the instruction's Outcome A criterion.
No universal strict consumer premise or new unconditional range beyond that
ledger is established.

## Bounded diagnostics and remaining obstruction

[Diagnostics](logs/diagnostics-033.json) contains 300 rows: every n=3..300,
plus 1031 and 5000. It enumerates endpoint pairs independently and retains
ANCHORCOUNT anchor reconstructions, including all required checkpoints and
210. The product sets are checked for injectivity, composite inclusion and
square inclusion. Digests link the unchanged 031 and 032 diagnostic sources.
Target factorization is used only to audit residuals; it does not define D.
All reported log weights and consumer margins are floating diagnostics only.

ANCHORS

The first numeric consumer failure in this range is n=210. Its E-D is about
428.038020, exceeding the available exact-ledger margin about 406.547983;
the resulting margin is about -21.490037. This failure and its minimality
are diagnostic only, not kernel-certified. Many later anchors pass, so no
monotone failure threshold is asserted. This finite experiment does not
prove a universal failure statement for all semiprime or adaptive strategies.

At 297,1031,5000 the residuals are about 699.205940,6266.644524,65561.859242,
and all three displayed consumers fail numerically. At 5000, D removes
about 115704.398537 of E's 181266.257779, but the remaining 65561.859242
still exceeds the exact-ledger margin about 10442.199332. Semiprime deletion
is substantial; it does not control the higher-composite residual globally.
No PNT, RH or unproved short-interval theorem is used to force closure.

## Validation

All final focused, Legendre facade, DkMath root and complete public axiom builds
passed with LEAN_NUM_THREADS=2. Focused and axiom builds emit no warnings.
Facade/root replay the existing PacketCross unused-variable warning. Root
additionally replays five inherited sorry warnings in unrelated modules,
whose sources were not edited. No repository-wide no-sorry claim is made.

METRICS

GNU time measures Lake and waited descendants. Peak RSS is process telemetry,
not a sum of simultaneous allocation. No build memory failure or swap occurred.
All 15 production and ten calibration declarations have only the standard
logical axioms propext, Classical.choice and Quot.sound, with no sorryAx in
that checked scope. Scoped large-product kernel budgets are documented in
calibration; binomial computation uses the proved fast_choose identity.
Headers, immediate file markers, forbidden constructs, dependency direction,
whitespace, source digests, finite diagnostic identities, ASCII artifacts and
Markdown links passed their audits. Exact evidence is in
[validation](validation-033.md).

## Next natural frontier and implementation proposal

The remaining quantitative target is a collision-safe lower certificate for
higher-composite weight, or an independent upper estimate for the residual
weighted carrier. In the current coordinates closure needs

 min(U-Q,E-D) < log(cell)-oldBudget.

Unique prime pairs solve the pair collision issue, but do not control cubes
or products with three or more prime factors. A bounded next investigation
could first measure ordered prime triples, including repeated factors, against
the retained 343 and 539 regression and the failing large-anchor residuals.
Any subtraction must have a proved product injection or an exact collision
correction; simply returning to raw factor-pair weights is invalid.

Before promoting an additional carrier, compare its distinct-product lower
mass with the accumulated residual and retain endpoint/window multiplicities.
A complete factorization hierarchy that eventually reconstructs all composites
is exact classification, not a new independent quantitative estimate. A useful
next provider must justify a nontrivial bound for the remaining weighted
short-window mass. No theorem that every elementary route necessarily needs
analytic prime-distribution input has been established. No later checkpoint
architecture or speculative hierarchy is prescribed.

Outcome B - DISTINCT SEMIPRIME CORRECTION WITHOUT GLOBAL CLOSURE
'''.replace('ANCHORS',anchors.rstrip()).replace('METRICS',table.rstrip()).replace('ANCHORCOUNT',str(len(data['anchors'])))
(base/'report-033.md').write_text(report)
warnings=[]
for label in ['facade','root']:
    found=re.findall(r'^warning:.*$',(base/f'logs/{label}-033.txt').read_text(),re.M)
    warnings.append(label+': '+str(len(found))+' inherited warnings.\n'+'\n'.join('- '+w for w in found))
validation='''# Validation 033 - Final checked scope

Commands executed from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorSemiprimeAxiomAudit

METRICS

All exits are zero. GNU time includes Lake and waited descendants, with no
build memory failure. Changes comprise the new production module, calibration,
axiom audit and one facade import. Earlier production modules have no diff.
All 15 production and ten named calibration declarations are covered;
only propext, Classical.choice and Quot.sound occur, with no sorryAx.
The private production pair-facts helper and private calibration helpers are
covered transitively. Focused and axiom builds have no warnings. Inherited
warnings are recorded below; root success is not a whole-repository no-sorry
certificate.

WARNINGS

Kernel checks include 49/77 pair and product membership, complete witness
coverage and Z=Q at 9,12,29,31, exclusion of the two 539 representations,
all residual windows at 32, preserved consumer at 29, exact integer products
and strict consumer recovery at 31, strict improvement over 032 at 31, and
equality at 3. Scoped recursion/heartbeat allowances for the 31 products are
documented; binomial computation uses the proved fast_choose identity.
No native_decide or custom evaluation axiom is used.

Independent diagnostics retain 300 rows: n=3..300 plus 1031 and 5000, with
ANCHORCOUNT direct anchor reconstructions. The first numeric failure 210
and its minimality are diagnostic only, not kernel claims. Audit checks
source digests, exact endpoint prime-pair carriers, product injection,
composite and square inclusion, finite weighted identities and floating-only
margins. Target factorization in diagnostics is not used to construct D.
Additional checks cover public axiom names, forbidden constructs, import
scope, headers, immediate file markers, whitespace, Markdown links and ASCII
logs. Results are evidence only for these recorded scopes.

Evidence: [focused](logs/focused-033.txt), [facade](logs/facade-033.txt),
[root](logs/root-033.txt), [axioms](logs/axiom-audit-033.txt),
[coverage](logs/declaration-coverage-033.json), [diagnostics](logs/diagnostics-033.json),
[artifact audit](logs/artifact-check-033.txt).

Outcome B - distinct semiprime correction; no global closure.
'''.replace('METRICS',table.rstrip()).replace('WARNINGS','\n\n'.join(warnings)).replace('ANCHORCOUNT',str(len(data['anchors'])))
(base/'validation-033.md').write_text(validation)
p=base/'findings-033.md';s=p.read_text().split('\n## Final validation\n')[0]
p.write_text(s+'''\n## Final validation

Focused, facade, root and all 25 named public axiom checks passed with two
Lean threads. No new warning or sorryAx occurs in the checked public surface.
Kernel checks fix complete small-anchor coverage, strict recovery at 31 and
higher-composite residual at 32. Inherited root warnings are scoped separately.
Outcome B: a distinct lower witness and stronger envelope, without global closure.
''')
subprocess.run([sys.executable,str(base/'checks/plain-logs-033.py')],check=True)
with (base/'logs/artifact-check-033.txt').open('w') as out:
    result=subprocess.run([sys.executable,str(base/'checks/check-033.py')],stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/artifact-check-033.txt').read_text(),end='')
raise SystemExit(result.returncode)
