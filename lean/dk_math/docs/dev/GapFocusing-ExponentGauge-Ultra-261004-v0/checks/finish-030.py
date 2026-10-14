"""Render verified finite results, build telemetry and the bounded research frontier."""
from pathlib import Path
import json, subprocess, sys

base=Path(__file__).resolve().parent.parent
coverage=json.loads((base/'logs/declaration-coverage-030.json').read_text())
data=json.loads((base/'logs/diagnostics-030.json').read_text())
metrics=[]
for label in ['focused','facade','root','axiom-audit']:
    r=json.loads((base/f'logs/performance-{label}-030.json').read_text())
    assert r['exit_code']==0
    metrics.append((label,r))
table='| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |\n| --- | --- | --- | --- | --- | --- | --- |\n'
for label,r in metrics:
    table+=f"| {label} | 0 | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['major_page_faults']} | {r['minor_page_faults']} | {r['swap_count']} |\n"
anchors='| n | Q approx | binomial U approx | combined G approx | combined consumer margin approx |\n| --- | --- | --- | --- | --- |\n'
for r in data['anchors']:
    anchors+=f"| {r['n']} | {r['singleton_mass_approx']:.6f} | {r['binomial_budget_approx']:.6f} | {r['geometric_budget_approx']:.6f} | {r['geometric_consumer_margin_approx']:.6f} |\n"
names='\n'.join('- '+d.rsplit('.',1)[1] for d in coverage['modules'][0]['declarations'])
report='''# Report 030 - Singleton cofactor windows and an independent finite bound

Q is proved to be exactly the old large singleton-prime carry mass. An
independent endpoint-only geometric bound G combines binomial divisibility
and odd-prime spacing, and is connected to the exact 028 ledger. Its envelope
has excess G-Q over that ledger. No strict budget gain or new prime-existence range is established. The first failed
strict consumer is n=7, certified by integer products and symbolic logarithms.

## Implementation and scope

Added [GnomonCofactorWindow](../../../DkMath/NumberTheory/Legendre/GnomonCofactorWindow.lean),
with 18 public declarations: six definitions and twelve theorems. Three private
proof helpers implement window routing, distinct-prime product comparison,
and odd-spacing cardinality.
The [Legendre facade](../../../DkMath/NumberTheory/Legendre.lean) exports the
module. Earlier production modules are reused without edits. Direct imports
are GnomonCarryFiber and Mathlib.Data.Nat.Choose.Dvd. Unified copyright/import
headers and the immediate file print marker are retained in all affected Lean
files. No prime-distribution assumption is added.

DECLARATIONS

[Source inventory](source-inventory-030.md) records the finite quotient,
rough-factorization, binomial, factorial and Chebyshev receivers inspected.
[Findings](findings-030.md) retain the route decisions.
[Calibration](../../../DkMathTest/NumberTheory/GnomonCofactorWindowCalibration.lean)
contains 13 public kernel checks; [axiom audit](../../../DkMathTest/NumberTheory/GnomonCofactorWindowAxiomAudit.lean)
covers all new named public declarations.

## Exact meaning of Q and uniqueness

Write base=n^2, width=2*n, top=base+width. All quotient endpoints are natural
floor quotients. For k in Icc(2,n-1), set A=max(base/k,width), B=top/k.
The prime window consists exactly of the primes A<p<=B. The double weighted
sum Q is gnomonCofactorWindowMass. For n>=3 the exact bridge proves

 Q = gnomonSingletonCarryMass
   = sum over prime labels in gnomonPascalLargeCarryEvents of log(p).

A contributing pair has base<p*k<=top, p<=base, and a binary low carry.
The 028 next-multiple uniqueness theorem forces k=base/p+1. Conversely each
large prime carry has this cofactor in Icc(2,n-1) and belongs to its window.
These are the two directions of the proved finite sum bijection.

Thus distinct cofactor windows have disjoint prime carriers. The uniqueness
theorem is used in the bridge proof. Window targets p*k are also distinct:
different large prime bases cannot divide one shell target by the existing
028 theorem; a repeated base has the unique cofactor. This latter observation
uses the earlier target-injection geometry rather than a new production API.
The raw intervals below the width cutoff need not be disjoint. Only the actual
cutoff carriers are relevant. Disjoint indexing alone saves no logarithmic mass.

Singleton-prime means a prime label p>width here. It excludes singleton
higher-power fibers, such as the n=6 base-2 fiber at target 48.

The repeated contribution is the complementary nonprime large carry mass,
whose labels are higher powers of their unique prime bases. These old large
divisor labels are different from higher prime powers lying in the shell.
The exact split is largeCarry = repeatedCarry + singletonCarry, so the 028
divisor/von-Mangoldt identity is preserved without changing multiplicities.
No rough-active or parity-safe hypothesis is imported from the older quotient
campaign: its carrier-specific APIs do not identify these windows directly.

## Strongest independent estimate proved here

Set C=B-A using natural subtraction, and define

 U(n) = sum over k in Icc(2,n-1) of log(choose(B,C)).

This definition contains only n, quotient endpoints and binomial coefficients.
It contains no carry-event predicate, occupied target set, or prime inventory.
For a window prime, A<p<=B. The floor-quotient estimate gives C<=n+1<p for
n>=3 and k>=2. Therefore p divides choose(B,C) by Nat.Prime.dvd_choose: both
denominator factorial cutoffs are below p, and the numerator reaches p.
The product of distinct window primes divides this positive coefficient, hence
is no larger than it. Real.log_prod and logarithmic monotonicity prove Q<=U.
Empty/reversed windows are handled: if A>B then C=0 and choose(B,0)=1.

This is a genuine new application-level finite estimate, built from existing
elementary library theorems. It is not a new general prime-distribution theorem,
and it is not merely the exact Q reindexing or a renamed carry capacity.
It is one component of the strongest independent bound formalized here.
No optimality among elementary estimates is claimed.

The audit also considers the all-integer cardinal cap (B-A)*log(B) and the
odd-cardinality cap J*log(max(1,B)), where J=((B+1)/2)-((A+1)/2) in natural
subtraction. The cardinal bound is now proved by injecting each window prime
p into the half-interval via p/2. Primes p>width>=6 are odd; their halves are
distinct and lie between the indicated endpoints. Monotonicity of log and the
cardinal bound give the weighted odd cap. This reuses the arithmetic idea of
the earlier rough-quotient odd-span theorem, without its carrier hypotheses.

The final independent bound takes the smaller estimate separately in each
window, rather than just the smaller of the two total sums:

 G(n) = sum over k of log(min(choose(B,C), max(1,B)^J))
 Q(n) <= G(n) <= U(n).

Both coefficients are positive. The max(1,B) convention handles empty and
zero-top windows and changes no occupied window. Each prime sum is bounded
by both logs, so taking the minimum is valid. This final G is the strongest
bound proved in this checkpoint. It gains the passing finite anchor n=8 over
the binomial-only candidate, but does not improve the exact 028 ledger or the
029 envelope in the retained diagnostic range. In fact G agrees numerically
with the odd-only cap at every retained anchor; no extra gain from taking
the per-window minimum is observed. No universal equality is asserted.

Global theta/psi bounds exist in Mathlib. The difference of finite theta sums
would exactly reindex Q. Subtracting global upper bounds for two endpoints is
not a valid upper bound for their difference. Neither PNT nor RH nor an unproved
short-interval estimate is used.

## Effect on the exact ledger

Let S be small carry, R repeated large carry, and H the exact higher shell
correction. The inherited ledger and the new split give

 oldBudget = H + S + R + Q.

The new exact excess theorem proves

 S + R + G + H = oldBudget + (G-Q).

Since Q<=G, the envelope is at least the old budget for every n>=3. The consumer
accepts S+R+G+H<log(cell), then applies the existing old-budget prime-existence
iff. This is a true upper-bound insertion with an explicit strict premise.
It does not prove that premise in general. It cannot remove the small,
repeated-power or higher residual terms. The entire overestimate is G-Q.

At n=3 the bound is exact, Q=G=U=log(7). At n=4, Q=log(11), G=log(144)
and U=log(495), so the first strict slack is kernel proved. The universal consumer inequality
is refuted at n=7. Kernel calibration proves it holds for all n=3..6, fixing
the first failure among the admissible anchors. The combined consumer also
passes n=8, kernel checked; it is not a monotone threshold. These small finite
checks do not extend the existing research range or supply a new unconditional range
of mathematical prime-existence results. The exact ledger is already a
weaker consumer than this envelope.

## Counterexample and bounded diagnostics

At n=7 the prime windows are k=2: {29,31}, k=3: {17,19}, and k=4: empty.
The numerical window for k=4 is (14,15], so its binomial coefficient is 15,
despite carrying no prime. Small labels are {3,5,9}, repeated large labels
{25,27}, and the higher shell correction is zero. Their base-weight product
is 675. The binomial-only product is 802638325125; taking the smaller
odd-spacing coefficients gives the combined product 128290919715. Cell is
37387265592825. Even the stronger envelope has the exact integer inequality

 37387265592825 < 675*128290919715 = 86596370807625.

Taking logarithms proves log(cell)<S+R+G+H. This is a kernel counterexample
to the proposed universal strict margin, not merely failure of a numeric test.
The combined envelope still charges odd composite slots and replaces each
weight by the top-endpoint log. The binomial-only candidate also charges
prime factors outside the actual window. These are concrete sources of loss.

[Diagnostics](logs/diagnostics-030.json) independently sieve primes through
top(5000)/2 and form all cofactor-window pairs for n=3..5000. At all 4998
anchors, their prime labels equal the hashed 028 inventory and both prime and
target projections are injective. The old 029 fiber budget is retained for
comparison with its own digest. No anchor in this finite range improves that
budget using either R+U or R+G. Binomial log estimates use lgamma; displayed
weights and all large-anchor margins are floating diagnostics, never Lean premises.

ANCHORS

The binomial-only exact-higher consumer passes numerically at 3,4,5,6,
whereas the odd cap and combined G pass at 3,4,5,6,8. The combined G fails
at all other 4993 retained anchors. Replacing H by the 027 log-log bound
passes 3,4 for U and 3,4,6 for G. These finite observations prove no universal
failure threshold and rule out no other elementary bound. The Lean first-failure proof is independent of
the diagnostic file and its floating evaluations.

## Validation

All four final builds passed with LEAN_NUM_THREADS=2. The focused and axiom
builds have no warnings. The facade replays the existing PacketCross unused
variable warning. The root additionally replays five pre-existing sorry
warnings in unrelated modules. Those modules were not edited, and root success
is not claimed as a repository-wide no-sorry result.

METRICS

GNU time measures Lake and waited descendants; RSS is process telemetry, not
a sum of simultaneous process memory. There was no memory failure or swap.
All 18 production and 13 calibration declarations were printed in the complete
axiom audit. Only propext, Classical.choice and Quot.sound occur; no sorryAx
appears. The three private proof helpers are covered transitively through these
audited public declarations. Forbidden constructs, header markers, dependency
direction, whitespace, source digests, finite diagnostics and parser-safe
artifact checks passed. Exact targets, warning scope and telemetry are retained
in [validation](validation-030.md).

## Next natural frontier and implementation proposal

The remaining useful question is how to bound the accumulated prime weight
over all quotient windows with an error small enough for log(cell)-S-R-H.
Neither reindexing nor a separate crude cap for every interval achieves that.
Removing the extra binomial factors or excluding small-prime composites is
an elementary candidate, but a local parity or fixed wheel filter alone needs
an error analysis before it can be a global provider.

A bounded next experiment should first compare exact odd/wheel-filtered
interval products with the remaining ledger margin, preserving the n=7
composite-only example. If that identifies a useful saving, formalize the
carrier inclusion and a weighted finite sieve estimate whose accumulated
errors are explicit and independent of carry-event membership. If no such
estimate closes the margin, the frontier is short-interval weighted prime
control, elementary or analytic, rather than further cofactor renaming.
No assertion that every elementary route must fail is justified here, and no
subsequent checkpoint architecture is prescribed.

Outcome B - INDEPENDENT FINITE GEOMETRIC BOUND WITHOUT A STRICT BUDGET GAIN
'''
report=report.replace('DECLARATIONS',names).replace('ANCHORS',anchors.rstrip()).replace('METRICS',table.rstrip())
(base/'report-030.md').write_text(report)
validation='''# Validation 030 - Exact scope and final evidence

Commands run from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorWindow DkMathTest.NumberTheory.GnomonCofactorWindowCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorWindowAxiomAudit

METRICS

All exits are zero. GNU time includes Lake and waited descendants. There is no
memory failure and all swap counts are zero. Focused build: 8957 jobs;
Legendre facade: 9133 jobs; root: 10429 jobs; axiom audit: 8958 jobs.
The affected implementation is the new GnomonCofactorWindow module, its new
calibration and axiom audit, and one import in the existing facade. Earlier
production modules were inspected/reused but have no source diff.

Axiom coverage is complete for 18 new production declarations and 13 named
calibrations. The three private production helpers occur only under audited
public proofs. The allowed dependency set is propext, Classical.choice,
Quot.sound. No sorryAx or custom axiom occurs in that checked scope.

Focused and axiom builds emit no warnings. Facade/root replay the existing
PacketCross.lean:285 unused-variable warning. Root also replays existing sorry
warnings in ZsigmondyCyclotomicResearch.lean:147, TriominoFLT.lean:1919,
TriominoCosmicBranchA.lean:4187, GcdNextResearch.lean:850 and
CyclotomicPrincipalization.lean:5389. No repository-wide absence claim is made.

The kernel checks certify the first strict slack n=4, exactness n=3,
all n=3..6 consumer margins, the passing anchor 8, and the first failure n=7 by integer products
and log monotonicity. Independent sieve diagnostics cover n=3..5000 and match
the hashed earlier inventory. Large log values and margins are floating only.

The final artifact check verifies all printed names, standard axiom sets,
forbidden constructs, unified headers, immediate file markers, imports,
git diff --check and untracked Lean whitespace, both source digests,
bounded diagnostic identities, Markdown links and ASCII artifacts. The
root build and diagnostics are evidence only for their recorded scopes.

Evidence: [focused](logs/focused-030.txt), [facade](logs/facade-030.txt),
[root](logs/root-030.txt), [axioms](logs/axiom-audit-030.txt),
[coverage](logs/declaration-coverage-030.json), [diagnostics](logs/diagnostics-030.json),
[artifact audit](logs/artifact-check-030.txt).

Outcome B - independent finite bound; no universal strict budget gain.
'''.replace('METRICS',table.rstrip())
(base/'validation-030.md').write_text(validation)
p=base/'findings-030.md'
s=p.read_text().replace('are to be preserved by kernel-checked','are preserved by kernel-checked')
marker='\n## Final validation\n'
s=s.split(marker)[0]+marker+'''
Focused, facade, root and complete public axiom builds passed with two Lean
threads. Kernel checks fix first strict slack at 4 and first consumer failure
at 7, with all earlier admissible margins checked. All 31 public declarations
have only standard logical axioms and no sorryAx dependencies. Root warnings
are inherited and documented separately. Outcome B: independent geometric
bound, exact ledger bridge, and no universal strict gain.
'''
p.write_text(s)
subprocess.run([sys.executable,str(base/'checks/plain-logs-030.py')],check=True)
with (base/'logs/artifact-check-030.txt').open('w') as out:
    result=subprocess.run([sys.executable,str(base/'checks/check-030.py')],stdout=out,stderr=subprocess.STDOUT)
print((base/'logs/artifact-check-030.txt').read_text(),end='')
raise SystemExit(result.returncode)
