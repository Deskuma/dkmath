# Report 031 - Finite wheel weight and accumulated cofactor error

A genuine independent finite wheel bound is now formalized. It removes the
n=7 composite-only obstruction and recovers the strict consumer there. Its
remaining error is exactly the accumulated logarithmic weight of surviving
composites, capped by the previous geometric slack. The fixed 30-wheel fails
the consumer at n=29, certified in Lean. No universal strict gain or new
unconditional prime-existence range beyond the exact ledger is established.

## Implementation and source reuse

Added [GnomonCofactorSieve](../../../DkMath/NumberTheory/Legendre/GnomonCofactorSieve.lean),
with four definitions and nine theorems, exported through the
[Legendre facade](../../../DkMath/NumberTheory/Legendre.lean).
Direct imports are GnomonCofactorWindow and PrimorialUniverse.WheelSurvivor.
Earlier production modules are reused without edits. The dependency points
from the Legendre application into PrimorialUniverse, not the reverse.
Unified copyright/import headers and immediate file print markers are retained.

[Source inventory](source-inventory-031.md) records the inspected wheel,
reservation, reduced-residue, quotient and Mobius APIs and their exact scopes.
[Findings](findings-031.md) records the chosen route and remaining obstruction.
The existing not_reserved_iff_coprime_finitePrimeBasisProduct theorem is the
thin carrier bridge. Existing period projection and Mobius count identities
are not silently promoted into weighted short-interval estimates.

[Calibration](../../../DkMathTest/NumberTheory/GnomonCofactorSieveCalibration.lean)
contains 13 public kernel checks. The
[axiom audit](../../../DkMathTest/NumberTheory/GnomonCofactorSieveAxiomAudit.lean)
covers all 26 new named public declarations. No speculative sieve hierarchy,
prime-distribution hypothesis, PNT, RH or new custom axiom is introduced.

## Actual filtered carrier

Write base=n^2, width=2*n, top=base+width. For k in Icc(2,n-1), let
A=max(base/k,width), B=top/k, using natural floor quotients. For a finite
prime basis S, let M be its finitePrimeBasisProduct. The carrier is

 T(n,k,S) = Icc(A+1,B).filter(fun q => Nat.Coprime q M).

It uses absolute integers across all wheel periods; it does not require q<M.
The membership bridge says q belongs exactly when A<q<=B and q is not
ReservedByPrimeBasis S. The basis must consist of primes, and each basis
prime must be at most width. Under these hypotheses the prime filter of T
is exactly gnomonCofactorWindowPrimes n k. A desired prime p>width differs
from every basis prime, so no desired prime is removed. This equality is
proved without any prime-distribution assumption or carry-event test.

The cutoff is essential. Kernel calibration at n=3 with S={7} gives an empty
filtered window, while the actual prime window is {7}. This inadmissible
basis removes the desired prime. Reduced residues therefore cannot be used
without checking the basis cutoff and the lifted interval carrier.

## Strongest bound and exact accumulated error

Define V by summing log(q) over all T(n,k,S), and define E by summing log(q)
over their nonprime members. V contains no primality predicate, actual prime
inventory, occupied target set or carry-event membership. E is an exact audit
quantity, not an oracle inserted into the bound. Finite filter partition and
the prime-carrier equality prove

 V = Q + E,                 E >= 0.

Here Q is the exact singleton mass from 030. Its bridge to old large prime
carry is inherited unchanged. Empty and reversed windows contribute zero.
The sum preserves window multiplicity; no unsupported deduplication is used.

The final independent bound combines the existing geometric G with V:

 W = min(G,V),              Q <= W <= G,
 W-Q = min(G-Q,E).

For Q<=W, n>=3 and the admissible basis hypotheses are required. The cap
W<=G itself holds without them. This is the strongest bound proved in this
checkpoint, without a claim of optimality. It is a concrete finite weighted
sieve estimate computable from endpoints and coprimality, rather than just
a reindexing of Q. Computing V exactly is not a general distribution bound
with a small asymptotic error.

## n=7 obstruction and surviving composite mass

For S={2,3,5}, M=30. Kernel checks give the surviving windows at n=7:
k=2 has {29,31}, k=3 has {17,19}, and k=4 is empty. In particular 15 in
(14,15] is deleted. Composite slots 25,27,21 in neighboring windows are also
deleted. The remaining slots are prime, so E=0 and W=Q at this anchor.

The raw sieve product is 290377. The 030 geometric product is 128290919715,
and the residual small/repeated/higher product is 675. Kernel arithmetic gives

 675*290377 = 196004475 < 37387265592825 < 675*128290919715.

Symbolic logarithms therefore prove both W<G and S_small+R+W+H<log(cell).
This repairs the former envelope's failure at 7. The exact old ledger already
passes there; this is recovery of a known finite case, not a new existence range.

Deletion introduces no compensating mass into V. Nevertheless unsieved rough
composites remain elsewhere. Kernel checks certify there are none for n=3..8,
and the first error at n=9 is exactly E=log(49), from k=2. Its old repeated
carry label contributes log(7), not log(49); these weights cannot be canceled
or identified. At n=12 the survivor 77=7*11 is not a prime power at all.
The error is therefore not the earlier repeated-power carry inventory.

## Exact ledger and consumer failure

The inherited identity is oldBudget=H+S_small+R+Q. The new excess theorem is

 S_small+R+W+H = oldBudget+(W-Q).

The prime-existence consumer accepts the explicit strict premise
S_small+R+W+H<log(cell), with n>=3 and an admissible basis. Because W>=Q,
the new envelope remains at least the exact old budget. It can be strictly
stronger than the independent 030 envelope, but cannot improve the exact
ledger merely by replacing Q with an upper bound.

At n=3, W=G, kernel checked; thus strict improvement for every n>=3 is false.
At n=29, the 30-wheel has 36 surviving slots, 25 prime slots and 11 composite
slots. E is about 59.173469, exceeding the available exact-ledger margin
54.147116. The resulting consumer margin is about -5.026353, despite saving
163.046265 relative to G. Both residual*sieveProduct and
residual*geometricProduct exceed cell by exact integer kernel checks;
log monotonicity proves log(cell)<S_small+R+W+H. This refutes a universal
strict consumer for the fixed 30-wheel independently of floating diagnostics.

The 11 composite slots are 427,437,287,289,299,217,221,169,143,121,77,
in windows k=2,3,4,5,6,7,11. Their least factors are all outside {2,3,5}.
A larger wheel can help locally: the 210-wheel's diagnostic margin at 29 is
about 16.4136. This does not establish a universal successful choice of basis.

## Bounded diagnostics and endpoint counterexamples

[Diagnostics](evidence/MANIFEST.md#log-52fe69656210b928) covers all 4998 anchors n=3..5000,
with the 030 source digest recorded and checked. Survivor counts use exact
prefix counts. Weighted sums use compensated floating prefix differences,
with direct gcd/factor reconstruction and fsum checks at 14 retained anchors.
These weights and margins are diagnostics only, never Lean proof premises.
The primary 30-wheel raw bound is below G throughout this finite range;
strict saving is observed at all n=4..5000. No universal version is inferred.

The strict consumer passes numerically at n=3..28,30,33 and fails at the
remaining 4970 anchors. The first diagnostic failure is 29. Its failure is
kernel certified, but minimality among all earlier margins is diagnostic only.
The later passes show there is no monotone failure threshold established.

| n | Q approx | V approx | E approx | G-W approx | Consumer margin approx |
| --- | --- | --- | --- | --- | --- |
| 3 | 1.945910 | 1.945910 | 0.000000 | 0.000000 | 4.962845 |
| 4 | 2.397895 | 2.397895 | 0.000000 | 2.571918 | 8.913147 |
| 5 | 7.796058 | 7.796058 | 0.000000 | 3.101477 | 6.801283 |
| 6 | 8.644883 | 8.644883 | 0.000000 | 6.434456 | 14.935838 |
| 7 | 12.578935 | 12.578935 | 0.000000 | 12.998631 | 12.158703 |
| 8 | 12.524064 | 12.524064 | 0.000000 | 14.739111 | 17.127280 |
| 9 | 24.206136 | 28.097956 | 3.891820 | 11.151215 | 9.590368 |
| 11 | 30.472648 | 30.472648 | 0.000000 | 30.969970 | 19.573839 |
| 12 | 31.174813 | 39.410439 | 8.235626 | 31.642810 | 17.053590 |
| 19 | 68.650057 | 96.313791 | 27.663734 | 75.018791 | 7.996294 |
| 29 | 128.119601 | 187.293070 | 59.173469 | 163.046265 | -5.026353 |
| 297 | 2814.032462 | 6296.584440 | 3482.551978 | 5509.270461 | -2969.959261 |
| 1031 | 11769.172577 | 33700.728319 | 21931.555742 | 29598.679464 | -19711.151466 |
| 5000 | 73428.352340 | 254694.610119 | 181266.257779 | 223090.738731 | -170824.058447 |

Alternative fixed wheels 6,30,210,2310 are tested only where their largest
basis prime is at most width. They help in some small windows but all fail
at the displayed anchors 297,1031,5000. At 5000 the 30-wheel error is about
181266.258; even the 2310-wheel error is about 124977.167. These finite
observations do not rule out every finite sieve or adaptive basis strategy.

Kernel calibration also refutes using whole-period density as a pointwise
upper bound without endpoint correction: the 30-period has eight reduced
residues, but (6,7] contains one survivor, so 8*1<30*1. An exact Mobius
cardinality identity still needs weighted and boundary-error control.

## Validation

The focused, Legendre facade, root and complete public axiom builds passed
with LEAN_NUM_THREADS=2. Focused and axiom builds emit no warnings. Facade/root
replay the existing PacketCross unused-variable warning; root additionally
replays five inherited sorry warnings in unrelated modules. These sources
were not edited. No repository-wide no-sorry claim is made.

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 8.365 | 969160 | 0 | 33992 | 0 |
| facade | 0 | 13.868 | 6745696 | 0 | 197696 | 0 |
| root | 0 | 14.676 | 7110708 | 0 | 208666 | 0 |
| axiom-audit | 0 | 13.946 | 6687756 | 0 | 198883 | 0 |

GNU time measures Lake and waited descendants. Peak RSS is process telemetry,
not a sum of concurrent process memory. There was no build memory failure or
swap. All 13 production and 13 calibration declarations have only standard
logical axioms propext, Classical.choice and Quot.sound, with no sorryAx.
Private calibration helpers are covered transitively through the named checks.
Header, forbidden-construct, whitespace, source-digest, diagnostic-identity,
Markdown-link and ASCII artifact checks passed in their recorded scopes.
Exact evidence is retained in [validation](validation-031.md).

## Next natural frontier and implementation proposal

The missing quantitative estimate is an independent upper bound for V, or
for its accumulated rough-composite excess E, small enough that

 min(G-Q,E) < log(cell)-oldBudget.

Equivalently the consumer needs W<log(cell)-S_small-R-H. The exact error
identity specifies the cofactor coordinates but does not prove this estimate.
Whole-period residue density, interval counts alone, or renaming the exact
prime filter do not supply it. No theorem that every elementary route must
fail has been established; weighted short-interval sieve control is the
remaining frontier of the route actually investigated.

A bounded next implementation should group surviving composites by their
least prime factor, estimate weighted factor-pair counts over A<q<=B, and
retain explicit endpoint errors and window multiplicity. First compare that
error to the available ledger margin at 9,12,29 and the retained large anchors.
Only promote a bound after it is independent of actual prime/carry inventory
and its accumulated error is useful. A complete factor-test basis can
classify the carrier back into primes; that alone gives Q again, not a new
independent quantitative improvement. No architecture for a later checkpoint
or unproved analytic hypothesis is prescribed here.

Outcome B - INDEPENDENT FINITE WHEEL BOUND WITH UNCONTROLLED ACCUMULATED ERROR
