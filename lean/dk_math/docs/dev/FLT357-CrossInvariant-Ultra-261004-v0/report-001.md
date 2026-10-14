# FLT3/5/7 cross-invariant pre-audit — report 001

Date: 2026-10-04. Branch: `research/FLT357-CrossInvariant-Ultra-261004-v0`.
Initial audited HEAD: `69d44fa3e`. Scope: current completed FLT3/FLT5 towers,
current FLT7 corrected carrier, and the bounded prime facade.

## Decision

**Outcome B holds for the extracted algebraic obstruction.** For a fixed
actual order, source element, and ramifier normalization, the residual unit
class modulo p-th powers is independent of the chosen extracted root. A
small test-only Lean lemma verifies this statement and its specializations
to the three actual orders. This is more than a checklist of proof stages.

**Outcome A is not established for the entire FLT proof.** The first genuine
arithmetic split is carrier generation. The later exact coefficient identities
and closed descent states also differ. Those differences are visible before
the incomplete p=7 endpoint; they cannot be removed by renaming packets or
assuming a generic field called `descent`. This audit does not prove the
nonexistence of a stronger common theorem.

The completed p=3/p=5 endpoints remain unconditional for positive naturals.
The p=7 result remains packet-relative algebraic extraction with the
unit/additive-successor frontier open.

## Production matrix

Full theorem-by-theorem maps: [FLT3](flt3-audit-001.md),
[FLT5](flt5-audit-001.md), [FLT7](flt7-audit-001.md),
[generic facade](generic-state-audit-001.md).

| Layer | p=3 | p=5 | p=7 current carrier |
| --- | --- | --- | --- |
| Integer/GN source | Signed difference/sum cubic factors, same primitive source orientation | Signed quintic GN factors; endpoint-square coordinates retained | `Body7=g*GN 7`; later current carrier is generated after real-cubic root extraction |
| Actual order/carrier | Full degree-two `EisensteinInt := TraceOneInt (-1)` | Real quadratic `GoldenInt`, with square-linked quartic GN norm | `SevenCyclotomicDegreeSixInt.Ring`, quadratic over the real cubic order; root-orbit factor |
| Ramified correction | `alpha=(1+tau)*beta`, norm beta=B³, 3 does not divide B | `alpha=(2+phi)*beta`, norm beta=b⁵, tau does not divide beta | Exact raw prime exponent1; `A=lambda*B`, lambda=1-zeta |
| Normalized power | Coprime conjugates plus Euclidean GCD yield beta=epsilon*gamma³ directly | Coprime conjugates plus Euclidean GCD yield beta=epsilon*gamma⁵ directly | All six normalized phase ideals; complete product/coprimality gives `(B)=J⁷`; PID yields B=u*beta⁷ |
| Unit/phase | Three cube representatives; exact coordinates exclude tau and tau² | Five representative coverage; exact coordinates exclude indices1..4 | New degree-six u retained; real-cubic unit log alone does not remove it |
| Integral/additive landing | Exact `r*s*(r+s)=A³`, then signed cube roots and a positive primitive Fermat successor | Exact second-coordinate/quartic relation, square-source inversion, Golden lift | Original source equation retained; no integer/natural successor equation for the new beta |
| Descent measure | Product of a positive primitive Fermat triple | Absolute second coordinate of a Golden zero-sector packet | A smaller twisted real-cubic norm exists; recursive positive Fermat packet not reconstructed |
| Remaining obstruction | None for `fermatThree_no_positive_solution` | None for `flt5Target` | Source-compatible unit/phase elimination, then additive successor and well-founded re-entry |

For p=3/p=5, a normalized principal ideal power is a mathematical consequence
of the stronger element equality. It is not a separately stored ideal-power
step in their completed production proof. The exact collapsing theorems are
`Three.exists_unit_mul_cube_of_coprime_mul_eq_cube` and
`Five.goldenCoprimeFactorOfFifthPower`, backed by the respective norm-Euclidean
GCD structures and `exists_associated_pow_of_mul_eq_pow`.

For p=7, the exact endpoints are
`SevenRealCubic.CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power`
and `currentCarrier_ramified_element_receiver`. They prove `(A)=P7*J⁷` and
`A=lambda*u*beta⁷` under the current packet inputs. The raw complete-support
seventh-divisibility target is false because the P7 exponent is 1.

## Smallest honest shared invariant

Fix an integrally closed domain R, p>0, a nonzero actual element A, and a
nonzero chosen ramifier pi. At the selected production stages all three routes
have the form

```text
A = pi * u * beta^p,     u a unit.
```

The common obstruction is `[u]` in `Rˣ/(Rˣ)^p`, relative to these fixed data.
The checked statement is: if the same A and pi also have a representation
`A=pi*v*gamma^p`, then `u=v*t^p` for a unit t. It follows from
`Associated.pow_iff` in an integrally closed domain, root association and
nonzero cancellation. The proof constructs neither a power root nor an FLT
successor. See [UnitPowerClassAudit.lean](checks/UnitPowerClassAudit.lean).

Before element extraction, a normalized ideal root J has class `[J]` with
`[J]^p=1`. Its principalization is an additional obstruction layer. A global
`classGroupPTorsionFreeAt R p` is sufficient to discharge it; global torsion
freeness is not necessary if this individual J is already principal. The
completed p=3/p=5 and current p=7 stages use their actual Euclidean/PID
arithmetic to discharge that layer.

The ramified load modulo p is a separate local obstruction to an uncorrected
power. Current p=7 formally has load1; the corrected representation is mandatory.
The test lemma checks the once-stripped, fixed-ramifier case shared here;
it does not formalize a global classification for every load or carrier.

Within the fixed order/source/ramifier context, the minimal post-extraction
obstruction coordinate exhibited here is [u]. The layered audit additionally
records the exponent, prime direction/load, and ideal-root class before
principalization; these are not all independent coordinates of one state.
To continue the proof, source orientation and the exact coordinate/additive
identity must be retained. A smaller measure without re-entry into the same
closed state is insufficient.

## Normalization and the generic architecture

There is a concrete reason to keep the ramifier representative. If
`pi'=w*pi` for a unit w, the same corrected expression has residual unit
`u'=w^(-r)*u` at load r. Thus its class is root-independent, but not independent
of ramifier normalization.

The exact checked coordinate identities are

```text
p=3: discrAxis(-1) = tau * (1+tau)
p=5: goldenTraceOneRingEquiv(goldenTau) = tau(1) * discrAxis(1).
```

For the same alpha, switching from the production ramifier to the generic
discriminant axis multiplies the stripped residual by tau-inverse at p=3,
and by phi at p=5. A zero sector in the specialized proof cannot be silently
transferred to the other normalization. See the two normalization lemmas in
[EndpointAudit.lean](checks/EndpointAudit.lean). This computation does not
identify an arbitrary generic coordinate packet with the production packet.

The historical p=3 carrier/API gap is resolved by the current type alignment
and `lib_eisensteinCoord_eq_FLT3_coord`; the latter explicitly preserves the
omega/tau sign convention. GoldenInt and TraceOneInt1 are now related by
`goldenTraceOneRingEquiv`, an actual ring equivalence. These presentation
boundaries are implementation artifacts. Source provenance and normalization
remain necessary mathematical data.

The signed-quadratic p mod4 split is mathematical: it selects imaginary
sign-only units for p>=7, or real quadratic rank1/Fin p representative coverage.
The signed parameter is determined by p and that branch, so it is not another
independent state coordinate. `UnitPowerSectorSystem` proves coverage; its
contract alone gives neither uniqueness nor exact quotient cardinality.

At p=7, the sign-only quadratic order is TraceOneInt(-2), whereas the current
carrier is full degree six. Likewise the checked two-coordinate projective
log is for real-cubic units. Neither statement alone eliminates the new
degree-six u. The original rational-endpoint quotient's unconditional unit
theorem concerns a different source from the new root-orbit quotient.

## Reverse projections and the first split

```text
3: one ramifier -> element cube up to unit -> three representatives
   -> exact coordinate product -> signed positive cube roots
   -> smaller positive primitive Fermat triple, product descent.

5: one ramifier -> element fifth power up to unit -> five representatives
   -> exact second coordinate + square-source inversion
   -> Golden lift T(r,s)=(r²+rs+s²,s²)
   -> smaller Golden zero-sector packet, abs(snd) descent.

7: one ramifier -> all normalized phase ideals are seventh powers -> PID
   -> new degree-six unit class -> additive successor frontier open.
```

The p=3 initial carrier is linear in routed endpoint coordinates. The p=5
carrier is generated from endpoint squares and retains a discriminant-square
constraint. Current p=7 starts from an already extracted real-cubic rho and
uses `rotate(rho)-zeta^j*rho`. These are substantive source-generation
mechanisms, even though they reach a shared extracted algebraic obstruction.
Equal norms cannot bridge them.

The moire/sampling interpretation can describe concrete discrete data:
source orientation, ramified load, quadratic signature, unit-power classes,
real-cubic ZMod7 log coordinates, and local prime directions. Splitting degree
and class-group torsion also have generic arithmetic APIs. This audit proves
no common periodic sampling law or closed state-transition machine; the
metaphor contributes no theorem beyond the checked obstruction invariant.

## Forecast after the 3/5/7 comparison

This table concerns a supplied **ramified quadratic packet** in the current
generic facade, with its genuine QR coordinate provenance.

| Layer | p=11 | p=13 |
| --- | --- | --- |
| Signed quadratic order | `TraceOneInt (-3)`, discriminant -11 | `TraceOneInt 3`, discriminant13 |
| Existing layers | Ramified strip, normalized ideal power, conditional principalization, exact coordinate receiver | Same layers |
| Existing unit datum | Generic sign units / singleton sector | Generic real rank1 / Fin13 coverage |
| First unprovided arithmetic discharge | `classGroupPTorsionFreeAt (TraceOneInt (-3)) 11`, or coprimality of11 with the corresponding class number | `classGroupPTorsionFreeAt (TraceOneInt 3) 13`, or coprimality of13 with the corresponding class number |
| Later obligations | Source-specific additive exclusion and strict descent | Source-specific sector exclusions, additive landing and strict descent |

These are missing discharges in the audited production sources, not a claim
that the class groups actually contain 11/13-torsion. From an **arbitrary**
primitive counterexample, an earlier boundary applies to both: the generic
away branch has no contradiction, and no uniform orientation forces the
ramified packet input.

For the full cyclotomic carrier, the generic canonical factor/ideal norm and
pinned Mathlib unique ramified prime, inertia degree1, ramification index p-1,
and norm of1-zeta APIs already exist. Together with the packet's checked
p-adic ideal-norm valuation1, they predict a mandatory factor associated to
1-zeta at both11 and13. They do not supply a newly checked corrected ideal
power at those exponents.

The first new full-carrier obligation is actual complete nonramified exponent
divisibility and the corrected ideal-power theorem for the chosen source.
Principalization, full-carrier unit arithmetic and additive descent follow
as distinct obligations. Quadratic sectors do not describe full cyclotomic
unit groups. Exact source declarations and historical-route boundaries are
recorded in [generic audit G6](generic-state-audit-001.md#g6--bounded-p11-and-p13-forecast).

## Verification and durable artifacts

Three focused `lake env lean` checks passed: the unit-class lemma and concrete
instances, endpoint/axiom/normalization checks, and recursive compiled
dependency inspection. The dependency audit visits kernel types, available
bodies including opaque bodies, and inductive constructors. Missing constants,
unreadable expected bodies and forbidden dependencies make it fail.

The checked p=3/p=5 endpoints and current p=7 corrected receivers have only
propext, Classical.choice and Quot.sound as axiom leaves. The inspected
closures contain no sorryAx or the explicitly enumerated completed external
FLT3/FLT4 proof families. This is evidence about these declaration closures,
not exclusion of Mathlib modules from the import graph.

Commands, counts and output links are in [validation-summary.md](logs/validation-summary.md).
Continuous checkpoints are in [findings-001.md](findings-001.md).
The work produced documentation and three test-only probes; no production
proof or facade was changed.
