# Generic state audit — FLT357 pre-audit

2026-10-04. Scope: current `DkMath.FLT.Prime` and the neutral ideal/unit/
coordinate interfaces. This is a source audit, with no new production theorem.

## G0 — Current generic spine and its input boundary

`DkMath/FLT/Prime.lean` is an import-only facade. Its comment explicitly says
that the ramified branch enters `PrimeAdicFactorPacket`, while the away branch
stops at a simultaneous power split. It does not supply a general FLT theorem.

Source `DkMath/FLT/Prime/CounterexampleRouting.lean`:

- `PrimitivePrimeCounterexample.gap_mul_GTail_eq` retains the original
  equation through `(z-y) * GTail p 1 (z-y) y = x^p`.
- `primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap` needs
  `hgap : p ∣ z-y`.
- `away_branch_power_factor_split` needs `¬ p ∣ z-y` and produces both
  `(z-y)=a^p` and `GTail=b^p`. It proves neither a contradiction nor a
  coordinate permutation into the ramified branch.
- `counterexampleRoute_of_primitive` exposes these alternatives as
  `PrimeCounterexampleRoute`; the branch choice is not hidden.

Source `DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean`:

- `nonempty_primeTraceOneStrippedIdealPacket P0 P` requires a supplied
  `PrimeAdicFactorPacket p g u x`, a genuine
  `PrimeTraceOneCoordinatePacket L p ζ hζ`, and the cyclotomic field/root
  instances. It gives `parent = P.coord (g+u) u`,
  `parent = discrAxis (signedPrimeParameter p) * residual`, terminal axis,
  coprime residual coordinates/conjugate ideals, nonzero `idealRoot`, and
  `(residual) = idealRoot^p`.
- The ideal-power proof uses
  `ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal`,
  `span_mul_span_conj_eq_pow_of_norm_eq_pow`, and neutral
  `DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow`.
  It does not assume PID or class-group triviality at this stage.

The generic ramified axis is `discrAxis s = <-1,2>` in the quadratic order.
Its square is the signed discriminant. This is not a silent identification
with the full cyclotomic `1-ζ` or the current degree-six FLT7 `lambda`.

The older `PrimeCyclotomicTraceOne.lean` facade transports only the scalar
norm. The later actual provenance lift in
`DkMath/NumberTheory/CyclotomicQRProvenanceLift.lean` is stronger:
`gaussEmbedding`, `gaussSubfieldEquiv`, `coord_image_eq_qr`,
`conj_coord_image_eq_qnr`, `subfield_coord_relative_norm`, and
`map_coordinate_ideal` give checked element/subfield/ideal maps for the
QR/QNR coordinates. `integralEmbedding_discrAxis` identifies the chosen axis
image with `quadraticGauss ζ hζ`, including its sign. These genuine maps do
not identify a QR product with a single full cyclotomic linear factor, or
with the current FLT7 phase-corrected degree-six carrier.

## G1 — Principalization, unit class, and coordinate landing stay separate

`DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt R p` is exactly
`∀ a : ClassGroup R, a^p=1 → a=1` (`IdealPowerFactor.lean`).

`exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` in
`PrincipalIdealPower.lean` assumes a Dedekind domain, nonzero ideal root,
that explicit torsion condition, and `(a)=I^p`; it returns
`a=u*gamma^p`, `IsUnit u`, and `(gamma)=I`. No unit is removed there.

`UnitPowerSectorSystem R p` (`UnitPowerSector.lean`) provides a type
`Sector`, unit representatives, and the completeness condition
`∀ u, ∃ s e, u=rep s * e^p`. There is no uniqueness, finiteness, or
minimal-cardinality field. Calling a supplied `Fin p` sector system an exact
quotient cardinality would exceed this API without a separate theorem.

`exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` needs the separate
unit-power-surjectivity hypothesis. The sector receiver instead retains
`rep s * delta^p`.

`traceOne_pow_core_landing_iff` (`TraceOnePowerLanding.lean`) is an exact
integer-coordinate criterion, under `norm beta ≠ 0`, for
`∃ gamma, alpha=beta*gamma^r`. It is not a power-root provider or a strict
descent theorem. Current facade coordinate receivers apply it to the
already-produced element/sector equalities.

## G2 — What the quadratic prime sectors actually say

The normalization is in
`DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean`:

```text
D_p = if p % 4 = 1 then p else -p
s_p = (D_p - 1) / 4
discr(s_p) = D_p                      [p prime, p ≠ 2]
```

Thus `signedPrimeParameter` is determined by the prime and its mod-four
branch, not an additional independent coordinate.

`TraceOnePrimeUnitSectors.lean` proves:

- For `hp : p.Prime`, `hp7 : 7 ≤ p`, `hmod : p%4=3`,
  `traceOnePrimeImaginary_unit_eq_one_or_neg_one` says every unit of
  `TraceOneInt s_p` is a sign. Since p is odd, the power map on these units is
  surjective; `traceOnePrimeImaginarySingletonSectorSystem` has `PUnit`
  sectors. This is a mathematical property of this **quadratic** carrier.
- For `hp : p.Prime`, `hmod : p%4=1`,
  `traceOnePrimeReal_signature` gives degree 2, zero complex places, two real
  places, and unit rank 1. `traceOnePrimeRealFinSectorSystem` gives `Fin p`
  representatives obtained from a Dirichlet fundamental unit and proves
  completeness. No nonzero sector is eliminated by that theorem.
- The module's opening prose still says that real-sector construction is
  not asserted until a signature bridge exists, but the same current file
  now implements the signature and real sector system. The declarations,
  not that stale opening prose, control this audit.

The mod-four split therefore has actual signature/unit evidence, but only
for the identified signed-prime quadratic order. It does not describe every
full cyclotomic or real-subfield carrier in FLT3/5/7.

## G3 — Current p=3/5/7 facade instances

| p | Current quadratic carrier | Principalization evidence | Unit endpoint |
|---|---|---|---|
| 3 | `TraceOneInt (-1)`; `EisensteinInt` is an abbrev | `classGroupPTorsionFreeAt_traceOneNegOne_three` via PID | `exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three`; explicit `EisensteinUnitSector` |
| 5 | `TraceOneInt 1`, equivalent as a ring to `GoldenInt` | `classGroupPTorsionFreeAt_traceOneOne_five`, transported Golden Euclidean/PID | `exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five`; explicit `Fin 5` representatives |
| 7 | `TraceOneInt (-2)` | `classGroupPTorsionFreeAt_traceOneNegTwo_seven` via Euclidean/PID | `exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven`; exact residual seventh power |

The p=3 carrier/API boundary in
`docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md` is historical:
`traceOneInt_signedPrimeParameter_three_type` and
`lib_eisensteinCoord_eq_FLT3_coord` in `FLT/Three/EisensteinLibBridge.lean`
now record the actual type alignment and omega/tau sign convention. The
former needs no fabricated ring equivalence.

At p=5, `goldenTraceOneRingEquiv` in `FLT/Five/TraceOneBridge.lean` is an
actual coordinate-preserving ring equivalence. It preserves multiplication,
conjugation, powers, and norm; this boundary was an implementation artifact,
not evidence of inequivalent rings. The remaining packet-to-specialized
Golden arithmetic/sector-elimination boundary is separate.

At p=7 the current new full-support endpoint lives in
`SevenCyclotomicDegreeSixInt.Ring`. Nothing above transports its unit `u`
to the sign-only unit group of `TraceOneInt (-2)`. Equal absolute norms do
not give that transport. In particular, the generic quadratic exact seventh
power does not remove the degree-six receiver's unit/additive frontier.

## G4 — Candidate state ledger, not a fabricated common theorem

The source-supported **audit ledger** includes:

1. The actual carrier/order together with coordinate conventions and checked
   element maps; record whether a claim is an equality, a relative norm, or
   only a scalar norm.
2. The distinguished factor and original additive equation, plus the explicit
   ramified/away branch condition.
3. Ramified valuation data and the chosen correction; retain orientations
   when a carrier has conjugate/Galois prime directions.
4. The actual ideal-root principalization class, or a checked PID discharge.
   `p`-torsion freeness is sufficient to principalize the root; it is not a
   necessary condition on all classes if this individual root is already
   principal.
5. The unit class modulo p-th powers in that carrier. A representative type
   supplied by `UnitPowerSectorSystem` is checked coverage, not automatically
   a canonical quotient.
6. The coordinate/additive landing obligation and a checked positive smaller
   successor or contradiction. Recording a field called `descent` would not
   prove it.

The prime's mod-four/sign parameter can select the quadratic unit system,
but is redundant with the signed discriminant once the carrier is fixed.
Residue degree and splitting/orientation are mathematical local data, though
not an additional universal coordinate in the generic quadratic packet
alone. The historical p=3 type adapter and p=5 ring adapter are resolved
implementation boundaries; p=3 exceptional units and real/imaginary unit
rank remain mathematical distinctions.

This ledger organizes evidence; its fields are not claimed to be independent
coordinates of a minimal state. In particular, PID makes the root's
class-group coordinate trivial for the concrete 3/5/7 extraction steps.
It is not itself a proved invariant/state-transition theorem for all
completed production routes. The genuine shared invariant is checked next.

## G5 — Verified shared algebraic invariant: limited Outcome B

After the production 3/5 maps were saved and the current 7 endpoint was
fixed, a stronger candidate than the ledger is available. Fix the actual
order R, exponent p, nonzero selected element alpha, and ramified correction
pi^r. The checked endpoints have the form

```text
alpha = pi^r * u * beta^p.
```

For the nonzero corrected element, the unit class modulo p-th powers is
now kernel-checked to be independent of the chosen root beta. The
test-only proof is stronger than the initial UFD/PID forecast:

```lean
FLT357CrossInvariantAudit.unitPowerClass_independent
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  (hn : n ≠ 0) (halpha : alpha ≠ 0)
  (hu : IsUnit u) (hv : IsUnit v)
  (hleft : alpha = u * beta^n)
  (hright : alpha = v * gamma^n) :
  ∃ t : R, IsUnit t ∧ u = v * t^n
```

`fixedRamifier_unitPowerClass_independent` proves the same statement from
`A=lambda*(u*beta^n)=lambda*(v*gamma^n)`, retaining the nonzero raw element
and fixed nonzero ramifier hypotheses. Taking `lambda=pi^r` gives the
displayed form. `Associated.pow_iff hn` in an integrally closed domain
supplies association of the roots; cancellation supplies the exact unit
ratio. No production proof-root provider, unit-sector elimination, or
desired FLT conclusion is assumed.

Both proofs and concrete carrier instantiations at 3, 5, and 7 are in
[UnitPowerClassAudit.lean](checks/UnitPowerClassAudit.lean); the parent
reports successful execution (exit 0), and
[unit-power-class.log](logs/unit-power-class.log) records only `propext`,
`Classical.choice`, and `Quot.sound` for their axioms. This establishes the
choice-independent unit-class relation, without adding a canonical finite
quotient/cardinality theorem.

The residue of the ramified multiplicity modulo p is a further algebraic
obstruction before correction; the current raw degree-six FLT7 multiplicity
is 1, so its uncorrected element cannot be unit times a seventh power.

This invariant must fix the ramifier representative. If `pi'=eta*pi` for
a unit eta, the corresponding residual class changes by `[eta]^-r`:
`u'=eta^-r*u`. Thus it is not an independent choice-free scalar without
that normalization. The algebraic unit class also depends on the actual
carrier. It cannot be transported from the quadratic p=7 suborder to the
degree-six carrier without an actual element map and applicable hypotheses.

This is visible in concrete current source, not only a hypothetical issue:

```text
p=3: discrAxis(-1) = tau * (1+tau)
p=5: goldenTau = goldenPhi * goldenSqrtFive
     goldenTraceOneRingEquiv(goldenSqrtFive) = discrAxis(1)
```

The p=3 identity is now kernel-checked as
`FLT357CrossInvariantAudit.three_ramifier_normalization`, and the p=5
identity as `five_ramifier_normalization`, in
[EndpointAudit.lean](checks/EndpointAudit.lean). The latter checks the
stronger exact image
`goldenTraceOneRingEquiv goldenTau = tau 1 * discrAxis 1`.
[endpoint-audit.log](logs/endpoint-audit.log) records their standard axioms
after the parent's successful execution (exit 0). Thus for the **same** alpha, the p=3 generic
axis-stripped residual differs from the production ramifier-stripped
residual by `tau^-1`, and the p=5 one differs by `phi`. The production
proof's zero unit class is relative to its chosen ramifier. It cannot be
silently asserted for the generic discriminant-axis normalization.

This calculation does not itself identify `P.coord` with a production
source packet. Such an identification still needs the actual coordinate/
orientation map. It shows exactly which unit twist must be retained if
that same-element comparison is made.

The successful neutral independence proof supports **Outcome B for the
shared algebraic obstruction layer**. The smallest checked invariant after
extraction is the residual unit class, with `(R,p,alpha,pi^r)` as fixed
context. The raw valuation residue and the chosen correction tell which
extracted state applies. The original source orientation/coordinate map
must accompany it when comparing the production routes. The class-group
root coordinate is already trivial in the concrete PID cases; it becomes
an additional principalization obligation in the generic forecast.

The completed routes use different exact coordinate identities to force
the permitted unit class for their production normalization and return to
their respective descent invariants.
This does not assert one shared additive-descent theorem: p=3 reconstructs
a smaller positive primitive Fermat triple, while p=5 descends on a Golden
packet's second-coordinate absolute value, and the current p=7 receiver
has not supplied either successor.

## G6 — Bounded p=11 and p=13 forecast

This forecast was recorded only after the production 3/5 maps and current
7 endpoint were stable. It is about the audited existing generic route,
not an FLT11/13 implementation or a claim that the same specialized
coordinate descent works for higher primes.

| Layer | p=11 | p=13 |
|---|---|---|
| Quadratic parameter | `11%4=3`, `D=-11`, `s=-3` | `13%4=1`, `D=13`, `s=3` |
| Existing carrier arithmetic | `TraceOneInt (-3)`, rational quadratic field, maximal-order/Dedekind theorem, QR/QNR coordinate realization and actual Gauss embedding | `TraceOneInt 3`, same generic arithmetic and provenance interfaces |
| Existing ramified correction, given a prime-adic packet | One `discrAxis (-3)` is extracted; its terminal residual has ideal `idealRoot^11` | One `discrAxis 3` is extracted; its terminal residual has ideal `idealRoot^13` |
| Unit datum already available | Generic imaginary unit theorem says units are signs, so singleton 11-power sectors | Generic real signature gives rank 1 and `Fin 13` Dirichlet representatives; all sectors retained |
| First packet-relative missing discharge | `classGroupPTorsionFreeAt (TraceOneInt (-3)) 11`, sufficient via `Nat.Coprime 11 (NumberField.classNumber (TraceOneRat (-3)))` | `classGroupPTorsionFreeAt (TraceOneInt 3) 13`, sufficient via `Nat.Coprime 13 (NumberField.classNumber (TraceOneRat 3))` |
| After principalization | Exact residual eleventh power and recurrence coordinates are already generic; no specialized additive exclusion/strict successor theorem is supplied | Sector-times-thirteenth-power coordinates are already generic; packet-specific nonzero-sector exclusion and subsequent additive landing/descent are not supplied |

The class-number bridge is actual production source
`DkMath/NumberTheory/PrimeTraceOneClassNumber.lean`:

- `traceOne_classGroup_card_eq_classNumber` transports through the checked
  ring-of-integers equivalence and `ClassGroup.mulEquiv`.
- `classGroupPTorsionFreeAt_primeTraceOne_of_coprime_classNumber` assumes,
  rather than proves, the displayed arithmetic coprimality.
- The current generic facade has p=3/5/7 PID discharges; the scoped source
  search found no corresponding `TraceOneInt (-3)`/`TraceOneInt 3`
  Euclidean/PID or class-group 11/13-torsion discharge theorem.

Existing `PrimeTraceOneConditionalDescentProbe.lean` instantiates the 11 and
13 conditional routes, but its examples conclude `True` after obtaining
the endpoint under `hfree`. These are elaboration/composition probes,
not proofs that `hfree` holds or that no counterexample exists.

From an **arbitrary primitive counterexample**, an earlier obligation is
already visible: `PrimeCounterexampleRoute.away` has no contradiction and
the facade proves no uniform orientation/permutation making `p ∣ z-y`.
The class-group entries in the table are the first missing arithmetic
discharges *after a ramified PrimeAdicFactorPacket has been supplied*.

### Full cyclotomic forecast and the mandatory factor

The canonical full cyclotomic carrier
`CFBRC.cyclotomicLinearFactorInRingOfIntegers hζ g u` is
`(g+u)-ζ*u`, in `𝓞 K` for `K=ℚ(ζ_p)`. Its norm/ideal-norm interface is
already generic. `PrimeAdicFactorPacket.padicValNat_cyclotomicIdeal_absNorm_eq_one`
gives rational p-adic valuation 1, not a complete prime-ideal factorization.

The pinned Mathlib has genuine generic ramification support in
`NumberTheory/NumberField/Cyclotomic/Ideal.lean`:

```text
IsCyclotomicExtension.Rat.ncard_primesOver_of_prime
IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
IsCyclotomicExtension.Rat.inertiaDeg_span_zeta_sub_one'       = 1
IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one'   = p-1
IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime
```

`IsPrimitiveRoot.zeta_sub_one_prime'` and
`norm_toInteger_sub_one_of_prime_ne_two'` in the companion `Basic.lean`
fix the prime element and its norm. Thus a degree-one ramified prime above
p with exponent 1 is a source-grounded prediction for the canonical
packet carrier at both 11 and 13. Its stripped normalization should retain
one factor associated to `1-ζ_p`; an uncorrected p-th ideal power would
conflict with the checked rational norm valuation. This is a prediction
from the audited APIs, not a newly compiled equality `(A)=P_p*J^p`.

The full-carrier first new implementation obligation is an actual
carrier-specific corrected ideal-power theorem with complete prime-ideal
ownership/nonramified exponent divisibility. The neutral
`FiniteIdealPowerAggregation.eq_powerRoot_pow` can aggregate supplied
exponents; it cannot prove their divisibility. Full-carrier root
principalization, unit sectors, and additive landing then require their
own arithmetic. Quadratic sign units at 11 and quadratic `Fin 13`
representatives are not the full cyclotomic unit groups.

The pinned `NumberTheory/NumberField/Cyclotomic/PID.lean` actually implements
`three_pid` and `five_pid`; its prose mentioning results through 19 does not
provide p=11/13 PID declarations. The older DkMath
`FLT/Kummer/CyclotomicPrincipalization.lean` contains conditional receivers
such as `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin`
with explicit first-case, nonzero/product and torsion-kill premises, plus
a `sorry` at line 5409. No theorem from that file is used as unconditional
forecast evidence here; no dependency audit of that historical route was
performed in this generic sub-audit.

## G7 — Validation performed by this sub-audit

This sub-audit read the current declarations and historical summaries and
searched production/tests plus the pinned Mathlib ramification/PID APIs.
It made only this Markdown record. No production edit, scratch proof,
build, or commit was performed by this sub-audit. It subsequently inspected
the parent's two successful test-only probes and their saved logs, and
updated G5 with the verified unit-class independence and exact ramifier
normalizations. The parent coordinates focused axiom/kernel verification
and the repository checkpoint commit.
