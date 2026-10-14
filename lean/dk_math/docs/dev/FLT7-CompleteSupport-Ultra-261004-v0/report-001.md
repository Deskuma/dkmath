# FLT7 Complete-Support Ultra — Report 001

## Outcome C for the raw target, with a checked normalized global receiver

The literal complete-support seventh-divisibility target for the **raw**
`currentLinearCarrier c` is obstructed: under the current packet inputs, its
ramified prime above 7 occurs with exponent **one**. This prime is in the
complete support and outside both the selected current kernel and its conjugate.
A unit cannot absorb this obstruction.

After extracting exactly one actual ramified uniformizer, complete-support
seventh-divisibility **is proved**. No additional exponent hypothesis is needed.
The complete current global endpoints are:

```text
(A) = P₇ * J^7
A = lambda * u * beta^7,  IsUnit u
```

The original `Fermat7Equation x y z` is retained. The extracted `beta` has not
been converted to a smaller positive Fermat counterexample. Unconditional FLT7
and strict descent were not reached.

## Workspace and recovery artifacts

- Requested branch: `research/FLT7-CompleteSupport-Ultra-261004-v0`.
- Initial HEAD: `cf7df8206`; initial working tree clean.
- Lean/Mathlib: `v4.34.1`; build cwd: `lean/dk_math`.
- The append-oriented recovery artifact is [findings-001.md](findings-001.md).
- Detailed side audits: [drc-bridge-audit-001.md](drc-bridge-audit-001.md) and
  [unit-frontier-audit-001.md](unit-frontier-audit-001.md).
- Focused checks and build output are saved in `logs/`; the reusable normalized
  axiom script is [checks/NormalizedCarrierAxioms.lean](checks/NormalizedCarrierAxioms.lean).

The earlier R64 freeze was used as historical orientation only. DRC-008 and the
live current sources are the audited baseline; this branch continues them.
The DRC-008 raw receiver remains a correct conditional theorem, but this audit
shows that its complete-support hypothesis cannot hold for the current raw
carrier. The new receiver includes the necessary ramified factor explicitly.

## Canonical current carrier

The input stack is unchanged:

```text
CounterexamplePack x y z
PrimitiveCounterexampleRamifiedProvenance source
DirectRealCubicRootPacket source r
DirectOrbitCanonicalCommonFactorPacket p
CurrentCommonPrimeCyclotomicPacket h q
```

All these inputs remain visible parameters of the results. No Fermat
counterexample is constructed or assumed to exist globally.

The ring is the current `SevenCyclotomicDegreeSixInt.Ring`, the explicit
quadratic algebra over `SevenRealCubicInt`. Write

```text
X = ofReal (rotateEquiv p.rho), Y = ofReal p.rho
F_j = X - zeta^j * Y, j=1,...,6
lambda = 1-zeta, P₇ = ker ramifiedEval = (lambda)
```

For the actual current packet, `j = phaseInverseExponent c.phase ∈ {1,4,5}`.
`currentLinearCarrier_eq_phaseCarrier` is a definitional element equality.
No historical signed/oriented carrier is identified with it. Neutral ring,
root-difference, ideal-factorization, and PID theorems are reused on their
actual typed rings.

## Why complementary support occurs

### Ramified exponent one

`directOrbit_gap_axis_pow32_dvd p` supplies real-axis divisibility of the
current gap. The checked ring identity

```text
ofReal eisensteinAxis = zetaInv * lambda^2
```

puts the mapped gap in `P₇²`. Therefore

```text
F_j = ofReal (rotate rho - rho) + (1-zeta^j)*ofReal rho.
```

The geometric sum divides `1-zeta^j` by exactly one `lambda`. Its residue is
`j` in `ZMod 7`, while `thetaResidue rho ≠ 0` is a current root-packet field.
For `7 ∤ j`, the divided element has nonzero residue. Hence `F_j ∈ P₇` and
`F_j ∉ P₇²`. This applies to all six phases, including the three selected phases.

`CurrentSupportObstruction` turns this membership/cutoff into an actual
height-one support witness and exact exponent 1. The witness cannot equal the
selected current kernel, whose exponent is `14e`, or its conjugate, which does
not contain the actual carrier.

The exact raw target is formally negated:

```lean
¬ (∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
  7 ∣ exponent (carrierIdeal c) v)
```

It is not merely a missing theorem or an inability to enumerate primes.
This negation is conditional on the same current packet inputs as the target;
it neither provides a Fermat counterexample nor proves that those inputs exist.

### Every other exponent is controlled

Complementary support can include other primes, but it has no other
seventh-divisibility obstruction. The new
`away_ramified_exponent_seventh_dvd c v` proves `7 ∣ exponent (carrierIdeal c) v`
for **every** height-one prime with `v.asIdeal ≠ P₇`, without requiring a supplied
current residue address or a support-membership hypothesis.

Thus the complete raw exponent classification is:

| Prime | Checked exponent information |
| --- | --- |
| Actual ramified prime `P₇` | Exactly 1 |
| Selected current oriented prime | Existing exact `14e`, `e>0` |
| Every other height-one prime | Divisible by 7, including zero outside support |

## Corrected global aggregation

`CurrentCarrierRamification.phaseCarrierQuotient p j` is an explicit integral
quotient `B_j` with the checked **element** equality `F_j = lambda * B_j`.
It avoids `P₇` for `j=1,...,6`.

`CurrentCarrierPower` completes the following route:

1. The primitive-root polynomial factorization gives the actual product of all
   six `F_j` equal to `ofReal (directOrbitQuotient p)`.
2. Existing current root coprimality `directOrbit_roots_isCoprime p`, mapped by
   `ofReal`, and the cyclotomic root-difference span identity force any common
   prime of two different `F_j` to be `P₇`.
3. The `B_j` avoid `P₇`, so their principal ideals are pairwise coprime.
4. The existing current quotient identity is
   `axis^3 * U * S^14`. Mapping it and cancelling the nonzero `lambda^6`
   from the actual six-factor product gives
   `∏ B_j = (zetaInv^3 * ofReal U) * ofReal(S)^14`, with the unit retained.
5. The full product of normalized principal ideals is
   `(span {ofReal S}^2)^7`. The existing neutral Dedekind coprime-product
   theorem makes **each** normalized ideal a seventh power.
6. Associates count-of-power proves seventh-divisibility on the complete
   normalized support. The existing checked PID receiver converts the ideal
   power into a unit times an element seventh power.

This controls all six factors and all their primes. It uses no selected-prime
coverage assumption, no norm-only element identification, and no discarded
complement. No new class-group hypothesis is needed: the existing degree-six
PID instance supplies principalization.

## New production API

Files under `DkMath/FLT/Seven/`:

- `CurrentCarrierRamifiedObstruction.lean`, namespace
  `SevenRealCubic.CurrentCarrierRamification`: explicit phase carrier/quotient,
  exact division, residue, ramified membership and strict square cutoff.
- `CurrentCarrierNormalizedPower.lean`, namespace
  `SevenRealCubic.CurrentCarrierPower`: six-factor product, common-prime
  classification, normalized pairwise coprimality, full product and individual
  ideal powers, normalized complete-support divisibility, and the corrected
  actual-carrier ideal/element receiver.
- `CurrentSupportObstruction.lean`, namespace
  `SevenRealCubic.CurrentAggregation`: actual ramified support witness,
  exponent 1, placement in the complement, every other exponent a seventh
  multiple, negation of the raw target and raw unit-times-seventh-power form.

Public `DkMath.FLT.Seven` imports the complete new route. Regression modules
are imported by `DkMathTest`.

## DRC-004 through DRC-007 and the prime-below route

| Family | Actual contribution and boundary |
| --- | --- |
| DRC-004 cyclic gluing | Genuine powers in augmentation and `AdjoinRoot Phi_p` reconstruct an AKS cyclic power. Neither inputs nor a carrier equivalence for the new normalized current factor are supplied. No unit elimination follows. |
| DRC-005 Hensel/shell | Root-of-unity and simple-root lifting alone do not force seventh-multiple depth. The test gives degree 7, prime 29, base 1, gap 15 with exact depth 1 and a nontrivial seventh root residue; the existing theorem permits every positive exact depth. This scalar calibration is not a current FLT7 counterexample model. |
| DRC-006 residue classification | Classifies supplied quadratic residues. It can describe a current ratio/inverse fibre but does not generate a degree-one residue address for arbitrary complete support. |
| DRC-007 QR provenance | Explicitly embeds the QR product of three factors at p=7 into the quadratic Gauss subfield and transports norms/ideals. That product is not this single degree-six linear factor of the current real root. No equality or norm-stage bridge identifies them. |

The formal neutral-address regression proves `CurrentMuSevenResidueAddress q`
requires `q ≠ 7`. Ramified support therefore cannot be covered by that address
family. An arbitrary support prime has a rational prime below it through the
existing integral ring-of-integers representation, but its residue field can
have degree greater than one. A seventh-order residue root generally controls
`q^f-1`, whereas an address into `ZMod q` requires degree-one control. This route
has an additional classification obligation; it is bypassed by the checked
full six-factor product route above.

## Remaining unit and descent frontier

The global support question is resolved in its correct ramified formulation.
The remaining receiver keeps `u`. Existing
`DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional`
concerns the original summit quotient `directCyclotomicPhaseQuotient r 1`, not
`phaseCarrierQuotient p j`. There is no checked equality transferring that
packet's unit theorem to the new quotient.

Generic CM unit/relative-norm facts are available, and the current root's
nilpotent real coordinates modulo 7 already vanish. The next **candidate** unit
lemma is to identify the new quotient's unit class while retaining the phase
geometric-sum cyclotomic unit. For example, the stronger formula

```text
phaseCarrier p j = (1-zeta^j) * gamma^7
```

would express such normalization. It was not proved in this checkpoint.
The necessary new-quotient scalar congruence / relative-norm unit criterion
and phase compatibility must be checked rather than inherited from the summit.
See the separate unit-frontier audit for exact existing APIs.

After unit/coordinate landing, genuine descent requires a new positive
primitive `CounterexamplePack x' y' z'`, its actual additive seventh-power
identity, and a strict decrease in the chosen natural measure. The existing
smaller twisted-state norm does not supply that packet. The conjunction with
`Fermat7Equation x y z` in this checkpoint is precisely the original source
identity; it is not a Fermat identity for coordinates extracted from `beta`.

## Validation

- `lake build DkMath.FLT.Seven.CurrentCarrierRamifiedObstruction`: passed,
  9188 jobs (`logs/current-ramified-focused.log`).
- Final normalized module build: passed, 9189 jobs
  (`logs/normalized-focused.log`).
- Final support classification build: passed, 9190 jobs
  (`logs/current-support-focused-final.log`).
- Combined current/DRC regressions and public FLT7/Prime facades: passed,
  9334 jobs (`logs/current-regression-facades-final.log`).
- Full `lake build`: passed, 10350 jobs (`logs/full-build.log`).
- Full `lake build DkMathTest`: passed, 10942 jobs (`logs/full-test-build.log`).
- Every new public production endpoint was printed and checked: 31 theorems
  and 5 definitions (36 total). Dependencies are only `propext`,
  `Classical.choice`, and `Quot.sound`, or subsets thereof.
- The three reused neutral cyclotomic difference-span / ideal-coprimality /
  Dedekind extraction endpoints were audited separately; same standard axioms.
- The six DRC shell/address regression theorems were also audited; same
  standard axioms. Unrelated existing incomplete research declarations in the
  larger import graph do not occur in the new endpoint dependency lists.
- New implementation/test source scans found no forbidden proof constructs.
  Tracked and new-file whitespace checks passed.

Logs remain saved in this directory's `logs/` folder; `.log` files are ignored
by the repository's existing policy. A versionable command/result index is
saved as `logs/validation-summary.md`.

The requested optional checkpoint commit was rejected by automatic approval
review, with the stated reason that the authorized task prohibits commits.
The work and incremental checkpoints remain as files; no commit workaround
was attempted.
