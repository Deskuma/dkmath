# FLT7TC-005R9 — Direct second-case cyclotomic launchpad and μ₇-unit phase frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

## Purpose

FLT7TC-005R8 established an honest Outcome D:

- p=7 cyclotomic PID / class-number-one is available;
- PID extraction alone gives `unit * seventh power`, not a seventh power;
- the existing degree-six element packet starts downstream of the historical signed-routing tower and therefore does not bypass the current TraceOne receiver;
- the clean generic Kummer route still needs an unavailable provider and legacy/default `sorryAx` surfaces are quarantined.

This checkpoint must **not** attempt another receiver normalization.  Instead,
construct the classical p=7 second-case cyclotomic launchpad **directly from the
current counterexample-origin ramified provenance**.

The key observation to kernel-check is that the common ramified summit already
packages an oriented signed difference

```text
endpointLeft^7 - endpointRight^7 = distinguished^7
endpointLeft - endpointRight = 7^6 * gapRoot^7
distinguished = 7 * gapRoot * residualRoot
```

(up to the exact existing field names/equalities).  Hence for the concrete
seventh-cyclotomic factor

```text
η := endpointLeft - ζ * endpointRight
```

one expects the degree-six cyclotomic norm

```text
N(η) = (endpointLeft^7 - endpointRight^7) / (endpointLeft - endpointRight)
     = 7 * residualRoot^7.
```

This is the classical second-case launchpad and does **not** require the
`CubicGapSeventhShapeReceiver`.

## Read first

Read the current checked APIs, especially:

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean
DkMath/FLT/Seven/PrimeTraceOneCyclotomicPidBypassAudit.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedPrimitiveSummit.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicRamifiedPrime.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean
DkMath/FLT/Seven/SevenRealCubicUnitClass.lean
DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
```

Use only clean low-level Kummer lemmas whose axiom audit has no `sorryAx`.
Do not use the quarantined default/legacy norm-descent theorems identified by
`report-013.md`.

## 1. Concrete p=7 local cyclotomic context

If useful, define the smallest adapter

```lean
noncomputable def sevenCyclotomicLocalFactorizationContext :
    CyclotomicLocalFactorizationContext SevenCyclotomicDegreeSixInt.Ring :=
  { p := 7
    zeta := SevenCyclotomicDegreeSixInt.zeta
    hzeta_pow := SevenCyclotomicDegreeSixInt.zeta_pow_seven }
```

or the exact equivalent dictated by the current generic API.

This context is intentionally weak; do not infer primitive-root or ramified
prime facts from `hzeta_pow` alone.  Use the explicit specialized theorems for
those facts.

## 2. Direct linear factor from the current summit

For a `PrimitiveCounterexampleRamifiedProvenance`, define a concrete degree-six
factor using the **same stored summit**:

```text
η = endpointLeft - ζ * endpointRight.
```

Use integer casts through the real-cubic inclusion honestly.  Do not build a
second summit or identify independently chosen packets by proof irrelevance.

Expose a thin packet if useful, retaining at least:

```text
source counterexample / provenance
same summit
linearFactor : SevenCyclotomicDegreeSixInt.Ring
linearFactor_eq
```

and the exact signed endpoint orientation already stored by the provenance.

## 3. Kernel-check the cyclotomic norm identity

Prove the exact concrete norm formula, preferably in two layers:

```text
cyclotomicNormHom (L - ζ*R)
  = (L^7 - R^7) / (L - R)
```

in a division-free form suitable for `ℤ`, followed by the summit
specialization

```text
cyclotomicNormHom η = 7 * residualRoot^7
```

or the exact sign-normalized statement dictated by the concrete norm API.

Do not divide in `ℤ` unless divisibility is already checked.  A product identity
such as

```text
(L - R) * cyclotomicNormHom η = L^7 - R^7
```

is an acceptable first theorem and may be the safer implementation surface.

Audit the sign carefully for the signed Row-Z orientation.

## 4. Direct ideal second-case packet

Main target: determine whether the current provenance is sufficient to prove,
without the TraceOne receiver or historical signed-root routing packet, an
ideal identity of the classical shape

```text
Ideal.span {η} = ramifiedPrime * I^7
```

for some ideal `I` in `SevenCyclotomicDegreeSixInt.Ring`.

Equivalent orientation / association-normalized formulations are acceptable,
for example a distinguished power of the explicit ramified prime if the exact
valuation convention requires it.  The exponent of the ramified prime must be
**proved**, not guessed from the norm formula.

Preferred strategy:

1. use the explicit primitive seventh root and explicit ramified prime
   `span {1 - ζ}`;
2. use the summit endpoint coprimality / seven-unit provenance;
3. establish the exact ramified-prime valuation of `η`;
4. establish that every nonramified prime ideal occurs with multiplicity
   divisible by seven, using the factorization of `L^7-R^7` and conjugate
   linear factors / clean low-level Kummer ideal arithmetic;
5. reconstruct `I` from the prime-ideal exponents if the repository already
   has a suitable Dedekind factorization theorem.

Reusing generic clean lemmas from `CyclotomicPrincipalization.lean` is
encouraged, but do not instantiate a theorem whose proof depends on a
quarantined target/default provider.

### Hard boundary

The norm identity

```text
N(η) = 7 * residualRoot^7
```

**alone does not imply** the principal ideal identity.  Do not promote a
rational norm statement to ideal-exponent ownership without proof.

## 5. PID extraction after the direct ideal packet

If the ideal identity is obtained, use the already checked PID to reach an
exact element equation.  Prefer a packet of the form

```text
η = loadElement * beta^7
span {loadElement} = ramifiedPrime
```

so that the arbitrary associated unit is absorbed into the distinguished
ramified load generator, exactly as in the existing
`exists_mul_pow_of_span_eq_mul_pow` pattern.

Then compare the load generator with the canonical uniformizer

```text
lambda := 1 - zeta.
```

Since both generate the same prime ideal, extract only the honest associated
unit:

```text
loadElement = u * lambda
```

(up to orientation/order), with `u` explicitly retained.

Do **not** assert that `u` is a seventh power.

## 6. μ₇ phase audit — only after the unit is concrete

Once a concrete associated unit `u` is attached to the actual counterexample
linear factor, audit the strongest honest unit-class reduction available.

The desired conceptual normal form is

```text
u = zetaUnit^j * v^7
```

for some `j : ZMod 7` / `Fin 7` and some degree-six unit `v`, or an equivalent
statement saying that the only possible non-seventh-power unit class is the
`mu_7` phase.

This is a **target to prove or reject**, not an allowed assumption.

Useful facts to inspect:

- the degree-six carrier is a CM quadratic extension of the real-cubic order;
- quadratic star fixes `ofReal` and sends `zeta` to `zetaInv`;
- the real-cubic unit-class quotient modulo seventh powers is already fully
  controlled by `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero`;
- the historical U1.5 residual-root packet proves that a genuine `mu_7` gauge
  exists and changes coordinates while preserving the seventh power.

Possible approaches, in increasing cost:

1. prove only a relative-norm statement for the actual associated unit;
2. reduce the free unit class to the real-cubic projective-log class;
3. show that the kernel of the relative norm on unit classes modulo seventh
   powers is generated by `zetaUnit`;
4. only if necessary, prove a full ring-of-integers / unit-group equivalence
   between the explicit degree-six carrier and the abstract seventh
   cyclotomic ring.

Do not undertake (4) merely for aesthetic completeness.

## 7. Phase selection from the ramified linear factor

If a `mu_7`-phase normal form is established, test whether the actual source
linear factor fixes `j` through an explicit congruence at the ramified prime.
This is the p=7 analogue of the classical primary-unit phase normalization.

Work at the smallest modulus that distinguishes the phase; do not assume it is
mod 7.  Candidate surfaces include powers of the explicit uniformizer
`1-zeta` or an equivalent finite quotient.

A useful endpoint would be one of:

```text
j = 0
```

or a unique explicitly determined `j`, together with a normalized exact
formula

```text
η = canonicalRamifiedLoad * gamma^7.
```

A nonzero forced phase is not automatically a contradiction; report exactly
what it implies.

## 8. Comparison with the TraceOne receiver

Only after the direct packet exists, compare it with the current
`CubicGapSeventhShapeReceiver`.

Acceptable conclusions:

- direct cyclotomic phase normalization implies the current receiver;
- the current receiver implies trivial cyclotomic phase;
- both are consequences of a smaller common unit-class condition;
- they are genuinely distinct with no checked bridge.

Do not claim equivalence from analogy.

## 9. Public/API discipline

Prefer a new focused module, for example:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicSecondCase.lean
```

If the checkpoint stops at an audit boundary, use an `...Audit.lean` name and
do not export speculative definitions through `DkMath.FLT.Seven`.

Add focused API and axiom audits only for stable proved surfaces.

## 10. Report

Create `report-014.md` and answer explicitly:

1. Is the direct norm identity `N(η)=7*residualRoot^7` kernel-checked?
2. Is `span {η} = ramifiedPrime * I^7` kernel-checked directly from current
   counterexample provenance?
3. If yes, what exact element equation does PID give?
4. What is the remaining associated unit/load ambiguity?
5. Can it be reduced to a pure `mu_7` phase?
6. Can the phase be selected by a ramified congruence?
7. Does any proved condition imply or equal the TraceOne cubic receiver?
8. Did any theorem used by the new route depend on `sorryAx`?  This must be
   answered by axiom audit, not source-text inspection alone.

Update the campaign `ROADMAP.md` with the exact new frontier.

## 11. Required validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCase
# or the exact chosen audit module
lake build DkMath.FLT.Seven
lake build <new API audit>
lake build <new axiom audit>
git diff --check
```

Scan new production/audit sources for:

```text
sorry
admit
unsafe
axiom
```

and separately `#print axioms` all decisive theorems, including any imported
Kummer theorem used in the route.  `sorryAx` contamination is a hard failure.

## 12. Outcome labels

Use exactly one of:

### Outcome A — DIRECT SECOND-CASE CYCLOTOMIC PACKET GREEN; μ₇ PHASE NORMALIZED

Current counterexample provenance directly gives the cyclotomic ideal/element
packet, the associated unit is reduced to the `mu_7` phase, and the actual
ramified congruence fixes that phase.  State separately whether this closes the
TraceOne receiver or yields a contradiction; do not bundle an unproved final
step into Outcome A.

### Outcome B — DIRECT SECOND-CASE CYCLOTOMIC PACKET GREEN; μ₇ PHASE IS THE PRECISE FRONTIER

The norm, ideal second-case packet, and PID element equation are direct and
clean, but the associated unit class cannot yet be reduced/selected beyond an
explicit `mu_7` or unit-class receiver.

### Outcome C — DIRECT NORM GREEN; IDEAL RAMIFIED-LOAD OWNERSHIP IS THE PRECISE FRONTIER

The current provenance gives the exact norm identity, but the checked library
does not yet prove `span {η} = ramifiedPrime * I^7` without importing the old
downstream routing or a quarantined generic theorem.

### Outcome D — DIRECT LINEAR-FACTOR ADAPTER ITSELF NEEDS A NEW BRIDGE

Even the source/signed-orientation to concrete p=7 cyclotomic factor cannot be
made honest with current APIs.  Record the smallest missing bridge and stop.

## 13. Hard stop rules

Do not:

- assume every degree-six unit is a seventh power (`zetaUnit` already rules
  this out as a naive global statement);
- infer ideal seventh-power factorization from the integer norm alone;
- infer a squarefree/no-lift GN provider from `GN = s^7`;
- use any theorem whose axiom audit contains `sorryAx`;
- enter the historical `RamifiedSignedRootRoutingPacket` merely to recover an
  element packet and then call it a bypass;
- assume the `mu_7` gauge is harmless for additive coordinates;
- claim FLT7TC-006 or unconditional FLT7 unless an actual contradiction is
  kernel-checked.
