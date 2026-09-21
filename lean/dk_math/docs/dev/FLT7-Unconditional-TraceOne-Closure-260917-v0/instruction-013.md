# FLT7TC-005R8 — Receiver-bypass audit via cyclotomic PID / clean Kummer p=7 specialization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

## Purpose

FLT7TC-005R7 has reduced the TraceOne/ramified route to one precise global receiver:

```text
CubicGapSeventhShapeReceiver
  <-> compensationCore * residualRoot is an integer seventh power
  <-> compensationCore is an integer seventh power
      and residualRoot is an integer seventh power.
```

The generalized routing, canonical split, and conditional inner-root extraction are already available at arbitrary 7-primary depth.  Do **not** add more local valuation layers before checking whether the repository's existing cyclotomic/Kummer infrastructure bypasses this receiver entirely.

The repository already contains two potentially stronger global assets:

1. an explicit proof that the seventh cyclotomic ring of integers is principal, together with a transported PID structure on the concrete degree-six carrier;
2. the generic `DkMath.FLT.Kummer.*` route, including linear-factor ideal arithmetic, principalization, unit normalization, and clean provider-based non-first-case variants.

This checkpoint is an **audit plus the thinnest honest adapters**.  It may close FLT7, expose a weaker global receiver, or prove that both routes return to the same receiver/unit obstruction.

## Absolute safety rule: no hidden `sorryAx`

Before using any nontrivial Kummer theorem in a production proof, inspect its axiom surface.

In particular, do **not** use any theorem whose `#print axioms` contains `sorryAx`.

Explicitly quarantine legacy/default routes depending on things such as:

```text
triominoCosmicNoPowOnGN_default
cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree
```

if their current axiom audit is not clean.

The provider-explicit variants introduced later are eligible only if their own axiom audits are clean and every provider argument is genuinely constructed.  Never manufacture a `TriominoSquarefreeGNBridgeProvider` from the p=7 data.

## 0. Read first

Read at minimum:

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean
DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedRouting.lean
DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedCanonicalReceiver.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedResidualRootClass.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean
DkMath/FLT/Seven/SevenRamifiedFusionElementLevelOrientedPower.lean
DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
DkMath/FLT/Kummer/ClassGroupBridge.lean
DkMath/FLT/Kummer/RegularPrimeRoute.lean
DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProvider.lean
DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean
```

Also read the current reports `report-009.md` through `report-012.md` and the current campaign `ROADMAP.md`.

Historical U1.4/U1.5 element-level packets are useful for comparison, but their input is already downstream of the old receiver.  They must not be imported as a circular proof of the receiver.

## 1. Create a bounded audit module

Suggested production/audit module name:

```text
DkMath/FLT/Seven/PrimeTraceOneCyclotomicPidBypassAudit.lean
```

Keep the module thin.  Prefer adapters and exact boundary theorems over duplicating the large Kummer development.

If no new reusable production theorem is obtained, it is acceptable for the core work to live in an audit module plus report.  Do not promote speculative APIs into the facade.

## 2. Audit the clean generic Kummer p=7 specialization

Specialize only clean, no-`sorryAx` Kummer surfaces to `p = 7`.

Determine exactly which of the following are already constructible from checked repository theorems:

```text
7 is prime / regular as required by the route
class-group 7-torsion is trivial
cyclotomic ring / concrete carrier is principal
linear-factor ideal p-th power extraction
unit normalization
norm-to-GN identity
GN = s^7
final pure-Nat descent receiver
```

### 2a. Class-group/PID adapter

Try to derive the p=7 class-group hypothesis required by the clean Kummer route from the already checked theorem

```text
CyclotomicSeven.classNumber_eq_one
```

or the corresponding principal-ideal-ring theorem.

If the generic target asks only for p-torsion-freeness, prove the **thinnest** adapter from class number one / PID to that target.

Do not re-prove the Minkowski calculation.

### 2b. Unit-normalization audit

Identify whether the clean generic route's unit-normalization target is already concretely inhabited at p=7.

Do not silently substitute the real-cubic `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero` theorem for a degree-six cyclotomic-unit theorem.  The two unit groups may be related, but that relation must be explicitly proved before transport.

If the only missing step is a cyclotomic-unit-class bridge, state that exact type.

### 2c. Squarefree/provider audit

Inspect the clean provider-based non-first-case variants, especially the versions taking

```text
TriominoSquarefreeGNBridgeProvider
```

or a weaker honest provider.

Determine whether current p=7 counterexample data actually construct such a provider.

Important:

```text
GN = s^7
```

does **not** by itself imply squarefreeness and must not be used to fabricate a squarefree provider.

If the clean generic Kummer route stops solely because no provider is inhabited, record that as a genuine boundary; do not fall back to the default theorem if that default inherits `sorryAx`.

## 3. Direct p=7 cyclotomic PID bypass from the original counterexample

Independently of the generic orchestration, try the shortest direct p=7 route from

```text
source : CounterexamplePack x y z
```

using the existing concrete seventh-cyclotomic PID.

The goal is **not** to rebuild all of classical Kummer theory.  Reuse generic linear-factor and ideal lemmas wherever possible.

### 3a. Honest linear-factor surface

Construct or locate an explicit p=7 cyclotomic linear-factor packet associated to the original primitive counterexample, with the correct second-case ramified factor.

Use the already checked one-hot endpoint classification / orientation from FLT7TC-005R4/R5.

A satisfactory packet should retain enough provenance to state which original endpoint is divisible by seven and how the unique ramified cyclotomic prime is loaded.

Do not erase signs/orientation merely to match an existing theorem.

### 3b. Ideal seventh-power extraction

Use the PID/class-number-one result to push the factor ideal as far as honest ideal arithmetic allows.

Preferred shapes include something like

```text
span {linearFactor} = ramifiedLoad * J^7
```

or, if the ramified factor has been normalized away,

```text
span {normalizedLinearFactor} = J^7.
```

Then use existing principal-generator APIs to obtain the strongest valid element equation, for example

```text
linearFactor = loadElement * beta^7
```

with the associated unit absorbed into `loadElement` when justified.

Do not assume the load element or unit is itself a seventh power.

### 3c. Compare with the current TraceOne receiver

From the direct cyclotomic element equation, audit whether one can obtain any of:

```text
CubicGapSeventhShapeReceiver
residualRoot = b^7
compensationCore = c^7
root = innerRoot^7
False
```

without re-importing a packet whose construction already assumes the old receiver.

If an implication is real, kernel-check it.

If not, identify the exact remaining element/unit condition and compare it to the current receiver:

- equivalent to the receiver;
- strictly weaker;
- strictly stronger;
- incomparable with currently checked APIs.

Do not claim equivalence from conceptual similarity alone.

## 4. Explicitly audit the degree-six unit obstruction

The concrete degree-six carrier is a PID, but principalization generally gives an associated unit/load factor.

Determine the thinnest exact unit statement required to convert the direct element equation into a pure seventh power.

Possible shapes to audit include:

```text
∃ u : Ringˣ, linearFactor = u * beta^7

∃ v : Ringˣ, u = v^7
```

or a statement that the non-seventh-power unit part is confined to the distinguished ramified load.

Compare this with the already checked real-cubic unit-class machinery:

```text
unitClassProjectiveLog_bijective
unit_isSeventhPower_iff_projectiveLog_eq_zero
```

but do not transport across the real-cubic / degree-six boundary without a proved map/equivalence and a theorem about its effect on units modulo seventh powers.

If a `mu_7` gauge remains, state it explicitly and verify whether it is harmless for the desired contradiction or whether it recreates the historical U1.5 obstruction.

## 5. Reconcile with the generic Kummer route

At the end of the audit, answer these questions with theorem-level evidence:

1. Does p=7 class number one close the clean generic class-group target?
2. Does the clean generic unit-normalization stage close at p=7?
3. Does the clean generic route still require an uninhabited squarefree/no-lift provider?
4. Does the direct PID route avoid that provider?
5. What is the exact remaining global condition on the direct PID route?
6. Is that condition the same as the current cubic receiver, or genuinely different?

If the direct PID route and the TraceOne route meet at a common receiver, define the **smallest common receiver** only if it improves the public architecture.  Otherwise record the equivalence/implications in the report.

## 6. Do not start a new elliptic-curve formalization here

A classical exponent-seven proof may also be organized through explicit descent on lower-dimensional curves.  That is a legitimate fallback research direction, but this checkpoint is only the cyclotomic/PID bypass audit.

Do not introduce a new elliptic-curve or modular-form development unless an already existing DkMath/Mathlib theorem closes the needed step almost immediately.

## 7. Direct contradiction attempt

If the clean direct PID packet plus existing unit arithmetic genuinely imply contradiction for every

```text
source : CounterexamplePack x y z
```

then prove a theorem of the form

```text
PrimitiveCounterexampleRamifiedProvenance source -> False
```

or directly

```text
CounterexamplePack x y z -> False.
```

Only then may FLT7TC-006 be marked unblocked/completed.

Otherwise stop at the exact global receiver.  A precise boundary is the expected useful outcome.

## 8. Required stop rules

Stop rather than force a theorem if any step would require:

- a theorem with `sorryAx` in its axiom surface;
- `triominoCosmicNoPowOnGN_default` or an equivalent research/default injection;
- inventing `TriominoSquarefreeGNBridgeProvider`;
- assuming `GN = s^7` implies `Squarefree GN`;
- identifying real-cubic and degree-six cyclotomic unit classes without a checked bridge;
- treating an associated unit as a seventh power without proof;
- using `RamifiedSignedRootRoutingPacket` / U1.4 element-level extraction to prove a hypothesis that is already required to construct that packet;
- claiming local mod-49 seventh-power membership gives a global integer seventh root;
- claiming principality alone makes a generator a seventh power;
- `sorry`, `sorryAx`, `admit`, `unsafe`, or a new project `axiom`.

## 9. Outcomes

Report exactly one of:

### Outcome A — CLEAN CYCLOTOMIC PID BYPASS CLOSES THE COUNTEREXAMPLE

A no-`sorryAx`, non-circular p=7 cyclotomic/PID route proves

```text
CounterexamplePack x y z -> False
```

or the equivalent provenance exclusion.  FLT7TC-006 may proceed to public primitive closure.

### Outcome B — CLEAN PID BYPASS REACHES A STRICTLY WEAKER GLOBAL RECEIVER

The direct p=7 route bypasses `CubicGapSeventhShapeReceiver` and isolates a new, strictly weaker global condition whose discharge would close the primitive counterexample.

### Outcome C — CYCLOTOMIC PID AND TRACEONE ROUTES REJOIN AT THE SAME GLOBAL RECEIVER

The clean direct PID route is implemented/audited far enough to prove that its remaining unit/power condition is equivalent (or mutually reducible by checked theorems) to the current cubic receiver.

### Outcome D — CLEAN KUMMER NEEDS AN UNAVAILABLE PROVIDER; DIRECT PID NEEDS A NEW UNIT/LINEAR-FACTOR BRIDGE

No honest bypass is presently available.  Record the exact clean Kummer provider boundary and the exact direct-PID unit/linear-factor boundary.  Do not regress to legacy default/research theorems.

## 10. Validation

Add focused API/axiom audits for every new public theorem.

At minimum run:

```text
lake build DkMath.FLT.Seven
```

plus the focused new modules/tests.

For every Kummer theorem imported into the new route, inspect `#print axioms` either directly or through a dedicated audit file.  The final new target theorem must not inherit `sorryAx`.

Also run:

```text
git diff --check
```

and scan newly added sources for forbidden proof escapes.

## 11. Documentation

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-013.md
```

Update `ROADMAP.md` with FLT7TC-005R8 as an intermediate checkpoint.

Do not mark FLT7TC-006 complete unless an unconditional primitive contradiction is kernel-checked.
