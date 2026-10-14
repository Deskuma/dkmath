# NGEO-012 — Seven / fourteen-phase calibration

Branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-011.md
lean/dk_math/DkMath/NumberGeometry/Phase/TwoPrime.lean
lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean
lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean
lean/dk_math/DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixDomain.lean
~~~

NGEO-011 established a general primitive signed 2*p phase:

~~~text
eta^(2*p) = 1
eta^p     = -1

evenPhase j = eta^(2*j)
oddPhase  j = eta^(2*j+1)

even^p = 1
odd^p  = -1
~~~

and proved finite even/odd sector injectivity and disjointness.

NGEO-012 specializes this algebra to p = 7 and performs a bounded calibration
against the existing DkMath seventh-cyclotomic degree-six carrier and CF2D
fourteen-step phase.

This checkpoint is a calibration/bridge checkpoint only. It must not prove or
modify an FLT7 theorem.

## Architectural rule

Do NOT make the public NumberGeometry facade depend on DkMath.FLT.Seven modules.

Use two ownership directions:

1. Pure p=7 specialization remains under NumberGeometry and has no FLT import.
2. The exact bridge to the existing seventh-cyclotomic carrier is owned on the
   FLT/Seven side, or in a non-facade bridge module whose dependency direction
   is explicitly documented.

Preferred split:

~~~text
DkMath/NumberGeometry/Phase/SevenTreasure.lean
DkMath/FLT/Seven/NumberGeometryFourteenPhaseBridge.lean
~~~

The first may be exported from DkMath.NumberGeometry.

The second must NOT be imported by DkMath/NumberGeometry.lean.

Adding the second bridge to DkMath/FLT/Seven.lean is optional; do so only if it
matches current facade ownership and does not create a cycle.

## Objective

Formalize the exact p=7 specialization:

~~~text
14 = 7 + 7

eta^14 = 1
eta^7  = -1

7 even phases: eta^(2*j)
7 odd phases:  eta^(2*j+1)
~~~

with finite sector cardinalities and signed seventh-power equations.

Then connect the generic squared generator

~~~text
zeta = eta^2
~~~

to the existing explicit seventh-cyclotomic generator
SevenCyclotomicDegreeSixInt.zeta.

The strongest desired exact bridge is:

~~~text
eta14 := -(zeta^4)
eta14^2 = zeta
eta14^7 = -1
eta14^14 = 1
~~~

and, if Mathlib makes the order proof compact:

~~~text
IsPrimitiveRoot eta14 14
~~~

so that the existing seventh-cyclotomic carrier itself realizes the general
TwoPrimePhase packet for p=7.

## 1. Pure FourteenPhase specialization

Create:

~~~text
lean/dk_math/DkMath/NumberGeometry/Phase/SevenTreasure.lean
~~~

Define a standard mathematical alias/name, preferably:

~~~lean
abbrev FourteenPhase
    (R : Type*) [CommRing R] [NoZeroDivisors R] :=
  TwoPrimePhase R 7
~~~

The public mathematical API should prefer FourteenPhase. “Seven Treasure” may
remain the checkpoint/documentation nickname.

Do not duplicate TwoPrimePhase fields.

## 2. Canonical complex fourteen phase

Define:

~~~lean
noncomputable def complexFourteenPhase : FourteenPhase ℂ :=
  complexTwoPrimePhase 7 (by norm_num)
~~~

Expose thin calibration theorems:

~~~text
complexFourteenPhase.eta^14 = 1
complexFourteenPhase.eta^7  = -1
~~~

Reuse generic fullTurn/halfTurn.

Do not re-prove complex exponential identities.

## 3. Seven even and seven odd sectors

Build finite sector sets from the existing Fin 7 phase functions.

Preferred definitions:

~~~lean
def FourteenPhase.evenSector (P : FourteenPhase R) : Finset R :=
  Finset.univ.image P.evenPhaseFin

def FourteenPhase.oddSector (P : FourteenPhase R) : Finset R :=
  Finset.univ.image P.oddPhaseFin
~~~

Use classical locally if required.

Prove:

~~~text
evenSector.card = 7
oddSector.card  = 7
Disjoint evenSector oddSector
~~~

using the NGEO-011 injectivity/disjointness theorems.

Then define or expose:

~~~lean
def FourteenPhase.sector (P : FourteenPhase R) : Finset R :=
  P.evenSector ∪ P.oddSector
~~~

and prove:

~~~text
sector.card = 14
~~~

This is the exact formal content of 14 = 7 even phases + 7 odd phases.

Do not rely on informal counting.

## 4. Signed seventh-power equations

Specialize the generic equations:

~~~lean
theorem FourteenPhase.even_seventh_equation
    (P : FourteenPhase R) (j : ℕ) (Y : R) :
    (P.evenPhase j * Y)^7 - Y^7 = 0

theorem FourteenPhase.odd_seventh_equation
    (P : FourteenPhase R) (j : ℕ) (Y : R) :
    (P.oddPhase j * Y)^7 + Y^7 = 0
~~~

These should be thin wrappers around the generic signed equations.

Do not claim converse classification of all solutions.

## 5. Squared generator specialization

Expose the p=7 generator facts:

~~~text
zeta(P) = eta(P)^2
zeta(P)^7 = 1
IsPrimitiveRoot zeta(P) 7
~~~

Reuse the generic API.

A theorem such as this is desirable:

~~~lean
theorem FourteenPhase.zeta_isPrimitiveRoot_seven
    (P : FourteenPhase R) :
    IsPrimitiveRoot P.zeta 7
~~~

Do not add a second zeta definition.

## 6. CF2D fourteen-step calibration

The existing owner theorem gives exact order for regularKernel 14.

Add a thin calibration theorem, in test code or a small non-FLT bridge if clean:

~~~lean
theorem regularKernel_fourteen_exactOrder :
    orderOf (regularKernel 14) = 14
~~~

This must be a direct specialization of orderOf_regularKernel.

If small, also expose:

~~~text
regularKernel 14 ^ 14 = 1
~~~

Do not duplicate CycleDivision proofs.

A direct identification between CF2D regularKernel 14 and the canonical complex
eta is not required in NGEO-012.

Record that identification as DEFERRED unless an existing theorem makes it
trivial.

## 7. Existing seventh-cyclotomic carrier audit

Reuse the exact current facts:

~~~text
SevenCyclotomicDegreeSixInt.zeta_pow_seven
SevenCyclotomicDegreeSixInt.zeta_ne_one
SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot
SevenCyclotomicDegreeSixInt.ringIsDomain
~~~

Do not re-prove the degree-six ring construction or primitive seventh-root
theory.

## 8. Construct the fourteen-phase lift inside the existing carrier

In the FLT/Seven-owned bridge module, define:

~~~lean
def eta14 : SevenCyclotomicDegreeSixInt.Ring :=
  -(SevenCyclotomicDegreeSixInt.zeta ^ 4)
~~~

The exponent 4 is structural because 2*4 = 8 is congruent to 1 modulo 7.

Required exact target:

~~~lean
theorem eta14_sq :
    eta14 ^ 2 = SevenCyclotomicDegreeSixInt.zeta
~~~

Use zeta_pow_seven; do not use coordinates.

Also prove:

~~~lean
theorem eta14_pow_seven :
    eta14 ^ 7 = -1

theorem eta14_pow_fourteen :
    eta14 ^ 14 = 1
~~~

These are required even if exact primitive order 14 is deferred.

## 9. Primitive order 14 — strong target

Inspect Mathlib for a compact route.

Potential routes include:

~~~text
a theorem about negating an odd-order primitive root
IsPrimitiveRoot.pow plus a negation theorem
IsPrimitiveRoot.iff_orderOf
direct use of eta14_sq, eta14_pow_seven, and primitive order 7
~~~

Preferred theorem:

~~~lean
theorem eta14_isPrimitiveRoot :
    IsPrimitiveRoot eta14 14
~~~

Do not build a large custom order theory merely for this theorem.

If the proof is compact, implement it.

If not, report it as DEFERRED while retaining eta14 square/half/full-turn
identities.

## 10. Existing carrier as a TwoPrimePhase packet — strongest bridge

If eta14_isPrimitiveRoot is proved and the imported domain module supplies the
required NoZeroDivisors instance, define:

~~~lean
noncomputable def degreeSixFourteenPhase :
    FourteenPhase SevenCyclotomicDegreeSixInt.Ring where
  eta := eta14
  positive := by norm_num
  primitive := eta14_isPrimitiveRoot
~~~

Then prove the key exact identification:

~~~lean
@[simp] theorem degreeSixFourteenPhase_zeta :
    degreeSixFourteenPhase.zeta =
      SevenCyclotomicDegreeSixInt.zeta
~~~

This is the most important calibration theorem of NGEO-012.

It states:

~~~text
generic eta^2 seventh-phase generator
=
existing degree-six cyclotomic zeta
~~~

Also verify that generic halfTurn recovers eta14^7 = -1.

If the packet cannot be built cheaply, keep eta14_sq and report the packet as
deferred.

## 11. Existing oriented carrier interpretation

The current FLT/Seven carrier uses:

~~~text
R - zeta * L
R - zetaInv * L
~~~

NGEO-012 may add only a thin interpretation theorem showing that this zeta is
the even-sector generator of degreeSixFourteenPhase, if that packet exists.

For example, a one-line rewrite from existing zeta to:

~~~text
degreeSixFourteenPhase.evenPhase 1
~~~

is acceptable.

Do NOT alter or re-prove:

~~~text
cyclotomicDegreeSixCarrier
local evaluation
oriented factorization
PID/class-number results
ramified routing
FLT7 descent theorems
~~~

The purpose is phase identification only.

## 12. Exact status labels

report-012.md must classify relevant statements using:

~~~text
LEAN-CONFIRMED
STRUCTURAL-CALIBRATION
DEFERRED
OUT-OF-SCOPE
~~~

At minimum classify:

- generic 14 = 7+7 sector cardinality
- complex fourteen-phase witness
- CF2D exact order 14
- existing degree-six zeta primitive order 7
- eta14 square/half/full-turn identities
- eta14 exact primitive order 14
- degreeSixFourteenPhase packet
- CF2D to complex eta identification
- any relation to FLT7 equations

## 13. No FLT7 theorem

This checkpoint may import existing FLT/Seven modules only in the one-way
calibration bridge.

It must not prove, strengthen, or restate an FLT7 theorem.

Do not claim:

- the fourteen-phase split proves FLT7
- every signed seventh-power solution is a phase multiple
- the degree-six carrier alone closes descent
- CF2D regularKernel 14 is definitionally equal to eta14
- a new cyclotomic field is required before checking whether eta14 already
  lies in the current carrier

## 14. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/SevenTreasureAxiomAudit.lean
~~~

Audit:

- sector cardinalities/disjointness
- signed seventh equations
- complex fourteen-phase full/half turns
- CF2D order 14 calibration
- eta14_sq
- eta14_pow_seven
- eta14_pow_fourteen
- eta14_isPrimitiveRoot if implemented
- degreeSixFourteenPhase_zeta if implemented

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 15. Validation

Run focused builds for every new production module.

Expected commands include:

~~~text
lake build DkMath.NumberGeometry.Phase.SevenTreasure
lake build DkMath.NumberGeometry
lake build DkMath.FLT.Seven.NumberGeometryFourteenPhaseBridge
lake build DkMathTest.NumberGeometry.SevenTreasureAxiomAudit
lake build DkMath
git diff --check
~~~

If the FLT/Seven bridge filename differs, adjust the command and record it.

Scan changed/new files for prohibited proof shortcuts, malformed docstrings,
and accidental dependency inversion.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-012.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. Final FourteenPhase specialization.
4. Exact 7+7 finite-sector theorem and cardinalities.
5. Signed seventh-power equation theorems.
6. Complex fourteen-phase calibration.
7. CF2D order-14 calibration.
8. Existing degree-six zeta facts reused.
9. Final eta14 definition.
10. eta14 square / seventh / fourteenth power theorems.
11. Primitive-order-14 status.
12. degreeSixFourteenPhase packet status.
13. Exact theorem identifying generic zeta with existing carrier zeta, if implemented.
14. Explicit statement that no FLT7 theorem was proved.
15. Status table using LEAN-CONFIRMED / STRUCTURAL-CALIBRATION / DEFERRED / OUT-OF-SCOPE.
16. Build / axiom / diff-check results.
17. Recommended post-v0 next step.

Stop after NGEO-012.

Do not begin FLT7 re-entry, general-prime cyclotomic factorization, or
systematic classification of shared-point arithmetic landings in this same
checkpoint.
