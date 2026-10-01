# NGEO-011 — General 2p signed phase layer

Branch:

~~~text
research/NumberGeometry-TwoPointGauge-260924-v0
~~~

Read first:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/README.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-010.md

lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean
lean/dk_math/DkMath/NumberTheory/PrimeGauge/Return.lean
lean/dk_math/DkMath/RH/CFBRC/MirrorIndexedRoot.lean
lean/dk_math/DkMath/NumberTheory/CyclotomicQRProduct.lean
~~~

The audit already shows useful theorem ownership:

- CF2D regularKernel k has exact order k.
- DkMath.NumberTheory.PrimeGauge.Return exposes return/divisibility of that finite phase.
- Mathlib complex roots are already used through Complex.isPrimitiveRoot_exp.
- IsPrimitiveRoot is the established project vocabulary for cyclotomic phases.

NGEO-011 must build a general signed 2p phase layer independent of FLT.
It must not import any DkMath.FLT module.

## Objective

For a positive natural p, represent a phase element eta with:

~~~text
eta^(2*p) = 1
eta^p     = -1
~~~

Then define:

~~~text
even phase j = eta^(2*j)
odd  phase j = eta^(2*j + 1)
~~~

and prove:

~~~text
(even phase j)^p =  1
(odd  phase j)^p = -1
~~~

Thus the 2p orbit splits into the signed equations:

~~~text
X^p - Y^p = 0
X^p + Y^p = 0
~~~

when X is the corresponding phase multiple of Y.

This is the exact algebraic content needed before p=7 / fourteen-phase calibration in NGEO-012.

## Production layout

Preferred file:

~~~text
lean/dk_math/DkMath/NumberGeometry/Phase/TwoPrime.lean
~~~

Update:

~~~text
lean/dk_math/DkMath/NumberGeometry.lean
~~~

to export it.

The phase module should be algebraic and should not depend on LogGauge,
PrimeScale, UnitCycle, FLT, or the existing FLT7 carrier.

Narrow Mathlib roots-of-unity imports are allowed.

A small CF2D or complex calibration may be included in a bridge/test file if that keeps the generic core cleaner.

## 1. Audit IsPrimitiveRoot half-turn support first

Inspect current Mathlib for a theorem that derives the half-turn identity from a primitive 2*p root.

Desired mathematical statement over a suitable characteristic-zero field:

~~~text
IsPrimitiveRoot eta (2*p)
  -> eta^p = -1
~~~

Do not manually build a large roots-of-unity theory if Mathlib already owns this fact.

If a lightweight generic derivation is available, use it.

If not, use the bounded packet design in section 2 and prove that the canonical complex phase satisfies the packet.

Report the exact audit result.

## 2. Bounded generic packet

If the half-turn theorem is not cheaply available generically, define the smallest explicit contract.

Preferred shape:

~~~lean
structure TwoPrimePhase (R : Type*) [CommRing R] (p : ℕ) where
  eta : R
  primitive : IsPrimitiveRoot eta (2 * p)
  halfTurn : eta ^ p = -1
~~~

If IsPrimitiveRoot requires a stronger ambient type than CommRing in the current API, use the weakest practical standard typeclass.

Do not store eta^(2*p)=1 separately when it follows from primitive.

If Mathlib gives halfTurn directly from primitive under suitable field hypotheses, replace the redundant field by a theorem and document the stronger ambient assumptions.

## 3. Full-turn theorem

Expose:

~~~lean
theorem TwoPrimePhase.fullTurn
    (P : TwoPrimePhase R p) :
    P.eta ^ (2 * p) = 1
~~~

This should be a direct consequence of P.primitive.pow_eq_one.

Use one multiplication convention consistently: 2 * p is preferred.

## 4. Even and odd phase definitions

Define:

~~~lean
def TwoPrimePhase.evenPhase
    (P : TwoPrimePhase R p) (j : ℕ) : R :=
  P.eta ^ (2 * j)

def TwoPrimePhase.oddPhase
    (P : TwoPrimePhase R p) (j : ℕ) : R :=
  P.eta ^ (2 * j + 1)
~~~

Natural indices are acceptable for algebraic identities.

For finite orbit/cardinality statements, use j : Fin p rather than carrying manual j < p hypotheses.

Do not create multiple equivalent phase encodings.

## 5. Signed p-th power split

Required:

~~~lean
theorem TwoPrimePhase.evenPhase_pow
    (P : TwoPrimePhase R p) (j : ℕ) :
    (P.evenPhase j) ^ p = 1
~~~

~~~lean
theorem TwoPrimePhase.oddPhase_pow
    (P : TwoPrimePhase R p) (j : ℕ) :
    (P.oddPhase j) ^ p = -1
~~~

The proofs should reduce exponents and use:

~~~text
eta^(2*p)=1
eta^p=-1
~~~

Do not use coordinate/trigonometric expansions in these generic theorems.

## 6. p-phase generator eta^2

Define:

~~~lean
def TwoPrimePhase.zeta (P : TwoPrimePhase R p) : R :=
  P.eta ^ 2
~~~

Required:

~~~lean
theorem TwoPrimePhase.zeta_pow_p
    (P : TwoPrimePhase R p) :
    P.zeta ^ p = 1
~~~

Also prove the normal forms:

~~~text
evenPhase j = zeta^j
oddPhase  j = eta * zeta^j
~~~

For prime p, investigate:

~~~lean
theorem TwoPrimePhase.zeta_isPrimitiveRoot
    (P : TwoPrimePhase R p)
    (hp : Nat.Prime p) :
    IsPrimitiveRoot P.zeta p
~~~

Only include it if current Mathlib order APIs make the proof short.
Otherwise record it as deferred. zeta_pow_p is required.

## 7. Finite even/odd sectors

For hp : 0 < p, define or expose finite sectors indexed by Fin p.

Preferred minimal API:

~~~lean
def evenPhaseFin (P : TwoPrimePhase R p) (j : Fin p) : R := ...
def oddPhaseFin  (P : TwoPrimePhase R p) (j : Fin p) : R := ...
~~~

Strongly recommended if cheap:

- even-sector injectivity
- odd-sector injectivity
- even/odd disjointness

Use P.primitive.pow_inj or order APIs rather than proving exponent injectivity from scratch.

If disjointness becomes noisy in a generic ring, keep the signed p-th power classification and defer the cardinality theorem.

## 8. Signed power equations

This is a required bridge to the polynomial forms without introducing heavy product-factor infrastructure.

For any Y : R, prove:

~~~lean
theorem TwoPrimePhase.even_signed_equation
    (P : TwoPrimePhase R p) (j : ℕ) (Y : R) :
    (P.evenPhase j * Y) ^ p - Y ^ p = 0
~~~

~~~lean
theorem TwoPrimePhase.odd_signed_equation
    (P : TwoPrimePhase R p) (j : ℕ) (Y : R) :
    (P.oddPhase j * Y) ^ p + Y ^ p = 0
~~~

These formalize:

~~~text
X = eta^(2j) Y     -> X^p - Y^p = 0
X = eta^(2j+1) Y   -> X^p + Y^p = 0
~~~

Do not claim converses unless they are actually proved under adequate field and nonzero assumptions.

## 9. Optional exact factorization

Investigate current Mathlib roots-of-unity / nth-roots product APIs.

A desirable but optional stronger result over the complex numbers or a suitable field is:

~~~text
X^p - Y^p = product over even phases
X^p + Y^p = product over odd phases
~~~

Do not hand-roll a large finite-product proof if no compact existing API is available.

The signed root equations from section 8 are sufficient for Outcome A.

Report exact factorization as IMPLEMENTED or DEFERRED.

## 10. Canonical complex 2p phase

Provide at least one consistency/construction witness in the complex numbers.

Preferred definition conceptually:

~~~text
eta_p = exp(2*pi*i / (2*p))
      = exp(pi*i/p)
~~~

Use the already established Mathlib route:

~~~text
Complex.isPrimitiveRoot_exp
~~~

to prove primitive order 2*p for 0 < p.

Then prove:

~~~text
eta_p^p = -1
~~~

Use existing complex exponential/root-of-unity lemmas after reconnaissance.
Do not assume this as an axiom in the complex calibration.

If the generic packet stores halfTurn, package the canonical complex eta as:

~~~text
complexTwoPrimePhase p hp : TwoPrimePhase Complex p
~~~

This is the preferred proof that the generic contract is inhabited.

## 11. CF2D calibration

The repository already has:

~~~text
regularKernel (2*p)
orderOf_regularKernel
regularKernel_pow_eq_one
~~~

This is a real two-component phase of exact order 2*p.

A thin calibration is recommended, but do not invent an unfinished UnitKernel-to-Complex equivalence in this checkpoint.

At minimum record or prove in a test/bridge theorem:

~~~text
orderOf (regularKernel (2*p)) = 2*p
~~~

from the existing owner theorem.

If a small existing route proves the p-th power is the CF2D half-turn, add it.
Otherwise record:

~~~text
CF2D exact 2p order: LEAN-CONFIRMED
CF2D to canonical complex eta identification: DEFERRED
~~~

Do not duplicate CycleDivision theorem ownership.

## 12. No FLT or seventh-cyclotomic dependency

Production NGEO-011 must not import:

~~~text
DkMath.FLT.*
DkMath.FLT.Seven.*
~~~

Do not use the degree-six seventh-cyclotomic carrier yet.

NGEO-012 will specialize p=7 and audit the connection to existing seventh-cyclotomic code.

It is acceptable to use general Mathlib IsPrimitiveRoot APIs.

Avoid importing the heavy DkMath QR/QNR cyclotomic stack unless one tiny general theorem is genuinely reused and the dependency is justified.

## 13. False claims to avoid

Do not claim:

- every solution of X^p - Y^p = 0 is an even phase without an actual converse proof
- every solution of X^p + Y^p = 0 is an odd phase without proof
- the phase split proves FLT
- p must be 7
- the CF2D regular kernel is already definitionally the same object as a complex primitive root
- exact cyclotomic product factorization unless implemented

## 14. Axiom audit

Create:

~~~text
lean/dk_math/DkMathTest/NumberGeometry/TwoPrimePhaseAxiomAudit.lean
~~~

Audit substantive declarations:

- full turn
- half-turn source/construction
- even/odd p-th power
- zeta p-th power
- signed equations
- finite-sector injectivity/disjointness if implemented
- canonical complex phase primitive-root theorem

Expected logical infrastructure may remain:

~~~text
propext
Classical.choice
Quot.sound
~~~

No new axiom, sorryAx, unsafe shortcut, sorry, or admit.

## 15. Validation

Run:

~~~text
lake build DkMath.NumberGeometry.Phase.TwoPrime
lake build DkMath.NumberGeometry
lake build DkMathTest.NumberGeometry.TwoPrimePhaseAxiomAudit
lake build DkMath
git diff --check
~~~

If a separate CF2D calibration test/module is added, include its focused build.

Scan changed/new files for prohibited proof shortcuts and malformed docstrings.

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-011.md
~~~

The report must contain:

1. Outcome A or B.
2. Exact files added/changed.
3. IsPrimitiveRoot half-turn audit result.
4. Final TwoPrimePhase representation.
5. Full-turn and half-turn theorem ownership.
6. Even/odd phase definitions.
7. Signed p-th-power split theorems.
8. zeta=eta^2 API and primitive-p status.
9. Finite p+p sector injectivity/disjointness status.
10. Signed X^p - Y^p / X^p + Y^p equation theorems.
11. Exact product-factorization status.
12. Canonical complex 2p-phase construction.
13. CF2D regularKernel calibration status.
14. Claims intentionally not made.
15. Build / axiom / diff-check results.
16. Exact proposed scope for NGEO-012.

Stop after NGEO-011.

Do not implement the p=7 Fourteen-Phase / Seven Treasure calibration from NGEO-012 in the same checkpoint.
