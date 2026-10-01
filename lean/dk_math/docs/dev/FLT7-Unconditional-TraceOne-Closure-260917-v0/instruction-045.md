# FLT7TC-005R39 — C=1 ideal scalarization and unit-only twisted reduction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-043.md`
- `report-044.md`
- `PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean`
- `PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean`
- `PrimeTraceOneDirectRealCubicPrimeAllocation.lean`
- `PrimeTraceOneDirectRealCubicSquareIdealSupport.lean`
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean`
- `SevenRealCubicUnitClass.lean`

R38 closes the first common-prime Kummer audit with Outcome B.  The fixed
Kummer condition is not universally contradictory (`q=379` is a checked
compatible calibration), so R39 should not deepen the arbitrary-common-prime
residue-symbol theory yet.

Instead attack the other canonical branch:

```text
C = 1.
```

R37/R38 then give

```text
R = U^3
S = V^3
a = U*V
Nat.Coprime U V
U^5 < V.
```

The square-root principal ideals also satisfy

```text
(r) * (s) = (a)
IsCoprime (r) (s).
```

The goal of R39 is to prove that the rational scalar split is already exact
at the ideal level:

```text
(r) = (U)
(s) = (V),
```

and hence

```text
r = eta * U
s = xi * V
```

for global units `eta, xi`.  Then reduce the R27 square-twisted identity to
a unit-only three-term equation.

Stop after this scalarization and the first theta-adic audit.  Do not build a
successor or claim descent.

## Part A — scalar ideals and their norms

For a canonical packet `h : DirectOrbitCanonicalCommonFactorPacket p` with
`hc : h.c = 1`, write

```text
t := h.squareRefinement
r0 := t.gapSquareRoot
s0 := t.quotientSquareRoot
U := h.u
V := h.v.
```

Define in `O = 𝓞 SevenRealCubic.Field` the scalar principal ideals

```text
IU := Ideal.span {(U : O)}
IV := Ideal.span {(V : O)}.
```

Prove

```text
Ideal.absNorm IU = U^3
Ideal.absNorm IV = V^3.
```

Use `Ideal.absNorm_span_natCast` and the already checked cubic rank/finrank.
Do not reprove the field degree.

Also expose the existing square-root ideal norms under `C=1`:

```text
Ideal.absNorm (gapSquareIdeal t) = U^3
Ideal.absNorm (quotientSquareIdeal t) = V^3.
```

## Part B — neutral norm-coprime ideal lemma

Prefer a small reusable lemma specialized to the current ring of integers,
or neutral if the proof is genuinely generic:

```text
Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J)
  -> I != bottom
  -> J != bottom
  -> IsCoprime I J.
```

A recommended proof is by contradiction:

1. assume `I ⊔ J != top`;
2. choose a maximal ideal `P` containing `I ⊔ J`;
3. then `P` divides both `I` and `J`;
4. `Ideal.absNorm P` divides both absolute norms via
   `Ideal.absNorm_dvd_absNorm_of_le`;
5. `P != top`, hence `Ideal.absNorm P != 1` by `Ideal.absNorm_eq_one_iff`;
6. contradict natural-number coprimality.

If the maximal-ideal route is awkward, an equivalent checked prime-factor
argument is acceptable.

Do not assume the converse of norm multiplicativity without proof.

## Part C — cross-coprimality

From `Nat.Coprime U V`, derive

```text
Nat.Coprime (U^3) (V^3).
```

Then Part A/B should give the two cross statements

```text
IsCoprime (gapSquareIdeal t) IV
IsCoprime IU (quotientSquareIdeal t).
```

Keep the already checked

```text
IsCoprime (gapSquareIdeal t) (quotientSquareIdeal t)
```

separate.  The new cross-coprimality is the decisive input.

## Part D — scalar product identity

Use `h.unitPart_eq` with `hc` to rewrite

```text
a = U*V.
```

Combine this with

```text
directOrbitSquareRefinement_principal_ideal_scalar_split t
```

and `Ideal.span_singleton_mul_span_singleton` to prove

```text
gapSquareIdeal t * quotientSquareIdeal t = IU * IV.
```

Be explicit about the coercions

```text
(U : O), (V : O), (a : O)
```

and use the model/ring-of-integers scalar bridge already present in the
current files.  Do not identify model elements and ring-of-integers elements
by definitional equality unless `simp` actually checks it.

## Part E — Euclid cancellation in the ideal monoid

Let

```text
A := gapSquareIdeal t
B := quotientSquareIdeal t
X := IU
Y := IV.
```

From `A*B = X*Y`:

- `A | X*Y` and `IsCoprime A Y` imply `A | X` by
  `IsCoprime.dvd_of_dvd_mul_right` or the correctly oriented companion;
- `X | A*B` and `IsCoprime X B` imply `X | A`.

Use `Ideal.dvd_iff_le` plus antisymmetry, or associated ideals plus the fact
that ideals are normalized, to conclude

```text
A = X.
```

Similarly conclude

```text
B = Y.
```

This short Euclid-cancellation proof is preferred over rebuilding the entire
prime-ideal factorization.

Do not infer ideal equality merely from equal absolute norms.

## Part F — element-level scalarization

Use

```text
Ideal.span_singleton_eq_span_singleton
```

to obtain

```text
Associated (modelEquivRingOfIntegers r0) (U : O)
Associated (modelEquivRingOfIntegers s0) (V : O).
```

Extract units in `O`, then transport them through the existing model/ring-of-
integers unit equivalence if available, or construct model units through the
ring equivalence, to expose a stable model-level theorem:

```text
exists eta : SevenRealCubicIntˣ,
  r0 = (eta : SevenRealCubicInt) * (U : SevenRealCubicInt)

exists xi : SevenRealCubicIntˣ,
  s0 = (xi : SevenRealCubicInt) * (V : SevenRealCubicInt).
```

A single packet containing `eta, xi` is preferred if it stays small.

Check orientation carefully: `Associated x y` may produce `x = unit * y` or
`y = unit * x`; normalize to the displayed direction.

## Part G — rotate the scalarized gap root

For the gap-side unit `eta`, prove

```text
rotateEquiv r0 =
  (directOrbitRotateUnit eta : SevenRealCubicInt) * U

rotateEquiv (rotateEquiv r0) =
  (directOrbitRotateUnit (directOrbitRotateUnit eta) : SevenRealCubicInt) * U.
```

The rational scalar `U` must be fixed by rotation.  Kernel-check this rather
than relying on prose.

## Part H — unit-only square-twisted equation

Map the scalarization into

```text
directOrbit_squareTwist_twisted_eq t.
```

Every term contains `U^14`.  Since `U > 0`, cancel it in the domain and prove
the literal model-ring unit equation

```text
(c0 : SevenRealCubicInt) * (eta^7)^2
 + (c1 : SevenRealCubicInt) * ((rotateUnit eta)^7)^2
 + (c2 : SevenRealCubicInt) * ((rotateUnit^2 eta)^7)^2
 = 0,
```

where `c0,c1,c2` are the R27 square-twist coefficients.

Equivalent exponent spelling (`eta^14`) is acceptable, but retain a theorem
showing the seventh-power-square form because the next local audit needs it.

Then absorb the square-refinement unit factors already built into `c0,c1,c2`
only if this simplifies the statement without changing the exact unit class.

Mandatory conceptual endpoint:

```text
there exist three explicit global units e0,e1,e2, cyclically related,
such that
  directOrbitTwistedCoeff0 * e0^7
  + directOrbitTwistedCoeff1 * e1^7
  + directOrbitTwistedCoeff2 * e2^7 = 0.
```

The preferred choice is

```text
e0 = gapSquareUnit * eta^2
e1 = rotate(e0)
e2 = rotate^2(e0),
```

if the exact coefficient definitions make this literal.

## Part I — theta-adic first calibration

Do not expect a contradiction modulo the existing three mod-7 theta
coordinates.

Kernel-check or scratch-check the actual cancellation rather than assuming
it.  The expected pattern is:

```text
thetaResidue term0 + thetaResidue term1 + thetaResidue term2 = 0
thetaLinearModSeven term0 + ... = 0
thetaSquareModSeven term0 + ... = 0.
```

The reason to test this is structural: seventh powers of units are scalar at
the truncated theta level, while the coefficient classes and R25 transport
are arranged cyclically.

If all three coordinates cancel, record that the current
`projectiveLog/theta^3` surface is exhausted and that any contradiction from
the `C=1` unit equation must use a deeper `7`-adic/theta-adic invariant.

If one coordinate does not cancel, promote the resulting contradiction
immediately and stop.

## Part J — optional connection to existing mod-49/depth infrastructure

Only after Part I is green, audit whether an existing current-provenance
theorem (not a historical routing assumption) already lifts the relevant
unit equation one level deeper, for example through a checked `ZMod 49` or
ramified-axis depth statement.

Historical `RAMIFIED-*`, `FUSION-*`, or terminal-routing files may be read
as proof-pattern references but must not be imported as hidden closure input
unless their hypotheses are explicitly reconstructed from the current
counterexample provenance.

Do not implement a new mod-49 theory in R39.

## Part K — stable packet

Prefer a focused production file:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean
```

with a small structure conceptually:

```text
structure DirectOrbitTrivialCommonFactorPacket ... where
  canonical : DirectOrbitCanonicalCommonFactorPacket p
  c_eq_one : canonical.c = 1
  gapScalarUnit : SevenRealCubicIntˣ
  quotientScalarUnit : SevenRealCubicIntˣ
  gapRoot_scalar : ...
  quotientRoot_scalar : ...
  gapIdeal_eq_scalar : ...
  quotientIdeal_eq_scalar : ...
  unitTwistedEq : ...
```

Names may differ.

Do not duplicate the canonical arithmetic fields `U,V`; reference the
existing packet.

## Part L — stop and report

Stop after ideal scalarization, element scalarization, unit-only twisted
equation, and the first theta-adic calibration.

If the expected coordinate cancellation occurs, the next frontier is precise:

```text
C = 1:
  one deeper theta/7-adic coefficient of the unit-only equation;

C > 1:
  common-prime power-residue symbol beyond the R38 Kummer condition.
```

At that point compare which frontier has the smaller new-theory burden.

## Hard stops

- No ideal equality from absNorm equality alone.
- No scalarization from rational norm being a cube alone.
- No assumption that an algebraic integer with norm `U^3` is associated to
  the rational integer `U` without the ideal-coprime/product argument.
- No assumption that `C=1` follows from R38.
- No use of common-prime complete splitting in the `C=1` branch; there is no
  common prime there.
- No projectiveLog contradiction if the three theta coordinates actually
  cancel.
- No historical terminal packet imported as a shortcut.
- No successor/descent claim.
- No FLT7 contradiction without an actual checked noncancellation.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Tests

Add focused API/axiom tests and an R39 scratch file.  Keep all R37/R38 tests
green.

Create `report-045.md` and update `ROADMAP.md`.

## Report questions

1. Was a checked norm-coprime-to-ideal-coprime lemma obtained?
2. Were the scalar ideal norms `U^3` and `V^3` proved?
3. Were the two cross-coprimality statements proved?
4. Was the product identity `A*B = X*Y` rewritten with `a=U*V`?
5. Did Euclid cancellation prove `(r)=(U)` and `(s)=(V)`?
6. Were model-level units `eta,xi` extracted with `r=eta*U`, `s=xi*V`?
7. Was the R27 identity reduced to a unit-only three-term seventh-power
   equation?
8. Did the three existing mod-7 theta coordinates cancel exactly?
9. If they cancel, is there an already checked current-provenance mod-49/depth
   bridge that applies without importing historical closure assumptions?
10. Did any actual contradiction arise?

## Outcomes

- Outcome A — C=1 scalarization is green and a checked theta/depth invariant
  immediately contradicts the unit-only equation.
- Outcome B — ideal and element scalarization plus unit-only equation are
  green; existing theta^3 data cancels, so a deeper local invariant is needed.
- Outcome C — ideal scalarization is green; transporting associated generators
  to model units is the precise frontier.
- Outcome D — cross-coprimality is green; Euclid cancellation in the ideal
  monoid is the precise frontier.
- Outcome E — norm-coprime-to-ideal-coprime is the precise missing neutral
  lemma.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactor
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorR39Scratch.lean
git diff --check
```

Print axioms for:

- norm-coprime ideal lemma;
- gap/quotient scalar ideal equalities;
- model-level scalar unit equalities;
- unit-only twisted equation;
- any promoted theta-coordinate cancellation or contradiction theorem.

Run forbidden-source/import scans on every decisive file.
