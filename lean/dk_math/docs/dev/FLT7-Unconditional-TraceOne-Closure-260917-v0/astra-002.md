# FLT7 Astra Breakthrough Reconnaissance

Repository: `Deskuma/dkmath`

Current branch:

`research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This is a high-cost mathematical reconnaissance task.

Do **not** begin by implementing Lean.

First inspect the checked current surface, historical FLT7 infrastructure, and all plausible bridges. The goal is to identify a genuinely new theorem capable of moving the proof toward a provenance-preserving contradiction.

The current campaign has reached saturation under its existing local/deep-jet route.

## Current mandatory endpoint

For the `C = 1` branch of the canonical common-factor packet, Lean has kernel-checked:

```text
W = rho * t^(7^9)
```

where:

```text
rho = -alphaUnit^3
norm W = 1
projectiveLog W = (1,1)
Phi(W) = 0
```

and

```text
Phi(A + B*theta + C*theta^2)
  = 3*A - 10*B + 35*C.
```

The finite-Hensel argument is genuinely finite and currently saturated:

```text
theta^32 provenance
  -> theta^30
  -> scalar depth 10
  -> source nilpotent depth 9
  -> Z^7 depth 9
  -> Z depth 8
  -> v^(-1) depth 8
  -> v = t^(7^8)
  -> W = rho * t^(7^9).
```

The current provenance does **not** justify one more level.

Do not assume arbitrary Hensel continuation.

## Exact trace-plane surface

R46 kernel-checks the integer parameterization

```text
A = 5*(r+s)
B = 5*r - 2*s
C = r-s
```

for every integral trace-plane point.

The exact norm equation is

```text
norm W =
  -(r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3).
```

Thus `norm W = 1` gives

```text
r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3 = -1.
```

The projective class `(1,1)` gives

```text
r ≡ 3*s (mod 7).
```

The calibration unit `rho` corresponds to

```text
(r,s) = (-3,-1)
```

and satisfies every one of these constraints.

Therefore proving merely `W = rho` would **not yet be a contradiction**.

No current theorem excludes `W = rho`.

## Frozen routes

Do not reopen these without genuinely new information.

### Ordinary successor

R25 proves the ordinary homogeneous restart impossible.

The obstruction is a fixed nontrivial theta residue in the coefficient ratio and is independent of the later high-power correction.

### Square restart

R27 proves coefficient zero is a non-square norm-one mixed-sign unit.

The exponent `7^9` is odd, so the current high-power correction does not turn it into a square.

### Mixed real signature

Current sign information does not contradict an odd high power.

### Finite Hensel

The theta-depth budget is exhausted at the current `7^9` correction.

## C > 1 branch

For every prime `q | C`, the checked current surface gives:

```text
q | R
q | S
q | a
q != 7
q splits completely in the real cubic field
three primes lie above q
exact one-to-two gap/quotient prime allocation
q % 7 = 1 or 6
```

At an oriented gap prime, there are residue elements satisfying

```text
beta^3 = 2*beta^2 + beta - 1
z != 0
z^7 = beta*(1+beta).
```

This is derived from the stronger 14th-power square-twist relation.

Single-prime Kummer obstruction is **not universal**:

```text
q = 29
```

gives a nonresidue calibration, while

```text
q = 379
```

gives an actual seventh-power residue.

For `q ≡ -1 mod 7`, the seventh-power map is an automorphism, so the reduced Kummer equation alone is invisible.

No global seventh-power reciprocity/product theorem is currently connected to this branch.

## R46 audit result

R46 classified the obvious continuations:

* Trace-plane / Thue: exact surface, but no certified complete Thue solver or effective bound.
* Explicit unit lattice: unit rank two is known, but `alphaUnit` and `alphaAddOneUnit` are **not** proved to be a fundamental integral-unit basis.
* Global Kummer/reciprocity: current local data are strong, but the required aggregation theorem is absent.
* Successor/descent: existing homogeneous and square restart mechanisms remain structurally blocked.

R46 therefore ended with Outcome E.

## Important repository infrastructure not to ignore

Perform a fresh inspection of the existing historical/current FLT7 infrastructure, especially:

```text
DkMath/FLT/Seven/SevenRamifiedFusion*
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomic*
DkMath/FLT/Seven/SevenRamifiedFusionPrimeLoad*
DkMath/FLT/Seven/SevenRamifiedFusionGlobalOrientedPrimeFactorization.lean
DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicConjugatePrimePair.lean
DkMath/FLT/Seven/SevenRamifiedFusionLoadedResidualIdealBridge.lean
DkMath/FLT/Seven/SevenRamifiedFusionRealPair*
DkMath/FLT/Seven/SevenRealCubicNormFirstVariation.lean
DkMath/FLT/Seven/SevenRealCubicCoprimeExtraction.lean
```

There is already substantial degree-six cyclotomic-carrier, prime-address,
oriented-prime, real-pair, load-allocation, and norm infrastructure.

The key question is:

> Can any of this infrastructure be connected **non-circularly** to the
> current `DirectOrbitCanonicalCommonFactorPacket` / paired-deep-jet
> provenance and supply a second invariant that R37–R46 are currently missing?

Do not use a historical terminal contradiction merely because it already has the desired conclusion.

The bridge must start from current counterexample provenance.

## Primary research question

Find a theorem of approximately the following character:

```text
current counterexample-derived packet
  + current exact real-cubic / ideal / depth data
  -> NEW invariant
  -> contradiction
```

or

```text
current packet
  -> strictly smaller packet of the SAME provenance type
```

with an explicit well-founded measure.

The missing result must be more than another normalization.

## Search priorities

Investigate these in this order.

### 1. Degree-six fusion bridge

Can the exact one-to-two real-cubic prime allocation be lifted to the
degree-six cyclotomic carrier in a way that creates an orientation/parity
constraint absent from the real cubic field?

In particular inspect whether the conjugate prime pair or loaded residual
factorization forces a contradiction with the current allocation or
multiplicity table.

### 2. Stronger use of the original 14th-power relation

The C>1 reduction discards information when

```text
y^14 = twistRatio
```

is converted into

```text
z^7 = beta*(1+beta).
```

Determine whether the square component of the 14th-power statement,
combined with the exact one-to-two prime allocation or degree-six
orientation, gives an additional quadratic character constraint.

This is especially important for `q ≡ -1 mod 7`, where the seventh-power
condition alone is automatic.

### 3. Global product over the three primes above q

The real cubic extension is cyclic of degree three.

Check whether the three local evaluations of the coefficient ratio or Kummer
unit have a product/norm relation that forces a character product condition.

A useful theorem would look like:

```text
χ(P0) * χ(P1) * χ(P2) = fixed value
```

while the current allocation forces an incompatible pattern.

Do not invent such a law: derive it only if the repository or standard
algebra supports it.

### 4. Norm first variation / unused higher coordinate invariant

Inspect whether `SevenRealCubicNormFirstVariation.lean` or related exact norm
variation formulas provide a second linear/quadratic invariant independent
of the R40 trace plane.

The existing trace plane alone contains the calibration rho.

We need a second provenance-sensitive equation that rho does not
automatically satisfy.

### 5. Calibration exclusion

Search specifically for an exact theorem obtainable from original
counterexample provenance that would imply

```text
W != rho.
```

This would immediately make several currently non-closing normal forms much
more powerful.

Do not assume such an inequality from intuition.

### 6. Genuine smaller provenance packet

Revisit the old smaller-norm twisted state only with the new R37–R45 exact
information.

Ask whether the high-power correction supplies the missing coefficient/root
normalization needed to construct a new

```text
PrimitiveCounterexampleRamifiedProvenance
```

with strictly smaller well-founded measure.

If not, state precisely why not.

## What NOT to do

Do not:

* claim FLT7 from the current `7^9` correction;
* assume infinite Hensel lifting;
* assume `alphaUnit` and `alphaAddOneUnit` are fundamental units;
* invoke an unformalized generic Thue solver;
* use finite numerical search as a complete proof;
* import a historical terminal contradiction circularly;
* infer that a seventh power, 49th power, or `7^9`-th power is trivial;
* assume `W != rho`;
* assume reciprocity without constructing its exact hypotheses.

## Required output

Return a research report with the following structure.

### A. Three strongest candidate breakthroughs

For each candidate provide:

1. the exact proposed theorem statement;
2. the precise existing files/theorems it would depend on;
3. the missing lemma(s);
4. why it is not circular;
5. whether the endpoint is an actual contradiction or merely a stronger
   normal form;
6. estimated Lean implementation scale.

### B. Best candidate

Choose exactly one route as the best next attack.

Explain why it is stronger than:

* generic Thue completion;
* explicit fundamental-unit computation;
* merely extending the finite-Hensel depth.

### C. Concrete R47 checkpoint

Write an implementation-ready checkpoint with a narrow target.

The preferred R47 endpoint is one decisive bridge theorem, not dozens of
auxiliary results.

### D. Stop condition

If no credible bridge exists, say so explicitly and identify the minimum new
mathematical theory required.

Do not manufacture progress.

The purpose of this Astra run is discovery, not optimism.
