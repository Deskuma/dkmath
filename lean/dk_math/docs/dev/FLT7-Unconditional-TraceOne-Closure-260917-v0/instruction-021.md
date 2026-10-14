# FLT7TC-005R16 — Exact root norm and canonical μ₇ first-order phase normalization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the committed R15 state recorded in
`report-020.md`.

R15 proved unconditionally, for every current
`PrimitiveCounterexampleRamifiedProvenance source` and every associated
chosen-quotient packet,

```text
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7.
```

The remaining problem is no longer principalization or unit absorption.
Do not return to the historical `CubicGapSeventhShapeReceiver` route.

## Main goal

Promote the existential seventh root `gamma` to a provenance-preserving
root packet with two additional checked invariants:

1. its exact integral cyclotomic norm is the current summit residual root;
2. its residual `mu_7` ambiguity is canonically fixed to first ramified
   order modulo `ramifiedPrime^2`.

Then exploit the explicit depth-35 quotient formula to derive the strongest
honest rational congruence on `endpointRight`, preferably a seventh-power
condition modulo `49`.

This is a bounded checkpoint.  Do not force a primitive contradiction if the
result leaves surviving residue classes.

## Fixed notation

For current provenance `r`, write conceptually

```text
L := r.summit.endpointLeft
R := r.summit.endpointRight
A := r.summit.gapRoot
B := r.summit.residualRoot
pi := ramifiedUniformizer
U := ramifiedSevenUnit
Q₁ := directCyclotomicPhaseQuotient r 1.
```

Existing checked identities include

```text
Q₁ = directRamifiedQuotient r
Q₁ = ofReal R + directRamifiedGapTail r
directRamifiedGapTail r = pi^35 * U^6 * ofReal(A)^7
directLinearFactor r = pi * Q₁
cyclotomicNormHom (directLinearFactor r) = 7 * B^7
cyclotomicNormHom pi = 7.
```

R15 supplies `Q₁ = gamma^7`.

## Part A — provenance-preserving exact seventh-root packet

Create a small packet, conceptually:

```lean
structure DirectCyclotomicExactRootPacket ... where
  gamma : SevenCyclotomicDegreeSixInt.Ring
  quotient_eq : directCyclotomicPhaseQuotient r 1 = gamma ^ 7
  factor_eq :
    directLinearFactor r = ramifiedUniformizer * gamma ^ 7
  gamma_not_mem_ramifiedPrime : gamma ∉ ramifiedPrime
  norm_eq_residualRoot :
    cyclotomicNormHom gamma = (r.summit.residualRoot : ℤ)
```

Use the actual R15 theorem to construct it.

### A1. Nonramified root

Prove `gamma ∉ ramifiedPrime` from

```text
gamma^7 = Q₁
Q₁ ∉ ramifiedPrime.
```

Do not infer it from an integer norm.

### A2. Exact integral norm

Apply `cyclotomicNormHom` to

```text
directLinearFactor = pi * gamma^7.
```

Use the already checked identities

```text
N(directLinearFactor) = 7 * B^7
N(pi) = 7
```

to obtain

```text
(cyclotomicNormHom gamma)^7 = B^7.
```

Conclude

```text
cyclotomicNormHom gamma = B
```

in `ℤ`.

Use odd-power injectivity / monotonicity or another clean integer theorem.
Do not silently discard a sign.

This exact norm is an important stable theorem and should be included in the
focused API/axiom audit.

## Part B — generic first-order μ₇ phase normalization

The seventh root `gamma` is only determined up to

```text
gamma ↦ zeta^k * gamma,  k mod 7.
```

R15 removed the associated unit but did not canonically choose this root
phase.  Build the smallest direct normalization modulo
`ramifiedPrime^2`.

### B1. Canonical scalar lift

For any `g : Ring` with `g ∉ ramifiedPrime`, define a canonical integer
lift of its ramified residue, for example

```text
scalarLift(g) := Int.ofNat (ramifiedEval g).val.
```

Prove

```text
g - scalarLift(g) ∈ ramifiedPrime.
```

and that `scalarLift(g)` is not divisible by seven.

### B2. First-order phase predicate

Define conceptually

```lean
def FirstOrderPhaseNormalized (g : Ring) (k : Fin 7) : Prop :=
  zeta ^ (k : ℕ) * g - (scalarLift g : Ring) ∈ ramifiedPrime ^ 2
```

or an equivalent formulation with an explicit quotient by `pi`.

Prove a first-order expansion for `zeta^k`, sufficient to show

```text
zeta^k = 1 - k*pi  (mod pi^2).
```

Do this by finite induction / binomial expansion.  Do not use analytic
arguments.

### B3. Existence and uniqueness

Write

```text
g - c = pi * t
```

with `c = scalarLift(g)`.

Modulo `ramifiedPrime`, multiplication by `zeta^k` changes the first-order
coefficient by

```text
t ↦ t - k*c.
```

Since `c mod 7 ≠ 0`, there is a unique `k : ZMod 7` killing this
coefficient.

Kernel-check existence and uniqueness, preferably as

```lean
∃! k : Fin 7, FirstOrderPhaseNormalized g k
```

for every `g ∉ ramifiedPrime`.

If using `Fin 7` causes unnecessary coercion overhead, a unique
`k : ZMod 7` plus a canonical `Fin 7` representative is acceptable.

This theorem is the direct current-route implementation of the historical
“additional phase normalization” requirement.  Keep it independent of FLT
provenance.

## Part C — normalized current root

Apply Part B to the actual `gamma` from Part A.

Define

```text
gammaNorm := zeta^k * gamma.
```

Prove all of the following:

```text
gammaNorm^7 = Q₁
cyclotomicNormHom gammaNorm = B
gammaNorm - c ∈ ramifiedPrime^2
c mod 7 ≠ 0.
```

The first equality uses `zeta^7 = 1`.
The norm equality should use the norm of `zeta` / Galois invariance already
available; do not re-prove the full number-field norm theory.

Package this as a provenance-preserving normalized-root packet.

## Part D — lift the normalized root to a rational mod-49 gate

This part is the preferred arithmetic consequence.

From

```text
gammaNorm - c ∈ ramifiedPrime^2
```

prove a seventh-power first-order gain:

```text
gammaNorm^7 - c^7 ∈ ramifiedPrime^8.
```

Reason: if `gammaNorm = c + pi^2*t`, every nonconstant term in the seventh
power has at least `pi^2`, and its linear coefficient carries an additional
factor seven, hence an additional `pi^6`.

Use the checked total ramification identity

```text
7 = pi^6 * U
```

with `U` a unit.

Separately, from the explicit quotient formula,

```text
Q₁ - R = pi^35 * U^6 * A^7,
```

hence certainly

```text
Q₁ - R ∈ ramifiedPrime^8.
```

Since `gammaNorm^7 = Q₁`, conclude

```text
(R - c^7 : Ring) ∈ ramifiedPrime^8.
```

### D1. Rational contraction lemma

Prove a clean generic contraction theorem sufficient for this application,
conceptually:

```lean
theorem fortyNine_dvd_of_intCast_mem_ramifiedPrime_pow_eight
    (n : ℤ)
    (h : (n : Ring) ∈ ramifiedPrime ^ 8) :
    (49 : ℤ) ∣ n
```

Search existing DkMath/Mathlib infrastructure before writing a new proof.

Preferred proof if no direct contraction API exists:

- write membership as `n = pi^8 * a`;
- apply `cyclotomicNormHom`;
- prove/check `cyclotomicNormHom (n : Ring) = n^6`;
- use `N(pi)=7` to get `7^8 | n^6`;
- convert prime-power divisibility to `7^2 | n`.

An ideal-contraction proof is also acceptable if shorter.

Do not claim a stronger contraction exponent without proof.

### D2. Endpoint-right seventh-power congruence

Conclude

```text
49 ∣ (R - c^7)
```

or equivalently

```text
(R : ZMod 49) = (c : ZMod 49)^7.
```

Since `7 ∤ R`, this is a unit seventh-power class modulo `49`.

If a clean public generic classifier is already available, reuse it.
Otherwise a small provenance-independent finite theorem on `ZMod 49` may be
added:

```text
unit seventh powers mod 49
  = {1, 18, 19, 30, 31, 48}.
```

Do not import a historical receiver packet merely to obtain this finite
classifier.

The desired current-route conclusion is therefore:

```text
R mod 49 ∈ {1, 18, 19, 30, 31, 48}.
```

This is a necessary local gate, not yet a contradiction.

## Part E — bounded contradiction/descent audit

After Part D, compare the new current-provenance facts

```text
gammaNorm^7 = Q₁
N(gammaNorm) = B
gammaNorm ≡ c (mod ramifiedPrime^2)
R ≡ c^7 (mod 49)
```

with existing clean FLT7 APIs.

Audit only the following possibilities:

1. Does the exact norm `N(gammaNorm)=B` plus the current summit
   `Nat.Coprime gapRoot residualRoot` construct a smaller primitive
   counterexample or an existing descent packet?
2. Does the endpoint-right mod-49 seventh-power gate combine with an existing
   current-provenance endpoint/residual congruence to give a contradiction?
3. Does the normalized `mu_7` phase satisfy the previously missing
   phase-normalization input of a clean additive reconstruction theorem?

Do not use:

- `CubicGapSeventhShapeReceiver`;
- `RamifiedSignedRootRoutingPacket` as a prerequisite;
- historical recursive reconstruction obligations;
- any theorem carrying `sorryAx`;
- coordinate maps as if they were multiplicative ring homomorphisms.

If no contradiction follows, stop and identify the exact finite/global
intersection that remains.

## Important hard stops

- Do not assume `ramifiedSevenUnit^6` is a seventh power.
- Do not arbitrarily choose a seventh root phase; prove the normalization.
- Do not treat the mod-49 six-residue condition as a contradiction.
- Do not infer integer coordinates from a cyclotomic element equation by
  componentwise multiplication.
- Do not weaken current provenance by translating back into an old receiver
  packet unless an explicit theorem proves the equivalence and it is
  genuinely necessary.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred files

Production:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRootPhaseNormalization.lean
```

Focused tests:

```text
DkMathTest/FLT/SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationApi.lean
DkMathTest/FLT/SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationAxiom.lean
```

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-021.md
```

and update `ROADMAP.md`.

Do not add the new module to the public facade unless the normalized-root
packet and its stable arithmetic consequences are complete.

## Report questions

1. Was an actual R15 root `gamma` retained in a provenance-preserving packet?
2. Was `gamma ∉ ramifiedPrime` proved?
3. Was the exact norm `cyclotomicNormHom gamma = residualRoot` proved?
4. Was generic first-order `mu_7` phase normalization modulo
   `ramifiedPrime^2` proved with existence and uniqueness?
5. Was a normalized current root constructed while preserving its seventh
   power and norm?
6. Was the gain
   `gammaNorm^7 - c^7 ∈ ramifiedPrime^8` proved?
7. Was the rational contraction
   `ramifiedPrime^8 ∩ ℤ ⊆ (49)` proved?
8. Was `endpointRight ≡ c^7 (mod 49)` proved?
9. Was the six-residue unit seventh-power classifier obtained on the current
   route?
10. Did any clean receiver-free contradiction/descent consumer become
    available? If not, what exact intersection remains?

## Outcome labels

- **Outcome A — NORMALIZED ROOT PACKET GREEN; MOD-49 GATE GREEN; CLEAN PRIMITIVE CONTRADICTION/DESCENT OBTAINED.**
- **Outcome B — NORMALIZED ROOT PACKET GREEN; EXACT NORM AND MOD-49 SEVENTH-POWER GATE GREEN; SURVIVING RESIDUE/GLOBAL BRANCHES REMAIN.**
- **Outcome C — CANONICAL μ₇ PHASE NORMALIZATION GREEN; RATIONAL pi^8-TO-49 CONTRACTION IS THE PRECISE FRONTIER.**
- **Outcome D — FIRST-ORDER μ₇ PHASE NORMALIZATION ITSELF REQUIRES A NEW LOCAL BRIDGE.**

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRootPhaseNormalization
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationAxiom
git diff --check
```

Also run forbidden-source scans for every new/modified decisive file and print
axioms for:

- the exact-root norm theorem;
- the generic first-order phase-normalization theorem;
- the normalized current-root theorem;
- the rational contraction theorem;
- the endpoint-right mod-49 gate.

The decisive theorem chain must contain no `sorryAx`.
