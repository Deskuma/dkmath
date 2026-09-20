# FLT7TC-005R47 — Source-sensitive calibration exclusion

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `astra-002-report.md`
- `astra-002-r47-checkpoint.md`
- `DkMathTest/FLT/SevenCalibrationExclusionAstra02Scratch.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `PrimeTraceOneDirectRealCubicOrbit.lean`
- `SevenRealCubicThetaSeventhPower.lean`

Astra-002 has already kernel-checked the decisive source-sensitive exclusion:

```text
W != rho.
```

R47 is not a research checkpoint. It is a focused promotion checkpoint:
move that checked bridge from scratch into one independent production module,
attach facade/API/axiom/client coverage, and preserve the exact provenance.

Do not mix the separate `q % 7 = 1` bridge into this checkpoint.

## Part A — new production module

Create:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCalibrationExclusion.lean
```

Preferred sole project import:

```lean
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet
```

Do not import PairedDeepJet or R45 depth-amplification modules unless the
reference scratch unexpectedly depends on them after cleanup.

Namespace:

```text
DkMath.FLT.Seven.SevenRealCubic
```

Retain the same original:

```text
source
r
p
h
```

throughout.

## Part B — exact public endpoint

Promote the following theorem, preserving the current theorem shape:

```lean
theorem directOrbitDeepJetWUnit_ne_calibration
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitDeepJetWUnit h.squareRefinement eta ≠
      directOrbitDeepJetRho
```

This is the mandatory R47 endpoint.

Do not strengthen it to contradiction for all C=1 packets.

## Part C — source-tail direction

Keep the helper private unless a second concrete consumer already exists.

Prove:

```text
theta^35 * thetaSevenUnit^12
  = -7^11 * (2 + alpha + alpha^2).
```

Preferred route:

1. compute
   `theta^2 * thetaSevenUnit = -(2 + alpha + alpha^2)`;
2. regroup
   `theta^35 * thetaSevenUnit^12` as
   `(theta^3 * thetaSevenUnit)^11 * (theta^2 * thetaSevenUnit)`;
3. use
   `7 = theta^3 * thetaSevenUnit`.

Do not directly expand the 35th power.

## Part D — source seventh-power plane identity

From the original packet theorem

```text
p.source_eq_pow
```

and the exact current source tail, prove

```text
(p.rho^7).snd = (p.rho^7).thd.
```

This is the provenance-sensitive input that the R40–R46 normalized surface
did not retain.

Do not replace it by a trace-plane or norm-one condition.

## Part E — calibration defect polynomial

Define privately unless reuse justifies public exposure:

```text
F(a,K)
  = 3*a^5
  + 40*a^4*K
  + 295*a^3*K^2
  + 1293*a^2*K^3
  + 3145*a*K^4
  + 3278*K^5.
```

Prove the exact coefficient defect:

```text
((a,K,K)^7).snd - ((a,K,K)^7).thd
  = -49*K^2*F(a,K).
```

Reuse:

```text
thetaLinear_pow_seven
thetaSquare_pow_seven
```

rather than introducing a second unrestricted seventh-power expansion.

## Part F — impossible calibration line

Prove the neutral internal lemma:

Assume

```text
K != 0
7 | K
thetaResidue (a,K,K) != 0
((a,K,K)^7).snd = ((a,K,K)^7).thd.
```

Then derive `False`.

Required proof order:

1. use the exact defect to get
   `-49*K^2*F(a,K)=0`;
2. cancel the nonzero integer factor `-49*K^2` **over ℤ**;
3. only then cast `F(a,K)=0` to `ZMod 7`;
4. use `7 | K` so the residue equation becomes
   `3*a^5=0`;
5. deduce `a=0 mod 7`;
6. combine with `K=0 mod 7` to contradict the theta residue.

Do not cast before cancelling the factor 49.

## Part G — recover the calibration line from the orbit gap

From

```text
sigma(x)-x = K*theta^2*rho
```

prove

```text
x = (x.fst, K, K).
```

Use exact coordinates of `rotateEquiv`, `theta^2`, and `rho`.

Do not infer this from norm or projective class.

## Part H — instantiate the current C=1 provenance

Assume the public theorem's hypotheses and, for contradiction,

```text
W = rho.
```

Set

```text
n := directOrbitDeepJetExponent h.squareRefinement
K := 7^n * h.u^14
```

over integers.

Prove:

```text
K != 0
7 | K.
```

Use:

- positivity of `h.u`;
- positivity/nonzeroness of the exponent;
- the existing deep-jet normalization;
- the C=1 gap scalarization.

Recover:

```text
rotateEquiv p.rho - p.rho
  = K * theta^2 * rho.
```

Apply Parts D/G/F together with

```text
p.thetaResidue_ne_zero
```

to close the contradiction.

## Part I — integration

Add the module to the public FLT7 facade in the repository's current import
ordering.

Add:

- focused API audit;
- focused axiom audit;
- R47 client regression.

The Astra scratch may remain as research provenance, but the regression test
should consume the production theorem rather than duplicate the full proof.

Update:

- `report-053.md`;
- `ROADMAP.md`.

## Part J — immediate corollary audit

After the public theorem is green, check whether the existing R45 wrapper can
yield, without adding heavy dependencies, a clean corollary of the form:

```text
W = rho * t^(7^9)
-> t^(7^9) != 1
```

or equivalently under the exact current unit equality,

```text
t^(7^9) ≠ 1.
```

This is optional for R47.

Promote it only if the dependency direction remains clean and the theorem is
a one-line consequence. Do not import PairedDeepJet into the new calibration
module merely to state it.

## Hard stops

- No claim that C=1 is impossible.
- No claim that the full Thue surface has a unique solution.
- No claim that `t = 1` is the only torsion possibility unless the required
  torsion theorem is explicitly used and its hypotheses are checked.
- Do not add the separate `q % 7 = 1` theorem here.
- No further Hensel depth.
- No successor/descent construction.
- No historical terminal contradiction.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Validation

At minimum, run sequentially:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCalibrationExclusion
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCalibrationExclusionApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCalibrationExclusionAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCalibrationExclusionR47Scratch.lean
git diff --check
```

If the repository naming convention suggests a shorter client filename, use
the local convention but record the exact command in the report.

Print axioms for:

```text
directOrbitDeepJetWUnit_ne_calibration
```

Expected project-level audit:

```text
[propext, Classical.choice, Quot.sound]
```

Run forbidden-source/import scans on all decisive files.

## Report questions

1. Was the Astra scratch proof promoted without adding assumptions?
2. Does the production theorem retain the original source/r/p/h provenance?
3. Is the source seventh-power plane identity derived directly from
   `p.source_eq_pow`?
4. Is the defect factorization exact?
5. Is `-49*K^2` cancelled before reduction mod 7?
6. Is `K != 0` proved from current packet positivity?
7. Is `7 | K` proved without arbitrary-depth assumptions?
8. Is `p.thetaResidue_ne_zero` the final independent clash?
9. Does the public theorem avoid PairedDeepJet/R45 dependencies?
10. Are facade/API/axiom/client checks green?
11. Did any clean one-line high-power-correction corollary become available?

## Outcome

- Outcome A — public source-sensitive calibration exclusion is green and a
  clean current-wrapper corollary also shows the `7^9)-correction is
  nontrivial.
- Outcome B — public source-sensitive calibration exclusion is green; wrapper
  corollary is intentionally left for the consuming module.
- Outcome C — production proof is green but dependency cleanup/facade
  integration is the remaining frontier.
- Outcome D — the scratch depends on a hidden assumption not valid in
  production; document the exact gap and stop.
