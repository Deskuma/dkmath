# ZDSS-004 — dual-tail rate extraction / normalized-mode bridge exploration report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

## 0. Decision

The strongest exact classification is:

```text
TWO-SIDED-TAIL-RATE-FOUND
RATE-OBSERVABLE-FOUND
PARTIAL-RATE-BRIDGE
RATE-INFORMATION-OBSTRUCTION
SOURCE-ASYMPTOTIC-GAP
```

The two zero-derived endpoint sources have genuine nonzero normalized rate
limits. For each endpoint, multiplication by its own natural power and a unit
pair-frame rotation gives a finite nonzero limit. This is stronger than the
one-sided power upper bounds used in ZDSS-003.

The exact comparison with the normalized mode detector is nevertheless
negative. For all sufficiently large cutoffs of a nonreal standard zero,

```text
rawEndpointNormRatio_K
  = endpointIncrementMirrorRatio_K
      * selfNormalizedEndpointNormRatio_K,
```

and the self-normalized endpoint ratio tends to a finite positive constant.
Thus the off-critical power in the increment-mode ratio is not removed by the
two tail asymptotics. It is transported directly into the raw ratio of the two
whole endpoint norms.

No normalized-Gap boundedness, cofinal boundedness, non-divergence, or
`O(1/K)` raw-Gap estimate was obtained. This checkpoint does not prove
`RiemannHypothesis` and introduces no assumed U2 provider.

## 1. Trusted ZDSS spine

ZDSS-001 supplies, for

```lean
hs : NontrivialRiemannZetaZero s
him : s.im != 0,
```

the separate exact identities

```text
A_K(s) = etaPairedPartial K s
       = -etaPairTail K s,

B_K(s) = etaPairedPartial K (criticalMirror s)
       = -etaPairTail K (criticalMirror s).
```

ZDSS-003 defines

```text
E_K(s) = ||A_K(s)||^2 + ||B_K(s)||^2
```

and proves a separate-tail power upper bound and `E_K(s) -> 0`. It also
identifies the existing mode-rate boundary:

```text
rawGap_K(s) -> 0
```

throughout the open strip, while the `(K+1)`-normalized Gap diverges off the
critical line.

ZDSS-004 preserves those facts and investigates only the missing `U1 -> U2`
passage.

## 2. Target normalized-Gap dichotomy

The existing exact mode detector is

```lean
etaEndpointIncrementMirrorGap s K.
```

Writing `q = K+1` and `delta = centeredSigma s.re`, the repository proves

```text
G_K(s) = q^(2*delta) + q^(-2*delta) - 2.
```

Consequently:

```text
s.re = 1/2  -> G_K(s) = 0 for every K,
s.re != 1/2 -> G_K(s) -> +infinity.
```

The corresponding ratio before applying `r + r^-1 - 2` is

```text
etaEndpointIncrementMirrorRatio s K = q^(2*delta).
```

This is an unconditional `U0` mode identity and a complete `C` detector. The
research question was whether zero-derived tail rates force any U2
anti-divergence property for this sequence.

## 3. Mandatory normalized-tail API audit

The main declaration inspected was

```lean
etaPairIndexNormalizedRotatedTail_tendsto_constant.
```

Its normalized tail is exactly

```text
q^(z.re) * etaPairBaseRotation z K * etaPairTail q z,
q = K+1.
```

The limit is the explicit complex constant

```text
etaPairIndexNormalizedTailConstant z
  = (1/2) * ((1/2)^(z.re) : Complex).
```

The audit found:

- the theorem assumes only `0 < z.re`; it is `U0`, not zero-derived;
- it is an actual complex limit, not merely an upper bound;
- the limit is nonzero for every complex `z`;
- the Euler remainder after normalization has an explicit `O(1/K)` norm
  majorant and tends to zero;
- `etaPairBaseRotation` has norm one, so rotation preserves all amplitude
  information;
- the theorem applies independently to `s` and `criticalMirror s` in the open
  critical strip;
- the zero-derived identities transport the two tail limits to the two finite
  partials with a minus sign.

The two endpoint constants can be compared, but their comparison is governed
by the already present exponents `s.re` and `1-s.re`. No equality between the
two constants is supplied by the simultaneous zero equations.

## 4. New Lean implementation

The focused module is

```text
ZeroDerivedDualTailRateNormalizedModeBridgeAudit.lean.
```

### 4.1 Normalized finite partials

The module defines

```lean
etaPairIndexNormalizedRotatedPartial
etaPairIndexNormalizedPartialNorm.
```

The first exact source theorem is

```lean
etaPairIndexNormalizedRotatedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero.
```

It proves pointwise that the normalized partial is the negative normalized
tail. The transported limit is

```lean
etaPairIndexNormalizedRotatedPartial_tendsto_neg_constant_of_nontrivialRiemannZetaZero.
```

Taking norms gives

```lean
etaPairIndexNormalizedPartialNorm_tendsto_constantNorm_of_nontrivialRiemannZetaZero.
```

The limiting norm is nonzero. Therefore this is exact two-sided rate
information, not only a big-O upper estimate.

The theorem

```lean
etaDualEndpointNormalizedRateCertificate_of_nontrivialRiemannZetaZero
```

packages the original and mirror complex limits and both nonvanishing facts.
This certificate is classified `U1`; it deliberately has no normalized-Gap
field.

### 4.2 Self-normalized endpoint ratio

The module defines

```text
R_K(s)
  = [(K+1)^(re (criticalMirror s)) * ||B_(K+1)(s)||]
      /
    [(K+1)^(s.re) * ||A_(K+1)(s)||].
```

Lean proves

```lean
etaDualEndpointNormalizedNormRatio_tendsto_limit_of_nontrivialRiemannZetaZero
```

with limit

```text
||etaPairIndexNormalizedTailConstant (criticalMirror s)||
  / ||etaPairIndexNormalizedTailConstant s||.
```

The theorem

```lean
etaDualEndpointNormalizedNormRatioLimit_pos
```

proves that this limit is strictly positive.

### 4.3 Exact source/mode ratio factorization

For any index at which the original partial is nonzero, Lean proves

```lean
etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio.
```

In symbols:

```text
||B_(K+1)|| / ||A_(K+1)||
  = etaEndpointIncrementMirrorRatio s K * R_K(s).
```

The proof uses only positive-base real-power algebra and the exact mode ratio

```text
etaEndpointIncrementMirrorRatio s K
  = (K+1)^(2 * centeredSigma s.re).
```

At a nonreal standard zero, eventual nonvanishing of the original partial is
derived from its nonzero normalized limit. Hence

```lean
eventually_etaDualEndpointRawNormRatio_eq_incrementRatio_mul_normalizedNormRatio_of_nontrivialRiemannZetaZero
```

supplies the factorization eventually without assuming monotonicity or
no-cancellation.

## 5. Candidate rate observable table

| Candidate | Level | Exact outcome | U2 consequence |
|---|---|---|---|
| Natural normalized original/mirror partials | `U1` after `partial = -tail` | Both converge after unit rotation to explicit nonzero constants | None; compatible with off-critical exponents |
| Normalized partial norms | `U1` | Each tends to a positive constant; gives two-sided individual rate | Does not compare endpoints on one common scale |
| Self-normalized endpoint norm ratio `R_K` | `U1` | Tends to a finite positive constant | Does not bound the mode ratio; it divides out exactly the horizontal power |
| Consecutive cutoff differences | `U0` | Exact appended Eta mode; zero identity rewrites it as a tail difference | No extra zero-specific mode constraint found |
| Multiplicative/sparse cutoff quotient | `U1` consequence of regular rate | Expected to recover the individual exponent | Exponent recovery is compatible with every open-strip `s.re` |
| Log-slope of endpoint norms | `U1` consequence after eventual nonvanishing | The nonzero normalized norm limit is enough in principle to recover `-s.re` and `-(1-s.re)` | Re-reads the existing exponents; no equality constraint |
| Direct raw endpoint ratio | `U1` plus exact `U0` factorization | Equals mode ratio times `R_K` eventually | Carries the same off-critical divergence rather than bounding it |
| Normalized increment Gap | `U0` and `C` | Zero on the critical line, tends to `+infinity` off it | Desired anti-divergence remains absent |
| Abel/Euler remainder structure | `U0` | Supplies the nonzero normalized-tail asymptotic and `O(1/K)` normalized remainder | No positive Gram/no-cancellation bridge to mode energy |

Scale quotients and log slopes were not given additional Lean definitions:
the stronger normalized norm limit already records their relevant rate
content, and those reformulations do not create U2 information.

## 6. Exact compatibility obstruction

The structure

```lean
EtaDualEndpointRateNormalizedGapCompatibilityCertificate
```

collects:

```text
1. both nonzero zero-derived normalized endpoint rates;
2. R_K(s) -> a finite positive constant;
3. the eventual exact source/mode ratio factorization;
4. G_K(s) -> +infinity.
```

The theorem

```lean
etaDualEndpointRateNormalizedGapCompatibilityCertificate_of_offCriticalZero
```

builds all four facts simultaneously under the hypothetical off-critical-zero
case. This is not an existence theorem for an off-critical zero. It is an
exact implication showing that the currently extracted U1 data do not
contradict the repository's U2 divergence conclusion.

The obstruction is sharper than merely saying that upper bounds are too weak:
even the actual nonzero two-sided tail rates remain compatible with
off-critical normalized-Gap divergence.

## 7. Information-level accounting

| New theorem family | Level | Information added |
|---|---|---|
| normalized partial equals negative normalized tail | `U1` characterization | Connects the unconditional tail object to the zero-derived endpoint source |
| normalized complex/norm limits | `U1` | Exact nonzero two-sided rates for each endpoint |
| normalized endpoint ratio limit | `U1` | Phase-free finite positive relative rate after separate normalization |
| raw/source-mode ratio factorization | exact `U0` algebra, eventually available at `U1` zeros | Locates the horizontal power in the unnormalized cross-endpoint ratio |
| normalized Gap divergence inside compatibility certificate | `U2` conditional on off-critical coordinate | Demonstrates coexistence, not zero-derived control |

No theorem of the following types was obtained:

```text
eventually G_K(s) <= C,
cofinally G_K(s) <= C,
not Tendsto G atTop atTop,
rawGap_K(s) = O(1/K),
rawGap_K(s) = o(1/K).
```

## 8. Why the plausible bridge loses information

The natural separate normalizations are

```text
(K+1)^(s.re)       * ||A_(K+1)||,
(K+1)^(1-s.re)     * ||B_(K+1)||.
```

Both converge to positive constants. Dividing them produces a bounded
quantity because each endpoint is normalized by a different exponent. When
the normalization is undone, the missing power is exactly

```text
(K+1)^(s.re-(1-s.re))
  = (K+1)^(2 * centeredSigma s.re),
```

which is the increment-mode ratio itself.

Thus separate tail asymptotics determine the two rates but supply no reason
for those rates to coincide. An argument asserting that their ratio is
bounded on the raw common scale would add precisely the critical-line
information still missing.

Whole-tail cancellation is no longer the only issue at this checkpoint. The
stronger obstruction is that the correct individual asymptotics themselves
allow unequal mirror exponents.

## 9. Dependency and axiom audit

The new module uses:

```text
ZeroDerivedDualEndpointPositiveScalarCoercivityAudit
EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
PrimeMirrorEtaAsymptoticDichotomy
```

and their accepted upstream source declarations. It does not use
endpoint-Gap-to-UnitGap control, dominant endpoint rate-collapse providers,
completed-zeta orbit-collapse providers, or a new axiom.

Every load-bearing theorem is inspected with `#print axioms`. The output is:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, `native_decide`, or new axiom occurs in the module.

Validation from `lean/dk_math`:

```text
lake build DkMath.RH.CFBRC.ZeroDerivedDualTailRateNormalizedModeBridgeAudit
./lean-build.sh DkMath.RH.CFBRC.ZeroDerivedDualTailRateNormalizedModeBridgeAudit
lake build DkMath.RH
git diff --check
```

All commands passed. The aggregate build may replay pre-existing warnings from
unrelated modules; none originates in the ZDSS-004 module.

## 10. Smallest remaining mathematical obligation

The remaining obligation is not another separate endpoint rate theorem. It is
an independent cross-endpoint source relation on a common scale that prevents
the exact factor

```text
(K+1)^(2 * centeredSigma s.re)
```

from surviving in the raw endpoint ratio or normalized mode Gap.

Any one of the following would suffice if proved from accepted zero data:

```text
1. a bounded or cofinally bounded raw endpoint norm ratio;
2. a same-scale nonzero comparison of the two endpoint tails;
3. a finite-truncation functional-equation relation controlling the mode
   ratio, not merely transporting the two complete zeros;
4. an actual-source Gram/no-cancellation identity that bounds the normalized
   increment Gap.
```

Each is RH-load-bearing in the presence of the proved positive limit of
`R_K(s)` and must therefore have independent provenance.

## 11. Recommended next checkpoint

The recommended next checkpoint is a **same-scale cross-endpoint coupling
source audit**. It should inspect whether the functional equation,
completed-zeta first-order data, or another independently zero-derived finite
identity relates the original and mirror tails at one common normalization.

The first test should be explicit: can accepted source data bound the raw
endpoint norm ratio along all large cutoffs or a cofinal subsequence? By the
new exact factorization, a positive answer immediately yields anti-divergence
of the mode ratio and should be connected to the existing critical-line
dichotomy. A negative audit should record the precise missing cross-endpoint
provider instead of reopening unnormalized energies or the closed
positive-density/current-majorant route.
