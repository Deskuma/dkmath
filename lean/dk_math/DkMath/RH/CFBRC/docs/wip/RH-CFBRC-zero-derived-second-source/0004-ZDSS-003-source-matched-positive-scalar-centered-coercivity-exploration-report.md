# ZDSS-003 — source-matched positive scalar / centered-coercivity exploration report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

## 0. Decision

The strongest proved state is:

```text
POSITIVE-SCALAR-UPPER-CLOSED
RATE-ASYMMETRY-IDENTIFIED
RH-EQUIVALENT-FRONTIER-IDENTIFIED
NEW-INFORMATION-OBSTRUCTION
```

The smallest natural positive scalar genuinely controlled by ZDSS-001 is

```text
E_K(s) = ||etaPairedPartial K s||^2
       + ||etaPairedPartial K (criticalMirror s)||^2.
```

Its U-side is complete: it is nonnegative, is exactly the existing finite
endpoint total energy at cutoff `2K`, has a separate-tail explicit upper
bound, and tends to zero at every nonreal standard nontrivial zeta zero.

No unconditional C-side lower bound with a quantitatively nonvanishing
coefficient was found. Norm imbalance and both Hermitian `+`/`-`
polarizations are bounded by the same collapsing total energy. The historical
mode Gap detects `centeredSigma`, but whole endpoint smallness does not control
its positive mode energy. The precise information retained by the mode
geometry is a cutoff rate: the raw mode Gap tends to zero throughout the open
strip, while its `(K+1)` normalization diverges at every off-critical point.

This checkpoint does not prove `RiemannHypothesis` and introduces no assumed
coercivity, endpoint-Gap-to-UnitGap provider, or modewise no-cancellation
hypothesis.

## 1. Repository APIs inspected

The audit compared declarations in the following groups.

### 1.1 Endpoint sources and tails

```text
etaPairedPartial
etaPairTail
etaPairTerm
etaPartialEndpoint_two_mul_eq_etaPairedPartial
etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
norm_etaPairedPartial_le_powerBound_of_nontrivialRiemannZetaZero
norm_etaPairedPartial_criticalMirror_le_powerBound_of_nontrivialRiemannZetaZero
```

### 1.2 Endpoint energy and polarization

```text
etaMirrorEndpointTotalEnergy
etaMirrorEndpointBig
etaMirrorEndpointGap
etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy
etaCriticalMirror_pairEnergy_tendsto_zero
EtaMirrorEndpointGapControlsUnitGapAt
etaMirrorEndpointGapControlsUnitGapAt_iff_re_eq_half
```

The last equivalence confirms that endpoint-Gap-to-UnitGap control is already
the critical-line frontier under the available endpoint limits. It was
inspected as a boundary and was not used as a provider.

### 1.3 Mode, increment, and rate geometry

```text
etaEndpointIncrementMirrorGap
etaEndpointIncrementMirrorEnergyUpTo
etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap
etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half
etaEndpointIncrementMirrorGap_tendsto_zero_iff_re_eq_half
etaMirrorAmplitudeGap_raw_zero_normalized_atTop
etaPairIndexNormalizedRotatedTail_tendsto_constant
```

The exact increment Gap is the prime-mirror offset Gap at mode `K+1` and
therefore sees `centeredSigma`. This fact is unconditional in `s`; it is not a
second consequence of the zeta-zero equation.

### 1.4 Historical positive horizontal detectors

```text
primeMirrorOffsetGap
primeMirrorEnergy
primeMirrorEnergy_nonneg
primeMirrorEnergy_eq_zero_iff_delta_eq_zero
cfzpAggregateMirrorGapUpTo
cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam
```

These objects have a valid C-side. No exact bridge was found from the two
whole endpoint values or their total energy to these sums of nonnegative
modewise energies.

## 2. Implemented scalar and exact U-side

The new module
`ZeroDerivedDualEndpointPositiveScalarCoercivityAudit.lean` defines

```lean
etaDualEndpointTotalEnergy K s
etaDualEndpointPowerUpperBound K s.
```

The exact finite characterization is

```lean
etaDualEndpointTotalEnergy K s =
  etaMirrorEndpointTotalEnergy (2 * K) s.
```

For `hs : NontrivialRiemannZetaZero s`, `him : s.im != 0`, and `1 <= K`, Lean
proves

```text
etaDualEndpointTotalEnergy K s
  <= (||s|| * K^(-s.re) / s.re)^2
     + (||criticalMirror s||
          * K^(-re (criticalMirror s))
          / re (criticalMirror s))^2.
```

Both exponents are positive in the denominator on the open critical strip,
so the explicit upper bound tends to zero. Independently, the exact even
cutoff characterization transports the existing two-endpoint energy limit to

```lean
etaDualEndpointTotalEnergy_tendsto_zero_of_nontrivialRiemannZetaZero.
```

These are Lean-proved facts. The power majorant is an upper estimate only; no
reverse estimate or asymptotic equivalence is claimed.

## 3. Candidate table

| Candidate | Exact U-side status | Exact C-side status | Decision |
|---|---|---|---|
| A. `||A_K||^2 + ||B_K||^2` | Nonnegative; separate-tail explicit upper bound; upper bound and scalar tend to `0` at a nonreal zero | No lower trace of `centeredSigma` proved | Accepted reusable Core |
| B. `(||A_K|| - ||B_K||)^2` | Proved `<= E_K`; hence tends to `0` at a nonreal zero | Upper bounds on both norms do not give a lower norm imbalance; internal cancellation remains | Degenerates on U-side |
| C1. `||A_K + B_K||^2` | Proved `<= 2 E_K`; hence tends to `0` | Polarization cross term has no independent sign/lower bound | Degenerates on U-side |
| C2. `||A_K - B_K||^2` | Proved `<= 2 E_K`; hence tends to `0` | This is the old antisymmetric P2-F projection; no new source coordinate | Old information |
| D. Positive mode energy from endpoint modes | Historical mode energy is finite and nonnegative | No theorem turns small whole endpoint sums into a sum of mode norm-squares | Source bridge absent |
| E. Raw or normalized mode Gap | Raw Gap tends to `0` throughout the open strip; normalized Gap exactly detects the critical line | Off critical, `(K+1) * rawGap -> +infinity`; zero-derived endpoint convergence does not control this normalization | Rate asymmetry found; U/C bridge absent |
| F. `primeMirrorEnergy` / aggregate Gap | Positive and exactly centered-coercive in its own mode coordinates | No exact endpoint-source upper bound; importing collapse would be circular | Comparison target only |

## 4. Where the horizontal coordinate is visible

### 4.1 Lean-proved facts

At the whole-endpoint level, `E_K` is exactly a sum of squared norms of two
finite complex sums. Neither its diagonal terms nor the `+`/`-` polarization
identities produce a sign-controlled cross term involving
`centeredSigma s.re`.

At the individual increment/mode level, the mirror amplitude ratio consists
of the mirror exponents `s.re` and `1-s.re`. The normalized increment Gap is
exactly a positive horizontal detector, and

```text
normalizedGap_K = (K+1) * rawGap_K.
```

For a hypothetical off-critical standard zero the new theorem

```lean
etaMirrorAmplitudeGap_zero_normalized_atTop_of_nontrivialRiemannZetaZero_offCritical
```

packages the compatible pair of conclusions

```text
rawGap_K -> 0,
(K+1) * rawGap_K -> +infinity.
```

### 4.2 Repository-derived inference

The two-source structure repairs the outer projection loss

```text
(A_K, B_K) -> B_K - A_K,
```

but not the inner aggregation loss inside either finite sum. Passing from
whole endpoint smallness to positive mode energy would require a new exact
orthogonality, Gram lower bound, or source-specific no-cancellation theorem.
No such declaration was found.

The centered coordinate is therefore visible in a mode ratio/rate, not in a
currently controlled whole-endpoint diagonal or cross term.

### 4.3 Heuristic direction, not a proved result

The different tail exponents suggest auditing log-slopes or two-sided
normalized asymptotics of the two separate tails. Upper power bounds alone do
not identify those slopes, and a normalization depending on `s.re` would not
by itself create coercivity. Any future rate observable must be extracted by
an exact source theorem rather than inserted into a definition.

## 5. Exact RH-equivalent frontier

The new obstruction theorem is

```lean
re_eq_half_of_eventually_dualEndpoint_uniform_centered_coercivity
```

with schematic hypothesis

```text
c > 0,
eventually c * centeredSigma(s.re)^2 <= E_K(s).
```

For a nonreal standard zero, `E_K(s) -> 0`; closedness of order under the
limit forces `c * centeredSigma(s.re)^2 <= 0`, hence
`centeredSigma(s.re) = 0` and `s.re = 1/2`.

This is a Lean-proved conditional frontier theorem, not a coercivity provider.
The module supplies no inhabitant of its lower-bound hypothesis. It precisely
classifies any fixed positive centered lower coefficient as RH-load-bearing.

The historical
`etaMirrorEndpointGapControlsUnitGapAt_iff_re_eq_half` gives the analogous
qualitative frontier. Neither frontier is used to assert RH.

## 6. Strongest accepted theorem chain

The accepted chain is:

```text
NontrivialRiemannZetaZero s and s.im != 0
  -> separate exact identities A_K = -tail_s(K), B_K = -tail_mirror(K)
  -> separate norm power bounds
  -> E_K = ||A_K||^2 + ||B_K||^2
  -> 0 <= E_K <= explicit dual power upper bound
  -> E_K -> 0
  -> norm imbalance -> 0
  -> ||A_K + B_K||^2 -> 0 and ||A_K - B_K||^2 -> 0.
```

The missing arrow is:

```text
E_K small
  -/-> source-derived positive lower information for centeredSigma(s.re).
```

This absence is not encoded as an axiom. It is documented by the candidate
comparison and the exact fixed-coefficient frontier theorem.

## 7. Axiom audit and validation

The load-bearing declarations are inspected with `#print axioms` in the new
module. The output contains only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` occurs.

Validation from `lean/dk_math`:

```text
lake build DkMath.RH.CFBRC.ZeroDerivedDualEndpointPositiveScalarCoercivityAudit
./lean-build.sh DkMath.RH.CFBRC.ZeroDerivedDualEndpointPositiveScalarCoercivityAudit
lake build DkMath.RH
git diff --check
```

All commands passed.

The aggregate `DkMath.RH` build replayed pre-existing warnings from unrelated
modules, including an existing declaration using `sorry`; no new warning or
`sorryAx` came from the ZDSS-003 module.

## 8. Unresolved gap and recommended next checkpoint

The unresolved mathematical gap is an exact source-preserving passage from
the two whole endpoint equations to a quantitatively nonvanishing horizontal
detector. The candidate audit localizes it to one of two missing ingredients:

```text
1. an actual-source Gram/no-cancellation lower theorem for Eta modes; or
2. a zero-derived rate theorem strong enough to control the normalized
   increment Gap, rather than only the raw endpoint values.
```

The recommended next checkpoint is a **dual-tail rate-extraction and
normalized-mode bridge audit**. It should test whether existing normalized
ordinary tail asymptotics yield a two-sided, source-derived rate observable
for each endpoint and whether that observable controls the exact normalized
increment Gap. If they do not, the checkpoint should prove the sharpest
rate-information obstruction rather than returning to the closed
positive-density/current-majorant route.

No DkReal shrinking interval or RH wrapper should be attempted before one of
these two C-side ingredients is proved independently.
