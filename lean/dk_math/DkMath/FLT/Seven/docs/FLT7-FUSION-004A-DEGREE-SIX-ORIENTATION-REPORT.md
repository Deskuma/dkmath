# FLT7-FUSION-004A degree-six orientation completion report

Date: 2026-07-30

## Result

The interrupted degree-six orientation stage is restored and builds
successfully. The local carrier and conjugate-prime pair are now exposed by
the public `DkMath.FLT.Seven` facade.

## Lean facts fixed in this stage

The concrete carrier
`SevenCyclotomicDegreeSixInt.Ring` is a quadratic algebra over
`SevenRealCubicInt`. Lean proves:

- explicit conjugate elements `zeta` and `zetaInv`;
- their quadratic relation and seventh-root identities;
- rank two over the real cubic order and rank six over `ℤ`;
- explicit `Fin 6` coordinates;
- a local evaluation extending every canonical real-cubic ratio address;
- the product of the two oriented linear carriers equals
  `ofReal (realPairCarrier 0)`;
- the oriented product is associated to the loaded core.

Thus the previously abstract `DegreeSixLocalRatioProvider` and
`AdditiveChartFrontierPacket` are inhabited by concrete data.

At every `CyclotomicLinearPrimeAddress`, the oriented and conjugate
evaluations give two ideals. Lean proves that they:

- are maximal;
- are distinct and comaximal;
- contain opposite oriented linear carriers;
- contract to the same real-cubic evaluation kernel;
- contract to `(q)` over `ℤ`;
- have residue quotient cardinality `q`.

Quadratic conjugation exchanges the two carriers and the two root
orientations.

## Prime-load valuation completion

The three cyclic real-cubic evaluation kernels split `(q)` completely. This
upgrades the earlier local upper bound to the unconditional equality

```text
evalKernelMultiplicity = padicValNat q addressedCell.
```

Over the finite prime support, the exact powers of the addressed kernels
multiply to the principal addressed-load ideal.

## Exact remaining obligation

Let `P` and `Pbar` be the two conjugate degree-one kernels and let `p` be
their common real-cubic contraction. Lean currently proves

```text
map(ofReal, p) <= P * Pbar.
```

Because `P` and `Pbar` are comaximal, exact fibre equality is equivalent to
the single reverse containment

```text
P * Pbar <= map(ofReal, p).
```

This is recorded as
`ConjugatePrimeFiberProductEqualityObligation`; it is not assumed or hidden.

## Error recovery

The interrupted file had three elaboration failures:

1. two conjugation lemmas left only commutativity of scalar multiplication;
2. conjugate-evaluation surjectivity used a witness from a different
   existential proof.

The first two goals are closed explicitly by commutativity. The surjectivity
proof now evaluates its displayed constant witness directly and uses the
canonical `ZMod` representative theorem.

## Verification boundary

The completed stage does not claim:

- that this quadratic algebra is the full degree-six ring of integers;
- exact conjugate-fibre product equality;
- a primitive reconstructed integer or quadratic Fermat chart;
- a strict well-founded decrease;
- an inhabited recursive descent provider;
- FLT7.

The next sound checkpoint is the reverse fibre containment or an equivalent
theorem that bypasses it while preserving the oriented local data. Only after
that bridge yields a primitive chart may the strict-drop and descent layers
resume.

## Checkpoint integration and continuation

This 004A checkpoint was integrated into `develop` by PR #73 at merge commit

```text
bac2a3b1f5881a4341138e7d47429c98ca9ca4b1
```

Further work no longer continues on `wip/FLT7-fusion-260729`. The focused
continuation branch is

```text
wip/FLT7-fusion-004b-conjugate-fiber-260730
```

and begins from the merged `develop` checkpoint. Its sole initial frontier is
`ConjugatePrimeFiberProductEqualityObligation` and the reverse fibre
containment displayed above.
