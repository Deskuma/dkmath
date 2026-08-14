# IPSM-038 — CS14 closeout and CS15 finite geometric ray compression roadmap

## 1. Status

CS14 is Green-B.

`PascalCenteredXiPrimeSidePrimePowerRayAudit.lean` now provides the finite source rewrites required before any signed ray argument:

1. the natural von Mangoldt mode sum is restricted exactly to `canonicalPrimePowerSupportUpTo X`;
2. the canonical support is reindexed exactly by `pascalPrimePowerPairSupportUpTo X`;
3. the pair support is grouped by base prime into `pascalCenteredXiPrimeSideFinitePrimePowerRayKernel`;
4. on a prime-power label `p ^ j`, `Real.log (p ^ j) = j * Real.log p` is available in the phase bookkeeping;
5. the plus/minus phase frequencies advance by the constant step `-Real.log p` along one fixed base-prime ray;
6. the complex prime-power mode is identified with the natural-label complex power;
7. no ray sign, cancellation provider, infinite rearrangement, or RH consequence has been asserted.

The public `DkMath.RH` import includes the CS14 module.

## 2. Why CS15 should be geometric compression before signed cancellation

The next tempting step is to attack the sign of a prime-power ray directly. Do not do that yet.

For one fixed prime `p`, the CS14 ray is already a finite geometric source before taking real parts and before integrating in the right-edge height. Compressing that source first has three advantages:

1. it keeps all manipulations finite;
2. it replaces many oscillatory modes by one exact Euler-factor-type surface;
3. it exposes the true denominator/numerator geometry before a sign theorem is attempted.

The signed ray provider should therefore be postponed until after this exact compression layer is available.

## 3. Target module

Create a new chained module:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit
```

Suggested file:

```text
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideFiniteGeometricRayAudit.lean
```

Do not modify the already Green CS13 or CS14 modules except for compatibility fixes.

## 4. CS15-A — finite exponent support of one base prime

Name the positive-exponent support of one base prime under cutoff `X`.

A suitable shape is conceptually:

```lean
noncomputable def pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo
    (X p : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun k => p ^ (k + 1) ≤ X)
```

The exact name may differ.

Prove only finite combinatorial facts first:

* membership equivalence;
* every supported exponent is positive after translating `k` to `j = k + 1`;
* for prime `p`, support is downward closed in the exponent index;
* the support is therefore a finite prefix.

Do not guess a Mathlib `Nat.log` API unless it materially simplifies the proof. A prefix theorem stated using the support cardinality is acceptable and may be more robust under the current Mathlib v4.32.2 pin.

A preferred abstract endpoint is a theorem of the form

```text
Prime p -> exponentSupport X p = Finset.range m
```

for a canonically chosen finite `m` attached to `X,p`.

The precise indexing convention must be audited carefully because CS14 stores exponent index `k` but the natural prime power is `p ^ (k + 1)`.

## 5. CS15-B — pointwise geometric ratio on the right edge

For a complex point `s`, define or locally name the one-step prime ratio

```text
q_p(s) := (p : ℂ) ^ (-s)
```

For prime `p` and positive exponent `j`, prove the exact finite mode identity

```text
((p ^ j : ℕ) : ℂ) ^ (-s) = q_p(s) ^ j
```

Prefer reusing the already established `eulerPrimePowerMode_eq_primePower_cpow_neg` / complex `cpow` multiplication machinery rather than reproving complex-power algebra from scratch.

At the actual right-edge point

```text
s_t := pascalSymmetricRectangleRightEdge W.rectangle.σ t
```

the ratio becomes one geometric step along the entire fixed-`p` ray.

No infinite geometric series is allowed here.

## 6. CS15-C — finite complex ray amplitude before `re` and integration

Introduce a complex source-level ray amplitude before taking `Complex.re` and before interval integration.

Conceptually:

```text
RayAmplitude(ε,W,X,p,t)
  = sum over supported j of
      MellinWeight(ε,W,t) * ((p^j)^(-s_t))
```

The common factors `Real.log p` and the Mellin weight may either be included in this definition or kept as outer factors. Choose the form that yields the cleanest exact theorem.

Then prove that the existing CS14 real ray kernel is recovered by finite sum/integral linearity from this source amplitude.

This is a finite sum/interchange only. It is authorized. Do not introduce any infinite tail/integral exchange.

## 7. CS15-D — denominator-free finite geometric compression

This is the load-bearing algebraic target.

Do not begin with division by `1 - q`.

For the finite ray of length `m`, first prove the denominator-free identity

$$
(1-q)\sum_{j=1}^{m}q^j=q-q^{m+1}.
$$

Applied pointwise to the fixed prime ratio, the preferred theorem shape is conceptually

```text
(1 - q_p(s_t)) * PrimePowerRayGeometricCore
  = q_p(s_t) - q_p(s_t)^(m+1)
```

with all cutoff/index details explicit.

This theorem is purely finite algebra and requires no proof that `q_p(s_t) ≠ 1`.

If the implementation is easier with zero-based indexing, use

$$
(1-q)\sum_{k=0}^{m-1}q^{k+1}=q-q^{m+1}.
$$

Keep the theorem aligned with the actual CS14 `k + 1` convention.

## 8. CS15-E — optional quotient form on the safe right edge

Only after the denominator-free theorem is Green, optionally derive

$$
\sum_{j=1}^{m}q^j=\frac{q-q^{m+1}}{1-q}.
$$

This requires `q != 1`.

For the repository right edge `1 < σ` and prime `p`, this should follow from the fact that the modulus of `(p : ℂ)^(-s)` is strictly below one. However, do not spend CS15 on a large analytic detour if the exact nonzero theorem is awkward in Mathlib v4.32.2.

The denominator-free identity is already sufficient for Green-B.

If quotient form is proved, keep the nonzero proof source-derived from `p > 1` and the right-edge real part. Do not use a synthetic assumption `q != 1` in the public theorem unless it is explicitly marked as a generic algebra adapter.

## 9. CS15-F — phase-lattice compatibility

Connect geometric compression back to CS14 phase spacing.

For `p^j`, CS14 provides frequencies

$$
r_+(j)=\varepsilon-j\log p,
\qquad
r_-(j)=-\varepsilon-j\log p.
$$

Record that multiplication by one further `q_p(s_t)` advances the phase by exactly `-log p` and supplies the expected geometric damping on the right edge.

This should be a structural compatibility theorem, not a sign theorem.

The important conceptual identity is:

```text
prime-power phase lattice
<-> repeated multiplication by one complex ratio q_p(s_t)
```

This is the point where the CS13 oscillatory picture and the CS14 prime-power picture become the same object.

## 10. CS15-G — signed-ray frontier after compression

After geometric compression, audit the real signed projection of one ray.

Do not immediately claim a sign for the compressed quotient or numerator.

The correct questions are:

1. does the compressed numerator `q - q^(m+1)` have a useful pairing or square structure after multiplication by the Mellin boundary weight?
2. does the factor `1 - q` admit a source-derived positive-real-part or norm identity on the right edge?
3. can the real projection be rewritten as a CF2D/q2 quantity after the main analytic route is closed?
4. does cancellation occur within one fixed `p` ray, or only after summing several base primes?

If no independent sign mechanism is found, preserve a named gap such as

```lean
inductive PascalCenteredXiPrimeSideFiniteGeometricRayGap : Prop
  | signedRayCancellationProviderPending
```

Do not encode the desired sign as a provider assumption.

## 11. Important firewall: finite ray sign is still not the endpoint sign

Even a theorem that every finite prime ray has one sign does not by itself close the original CS8 upper-envelope problem.

Remember the established hierarchy:

```text
mode/ray sign
-> finite block or finite-tail ordering
-> finite approximant versus fixed-epsilon endpoint
+ independent finite-cutoff anchor
-> endpoint upper control
-> epsilon closure
```

The finite-cutoff anchor remains logically separate unless a future source identity joins the two.

Do not silently collapse these layers.

## 12. No-go list

CS15 must not introduce:

* an infinite geometric series;
* an infinite prime-power sum/interchange;
* a sum/integral exchange beyond finite `Finset` linearity;
* a fixed-`ε` defect sign theorem without a source-derived proof;
* an assumed ray-cancellation provider disguised as structure;
* an RH conclusion;
* a reverse, joint, or exchanged `X` / `ε` limit;
* cfcos/cfsin rewrites in the main proof path.

The CF2D trigonometric rewrite remains an optional post-closeout experiment.

## 13. Validation

Required checks:

```text
lake env lean <target-file>
lake build DkMath.RH
git diff --check
```

Also audit the new source for:

```text
sorry
axiom
native_decide
```

If `./lb` is absent in this checkout, record that fact and do not fabricate a result.

## 14. Green criteria

CS15 is Green-B when the branch contains, with successful Lean validation:

1. an exact finite exponent support for one base prime;
2. exact reindexing to a contiguous finite ray or an equally strong finite-support representation;
3. the pointwise `q_p(s)^j` prime-power mode identity;
4. a source-level complex finite ray amplitude;
5. exact recovery of the existing CS14 real ray kernel from that amplitude;
6. the denominator-free finite geometric identity;
7. phase-lattice compatibility;
8. any remaining signed cancellation recorded explicitly as a gap.

Quotient-form compression is desirable but optional.

## 15. Strategic interpretation

After CS14, the prime side is no longer merely a von Mangoldt-weighted collection of unrelated oscillatory modes.

For each primitive prime `p`, the entire finite prime-power family lies on one geometric orbit:

```text
p, p^2, p^3, ...
-> q_p, q_p^2, q_p^3, ...
-> equal log-phase spacing
-> geometric damping
```

CS15 should make that orbit an exact Lean object.

If this compression succeeds, the next genuine sign audit will no longer ask for cancellation among many individual `sin/cos` modes. It will ask whether one finite Euler-factor-type ray surface carries the required signed projection.

That is a substantially sharper frontier.