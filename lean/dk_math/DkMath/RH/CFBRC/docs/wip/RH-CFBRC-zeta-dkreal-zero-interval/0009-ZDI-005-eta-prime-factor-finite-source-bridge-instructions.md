# ZDI-005 — Eta prime-factor finite source bridge instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`
- `0004-ZDI-002-DkReal-common-shrinking-interval-uniqueness-report.md`
- `0006-ZDI-003-finite-prime-certificate-source-audit-report.md`
- `0008-ZDI-004-zero-derived-finite-tail-source-recovery-report.md`

## Goal

Test one deliberately small route to the first genuine prime-derived P2 bridge without constructing a new analytic continuation theorem.

The route is:

```text
nontrivial zeta zero
  -> existing T1 Eta finite-partial + tail identity
  -> rewrite every finite Eta natural-index term through exact finite prime factorization
  -> finite prime-log observable = - existing Eta tail
```

The task is to determine whether the finite Eta main term can be exposed exactly as a finite prime-factor / prime-log observable on the same critical-strip domain where T1 already holds.

This is not yet an RH proof and not yet a shrinking-coordinate estimate.

## Why this route is being tested first

ZDI-004 established that the currently implemented prime PHZ / von Mangoldt convergence route first enters the analytic identity

```text
finite PHZ cutoff -> -zeta'/zeta
```

under `1 < s.re`, while a nontrivial zero lies only in `0 < s.re < 1`, and `-zeta'/zeta` cannot be evaluated at the zero itself.

By contrast, every finite Eta term is already defined for arbitrary complex `s` by

```lean
etaUnsignedVector s m = ((m + 1 : ℕ) : ℂ) ^ (-s)
```

and every positive natural number has a finite prime factorization. Therefore the finite Eta main term may admit a prime-source exposure using only finite algebra and logarithms, with no Euler-product convergence argument.

## Fixed trusted ingredients

### T1 zero-derived finite-plus-tail identity

Reuse:

```lean
etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
```

with hypotheses

```lean
hs  : NontrivialRiemannZetaZero s
him : s.im ≠ 0
K   : ℕ
```

The `him` hypothesis is independently available from `hs` through the audited S0 theorem and may be discharged where appropriate.

Do not re-prove the Eta convergence machinery.

### Finite prime-factor log identity

Reuse:

```lean
DkMath.NumberTheory.PrimitiveSet.sum_factorization_mul_log_eq_log_nat
```

which proves for `n ≠ 0`:

```text
Σ p in n.factorization.support,
  v_p(n) * log p
= log n.
```

This is an exact finite identity based on `Nat.factorization` and `Nat.prod_factorization_pow_eq_self`.

### Eta finite source decomposition

Reuse:

```lean
etaCriticalMirrorDefectPairTerm_eq_etaPairTerm_sub
etaCriticalMirrorDefectPairedPartial_eq_etaPairedPartial_sub
```

and the existing definitions of `etaUnsignedVector`, `etaSignedVector`, `etaPairTerm`, and the paired defect partial.

## Primary theorem target: one natural Eta mode

First prove the smallest generic theorem for a positive natural base.

Preferred semantic shape:

```lean
theorem natCpowNeg_eq_exp_factorization_logSum
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-s) =
      Complex.exp
        (-s *
          (((n.factorization.support.sum fun p =>
              (n.factorization p : ℝ) * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  ...
```

The exact syntactic orientation may be adjusted to fit Mathlib APIs.

Prefer proving this directly from:

- `Complex.cpow_def_of_ne_zero` or the existing positive-natural cpow API;
- `Complex.natCast_log` where useful;
- `sum_factorization_mul_log_eq_log_nat`.

Do not introduce a new prime-factor source definition merely to make the equality easy. If a helper definition is genuinely useful, it must receive an immediate characterization theorem whose right-hand side is the explicit factorization-support sum.

For `n = m + 1`, positivity is automatic.

## Second target: Eta unsigned vector prime-log exposure

Derive a theorem of the form

```lean
theorem etaUnsignedVector_eq_primeFactorLogExp
    (s : ℂ) (m : ℕ) :
    etaUnsignedVector s m =
      Complex.exp
        (-s *
          ((((m + 1).factorization.support.sum fun p =>
              ((m + 1).factorization p : ℝ) * Real.log (p : ℝ)) : ℝ) : ℂ)) := by
  ...
```

Again, exact syntax may be simplified.

The important semantic fact is that the natural-index mode is represented by a finite sum over the genuine prime-factor support of `m + 1`.

## Third target: finite paired Eta source rewritten through prime factors

Lift the one-mode equality through the existing finite Eta pair and defect sums.

Preferred outcome:

1. an exact theorem for `etaPairTerm s k` in which both natural bases `2*k+1` and `2*k+2` are exposed through their finite factorization-support prime-log sums;
2. an exact theorem for `etaCriticalMirrorDefectPairTerm s k` as mirror prime-log pair minus original prime-log pair;
3. an exact theorem for `etaCriticalMirrorDefectPairedPartial K s` as a finite `Finset.range K` sum of those prime-factorized defect-pair terms.

Avoid large new structures. A direct theorem with a local `let` or an existing expression is preferable.

## P2 candidate theorem

If the finite rewrite succeeds, combine it with T1 to prove one theorem whose hypotheses begin with a standard nontrivial zeta zero and whose finite left-hand side is explicitly prime-factor derived.

Schematic target:

```text
hs : NontrivialRiemannZetaZero s
K  : ℕ

finitePrimeFactorEtaMirrorDefectMain K s
  = - etaCriticalMirrorDefectPairTail K s
```

The finite left-hand side must be definitionally or theoremically characterized as a finite expression over `Nat.factorization.support` and prime logarithms. It must not contain `riemannZeta s` as a multiplicative factor.

If a named finite observable is introduced, require both:

```text
characterization theorem
zero-provenance theorem
```

before classifying it as P2.

## Classification rule

If the route succeeds, classify the result carefully as:

**P2-F — finite prime-factor source bridge**

rather than silently identifying it with the previously sought linear PHZ/von-Mangoldt P2.

P2-F means:

- zero provenance comes from T1 and hence ultimately from the zeta zero;
- the finite main term is exactly reconstructed from finite prime factorizations of its natural-index terms;
- no `Re(s) > 1` Euler-product convergence or zero-point log derivative is used.

It does **not** yet mean:

- the finite main is a linear sum over prime powers with von Mangoldt weight;
- the Eta tail is prime-only;
- a bound on `centeredSigma s.re` has been obtained;
- RH has advanced beyond the source-provenance frontier quantitatively.

If this distinction is mathematically too weak to count as P2, record that explicitly and classify it as a new intermediate `A2-F` instead. Do not inflate the classification for progress credit.

## Quantitative follow-up audit

After obtaining the exact finite prime-factor rewrite, do not launch a long estimate chain.

Only inspect whether the already proved Eta tail majorant can be attached directly:

```lean
norm_etaCriticalMirrorDefectPairTail_le_powerBound
```

or an existing projected-tail bound.

If so, record the immediate corollary

```text
norm(finite prime-factor Eta main)
  <= existing Eta tail power bound.
```

This may be called a `Q2-F` candidate only if the finite left-hand side is already characterized prime-factorially.

Do not yet attempt to infer `|centeredSigma s.re| <= q_K` unless a separately proved lower/coercivity estimate for that finite observable is already available.

## Mandatory non-circularity checks

The final P2-F candidate must not depend on:

- `RiemannHypothesis`;
- universal standard-zeta `map_zero`;
- any theorem proved equivalent to RH;
- fixed-Xi defect vanishing;
- endpoint balance;
- moving-line assimilation or `*_research_goal`;
- a new strip or growth provider;
- `sorryAx`.

Run `#print axioms` on the final one-mode factorization theorem and the final zero-derived prime-factor finite-tail theorem.

## Stop conditions

Stop and report rather than changing route if any of the following occurs.

1. The cpow-to-prime-factor rewrite requires an unproved branch identity that is not valid for positive natural bases.
2. A proposed prime-factor observable is merely defined to equal the old Eta partial without an independent factorization characterization.
3. The only way to connect the rewritten finite term to the zero is to import an RH-equivalent provider.
4. The rewrite is formally correct but exposes no more arithmetic information than `log n` and cannot be used with any existing tail estimate; classify it honestly and stop.
5. A new analytic continuation theorem becomes necessary. That belongs to a different route and must not be smuggled into ZDI-005.

## Suggested module

If new reusable Lean theorems are needed, prefer a small module such as:

`DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorFiniteSourceBridge`

Import only the smallest Eta finite/T1 dependencies and the generic factorization-log theorem needed.

Do not modify the historical Eta modules except for narrowly justified docstrings.

## Required report

Create:

`0010-ZDI-005-eta-prime-factor-finite-source-bridge-report.md`

The report must state:

1. whether the one-natural-mode prime-factor cpow identity was proved;
2. whether the finite Eta pair/defect partial was rewritten exactly through prime-factor support;
3. whether a genuine zero-derived P2-F theorem was obtained;
4. whether an immediate Q2-F norm bound follows from the existing Eta tail majorant;
5. the precise axiom sets of the strongest new theorems;
6. whether this route gives any coercive information on `centeredSigma s.re` or only source provenance;
7. the single smallest next obligation, if any.

## Verification

Run the narrow build for every touched Lean module and `git diff --check`.

If a new public RH/CFBRC module is imported into an umbrella file, also build the narrowest affected umbrella import.

## Completion condition

ZDI-005 is complete when Lean has either:

- an axiom-audited exact prime-factor rewrite of the finite T1 Eta main and its zero-derived finite-tail equality, with honest P2-F/A2-F classification; or
- a precise formal obstruction explaining why even this finite algebraic route cannot expose the zero-derived Eta main through prime factors without new analytic assumptions.
