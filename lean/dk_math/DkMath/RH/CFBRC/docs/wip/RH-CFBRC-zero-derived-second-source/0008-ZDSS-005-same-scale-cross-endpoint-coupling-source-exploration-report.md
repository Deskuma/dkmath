# ZDSS-005 — same-scale cross-endpoint coupling source exploration report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

## 0. Decision and classification

The strongest exact classification is:

```text
RAW-RATIO-ASYMPTOTIC-DICHOTOMY-FOUND
COFINAL-FRONTIER-FOUND
MIRROR-CLOSURE-FORMALIZED
TWO-SIDED-COMPARABILITY-FRONTIER-FOUND
GLOBAL-FRONTIER-RH-EQUIVALENT
CROSS-ENDPOINT-SOURCE-ABSENT-IN-CURRENT-API
FUNCTIONAL-EQUATION-FINITE-GAP
COMMON-SCALE-INFORMATION-OBSTRUCTION
```

ZDSS-005 proves that the common-scale raw endpoint ratio itself has the exact
off-critical dichotomy predicted by ZDSS-004:

```text
centeredSigma s.re > 0  -> raw ratio -> +infinity,
centeredSigma s.re < 0  -> raw ratio -> 0.
```

This yields a substantially weaker sufficient frontier than eventual
boundedness. It is enough that the raw ratio be bounded above at infinitely
many cutoffs for every nonreal standard zero. Applying that property first to
`s` and then to `criticalMirror s` forces the critical line.

Lean also proves that this global frequent-upper-control proposition is
equivalent to `RiemannHypothesis`. No existing zero, finite functional-equation,
completed-zeta, tail, derivative, phase, or prime-coordinate API supplies its
forward direction. Therefore the checkpoint identifies the exact missing U1X
source but does not prove RH.

## 1. Inherited ZDSS-004 factorization and rates

For a nonreal standard zero, write

```text
A_q(s) = etaPairedPartial q s,
B_q(s) = etaPairedPartial q (criticalMirror s),
q = K + 1,
delta = centeredSigma s.re.
```

ZDSS-004 supplies the eventual exact identity

```text
Q_K(s) = M_K(s) * R_K(s),

Q_K(s) = ||B_q(s)|| / ||A_q(s)||,
M_K(s) = etaEndpointIncrementMirrorRatio s K = q^(2*delta),
R_K(s) = separately normalized endpoint norm ratio.
```

It also proves

```text
R_K(s) -> R_infinity(s),
0 < R_infinity(s).
```

Thus `R_K` neither vanishes nor diverges and all common-scale horizontal
escape is carried by `q^(2*delta)`.

## 2. Common scale versus endpoint-specific normalization

The two endpoint-specific normalizations are

```text
q^(s.re)                 * ||A_q(s)||,
q^((criticalMirror s).re) * ||B_q(s)||.
```

Both have positive finite limits, but their quotient is `R_K`. This quotient
has divided out the horizontal power and remains U1 information.

The common raw scale retains

```text
Q_K(s) = ||B_q(s)|| / ||A_q(s)||.
```

Undoing the endpoint-specific normalizations restores exactly

```text
q^(s.re - (1 - s.re)) = q^(2*delta).
```

Therefore a theorem about `R_K` is not a same-scale coupling theorem. A
genuine U1X theorem must constrain `Q_K` or an equivalent observable without
inserting the two different natural exponents by construction.

## 3. New exact raw-ratio dichotomy

The focused module is

```text
ZeroDerivedSameScaleCrossEndpointCouplingAudit.lean.
```

It first proves the unconditional mode limits

```lean
etaEndpointIncrementMirrorRatio_tendsto_atTop_of_centeredSigma_pos
etaEndpointIncrementMirrorRatio_tendsto_zero_of_centeredSigma_neg.
```

Combining them with the zero-derived ZDSS-004 factorization gives

```lean
etaDualEndpointRawNormRatio_tendsto_atTop_of_centeredSigma_pos
etaDualEndpointRawNormRatio_tendsto_zero_of_centeredSigma_neg.
```

These theorems are exact U1-plus-U0 consequences. They do not introduce a
cross-endpoint source. Rather, they calculate precisely how a hypothetical
off-critical zero behaves on the common raw scale.

## 4. Weak frontier predicates

The module defines

```lean
EtaDualEndpointRawNormRatioFrequentlyBoundedAboveAt s
```

as

```text
there exists C such that Q_K(s) <= C frequently in atTop.
```

For a natural-number sequence, this is an infinitely-often/cofinal upper
control. It is strictly weaker than an eventual upper bound.

It also defines

```lean
EtaDualEndpointRawNormRatioEventuallyBoundedAwayFromZeroAt s
```

as the existence of `c > 0` with `c <= Q_K(s)` eventually.

The one-sided frontier theorems are:

```lean
centeredSigma_nonpos_of_rawNormRatio_frequently_boundedAbove
centeredSigma_nonneg_of_rawNormRatio_eventually_boundedAwayFromZero.
```

Their information content is deliberately asymmetric:

```text
frequent upper control       excludes delta > 0 only,
eventual positive lower bound excludes delta < 0 only.
```

The theorem

```lean
re_eq_half_of_rawNormRatio_twoSided_comparability
```

combines the two conditions at one zero and forces `s.re = 1/2`.

## 5. Mirror reapplication audit

The theorem

```lean
re_eq_half_of_rawNormRatio_frequently_boundedAbove_at_zero_and_mirror
```

formalizes the weaker mirror route. Frequent upper control at `s` gives

```text
centeredSigma s.re <= 0.
```

The critical mirror is another nonreal standard zero, and

```text
centeredSigma (criticalMirror s).re = -centeredSigma s.re.
```

Frequent upper control at the mirror therefore gives

```text
-centeredSigma s.re <= 0.
```

The two inequalities force equality. No lower bound at either individual zero
is needed if the same upper-control provider applies uniformly around the zero
orbit.

The global candidate is

```lean
EtaDualEndpointRawNormRatioFrequentlyBoundedAboveOnZeros.
```

Lean proves both

```lean
riemannHypothesis_of_rawNormRatio_frequently_boundedAboveOnZeros
```

and the sharp classification

```lean
rawNormRatio_frequently_boundedAboveOnZeros_iff_riemannHypothesis.
```

The reverse implication is realizable: on the critical line,
`criticalMirror s = s`, so `Q_K(s) <= 1` at every cutoff, including the field
convention `0 / 0 = 0`.

This equivalence is not used as evidence for the forward implication. It shows
that any claimed provider must carry genuinely RH-load-bearing information.

## 6. Source/API inventory

| Source family | Exact current declaration/content | Level | Same-scale U1X outcome |
|---|---|---|---|
| Separate ordinary Eta tails | Each endpoint partial is its own negative tail; each natural normalization has a nonzero limit | `U1` | Determines individual exponents but supplies no common-scale comparison |
| ZDSS-004 raw factorization | `Q_K = M_K * R_K` eventually, `R_K -> positive finite` | `U1` plus `U0` | Locates the missing horizontal power; does not bound it |
| Functional-equation endpoint orbit | Mirror, conjugate, and `1-s` endpoint data are sign/conjugation transports | `U0/U1` transport | Reapplication can close a supplied bound, but does not supply the bound |
| Completed-zeta same-truncation orbit residual | Same-index finite residual is equivalent to completed-zeta slope-line compatibility | RH frontier | Exact finite expansion exists, but residual collapse is an unproved RH-sufficient antecedent |
| Completed-zeta finite Eta/tail reduction | Rewrites the same residual through finite Eta defect and then the complete defect tail | exact reduction | Changes representation, not source rank or amplitude control |
| Completed-zeta first-order reflection | Zero values transport; derivatives are antisymmetric and norm-preserving | orbit data | No theorem links the derivative coefficient to a common-scale bound for `A_q,B_q` |
| Tail nearby-Euler decomposition | Weighted defect tail splits into Euler main plus remainder | exact algebra | The missing main transverse collapse remains an RH provider; remainder control alone is insufficient |
| Direct endpoint-tail comparison | Unconditional leading rates have exponents `s.re` and `1-s.re` | `U0/U1` | Off-critical unequal rates are explicitly compatible |
| Prime-factor endpoint decomposition | P2-F is the mirror-minus-original finite endpoint difference | finite source | Whole-sum cancellation prevents norm/energy coercivity; no coordinatewise joint constraint is present |
| Consecutive/multiple cutoffs | Cutoff subtraction recovers unconditional Eta modes | `U0` | Recovers the known exponent and no new zero-specific relation |
| Scale-coupled cutoffs | No canonical finite functional-equation cutoff pairing is present in the audited API | absent | No source-preserving common-scale comparison obtained |

## 7. Finite functional-equation and completed-zeta audit

The most promising filename-level candidate was

```text
EtaCriticalMirrorPairedFrameCompletedZetaSameTruncationOrbit.
```

Its residual genuinely uses one finite index, but it is not a theorem derived
from `hs`. The declaration

```text
EtaCriticalMirrorEndpointCompletedZetaSameTruncationOrbitResidualCollapse
```

is a global antecedent, and the repository proves it equivalent to the
completed-zeta slope-line compatibility already sufficient for RH.

`CompletedZetaFiniteEtaOrbitExpansion` and
`CompletedZetaFiniteEtaTailReduction` expand this antecedent exactly:

```text
dominant weighted finite Eta defect
  -> unweighted finite phase residual
  -> weighted complete defect-tail phase residual.
```

These are valuable exact reductions, but none proves the collapse from the
standard zero hypothesis. Treating the residual collapse as a provider would
be circular.

The nearby completed-zeta Euler decomposition separates an Euler main mismatch
from a controlled remainder. Existing work discharges the remainder side but
leaves the Euler-main transverse collapse as the load-bearing condition. It
does not imply frequent upper control for the raw endpoint ratio.

## 8. First-order, phase, and prime-coordinate audit

The completed-zeta first-order theorem proves

```text
completedZeta'(1-s) = -completedZeta'(s).
```

After transport through the reflection tangent map this is equality of the
same derivative data, and the derivative norms agree. It is not a finite Eta
remainder identity. No derivative vanishing or simple-zero assumption was
introduced.

The completed-zeta projective phase APIs provide exact implications once a
tail-orbit residual collapse is assumed. They do not derive phase locking from
`hs`; the phase collapse is another presentation of the same RH frontier.

At prime-coordinate level, the actual source remains

```text
sum mirror coordinates - sum original coordinates.
```

The repository's `1,-1` firewall shows why a small whole complex sum cannot
control mode norm-square energy. ZDSS-001 supplies two endpoint whole-sum
equations, but the orbit maps only swap or conjugate those coordinates. No
modewise linear constraint, positive Gram lower bound, or same-prime amplitude
comparison follows.

## 9. Candidate strength table

| Candidate | Needed strength | Exact implication | Status |
|---|---|---|---|
| Eventual upper bound for `Q_K(s)` | stronger than necessary | Excludes `delta > 0` | No source provider |
| Frequent/cofinal upper bound for `Q_K(s)` | weakest implemented upper frontier | Excludes `delta > 0` | Frontier proved |
| Same property at the mirror | same weak frontier | Excludes `delta < 0` for the original zero | Mirror closure proved |
| Eventual lower bound `c <= Q_K(s)` | one-zero lower frontier | Excludes `delta < 0` | Frontier proved |
| Two-sided comparability at one zero | frequent upper plus eventual positive lower | Forces critical line | Frontier proved |
| Positive finite limit of raw ratio | stronger two-sided property | Forces critical line | No source provider |
| Endpoint-specific normalized ratio limit | bounded but exponent-dependent normalization | No restriction on `delta` | Already U1; insufficient |
| Completed-zeta finite orbit collapse | phase rather than direct ratio | Forces RH through existing line compatibility | Antecedent unproved; not a provider |
| First-order derivative norm equality | complete-zero orbit transport | No finite raw-ratio bound | Insufficient |
| Prime-coordinate energy control | would be U1X/U2 if source-connected | Could force centered coordinate | Missing bridge; cancellation firewall applies |

## 10. Lean implementation and axiom status

The focused module contains docstrings distinguishing unconditional
asymptotics, zero-derived factorization consequences, diagnostic frontier
predicates, and actual source providers.

Every load-bearing theorem is inspected with `#print axioms`. The output is:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, new `axiom`, or `native_decide`.

The module remains focused and is not added to `DkMath.RH`. Its results are an
exploratory frontier and source-availability audit, not an accepted new source
provider or reusable RH Core assumption.

Validation from `lean/dk_math` is recorded after implementation with:

```text
lake env lean DkMath/RH/CFBRC/ZeroDerivedSameScaleCrossEndpointCouplingAudit.lean
lake build DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
./lean-build.sh DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
git diff --check
```

All four commands passed. An aggregate `DkMath.RH` build is not required for
this checkpoint because the exploratory module is deliberately not added to
the public import surface.

## 11. Smallest remaining mathematical obligation

The smallest exact obligation is now:

```text
From the standard nonreal zero hypothesis alone, prove that
||etaPairedPartial (K+1) (criticalMirror s)||
  / ||etaPairedPartial (K+1) s||
is bounded above along infinitely many common cutoffs K,
uniformly in the sense that the same theorem applies to every zero orbit.
```

No eventual bound, convergence theorem, two-sided estimate, or positive lower
bound is required. Mirror reapplication supplies the opposite horizontal
direction automatically.

Because the global form is RH-equivalent, its proof must come from genuinely
independent finite functional-equation, arithmetic, or analytic source data.
The next step should not introduce another wrapper for this proposition. It
must instead construct a finite same-scale identity whose controlled remainder
implies the frequent bound, or establish rigorously that the required finite
functional-equation decomposition is absent and must be developed outside the
current API.
