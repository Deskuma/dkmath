# ZDSS-001 — zero-derived source rank / independence audit report

Date: 2026-08-20

Branch: `wip/RH-CFBRC-zero-derived-second-source-260820-v0`

Starting commit: `2d4b6574242822594df89c20aeab0435fd6ad716`

Base: `develop` at `e5098e181d6ff510822f872c26332ace2ce80b69`

## 0. Decision

The final ZDSS-001 classification is:

```text
INDEPENDENT-SOURCE-FOUND
```

The independent finite source is not another transformed P2-F defect value.
It is the already existing ordered pair of ordinary paired-Eta endpoints

```text
Sendpoint(K,s) =
  (etaPairedPartial K (criticalMirror s), etaPairedPartial K s).
```

For a nonreal standard nontrivial zeta zero, the same hypothesis gives an
exact finite-partial-plus-tail identity and an explicit power upper bound for
each coordinate separately. P2-F is only the mirror-minus-original projection
of this pair. The projection from an endpoint pair to its difference is not
injective, so the P2-F whole value does not reconstruct the endpoint pair.

This is a source-rank result only. It does not prove centered-coordinate
coercivity and does not prove `RiemannHypothesis`.

## 1. P2-F / Q2-F recap

The inherited P2-F source is

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
```

and ZDI-005 proves both

```lean
etaPrimeFactorMirrorDefectPairedPartial K s =
  etaCriticalMirrorDefectPairedPartial K s
```

and, at a nonreal standard zero,

```lean
etaPrimeFactorMirrorDefectPairedPartial K s =
  -etaCriticalMirrorDefectPairTail K s.
```

ZDI-006 supplies Q2-F convergence and ZDI-011 supplies the arbitrary
post-processing firewall. Those facts are retained unchanged.

The finite prime-factor provenance is inherited from
`etaPairTerm_eq_primeFactorLogExp_sub`: every ordinary endpoint mode is an
exact difference of exponentials of finite natural factorization-log sums.

## 2. Source inventory

| Candidate | Exact declaration used | Hypotheses | Finite object | Transport | Dependence on P2-F | Classification |
|---|---|---|---|---|---|---|
| P2-F baseline | `etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero` | standard zero, nonreal | prime-factor defect partial | identity | baseline | `SAME` |
| P2-F at `criticalMirror s` | `etaPrimeFactorMirrorDefectPairedPartial_criticalMirror_eq_neg` | none | defect partial | multiplication by `-1` | exactly `-P2F` | `SCALAR-DUPLICATE` |
| P2-F at `conj s` | `etaPrimeFactorMirrorDefectPairedPartial_conj` | none | defect partial | complex conjugation | exactly `conj P2F` | `CONJUGATE-DUPLICATE` |
| P2-F at `1-s` | `etaPrimeFactorMirrorDefectPairedPartial_one_sub_eq_neg_conj` | none | defect partial | negative conjugation | exactly `-conj P2F` | `INVERTIBLE-TRANSPORT-DUPLICATE` |
| completed-zeta zero at `s` | `completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero` | standard zero | no finite Eta source by itself | nonzero-factor zero transport | no new finite coordinate | `INVERTIBLE-TRANSPORT-DUPLICATE` |
| completed-zeta zero at `1-s` | `completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero` | standard zero | no finite Eta source by itself | functional equation | no new finite coordinate | `MIRROR-DUPLICATE` |
| completed-zeta derivative at `1-s` | `completedRiemannZeta_deriv_one_sub_eq_neg_of_nontrivialRiemannZetaZero` | standard zero | not a finite arithmetic source | multiplication by `-1` | first-order orbit transport only | `SCALAR-DUPLICATE` |
| original ordinary endpoint | `etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero` | standard zero, nonreal | `etaPairedPartial K s` | own finite-plus-tail identity | not recoverable from defect difference alone | `GENUINELY-INDEPENDENT` as second endpoint coordinate |
| mirror ordinary endpoint | `etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero` | standard zero, nonreal | `etaPairedPartial K (criticalMirror s)` | own finite-plus-tail identity | together with original projects to P2-F | `GENUINELY-INDEPENDENT` endpoint pair |
| consecutive P2-F cutoffs | `etaPrimeFactorMirrorDefectPairedPartial_succ_sub` | none | one defect pair term | subtraction | unconditional definition recovery | `SAME`, no new zero information |

## 3. Endpoint source audit

The new module first proves the unconditional split

```lean
etaPairedPartial K z + etaPairTail K z =
  ∑' k, etaPairTerm z k.
```

For a nonreal standard zero `s`, the ordinary Eta sum at `s` is zero, so:

```lean
etaPairedPartial K s = -etaPairTail K s.
```

The existing zero transport to `criticalMirror s`, followed by the same
ordinary Eta split, separately gives:

```lean
etaPairedPartial K (criticalMirror s) =
  -etaPairTail K (criticalMirror s).
```

The two finite coordinates have separate explicit upper controls:

```text
||etaPairedPartial K s||
  <= ||s|| * K^(-re s) / re s,

||etaPairedPartial K (criticalMirror s)||
  <= ||criticalMirror s||
       * K^(-re (criticalMirror s)) / re (criticalMirror s).
```

The theorem

```lean
etaDualEndpointFiniteSourceCertificate_of_nontrivialRiemannZetaZero
```

packages both exact tail identities together with

```lean
P2F K s = mirrorEndpoint K s - originalEndpoint K s.
```

The endpoint equations are related as a theorem family by applying the same
ordinary Eta theorem to the transported zero. They are nevertheless not
duplicate values of the P2-F whole source: `endpointDifference_not_injective`
proves that the projection `(mirror, original) ↦ mirror - original` loses one
complex coordinate.

This is the precise information gain certified in ZDSS-001. No abstract rank
predicate was introduced.

## 4. Mirror, conjugation, and functional-equation audit

The endpoint pair itself has the expected invertible orbit transports:

```text
criticalMirror : swap the two endpoint coordinates
conj           : conjugate both endpoint coordinates
1 - s          : conjugate and swap the endpoint coordinates
```

These are proved by

```lean
etaEndpointPair_criticalMirror_eq_swap
etaEndpointPair_conj_eq_componentwise_conj
etaEndpointPair_one_sub_eq_conj_swap.
```

This orbit symmetry does not create a third source coordinate. It only
classifies how the two-coordinate endpoint source transforms.

By contrast, the P2-F defect is the antisymmetric projection of the pair.
Consequently its complete four-point orbit reduces exactly to

```text
P(s), -P(s), conj(P(s)), -conj(P(s)).
```

All transformed P2-F values are therefore duplicates.

## 5. Functional-equation and completed-zeta audit

The existing completed-zeta API gives zero transport between `s` and `1-s`.
The existing first-derivative API gives exact sign reversal under that
reflection. These declarations transport zero and tangent data, but do not by
themselves expose a new finite arithmetic piece.

Instantiating the ordinary Eta finite-plus-tail theorem at the original and
critical-mirror zero does expose the two finite endpoint coordinates described
above. Instantiating the P2-F defect at the functional-equation orbit does not:
the new exact theorem reduces the value at `1-s` to `-conj(P(s))`.

No new functional equation, approximate functional equation, Xi construction,
or derivative identity was introduced.

## 6. Multi-cutoff audit

The new theorem

```lean
etaPrimeFactorMirrorDefectPairedPartial_succ_sub
```

proves

```lean
P2F (K+1) s - P2F K s = etaPrimeFactorMirrorDefectPairTerm s K.
```

It has no zero hypothesis. Thus consecutive cutoffs recover an unconditionally
defined source term, not a second zero-derived equation. No block schedule,
moving frame, or positive-density route is reopened.

## 7. Exact accepted theorems

The accepted reusable Core in
`ZeroDerivedPrimeCoordinateSourceRankAudit.lean` consists of:

```text
etaPairedPartial_add_etaPairTail_eq_tsum
etaPairedPartial_eq_neg_etaPairTail_of_tsum_eq_zero
etaPairedPartial_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
etaPairedPartial_criticalMirror_eq_neg_etaPairTail_of_nontrivialRiemannZetaZero
norm_etaPairedPartial_le_powerBound_of_nontrivialRiemannZetaZero
norm_etaPairedPartial_criticalMirror_le_powerBound_of_nontrivialRiemannZetaZero
etaDualEndpointFiniteSourceCertificate_of_nontrivialRiemannZetaZero
endpointDifference_not_injective
etaEndpointPair_criticalMirror_eq_swap
etaEndpointPair_conj_eq_componentwise_conj
etaEndpointPair_one_sub_eq_conj_swap
etaPrimeFactorMirrorDefectPairedPartial_criticalMirror_eq_neg
etaPrimeFactorMirrorDefectPairedPartial_conj
etaPrimeFactorMirrorDefectPairedPartial_one_sub_eq_neg_conj
etaPrimeFactorMirrorDefectPairedPartial_succ_sub
```

The module is added to the public `DkMath.RH` import surface because these are
accepted concrete source-comparison and finite-source theorems.

## 8. Axiom and build validation

The load-bearing theorems were inspected with `#print axioms`. Their only
reported dependencies are the standard Mathlib foundations:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` is present.

Validation from `lean/dk_math`:

```text
lake build DkMath.RH.CFBRC.ZeroDerivedPrimeCoordinateSourceRankAudit
./lean-build.sh DkMath.RH.CFBRC.ZeroDerivedPrimeCoordinateSourceRankAudit
lake build DkMath.RH
git diff --check
```

All commands passed.

## 9. Boundary and smallest next obligation

ZDSS-001 has found a genuine second finite source coordinate, but it has not
found the C-side theorem needed for RH. In particular, the already known
endpoint total energy tends to zero for every nonreal zero and does not by
itself select the critical line. The existing proposition that converts
endpoint-Gap collapse to term-amplitude UnitGap is RH-equivalent under the
available endpoint limits and must not be used as a provider.

The single smallest next mathematical obligation is:

```text
Find an unconditional, source-preserving centered-coordinate lower bound for
a positive scalar formed from the two separately controlled endpoint sources,
without assuming endpoint-Gap-to-UnitGap control or any RH-equivalent
vanishing provider.
```

Quadraticization and that coercivity audit belong to the next checkpoint, not
to ZDSS-001.
