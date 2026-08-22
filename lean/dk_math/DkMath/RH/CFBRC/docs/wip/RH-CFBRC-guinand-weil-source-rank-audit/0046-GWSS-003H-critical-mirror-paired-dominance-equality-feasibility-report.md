# GWSS-003H critical-mirror paired dominance/equality feasibility report

Date: 2026-08-22

Starting HEAD: `8ef9ac0df7e13507a1b7b747d26d442c2b75c804`

Predecessor: `0044-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-report.md`

## Scope

This report implements the bounded 0045 audit only.  It stops at the first
load-bearing finite API gap and does not begin GWSS-004, classical
Guinand--Weil, Weil positivity, Li's criterion, an infinite-height argument,
or an RH deduction.

## Files changed

- `DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean`
- `DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean`
- this report

The actual-window module receives the small public reindexing lemma
`pascalCenteredXiSquaredOrbitCoordinate_mem`, needed to state the mirror
coordinate existence theorem without exposing the private enumeration
equivalence.

## H1: centered mirror convention

The project convention is

```text
criticalMirror s = 1 - conj s
pascalCenteredXiCriticalMirror z = -conj z.
```

The new module proves that the centered map is the translated form of
`criticalMirror`, is involutive, and satisfies

```text
mirror(z)^2 = conj(z^2),
(mirror(z)^2).re = (z^2).re,
(mirror(z)^2).im = -(z^2).im.
```

The elementary square-imaginary identity is reused from the existing CFBRC
API; it is not treated as a new source rank.

## H2: zero-window closure

Closed.  The theorem
`pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff` transports the disk
condition by norm preservation and the zero condition by
`criticalMirror_nontrivialRiemannZetaZero`.  It uses no RH assumption.

## H3: squared-orbit conjugation

Closed at the carrier level.  The theorem
`conj_mem_pascalCenteredXiSquaredOrbitFinset_iff` gives conjugation closure of
the occupied squared-orbit finset.  The theorem
`exists_pascalCenteredXiSquaredOrbitMirrorIndex` gives, for every `Fin`
coordinate, an existential mirror index with conjugate coordinate.

No canonical `Fin` involution is introduced, and no arbitrary choice equality
is used as mathematical content.  The filtered-fibre theorem
`image_pascalCenteredXiCriticalMirror_filter_sq` also proves the exact image
relation between the `q` and `conj q` fibres.

## H4: orbit-mass relation

Not closed.  The current mass is

```text
pascalCenteredXiSquaredOrbitMass R q
  = ∑ z in (zeroDisk R).filter (fun z => z^2 = q),
      pascalCenteredXiZeroMultiplicity z.
```

The new fibre-image theorem transports the filtered carrier and therefore
accounts for all representatives in a fibre; it does not collapse a fibre to
two points.  However, the repository has no theorem of the required shape

```text
pascalCenteredXiZeroMultiplicity (mirror z) =
  pascalCenteredXiZeroMultiplicity z
```

on actual zeros.  Thus the equality of the two multiplicity-weighted masses
is not asserted.  This is the first genuine stopping point.

Primary classification is therefore `MIRROR-ORBIT-MASS-API-GAP`.

## H5: Mellin evaluation and extractor

Not reached after the H4 stop.  The existing Mellin weight is even in its
centered argument, and the fixed-`τ = 0` branch has a conjugation result in a
separate audit.  The current general-`τ` actual-window API does not provide a
public full matrix symmetry together with a canonical inverse-row transport.
In particular, the arbitrary real `τ` row family need not be invariant under
the column permutation induced by squared-orbit conjugation.  The existing
existential extractor therefore cannot be used to infer a mirror coefficient
relation.

## H6: coefficient-row relation

Not established.  The sign change of `q.im` under `q ↦ conj q` is elementary,
but it is insufficient without the missing extractor-row relation.  No claim
of either `-cOff`, `-conj(cOff)`, or a permutation/conjugation variant is made.

## H7: whole feature and shifted differences

Not established.  Since H6 is unavailable, the 003G finite linear APIs do not
currently yield an actual mirror relation for either shifted-energy
difference.  In particular, the implementation does not infer oddness from
the scalar `q.im` sign alone.

## H8: conditional paired P1 implication

The purely ordered-algebra theorem
`paired_shifted_difference_odd_forces_P2_equality` is implemented.  Given an
exact odd relation for a pair and both paired P1 inequalities, it proves
equality of the original plus/minus energies.  This is conditional on the two
P1 hypotheses and is not a P1 provider.  The theorem does not use P0
nonnegativity as a substitute for P1.

## H9: detector and same-object firewall

Not reached.  No conclusion is drawn about
`q.im * pascalCenteredXiSquaredOrbitMassVec R j`, and no equality is assumed
between the finite-`X` arithmetic approximant and the finite arithmetic RHS.
There is consequently no finite off-critical exclusion result and no hidden
`X → ∞` passage.

## Firewalls recorded

- The mirror index is not rewritten as the original index.
- Existential extractor choices are not treated as canonical.
- P0 individual energy nonnegativity is not promoted to P1 ordering.
- No coefficient-universal positivity statement is introduced; the
  first-order scaling sign test remains applicable.
- Critical-mirror symmetry is recorded as a transport constraint, not as an
  independent source rank.

## Verification

Focused validation passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
```

The load-bearing predecessor dependency also passed:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit
```

`git diff --check` passed.  There are no errors, `sorry`, `admit`,
`native_decide`, or new axioms.

For the new load-bearing declarations, `#print axioms` reports the standard
baseline `[propext, Classical.choice, Quot.sound]`, with no stronger axiom.

GWSS-004 was not started.

## Classification

Primary: `MIRROR-ORBIT-MASS-API-GAP`

Secondary: `MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER`
