# LUNA-021 — finite seven-depth incidence ledger

## Scope and files

This checkpoint turns the LUNA-020 mod-49 trichotomy into exact finite
filters over the existing realized large-modulus shell.  It adds no state
count estimate, density statement, relative-height theorem, or ABC closure.

Changed files:

- `DkMath/ABC/GNExcessCubicSevenDepthIncidence.lean`
- `DkMath/ABC.lean` (public import immediately after `GNExcessCubicSevenDepth`)
- `README.md`, `ROADMAP.md`, `validation-021.txt`, and this report.

## Seven-sector and three state spaces

`GNCubicPairedSevenSectorWitnessSpace X D` is the existing shell witness
space filtered by `a % 7 = 1`.  Its membership theorem is exact and exposes
the shell membership together with the residue condition.

The required state filters are provided by
`GNCubicPairedForwardSevenDeepWitnessSpace`,
`GNCubicPairedSwapSevenDeepWitnessSpace`, and
`GNCubicPairedShallowSevenWitnessSpace`.  Their membership theorems reduce
membership to the original shell witness plus, respectively, residues `29`,
`22`, or the two shallow exclusions.

The exact finite identity is

```text
SevenSectorWitnessSpace
  = ForwardDeepWitnessSpace ∪ SwapDeepWitnessSpace ∪ ShallowSevenWitnessSpace.
```

The three pairwise disjointness theorems are exposed separately.  The card
ledger is exact:

```text
SevenSector.card = ForwardDeep.card + SwapDeep.card + Shallow.card.
```

No estimate is attached to any of these cardinalities.

## State packet consumers

The three packet consumers
`GNCubicPairedForwardSevenDeepWitnessSpace_packet`,
`GNCubicPairedSwapSevenDeepWitnessSpace_packet`, and
`GNCubicPairedShallowSevenWitnessSpace_packet` derive positivity from shell
membership and directly invoke the LUNA-020 arithmetic and exact cross-gcd
packets.  Callers therefore supply only finite-set membership; no new residue
hypothesis or arithmetic proof is required.

## Repeated-product incidence

`GNCubicPairedRepeatedProductSevenWitnessSpace` filters the seven-sector shell
by `7 ∣ MF*MG`.  The exact set equality

```text
RepeatedProductSevenWitnessSpace
  = ForwardDeepWitnessSpace ∪ SwapDeepWitnessSpace
```

is proved using the LUNA-020 repeated-product/deep-state equivalence.  Its
cardinality is therefore the exact sum of the two deep-state cards.  The
shallow complement characterization

```text
a ∈ SevenSectorWitnessSpace ∧ ¬(7 ∣ MF*MG)
  ↔ a ∈ ShallowSevenWitnessSpace
```

is also exposed.

The optional residue-image and square-cube convenience APIs were not added;
the required finite geometry and arithmetic packet wrappers are complete.

## Explicit boundary

The three filters are exact finite incidence objects.  No comparison of their
cardinalities, equidistribution, higher 7-adic depth count, shell bound,
Hensel rarity, relative-height exclusion, or ABC quality coupling is claimed.
The single mod-49 residue classes do not constitute a density theorem.

## Verification and trust boundary

```text
lake build DkMath.ABC.GNExcessCubicSevenDepthIncidence  PASS
lake build DkMath.ABC                                  PASS
```

Changed production sources contain no new `sorry`, `admit`, `axiom`,
`abc_main_axiom`, or `native_decide`.  The principal declaration audit remains
within `propext`, `Classical.choice`, and `Quot.sound`.

The remaining research frontier is paired relative-height exclusion, shell
counts, squareful asymptotics, Hensel/Pell rarity, density, and ABC quality
coupling.
