
# TRM-048 — Universal triangular reduction / branch closure

## Goal

Close the face-star reduction program at the level of universal propositions.

No new local combinatorics is required in this checkpoint.

TRM-047 already provides the one-way reduction:

    face-star colorable -> original colorable

and, on the all-triangular genus-zero face-star map:

    tetrahedral assignment <-> face-star four-state colorable.

TRM-048 must package these facts with the existence of face-star indexing and
prove that the universal all-triangular targets are equivalent to the existing
general genus-zero Four-Color target.

This checkpoint must NOT prove any universal target itself.

The final status after TRM-048 must remain:

    Four Color theorem NOT PROVED.

The exact remaining Gap must be stated as the universal existence of a
tetrahedral A/B/C assignment on every all-triangular genus-zero Port map.

## Production

Create:

    DkMath/Tromino/PortTriangularReduction.lean

Imports:

    DkMath.Tromino.PortFaceStarColorReduction

Create audit:

    DkMathTest/Tromino/PortTriangularReductionAxiomAudit.lean

Create report:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-047.md

Update if appropriate:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/ROADMAP.md
    docs/dev/Tromino-ExchangeCalculus-260924-v0/CURRENT_STATE.md

Do not refactor earlier production modules in this checkpoint.

## Read first

Read only:

- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortFaceStarColorReduction.lean;
- DkMath/Tromino/PortTriangularTetrahedral.lean;
- DkMath/Tromino/PortTensionColoring.lean;
- the exact definition/proof of exists_portFaceStarIndexing.

Do not re-read the full branch.

## A. Indexing-free face-star reduction theorem

First expose the existential reduction without universal target notation.

Preferred theorem:

    theorem exists_faceStarGenusZeroTriangulation
        {P : PortNetwork}
        (G : PortGenusZeroCombinatorialMap P) :
      ∃ I : PortFaceStarIndexing G.map,
        PortAllFacesTriangular (faceStarGenusZero G I).map ∧
        (PortFourStateColorable (faceStarGenusZero G I).map.crossing →
          PortFourStateColorable G.map.crossing).

Proof:

1. obtain I from exists_portFaceStarIndexing G.map;
2. use faceStarGenusZero_allFacesTriangular G I;
3. use faceStarGenusZero_colorable_imp_original G I.

Do not introduce Classical.choose in a production definition.
This is an existence theorem only.

Optionally also expose the tetrahedral form:

    theorem exists_faceStarGenusZeroTetrahedralReduction
        (G : PortGenusZeroCombinatorialMap P) :
      ∃ I : PortFaceStarIndexing G.map,
        PortAllFacesTriangular (faceStarGenusZero G I).map ∧
        (HasTetrahedralFaceAssignment (faceStarGenusZero G I).map →
          PortFourStateColorable G.map.crossing).

This optional theorem should reuse
faceStar_tetrahedral_imp_original_colorable.

## B. Universal triangular four-color target

Define:

    def PortGenusZeroTriangularFourColorTarget : Prop :=
      ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map →
        PortFourStateColorable G.map.crossing

This is only a proposition schema.

It does NOT assert that the proposition is true.

## C. General target implies triangular target

Prove:

    theorem portGenusZeroFourColorTarget_imp_triangular :
      PortGenusZeroFourColorTarget →
      PortGenusZeroTriangularFourColorTarget.

This direction should simply forget the triangular hypothesis.

## D. Triangular target implies general target

Prove:

    theorem portGenusZeroTriangularFourColorTarget_imp_general :
      PortGenusZeroTriangularFourColorTarget →
      PortGenusZeroFourColorTarget.

For arbitrary P and G:

1. obtain I from exists_portFaceStarIndexing G.map;
2. let Gstar := faceStarGenusZero G I;
3. apply the triangular target to Gstar using
       faceStarGenusZero_allFacesTriangular G I;
4. restrict the resulting coloring to G using
       faceStarGenusZero_colorable_imp_original G I.

No coloring extension theorem is required.

## E. Four-color universal equivalence

Prove:

    theorem portGenusZeroTriangularFourColorTarget_iff_fourColorTarget :
      PortGenusZeroTriangularFourColorTarget ↔
      PortGenusZeroFourColorTarget.

This must be a thin packaging of C and D.

Do not prove either side.

## F. Universal triangular tetrahedral target

Define:

    def PortGenusZeroTriangularTetrahedralTarget : Prop :=
      ∀ (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map →
        HasTetrahedralFaceAssignment G.map

Again, this is only a proposition.

Do not assert it.

## G. Triangular tetrahedral target iff triangular four-color target

Using the already verified local theorem:

    hasTetrahedralFaceAssignment_iff_fourStateColorable G htri

prove:

    theorem portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget :
      PortGenusZeroTriangularTetrahedralTarget ↔
      PortGenusZeroTriangularFourColorTarget.

This should quantify pointwise over P, G, htri.

No face-star construction is needed for this theorem.

## H. Triangular tetrahedral target iff general four-color target

Prove:

    theorem portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget :
      PortGenusZeroTriangularTetrahedralTarget ↔
      PortGenusZeroFourColorTarget.

Preferred proof:

- compose G with E.

This theorem is a reduction equivalence only.

It does NOT prove the Four Color theorem.

## I. Exact remaining Gap proposition

Optionally define an alias that names the remaining existence problem:

    abbrev TrominoTetrahedralExistenceGap :=
      PortGenusZeroTriangularTetrahedralTarget

or a theorem:

    theorem fourColorTarget_iff_tetrahedralExistenceGap :
      PortGenusZeroFourColorTarget ↔
      PortGenusZeroTriangularTetrahedralTarget

as the symmetric form of H.

If adding an alias would create redundant public API, omit the alias and keep
only the theorem.

The report must state in plain language:

    Remaining Gap:
    prove PortGenusZeroTriangularTetrahedralTarget.

No stronger claim.

## J. Optional tension target composition

If it is a one-line consequence of existing public API, prove:

    PortGenusZeroTriangularTetrahedralTarget ↔
    PortGenusZeroTensionTarget

by composing:

- H;
- portGenusZeroTensionTarget_iff_fourColorTarget.

This is optional and should be omitted if it introduces unnecessary API
surface.

## K. Branch-closure theorem bundle

Optionally package the reduction chain as conjunctions of equivalences, but
do not create a large structure unless it materially improves discoverability.

A minimal acceptable public endpoint is:

    portGenusZeroTriangularFourColorTarget_iff_fourColorTarget

and:

    portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget.

These are the branch-closing theorems.

## L. Explicit non-theorems

The module documentation must explicitly say that it does NOT prove:

- PortGenusZeroFourColorTarget;
- PortGenusZeroTriangularFourColorTarget;
- PortGenusZeroTriangularTetrahedralTarget;
- the Four Color theorem;
- existence of an A/B/C assignment;
- Euclidean/Eisenstein lattice realization;
- coloring extension from arbitrary original coloring to face-star coloring.

It only proves equivalences/reductions between those targets.

## M. Safety / scope

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

No:

- theorem whose conclusion is one of the universal targets without a
  corresponding target hypothesis;
- hidden assumption of tetrahedral existence;
- claim that the Four Color theorem has been proved;
- Eisenstein realization;
- rigid physical tetrahedron orientation.

## N. Audit

Create:

    DkMathTest/Tromino/PortTriangularReductionAxiomAudit.lean

Audit at least:

1. exists_faceStarGenusZeroTriangulation;
2. optional tetrahedral existential reduction if implemented;
3. PortGenusZeroTriangularFourColorTarget;
4. general -> triangular theorem;
5. triangular -> general theorem;
6. triangular four-color equivalence;
7. PortGenusZeroTriangularTetrahedralTarget;
8. tetrahedral <-> triangular four-color theorem;
9. tetrahedral <-> general four-color theorem;
10. optional symmetric remaining-gap theorem;
11. optional tension composition theorem.

Run #print axioms on:

- exists_faceStarGenusZeroTriangulation;
- portGenusZeroTriangularFourColorTarget_iff_fourColorTarget;
- portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget;
- portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget.

Expected existing dependencies may include:

    propext
    Classical.choice
    Quot.sound.

No new axiom.

## O. Validation

Build:

- DkMath.Tromino.PortTriangularReduction
- DkMathTest/Tromino/PortTriangularReductionAxiomAudit

Regression-build:

- DkMath.Tromino.PortFaceStarColorReduction
- DkMath.Tromino.PortFaceStarEuler
- DkMath.Tromino.PortTriangularTetrahedral
- DkMath.Tromino.PortTensionColoring

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## P. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-047.md

Record:

- indexing-free face-star reduction;
- definition of triangular four-color target;
- proof of triangular target <-> general target;
- definition of triangular tetrahedral target;
- proof of tetrahedral target <-> triangular four-color target;
- proof of tetrahedral target <-> general four-color target;
- exact remaining Gap;
- explicit statement that no universal existence theorem was proved;
- build/axiom results.

If A-I and N-O are complete, report:

    Outcome A — universal triangular reduction complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and internally map:

    requirement | theorem/definition | status.

A successful build alone is not GREEN.

If any mandatory A-I or N-O item is missing, report Outcome P and identify the
exact missing theorem.

## Stop condition

Stop once the universal triangular four-color target and universal triangular
tetrahedral target have both been proved equivalent to the existing general
PortGenusZeroFourColorTarget.

Do not prove any target itself.
Do not begin Eisenstein realization in this branch.
