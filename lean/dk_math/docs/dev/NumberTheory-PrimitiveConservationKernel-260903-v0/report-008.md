# PCK-006 implementation report

## Outcome

PCK-006 is implemented as the generic bridge from a finite prime basis to
its product anchor and from that anchor to fine square-world certification.
The generating basis remains distinct from the complete prime closure.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
9eac171b012b39ca79cb311c11a31cbfe49011ea
(docs(PCK): add PCK-006 primorial coarse-anchor bridge instructions).
The worktree was clean at the start.

## Changed files

- DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean
  - Added the two required bridge theorems.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-008.md
  - Added this implementation report.

No existing source file, public aggregator, or prior PCK theorem was
modified.

## Owner and imports

The owner is
DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge in
DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean.

The imports are exactly:

    import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
    import DkMath.NumberTheory.Primitive.SquarePrimeExpansion

The Primitive namespace is opened explicitly. The dependency direction is
from the PrimorialUniverse bridge toward Primitive; no Primitive-to-
PrimorialUniverse dependency was introduced.

## Basis inclusion theorem

The first required theorem is:

    theorem finitePrimeBasis_subset_primeScalesUpTo_product
        {S : Finset ℕ}
        (hS : IsFinitePrimeBasis S) :
        S ⊆
          DkMath.NumberTheory.Primitive.primeScalesUpTo
            (finitePrimeBasisProduct S)

For p ∈ S, the proof reuses hS p hp for Nat.Prime p,
mem_dvd_finitePrimeBasisProduct hp for p dividing the product, and
finitePrimeBasisProduct_ne_zero hS for product positivity. Nat.le_of_dvd
then gives p ≤ finitePrimeBasisProduct S, which is packaged with the
existing mem_primeScalesUpTo theorem.

This proves only

    S ⊆ primeScalesUpTo (finitePrimeBasisProduct S).

It does not assert equality. The finite basis is the generating set, while
primeScalesUpTo A is the complete prime closure at the product anchor A.

## Product-anchor fine-certification theorem

The second required theorem is:

    theorem prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody
        {S : Finset ℕ} {q m : ℕ}
        (hq : q ≤ finitePrimeBasisProduct S)
        (hm : 1 < m)
        (hmUpper :
          m ≤ DkMath.NumberTheory.Primitive.squareBody q)
        (hdisj :
          DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
            (DkMath.NumberTheory.Primitive.primeScalesUpTo
              (finitePrimeBasisProduct S))
            m) :
        Nat.Prime m

The proof is a direct application of
prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody
with coarse anchor finitePrimeBasisProduct S. No IsFinitePrimeBasis
hypothesis is added, because this theorem needs only the numeric product
anchor and the canonical complete support at that anchor.

Thus the semantic separation is explicit:

    finite prime basis S
      -> product anchor A
      -> basis inclusion into primeScalesUpTo A
      -> fine certification for q ≤ A

The basis alone is not claimed to certify the square Body; the complete
closure primeScalesUpTo A is essential.

## Optional surfaces

No packaged packet theorem was added. It would only duplicate the two
required results.

No PCK-005 expansion specialization was added. The existing
squarePrimeExpansion equality remains available from the Primitive layer,
and no new expansion operator parameterized by S was introduced.

No numeric {2,3,5} or 30 example was hard-coded; that belongs to PCK-007.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge

Result: DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge built
successfully after 8672 jobs.

git diff --check passed.

The axiom checks were run for:

    finitePrimeBasis_subset_primeScalesUpTo_product
    prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody

Each reported only ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

The new module was audited for forbidden imports and constructs. It adds
no basis/closure equality, new primorial, wheel or survivor criterion,
fresh-prime mechanism, Gnomon theorem, analytic dependency, sorry, admit,
native_decide, or project axiom.

## Boundary and next authorization

PCK-006 is green at the finite-basis product-anchor and fine-square
certification boundary. The next authorized checkpoint is PCK-007:
the canonical {2,3,5} to 30 to primeScalesUpTo 30 to 960 to 31^2
regression with representative fine anchors below 30. PCK-007 is not
implemented here.
