# PCK-007 implementation report

## Outcome

PCK-007 is implemented as the concrete thirty-world regression. It records
the chain

    {2, 3, 5}
      -> finitePrimeBasisProduct = 30
      -> primeScalesUpTo 30
      -> squareBody 30 = 960 = 31^2 - 1
      -> squarePrimeExpansion 30 = primeScalesUpTo 960.

The generating basis is kept distinct from the complete prime closure.

The starting branch was
wip/number-theory-primitive-conservation-kernel-260903-v0.
The starting HEAD was
fe1a5a8a0baaf580533ddc766f52f25b6e6c3d56
(docs(PCK): add PCK-007 canonical thirty-world regression instructions).
The worktree was clean at the start.

## Changed files and imports

- DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean
  - Added the concrete regression theorems.
- docs/dev/NumberTheory-Primitive-ConservationKernel-260903-v0/report-009.md
  - Added this implementation report.

The new owner imports only:

    import DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge

No public aggregator, PHZ30 module, analytic module, or prior PCK source was
modified.

## Basis and complete closure

The theorem

    primeBasis235_subset_primeScalesUpTo_thirty :
      ({2, 3, 5} : Finset ℕ) ⊆
        DkMath.NumberTheory.Primitive.primeScalesUpTo 30

proves basis inclusion by locally establishing
IsFinitePrimeBasis ({2, 3, 5} : Finset ℕ), applying
finitePrimeBasis_subset_primeScalesUpTo_product, and rewriting with the
existing finitePrimeBasisProduct_two_three_five theorem.

The explicit complete closure is:

    primeScalesUpTo_thirty_eq :
      DkMath.NumberTheory.Primitive.primeScalesUpTo 30 =
        ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)

This is a concrete finite equality proved by decide. The basis
{2, 3, 5} is not identified with this closure.

## Square endpoint and expansion

The endpoint theorem is:

    @[simp] theorem squareBody_thirty :
      DkMath.NumberTheory.Primitive.squareBody 30 = 960

The existing endpoint identity is reused in:

    theorem squareBody_thirty_add_one_eq_thirtyOne_sq :
      DkMath.NumberTheory.Primitive.squareBody 30 + 1 = 31 ^ 2

The PCK-005 closure regression is:

    theorem squarePrimeExpansion_thirty_eq_primeScalesUpTo_960 :
      DkMath.NumberTheory.Primitive.squarePrimeExpansion 30 =
        DkMath.NumberTheory.Primitive.primeScalesUpTo 960

It applies the existing
squarePrimeExpansion_eq_primeScalesUpTo_squareBody theorem and rewrites
squareBody 30 to 960. No primes through 960 are enumerated.

## Fine-anchor certification and boundaries

The complete closure at 30 certifies all fine anchors q ≤ 30 through the
PCK-006 product-anchor theorem:

    theorem prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
        {q m : ℕ}
        (hq : q ≤ 30)
        (hm : 1 < m)
        (hmUpper :
          m ≤ DkMath.NumberTheory.Primitive.squareBody q)
        (hdisj :
          DkMath.NumberTheory.StructuralArithmetic.SupportDisjointFrom
            (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) m) :
        Nat.Prime m

The proof does not bypass PCK-006: it supplies S = {2, 3, 5} and rewrites
the product to 30.

The representative boundary packet covers anchors 6, 10, 12, 16, 18, 22,
28, and 30 by reusing squareBody_add_one_eq.

## 49 basis-versus-closure firewall

The theorem

    fortyNine_basis_vs_completeClosure_firewall :
      SupportDisjointFrom ({2, 3, 5} : Finset ℕ) 49 ∧
      ¬ SupportDisjointFrom
          (DkMath.NumberTheory.Primitive.primeScalesUpTo 30) 49 ∧
      ¬ Nat.Prime 49

is proved using 7 as the divisor of 49. It shows that 49 survives the
generating basis but fails against the complete closure because 7 is in
primeScalesUpTo 30. This permanently blocks the invalid inference from
basis survival, or gcd with 30, to primality through 960.

No strict-subset theorem was added.

## Verification

The required focused build passed:

    lake build DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld

Result: DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld built
successfully after 8673 jobs, with no final Lean linter warnings.

git diff --check passed.

The axiom checks were run for:

    primeBasis235_subset_primeScalesUpTo_thirty
    primeScalesUpTo_thirty_eq
    squarePrimeExpansion_thirty_eq_primeScalesUpTo_960
    prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
    fortyNine_basis_vs_completeClosure_firewall

Each reported only ordinary Lean/Mathlib foundations:

    propext, Classical.choice, Quot.sound

The new module was audited for forbidden imports and constructs. It adds no
new prime-support or primorial definition, no wheel-survivor primality
criterion, no PCK-008 implementation, no Gnomon or analytic dependency, and
no sorry, admit, native_decide, or project axiom.

## Next authorization

PCK-007 is green at the canonical thirty-world finite regression boundary.
The next authorized checkpoint is PCK-008: the primitive-kernel dichotomy
wrapper around the existing
primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody theorem.
PCK-008 is not implemented here.
