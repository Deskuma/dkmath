
# TRM-036 — Integral mod-2 Gaussian/Eisenstein parity bridge

## Goal

Close the source-side meaning of TRM-035 by connecting the local V4 exchange
frame to actual integral Gaussian and Eisenstein coordinate carriers.

The checkpoint must formalize the following distinction:

    Gaussian integral coordinates
          \
           \  mod-2 additive parity
            -> V4 = F2² <- 
           /  mod-2 additive parity
          /
    Eisenstein integral coordinates

The common object is the **additive mod-2 four-state carrier**.

Do not identify the Gaussian and Eisenstein rings themselves.

In fact, this checkpoint should also expose that the two induced
multiplications on the same additive V4 carrier are different.  This gives a
kernel-checked version of the source warning:

    same local 3+1 exchange frame
      does not mean
    same ring structure.

After TRM-036, return to the genus-zero exactness program.

## Production

Create:

DkMath/Tromino/IntegralMod2Bridge.lean

Import:

- DkMath.Tromino.LocalFrameEquiv
- DkMath.Tromino.PortV4Chains
- DkMath.Lib.NumberTheory.EisensteinCoordinates
- Mathlib.NumberTheory.Zsqrtd.GaussianInt

Use the existing:

    GaussianInt = Zsqrtd (-1)
    TraceOneInt (-1)
    eisensteinCoord
    TrominoState = ZMod 2 × ZMod 2.

## A. Gaussian parity map

Define a computable additive homomorphism:

    gaussianParity : GaussianInt →+ TrominoState

by:

    gaussianParity z := ((z.re : ZMod 2), (z.im : ZMod 2)).

Prove the coordinate formula and additive laws.

Prove surjectivity explicitly.

Recommended representatives:

    0        ↦ 0
    1        ↦ deltaA
    i        ↦ deltaB
    1 + i    ↦ deltaC.

Use explicit GaussianInt coordinate pairs:

    ⟨0,0⟩
    ⟨1,0⟩
    ⟨0,1⟩
    ⟨1,1⟩

rather than introducing unnecessary complex-number coercions.

Required theorems:

    gaussianParity_zero
    gaussianParity_one
    gaussianParity_i
    gaussianParity_one_add_i.

## B. Eisenstein parity map

Define a computable additive homomorphism:

    eisensteinParity : TraceOneInt (-1) →+ TrominoState

by:

    eisensteinParity z := ((z.fst : ZMod 2), (z.snd : ZMod 2)).

Prove surjectivity explicitly.

Using standard coordinates

    eisensteinCoord m n = ⟨m,-n⟩,

prove:

    eisensteinParity (eisensteinCoord 0 0) = 0
    eisensteinParity (eisensteinCoord 1 0) = deltaA
    eisensteinParity (eisensteinCoord 0 1) = deltaB
    eisensteinParity (eisensteinCoord 1 1) = deltaC.

The sign on the second coordinate disappears modulo 2.

This is the actual integral realization of the local Eisenstein direction
frame from TRM-035.

## C. Four-state representative sections

Define computable representative functions if clean:

    gaussianStateRep : TrominoState → GaussianInt
    eisensteinStateRep : TrominoState → TraceOneInt (-1)

with:

    gaussianParity (gaussianStateRep s) = s
    eisensteinParity (eisensteinStateRep s) = s.

A finite by-cases / fin_cases implementation is acceptable.

These are set-theoretic/computable sections only; no multiplicative claim.

## D. Gaussian panel coordinate bridge

Define:

    gaussianPanelIntegral :
      gaussianExchangeFrame.Panel → GaussianInt

using the underlying block2 cell coordinates:

    (x,y) ↦ ⟨x,y⟩.

Prove:

    gaussianParity (gaussianPanelIntegral p)
      =
    frameColor gaussianExchangeFrame p.

This should hold because the four block2 coordinates are exactly the four
parity states.

Then prove the relative-direction theorem:

    gaussianParity
      (gaussianPanelIntegral gaussianExchangeFrame.gap
        - gaussianPanelIntegral p)
      =
    frameDelta gaussianExchangeFrame p.

Because -x = x modulo 2, subtraction and addition have the same parity
difference.

An equivalent theorem using + is also acceptable.

## E. Integral interpretation of gaussianEisensteinFrameEquiv

Use the TRM-035 theorem:

    gaussianEisensteinFrameEquiv.panelEquiv p
      =
    frameDelta gaussianExchangeFrame p.

Combine it with section D to prove:

    gaussianEisensteinFrameEquiv.panelEquiv p
      =
    gaussianParity
      (gaussianPanelIntegral gaussianExchangeFrame.gap
        - gaussianPanelIntegral p).

Thus the frame equivalence is literally the Gaussian integral relative
direction reduced modulo 2.

For body panels, audit the three cases:

    1
    i
    1+i

up to the chosen gap-relative ordering:

    deltaA
    deltaB
    deltaC.

State the exact ordering used by the existing block2 coordinates.

## F. Eisenstein integral direction interpretation

For each nonzero local Eisenstein panel/direction s, prove:

    eisensteinParity (eisensteinStateRep s) = s.

Audit the canonical three standard representatives:

    1
    omega
    1+omega

represented by:

    eisensteinCoord 1 0
    eisensteinCoord 0 1
    eisensteinCoord 1 1.

Do not assert any equality of Gaussian and Eisenstein integral elements.
Only their parity images agree in V4.

## G. Common additive-frame theorem

Package the central source-supported statement:

The three nonzero Gaussian relative directions and the three standard
Eisenstein directions have the same image:

    {deltaA, deltaB, deltaC}.

A theorem at the Finset image level is preferred.

For example:

    gaussianNonzeroDirectionParities
      =
    eisensteinNonzeroDirectionParities
      =
    {deltaA, deltaB, deltaC}.

This is the formal content of:

    Gaussian local frame
      ≃
    Eisenstein local frame

at the mod-2 additive/exchange level.

## H. Induced Gaussian multiplication on V4

Define the mod-2 multiplication formula induced from Gaussian integer
multiplication:

    gaussianMulMod2 (x y : TrominoState) : TrominoState :=
      (x.1*y.1 + x.2*y.2,
       x.1*y.2 + x.2*y.1).

This is the formula from:

    (a + bi)(c + di)

after reducing coefficients modulo 2, where -1 = 1 in F2.

Prove compatibility:

    gaussianParity (x * y)
      =
    gaussianMulMod2 (gaussianParity x) (gaussianParity y).

Required calibrations:

    gaussianMulMod2 deltaB deltaB = deltaA
    gaussianMulMod2 deltaC deltaC = 0.

The second theorem exhibits a nonzero square-zero direction.

## I. Induced Eisenstein multiplication on V4

Define the mod-2 multiplication formula induced by TraceOneInt (-1), or
equivalently standard Eisenstein coordinates:

    eisensteinMulMod2 (x y : TrominoState) : TrominoState :=
      (x.1*y.1 + x.2*y.2,
       x.1*y.2 + x.2*y.1 + x.2*y.2).

Prove:

    eisensteinParity (x * y)
      =
    eisensteinMulMod2 (eisensteinParity x) (eisensteinParity y).

Also prove the standard-coordinate compatibility through eisensteinCoord.

Required calibrations:

    eisensteinMulMod2 deltaB deltaB = deltaC
    eisensteinMulMod2 deltaC deltaC = deltaB.

Hence deltaC is not square-zero on the Eisenstein side.

## J. Multiplicative-structure separation

Prove the finite theorem:

    gaussianMulMod2 deltaC deltaC = 0
    and
    eisensteinMulMod2 deltaC deltaC ≠ 0.

Also prove, preferably by finite cases:

    ∀ x : TrominoState,
      x ≠ 0 →
      eisensteinMulMod2 x x ≠ 0.

Then prove a clean obstruction theorem such as:

    no_zero_preserving_mul_equiv_gaussian_eisenstein :
      ¬ ∃ φ : TrominoState ≃ TrominoState,
          φ 0 = 0 ∧
          ∀ x y,
            φ (gaussianMulMod2 x y)
              =
            eisensteinMulMod2 (φ x) (φ y).

Suggested proof:

- deltaC is nonzero;
- gaussian deltaC² = 0;
- a bijection sends deltaC to a nonzero state;
- multiplication preservation would make its Eisenstein square zero;
- contradiction with the nonzero-square theorem.

This is stronger and cleaner than merely observing that the identity map is
not multiplicative.

Do not introduce global alternate Ring instances on TrominoState.

## K. Additive agreement / multiplicative disagreement theorem

Package the exact conceptual result:

1. both integral carriers admit surjective additive parity maps onto the same
   V4 carrier;
2. their three canonical nonzero directions have the same parity image;
3. their induced multiplications on that carrier are not multiplicatively
   equivalent.

This is the formal source interpretation:

    same 3+1 exchange geometry,
    different arithmetic multiplication.

Do not phrase this as a full theorem about quotient rings unless actual
quotient-ring types are constructed.

## L. Connection back to PortV4Chains

No new chain machinery is required.

Add small calibration theorems showing the common parity values
deltaA/deltaB/deltaC are exactly the coefficient values already used by:

- PortV4EdgeChain;
- triangle coloring differences;
- triangle-dual balanced Kirchhoff assignment.

The intended statement is:

    integral Gaussian/Eisenstein parity directions
      =
    TRM-035 V4 chain coefficients.

Keep this finite and explicit.

## M. Source / terminology boundary

The report must state clearly:

### Formalized

- GaussianInt and TraceOneInt(-1) both reduce additively to V4 through
  coordinate parity;
- the three nonzero local directions agree after this reduction;
- the TRM-035 frame equivalence is realized by Gaussian relative parity;
- the induced mod-2 multiplication formulas differ.

### Not claimed

- GaussianInt ≅ EisensteinInt as rings;
- Z[i]/(2) and the Eisenstein quotient are the same ring;
- full lattice equivalence;
- planar/topological equivalence;
- genus-zero exactness;
- Four Color theorem.

If desired, mention in the report that the multiplication obstruction is
exactly why the source's frame equivalence had to be additive/exchange-level.

## N. Computability / axioms

All parity maps, representative maps, and multiplication formulas must be
computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

## O. Audit

Create:

DkMathTest/Tromino/IntegralMod2BridgeAxiomAudit.lean

Audit at least:

1. Gaussian parity of 0, 1, i, 1+i;
2. Eisenstein parity of 0, 1, omega, 1+omega;
3. both parity maps are surjective;
4. representative sections;
5. Gaussian panel color = Gaussian integral parity;
6. Gaussian relative direction = frameDelta;
7. frame equivalence = Gaussian relative parity;
8. common nonzero direction image = {deltaA,deltaB,deltaC};
9. Gaussian multiplication compatibility;
10. Eisenstein multiplication compatibility;
11. Gaussian deltaC² = 0;
12. Eisenstein deltaC² = deltaB;
13. no nonzero Eisenstein square is zero;
14. no zero-preserving multiplicative equivalence theorem;
15. triangle/dual V4 coefficients agree with the integral parity directions.

## P. Validation

Build:

- DkMath.Tromino.IntegralMod2Bridge
- DkMathTest/Tromino/IntegralMod2BridgeAxiomAudit

Regression-build:

- DkMath.Tromino.LocalFrameEquiv
- DkMath.Tromino.PortV4Chains
- DkMathTest/Tromino/LocalFrameEquivAxiomAudit
- DkMathTest/Tromino/PortV4ChainsAxiomAudit
- DkMath.Lib.NumberTheory.EisensteinCoordinates

Run git diff --check, forbidden-construct scan, and #print axioms.

## Q. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-035.md

Record:

- Gaussian and Eisenstein additive parity maps;
- explicit four-state representatives;
- Gaussian block2 relative-parity interpretation;
- exact integral meaning of gaussianEisensteinFrameEquiv;
- common three nonzero parity directions;
- Gaussian/Eisenstein induced multiplication formulas;
- square-zero obstruction / multiplicative non-equivalence;
- connection to PortV4Chains coefficients;
- explicit statement that this closes the source-side local-frame bridge;
- recommendation to return next to genus-zero exactness
  im ∂2 = ker ∂1.

## Stop condition

Stop once the original source claim is realized on actual integral Gaussian
and Eisenstein coordinate carriers at the additive mod-2 level, and the
multiplicative distinction is kernel-checked.

Do not construct quotient rings, prove full ring/lattice equivalence,
genus-zero exactness, universal dual flow existence, topological realization,
or Four Color theorem results without review.
