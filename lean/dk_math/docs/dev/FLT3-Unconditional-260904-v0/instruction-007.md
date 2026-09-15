# instruction-007 — Eisenstein Norm-Euclidean Foundation

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-005 completed with Outcome A.

Checkpoint role: FLT3U-006A.

## 1. Mission

TraceOneInt (-1) / EisensteinInt に honest な norm-EuclideanDomain instance を構成する。

この checkpoint は cube extraction そのものを行わない。

目的は次 checkpoint FLT3U-006B で Mathlib の generic coprime-power theorem を使えるようにすることである。

Do not introduce a generic EuclideanDomain (TraceOneInt s).

Only the concrete s = -1 Eisenstein order is in scope.

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinSubstrate.lean
    lean/dk_math/DkMath/FLT/Three/EisensteinConjugateCoprime.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-006.md

architecture template only:

    lean/dk_math/DkMath/FLT/Seven/QuadraticEuclidean.lean
    lean/dk_math/DkMath/FLT/Seven/QuadraticCoprimeFactor.lean

FLT7 modules を production import しない。

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/EisensteinEuclidean.lean

Direct imports:

    import DkMath.FLT.Three.EisensteinConjugateCoprime
    import Mathlib.Algebra.Order.Round
    import Mathlib.RingTheory.EuclideanDomain

必要なら current transitive imports を見て最小化してよい。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. Honest domain foundation

First prove zero detection for the positive-definite Eisenstein norm.

For

$$
x=(r,s),
$$

$$
N(x)=r^2+rs+s^2.
$$

Use the completed-square identity

$$
4N(x)=(2r+s)^2+3s^2.
$$

Mandatory theorem:

$$
N(x)=0\iff x=0.
$$

Candidate:

    theorem eisenstein_norm_eq_zero_iff
        (x : EisensteinInt) :
        norm x = 0 ↔ x = 0

Then prove:

    NoZeroDivisors EisensteinInt
    Nontrivial EisensteinInt
    IsDomain EisensteinInt

using norm multiplicativity.

Do not assert domain structure without a proof.

## 5. Rational coordinate norm

Introduce only the local rational coordinate type needed for Euclidean division.

Candidate:

    abbrev EisensteinRat := ℚ × ℚ

    def eisensteinRatNorm (x : EisensteinRat) : ℚ :=
      x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2

Completed square:

$$
N_{\mathbb Q}(u,v)
=
\left(u+\frac v2\right)^2+\frac34v^2.
$$

Mandatory theorem.

## 6. Covering-cell bound

For

$$
|v|\le\frac12
$$

and

$$
\left|u+\frac v2\right|\le\frac12,
$$

prove

$$
N_{\mathbb Q}(u,v)\le\frac7{16}<1.
$$

Suggested theorem surfaces:

    eisensteinRatNorm_le_seven_sixteen
    eisensteinRatNorm_lt_one

This is the geometric heart of Euclidean division.

Do not use floating-point approximations.

## 7. Quotient numerator

For x,y : EisensteinInt define

$$
QNum(x,y)=x\overline y.
$$

For s = -1 the coordinates must be verified as

$$
QNum(x,y)_{\rm fst}
=
x_{\rm fst}(y_{\rm fst}+y_{\rm snd})
+
x_{\rm snd}y_{\rm snd},
$$

$$
QNum(x,y)_{\rm snd}
=
x_{\rm snd}y_{\rm fst}
-
x_{\rm fst}y_{\rm snd}.
$$

Do not copy the s = -2 first-coordinate coefficient 2.

This coefficient is 1 here.

## 8. Rational quotient coordinates

For y != 0 define

$$
(A,B)
=
\left(
\frac{QNum_{\rm fst}}{N(y)},
\frac{QNum_{\rm snd}}{N(y)}
\right).
$$

As in the FLT7 template, the definition may still be total at y = 0 because division in Q is total; the Euclidean quotient-zero theorem handles that branch.

Candidate:

    def eisensteinQuotientCoords
        (x y : EisensteinInt) :
        EisensteinRat := ...

## 9. Skew rounding

Use the lattice geometry for tau^2 - tau + 1 = 0.

Choose

$$
n=\operatorname{round}(B).
$$

Then choose

$$
m=
\operatorname{round}
\left(
A+\frac{B-n}{2}
\right).
$$

Define quotient

$$
q=m+n\tau.
$$

Candidate names:

    eisensteinRoundedSnd
    eisensteinRoundedFst
    eisensteinQuotient

Required error bounds:

$$
|B-n|\le\frac12,
$$

$$
\left|
(A-m)+\frac{B-n}{2}
\right|
\le\frac12.
$$

Use Mathlib abs_sub_round.

## 10. Remainder

Define

$$
r=x-qy.
$$

Candidate:

    def eisensteinRemainder
        (x y : EisensteinInt) :
        EisensteinInt :=
      x - eisensteinQuotient x y * y

Prove reconstruction:

$$
yq+r=x.
$$

and quotient at zero:

$$
q(x,0)=0.
$$

## 11. Rational remainder norm identity

For y != 0 prove

$$
N(r)
=
N(y)\,
N_{\mathbb Q}(A-m,B-n)
$$

after casting to Q.

This should be the s = -1 specialization of the algebraic calculation used in FLT7 QuadraticEuclidean.

Verify every coefficient independently.

Do not import the FLT7 theorem.

## 12. Euclidean size

Define

$$
\operatorname{size}(x)=|N(x)|_{\rm nat}.
$$

Since Eisenstein norm is nonnegative, this is just the Nat shadow of N.

Candidate:

    def eisensteinEuclideanSize
        (x : EisensteinInt) : ℕ :=
      Int.natAbs (norm x)

Prove:

- size > 0 for x != 0
- size(x*y) = size(x)*size(y)
- norm nonnegative
- remainder size < divisor size for y != 0

The strict inequality follows from the cell bound < 1 and positive N(y).

## 13. EuclideanDomain instance

Construct:

    noncomputable instance traceOneNegOneEuclideanDomain :
      EuclideanDomain (TraceOneInt (-1))

or a namespace-equivalent name.

The fields should mirror the honest proof pattern:

- quotient
- quotient_zero
- remainder
- quotient_mul_add_remainder_eq
- well-founded relation by measure size
- remainder_lt
- mul_left_not_lt

Do not use an axiom or noncomputable choice for the division algorithm beyond Mathlib round.

## 14. Optional GCDMonoid instance

If it is literally a one-line safe consequence and helps verification, add:

    noncomputable instance traceOneNegOneGCDMonoid :
      GCDMonoid EisensteinInt :=
      EuclideanDomain.gcdMonoid EisensteinInt

However, preferred ownership is FLT3U-006B.

Do not begin cube extraction in this checkpoint.

## 15. Important instance boundary

Generic TraceOneInt s is only a CommRing.

Do not add:

    instance : IsDomain (TraceOneInt s)
    instance : EuclideanDomain (TraceOneInt s)

for arbitrary s.

Only the concrete (-1) specialization is valid here.

Also do not interfere with existing (-2) FLT7 instances.

## 16. Axiom / dependency gate

The EuclideanDomain instance is a foundational theorem, so audit carefully.

Required:

- no sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no import of FLT7 Euclidean implementation
- no import of FLT5 algebraic implementation
- no provisional GEisenstein descent dependency

Use #print axioms on:

    eisenstein_norm_eq_zero_iff
    eisenstein_remainder_size_lt
    traceOneNegOneEuclideanDomain

or actual identifiers.

## 17. Required report

Create:

    report-007.md

Record:

1. zero-norm iff zero proof
2. domain instances
3. rational norm completed square
4. exact covering bound 7/16
5. quotient numerator coordinate formulas
6. rounding convention
7. remainder norm identity
8. strict remainder-size theorem
9. EuclideanDomain instance
10. whether GCDMonoid instance was added
11. actual imports
12. focused build result
13. axiom audit
14. exact next gate for U006B
15. Outcome A / B / C

## 18. Verification

focused build:

    lake build DkMath.FLT.Three.EisensteinEuclidean

Also run any focused #check / #print axioms needed.

## 19. Completion condition

FLT3U-006A is complete when kernel-checked source provides

$$
\operatorname{EuclideanDomain}(\operatorname{EisensteinInt})
$$

with Euclidean size derived from the Eisenstein norm and a proved strict remainder bound.

Stop there.

FLT3U-006B will then use the resulting GCDMonoid / unique-factorization infrastructure plus

$$
\beta\overline\beta=B^3
$$

and the already proved conjugate relative primality to obtain

$$
\beta=\varepsilon\gamma^3.
$$
