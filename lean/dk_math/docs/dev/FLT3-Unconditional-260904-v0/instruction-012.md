# instruction-012 — Positive Strict Descent Reconstruction

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-009A completed with Outcome A.

Checkpoint role: FLT3U-009B.

## 1. Mission

EisensteinSignedCubeFactors が保持する signed relation

$$
r+s=(r+s)
$$

と

$$
|r|=R^3,\qquad
|s|=S^3,\qquad
|r+s|=T^3
$$

を sign routing し、R,S,T の permutation から新しい positive primitive cubic solution

$$
x^3+y^3=z^3
$$

を構成する。

さらに

$$
xyz=RST=A<abc
$$

を証明し、strict descent packet として固定する。

この checkpoint で mathematical descent construction を完了する。
well-founded closure / final FLT3 theorem は U010 に残す。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/EisensteinDescentFactors.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-011.md

必要なら sign / natAbs API のためだけに generic Mathlib import を追加してよい。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/PrimitiveCubicDescent.lean

Direct import:

    import DkMath.FLT.Three.EisensteinDescentFactors

## 4. Define the primitive cubic pack

There is no production FLT3-local primitive counterexample pack in the current tower.

Add a minimal reusable Prop structure.

Candidate:

    structure PrimitiveCubicPack (x y z : ℕ) : Prop where
      hx : 0 < x
      hy : 0 < y
      hz : 0 < z
      coprime_xy : Nat.Coprime x y
      equation : x ^ 3 + y ^ 3 = z ^ 3

Keep only the fields required by the current tower.

Do not import FLT5 / FLT7 CounterexamplePack types.

## 5. Constructor for the original primitive hypotheses

Add:

    def primitiveCubicPack_of_hypotheses
        {a b c : ℕ}
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
        (hab : Nat.Coprime a b)
        (hEq : a^3 + b^3 = c^3) :
        PrimitiveCubicPack a b c

This gives U010 a single source object.

## 6. Measure

Define:

    def primitiveCubicMeasure
        {x y z : ℕ} (_ : PrimitiveCubicPack x y z) : ℕ :=
      x * y * z

or a pack-indexed equivalent.

Prefer a theorem-friendly surface where the measure is definitionally x*y*z.

## 7. Signed-value recovery

For p : EisensteinSignedCubeFactors a b c, obtain exact signed alternatives:

$$
r=(R:\mathbb Z)^3
\quad\text{or}\quad
r=-(R:\mathbb Z)^3,
$$

$$
s=(S:\mathbb Z)^3
\quad\text{or}\quad
s=-(S:\mathbb Z)^3,
$$

$$
r+s=(T:\mathbb Z)^3
\quad\text{or}\quad
r+s=-(T:\mathbb Z)^3.
$$

These follow from:

$$
|r|_{\rm nat}=R^3
$$

etc., together with sign cases on each nonzero integer.

Suggested helper:

    theorem int_eq_cube_or_neg_cube_of_natAbs_eq
        {x : ℤ} {n : ℕ}
        (h : x.natAbs = n^3) :
        x = (n : ℤ)^3 ∨ x = -((n : ℤ)^3)

Exact disjunction orientation may differ.

Do not use Real abs.

## 8. Product positivity constrains signs

From source.product_eq and A_pos:

$$
r\,s\,(r+s)=A^3>0.
$$

Use this to eliminate impossible sign combinations.

The only possible geometric patterns are:

### Case P — both r and s positive

$$
r=R^3,\qquad
s=S^3,\qquad
r+s=T^3.
$$

Then

$$
R^3+S^3=T^3.
$$

new triple:

$$
(x,y,z)=(R,S,T).
$$

### Case L — r positive, s negative

Product positivity forces r+s negative.

Thus

$$
r=R^3,\qquad
s=-S^3,\qquad
r+s=-T^3.
$$

Then

$$
R^3+T^3=S^3.
$$

new triple:

$$
(x,y,z)=(R,T,S).
$$

### Case R — r negative, s positive

Product positivity forces r+s negative.

Thus

$$
r=-R^3,\qquad
s=S^3,\qquad
r+s=-T^3.
$$

Then

$$
S^3+T^3=R^3.
$$

new triple:

$$
(x,y,z)=(S,T,R).
$$

The case r<0 and s<0 is impossible because r+s<0 and the product would be negative.

Likewise opposite-sign cases with positive r+s are impossible by product positivity.

Do not enumerate eight raw sign combinations unless Lean forces it; use order facts to reduce the branches.

## 9. Sign-routing theorem

Provide one theorem exposing exactly one of the three positive cube equations.

Candidate:

    theorem signed_cube_roots_route
        (p : EisensteinSignedCubeFactors a b c) :
        (p.R^3 + p.S^3 = p.T^3) ∨
        (p.R^3 + p.T^3 = p.S^3) ∨
        (p.S^3 + p.T^3 = p.R^3)

This theorem is mandatory.

It should be proved from the actual signed r,s relation, not by a numerical assumption.

## 10. Construct the next positive primitive pack

For each route:

### route 1

    PrimitiveCubicPack R S T

using:

- R_pos, S_pos, T_pos
- coprime_RS
- equation R^3 + S^3 = T^3

### route 2

    PrimitiveCubicPack R T S

using:

- R_pos, T_pos, S_pos
- coprime_RT
- equation R^3 + T^3 = S^3

### route 3

    PrimitiveCubicPack S T R

using:

- S_pos, T_pos, R_pos
- coprime_ST
- equation S^3 + T^3 = R^3

No gcd renormalization is necessary because U009A already proved pairwise coprimality.

## 11. Strict descent packet

Package the result.

Candidate:

    structure PrimitiveCubicStrictDescent
        {a b c : ℕ}
        (source : PrimitiveCubicPack a b c) : Type where
      x y z : ℕ
      next : PrimitiveCubicPack x y z
      product_eq_A :
        x * y * z = ...
      measure_lt :
        x * y * z < a * b * c

However, U010 will be easier if the packet also retains the U009A factors.

Recommended:

    structure PrimitiveCubicStrictDescent
        (a b c : ℕ) : Type where
      source : PrimitiveCubicPack a b c
      factors : EisensteinSignedCubeFactors a b c
      x y z : ℕ
      next : PrimitiveCubicPack x y z
      next_product_eq :
        x * y * z = factors.source.A
      measure_lt :
        x * y * z < a * b * c

The source and factors must come from the same primitive solution.

## 12. Same-source construction

The strict descent constructor must start from one PrimitiveCubicPack and build factors from exactly its fields:

    eisensteinSignedCubeFactors_of_primitive_solution
      source.hx source.hy source.hz
      source.coprime_xy source.equation

Then route signs and construct next.

Candidate:

    noncomputable def primitiveCubicStrictDescent
        {a b c : ℕ}
        (source : PrimitiveCubicPack a b c) :
        PrimitiveCubicStrictDescent a b c

Classical.choice is acceptable only for choosing the routed branch if needed.

No second independent reconstruction of the source triple.

## 13. Product is exactly A

In all three permutations:

$$
xyz=RST.
$$

Since U009A has

$$
RST=A,
$$

prove mandatory:

$$
xyz=A.
$$

This should be straightforward by commutativity.

Do not settle for xyz ≤ A.

## 14. Strict decrease

Use U009A:

$$
RST=A<abc.
$$

and xyz=RST.

Mandatory theorem/field:

$$
xyz<abc.
$$

No alternate measure is needed.

This is the exact strict descent required by U010.

## 15. Optional next-coordinate bounds

Do not spend effort proving x<a, y<b, z<c individually.

Only the product measure is required.

If some individual bound is free, it may be recorded but is not needed.

## 16. Closure-facing theorem

Expose a theorem in the simple form U010 can consume:

    theorem exists_smaller_primitiveCubicPack
        {a b c : ℕ}
        (source : PrimitiveCubicPack a b c) :
        ∃ x y z : ℕ,
          PrimitiveCubicPack x y z ∧
          x * y * z < a * b * c

This theorem is mandatory even if the richer strict descent packet exists.

Prefer deriving it from primitiveCubicStrictDescent.

## 17. Critical correctness gates

### Gate A — sign routing

The new equation must come from exact sign analysis of r,s,r+s.

Do not use natAbs identities alone to assert one of the three cube equations.

### Gate B — primitive property

The chosen two left coordinates must use the corresponding pairwise-coprime theorem:

- R,S -> coprime_RS
- R,T -> coprime_RT
- S,T -> coprime_ST

### Gate C — strict measure

The next product must be definitionally/permutation-equal to R*S*T and then to A.

Do not compare only one coordinate.

### Gate D — no circular FLT3

Do not use any theorem asserting nonexistence of positive cubic solutions.

The only contradiction closure belongs to U010.

## 18. Non-goals

Do not implement:

- Nat strong induction closure
- FLT_d3_unconditional
- arbitrary positive triple gcd normalization
- fermatThree_no_positive_solution
- public aggregator
- changes to DkMath.FLT.Main
- NoSqOnS0 removal/adapters

## 19. Required report

Create:

    report-012.md

Record:

1. PrimitiveCubicPack surface
2. measure definition
3. signed-value recovery helper
4. exact three sign routes
5. proof impossible sign configurations are excluded
6. signed_cube_roots_route theorem
7. next primitive pack for each branch
8. PrimitiveCubicStrictDescent packet
9. next product = A
10. next product < source product
11. closure-facing exists_smaller theorem
12. direct imports
13. focused build result
14. axiom audit
15. exact U010 closure task
16. Outcome A / B / C

## 20. Verification

Focused build:

    lake build DkMath.FLT.Three.PrimitiveCubicDescent

Major routing / descent / exists_smaller theorem: #print axioms.

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 theorem shortcut
- no FLT5 / FLT7 production import
- no GEisenstein provisional descent dependency

## 21. Completion condition

FLT3U-009B is complete when every PrimitiveCubicPack a b c yields a strictly smaller PrimitiveCubicPack x y z with

$$
x^3+y^3=z^3,
$$

$$
\gcd(x,y)=1,
$$

$$
x,y,z>0,
$$

and

$$
xyz<abc.
$$

Stop there.

FLT3U-010 will close the primitive theorem by strong induction on the product measure.
