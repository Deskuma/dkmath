# Codex Start Instruction

## Mission

Implement the first Lean checkpoints for the explicit three-dimensional Jacobian counterexample certificate.

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
hackathon/breaking-math-jacobian-counterexample
```

Workspace root:

```text
lean/dk_math
```

Read first:

```text
docs/hackathon/jacobian-counterexample-verification-260721/README.md
docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-implementation-design-260721.md
docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md
docs/BookOfMagic/0001_三重魔核と一意性解除.md
```

## Current checkpoint

Implement only:

```text
JAC-001 Polynomial syntax
JAC-002 Explicit collision
```

Do not implement derivatives, Jacobian matrices, determinants, complex scalar extension, normalization, or Book of Magic abstractions in this checkpoint.

## Create files

```text
DkMath/Hackathon/JacobianCounterexample3/Basic.lean
DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean
DkMath/Hackathon/JacobianCounterexample3/Collision.lean
```

Use the normal DkMath source header conventions found in nearby `DkMath/Hackathon` files.

## Mathematical object

Work over `ℚ`.

Use:

```lean
abbrev Var3 := Fin 3
abbrev Poly3Q := MvPolynomial Var3 ℚ
abbrev Point3Q := Var3 → ℚ
```

Coordinate order:

```text
0 = x
1 = y
2 = z
```

Define coordinate polynomials using `MvPolynomial.X`.

The polynomial map is exactly:

$$
P(x,y,z)=(1+xy)^3z+y^2(1+xy)(4+3xy)
$$

$$
Q(x,y,z)=y+3x(1+xy)^2z+3xy^2(4+3xy)
$$

$$
R(x,y,z)=2x-3x^2y-x^3z
$$

Recommended names:

```lean
x
y
z
counterexampleP
counterexampleQ
counterexampleR
counterexamplePoly
evalCounterexampleQ
```

Recommended map definition:

```lean
def counterexamplePoly : Fin 3 → Poly3Q
  | 0 => counterexampleP
  | 1 => counterexampleQ
  | 2 => counterexampleR
```

```lean
def evalCounterexampleQ (p : Point3Q) : Point3Q :=
  fun i => MvPolynomial.eval p (counterexamplePoly i)
```

If Lean does not accept numeric pattern matching directly on `Fin 3`, use `![counterexampleP, counterexampleQ, counterexampleR]` or a definition compatible with the local Mathlib version.

## Collision points

Define:

```lean
def p0Q : Point3Q := ![0, 0, -(1 / 4)]

def p1Q : Point3Q := ![1, -(3 / 2), 13 / 2]

def p2Q : Point3Q := ![-1, 3 / 2, 13 / 2]

def targetQ : Point3Q := ![-(1 / 4), 0, 0]
```

Make all rational literals unambiguous. If necessary, annotate selected literals with `: ℚ`.

## Required theorems

Prove:

```lean
theorem eval_p0Q :
    evalCounterexampleQ p0Q = targetQ
```

```lean
theorem eval_p1Q :
    evalCounterexampleQ p1Q = targetQ
```

```lean
theorem eval_p2Q :
    evalCounterexampleQ p2Q = targetQ
```

```lean
theorem p0Q_ne_p1Q : p0Q ≠ p1Q
```

```lean
theorem p0Q_ne_p2Q : p0Q ≠ p2Q
```

```lean
theorem p1Q_ne_p2Q : p1Q ≠ p2Q
```

Add a compact combined collision theorem only if it is naturally short. Do not introduce a large certificate structure yet.

## Suggested proof strategy

For image equalities:

```text
ext i
fin_cases i
norm_num [evalCounterexampleQ, counterexamplePoly,
  counterexampleP, counterexampleQ, counterexampleR,
  p0Q, p1Q, p2Q, targetQ, x, y, z]
```

If `norm_num` does not unfold `MvPolynomial.eval` enough, try a local sequence using:

```text
simp
ring_nf
norm_num
```

Avoid global simp attributes.

For point inequalities, project one coordinate:

```lean
intro h
have h0 := congrFun h 0
norm_num [p0Q, p1Q] at h0
```

Choose the coordinate that differs most simply.

## Import guidance

Start from minimal direct Mathlib imports for:

```text
MvPolynomial
MvPolynomial evaluation
Matrix/vector notation
fin_cases
ring/norm_num
```

Inspect nearby DkMath modules before selecting imports. Do not import all of `DkMath` unless required.

## Constraints

1. Do not use `sorry`.
2. Do not add axioms.
3. Do not use `native_decide`.
4. Do not manually define a function on points separately from polynomial evaluation.
5. `evalCounterexampleQ` must be generated from the `MvPolynomial` definitions.
6. Do not alter the published coefficients or collision points.
7. Do not implement the Jacobian in this checkpoint.
8. Keep the files small and reviewable.
9. Build only the new modules and their necessary import surface during iteration.
10. Do not refactor unrelated DkMath code.

## Verification

Run the appropriate Lean build commands for the new files.

Also provide a temporary local check or report showing:

```lean
#check eval_p0Q
#check eval_p1Q
#check eval_p2Q
#check p0Q_ne_p1Q
```

Do not commit temporary scratch files unless they belong in the final module.

## Report format

Return:

1. files created;
2. exact definitions added;
3. exact theorem names;
4. build result;
5. whether `MvPolynomial.eval` required any special normalization lemmas;
6. any import friction;
7. proposed next checkpoint, but do not implement it.

## Stop boundary

Stop immediately after JAC-001 and JAC-002 are complete and reported.

The next review decides whether to proceed to:

```text
JAC-003 Formal Jacobian
```
