# FLT7-FUSION-002 theta-jet report

Date: 2026-07-29

## Fixed in Lean

The integral change of basis is now explicit:

```text
A = x0 + 3*x1 + 9*x2
B = x1 + 6*x2
C = x2
x = A + B*theta + C*theta^2.
```

For `x = A + B*theta + C*theta^2`, Lean checks

```text
thetaLinearInt (x^7) = 7*G(A,B,C)
thetaSquareInt (x^7) = 7*H(A,B,C).
```

The exact triangular presentation is

```text
G = B*GB(A,B,C) + 7*C^2*GC(A,C)
H = C*HC(A,B,C) + B^2*HB(A,B).
```

The dependencies matter: the shorter dependency claims in the design note
would omit genuine cross terms. With the corrected factors Lean proves

```text
GB = A^6       (mod 7)
GC = -3*A^5    (mod 7)
HC = A^6       (mod 7)
HB = 3*A^5     (mod 7).
```

On the independent integer route Lean also proves

```text
quotientRoot = 1       (mod 7)
gapRoot = a^2*m        (mod 7),
```

where the second formula uses the canonical inner-coordinate names.

## Consequence and remaining gate

These identities validate the proposed triangular local mechanism and avoid
the unrestricted degree-seven zero-locus problem. They do not by themselves
prove exact depths. The next theorem must attach the actual left and right
source equations, prove the theta-constant coordinate is a seven-unit, and
then perform the noncancellation argument yielding

```text
v7(B)=3, v7(C)=6.
```

Only after that argument may Outcome A be formally excluded and the finite
theta-jet sector packet be declared complete. No such exclusion, reconstructed
Fermat chart, descent provider, or FLT7 theorem is claimed in this report.
