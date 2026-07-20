# Note: FLT5 cp-003c normal form and cp-003d descent survey

## Result

cp-003c is complete in production. cp-003d has **Outcome C**: both proposed
routes reach compiling exact interfaces, but neither yet supplies a descent
measure together with reconstruction of a strictly smaller candidate.

No final FLT5 theorem is introduced, and `BranchA.lean` is unchanged.

## cp-003c: certified normal form

`DkMath.FLT.Five.NormalForm` adds the packet
`BranchBFifthPowerNormalForm x y z a b`. From every Branch-B counterexample it
now certifies:

```text
z - y = a^5
GN5 (a^5) y = b^5
x = a*b
z = y + a^5
0 < a, 0 < b
Coprime a y
Coprime a b
Coprime b y
5 does not divide a
```

The additional coprimality input is elementary:

```text
GN5 g y = g^4 + y * (...),
```

so a common prime divisor of `GN5 g y` and `y` would divide `g`, contradicting
`Coprime g y`.

The narrowed unknown receiver is:

```lean
abbrev BranchBFifthPowerCore : Prop :=
  forall {a b y : Nat},
    0 < a ->
    0 < y ->
    Nat.Coprime a y ->
    not (5 divides a) ->
    GN5 (a^5) y = b^5 ->
    False
```

`branchB_false_of_fifthPowerCore` connects this core to every Branch-B
counterexample.

## cp-003d Route A: real-quadratic projection

Scratch Lean proves the polynomial identity over `Int`:

```text
4 * GN5 g y
  = (2*(g+y)^2 + (g+y)*y + 2*y^2)^2
      - 5*((g+y)*y)^2.
```

For a normal-form packet, put

```text
U = 2*z^2 + z*y + 2*y^2
V = z*y.
```

Lean then proves both exact forms:

```text
U^2 - 5*V^2 = 4*b^5
norm (⟨U,V⟩ : Zsqrtd 5) = 4*b^5.
```

Mathlib supplies `Zsqrtd`, conjugation, and the multiplicative norm. The
workspace search found no ready-made real-quadratic fifth-power factorization,
unit classification, or descent theorem specialized to discriminant five.

There is also an arithmetic representation issue that must not be hidden:
the full ring of integers of the real quadratic field uses the half-integral
golden-ratio basis, while `Zsqrtd 5` represents `Z[sqrt(5)]`. The factor `4`
and the matching parity of `U` and `V` point exactly at this normalization.

The named missing Route-A interface is therefore:

```text
realQuadraticFiveDescent:
  primitive/parity-normalized U,V and U^2-5*V^2=4*b^5
  -> a reconstructed strictly smaller Branch-B or Branch-A packet.
```

Before proving it, the implementation needs an explicit integral golden-ratio
order, conjugate-factor coprimality up to the primes above 2 and 5, its units,
and the descent measure.

## cp-003d Route B: modulo 25

A finite `Fin 25` theorem was proved by `native_decide` over all residue
triples and then lifted in scratch Lean to arbitrary naturals:

```lean
CounterexamplePack x y z ->
not (5 divides (z-y)) ->
5 divides y or 5 divides z
```

Thus the proposed modulo-25 classification is true; coprimality is not even
needed for the finite residue implication after the equation and Branch-B
condition are present.

The two output cases are not yet one existing Branch-A orientation:

- `5 divides y`: swapping `x` and `y` points to the natural-difference
  Branch-A orientation `5 divides z-x`.
- `5 divides z`: modulo five points instead to the signed/sum condition
  `5 divides x+y`. This is not represented by the current natural subtraction
  `BranchACondition`.

The named missing Route-B interface is:

```text
signedBranchANormalForm:
  the natural-difference case and the sum-gap case
  -> one common five-adic descent packet with an explicit measure.
```

Until that signed packet and its decreasing reconstruction exist, Route B is a
classification and routing theorem, not a Branch-B refuter.

## Route selection

Route B is the recommended next checkpoint. It is more elementary, its mod-25
classification is already certified, and it promises to merge Branch B into
one exceptional five-adic descent rather than build real-quadratic algebra
immediately. Route A remains a precise fallback and now has a verified norm
equation endpoint.

The next safe task is to design the signed Branch-A packet and descent measure
before modifying `BranchA.lean`.
