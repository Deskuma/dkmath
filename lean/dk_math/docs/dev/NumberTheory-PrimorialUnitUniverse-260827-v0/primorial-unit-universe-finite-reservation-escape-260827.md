# PUU-L001: Finite Prime-Basis Reservation Escape

## Result

PUU-L001 is closed at the finite Euclidean boundary.  The implementation is
in `DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape`, with the
public facade `DkMath.NumberTheory.PrimorialUniverse`.

In this checkpoint, “prime” means the ordinary Lean predicate `Nat.Prime`.
No Unit Universe-relative primitive notion is introduced.

## Definitions

- `IsFinitePrimeBasis S`: every member of the finite set `S` is `Nat.Prime`.
- `finitePrimeBasisProduct S`: the finite product `M(S) = ∏ p ∈ S, p`.
- `ReservedByPrimeBasis S n`: some `p ∈ S` divides `n`.
- `finitePrimeBasisEscapePoint S`: `M(S) + 1`.
- `PrimeSupportContainedIn S n`: every prime divisor of `n` is a member of
  `S`.

The product is nonzero under the basis hypothesis, and every member of `S`
divides the product.

## Exact finite escape

For `p ∈ S`, the product divisibility packet and
`M(S) + 1` divisibility would imply `p ∣ 1`, contradicting `Nat.Prime p`.
Thus the escape point is not reserved by `S`:

```text
¬ ReservedByPrimeBasis S (finitePrimeBasisEscapePoint S)
```

The basis hypothesis also gives `1 < finitePrimeBasisEscapePoint S`, including
the empty-basis case where the product is `1`.

Applying `Nat.exists_prime_and_dvd` to this concrete nontrivial escape point
produces the main theorem:

```text
∃ q, Nat.Prime q ∧
  q ∣ finitePrimeBasisEscapePoint S ∧ q ∉ S
```

The proof uses the constructed `M(S) + 1` witness; it does not use an
infinitude theorem as a substitute for the finite escape construction.

## Support interface

`newPrime_mul_not_primeSupportContainedIn` records the false beam needed by
later scale-refinement work: if `q` is prime and `q ∉ S`, then a positive
multiple `q * k` cannot have all prime divisors contained in `S`.  The proof
uses only the direct divisor `q ∣ q * k`; no factorization data structure is
introduced.

The optional consumer
`finitePrimeBasisEscapePoint_not_primeSupportContainedIn` applies the new
prime divisor theorem directly to the escape point.

## Regression and semantic boundary

For `S = {2, 3}`, the product is `6` and the Euclidean escape point is `7`.
The number `5` is deliberately not called this escape: it is a survivor of a
`mod 6` primorial-wheel viewpoint, which is a later concept.

This checkpoint does not define Unit Universe real quantities, common
lattices, `3*u₁ = 15*u₂`, PowerSwap bridges, canonical primorial products,
reduced-residue wheels, reflection/lift arguments, square anchors, Legendre
arguments, or analytic prime counting.  Work stops at finite reservation
escape as required by PUU-L001.

## Verification

The focused module and its facade are checked with the corresponding `lake
build` targets.  Repository-wide build, commit, push, merge, and CI are not
part of this checkpoint.
