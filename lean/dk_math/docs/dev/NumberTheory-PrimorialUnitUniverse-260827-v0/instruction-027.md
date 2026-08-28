# PUU-L027 — Square-Anchor Canonical Phase Transport / Successor Carry Law

## 0. Status / purpose

PUU-L026 completed revised-roadmap Phase E1:

```text
C(b) = -b / M
R(a) =  a / M
phase pair = C(b) ± R(a)
```

and proved that changing an old phase representative `b` rigidly translates the phase pair while preserving the radius.

PUU-L027 begins Phase E2: return to the actual moving square anchor `n -> n+1` and connect the phase/center/radius coordinates to the provider-side square-anchor orbit from PUU-L010.

A critical typing point must be preserved:

- `squareAnchorWheelProjection S n = n^2 mod M` is the **square-value coordinate** from PUU-L010;
- an element `b ∈ squareAnchorPhaseFiber S n` is an **anchor coordinate** satisfying `b^2 ≡ n^2 mod M`.

The canonical anchor-coordinate representative is therefore `n mod M`, not `n^2 mod M`.

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport
```

Preferred imports:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexCenterTransport
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Canonical phase representative

Define the canonical one-period anchor coordinate

```lean
def squareAnchorPhaseRepresentative
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  primeBasisWheelProjection S n
```

or use the existing projection directly if an extra definition adds no value.

Prove:

```lean
squareAnchorPhaseRepresentative_mem_phaseFiber
```

under `hS : IsFinitePrimeBasis S`, with conclusion

```text
squareAnchorPhaseRepresentative S n ∈ squareAnchorPhaseFiber S n.
```

The proof should explicitly use the fact that reducing `n` modulo `M` preserves `n^2 mod M`.

Also expose the bridge to PUU-L010:

```lean
squareAnchorWheelProjection_eq_representative_square
```

conceptually:

```text
squareAnchorWheelProjection S n
  = (squareAnchorPhaseRepresentative S n)^2 mod M.
```

This keeps the two levels visible:

```text
anchor coordinate r_n = n mod M
square-value coordinate = r_n^2 mod M = n^2 mod M.
```

---

## 2. Successor transport of the canonical representative

Prove the anchor-coordinate successor law

```lean
squareAnchorPhaseRepresentative_succ
```

with conclusion

```text
r_(n+1) = (r_n + 1) mod M.
```

This is distinct from the PUU-L010 square-value successor law

```text
n^2 -> n^2 + (2*n+1).
```

Record both in the module/report; do not conflate them.

---

## 3. The period carry

Define the canonical step carry

```lean
def squareAnchorPhaseStepCarry
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  (squareAnchorPhaseRepresentative S n + 1) /
    finitePrimeBasisProduct S
```

or an equivalent definition.

Prove the exact decomposition

```lean
squareAnchorPhaseRepresentative_succ_decomposition
```

conceptually:

```text
r_n + 1 = r_(n+1) + carry_n * M.
```

Since `0 <= r_n < M`, prove:

```text
carry_n <= 1
```

and preferably the exact branch classification

```text
carry_n = 1 <-> r_n + 1 = M
carry_n = 0 <-> r_n + 1 < M
```

or an equivalent clean pair of theorems.

The carry is the finite-wheel wrap indicator for the canonical anchor coordinate.

---

## 4. Canonical square-anchor center and radius

Define provider-side coordinates for the moving anchor:

```lean
noncomputable def squareAnchorFreshPrimeCenter
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  freshPrimeDeletedCenterCoord S q
    (squareAnchorPhaseRepresentative S n)

noncomputable def squareAnchorFreshPrimeRadius
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  freshPrimePhaseRadius S q n
```

The radius is attached to the moving anchor `n`; the center is attached to its canonical old representative `r_n`.

Also define or reuse the unit step radius

```text
U := freshPrimePhaseRadius S q 1 = M^-1.
```

A named definition is optional; a public theorem identifying `R(n+1)-R(n)` with `R(1)` is more important.

---

## 5. Radius successor law

For fresh prime `q`, prove

```lean
squareAnchorFreshPrimeRadius_succ
```

with conclusion

```text
R(n+1) - R(n) = R(1)
```

in `ZMod q`.

Equivalently:

```text
R(n+1) = R(n) + M^-1.
```

This is immediate algebraically from `R(a)=a*M^-1`, but expose it as the dynamic radius law.

No coprime-anchor assumption should be needed for this identity itself.

---

## 6. Center successor carry law — central theorem

Using PUU-L026 center transport and the representative decomposition, prove

```lean
squareAnchorFreshPrimeCenter_succ
```

with conclusion equivalent to

```text
C_(n+1) - C_n
  = (carry_n : ZMod q) - freshPrimePhaseRadius S q 1.
```

This is the central new theorem of PUU-L027.

Mathematical reading:

```text
ordinary +1 anchor motion
  = constant affine drift -M^-1
  + discrete period-wrap correction carry_n.
```

The theorem should use only provider-side finite arithmetic and fresh-prime invertibility.

---

## 7. Dynamic phase-pair coordinates

Define, or expose through theorem abbreviations,

```text
Pplus(n)  := C_n + R_n
Pminus(n) := C_n - R_n.
```

Then derive the exact successor laws:

```lean
squareAnchorFreshPrimePlus_succ
```

```text
Pplus(n+1) - Pplus(n) = carry_n
```

and

```lean
squareAnchorFreshPrimeMinus_succ
```

```text
Pminus(n+1) - Pminus(n)
  = carry_n - 2 * freshPrimePhaseRadius S q 1.
```

These should be derived from the center and radius transport laws, not reproved from CRT enumeration.

This is the key dynamical split:

```text
plus sheet  : moves only when the old-period representative wraps
minus sheet : carries a constant affine drift plus the same wrap correction.
```

If introducing `Pplus/Pminus` definitions makes the public API cleaner, do so.  Otherwise theorem-local expressions are acceptable.

---

## 8. Semantic connection to actual phase lifts

Under the existing hypotheses needed for the distinguished fresh-prime phase lifts — in particular an odd fresh prime and the coprime-anchor assumptions already used by L020–L025 — connect the dynamic coordinates to actual `+a/-a` lift indices over the canonical representative.

At minimum, prove that any distinguished plus/minus/deleted witnesses over

```text
b = squareAnchorPhaseRepresentative S n
```

agree in `ZMod q` with

```text
C_n + R_n,
C_n,
C_n - R_n.
```

Reuse L026.  Do not rebuild CRT existence unless a small wrapper is needed.

The transport identities themselves should remain algebraic/provider-side and should not depend on Legendre or square-shell escape.

---

## 9. Visible regression

Use a basis where the representative both advances normally and wraps.

Preferred minimal example:

```text
S = {2,3}, M = 6, q = 5.
```

For example compare anchors near the wrap:

```text
n = 4 : r_n = 4, carry = 0
n = 5 : r_n = 5, carry to n=6 is 1
n = 6 : r_n = 0.
```

Verify through public L027 API that:

```text
4 -> 5 : center displacement = -M^-1
5 -> 0 : center displacement = 1 - M^-1
```

and corresponding plus/minus dynamic coordinates obey the stated successor laws.

Prefer a regression that explicitly exhibits both carry `0` and carry `1` rather than only detached arithmetic.

---

## 10. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-square-anchor-canonical-phase-transport-260828.md
```

The report must state explicitly:

1. L026 transported phase geometry across arbitrary old representatives; L027 specializes this to the actual moving anchor `n -> n+1`.
2. The canonical phase representative is `n mod M`, while PUU-L010's square-value coordinate is `n^2 mod M`.
3. Anchor-coordinate motion is `+1 mod M`; square-value motion is `+(2*n+1) mod M`.
4. The carry is the wrap correction of the canonical representative.
5. Center motion is `carry - M^-1`.
6. Radius motion is `+M^-1`.
7. Therefore plus/minus phase coordinates have the asymmetric successor laws above.
8. This remains independent provider-side transport and is not an escape or prime-existence theorem.

---

## 11. A+ rubric

Outcome A+ if the implementation establishes:

1. canonical phase representative `n mod M` and its phase-fiber membership;
2. bridge from that representative to PUU-L010 square-value projection;
3. exact `r_(n+1) = (r_n+1) mod M` law;
4. a `0/1` period carry and exact decomposition;
5. moving center/radius coordinates;
6. radius successor law `Delta R = M^-1`;
7. center successor law `Delta C = carry - M^-1`;
8. plus-sheet successor law `Delta Pplus = carry`;
9. minus-sheet successor law `Delta Pminus = carry - 2*M^-1`;
10. at least one wrap/non-wrap regression;
11. facade export + docstrings + report.

---

## STOP

Do **not** add in L027:

- Legendre / `SquareCell` / `escapingSquareOffsets`,
- square-shell escape existence,
- Jacobsthal / wheel-gap bounds,
- neutral-seat primality/compositeness,
- PowerSwap / GN / CosmicFormula,
- PNT / RH,
- prime powers,
- asymptotic density,
- a new local reflection/cardinality hierarchy unrelated to transport,
- a claim that the transport law itself already obstructs complete square-shell reservation.

L027 is the first square-anchor **dynamic transport** checkpoint.  Its job is to turn the completed static phase geometry into an exact successor law; consumer consequences come only after a separate anti-relabeling / coverage-obstruction audit.
