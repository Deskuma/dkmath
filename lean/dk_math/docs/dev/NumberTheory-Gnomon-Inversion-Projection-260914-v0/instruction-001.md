# instruction-001 — GNIP-001 degree-two Cosmic / GTail bridge

## Goal

Connect the approved neutral gnomon algebra to the existing Cosmic Formula `GTail` kernel at degree two.

This checkpoint should prove that the neutral square-growth band is exactly the degree-two Cosmic tail contribution with the correct coordinate orientation.

Do **not** modify Collatz or Legendre in this checkpoint.  Those remain GNIP-002 and GNIP-003.

## Read first

```text
DkMath/Gnomon/Algebra.lean
DkMath/Lib/Cosmic/GTail.lean
DkMath/NumberTheory/Legendre/MultiGaugeBridge.lean
```

The last file is read only to confirm the already-approved unit orientation:

```text
GTail 2 1 1 n = 2*n+1.
```

Do not import Legendre into the new bridge.

---

## 1. Preferred module

Add a neutral bridge module, preferably:

```text
DkMath/Gnomon/CosmicBridge.lean
```

Namespace:

```lean
namespace DkMath.Gnomon
```

Imports should be limited to:

```text
DkMath.Gnomon.Algebra
DkMath.Lib.Cosmic.GTail
```

plus only minimal dependencies required by those files.

Update `DkMath/Gnomon.lean` to export the bridge after it is stable.

---

## 2. Exact degree-two normalized shell

Prove the exact formula in the existing production orientation:

```lean
theorem GTail_two_one_eq_square_shell
    (u x : ℕ) :
    DkMath.CosmicFormula.GTail 2 1 u x = 2 * x + u := by
  ...
```

Naming may vary minimally, but the theorem must make the coordinate roles clear:

```text
first GTail coordinate after d,r = growth thickness u
second GTail coordinate         = current square side x
```

Do not silently swap these roles.

A semiring-general version is optional if it comes essentially for free and does not obscure the Nat bridge.  The Nat theorem is required.

---

## 3. Unit-thickness bridge

Prove:

```lean
theorem oddGnomon_eq_GTail_two_one_unit
    (x : ℕ) :
    oddGnomon x = DkMath.CosmicFormula.GTail 2 1 1 x
```

or the orientation-equivalent equality with sides reversed.

This is the generic source behind the already-existing Legendre fact:

```text
GTail 2 1 1 n = 2*n+1.
```

Do not import the Legendre theorem to prove this; prove it directly from neutral definitions / GTail.

---

## 4. Arbitrary-thickness Cosmic bridge

Prove the main exact bridge:

```lean
theorem squareGnomonBand_eq_mul_GTail_two_one
    (x u : ℕ) :
    squareGnomonBand x u =
      u * DkMath.CosmicFormula.GTail 2 1 u x
```

Mathematical content:

```text
square growth thickness u
= boundary thickness u
  × normalized degree-two Cosmic shell.
```

This theorem is the exact formal version of:

$$
(x+u)^2-x^2=u(2x+u).
$$

Do not introduce a second GN or GTail definition.

---

## 5. Reconstruct square growth through the Cosmic identity

Add a theorem whose proof actually passes through the existing Cosmic theorem
`add_pow_eq_mul_GTail_one_add_gap` or an equally canonical GTail theorem:

```lean
theorem square_add_mul_GTail_two_one
    (x u : ℕ) :
    x ^ 2 + u * DkMath.CosmicFormula.GTail 2 1 u x =
      (x + u) ^ 2
```

The point is not merely to re-run `ring`; this theorem should certify that the neutral gnomon square-growth law is the degree-two specialization of the existing Cosmic Formula kernel.

If the existing Cosmic theorem naturally yields `(u + x)^2`, normalize by commutativity explicitly.

Also give the compatibility corollary:

```lean
square_add_squareGnomonBand x u = ...
```

only if it provides a useful bridge / rewrite.  Do not duplicate the existing GNIP-000 theorem under a new decorative name.

---

## 6. Composition law in Cosmic coordinates

Transport the approved GNIP-000 composition law into a Cosmic form.  Preferred theorem:

```lean
theorem mul_GTail_two_one_add_thickness
    (x u v : ℕ) :
    (u + v) * DkMath.CosmicFormula.GTail 2 1 (u + v) x =
      u * DkMath.CosmicFormula.GTail 2 1 u x +
      v * DkMath.CosmicFormula.GTail 2 1 v (x + u)
```

This should preferably be derived from:

```text
squareGnomonBand_add
squareGnomonBand_eq_mul_GTail_two_one
```

rather than proved as unrelated polynomial algebra.

This is the first bridge-level conservation/composition theorem.

---

## 7. Shifted-unit decomposition in Cosmic form

Prove a bridge form of the unit-layer decomposition:

```lean
theorem mul_GTail_two_one_eq_sum_unit_GTail
    (x u : ℕ) :
    u * DkMath.CosmicFormula.GTail 2 1 u x =
      (Finset.range u).sum
        (fun i => DkMath.CosmicFormula.GTail 2 1 1 (x + i))
```

Prefer deriving this from the approved neutral theorem:

```text
squareGnomonBand_eq_sum_shifted_oddGnomon
```

plus the unit GTail bridge.

This theorem is important for the later inversion/projection audit:

```text
one thick band
<->
finite sum of atomic unit Cosmic shells.
```

---

## 8. Concrete regressions

Kernel-check at least:

```text
GTail 2 1 1 30 = 61
GTail 2 1 1 31 = 63
2 * GTail 2 1 2 30 = 124
```

For the last one, note carefully that:

```text
GTail 2 1 2 30 = 62
2 * 62 = 124
```

and this is the same two-step square band:

```text
61 + 63 = 124.
```

A regression explicitly equating these two readings is encouraged:

```text
2 * GTail 2 1 2 30
  = GTail 2 1 1 30 + GTail 2 1 1 31
```

No primality claim is attached to these examples.

---

## 9. Scope boundary

Do not in GNIP-001:

- edit `DkMath.Collatz.GnomonEvaluation`;
- edit any Legendre production module;
- claim a prime exists in a gnomon shell;
- add `SquareOffset` bridges;
- add MultiGauge transitions;
- interpret `cosmicSquareImage` or Real analytic scaling;
- add inversion/projection preservation claims;
- add Pascal / PetalAtom / Polyomino work.

GNIP-001 is only the exact degree-two algebraic/Cosmic bridge.

---

## 10. Validation

Run:

```text
lake build DkMath.Gnomon.CosmicBridge
lake build DkMath.Gnomon
```

Also run:

```text
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
```

No new axiom declarations.

---

## 11. Deliverable report

Create:

```text
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-001.md
```

Report:

1. Outcome.
2. Files added/changed.
3. Exact GTail orientation used.
4. Main unit and arbitrary-thickness bridge theorem names.
5. Whether the square-growth proof uses the existing Cosmic identity.
6. Whether composition was transported to Cosmic coordinates.
7. Whether shifted unit decomposition was transported to Cosmic coordinates.
8. Concrete 30/31 regressions.
9. Build results and axiom scan.
10. Whether GNIP-002 Collatz compatibility refactor is now justified.
11. Whether GNIP-003 Legendre open-gnomon bridge is now justified in principle, while remaining unimplemented.

Outcome policy:

```text
A — DEGREE-TWO COSMIC BRIDGE COMPLETE
    Unit shell, arbitrary band, square-growth identity, composition,
    and shifted unit decomposition all established.

B — CORE BRIDGE COMPLETE / TRANSPORT PARTIAL
    Main exact GTail bridge is established, but composition or shifted
    decomposition transport is blocked by an API issue. Record the blocker.

C — EXISTING COSMIC API ALREADY SUBSUMES TARGET
    Reuse an exact existing neutral theorem rather than duplicate it.
```
