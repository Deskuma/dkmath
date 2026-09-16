# GNIP-001 report — degree-two Cosmic / GTail bridge

## 1. Outcome

**A — DEGREE-TWO COSMIC BRIDGE COMPLETE.**

The neutral square-growth layer is connected to the existing production
`GTail` kernel at degree two.  The unit shell, arbitrary-thickness band,
Cosmic reconstruction, composition transport, shifted unit decomposition,
and concrete regressions are all kernel-checked.

## 2. Files added or changed

```text
DkMath/Gnomon/CosmicBridge.lean       added
DkMath/Gnomon.lean                    updated to export CosmicBridge
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-001.md
                                      added
```

No Collatz or Legendre production file was changed.

## 3. Exact GTail orientation

The existing production orientation is:

```text
GTail 2 1 x u = x + 2*u.
```

The square-growth bridge deliberately uses the reversed coordinates:

```text
GTail 2 1 u x = 2*x + u.
```

Thus the first coordinate after `(d,r)` is the growth thickness `u`, and the
second is the current square side `x`.  This is stated in the module header
and encoded by:

```text
GTail_two_one_eq_square_shell
```

## 4. Main bridge theorem names

```text
GTail_two_one_eq_square_shell
oddGnomon_eq_GTail_two_one_unit
squareGnomonBand_eq_mul_GTail_two_one
square_add_mul_GTail_two_one
square_add_squareGnomonBand_eq_mul_GTail_two_one
```

The main exact identities are:

```text
oddGnomon x = GTail 2 1 1 x
squareGnomonBand x u = u * GTail 2 1 u x
```

## 5. Existing Cosmic identity usage

`square_add_mul_GTail_two_one` is proved from the existing
`DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap` theorem, specialized
with the reversed coordinates `(u, x)` and normalized by commutativity.  It is
not an independent re-run of the square polynomial identity.

## 6. Composition transport

The approved neutral composition law is transported to Cosmic coordinates by:

```text
mul_GTail_two_one_add_thickness
```

It proves:

```text
(u+v) * GTail 2 1 (u+v) x
  = u * GTail 2 1 u x + v * GTail 2 1 v (x+u).
```

The proof proceeds through `squareGnomonBand_add` and the exact band/GTail
bridge.

## 7. Shifted unit decomposition

The unit-layer decomposition is transported by:

```text
mul_GTail_two_one_eq_sum_unit_GTail
```

It proves:

```text
u * GTail 2 1 u x
  = (Finset.range u).sum (fun i => GTail 2 1 1 (x+i)).
```

The proof uses the approved neutral shifted-sum theorem and the unit GTail
bridge pointwise.

## 8. Concrete regressions

Kernel-checked examples include:

```text
GTail 2 1 1 30 = 61
GTail 2 1 1 31 = 63
2 * GTail 2 1 2 30 = 124
2 * GTail 2 1 2 30
  = GTail 2 1 1 30 + GTail 2 1 1 31
```

These are arithmetic regressions only; no primality claim is made.

## 9. Dependencies and validation

`DkMath.Gnomon.CosmicBridge` imports only:

```text
DkMath.Gnomon.Algebra
DkMath.Lib.Cosmic.GTail
```

Validation from `lean/dk_math`:

```text
lake build DkMath.Gnomon.CosmicBridge
Build completed successfully (8657 jobs).

lake build DkMath.Gnomon
Build completed successfully (8658 jobs).

git diff --check
passed with no diagnostics.
```

The new/changed Lean files were scanned for `sorry`, `admit`, and `axiom`; no
matches were found.  No new axiom declaration was added.

The three untracked files from this checkpoint were additionally checked with
`git diff --no-index --check` against `/dev/null`; no whitespace diagnostics
were produced.

## 10. GNIP-002 status

The bridge makes the neutral square facts available as an exact Cosmic source,
so a narrowly scoped GNIP-002 Collatz compatibility refactor is justified in
principle.  It remains unimplemented here: existing Collatz definitions and
public theorem names were left unchanged.

## 11. GNIP-003 status

The exact unit-shell identity and coordinate orientation justify a future
GNIP-003 open-gnomon restatement in principle.  That bridge remains
unimplemented, and this checkpoint makes no Legendre existence, prime
provider, or cover claim.

GNIP-004 inversion/projection preservation analysis is also outside this
checkpoint.
