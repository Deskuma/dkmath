# DRC-002 — GN product-degree generic lift

## Outcome A

A production product-degree composition theorem is kernel-checked for every
`CommSemiring`, with no positive-gap, nonzero-gap, cancellation, domain,
characteristic-zero, or nontriviality hypothesis on the coefficient semiring.
It includes `x = 0` and arbitrary natural degrees, including zero. This is a
repository generalization; no mathematical novelty claim is made.

## Audit and existing infrastructure

- Branch: `research/DkMath-ResearchConnections-261003-v0`.
- Initial HEAD: `fb2f625622c60b13aea5eb002a5f0b7a66e90dd0`; initial worktree clean.
- Lean `v4.34.1`; pinned Mathlib checkout
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Existing `DkMath.NumberTheory.GN_mul_degree` in
  `DkMath/NumberTheory/GNDegreeFactorization.lean` is the Nat theorem with
  hypothesis `0 < x`.
- Canonical `DkMath.CosmicFormula.GN` in `CosmicFormula/Defs.lean` is an
  abbreviation for the existing `GTail d 1 x u`; the legacy
  `DkMath.CosmicFormulaBinom.GN` abbreviates that same kernel.
- The lower Lib module already supplies the generic binomial tail identity
  `DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap`.
- Searches of DkMath production declarations and pinned Mathlib geometric-sum
  and product-length/power identities found no directly applicable generic GN
  composition endpoint. Mathlib supplies the polynomial semiring and evaluation
  APIs used below; no parallel GN definition is introduced.

## Added production endpoints

File: `DkMath/Lib/Cosmic/GNProductDegree.lean`.

```lean
DkMath.CosmicFormula.map_GN
DkMath.CosmicFormula.GN_mul_degree
```

The main theorem's literal lower-Lib statement is:

```lean
theorem GN_mul_degree {R : Type*} [CommSemiring R]
    (a b : ℕ) (x u : R) :
    GTail (a * b) 1 x u =
      GTail a 1 x u * GTail b 1 (x * GTail a 1 x u) (u ^ a)
```

Because both existing GN names are definitionally `GTail _ 1`, this is exactly

```text
GN (a*b) x u = GN a x u * GN b (x * GN a x u) (u^a).
```

The theorem uses the weakest coefficient class currently supported by the GN
definition itself: `CommSemiring`. The literal tail statement keeps the module
in the lower Lib layer without importing the heavier `CosmicFormula/Defs.lean`
facade. `map_GN` states that a semiring homomorphism preserves this same `r = 1`
tail and proves it directly from the defining finite sum.

`DkMath/Lib.lean` imports the new module.

## Proof actually used

The private polynomial certificate works in `MvPolynomial (Fin 2) ℕ`, with
`x = X 0` and `u = X 1`. Apply the existing cosmic identity at degrees `a`, `b`,
and `a*b`, then use `pow_mul` and associativity to obtain

```text
x * GN (a*b) x u + u^(a*b)
  = x * (GN a x u * GN b (x * GN a x u) (u^a)) + u^(a*b).
```

Addition and multiplication cancellation are valid in this universal polynomial
semiring. `add_right_cancel` removes the common gap power;
`mul_left_cancel₀ (MvPolynomial.X_ne_zero ...)` removes the formal indeterminate.
This establishes the polynomial identity before any target values are supplied.

The public proof applies `MvPolynomial.eval₂Hom (Nat.castRingHom R)` with
`X 0 ↦ x` and `X 1 ↦ u`. `map_GN`, `map_mul`, and `map_pow` transport the
certificate into arbitrary `R`. Cancellation is confined to the formal
polynomial certificate, not assumed of the evaluated gap or target semiring.
Thus evaluation at zero or at a zero divisor is valid. The proof does not use
finite enumeration of degrees or values.

## Existing Nat theorem compatibility

The existing `DkMath.NumberTheory.GN_mul_degree` retains its name, implicit
parameters, positive-gap argument named `hx`, and result type. Its proof is now
the direct specialization:

```lean
exact DkMath.CosmicFormula.GN_mul_degree a b x u
```

The obsolete positivity argument remains for source compatibility. Its unused
variable linter is disabled locally for this one declaration. Downstream prime
degree statements and their existing regression anchors compile unchanged.

## Regressions and axiom audit

Files:

- `DkMathTest/Lib/Cosmic/GNProductDegreeCalibration.lean`
- `DkMathTest/Lib/Cosmic/GNProductDegreeAxiomAudit.lean`

The calibration file verifies the canonical GN statement over arbitrary
`CommSemiring`, arbitrary-degree zero-gap specialization, the numerical zero-gap
value `GN 6 0 2 = 192` over Nat, both zero-degree boundaries, and compatibility
with the old Nat endpoint. A `ZMod 4` example verifies that the nonzero gap `2`
is a zero divisor (`2 * 2 = 0`) and nevertheless satisfies the composition
identity; `GN 6 2 1 = 0` there. Numerical `decide` is used only for these fixed
regression computations, not for the general identity.

`#print axioms` for `map_GN`, the generic `GN_mul_degree`, and the existing Nat
`GN_mul_degree` reports the same dependency list:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or project-added axioms occur in these endpoints.

## Validation

Commands ran from `lean/dk_math`:

| Command | Result |
| --- | --- |
| `lake env lean DkMath/Lib/Cosmic/GNProductDegree.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/Lib/Cosmic/GNProductDegreeCalibration.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/Lib/Cosmic/GNProductDegreeAxiomAudit.lean` | Pass, exit 0 |
| Combined build of `DkMath.Lib`, `DkMath.NumberTheory.GNDegreeFactorization`, and both new test modules | Pass, 8957 jobs, exit 0 |
| `lake build` | Pass, 10336 jobs, exit 0 |

The local `DkMath.Lib` import closure contains 24 source files. A recursive
source scan found no `sorry`, `admit`, or axiom declaration candidates.
`git diff --check` and checks of every new file with
`git diff --no-index --check /dev/null <file>` produced no whitespace diagnostics.
Build logs are `/tmp/drc-002-focused.log` and `/tmp/drc-002-full-build.log`.

No Mathlib API obstruction remains. During implementation, a vector-notation
import dependency was avoided by using an explicit variable-evaluation function;
the unused compatibility argument is handled locally. The final implementation
uses existing GTail and Mathlib polynomial APIs throughout.
