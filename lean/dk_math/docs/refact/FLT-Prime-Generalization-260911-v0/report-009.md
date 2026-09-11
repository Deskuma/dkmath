# FLT prime-generalization Phase 9 — cyclotomic automorphism realization and full invariance

## Scope and outcome

This report records the bounded implementation requested by
`instruction-009.md`. The Phase-8 abstract QR/QNR action is now connected to
actual algebra automorphisms of a cyclotomic extension. Every nonzero
`t : ZMod p` is realized by an automorphism with the prescribed action on a
primitive `p`-th root, and `Rpoly` and `Dpoly ^ 2` are invariant under every
cyclotomic algebra automorphism.

The resulting classification is:

```text
PGEN-GAUSS-GALOIS-GREEN
```

The implementation stops before coefficient descent, integrality, Gaussian
period coordinates, arbitrary-prime `TraceOneInt` bridges, or any FLT
contradiction.

## A. Pinned Mathlib API audit and selected route

The audit module is:

```text
DkMathTest/FLT/Prime/CyclotomicQRGaloisRealizationAxiomAudit.lean
```

The pinned declarations `IsPrimitiveRoot.autToPow` and
`IsPrimitiveRoot.autToPow_spec` provide the exponent of an existing algebra
automorphism and its action on a primitive root. The audit also confirms the
injectivity and modular-character declarations, the group equivalence
`IsCyclotomicExtension.autEquivPow`, the top-level equivalences
`galCyclotomicEquivUnitsZMod` and `galXPowEquivUnitsZMod`, and
`IsCyclotomicExtension.isGalois`.

For realization, the production proof uses the explicit inverse-side API
`IsCyclotomicExtension.fromZetaAut` together with
`IsCyclotomicExtension.fromZetaAut_spec`. This directly constructs an
`L ≃ₐ[K] L` from a primitive root `ω ^ t.val` and the explicit irreducibility
proof required by the pinned signature. The full equivalence APIs remain
audited rather than being reimplemented manually.

## B. Minimal production ambient

The production module is:

```text
DkMath/NumberTheory/CyclotomicQRGaloisRealization.lean
```

Its realization theorem uses the generic ambient

```lean
[Field K] [Field L] [Algebra K L]
[Fact p.Prime]
[IsCyclotomicExtension {p} K L]
```

with an explicit argument

```lean
hirr : Irreducible (Polynomial.cyclotomic p K)
```

No algebraic closure or stronger global field assumption is introduced. The
primitive-root hypothesis is supplied for the selected `ζ`; the canonical
`IsCyclotomicExtension.zeta` is used internally to construct the desired
automorphism. Irreducibility is intentionally explicit because it is not
silently inferred from the generic extension instance at the pinned API
boundary.

## C. Nonzero residue-to-unit bridge

The reusable definitions and lemmas are:

```text
nonzeroExponentUnit
coe_nonzeroExponentUnit
nonzeroExponentUnit_ne_zero
```

For `t ≠ 0`, primality gives `Nat.Coprime t.val p`, so
`ZMod.unitOfCoprime t.val ...` is a unit whose `ZMod p` coercion is exactly
`t`. The unit is therefore nonzero and can be used with the cyclotomic
automorphism API without confusing a residue with an arbitrary natural
representative.

## D. Realization of every nonzero exponent

The central theorem is:

```lean
theorem exists_cyclotomicAut_pow
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (hirr : Irreducible (Polynomial.cyclotomic p K))
    (t : ZMod p) (ht : t ≠ 0) :
    ∃ σ : L ≃ₐ[K] L, σ ζ = ζ ^ t.val
```

The proof takes the canonical primitive root `ω`, writes the supplied
primitive root as `ζ = ω ^ i`, proves that `ω ^ t.val` is primitive using the
unit/coprimality bridge, and applies `fromZetaAut`. The resulting action on
`ζ` is normalized by `pow_mul` and commutativity of natural multiplication.

## E. Adapter to the Phase-8 action API

No Phase-8 action proof is duplicated. The new theorems pass

```lean
σ.toRingEquiv.toRingHom
```

directly to the existing `MvPolynomial.map` API. The Phase-8 square and
nonsquare branches are reused for `Rpoly`, `Dpoly`, and `Dpoly ^ 2`.

## F. Full Galois invariance

The converse direction for an arbitrary algebra automorphism is packaged as:

```text
cyclotomicAut_power_spec
```

It extracts a unit exponent with `autToPow`, proves its `ZMod p` coercion is
nonzero, and supplies the exact primitive-root action needed by Phase 8.
The full results are:

```text
map_Rpoly_of_cyclotomicAut
map_Dpoly_of_cyclotomicAut
map_Dpoly_sq_of_cyclotomicAut
```

`Rpoly` is fixed for every algebra automorphism. `Dpoly` is fixed or negated
according to the square/nonsquare branch, and `Dpoly ^ 2` is fixed in both
branches.

## G. Converse coverage

The two directions required by the checkpoint are both present:

1. `exists_cyclotomicAut_pow` realizes every nonzero exponent `t` under the
   explicit irreducibility hypothesis.
2. `cyclotomicAut_power_spec` assigns a nonzero unit exponent to every
   algebra automorphism through `autToPow`.

Thus the result closes the gap between a supplied abstract exponent action and
the full cyclotomic automorphism action. The implementation uses the pinned
equivalence/inverse infrastructure rather than claiming a stronger new
equivalence theorem.

## H. Focused compatibility checks

The regression module is:

```text
DkMathTest/FLT/Prime/CyclotomicQRGaloisRealizationProbe.lean
```

It uses `CyclotomicField p ℚ` with explicit local `NeZero` instances and
checks both realization and full invariance for `p = 3, 5, 7, 11, 13`.
The production theorem remains arbitrary-prime; the five values are only
finite regressions and do not prove the general result by enumeration.

## I. Boundaries preserved

The following remain intentionally open:

```text
coefficient descent to base field   [NEXT]
integrality / ring-of-integers      [OPEN]
integral Gaussian coordinates       [OPEN]
TraceOne arbitrary-prime bridge     [OPEN]
FLT descent / contradiction         [OPEN]
```

In particular, invariance of a polynomial under the cyclotomic automorphism
group is not reported as coefficient descent or integrality.

## J. Verification and axiom audit

The focused production, regression, compatibility, and FLT7 targets were
built successfully:

```text
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMath.NumberTheory.CyclotomicQRGaloisAction
lake build DkMath.NumberTheory.CyclotomicQRGaloisRealization
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisRealizationProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisRealizationAxiomAudit
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility
lake build DkMath.FLT.Seven
```

The public Phase-9 declarations have focused `#print axioms` coverage. The
reported dependencies are only Lean kernel support (`propext`,
`Classical.choice`, and `Quot.sound`); no `sorryAx` is present. The new
production and test sources contain no `sorry` and no explicit `axiom`.

`git diff --check` and the final warning/source scans are part of the closeout
validation.
