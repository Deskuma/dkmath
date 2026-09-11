# FLT prime-generalization Phase 9 — cyclotomic automorphism realization and full invariance

## Goal

Close the next exact boundary from `report-008.md`.

Phase 8 proved the QR/QNR action for an explicitly supplied automorphism

```lean
σ : K ≃+* K
t : ZMod p
hσζ : σ ζ = ζ ^ t.val
```

but did **not** prove that every nonzero `t` is realized by an automorphism of a chosen cyclotomic extension.

This phase must construct that realization in a genuine cyclotomic/Galois ambient setting and then upgrade the existing action theorems to full Galois invariance of `Rpoly` and `Dpoly ^ 2`.

Do **not** attempt coefficient descent to `ℚ`, coefficient integrality, Gaussian-period integer coordinates, or any FLT contradiction in this phase.

## Scope boundary

Target classification on success:

```text
PGEN-GAUSS-GALOIS-GREEN
```

Keep these later boundaries open:

```text
coefficient descent to base field   [NEXT]
integrality / ring-of-integers      [OPEN]
integral Gaussian coordinates       [OPEN]
TraceOne arbitrary-prime bridge     [OPEN]
FLT descent / contradiction         [OPEN]
```

## Part A — audit pinned Mathlib realization APIs

Audit the exact signatures and assumptions of the declarations already identified in `report-008.md`:

```text
IsPrimitiveRoot.autToPow
IsPrimitiveRoot.autToPow_spec
IsPrimitiveRoot.autToPow_injective
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
IsCyclotomicExtension.autEquivPow
galCyclotomicEquivUnitsZMod
galXPowEquivUnitsZMod
IsCyclotomicExtension.isGalois
```

Also inspect any nearby declarations that give surjectivity or explicit inverse construction from `(ZMod p)ˣ` to the Galois group.

Prefer an existing equivalence such as

```text
Aut(cyclotomic extension / base) ≃ (ZMod p)ˣ
```

if the pinned API exposes it cleanly.

Do not reprove Galois theory manually if a pinned equivalence already provides the realization.

Record the exact chosen route in `report-009.md`.

## Part B — choose the minimal cyclotomic ambient

Use the weakest ambient assumptions under which the pinned API supplies all automorphisms.

Preferred shape, subject to the actual pinned signatures:

```lean
K : Type*
L : Type*
[Field K] [Field L]
[Algebra K L]
p : ℕ
[Fact p.Prime]
ζ : L
hζ : IsPrimitiveRoot ζ p
hcyclo : IsCyclotomicExtension {p} K L
```

or the canonical cyclotomic number field type if that is significantly cleaner in the pinned Mathlib.

Do not introduce algebraic closure or stronger hypotheses unless required by the actual API.

State clearly whether irreducibility / primitive-root generation / characteristic assumptions are automatic or explicit.

## Part C — nonzero residue to unit

For

```lean
t : ZMod p
ht : t ≠ 0
```

construct the corresponding unit

```lean
ut : (ZMod p)ˣ
```

with coercion equal to `t`.

Prove the exact bridge needed to compare

```lean
ζ ^ (ut : ZMod p).val
```

with

```lean
ζ ^ t.val.
```

Keep this as a small reusable theorem if useful.

## Part D — automorphism realization

Construct an algebra automorphism

```lean
σt : L ≃ₐ[K] L
```

for every nonzero `t : ZMod p` such that

```lean
σt ζ = ζ ^ t.val.
```

Suggested theorem shape:

```lean
theorem exists_cyclotomicAut_pow
    (t : ZMod p) (ht : t ≠ 0) :
    ∃ σ : L ≃ₐ[K] L, σ ζ = ζ ^ t.val := by
  ...
```

If the pinned equivalence gives a canonical automorphism, also define a noncomputable constructor only if it materially simplifies downstream use:

```lean
noncomputable def cyclotomicAutOfNonzero ... : L ≃ₐ[K] L := ...
```

Avoid `Classical.choice` if the equivalence provides an explicit inverse; if choice is used, record it in the axiom audit.

## Part E — bridge AlgEquiv to the Phase-8 RingEquiv action API

Phase 8 currently uses a supplied

```lean
σ : L ≃+* L
```

while the cyclotomic realization will likely produce

```lean
σ : L ≃ₐ[K] L.
```

Add the thinnest possible adapter theorem or coercion path. Do not duplicate the Phase-8 action proofs.

The goal is to reuse directly:

```text
map_qrFactorPoly_of_square
map_qnrFactorPoly_of_square
map_qrFactorPoly_to_qnr_of_nonsquare
map_qnrFactorPoly_to_qr_of_nonsquare
map_Rpoly_of_square
map_Rpoly_of_nonsquare
map_Dpoly_of_square
map_Dpoly_of_nonsquare
map_Dpoly_sq_of_square
map_Dpoly_sq_of_nonsquare
```

## Part F — full Galois invariance

For every algebra automorphism

```lean
σ : L ≃ₐ[K] L
```

use `autToPow` (or the pinned equivalent) to extract its exponent `t` and prove `t ≠ 0` / unit status.

Then split on whether `t` is square or nonsquare and prove:

```lean
theorem map_Rpoly_of_cyclotomicAut
    (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Rpoly ζ) = Rpoly ζ := by
  ...
```

and

```lean
theorem map_Dpoly_sq_of_cyclotomicAut
    (σ : L ≃ₐ[K] L) :
    MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly ζ ^ 2) = Dpoly ζ ^ 2 := by
  ...
```

Exact map syntax should follow the pinned API and existing Phase-8 implementation.

If useful, also prove the stronger character-valued statement for `Dpoly`:

```text
σ(Dpoly) = ± Dpoly
```

but do not let that block the mandatory invariance theorem for the square.

## Part G — converse coverage audit

It is not enough to prove existence of some automorphisms.

Verify explicitly that:

1. every nonzero `t : ZMod p` is realized by a cyclotomic automorphism; and
2. every cyclotomic automorphism has a corresponding nonzero power exponent.

Report whether these are supplied by a genuine equivalence or by separate injective/surjective theorems.

This closes the logical gap between:

```text
abstract action for a supplied exponent
```

and

```text
full Galois invariance.
```

## Part H — focused compatibility checks

Add a test module, suggested path:

```text
DkMathTest/FLT/Prime/CyclotomicQRGaloisRealizationProbe.lean
```

Check the realization and full invariance at least for:

```text
p = 3, 5, 7, 11, 13
```

Use the cleanest concrete cyclotomic extension available in the pinned library. These are regressions only; the production theorem must remain arbitrary-prime.

Do not enumerate automorphisms to prove the general theorem.

## Part I — compatibility with Phase 7/8 and FLT7

Build at least:

```text
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMath.NumberTheory.CyclotomicQRGaloisAction
lake build <new production realization module>
lake build <new probe>
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility
lake build DkMath.FLT.Seven
```

Do not modify FLT3/FLT5/FLT7 theorem statements or endpoints.

## Part J — axiom audit

Add focused `#print axioms` coverage for:

```text
exists_cyclotomicAut_pow
full Rpoly invariance theorem
full Dpoly^2 invariance theorem
```

plus any public canonical constructor.

Requirements:

- no `sorryAx`;
- no new `sorry`;
- no explicit `axiom`;
- `git diff --check` green.

Record whether `Classical.choice` appears and whether it originates only from existing finite/Galois infrastructure.

## Part K — report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-009.md
```

Classify the outcome precisely:

```text
PGEN-GAUSS-GALOIS-GREEN
```

only if all nonzero exponent classes are realized and the full invariance theorems compile.

Otherwise stop at the strongest honest boundary, for example:

```text
PGEN-GAUSS-GALOIS-INJECTIVE
PGEN-GAUSS-GALOIS-REALIZATION-MISSING
PGEN-GAUSS-GALOIS-ASSUMPTION-HEAVY
```

The report must explicitly separate:

```text
1. abstract action                     [Phase 8 GREEN]
2. existence/coverage of automorphisms [this phase]
3. full invariance                     [this phase target]
4. fixed-field coefficient descent     [future]
5. integral coefficient descent        [future]
6. Gaussian integer coordinates        [future]
7. FLT contradiction                   [future]
```

## Success criterion

The phase succeeds only when Lean proves that the Phase-8 invariants are fixed by **every** automorphism in the selected cyclotomic Galois group, not merely by an externally supplied automorphism satisfying a power equation.
