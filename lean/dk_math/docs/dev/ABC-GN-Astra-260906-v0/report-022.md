# LUNA-022 — ABC–GN cubic research-frontier capstone

## Files changed

- `DkMath/ABC/GNExcessCubicResearchFrontier.lean`
- `DkMath/ABC.lean` (public import after the LUNA-021 incidence module)
- `README.md`, `ROADMAP.md`, `validation-022.txt`, and this report.

The new production module is a composition checkpoint.  It contains no new
substantial arithmetic proof and introduces no provider or research axiom.

## Capstone composition theorem

The principal theorem is
`exp_GNExcessMassAt_sum_cubic_three_eighths_le_of_dyadicShellCardBounds`.
For an explicit function `B : ℕ → ℝ`, it assumes only

```text
∀ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
  (GNExcessCubicRealizedLargeModulusShellCount X (2^k) : ℝ) ≤ B k
```

and concludes the existing cubic finite-Euler excess-sum bound with the
explicit shell-card contribution

```text
∑ k ∈ GNExcessCubicRealizedLargeDyadicIndexSpace X,
  B k * (2^(k+1))^(3/8).
```

The proof is the direct transitive composition of
`exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment`
and
`GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds`.

## Exact research object and dyadic support

The only remaining input quantity is exactly

```text
GNExcessCubicRealizedLargeModulusShellCount X D.
```

No new conjecture object, provider class, or global assumption is defined.
For every represented dyadic index `k`, the existing endpoint theorem gives

```text
X + 1 < 2^(k+1)
2^k ≤ 3*(X+1)^2.
```

No logarithmic asymptotic is inferred.

## Positive production ledger

The verified deterministic chain is:

1. realized large-profile/fiber boundary transfer;
2. exact cubic `3/8` realized-modulus moment;
3. exact distinct realized modulus space;
4. exact dyadic shell partition;
5. shell moment bounded by shell count times shell upper weight;
6. generic explicit `B(k)` shell-card consumer;
7. witness/fiber incidence coordinates;
8. complement and incidence-pair coordinates;
9. squareful/Pell coordinates;
10. exceptional-prime-3 normalization;
11. finite three-sector incidence;
12. paired orientation factorization;
13. paired square-cube coordinates;
14. unique ordinary overlap prime `7`;
15. exact mod-49 three-state normalization;
16. finite seven-state incidence;
17. this end-to-end capstone composition.

The finite incidence ledger already contains shell-count domination by witness
cards, exact modulus-fiber, complement-fiber, incidence-pair, and Pell-
parameter-fiber identities.  The sector refinements include the fixed-`T`
split, normalized `T3` fibers, the seven-sector forward-deep/swap-deep/
shallow partition, and the repeated-product-seven deep union.

## Sector status

The finite three-sector production ledger is complete.  LUNA-021 supplies the
exact seven-sector identity

```text
SevenSector = ForwardDeep ⊔ SwapDeep ⊔ ShallowSeven
```

and

```text
RepeatedProductSeven = ForwardDeep ⊔ SwapDeep.
```

These are finite identities only; no state cardinality comparison is made.

## Negative regression ledger

The production and research records already rule out the following shortcuts:

- raw profile space contains impossible compound profiles, so the route uses
  realized profiles, realized moduli, and exact realized shells;
- point-to-modulus injectivity fails, with repeated moduli such as `169` and
  `8281` at multiple witnesses;
- small complement does not bound witness multiplicity, as shown by the
  Pell family with complement `3` and arbitrarily large increasing witnesses;
- opposite orientations admit independently deep exact local depths;
- coprime repeated parts do not imply smallness;
- simple-root Hensel lifting is not global rarity;
- the prime-7 mod-49 classification is not a density theorem.

No one of these regressions is reproved or hidden by the capstone theorem.

## RESEARCH TARGET — NOT PROVED

ASTRA-007 identified a sufficient target of rough shape

```text
N_X(D) ≤ C_ε * X^(1+ε) / sqrt(D)
```

through the realized large range, for suitable small `ε`.  This remains a
research target only.  It is not represented as a Lean conjecture, axiom,
provider, or assumption wrapper.

The exact open statement is an ordinary nontrivial upper bound for
`GNExcessCubicRealizedLargeModulusShellCount X D`.  The deterministic Lean
reduction is complete up to this finite arithmetic quantity.  ABC is not
proved.

## Verification and trust boundary

```text
lake build DkMath.ABC.GNExcessCubicResearchFrontier  PASS
lake build DkMath.ABC                               PASS
```

Changed production sources contain no new `sorry`, `admit`, `axiom`,
`abc_main_axiom`, or `native_decide`.  The principal capstone composition
uses only the existing trust boundary: `propext`, `Classical.choice`, and
`Quot.sound` (or a subset).

The recommended next action is to pause and reassess the mathematics.  Do not
continue into a new production layer until a genuinely new theorem bounding
the shell-count research object is available.
