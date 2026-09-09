# LUNA-002 — shell-fiber uniqueness production freeze

This checkpoint implements only the deterministic theorem approved by
`instruction-002.md`. The analytic estimates and external results in
`report-001.md` remain research material and are not imported into Lean.

## 1. Files changed

Added [GNExcessCubicShellFiberUniqueness.lean](../../../DkMath/ABC/GNExcessCubicShellFiberUniqueness.lean)
and imported it from `DkMath/ABC.lean` immediately after
`GNExcessCubicPrimitivePell`. Added the focused build and axiom output
artifacts [lean-002-output.txt](lean-002-output.txt),
[build-002-abc-output.txt](build-002-abc-output.txt), and this report.

The new module imports only `DkMath.ABC.GNExcessCubicPrimitivePell`. It
contains no asymptotic estimate, external theorem, Mordell counting result,
Eisenstein factorization existence claim, provider, or ABC axiom.

## 2. Conic cross identity

`conic_cross_identity` proves, over `ℤ`,

```text
y₁² + 3 = 4*T*d₁²,  y₂² + 3 = 4*T*d₂²
  → (y₂*d₁)² + 3*d₁² = (y₁*d₂)² + 3*d₂².
```

The proof multiplies the two equations by the opposite denominator square and
uses `nlinarith`. It contains no quadratic-field construction.

## 3. Conic lower bound

`conic_y_lower` proves `2*d ≤ y` from `2 ≤ T`, `0 ≤ y`, `0 < d`, and the
conic equation. The proof first obtains `1 ≤ d²`, then compares `2*d²` with
`T*d²` and closes the result by integer arithmetic.

## 4. Denominator separation

`conic_no_close_denominators` is the accepted determinant argument. With
`0 < d₁ < d₂`, set `A=y₂d₁` and `B=y₁d₂`. The cross identity gives

```text
A² - B² = 3*(d₂²-d₁²).
```

The lower bound gives `B ≥ 2*d₁*d₂`. Since the left factor ordering gives
`A ≥ B+1`, integrality yields `A²-B² ≥ 2B+1`. If `d₂² < 2*d₁²`, these
inequalities contradict one another. The theorem concludes
`2*d₁² ≤ d₂²`.

This is a purely integer proof. No ideal, unit, class-group, or analytic
argument entered the production module.

## 5. Production `T ≥ 2` wrapper

`cubic_parameter_ge_two` specializes the production numerator
`y=2*a+3`. The case `T=0` is impossible by the equation. The case `T=1`
would imply `a²+3a+3=d²`, contradicting the existing production theorem
`cubicQuadratic_ne_square`. No nonsquare lemma was reproved.

## 6. Abstract shell uniqueness

`conic_shell_unique` consumes the denominator separation theorem. For
`D ≤ r*dᵢ² < 2D`, two ordered denominators would satisfy both

```text
2*d₁² ≤ d₂²
and
r*d₂² < 2D ≤ 2*r*d₁²,
```

which is impossible. Trichotomy handles `d₁<d₂`, equality, and `d₂<d₁`.
After equal denominators, the two nonnegative conic numerators are equal by
integer arithmetic. The theorem assumes exactly the requested natural-number
conditions; it does not add squarefreeness, coprimality, `r ∣ d`, or a height
condition.

## 7. Refined production `(T,r)` fiber

The new finite set is

```lean
GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber X D T r
```

It filters the existing
`GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T` by

```lean
oddPart (GNExcessCubicFullRepeatedModulus a) = r.
```

This is the requested production name and keeps the existing Pell-parameter
fiber as the owner of witness, shell, and conic data.

## 8. Exact membership theorem

`mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff` states the
filter definition exactly:

```text
a ∈ refinedFiber X D T r
↔ a ∈ existingPellFiber X D T ∧ oddPart(M(a)) = r.
```

The proof is the finite-filter simplification only; no arithmetic packet is
duplicated.

## 9. Subsingleton theorem

`GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_subsingleton` obtains
the existing production witness packets, builds the incidence pair
`(M(a),S(a))`, and consumes:

1. the squareful packet `M = oddPart(M) * evenPart(M)²`;
2. the primitive Pell packet
   `(2a+3)²+3 = 4*T*evenPart(M)²`;
3. the shell inequalities;
4. `conic_shell_unique`.

The final equality `a=b` is closed from equality of the positive Pell
coordinates by `omega`. The implementation does not restate production
factorization or coprimality facts.

## 10. Card ≤ 1

`GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one` is the
canonical finite result:

```lean
(refinedFiber X D T r).card ≤ 1
```

It is exactly `Finset.card_le_one.mpr` applied to the subsingleton theorem.
The older research-only card-≤2 wrapper was intentionally not added to
production because no consumer needs the weaker constant.

## 11. Shell `(r,S)` injectivity

`GNExcessCubicRealizedLargeModulusShellWitness_pair_injective` proves

```lean
Set.InjOn
  (fun a => (oddPart (GNExcessCubicFullRepeatedModulus a),
    GNExcessCubicComplement a))
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D : Set ℕ)
```

For equal pairs, it reconstructs `T=r*S`, puts both witnesses into the same
refined fiber, and invokes the subsingleton result.

The result is local to one shell. It does not assert injectivity of `a ↦ M`,
injectivity of `a ↦ S`, or global injectivity of `(r,S)` across shells.

## 12. Optional pair-card result

Skipped. The required injectivity is already available and the instruction
made an image/card equality optional. No new incidence hierarchy was added.

## 13. Optional height inequality status

Skipped. The inequality `D²*T³ < 54*(X+1)⁶` remains independently checked in
`scratch-000.lean` and documented in `report-001.md`. Porting it here would
add no deterministic fiber consumer and was outside this freeze's priority.

## 14. Compatibility with known modulus collisions

The theorem is compatible with all known collisions because it fixes both
the Pell parameter and the cube-core and also fixes one dyadic shell.

`M=169` has witnesses `21` and `145` with different complements, so they are
not forced into the same `(T,r)` refined fiber. `M=8281` has four witnesses
with distinct complements and hence distinct `T` when `r=1`. The complement-3
Pell family keeps `T=3,r=1` but its denominators grow through different
dyadic shells. The theorem therefore removes no valid regression example.

The theorem also says nothing about opposite-orientation depth pairs,
arbitrary finite Hensel lifting, or coprime repeated parts in different
shells. Those remain the boundaries recorded in the previous research report.

## 15. Focused build

The required command passed:

```text
lake build DkMath.ABC.GNExcessCubicShellFiberUniqueness
```

The output is retained in [lean-002-output.txt](lean-002-output.txt).
The module was rebuilt after correcting one temporary elaboration attempt
that used an over-aggressive `simp`; the final source uses the direct
inequality transport from the accepted scratch proof.

## 16. ABC aggregator build

The required command passed:

```text
lake build DkMath.ABC
```

The complete output is retained in
[build-002-abc-output.txt](build-002-abc-output.txt). The only tracked source
change outside the new module is the requested import line in `DkMath/ABC.lean`.

## 17. Forbidden construct scan

The new production module was scanned for:

```text
sorry, admit, axiom, abc_main_axiom, native_decide, unsafe
```

No occurrences were found. The module contains no research analytics, no
external theorem statement, and no conjecture object.

The aggregator necessarily replays pre-existing repository declarations, some
of which have their own historical warnings. This checkpoint adds none.

## 18. Axiom audit

The principal declarations print the expected trust boundary:

```text
conic_no_close_denominators:
  [propext, Classical.choice, Quot.sound]
conic_shell_unique:
  [propext, Classical.choice, Quot.sound]
GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one:
  [propext, Classical.choice, Quot.sound]
GNExcessCubicRealizedLargeModulusShellWitness_pair_injective:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs in the final declarations, and no external theorem enters
the Lean dependency graph.

## 19. Exact remaining research frontier

PROVED in production:

- fixed `(T,r)` plus one dyadic shell gives at most one realized witness;
- inside one shell, `a ↦ (r,S)` is injective;
- the exact refined finite-set membership characterization;
- the existing production conic and squareful packets remain the only data
  source for the new proof.

NOT PROVED in production:

- `a ↦ M(a)` injective;
- bounded global multiplicity for fixed `S`;
- bounded global multiplicity for fixed `T`;
- a near-linear bound for `N_X(D)`;
- a balanced-box power saving;
- the Helfgott–Venkatesh specialization in Lean;
- any asymptotic shell moment estimate;
- ABC.

This closes LUNA-002 at its requested boundary. No LUNA-003 instruction is
opened automatically.
