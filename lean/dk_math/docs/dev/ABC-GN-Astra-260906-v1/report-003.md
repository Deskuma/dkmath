# LUNA-003 — Pell-parameter height production freeze

This checkpoint productionizes the deterministic range inequality from the
validated scratch theorem. It also freezes the exact shell image of canonical
`(r,S)` pairs and its card identity. No asymptotic estimate or external
analytic theorem is introduced.

## 1. Files changed

Added [GNExcessCubicShellParameterBounds.lean](../../../DkMath/ABC/GNExcessCubicShellParameterBounds.lean)
and imported it from `DkMath/ABC.lean` immediately after
`GNExcessCubicShellFiberUniqueness`. Added the focused and aggregator build
logs, [lean-003-output.txt](lean-003-output.txt),
[build-003-abc-output.txt](build-003-abc-output.txt), and this report plus
[validation-003.txt](validation-003.txt).

The new module imports only the LUNA-002 shell-fiber module. It is a
deterministic range ledger and contains no counting theorem, external
literature statement, Mordell estimate, Eisenstein factorization existence,
provider, or ABC axiom.

## 2. Abstract height lemma

`pellParameter_height_cube_aux` ports the checked scratch theorem. From

```text
0 < D
D*S ≤ 3*(X+1)^2
r^3 < 2*D
T = r*S
```

it proves

```text
D^2*T^3 < 54*(X+1)^6.
```

The proof forms `D*T ≤ r*(3*(X+1)^2)`, cubes that inequality, uses the strict
bound on `r^3`, and cancels the positive factor `D`. The constant `54` is
unchanged. No attempt is made to replace it by the sharper research-only
constant discussed in `report-001.md`.

## 3. `D*S` wrapper status

`GNExcessCubicRealizedLargeModulusShellIncidencePair_DS_le` is proved for
every represented shell incidence pair. It consumes the existing packet

```text
D ≤ M
M*S = a^2+3a+3
a ≤ X
```

and the elementary inequality
`a²+3a+3 ≤ 3*(X+1)²`. Thus it concludes
`D*S ≤ 3*(X+1)²` without restating the product or shell definitions.

## 4. Realized Pell-parameter height theorem

`GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube` consumes
`GNExcessCubicRealizedLargeModulusShellPellParameter_packet`, obtaining
`T=r*S` and `r³<2D`, then applies the abstract lemma and the `D*S` wrapper.
Its exact production statement is:

```lean
T ∈ GNExcessCubicRealizedLargeModulusShellPellParameterSpace X D
  → D^2*T^3 < 54*(X+1)^6
```

This is a range constraint only. It is not a bound on the number of
represented parameters.

## 5. Witness wrapper

`GNExcessCubicRealizedLargeModulusShellWitness_pellParameter_height_cube`
sets

```text
T = oddPart (GNExcessCubicFullRepeatedModulus a)
      * GNExcessCubicComplement a
```

and constructs its membership in the existing Pell-parameter space directly
from the witness image. The result is the requested witness-level inequality
with the same constant `54`.

## 6. Represented `(r,S)` image status

The recommended finite image is now defined as

```lean
GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace X D
```

It is the image of the shell witness space under

```text
a ↦ (oddPart (GNExcessCubicFullRepeatedModulus a),
     GNExcessCubicComplement a).
```

This is an exact finite object and does not assert sparsity.

## 7. Image membership theorem

`mem_GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_iff`
proves exactly:

```text
(r,S) is in the image
↔ ∃ a in the shell witness space,
     oddPart(M(a)) = r ∧ Complement(a) = S.
```

The proof is the standard finite-image membership simplification.

## 8. Pair-space cardinal identity

`GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_card` proves

```text
CubeCoreComplementSpace.card = ShellWitnessSpace.card.
```

It applies `Finset.card_image_of_injOn` to the production theorem
`GNExcessCubicRealizedLargeModulusShellWitness_pair_injective` from LUNA-002.
This is an exact identity, not a cardinal upper bound and not a sparsity
estimate.

## 9. Optional packet

Skipped. The instruction marks the represented-pair packet as optional. The
existing production packets already expose the needed `r³<2D`, squarefree,
coprimality, and `D*S` facts at their owning incidence/Pell layers. Adding a
second composite packet here would duplicate destructuring without advancing
the requested height theorem.

## 10. Explicit no-sparsity boundary

PROVED:

- represented Pell parameter `T` satisfies
  `D²*T³ < 54*(X+1)⁶`;
- every shell witness satisfies the corresponding canonical witness-level
  inequality;
- shell witnesses and represented canonical `(r,S)` pairs have the same
  finite cardinality.

NOT PROVED:

- represented `(r,S)` pairs are sparse;
- `N_X(D) ≪ X^(2/3)`;
- `N_X(D) ≪_ε X^(2+ε)D^(-4/5)`;
- the `17/12` or `31/24` moment bounds in Lean;
- any balanced-box power saving;
- ABC.

The height inequality is a range restriction and must not be read as a
counting theorem.

## 11. Focused build

The required command passed:

```text
lake build DkMath.ABC.GNExcessCubicShellParameterBounds
```

The output is retained in [lean-003-output.txt](lean-003-output.txt). The
principal declarations were rebuilt with no errors.

## 12. ABC aggregator build

The required command passed:

```text
lake build DkMath.ABC
```

The complete output is retained in
[build-003-abc-output.txt](build-003-abc-output.txt). The import was placed
immediately after `GNExcessCubicShellFiberUniqueness`; unrelated imports were
not reordered.

## 13. Forbidden scan

The new production module was scanned for:

```text
sorry, admit, axiom, abc_main_axiom, native_decide, unsafe
```

No occurrences were found. The new module has no asymptotic shell theorem,
Mordell estimate, Helfgott–Venkatesh statement, average Pell result, or
Eisenstein existence claim.

The aggregator log can replay historical declarations from unrelated files;
those pre-existing declarations are outside this checkpoint's source change.

## 14. Axiom audit

The principal new declarations report the expected kernel trust boundary:

```text
pellParameter_height_cube_aux:
  [propext, Classical.choice, Quot.sound]
GNExcessCubicRealizedLargeModulusShellPellParameter_height_cube:
  [propext, Classical.choice, Quot.sound]
GNExcessCubicRealizedLargeModulusShellCubeCoreComplementSpace_card:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or external theorem occurs in the new module's declarations.

## 15. Remaining research frontier

The production graph now exposes the exact height range for every represented
Pell parameter and the exact shell-level `(r,S)` image/card identity. The
remaining problem is still family-level represented-pair sparsity. Neither
the height range nor the finite image identity supplies a power saving.

This completes LUNA-003 at its requested stop condition. No LUNA-004
instruction is opened automatically, and no balanced-box counting work was
started.
