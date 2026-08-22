# GWSS-003H3 mirror Mellin-matrix / extractor-row transport — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0048-GWSS-003H2-critical-mirror-multiplicity-mass-closure-report.md`

## 0. Mission

GWSS-003H2 closed the finite critical-mirror transport through multiplicity-weighted squared-orbit mass:

```text
centered critical mirror z ↦ -conj z
squared orbit q ↦ conj q
multiplicity preservation
orbit-mass invariance
Fin-index mirror coordinate + equal mass-vector entry
```

with primary classification

```text
MIRROR-ORBIT-MASS-TRANSPORT-CLOSED
```

The next bounded stage is H5 only.

Determine how the **actual general-τ Mellin evaluation matrix** transforms under the conjugate-orbit permutation, and from that determine the exact transport law for the **canonical inverse-matrix extractor row**.

The stage must answer the question that was deliberately left open in GWSS-003H:

```text
What is the extractor row for the mirror target?
```

Do not assume any of the following:

```text
mirror row = original row
mirror row = - original row
mirror row = conj original row
mirror row = a permuted/conjugated row
```

One of these, or a different exact relation, must be derived from the matrix definitions.

Stop after the canonical extractor-row transport is proved or after the first genuine finite API obstruction is identified.

Do not multiply by the target `q.im` in this stage. That coefficient-row sign step is H6, not H5.

Do not proceed to whole-feature transport, shifted-energy oddness, P1/P2, GWSS-004, classical Guinand--Weil, Weil positivity, Li criterion, any infinite-height argument, or RH.

## 1. Required files to inspect first

Read the current branch versions of at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinOffCriticalWitnessAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinArithmeticSpecialization.lean
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaHorizontalPairing.lean
DkMath/Analysis/MellinMultiplicativeApproxIdentity.lean
DkMath/Analysis/MellinCenteredDilation.lean
DkMath/Analysis/MellinCompactSupportHolomorphic.lean
```

Known relevant existing declarations include:

```text
pascalCenteredXiSquaredOrbitRepresentativeFin_sq
pascalCenteredXiSquaredOrbitCoordinate
pascalCenteredXiMellinEvaluationMatrix
exists_pascalCenteredXiSquaredOrbitMirrorIndex_with_mass
pascalCenteredXiMellinSecondDifferenceWeight_even
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
centeredMellinSpectralWeight_centeredMellinBoxApprox_even
centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even
exists_matrix_coordinate_extractor
```

The pinned older Mellin layer already exposes the exact logarithmic representation

```text
centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
  = ((2 * ε)^-1 : ℂ) * ∫ t in (-ε)..ε, exp ((t : ℂ) * z)
```

for `0 < ε`. Use that finite identity if it is the shortest route to conjugation covariance. Do not introduce the previously optional `centeredMellinBoxApprox_mellinCriticalMirror` theorem unless it is actually needed.

## 2. H5-A — conjugation covariance of the actual Mellin weight

First prove the exact spectral-weight conjugation law for the centered box.

Preferred theorem shape:

```lean
theorem centeredMellinSpectralWeight_centeredMellinBoxApprox_conj
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    centeredMellinSpectralWeight (centeredMellinBoxApprox ε) (conj z) =
      conj (centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z) := by
  ...
```

Use the exact log-average and finite interval integral. The integration variable is real, so pointwise

```text
conj (exp (t*z)) = exp (t*conj z).
```

If a pinned `intervalIntegral.integral_conj`/Bochner conjugation theorem is inconvenient, prove only the smallest local integral-conjugation helper needed. Do not use an infinite Mellin continuation argument.

Then prove the all-real-`τ` actual-weight theorem, including the patched `τ = 0` branch:

```lean
theorem pascalCenteredXiMellinSecondDifferenceWeight_conj
    {ε τ : ℝ} (hε : 0 < ε) (z : ℂ) :
    pascalCenteredXiMellinSecondDifferenceWeight ε τ (conj z) =
      conj (pascalCenteredXiMellinSecondDifferenceWeight ε τ z) := by
  ...
```

For `τ ≠ 0`, either use the kernel factorization and `Complex.exp_conj`, or unfold the finite second difference. For `τ = 0`, use the patched quadratic formula and the spectral conjugation theorem.

This theorem is the load-bearing analytic input for H5. If it cannot be proved in the pinned checkout without a materially new library development, stop and classify:

```text
MIRROR-MELLIN-WEIGHT-CONJUGATION-API-GAP
```

Do not bypass it by asserting matrix conjugation directly.

## 3. H5-B — canonical mirror permutation on the `Fin` orbit index

The previous stage provides only an existential mirror index. H5 requires a reusable canonical finite permutation.

Introduce the smallest public injectivity helper needed for the coordinate presentation, preferably in `PascalCenteredXiMellinActualWindowFullRankAudit.lean` if the existing private equivalence is needed internally:

```lean
theorem pascalCenteredXiSquaredOrbitCoordinate_injective (R : ℝ) :
    Function.Injective (pascalCenteredXiSquaredOrbitCoordinate R) := by
  ...
```

Then define a noncomputable mirror-index function from the existing existence theorem:

```lean
noncomputable def pascalCenteredXiSquaredOrbitMirrorIndex
    (R : ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) :=
  Classical.choose (exists_pascalCenteredXiSquaredOrbitMirrorIndex R j)
```

Expose its specification:

```text
coordinate R (mirrorIndex R j) = conj (coordinate R j)
```

and prove involutivity by coordinate injectivity:

```text
mirrorIndex R (mirrorIndex R j) = j.
```

Package it as an `Equiv` if useful:

```lean
pascalCenteredXiSquaredOrbitMirrorEquiv R : Fin n ≃ Fin n
```

The arbitrary original `Fin` enumeration remains presentation-only. The new mirror map is legitimate because the conjugate coordinate determines a unique index in that fixed presentation.

Do not assert that the mirror index equals the original index.

If a canonical function cannot be exposed cleanly, an `Equiv` built by conjugation on the subtype carrier and reindexing is also acceptable, but do not change the mathematical carrier.

## 4. H5-C — representative-level mirror column relation

For every index `j`, the representative squares satisfy

```text
(repFin R (mirrorIndex R j))^2
  = conj ((repFin R j)^2).
```

Also

```text
(conj (repFin R j))^2
  = conj ((repFin R j)^2).
```

Hence the mirror representative and `conj (repFin R j)` have the same square. Since the actual Mellin weight is even, equality of squares is enough to identify their evaluations.

Prove the entrywise column theorem for every real `τ`:

```lean
theorem pascalCenteredXiMellinEvaluationMatrix_mirror_entry
    {R ε : ℝ} (hε : 0 < ε)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (i j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    pascalCenteredXiMellinEvaluationMatrix R ε τ i
        (pascalCenteredXiSquaredOrbitMirrorIndex R j) =
      conj (pascalCenteredXiMellinEvaluationMatrix R ε τ i j) := by
  ...
```

This entrywise theorem is mandatory even if a later matrix identity is also proved.

Important: the row parameter `τ i` is real and is **not** mirrored or permuted.

## 5. H5-D — matrix-level conjugate-column permutation

If the pinned matrix API permits a clean formulation, define the permutation matrix/equivalence induced by `mirrorIndex` and prove the corresponding matrix identity.

Conceptually, with `P` the mirror column permutation,

```text
H * P = conj(H)
```

where `conj(H)` means entrywise complex conjugation.

The exact left/right orientation of `P` must be checked from the chosen Matrix convention. Do not copy the conceptual formula without an entrywise verification.

If the permutation-matrix API is cumbersome, a `Matrix.reindex` theorem or the mandatory entrywise theorem plus a finite-sum reindexing lemma is sufficient. The endpoint is the inverse-row relation, not a particular matrix notation.

Potential classification if the entrywise theorem closes but matrix plumbing is the first real blocker:

```text
MIRROR-MELLIN-COLUMN-TRANSPORT-CLOSED-MATRIX-REINDEX-API-GAP
```

Do not call this a mathematical obstruction unless the entrywise finite identity itself fails.

## 6. H5-E — canonical inverse extractor row

The existing theorem `exists_matrix_coordinate_extractor` is existential. Do not try to compare two arbitrary existential witnesses.

Instead expose the canonical inverse row:

```lean
noncomputable def pascalCenteredXiMellinCanonicalExtractorRow
    (R ε : ℝ)
    (τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ)
    (j : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ :=
  fun i => (pascalCenteredXiMellinEvaluationMatrix R ε τ)⁻¹ j i
```

Under

```text
hdet : det (pascalCenteredXiMellinEvaluationMatrix R ε τ) ≠ 0
```

prove first that this row is the canonical coordinate extractor if a named theorem is useful:

```text
Σ i, extractorRow j i * (H *ᵥ m) i = m j.
```

Then prove the mirror-row transport. The mathematically expected candidate, if H5-A through H5-D have the anticipated orientation, is

```lean
pascalCenteredXiMellinCanonicalExtractorRow R ε τ
    (pascalCenteredXiSquaredOrbitMirrorIndex R j) i =
  conj (pascalCenteredXiMellinCanonicalExtractorRow R ε τ j i)
```

for all `i`.

However this equality is a **candidate, not an instruction to assume it**. Derive it from the matrix relation or by proving that the conjugated original row extracts the mirror coordinate and invoking uniqueness from invertibility.

The uniqueness route is acceptable and may be simpler than proving a general theorem that matrix inversion commutes with entrywise conjugation.

If the actual derivation produces an additional row permutation or a different orientation, state the exact derived law instead and explain it in the report.

This is the H5 endpoint.

## 7. Explicit STOP boundary

Once the canonical extractor-row relation is closed, STOP.

Do **not** yet define or prove the mirror relation for the off-critical scaled coefficient row

```text
q.im * c0
```

and do not use

```text
(conj q).im = -q.im
```

to derive a sign. That is the next H6 stage.

In particular, do not yet claim

```text
cOffMirror = -conj cOff
```

although H5 may make that the obvious next candidate.

Do not transport the synthesized witness, WholeBoxFeature, WholeSource, finite arithmetic approximant, or shifted-energy differences in this stage.

## 8. Firewalls

The implementation and report must explicitly preserve all of the following:

1. **Mass equality does not imply matrix equality.** H5 must come from the Mellin weight itself.
2. **Existential extractors are not canonical.** Compare inverse rows, not arbitrary witnesses.
3. **Mirror index is not the original index.** Any equality must be proved through coordinate injectivity.
4. **Representative choice is not mathematical content.** Use equality of squares + evenness to eliminate the choice.
5. **No hidden `τ` permutation.** `τ : Fin n → ℝ` remains the same real row family.
6. **No `q.im` sign step yet.** That is H6.
7. **No P0→P1 promotion.** This stage contains no positivity provider.
8. **No critical-mirror source-rank claim.** Symmetry remains transport information.
9. **No finite-approximant/RHS identification.** Arithmetic objects are outside this stage.
10. **No limit exchange, no `X → ∞`, no `T → ∞`.** Everything here is finite.
11. **No RH, Li, Weil-positivity, raw-ratio, or classical Guinand--Weil shortcut.**
12. **GWSS-004 remains unauthorized.**

## 9. Suggested implementation location

Prefer a new focused module such as

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean
```

Import the existing critical-mirror pair audit and only the Mellin/matrix dependencies actually needed.

A very small public injectivity/reindexing helper may be added to

```text
PascalCenteredXiMellinActualWindowFullRankAudit.lean
```

if required to avoid reaching into its private enumeration equivalence.

Do not refactor unrelated predecessor modules.

## 10. Required verification

At minimum run:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessCriticalMirrorExtractorAudit
git diff --check
```

Also audit the new load-bearing public declarations with `#print axioms`.

Expected acceptable baseline remains:

```text
[propext, Classical.choice, Quot.sound]
```

No new `sorry`, `admit`, `native_decide`, or axiom.

## 11. Required report

Create:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/0050-GWSS-003H3-mirror-mellin-matrix-extractor-row-transport-report.md
```

The report must state separately:

```text
H5-A weight conjugation
H5-B canonical mirror Fin permutation
H5-C entrywise matrix column relation
H5-D matrix/reindex relation
H5-E canonical inverse extractor-row relation
```

and identify the first unresolved item, if any.

## 12. Classification

Use one primary classification matching the actual endpoint. Preferred labels are:

```text
MIRROR-MELLIN-WEIGHT-CONJUGATION-API-GAP
MIRROR-MELLIN-COLUMN-TRANSPORT-CLOSED-MATRIX-REINDEX-API-GAP
MIRROR-MELLIN-MATRIX-TRANSPORT-CLOSED-EXTRACTOR-GAP
MIRROR-EXTRACTOR-ROW-TRANSPORT-CLOSED
```

If the exact algebra gives a materially different result, introduce a precise label rather than forcing one of these.

Secondary classification should remain, where appropriate:

```text
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

## 13. Mathematical checkpoint

The anticipated finite chain is:

```text
q_j
  ↦ conj(q_j)
  ↦ mirrorIndex(j)

rep(mirrorIndex j)^2 = conj(rep(j)^2)
  + evenness
  + W(conj z) = conj(W z)

H[i, mirrorIndex(j)] = conj(H[i,j])

invertibility
  ⇒ canonical extractor row at mirrorIndex(j)
     is determined from the original row by the exact conjugation/permutation law
```

This chain is only a transport theorem. It contains no new sign, positivity, or RH information.
