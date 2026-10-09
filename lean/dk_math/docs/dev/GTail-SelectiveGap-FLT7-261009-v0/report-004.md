# Report 004 — degree-seven selection calibration

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Outcome **B — exact degree-seven algebraic instrumentation**.
Step 004 is complete; stop before Step 005.

## Changed files

Paths are relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailSeven.lean`: fifteen public calibration endpoints;
  no new mathematical definitions or arithmetic carriers.
- `DkMathTest/CosmicFormula/GTailSeven.lean`: general semiring checks, numerical
  and independent ring regressions, transport/content checks, and axiom audit.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-004.md`: pre-code
  inventory, overlap/norm-carrier audit, and proposed interfaces.
- This report and the adjacent `ROADMAP.md`.

The initial tree was clean and on the requested branch. Existing generic kernels,
FLT owners, façade and library README are unchanged. The new Lean sources retain
License headers, import/file-print ordering and the established formatting.

## Exact theorem signatures

Namespace: `DkMath.CosmicFormula`. Below the implicit semiring parameters from
the source's variable declaration are expanded. There are eleven CommSemiring
endpoints, one separately typed CommRing subtraction endpoint, and three
natural content/divisibility endpoints.

```lean
theorem GTail_seven_six
    {R : Type*} [CommSemiring R] (x u : R) : GTail 7 6 x u = x + 7 * u

theorem GTail_seven_five
    {R : Type*} [CommSemiring R] (x u : R) :
    GTail 7 5 x u = x ^ 2 + 7 * x * u + 21 * u ^ 2

theorem selectedBody_seven_six
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedBody 7 (Finset.Ico 6 8) x u = x ^ 6 * (x + 7 * u)

theorem selectedBody_seven_five
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedBody 7 (Finset.Ico 5 8) x u =
      x ^ 5 * (x ^ 2 + 7 * x * u + 21 * u ^ 2)

theorem selectedGap_seven_interior
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedGap 7 (Finset.Ico 1 7) x u = u ^ 7 + x ^ 7

theorem selectedBody_seven_interior_eq_mul_residual
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedBody 7 (Finset.Ico 1 7) x u =
      x * u * selectedResidual 7 (Finset.Ico 1 7) 1 6 x u

theorem coeffGCD_seven_interior : coeffGCD 7 (Finset.Ico 1 7) = 7

theorem seven_mul_coords_dvd_selectedBody_interior (x u : ℕ) :
    7 * x * u ∣ selectedBody 7 (Finset.Ico 1 7) x u

theorem selectedResidual_seven_interior
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedResidual 7 (Finset.Ico 1 7) 1 6 x u =
      7 * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2

theorem selectedBody_seven_interior
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedBody 7 (Finset.Ico 1 7) x u =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2

theorem add_pow_seven_eq_gap_add_interior
    {R : Type*} [CommSemiring R] (x u : R) :
    (x + u) ^ 7 = (u ^ 7 + x ^ 7) +
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2

theorem add_pow_seven_sub_endpoints {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 7 - x ^ 7 - u ^ 7 =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2

theorem selectedSeven_zero_endpoint_transport
    {R : Type*} [CommSemiring R] (x u : R) :
    selectedBody 7 (insert 0 (Finset.Ico 1 7)) x u =
      7 * x * u * (x + u) * (x ^ 2 + x * u + u ^ 2) ^ 2 + u ^ 7 ∧
    selectedGap 7 (Finset.Ico 1 7) x u =
      selectedGap 7 (insert 0 (Finset.Ico 1 7)) x u + u ^ 7

theorem coeffGCD_seven_zero_endpoint :
    coeffGCD 7 (Finset.Ico 1 7) = 7 ∧ coeffGCD 7 (insert 0 (Finset.Ico 1 7)) = 1

theorem quadratic_form_four_mul
    {R : Type*} [CommSemiring R] (x u : R) :
    (2 * x + u) ^ 2 + 3 * u ^ 2 = 4 * (x ^ 2 + x * u + u ^ 2)
```

No nonzero, characteristic-zero, cancellation, positivity or FLT assumptions
are needed for the semiring equalities. The statements display the quadratic
form directly; no new norm-shaped helper duplicates an existing arithmetic API.

## Dependency route: all three reusable layers are used

| Observation | Actual proof dependencies |
| --- | --- |
| r=6 and r=5 kernels | `GTail_rec`, `GTail_self_eq_one`; finite coefficient evaluation and a small polynomial rearrangement |
| Selected r=6/r=5 Bodies | `selectedBody_Ico` plus the evaluated GTail kernels |
| Interior Gap | finite evaluation of the unselected endpoint terms |
| Interior `x*u` extraction | `selectedBody_eq_monomial_mul_residual` with active bounds i=1, j=6; `activeSelectedIndices_interior` supplies those bounds |
| Interior coefficient gcd and `7*x*u` divisor | `coeffGCD_prime_interior`, `prime_mul_coords_dvd_selectedBody_interior` at p=7 |
| Residual quadratic square | explicit finite residual expansion followed by `ring` |
| Exact interior Body factor | the general-factor adapter followed by the residual square; multiplication associativity/commutativity |
| Big reconstruction | `selectedGap_add_selectedBody`, calibrated Gap and calibrated Body |
| Ring subtraction reading | semiring reconstruction followed by ring rearrangement of the remaining addends |
| Public endpoint-insertion observation | `selectedBody_insert`, `selectedGap_insert`, calibrated Body factor |
| Content change | existing prime-interior and active-endpoint gcd APIs |
| Optional quadratic calibration | `ring`; a polynomial identity with no norm carrier |

The main derivation therefore is:

```text
active bounds -> Body = x*u*Residual
finite residual -> Residual = 7*(x+u)*(x^2+x*u+u^2)^2
selection balance -> Big = endpoint Gap + factored Body
transport -> endpoint u^7 enters Body and leaves Gap
```

Only the small residual and cut-polynomial arithmetic is normalized directly.
The Body proof itself does not unfold the full binomial expansion or substitute
a seventh-power ring identity for the general factor theorem. Reconstruction
does not use an independent full-power expansion. The natural divisor remains
a distinct specialization of the existing coefficient/monomial API.

The explicit residual evaluated in production is:

```text
7*u^5 + 21*x*u^4 + 35*x^2*u^3 + 35*x^3*u^2 + 21*x^4*u + 7*x^5.
```

Multiplying by the forced `x*u` recovers exactly the six interior terms listed
in instruction 004. The factor is an exact equality, not a maximal coordinate
multiplicity or evaluated-value gcd assertion. Endpoint insertion adds `u^7`
while coefficient gcd changes from 7 to 1; these are compatible observations.

## Norm-shaped boundary and overlap audit

The existing integer `TraceOneInt (-1)` norm satisfies
`norm ⟨a,b⟩ = a^2+a*b+b^2`; the existing standard Eisenstein-coordinate map
uses `(m,-n)` and its norm is `m^2-m*n+n^2`. Their carriers and signs were
recorded in the inventory. These APIs are inspected but not imported here.

The optional identity `(2*x+u)^2+3*u^2 = 4*(x^2+x*u+u^2)` is proved over a
CommSemiring. It is a polynomial calibration only. No equality with an actual
norm map, FLT7 cyclotomic degree-six carrier, ideal norm or unit-power class is
claimed. Existing FLT seventh-coordinate cubic factorization is a different
integer polynomial and is not an imported premise.

## Regression results

The focused test provides general CommSemiring type checks for both GTail cuts,
their selected Bodies, interior Gap, residual, balance and zero coordinates.
It checks the ring subtraction corollary over integers. In addition to the
layered derivation, an independent `ring` proof validates the full balanced
identity without calling any selection/factor theorem.

Numerical checks use `norm_num`, not solely `decide`:

| (x,u) over naturals | Gap | Body | Residual |
| --- | ---: | ---: | ---: |
| (1,1) | 2 | 126 | 126 |
| (2,3) | 2315 | 75810 | 12635 |
| (3,2) | 2315 | 75810 | not separately asserted by the numeric test |

At (2,3), the GTail kernels are 23 and 235; selected r=6/r=5 Bodies are
1472 and 7520. A separate direct finite-sum evaluation of the original Body
at (2,3), without the Body factor theorem, and a direct evaluation of the
factored RHS both give 75810. Joint `7*x*u` divisibility is checked at all
three coordinate pairs. The coefficient gcd remains exactly 7.

`(1+1)^7-1-1=126` is checked on naturals by numerical normalization. The
factored RHS is separately normalized to 126. An integer proof also obtains
126 through the ring subtraction theorem before evaluating its RHS.

At x=0 or u=0 the interior Body vanishes and Gap is the surviving endpoint
power, over the same general CommSemiring. A public transport observation and
focused tests give the endpoint-inserted Body, the complementary Gap equation,
conserved Big via `selected_balance_transport`, and coefficient gcd 7 -> 1.
The inserted Body at (1,1) is computed from transport to be 127.

## Exact validation commands and outputs

Working directory: `lean/dk_math`. Focused builds were run sequentially:

```text
lake build DkMath.Lib.Cosmic.GTailSeven
ℹ [1068/1068] Built DkMath.Lib.Cosmic.GTailSeven (3.0s)
info: DkMath/Lib/Cosmic/GTailSeven.lean:11:0: file: DkMath.Lib.Cosmic.GTailSeven
Build completed successfully (1068 jobs).
exit 0

lake build DkMathTest.CosmicFormula.GTailSeven
ℹ [1069/1069] Built DkMathTest.CosmicFormula.GTailSeven (3.2s)
info: DkMathTest/CosmicFormula/GTailSeven.lean:9:0: file: DkMathTest.CosmicFormula.GTailSeven
Build completed successfully (1069 jobs).
exit 0

lake build DkMath.Lib.Cosmic.GTailTransport DkMathTest.CosmicFormula.GTailTransport
Build completed successfully (1068 jobs).
exit 0
```

Final runs have no warnings/errors. An initial test build failed because the
simp attribute on the canonical GTail definition expanded it before the named
numerical-cut adapters were used. Replacing that simplification with explicit
rewrites through those adapters fixed the local test; no statement or
mathematical hypothesis changed. The Step 003 replay again reports its twelve
standard-foundation axiom checks. These are incremental focused runs; no clean
or full-workspace build is claimed.

The focused test runs `#print axioms` on every public endpoint. Exact axiom
lists are below (tool output wraps two of the lists across several lines):

```text
'DkMath.CosmicFormula.GTail_seven_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.GTail_seven_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_seven_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_seven_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedGap_seven_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_seven_interior_eq_mul_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.coeffGCD_seven_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.seven_mul_coords_dvd_selectedBody_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedResidual_seven_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_seven_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.add_pow_seven_eq_gap_add_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.add_pow_seven_sub_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedSeven_zero_endpoint_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.coeffGCD_seven_zero_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.quadratic_form_four_mul' depends on axioms: [propext]

```

All are standard Lean foundations; no `sorryAx` or additional axiom.

From repository root:

```text
rg -n '\b(sorry|admit|axiom|unsafe)\b|^import DkMath\.FLT\.' \
  lean/dk_math/DkMath/Lib/Cosmic/GTailSeven.lean \
  lean/dk_math/DkMathTest/CosmicFormula/GTailSeven.lean
(no matches; exit 1)

git diff --check
(no output; exit 0)
```

Both new sources were read back for review. An additional whitespace check
covers all four new files, including untracked files not examined by git diff.
Production imports are exactly `GTailTransport`, `Mathlib.Tactic.NormNum`, and
`Mathlib.Tactic.Ring`, with no FLT owner dependency.

## Conclusions and stop boundary

The requested factorization is correct with the stated carriers and needs no
specification repair. Steps 001–003 are demonstrably used to obtain the degree-
seven observations. Outcome B records exact finite algebraic calibration.

No FLT7 hypothesis, noncircular arithmetic obstruction, ideal/unit extraction,
norm-map identification, valuation conclusion, descent or contradiction is
proved here. Step 005 (hypothetical FLT7 bridge), Step 006 (constraint audit),
and Step 007 (façade promotion) remain deferred. Work stops after instruction 004.
