# FLT3 Unconditional — reconnaissance report 000

cid: `6a9aa2b0-937c-83e8-aa29-b3474c8acdf9`

Branch: `wip/flt3-unconditional-260904-v0`

Base: `develop @ 99ff6fcefed5bb1775e0a685cee9025fd7fdcc69`

Date: 2026-09-04

## 1. Executive conclusion

この checkpoint では Lean source を変更していない。現行 workspace の
read-only reconnaissance の結果、FLT3U-001 は計画どおり進められる。

**Outcome A — FLT3U-001 can proceed essentially as planned.**

primitive FLT3 counterexample と `exists_prime_factor_cube_diff` の witness から、
次の packet data は既存 API の合成で供給できる。

- `Nat.Coprime (c - b) b`
- `q ∣ GN 3 (c - b) b` および `q ∣ S0_nat c b`
- `q ≠ 3`
- `3 ∣ q - 1`
- `¬ q ∣ 2 * (c - b) + 3 * b`
- `3 ≤ padicValNat q (GN 3 (c - b) b)`

ただしこれは FLT3 の無条件閉包ではない。有限 Hensel の一意性は lift branch
を否定せず、`GN 3 17 1 = 7^3` がその境界反例である。strict descent に必要な
Eisenstein の divisibility / coprime factor extraction / unit sectors はまだ
production theorem になっていない。

## 2. Exact current FLT3 proof frontier

### 2.1 Conditional endpoint

`DkMath.FLT.FLT_d3_by_padicValNat` は
[`DkMath/FLT/Main.lean:142`](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/FLT/Main.lean:142)
にあり、完全な型は次である。

```lean
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 →
        ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

`hS0_not_sq` は証明本体の [`Main.lean:171-173`](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/FLT/Main.lean:171)
で、選ばれた `q` に一度だけ適用される。その出力が
`padicValNat_upper_bound_d3` の入力になる。

`NoSqOnS0`、`NoSqInput`、`NoSqBaseInput`、`AllNonLiftableOnS0` および
`GEisenstein` 経由の `NoSq` adapter は、この obligation を供給するための
互換・合成層であり、lift branch を数学的に閉じる本体ではない。

### 2.2 Existing proof chain

現在の conditional contradiction は次の順である。

1. `coprime_cb_of_eq` が `Nat.Coprime a b` と仮想等式から
   `Nat.Coprime c b` を得る（[`PhaseLift.lean:478`](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/FLT/PhaseLift.lean:478)）。
2. `b < c` を正値性から得る。
3. `exists_prime_factor_cube_diff` で primitive-style witness `q` を得る。
4. `q ∣ a` から `3 ≤ padicValNat q (a^3)` を得る。
5. `hS0_not_sq` から `padicValNat q (c^3-b^3) ≤ 1` を得る。
6. `c^3-b^3=a^3` と `omega` で矛盾する。

この chain に lift branch の descent は含まれない。

## 3. Reusable theorem inventory table

| obligation | exact identifier | path / lines | result |
|---|---|---|---|
| cube subtraction | `cube_sub_eq_of_add_eq` | `DkMath/FLT/PhaseLift.lean:470` | `c^3-b^3=a^3` |
| `gcd(c,b)` | `coprime_cb_of_eq` | `DkMath/FLT/PhaseLift.lean:478` | `Nat.Coprime c b` |
| primitive q existence | `exists_prime_factor_cube_diff` | `DkMath/FLT/PhaseLift.lean:613-618` | `q` prime, divides difference, avoids gap |
| difference factorization | `cube_sub_eq_mul_sub_S0` | `DkMath/FLT/PhaseLift.lean:624-630` | `c^3-b^3=(c-b)*S0_nat c b` |
| q to S0 | `prime_dvd_S0_via_cosmic_bridge` | `DkMath/FLT/CosmicPetalBridge.lean:153-163` | `q ∣ S0_nat c b` |
| canonical GN/S0 equality | `GN_three_sub_eq_S0_nat` | `DkMath/FLT/CosmicPetalBridge.lean:142-147` | `GN 3 (c-b) b = S0_nat c b` |
| Petal-facing reverse equality | `S0_nat_eq_GN_three_sub` | `DkMath/Petal/GNBridge.lean:31-37` | reverse orientation |
| primitive valuation transport | `primitive_prime_padic_eq_GN` | `DkMath/NumberTheory/PrimitiveBeam.lean:77-102` | difference valuation equals GN valuation |
| Petal valuation wrapper | `primitive_prime_padicValNat_cube_sub_eq_S0_nat` | `DkMath/Petal/PrimitiveBridge.lean:42-57` | difference valuation equals S0 valuation |
| q=3 criterion | `three_dvd_GN_three_iff_dvd_boundary` | `DkMath/NumberTheory/GNThreePrimeArithmetic.lean:34-55` | `3 ∣ GN 3 u x ↔ 3 ∣ u` |
| ramified square exclusion | `not_nine_dvd_GN_three_of_coprime` | same file:59-98 | coprime coordinates imply `¬9 ∣ GN` |
| residue constraint | `three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three` | same file:166-249 | `3 ∣ q-1` |
| derivative exclusion | `prime_not_dvd_cubic_boundary_derivative` | same file:255-286 | `¬q ∣ 2*u+3*x` |
| one-step lift | `existsUnique_GN_three_sqLift_digit` | `GNThreeHenselLift.lean:109-165` | unique `Fin q` digit for `q → q²` |
| arbitrary finite lift | `existsUnique_GN_three_powLift_digit` | `GNThreeHenselDepth.lean:120-173` | unique digit for `q^k → q^(k+1)` |
| primitive finite lift | `existsUnique_GN_three_powLift_digit_of_primitive_nonramified` | same file:176-191 | wrapper using primitive non-ramified data |
| derivative stability | `prime_not_dvd_cubic_boundary_derivative_add_prime_pow_mul` | same file:196-211 | derivative remains nonzero after finite shift |
| descent interface | `PrimitiveSquareDescentStep` | `GEisensteinBridge.lean:421-429` | abstract smaller square-lift witness |
| descent closure skeleton | `false_of_state_of_stepExists` | same file:694-706 | strong induction over an abstract `q` measure |

### 3.1 Primitive prime witness exact return data

`exists_prime_factor_cube_diff` returns exactly

```lean
∃ q : ℕ,
  Nat.Prime q ∧
  q ∣ c ^ 3 - b ^ 3 ∧
  ¬ q ∣ c - b
```

It does not directly return `q ∣ S0_nat c b`, `q ≠ 3`, `3 ∣ q - 1`, derivative
nondegeneracy, a valuation lower bound, or `Nat.Coprime (c-b) b`.

`PrimitivePrimeFactorOfDiffPow` in `PrimitiveBeam.lean:23-26` is a richer predicate,
but it is a separate wrapper and is not the return type of the FLT `PhaseLift`
witness theorem.

### 3.2 Primitive coordinate coprimality

For the FLT counterexample coordinates, `coprime_cb_of_eq` supplies
`Nat.Coprime c b`. The gap form is the standard library theorem used by
`DkMath.Petal.coprime_sub_right_of_coprime`:

```lean
(Nat.coprime_sub_self_left hbc.le).2 hcop
```

The wrapper is at [`DkMath/Petal/GcdBridge.lean:34-37`](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/Petal/GcdBridge.lean:34).
No new mathematical lemma is needed for FLT3U-001.

### 3.3 q=3, residue, and derivative chain

Set `u := c - b` and `x := b`.

- From the witness and `prime_dvd_S0_via_cosmic_bridge`, then
  `GN_three_sub_eq_S0_nat`, obtain `q ∣ GN 3 u x`.
- If `q = 3`, `three_dvd_GN_three_iff_dvd_boundary` gives `3 ∣ u`, contradicting
  `¬ q ∣ c-b`. Thus `q ≠ 3`.
- With `Nat.Coprime u x`, `q ∣ GN 3 u x`, and `q ≠ 3`, apply
  `three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three` to get
  `3 ∣ q - 1`.
- The same inputs feed `prime_not_dvd_cubic_boundary_derivative` and give
  `¬ q ∣ 2*u+3*x`.

For a square-lift input `q^2 ∣ GN 3 u x`, the specialized theorem
`three_dvd_prime_sub_one_of_square_lift_GN_three` packages the q=3 exclusion via
`not_nine_dvd_GN_three_of_coprime` and supplies the same residue constraint.

## 4. False / forbidden route inventory

### 4.1 Universal no-lift is false

`GNThreePrimeArithmetic.lean` contains executable regressions

```lean
GN 3 17 1 = 343
GN 3 17 1 = 7 ^ 3
7 ^ 2 ∣ GN 3 17 1
```

Therefore neither `∀ q, ¬ q^2 ∣ GN 3 u x` nor a universal squarefree claim may
be used for the primitive cubic shell.

### 4.2 Hensel uniqueness is not a contradiction

The Hensel modules prove existence and uniqueness of a finite next digit. They
do not prove that a lift digit fails to exist, that an infinite q-adic object
exists, or that a finite lift contradicts a perfect cube. The `17,1,7` regression
is deliberately retained as a boundary test.

### 4.3 Existing no-lift research route

`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains
`squarefree_implies_padic_val_le_one_research` with `sorry` at lines 147-159 and
the wrapper `padicValNat_primitive_prime_factor_le_one_research` at lines 170-178.
This is not a valid provider for the unconditional FLT3 route. The honest
replacement requires an explicit `Squarefree (GN d (a-b) b)` assumption, or the
new lift/descent route.

## 5. GNPC-to-FLT3 connection

For the packet, the recommended production chain is:

```text
FLT equation
  -> coprime_cb_of_eq
  -> b < c
  -> exists_prime_factor_cube_diff
  -> GN_three_sub_eq_S0_nat / prime_dvd_S0_via_cosmic_bridge
  -> q != 3 via three_dvd_GN_three_iff_dvd_boundary
  -> 3 | q - 1 and derivative nondegeneracy
  -> finite-depth GN Hensel API
```

The current Main theorem's lower-bound chain is already kernel-checked:

```text
cube_sub_eq_of_add_eq
  -> q ∣ a^3
  -> Nat.Prime.dvd_of_dvd_pow
  -> padicValNat_lower_bound_of_dvd_d3
  -> 3 ≤ padicValNat q (c^3-b^3)
```

The stronger divisibility statement
`3 ∣ padicValNat q (GN 3 (c-b) b)` is also a short finite composition once
the valuation is transported to `a^3`: use
`DkMath.ABC.dvd_padicValNat_pow hq 3 (Nat.ne_of_gt ha)` and rewrite with
`cube_sub_eq_of_add_eq`, followed by the GN/S0 valuation bridge. This is not an
infinite-depth or valuation-classification theorem.

## 6. Eisenstein substrate inventory

### 6.1 What exists

`DkMath.FLT.GEisensteinBridge` defines the Nat-valued form
`eisensteinNormNat x y := x^2 - x*y + y^2` and proves:

- `S0_eq_eisensteinNorm_shift` at lines 25-36;
- `GN3_sub_eq_S0` at lines 38-49;
- `GN3_sub_eq_eisensteinNorm_shift` at lines 51-54.

`DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)` is a coordinate
`CommRing` with conjugation, multiplicative norm, and the identity
`norm (a,b) = a^2+a*b+b^2`; see
[`TraceOneQuadratic.lean:14-119`](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean).
It is the appropriate coordinate-ring model for the Eisenstein order
(`tau^2 - tau + 1 = 0`).

Mathlib also provides the generic `QuadraticAlgebra` norm/star API and the
`Zsqrtd` quadratic-coordinate infrastructure. The `Zsqrtd.GaussianInt` file is
for `sqrt(-1)`, not the Eisenstein order. No dedicated production-ready
Eisenstein integer type with all required descent infrastructure was found.

### 6.2 What is missing

For the FLT3 route, the current code does not provide a production theorem for:

- Eisenstein divisibility and gcd/ideal coprimality in `TraceOneInt (-1)`;
- EuclideanDomain, PID, or UFD structure for that order;
- exact ramifier-above-3 ownership;
- unit classification modulo cubes;
- cube extraction from coprime conjugate factors;
- the coordinate reconstruction and strict smaller-packet theorem.

Thus `eisensteinNormNat` and the TraceOne norm identities are bridges only.

### 6.3 Existing GEisensteinBridge separation

The existing bridge does implement useful abstract interfaces:

- `PrimitiveSquareWitness` and `PrimitiveSquareDescentStep`;
- `PrimitiveSquareDescentEngine` / `ReductionKernel`;
- `NumberTheoryDescentState` with strong-induction contradiction;
- `GEisensteinDescentFrame` and bounded `descend`;
- `GEisensteinDescentCore` with `classifyImpossible`, a frame, and a `pred` step.

However, `GEisensteinCandidate.step` and
`GEisensteinPrimitiveSizedCandidate.step` are explicitly provisional `Nat.pred`
steps (lines 188-305), not arithmetic Eisenstein descent. The current
`GEisensteinDescentCore` therefore records a provider contract; it does not
prove the provider.

## 7. Dependency audit

### 7.1 Completed FLT3 shortcut

The forbidden completed theorem dependency is present in the old route:

- `DkMath/FLT/Core.lean:11` imports `Mathlib.NumberTheory.FLT.Three`;
- `DkMath/FLT/Basic.lean:23` imports it directly;
- `DkMath/FLT/MathlibBridge/FLT34.lean:7-8` imports the Mathlib FLT(3,4)
  theorems and defines `FLT3_core := fermatLastTheoremThree`;
- `DkMath/FLT/Basic.lean:55-97` uses `fermatLastTheoremThree` in the `u=1`
  slice.

This is an existing compatibility/control route, not evidence for the new
unconditional route.

### 7.2 Recommended new import boundary

`FLT3U-001` should use a new module below `DkMath/FLT/Three/` with the stable
minimal imports:

```lean
import DkMath.FLT.PhaseLift
import DkMath.NumberTheory.GNThreeHenselDepth
```

`GNThreeHenselDepth` brings the prime-arithmetic and one-step Hensel layers.
The module should not import `DkMath.FLT.Basic`, `DkMath.FLT.Core`,
`DkMath.FLT.MathlibBridge.FLT34`, or any completed FLT theorem. It should also
avoid `DkMath.Petal.PrimitiveBridge` and `DkMath.NumberTheory.PrimitiveBeam`
unless the dependency audit explicitly accepts their research-module imports;
the packet can use the weak `PhaseLift` witness and a local thin valuation/GN
wrapper instead.

The public `DkMath.FLT` aggregator is also inappropriate as a construction
import: it is a broad facade and obscures the dependency boundary.

## 8. Minimal imports recommended for FLT3U-001

Recommended implementation import surface:

```lean
import DkMath.FLT.PhaseLift
import DkMath.NumberTheory.GNThreeHenselDepth
```

The first import supplies the FLT equation normalization, primitive q witness,
cube/S0 factorization, `S0_nat`, and the existing p-adic lower-bound lemmas.
The second supplies `GNThreePrimeArithmetic`, exact finite-depth linearization,
unique digits, and derivative stability.

If the implementation chooses the already-defined `PrimitivePrimeFactorOfDiffPow`
bridge, that choice must be called out because `PrimitiveBeam.lean` imports
`ZsigmondyCyclotomicResearch`. The preferred U001 boundary is a direct local
construction from the four-field FLT witness, without importing that research
adapter.

## 9. Proposed exact theorem / structure surface for FLT3U-001

The first production object should be a packet, not a final theorem or a
descent provider. A suitable surface is:

```lean
structure PrimitiveCubicLiftPacket (a b c q : ℕ) : Prop where
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hab : Nat.Coprime a b
  hEq : a ^ 3 + b ^ 3 = c ^ 3
  hbc : b < c
  hcb_coprime : Nat.Coprime c b
  hgap_coprime : Nat.Coprime (c - b) b
  q_prime : Nat.Prime q
  q_dvd_diff : q ∣ c ^ 3 - b ^ 3
  q_not_dvd_gap : ¬ q ∣ c - b
  q_dvd_GN : q ∣ GN 3 (c - b) b
  q_ne_three : q ≠ 3
  q_mod_three : 3 ∣ q - 1
  derivative_ne_zero : ¬ q ∣ 2 * (c - b) + 3 * b
  valuation_lower : 3 ≤ padicValNat q (GN 3 (c - b) b)
```

The constructor theorem should have the shape

```lean
theorem PrimitiveCubicLiftPacket.of_counterexample_and_witness
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3)
    (q : ℕ) (hq : Nat.Prime q)
    (hqDiff : q ∣ c ^ 3 - b ^ 3)
    (hqGap : ¬ q ∣ c - b) :
    PrimitiveCubicLiftPacket a b c q
```

The constructor is expected to use `coprime_cb_of_eq`,
`Nat.coprime_sub_self_left`, `GN_three_sub_eq_S0_nat`,
`three_dvd_GN_three_iff_dvd_boundary`,
`three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three`,
`prime_not_dvd_cubic_boundary_derivative`, and the cube-side valuation chain.

U001 should not yet add:

- an `either` theorem that claims all lifts are impossible;
- an infinite q-adic sequence;
- Eisenstein UFD assumptions hidden in a packet;
- `FLT_d3_unconditional` or positive-natural gcd normalization;
- a new `research` theorem, axiom, or `sorry`.

## 10. Risks and stop conditions

1. The selected q may lie in a square-lift branch. This is expected and must be
   represented, not eliminated by a universal no-lift lemma.
2. `3 ∣ q-1` is a residue constraint, not a descent or contradiction.
3. The finite Hensel theorem gives one digit at each positive depth but does not
   provide a limit or a contradiction with cube valuation.
4. The Nat form `eisensteinNormNat` uses truncated subtraction; production
   arithmetic should prefer the integral `TraceOneInt (-1)` coordinates or prove
   the required non-truncation side conditions explicitly.
5. A theorem imported through `PrimitiveBeam` may be mathematically suitable but
   can widen the dependency graph to a research module. Audit imports before
   adopting it.
6. The current `GEisensteinDescentFrame` can prove termination of a supplied
   `pred`-like step, but does not construct an arithmetic step.

Stop and return to a new report if a required packet field cannot be obtained
without a new assumption, if the proposed statement becomes universal no-lift,
or if the module begins to depend on `Mathlib.NumberTheory.FLT.Three`.

## 11. Outcome

**Outcome A.** The reconnaissance establishes a sufficient and narrow theorem
surface for `FLT3U-001`. The next checkpoint may implement
`DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean` under the import boundary above.

This report is the only file changed by checkpoint FLT3U-000. No commit, push,
public-import update, or Lean source implementation was performed here.
