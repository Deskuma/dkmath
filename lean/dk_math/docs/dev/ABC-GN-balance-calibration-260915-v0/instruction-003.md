# Instruction-003 — Extract the local valuation balance law

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
checkpoint base: 670acf204798d7965f32faffb0e1ab5ac1102282
```

Accepted checkpoints:

```text
BCAL-000 — Outcome A
BCAL-001 — Outcome A
BCAL-002 — Outcome A
```

Read first:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-002.md
DkMath/ABC/GNBalanceCalibration.lean
DkMath/ABC/GNDepthPressure.lean
DkMath/ABC/GNValuationExcess.lean
DkMath/ABC/GNSupportReturn.lean
```

This checkpoint remains structural. Do not improve an exponent, prove a uniform calibration bound, or construct a new ABC contract.

The new question is no longer the total channel mass alone. We now need to understand the signed balance coordinate

```text
Q = S - E
```

prime by prime and depth layer by depth layer.

---

## 0. Repository-first audit

Confirm the exact current declarations and their source files:

```lean
GNChannelSupportMass
GNChannelDepthMass
GNChannelMass
GNChannelBalance

GNNonExceptionalSupport
GNNonExceptionalSupportProduct
GNNonExceptionalValuationExcess

GNNonExceptionalDepthSupport
GNNonExceptionalDepthMass
GNNonExceptionalSupportLogMass
GNNonExceptionalValuationExcess_eq_sum_prime_depths
GNNonExceptionalValuationExcess_eq_sum_depthMass
GNNonExceptionalSupportLogMass_eq_log_product
one_le_factorization_of_mem_support
```

Also record any already-existing theorem that expresses a local contribution of the form

```text
factorization exponent * log q
```

or a sum of such contributions. Reuse production results rather than duplicating them.

Write the audit and result to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-003.md
```

---

## 1. First-layer / repeated-layer form of the balance

Production already gives the exact first support layer

```text
S = sum_{q in nonExceptionalSupport} log q
```

and the exact repeated-depth layer cake

```text
E = sum_{k >= 2} GNNonExceptionalDepthMass(..., k).
```

Expose these directly in the checkpoint-000 coordinates.

Target exact bridges of the form:

```lean
GNChannelSupportMass T p =
  GNNonExceptionalSupportLogMass p T.a T.b

GNChannelDepthMass T p =
  ∑ k ∈ (Finset.range (GN p T.a T.b)).filter (fun k => 2 ≤ k),
    GNNonExceptionalDepthMass p T.a T.b k
```

and hence exact mass/balance formulas:

```text
GNChannelMass
  = first support layer + all repeated-depth layers

GNChannelBalance
  = first support layer - all repeated-depth layers.
```

These are exact coordinate identities. No estimate is involved.

---

## 2. Local prime contribution

For a non-exceptional support prime `q`, let conceptually

```text
v := (GN p a b).factorization q
w := log q.
```

Then the existing definitions imply

```text
support contribution = w
depth contribution   = (v - 1) * w
local mass            = v * w
local balance         = (2 - v) * w.
```

Introduce the thinnest useful local definitions if they improve the API. Suggested names:

```lean
GNNonExceptionalLocalMass
GNNonExceptionalLocalBalance
```

with mathematical meanings

```text
LocalMass(p,a,b,q)
  := ((GN p a b).factorization q : R) * log(q)

LocalBalance(p,a,b,q)
  := (2 - ((GN p a b).factorization q : R)) * log(q).
```

If repository style favors theorem-only exposure instead of definitions, that is acceptable; document the choice.

---

## 3. Global sum identities

Prove, preferably by reusing the existing support/excess sums, exact identities of the form

```text
GNChannelMass T p
  = sum_{q in GNNonExceptionalSupport p T.a T.b}
      LocalMass(p,T.a,T.b,q)

GNChannelBalance T p
  = sum_{q in GNNonExceptionalSupport p T.a T.b}
      LocalBalance(p,T.a,T.b,q).
```

The second identity is the load-bearing target of this checkpoint.

Equivalently, if a direct local definition is not introduced, expose the exact formula

```text
GNChannelBalance T p
  = sum_{q in nonExceptionalSupport}
      (2 - factorization(q)) * log(q)
```

over `R`, with the necessary casts made explicit.

Do not hide the sign-bearing coefficient inside a natural-number subtraction. The coefficient must live in a signed type (`R` is preferred) so that valuations above `2` visibly contribute negatively.

---

## 4. Identify the local balance pivot

For `q` in non-exceptional support, production already gives `1 <= factorization q`, and support membership gives primality of `q`.

Prove exact/sign consequences whenever clean:

```text
v = 1  -> local balance = + log q
v = 2  -> local balance = 0
3 <= v -> local balance < 0
```

The mandatory result is the exact zero statement at valuation depth `2`.

The positive/negative sign theorems are desirable if they follow cleanly from existing prime/log positivity facts.

Interpretation to record in the report:

```text
v = 1 : support-heavy local contribution
v = 2 : local balance pivot
v >= 3: depth-heavy local contribution
```

This is a **local valuation pivot** extracted from the definitions. It is not a claim that the global contour `GNChannelBalance = 0` occurs only when every local valuation equals `2`.

Do not state that false/unsupported converse: positive and negative local contributions may cancel globally.

---

## 5. Optional local reconstruction law

If useful and algebraically clean, expose the local analogue of checkpoint 000:

```text
support contribution
  = (local mass + local balance) / 2

depth contribution
  = (local mass - local balance) / 2.
```

For a support prime this should reduce respectively to

```text
log q
(v - 1) * log q.
```

This is optional if it adds only naming noise.

---

## 6. What this checkpoint does NOT do

Do not compare two different triples and do not invent a mutation operation that increments a factorization exponent.

In particular do not claim yet:

```text
adding a fresh prime globally increases Q
Hensel lifting globally decreases Q
Q is monotone along a family
Q = 0 is globally optimal
Q = 0 iff every non-exceptional valuation is 2
inner GN balance equals outer ABC balance
```

The algebra suggests the local transport vectors

```text
new first-layer support copy : (+mass, +balance)
additional repeated copy     : (+mass, -balance)
```

but checkpoint 003 should encode these only as local exact identities, not as a global dynamics theorem unless an already-formalized operation supplies the comparison.

Actual Hensel/shell transport can be studied later from this local API.

---

## 7. Preferred module structure

Prefer a new module such as:

```text
DkMath/ABC/GNBalanceDepthLayers.lean
```

with imports no stronger than necessary, likely including:

```lean
DkMath.ABC.ABCCalibrationSourceDecomposition
DkMath.ABC.GNDepthPressure
```

Avoid refactoring historical production files.

After focused build success, export the module through `DkMath.ABC` once.

---

## 8. Validation

Run at least:

```text
lake env lean DkMath/ABC/GNBalanceDepthLayers.lean
lake build DkMath.ABC.GNBalanceDepthLayers
lake build DkMath.ABC
```

or repository-equivalent commands if another module path is justified.

Also run:

```text
git diff --check
```

and the standard forbidden-pattern scan for:

```text
sorry
admit
axiom
unsafe
```

Audit `#print axioms` for the load-bearing global balance-sum theorem.

---

## 9. Outcome classification

Use one of:

```text
Outcome A — LOCAL VALUATION BALANCE LAW COMPLETE
Outcome B — PARTIAL LOCALIZATION / CAST OR API BOUNDARY FOUND
Outcome C — EXISTING DEPTH API ALREADY SUFFICIENT / NO NEW PRODUCTION SURFACE JUSTIFIED
```

Outcome A requires at minimum:

```text
first-layer / repeated-layer expression of GNChannelBalance
exact prime-local balance sum
valuation-depth-2 local zero pivot
focused build success
```

---

## 10. Hard boundary

No numerical exponent work, no uniform residual bound, no supremum, no new ABC contract, no cubic shell count, and no claim that valuation `2` globally solves the ABC balance problem.

The purpose is to identify the **local ruler of the scale**: one fresh support copy contributes positively, the second copy reaches the local pivot, and copies beyond the second contribute to the depth side.
