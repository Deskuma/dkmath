# Git diff / Report / Review

## hack: cp-002

gch: 814f111f702dfaf8c2eb93f98274a424fba5aa09

## Report

Checkpoint `hack-002` completed.

Implemented in [FinitePrimeEscape.lean](/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean):

- `FreshPrimeFactor`
- `prime_dvd_product_add_coprime_not_mem`
- `exists_fresh_prime_factor`

Also wrote [report-hack-002.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md) and corrected the audited Nat API signature in [EXISTING_DKMATH_MAP.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md).

Verification:

- Focused build passed: `726/726`
- No `sorry`, `admit`, or `axiom`
- `git diff --check` passed
- Proof remains entirely in `ℕ`
- No unnecessary primality, nonempty, or positivity assumptions added
- No `hack-003` work begun

Next action: Wise Wolf review of `hack-002`.

## Review

# hack-002 状況分析・レビュー

## 判定

**ACCEPT — checkpoint `hack-002` を受理。**

要求された三つの宣言が、予定どおり最小の `Nat` facade として完成しておる。

```text
FreshPrimeFactor
prime_dvd_product_add_coprime_not_mem
exists_fresh_prime_factor
```

focused build は `726/726`、`sorry`・`admit`・`axiom` なし、許可された範囲外への実装拡張もない。

---

## 状況分析

### Core — 有限 prime escape の核が閉じた

今回の定理は、有限集合 `S` の積を

$$
P=\prod_{p\in S}p
$$

としたとき、

$$
\gcd(P,u)=1
$$

ならば、`P + u` の任意の素因子 `q` は `S` に含まれないことを正式に閉じた。

Lean 上の流れも綺麗じゃ。

```text
q ∈ S
→ q ∣ P
→ q ∣ P + u
→ q ∣ u
→ q ∣ gcd(P,u)
→ q ∣ 1
→ contradiction
```

特に、監査時に想定した一般 ring theorem ではなく、実際の `Nat` API である

```lean
Nat.dvd_add_iff_right
```

へ正しく補正された。最初の `.mp` / `.mpr` の向き違いも、局所 API 修正として処理されており、数学的障害ではない。

---

### True Beam — theorem surface が余計な仮定を持っていない

完成した核定理には、次が入っていない。

```text
∀ p ∈ S, Nat.Prime p
S.Nonempty
0 < u
0 < P
```

これは正しい。

除外証明に必要なのは、

```text
q が S に入っている
q が prime
q が P + u を割る
P と u が coprime
```

だけである。

したがってこの定理は、物語上の「有限素数宇宙」よりも数学的には強い。

> `S` が任意の有限自然数集合であっても、その積と coprime な offset を加えた境界の素因子は `S` の元ではない。

`S` の要素がすべて素数であることは、後の Demo や解説で「既知の素数集合」と呼ぶための意味条件であって、kernel theorem の証明条件ではない。

この分離が Lean 宣言にそのまま反映されたのは非常に良い。

---

### 存在定理も正しく分離された

kernel theorem は supplied divisor の排除だけを担当する。

```lean
prime_dvd_product_add_coprime_not_mem
```

存在側は、

```lean
Nat.ne_one_iff_exists_prime_dvd
```

から素因子を一つ取り出し、kernel theorem へ流している。

```text
boundary > 1
→ boundary ≠ 1
→ prime divisor exists
→ divisor is outside S
```

これにより、

```lean
exists_fresh_prime_factor
```

が自然に閉じた。

排除と存在を一つの巨大証明へ混ぜず、役割を分けた設計は、後の Demo でも使いやすい。

---

## 実装レビュー

### `FreshPrimeFactor`

```lean
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

意味が最小で明確じゃ。

```text
prime
divides target
outside reference set
```

以上も以下も含まない。

特に、

```text
primitive
first occurrence
valuation
multiplicity
sequence history
```

を混ぜていない点が正しい。

---

### kernel theorem

```lean
theorem prime_dvd_product_add_coprime_not_mem ...
```

実装は読みやすく、各中間事実にも意味のある名前が付いている。

```lean
hqProd
hqU
hqGcd
hgcd
```

証明経路がそのままコードから読めるため、hackathon のコード表示にも向いておる。

`classical` は `Finset` membership/product の処理上許容範囲であり、この小さな facade では問題ない。

---

### imports

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic
```

`import Mathlib` へ逃げず、狭い import で閉じたのも良い。

また、明示的に避けるべきだった以下へ依存していない。

```text
DkMath.Samples.Prime.B
PrimitiveSet
Petal
Zsigmondy
KUS
Units
```

したがって Hackathon facade は完全に downstream の薄い層として保たれている。

---

## 意味境界

今回証明されたのは、

> 有限集合の積と coprime な offset による fresh factor escape

である。

まだ証明していないものは明確じゃ。

```text
Cosmic Formula completion
固定 Demo
projection
inverse projection
DkReal reconstruction
prime infinitude
primitive prime divisor
```

ここで止まったのは正しい。

---

## 軽微な留意点

外側レビュー名が再び `cp-002`、正式 checkpoint が `hack-002` となっている。

以後の保存名・レビュー名は、

```text
hack-003
hack-004
```

へ統一してよい。

それ以外に修正要求はない。

---

# 次の checkpoint

次は `hack-003`、Cosmic Formula の平方完成である。

今回はさらに小さい。

追加すべき数学宣言は原則一件だけじゃ。

$$
P(P+2u)+u^2=(P+u)^2
$$

既存 DkMath の一般 Big / Body / Gap 理論との意味的一致は監査済みである。しかし MVP facade では、その深い層を import せず、局所的な `ring` theorem として閉じる。

# 次の Codex Instructions

````md
# Checkpoint hack-003 — Cosmic Formula Square Completion

## Session Class

```text
IMPLEMENTATION
```

## Primary Goal

Implement the minimal natural-number Cosmic Formula square-completion theorem.

Add one public theorem proving:

```lean
P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

This checkpoint must remain a thin arithmetic facade.

Do not begin Demo, projection, DkReal, geometry, or visualization work.

## Required Reading

Read:

```text
MATHEMATICAL_CONTRACT.md
ARCHITECTURE.md
EXISTING_DKMATH_MAP.md
report-hack-001.md
report-hack-002.md
this instruction
```

Use the accepted audit findings.

Do not repeat the broad repository audit.

## Permitted Edit Files

```text
lean/dk_math/DkMath/Hackathon/CosmicCompletion.lean

lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-003.md
```

You may correct an implementation-confirmed error in:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  EXISTING_DKMATH_MAP.md
```

only if Lean demonstrates that the audited entry is inaccurate.

No other file is editable.

## Required Declaration

Inside:

```lean
namespace DkMath.Hackathon
```

implement a theorem equivalent to:

```lean
/--
The square case of the Cosmic Formula: Body plus square Gap completes
the square with boundary `P + u`.
-/
theorem cosmicCompletion
    (P u : ℕ) :
    P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2 := by
  ring
```

The exact theorem name should remain `cosmicCompletion` unless Lean naming or repository conventions require a justified change.

## Architectural Decision

The audit confirmed that DkMath already contains generic Big / Body / Gap theory.

For this public MVP theorem, do not force the natural-number identity through:

```text
DkMath.CosmicFormula.Defs
DkMath.CosmicFormulaBinom
DkMath.CosmicFormula.CoreBeamGap
DkMath.Samples.Prime.B
```

The local theorem is intentionally a thin stable specialization.

The report must explain that this theorem is mathematically consistent with the existing generic Cosmic Formula architecture while avoiding a broad or unfinished dependency.

## Imports

Prefer a narrow import sufficient for `ring`.

A suitable first attempt is:

```lean
import Mathlib.Tactic
```

Using `import Mathlib` is acceptable only if a narrower import causes disproportionate effort. Record the actual choice.

Do not import:

```text
DkMath.Samples.Prime.B
DkMath.Hackathon.Demo
DkMath.Analysis.DkReal.*
DkMath.Petal.*
DkMath.NumberTheory.PrimitiveSet.*
```

## Stages

### Stage A — Confirm the local target

Confirm that the target theorem elaborates over `ℕ` and requires no additional assumptions.

Do not add:

```text
0 < P
0 < u
Nat.Coprime P u
```

The equality is unconditional.

### Stage B — Implement the theorem

Add only the public square-completion theorem and its concise documentation comment.

Do not create new foundational definitions for:

```text
Big
Body
Gap
Gnomon
```

### Stage C — Verify

Run from `lean/dk_math`:

```bash
lake build DkMath.Hackathon.CosmicCompletion
```

Then run:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
  DkMath/Hackathon/CosmicCompletion.lean

git diff --check
git status --short
```

Inspect the final diff.

### Stage D — Report and Stop

Write:

```text
docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-003.md
```

The report must include:

```text
status
files changed
theorem added
import used
proof method
relation to existing DkMath Cosmic Formula APIs
reason for the thin local wrapper
build command and result
no-sorry result
git diff result
mathematical meaning
meaning boundary
first genuine obstruction
next permitted action
stop confirmation
```

## Completion Conditions

The checkpoint is complete when:

```text
cosmicCompletion builds over ℕ;

the theorem has no unnecessary assumptions;

no parallel Big / Body / Gap hierarchy was created;

no broad unfinished sample module was imported;

only permitted files changed;

the focused build passes;

report-hack-003.md is complete.
```

## Stopping Rule

Stop and report the smallest exact obstruction if:

```text
the target does not close over Nat with ring;

the required tactic import creates an unexpected dependency problem;

the theorem requires a statement change;

a permitted edit would force modification of existing core DkMath.
```

Do not respond by:

```text
adding sorry;
adding an axiom;
changing the theorem into subtraction form;
moving the theorem to Real;
editing Demo.lean;
beginning projection or DkReal work.
```

## Final Instruction

Complete `hack-003`, write `report-hack-003.md`, and stop.

Do not begin `hack-004`.
````

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean b/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
index 64eeea5b..8a7aa7d6 100644
--- a/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
+++ b/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
@@ -3,3 +3,52 @@ Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
 Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
+
+import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
+import Mathlib.Data.Nat.Prime.Basic
+
+namespace DkMath.Hackathon
+
+open scoped BigOperators
+
+/-- A prime divisor of `n` outside the finite reference set `S`. -/
+def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
+  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
+
+/--
+A prime divisor of the product-plus-offset boundary cannot be one of the
+factors in the product when the product and offset are coprime.
+-/
+theorem prime_dvd_product_add_coprime_not_mem
+    {S : Finset ℕ} {u q : ℕ}
+    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
+    (hqPrime : Nat.Prime q)
+    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
+    q ∉ S := by
+  classical
+  intro hqMem
+  have hqProd : q ∣ ∏ p ∈ S, p :=
+    Finset.dvd_prod_of_mem (fun p : ℕ => p) hqMem
+  have hqU : q ∣ u :=
+    (Nat.dvd_add_iff_right hqProd).mpr hqDiv
+  have hqGcd : q ∣ Nat.gcd (∏ p ∈ S, p) u :=
+    Nat.dvd_gcd hqProd hqU
+  have hgcd : Nat.gcd (∏ p ∈ S, p) u = 1 := hcop
+  rw [hgcd] at hqGcd
+  exact hqPrime.not_dvd_one hqGcd
+
+/--
+Every nontrivial product-plus-offset boundary has a prime divisor outside the
+finite reference set when the product and offset are coprime.
+-/
+theorem exists_fresh_prime_factor
+    {S : Finset ℕ} {u : ℕ}
+    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
+    (hboundary : 1 < (∏ p ∈ S, p) + u) :
+    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q := by
+  obtain ⟨q, hqPrime, hqDiv⟩ :=
+    Nat.ne_one_iff_exists_prime_dvd.mp (Nat.ne_of_gt hboundary)
+  refine ⟨q, hqPrime, hqDiv, ?_⟩
+  exact prime_dvd_product_add_coprime_not_mem hcop hqPrime hqDiv
+
+end DkMath.Hackathon
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
index c9c66fba..110f0e20 100644
--- a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
@@ -20,7 +20,7 @@ needed.
 | Role | Module | Declaration and normalized type | Class | Cost |
 |---|---|---|---|---|
 | member divides product | `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` | `Finset.dvd_prod_of_mem (f) (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i` | DIRECT | narrow through Mathlib |
-| remove known addend | `Mathlib.Algebra.Ring.Divisibility.Basic` | `dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c` | DIRECT | narrow |
+| remove known Nat addend | Mathlib Nat divisibility API | `Nat.dvd_add_iff_right (h : k ∣ m) : k ∣ n ↔ k ∣ m + n` | DIRECT | narrow |
 | coprime means gcd one | Mathlib Nat gcd | `Nat.coprime_iff_gcd_eq_one : Nat.Coprime a b ↔ Nat.gcd a b = 1` | DIRECT | narrow |
 | common divisor divides gcd | Mathlib Nat gcd | `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n` | DIRECT | narrow |
 | prime cannot divide one | Mathlib Nat prime | `Nat.Prime.not_dvd_one : Nat.Prime q → ¬ q ∣ 1` | DIRECT | narrow |
@@ -28,7 +28,7 @@ needed.
 
 Shortest exclusion route, entirely in `ℕ`: from `q ∈ S`, use
 `Finset.dvd_prod_of_mem id` to obtain `q ∣ P`; combine that with
-`q ∣ P + u` via `dvd_add_right` to get `q ∣ u`; then `Nat.dvd_gcd`,
+`q ∣ P + u` via `Nat.dvd_add_iff_right` to get `q ∣ u`; then `Nat.dvd_gcd`,
 `Nat.coprime_iff_gcd_eq_one`, and `Nat.Prime.not_dvd_one` contradict
 primality. No subtraction or `ℤ` bridge is required.
 
@@ -85,7 +85,7 @@ exclusion proof may rewrite with `Nat.coprime_iff_gcd_eq_one`.
 
 ### MAP-005 — Divisor of `P + u` and `P` Divides `u`
 
-CONFIRMED / DIRECT. `dvd_add_right hqP` turns `q ∣ P + u` into `q ∣ u`.
+CONFIRMED / DIRECT. `Nat.dvd_add_iff_right hqP` turns `q ∣ P + u` into `q ∣ u`.
 This is cleaner than the `Nat.dvd_sub` route used in the older sample.
 
 ### MAP-006 — Coprimality Excludes a Prime Dividing Both Inputs
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md
new file mode 100644
index 00000000..23e7cf62
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md
@@ -0,0 +1,202 @@
+# Report — Checkpoint hack-002
+
+## Status
+
+```text
+COMPLETED
+```
+
+## Session Metadata
+
+```text
+Checkpoint: hack-002
+Session class: IMPLEMENTATION
+Model: GPT-5 Codex
+End: 2026/07/15 07:49 JST
+```
+
+## Primary Goal
+
+Implement the minimal natural-number facade for finite-set prime escape: a
+fresh-prime-factor predicate, supplied-divisor exclusion, and an existence
+corollary.
+
+## Files Changed
+
+Checkpoint implementation files:
+
+- `DkMath/Hackathon/FinitePrimeEscape.lean`
+- `docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md`
+
+Implementation-confirmed correction:
+
+- `docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md`
+
+The map correction changes the ring-only unqualified `dvd_add_right` audit
+entry to the actual Nat declaration `Nat.dvd_add_iff_right`, including its
+correct implication orientation.
+
+The pre-existing `hack-001` map and report changes remained in the working
+tree and were not reverted.
+
+## Definition Added
+
+```lean
+def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
+  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
+```
+
+This predicate means exactly that `q` is a prime divisor of `n` outside the
+finite reference set `S`.
+
+## Theorems Added
+
+```lean
+theorem prime_dvd_product_add_coprime_not_mem
+    {S : Finset ℕ} {u q : ℕ}
+    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
+    (hqPrime : Nat.Prime q)
+    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
+    q ∉ S
+```
+
+```lean
+theorem exists_fresh_prime_factor
+    {S : Finset ℕ} {u : ℕ}
+    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
+    (hboundary : 1 < (∏ p ∈ S, p) + u) :
+    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
+```
+
+The requested names and binder shapes were retained.
+
+## Imports
+
+The implementation uses narrow imports:
+
+```lean
+import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
+import Mathlib.Data.Nat.Prime.Basic
+```
+
+No unfinished DkMath sample or prohibited primitive-factor, Petal, Zsigmondy,
+KUS, Units, CosmicCompletion, or Demo module is imported.
+
+## Exact Mathlib Declarations Reused
+
+- `Finset.dvd_prod_of_mem (f) (ha : a ∈ s) :
+  f a ∣ ∏ i ∈ s, f i`
+- `Nat.dvd_add_iff_right (h : k ∣ m) :
+  k ∣ n ↔ k ∣ m + n`
+- `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n`
+- `Nat.Coprime`, definitionally supplying `Nat.gcd m n = 1`
+- `Nat.Prime.not_dvd_one : Nat.Prime q → ¬ q ∣ 1`
+- `Nat.ne_one_iff_exists_prime_dvd :
+  n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n`
+- `Nat.ne_of_gt : 1 < n → n ≠ 1`
+
+## Actual Proof Route
+
+For the kernel theorem, assume `q ∈ S`. Product membership gives
+`q ∣ ∏ p ∈ S, p`. The reverse direction of `Nat.dvd_add_iff_right` removes
+that known addend from the boundary divisibility and yields `q ∣ u`.
+`Nat.dvd_gcd` then makes `q` divide the gcd. Coprimality rewrites the gcd to
+`1`, contradicting `Nat.Prime.not_dvd_one`.
+
+For existence, `hboundary` gives boundary `≠ 1`.
+`Nat.ne_one_iff_exists_prime_dvd` supplies `q`, its primality, and its boundary
+divisibility. The kernel theorem supplies `q ∉ S`, completing
+`FreshPrimeFactor`.
+
+The proof remains entirely in `ℕ`; no subtraction or integer bridge is used.
+
+## Assumption Audit
+
+The theorem surface contains only the required assumptions:
+
+- `Nat.Coprime (∏ p ∈ S, p) u` for exclusion;
+- `Nat.Prime q` and boundary divisibility for a supplied witness;
+- `1 < (∏ p ∈ S, p) + u` only for prime-divisor existence.
+
+It does not assume:
+
+- every member of `S` is prime;
+- `S.Nonempty`;
+- `0 < u`;
+- `0 < ∏ p ∈ S, p`.
+
+These assumptions are mathematically unnecessary for this exact facade.
+
+## Verification
+
+Focused build:
+
+```text
+$ lake build DkMath.Hackathon.FinitePrimeEscape
+✔ [726/726] Built DkMath.Hackathon.FinitePrimeEscape
+Build completed successfully (726 jobs).
+```
+
+The first build exposed the exact orientation of
+`Nat.dvd_add_iff_right`: the proof needed `.mpr`, not `.mp`. After correcting
+that elaboration issue, the focused build passed.
+
+No-sorry check:
+
+```text
+rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
+  DkMath/Hackathon/FinitePrimeEscape.lean
+```
+
+Result: no matches.
+
+Repository checks:
+
+```text
+git diff --check
+```
+
+Result: passed with no output.
+
+`git status --short` was inspected. The only new checkpoint changes are the
+permitted source, report, and implementation-confirmed map correction; the
+accepted `hack-001` documentation changes were already present.
+
+## Mathematical Meaning
+
+A prime factor of the completed boundary cannot be one of the numbers already
+multiplied into `P` when `P` is coprime to the offset. If the boundary is
+greater than one, at least one such fresh prime factor exists.
+
+## Meaning Boundary
+
+The result proves finite-set freshness only. It does not assert:
+
+- sequence-relative primitive-divisor status;
+- uniqueness of the fresh prime factor;
+- that every outside prime divides the boundary;
+- infinitude of primes;
+- any Cosmic Formula, projection, DkReal, or geometric statement.
+
+## First Genuine Obstruction
+
+```text
+none
+```
+
+The initial `.mp`/`.mpr` mismatch was a local API-orientation repair, not a
+mathematical obstruction.
+
+## Next Permitted Action
+
+```text
+Wise Wolf review of checkpoint hack-002.
+```
+
+## Stop Confirmation
+
+```text
+The checkpoint stopped after the finite-prime facade and report.
+No Cosmic Formula implementation was begun.
+No demo, projection, DkReal, visualization, or hack-003 work was begun.
+```
````
`````
