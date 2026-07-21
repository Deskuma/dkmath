# Git diff / Report / Review

## hack: cp-001

gch: 9a45b602502aed8cc20c57ce3251984d57756446

## Report

Checkpoint `hack-001` is complete.

Updated only:

- [EXISTING_DKMATH_MAP.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md)
- [report-hack-001.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-001.md)

Key finding: the smallest missing MVP result is the Coprime-based supplied-divisor exclusion theorem. The proof route remains entirely in `ℕ`, using existing Mathlib product, divisibility, gcd, and prime-factor APIs.

The Cosmic square identity should be a thin local `ring` theorem rather than importing the broad unfinished sample module. Projection inverse mapping and DkReal width transport remain genuinely missing later bridges.

Verification completed:

- All `MAP-001` through `MAP-047` identifiers preserved.
- `git diff --check` passes.
- No Lean source was edited.
- No Lean build was run, as required.
- No later checkpoint work was begun.

Next permitted action: Wise Wolf review of checkpoint `hack-001`.

## Review

# hack-001 状況分析・レビュー

## 判定

**ACCEPT — checkpoint `hack-001` を受理。**

監査目的、編集境界、停止条件のすべてを満たしておる。Lean 実装へ踏み込まず、`EXISTING_DKMATH_MAP.md` と `report-hack-001.md` だけを更新して停止した。次は予定どおり `hack-002` へ進める。

## 状況分析

### Core — 未知の探索空間が、一本の証明路へ圧縮された

最大の成果は、有限素数脱出の証明が完全に `ℕ` 内で閉じると確定したことじゃ。

```text
q ∈ S
→ q ∣ ∏ p ∈ S, p
→ q ∣ P
→ q ∣ P + u
→ q ∣ u
→ q ∣ gcd(P, u)
→ q ∣ 1
→ contradiction
```

使用候補も具体化された。

```lean
Finset.dvd_prod_of_mem
dvd_add_right
Nat.dvd_gcd
Nat.coprime_iff_gcd_eq_one
Nat.Prime.not_dvd_one
Nat.ne_one_iff_exists_prime_dvd
```

`Nat.sub` も `ℤ` への持ち上げも不要である。これはかなり良い。最初の実装は、型変換や切断減算に邪魔されず、数学本体だけを書ける。

### True Beam — 本当に欠けていた定理が小さい

監査で確定した最小の欠損は、次の一件だけじゃ。

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

つまり、既存ライブラリに巨大な構造欠損があったのではない。

```text
既存 Mathlib API
+
小さな Coprime 合成補題
=
有限 prime escape
```

という状態じゃ。これは hackathon に理想的である。Codex の仕事が、巨大な新理論の建設ではなく、既存資産を正しく結ぶ**検証可能な橋渡し**になる。

### 発見 — `S` の全要素が素数である必要はない

監査で最も数学的に面白い点はここじゃ。

supplied-divisor exclusion そのものには、

```lean
∀ p ∈ S, Nat.Prime p
```

が不要である。

必要なのは、

```text
q ∈ S
q is prime
q divides product(S) + u
Coprime product(S) u
```

だけである。

したがって核心定理は、実は「有限素数集合」より少し強い。

> 任意の有限参照集合 `S` に対して、その積と互いに素な offset を加えた境界の素因子は、`S` に属さない。

`S` が素数集合であることは、**有限 prime universe という物語を成立させる意味条件**であって、除外証明の論理条件ではない。報告書の assumption audit は、この分離を正しく捉えている。

これは契約違反ではない。要求定理を弱めたのではなく、不要仮定を除いて強化した結果じゃ。

### Cosmic Formula — 深い API を無理に通さない判断は正しい

既存 DkMath には、

```lean
DkMath.CosmicFormulaBinom.big_is_body_and_gap
```

および `CoreBeamGap.big_eq_body_add_gap` があり、一般の Big / Body / Gap 構造は存在する。

しかし公開 MVP に必要なのは、単純な自然数恒等式である。

```lean
P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

これを unfinished な `DkMath.Samples.Prime.B` から輸入せず、`CosmicCompletion.lean` に局所的な `ring` 定理として置くという判断は正しい。

これは DkMath を無視したのではない。

```text
深層 DkMath:
  一般構造の意味を保証する

Hackathon facade:
  Judge に見せる最短の安定 API を提供する
```

という役割分担じゃ。

### Projection / DkReal — 後段の障害も正しく分離された

監査は stretch layer へ実装侵入せず、入口と欠損だけを特定した。

既存 DkReal には、

```text
GapInterval
nested intervals
width
width → 0
ofRat
interval membership
```

が存在する。

一方で欠けているのは、

```text
fractional-linear inverse による interval map
endpoint ordering
membership transport
inverse-mapped width control
width < 1 の packaged integer uniqueness
```

である。

つまり DkReal 自体が足りないのではない。

> 射影の逆写像を既存 `GapInterval` へ作用させる橋がない。

ここまで障害を具体化できたので、後の `hack-007` は無秩序な実数探索にならぬ。

## 文書構造レビュー

`EXISTING_DKMATH_MAP.md` が約 2000 行から約 394 行へ縮んだのは、削りすぎではなく**監査成功の証拠**じゃ。

監査前は、

```text
問い
検索候補
確認事項
判断基準
```

の一覧だった。

監査後は、

```text
確定 API
拒否した近似定理
欠けている定理
依存コスト
次の実装面
```

へ置き換わった。

先ほど心配していた「巨大文書で頭脳がパンクする」問題に対して、Codex 自身が正しい圧縮を行ったことになる。

```text
2000-line audit questionnaire
→ 394-line verified repository map
```

これは今後の理想的な文書遷移モデルじゃ。

## 軽微な留意点

外側のレビュー・パッケージ見出しが `cp-001`、本文が `hack-001` となっている。リポジトリ内の正式識別子は `hack-001` なので、以後はこれに統一する。

また、監査で unsigned projection が DkReal に適合しやすいと推薦されたが、これはまだ ADR の正式決定ではない。`hack-002` では一切触れず、MVP 完成後に決定する。

## 次 checkpoint の焦点

`hack-002` は三宣言だけでよい。

```text
1 definition
  FreshPrimeFactor

1 kernel theorem
  prime_dvd_product_add_coprime_not_mem

1 existence corollary
  exists_fresh_prime_factor
```

不要なものは次のとおり。

```text
S の全要素が prime という仮定
S.Nonempty
0 < u
0 < P
Cosmic Formula
Demo constants
Projection
DkReal
Primitive divisor APIs
```

ここで重要なのは、`DkMath.Samples.Prime.B` の `sorry` theorem を import して埋めることではない。

そのサンプルは proof precedent として読むだけに留め、Mathlib の完成済み API から独立した no-sorry theorem を構築する。

# 次の Codex Instructions

````md
# Checkpoint hack-002 — Finite Prime Escape

## Session Class

```text
IMPLEMENTATION
```

## Primary Goal

Implement the minimal `Nat` facade for finite-set prime escape.

Add exactly:

1. a local `FreshPrimeFactor` predicate;
2. the supplied-prime-divisor exclusion theorem;
3. the fresh-prime-factor existence corollary.

Do not begin Cosmic Formula, demo, projection, DkReal, or visualization work.

## Required Reading

Read the stable project documents according to `CODEX_PLAN.md`, then read:

```text
EXISTING_DKMATH_MAP.md
report-hack-001.md
this instruction
```

Use the accepted `hack-001` audit as the repository map.

Do not repeat the broad repository audit.

## Permitted Edit Files

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean

lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-002.md
```

You may correct an implementation-confirmed declaration name or type in:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  EXISTING_DKMATH_MAP.md
```

only when Lean demonstrates that the audited entry was inaccurate.

No other file is editable.

## Required Declaration Surface

Implement a definition equivalent to:

```lean
/-- A prime divisor of `n` outside the finite reference set `S`. -/
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

Implement the kernel theorem:

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

Implement the existence corollary:

```lean
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hboundary : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
```

Equivalent theorem names or binder normalization require a clear reason in the report.

Do not add `∀ p ∈ S, Nat.Prime p`, `S.Nonempty`, `0 < u`, or `0 < P`; the audit established that they are logically unnecessary for this theorem surface.

## Intended Proof Route

Use the accepted `Nat` route:

```text
q ∈ S
→ Finset.dvd_prod_of_mem
→ q divides the product

q divides the product
and
q divides product + u
→ dvd_add_right
→ q divides u

q divides both numbers
→ Nat.dvd_gcd

Nat.Coprime
→ gcd = 1

Nat.Prime q
→ q does not divide 1
→ contradiction
```

For existence:

```text
1 < product + u
→ product + u ≠ 1
→ Nat.ne_one_iff_exists_prime_dvd
→ supplied-divisor exclusion
→ FreshPrimeFactor
```

You may use a cleaner completed Mathlib theorem if it is semantically identical, but do not import an unfinished sample theorem.

## Dependency Restrictions

Do not import:

```text
DkMath.Samples.Prime.B
DkMath.NumberTheory.PrimitiveSet.*
DkMath.Petal.*
DkMath.Zsigmondy.*
DkMath.KUS.*
DkMath.Units.*
DkMath.Hackathon.CosmicCompletion
DkMath.Hackathon.Demo
```

Use narrow Mathlib imports when straightforward.

`import Mathlib` is acceptable for this checkpoint if narrowing imports would consume disproportionate effort. Record the choice.

## Stages

### Stage A — Confirm the immediate APIs

Confirm the exact Lean signatures of:

```lean
Finset.dvd_prod_of_mem
dvd_add_right
Nat.dvd_gcd
Nat.coprime_iff_gcd_eq_one
Nat.Prime.not_dvd_one
Nat.ne_one_iff_exists_prime_dvd
```

Do not reopen the broad audit.

### Stage B — Implement the kernel theorem

Implement and build:

```lean
prime_dvd_product_add_coprime_not_mem
```

Repair local theorem-name, binder, or elaboration issues within this checkpoint.

### Stage C — Implement freshness and existence

Add `FreshPrimeFactor` and prove:

```lean
exists_fresh_prime_factor
```

Keep the public surface minimal.

Do not add optional universal wrappers unless a concrete caller requires one.

### Stage D — Verify

Run from `lean/dk_math`:

```bash
lake build DkMath.Hackathon.FinitePrimeEscape
```

Then run:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
  DkMath/Hackathon/FinitePrimeEscape.lean

git diff --check
git status --short
```

Inspect the final diff.

### Stage E — Report and Stop

Write:

```text
docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-002.md
```

The report must include:

```text
status
files changed
definitions added
theorems added
exact Mathlib declarations reused
actual proof route
assumption audit
build commands and results
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
FreshPrimeFactor is defined.

prime_dvd_product_add_coprime_not_mem builds.

exists_fresh_prime_factor builds.

No unnecessary prime-set or positivity hypotheses were added.

No unfinished or sample theorem is imported.

Only permitted files changed.

The focused build passes.

The report is complete.
```

## Stopping Rule

Stop and report the smallest exact obstruction if:

```text
the audited Mathlib route has an incompatible theorem signature;

the target requires an additional mathematical hypothesis;

the theorem cannot remain entirely in Nat;

a permitted import creates an unexpected dependency problem.
```

Do not respond to an obstruction by:

```text
adding sorry;
adding an axiom;
weakening the theorem;
adding unreviewed assumptions;
editing CosmicCompletion.lean;
editing Demo.lean;
opening projection or DkReal work.
```

## Final Instruction

Complete `hack-002`, write `report-hack-002.md`, and stop.

Do not begin `hack-003`.
````

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
index 163fc8df..c9c66fba 100644
--- a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md
@@ -2,2000 +2,394 @@

 ## DkMath — Cosmic Formula Inversion

-This document records the existing DkMath and Mathlib declarations that may support the hackathon theorem surface.
-
-Its purpose is to prevent:
-
-- duplicate definitions;
-- duplicate proofs;
-- unnecessary imports;
-- incorrect theorem reuse;
-- parallel Big / Body / Gap structures;
-- avoidable Codex exploration in later checkpoints.
-
-This file begins as an audit framework.
-
-The first Codex session must update it with exact module paths, declaration names, theorem statements, and reuse classifications.
-
-Codex must not edit Lean source files during that audit.
-
----
-
 ## 1. Current Status

 ```text
-DOCUMENT STATUS:
-  PRE-AUDIT SCAFFOLD
-
-LEAN SOURCE AUDIT:
-  NOT STARTED
-
-CURRENT AUTHORITY:
-  MATHEMATICAL_CONTRACT.md
-  ARCHITECTURE.md
-  DECISIONS.md
-  RISKS_AND_STOPPING_RULES.md
-
-NEXT REQUIRED ACTION:
-  repository-audit-only Codex session
-```
-
-No declaration listed as a candidate in this document is considered reusable until its exact type has been inspected.
-
----
-
-## 2. Audit Objective
-
-The audit must determine the smallest existing theorem path for:
-
-```text
-finite prime set S
-→ product P
-→ Coprime P u
-→ prime divisor q of P + u
-→ q ∉ S
-→ fresh prime-factor existence
-→ Cosmic Formula completion
-→ concrete Demo.lean
+DOCUMENT STATUS: AUDITED AT hack-001
+LEAN SOURCE AUDIT: COMPLETED
+SOURCE EDITS: NONE
+FINAL RECOMMENDATION: a thin Nat facade over Mathlib, with a local ring identity
 ```

-The stronger audit should also locate candidate APIs for:
+The audit distinguishes finite-set freshness from sequence-relative primitive
+divisors. `Finset ℕ` is sufficient; no new finite-prime-universe structure is
+needed.

-```text
-bounded rational projection
-exact inverse
-normalized Body / Gap conservation
-DkReal nested intervals
-interval-width transport
-unique integer candidate
-```
+## 2. Audit Objective and Confirmed Core Route

-The audit must distinguish:
+| Role | Module | Declaration and normalized type | Class | Cost |
+|---|---|---|---|---|
+| member divides product | `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` | `Finset.dvd_prod_of_mem (f) (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i` | DIRECT | narrow through Mathlib |
+| remove known addend | `Mathlib.Algebra.Ring.Divisibility.Basic` | `dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c` | DIRECT | narrow |
+| coprime means gcd one | Mathlib Nat gcd | `Nat.coprime_iff_gcd_eq_one : Nat.Coprime a b ↔ Nat.gcd a b = 1` | DIRECT | narrow |
+| common divisor divides gcd | Mathlib Nat gcd | `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n` | DIRECT | narrow |
+| prime cannot divide one | Mathlib Nat prime | `Nat.Prime.not_dvd_one : Nat.Prime q → ¬ q ∣ 1` | DIRECT | narrow |
+| prime divisor exists | `Mathlib.Data.Nat.Prime.Basic` | `Nat.ne_one_iff_exists_prime_dvd : n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n` | DIRECT | narrow |

-```text
-what already exists
-what only needs a wrapper
-what requires a small corollary
-what requires a genuine bridge
-what is absent
-what is semantically unsuitable
-```
+Shortest exclusion route, entirely in `ℕ`: from `q ∈ S`, use
+`Finset.dvd_prod_of_mem id` to obtain `q ∣ P`; combine that with
+`q ∣ P + u` via `dvd_add_right` to get `q ∣ u`; then `Nat.dvd_gcd`,
+`Nat.coprime_iff_gcd_eq_one`, and `Nat.Prime.not_dvd_one` contradict
+primality. No subtraction or `ℤ` bridge is required.

----
+`DkMath.Samples.Prime.B` contains
+`exists_prime_not_mem_dvd_prod_add_unit` with assumptions `0 < u`, every
+member prime, and every member not dividing `u`. It is a useful near match but
+not the requested Coprime API. The Coprime variant in that file,
+`exists_prime_not_mem_dvd_prod_add_unit_of_coprime'`, contains `sorry`, so it
+is rejected as a dependency.

 ## 3. Reuse Classification

-Every audited declaration must receive exactly one primary classification.
-
-### `DIRECT`
-
-Use the existing declaration without a new theorem.
-
-```text
-Meaning:
-  exact required statement already exists
-
-Expected action:
-  import and apply directly
-```
-
-### `WRAPPER`
-
-Expose an existing declaration under a stable hackathon-facing theorem name.
-
-```text
-Meaning:
-  mathematical content already exists
-  public theorem surface needs a clearer specialization or name
-
-Expected action:
-  add a thin theorem wrapper
-```
-
-### `COROLLARY`
-
-Derive the requested result through a small amount of local reasoning.
-
-```text
-Meaning:
-  all substantial mathematics already exists
-
-Expected action:
-  prove a short theorem from existing declarations
-```
-
-### `BRIDGE`
-
-Translate between two existing representations or APIs.
-
-```text
-Examples:
-  Finset product ↔ existing product wrapper
-  Nat identity ↔ existing Cosmic Formula structure
-  rational projection ↔ DkReal interval representation
-```
-
-### `MISSING`
-
-No suitable existing declaration was found.
-
-```text
-Expected action:
-  state the smallest proposed missing theorem
-  do not implement it during the audit
-```
-
-### `REJECTED`
-
-A related declaration exists but does not match the contract.
-
-```text
-Examples:
-  primitive prime divisor instead of finite-set freshness
-  incompatible number domain
-  sequence-relative result
-  theorem with materially different hypotheses
-```
-
-### `DANGEROUS`
-
-The declaration is mathematically relevant but architecturally unsuitable.
-
-```text
-Examples:
-  creates reverse dependency
-  imports a very large unrelated branch
-  depends on unverified experimental infrastructure
-  would force a core DkMath refactor
-```
-
-### `DEMO_ONLY`
-
-A concrete fact should be proved locally with automation.
-
-```text
-Examples:
-  221 = 13 * 17
-  Nat.Coprime 210 11
-  13 ∉ {2, 3, 5, 7}
-```
-
----
+The primary labels used below retain the project meanings: `DIRECT`,
+`WRAPPER`, `COROLLARY`, `BRIDGE`, `MISSING`, `REJECTED`, `DANGEROUS`, and
+`DEMO_ONLY`.

 ## 4. Audit Record Format

-Each confirmed declaration should be recorded in this form.
-
-````md
-### MAP-XXX — Concept Name
-
-```text
-Status:
-  CONFIRMED / PARTIAL / NOT FOUND / REJECTED
-
-Classification:
-  DIRECT / WRAPPER / COROLLARY / BRIDGE / MISSING / REJECTED / DANGEROUS
-
-Module:
-  DkMath.Example.Module
-
-Declaration:
-  exactDeclarationName
-
-Domain:
-  ℕ / ℤ / ℚ / ℝ / DkReal / generic
-
-Exact Type:
-  copied or accurately normalized theorem statement
-
-Required Hypotheses:
-  list
-
-Produced Conclusion:
-  list
-
-Intended Hackathon Use:
-  description
-
-Import Cost:
-  narrow / moderate / broad
-
-Dependency Risk:
-  none / low / medium / high
-
-Notes:
-  semantic boundary, coercion issue, or proof strategy
-
-Decision:
-  use directly / wrap / derive / reject / defer
-```
-````
-
-Exact theorem types should be copied accurately enough that a later Codex checkpoint does not need to repeat the same search.
-
----
+Each MAP entry records a status/classification, exact declaration where one
+exists, hypotheses or semantic boundary, and the reuse decision.

 ## 5. Search Sources

-The repository audit should use sources in this order.
-
-```text
-1. exact theorem-name and concept search in Lean source
-2. __theorems-heading.txt
-3. __dkmath-all.lean.txt.gz through zgrep / zcat
-4. summary reports in __summary_report_data.tar.gz
-5. direct module inspection
-6. Mathlib source inspection when DkMath has no suitable theorem
-```
-
-The audit should read the project-level repository instructions before searching:
-
-```text
-README.md
-AGENT.md
-SUMMARY.md
-```
-
-UUID-named empty tracking anchors must not be repeatedly inspected.
-
----
+Direct source, theorem index, compressed source database, summary archive,
+candidate modules, and Mathlib source were checked in the prescribed order.

 ## 6. Search Rules

-Codex must search by both standard mathematics vocabulary and DkMath vocabulary.
-
-Example:
-
-```text
-standard search:
-  prime divisor
-  Finset product
-  Coprime
-  not_mem
-  exists_prime_and_dvd
-  interval width
-  injective
-  left inverse
-
-DkMath search:
-  Big
-  Body
-  Gap
-  GN
-  CosmicFormula
-  Projection
-  DkReal
-  GapInterval
-  NoLift
-  primitive
-  fresh
-```
-
-A name match is not sufficient.
-
-Codex must inspect:
-
-```text
-domain
-hypotheses
-conclusion
-namespace
-import path
-dependency direction
-```
-
----
+Both standard mathematical vocabulary and DkMath vocabulary were searched;
+no declaration was accepted from its name alone.

 ## 7. Required Discrete Arithmetic Map

 ### MAP-001 — Finite Prime Set Representation

-```text
-Audit Status:
-  TO AUDIT
-
-Required Concept:
-  S : Finset ℕ
-
-Required Hypothesis:
-  ∀ p ∈ S, Nat.Prime p
-
-Expected Source:
-  Mathlib Finset and Nat.Prime APIs
-  possible DkMath finite-prime wrappers
-
-Questions:
-  Is there an existing DkMath structure for a finite prime family?
-  Is a plain Finset sufficient?
-  Would an existing wrapper increase import or coercion cost?
-  Does a reusable theorem already expect a Finset of primes?
-
-Preferred Outcome:
-  use Finset ℕ directly unless a clearly superior existing API exists
-
-Prohibited Outcome:
-  create a new foundational finite-prime-set structure only for the demo
-```
-
----
+CONFIRMED / DIRECT. Use `S : Finset ℕ` and, only where the public contract
+needs it, `∀ p ∈ S, Nat.Prime p`. A wrapper structure adds no value.

 ### MAP-002 — Finset Product of Prime Members

-```text
-Audit Status:
-  TO AUDIT
-
-Required Expression:
-  ∏ p ∈ S, p
-
-Required Fact:
-  q ∈ S → q ∣ ∏ p ∈ S, p
-
-Likely Source:
-  Mathlib Finset product divisibility
-
-Search Terms:
-  Finset.dvd_prod_of_mem
-  dvd_prod
-  mem.*dvd.*prod
-  prime_mem_dvd_product
-
-Questions:
-  What exact binder form is most compatible?
-  Is the product written as S.prod id?
-  Is a two-binder product unnecessarily duplicating the same set?
-  Does DkMath already expose a specialized theorem?
-
-Preferred Classification:
-  DIRECT or WRAPPER
-```
-
----
+CONFIRMED / DIRECT. Use `P := ∏ p ∈ S, p` and
+`Finset.dvd_prod_of_mem (fun p => p) hqMem`.

 ### MAP-003 — Product Positivity

-```text
-Audit Status:
-  TO AUDIT
-
-Potential Requirement:
-  0 < P
-
-Possible Derivation:
-  all primes in S are positive
-  finite product of positive values is positive
-
-Questions:
-  Is positivity required by the arithmetic theorem?
-  Is it only required by projection or visualization?
-  Does empty S already give P = 1 and positivity automatically?
-
-Preferred Outcome:
-  do not add nonempty S if product positivity already holds for the empty product
-```
-
----
+CONFIRMED / COROLLARY. It is not needed for divisor exclusion. If needed,
+primality gives nonzero factors and `Finset.prod_ne_zero_iff`; the empty
+product is already `1`, so `S.Nonempty` is unnecessary.

 ### MAP-004 — Coprimality API

-```text
-Audit Status:
-  TO AUDIT
-
-Required Concept:
-  Nat.Coprime P u
-
-Equivalent Form:
-  Nat.gcd P u = 1
-
-Likely Source:
-  Mathlib Nat gcd / Coprime APIs
-  possible DkMath coprime-product bridges
-
-Search Terms:
-  Nat.Coprime
-  coprime_prod
-  gcd_eq_one
-  dvd_gcd
-  Coprime.dvd_of_dvd_mul_left
-  Coprime.not_dvd_of_dvd
-
-Questions:
-  Which theorem most directly excludes q dividing both P and u?
-  Is there an existing DkMath theorem for a product coprime to an offset?
-  Is the project better stated through Nat.Coprime rather than gcd equality?
-
-Preferred Outcome:
-  public theorem uses Nat.Coprime
-```
-
----
+CONFIRMED / DIRECT. Public statements should use `Nat.Coprime P u`; the
+exclusion proof may rewrite with `Nat.coprime_iff_gcd_eq_one`.

 ### MAP-005 — Divisor of `P + u` and `P` Divides `u`

-```text
-Audit Status:
-  TO AUDIT
-
-Required Local Fact:
-  q ∣ P
-  q ∣ P + u
-  → q ∣ u
-
-Possible Proof Routes:
-  Nat.dvd_add_iff_left
-  Nat.dvd_add_right
-  modular congruence
-  integer subtraction bridge
-  exact divisibility algebra
-
-Search Terms:
-  dvd_add_iff
-  dvd_add_iff_left
-  dvd_add_iff_right
-  dvd_sub
-  add_sub_cancel_left
-  Nat.ModEq
-
-Questions:
-  Can this remain entirely in Nat without truncated subtraction?
-  Is a ModEq proof cleaner?
-  Is there already a DkMath bridge theorem?
-
-Preferred Classification:
-  DIRECT or COROLLARY
-
-Avoid:
-  unnecessary conversion to Int unless Nat APIs are genuinely awkward
-```
-
----
+CONFIRMED / DIRECT. `dvd_add_right hqP` turns `q ∣ P + u` into `q ∣ u`.
+This is cleaner than the `Nat.dvd_sub` route used in the older sample.

 ### MAP-006 — Coprimality Excludes a Prime Dividing Both Inputs

-```text
-Audit Status:
-  TO AUDIT
-
-Required Fact:
-  Nat.Coprime P u
-  q ∣ P
-  q ∣ u
-  Nat.Prime q
-  → False
-
-Equivalent Routes:
-  q ∣ gcd P u
-  gcd P u = 1
-  prime q cannot divide 1
-
-Search Terms:
-  Coprime
-  dvd_gcd
-  Prime.not_dvd_one
-  Nat.dvd_one
-  coprime_iff_gcd_eq_one
-
-Preferred Classification:
-  DIRECT or COROLLARY
-```
-
----
+CONFIRMED / COROLLARY. `Nat.dvd_gcd hqP hqu`, the gcd-one form of
+coprimality, and `hqPrime.not_dvd_one` close the contradiction.

 ### MAP-007 — Supplied Prime Divisor Is Fresh

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem Meaning:
-  q is prime
-  q ∣ P + u
-  P = product S
-  Coprime P u
-  → q ∉ S
-
-Target Module:
-  DkMath.Hackathon.FinitePrimeEscape
-
-Potential Existing DkMath Areas:
-  finite prime products
-  Euclid-style prime escape
-  primitive-set APIs
-  BezoutBridge
-  coprime product theorems
-
-Search Terms:
-  forall_not_dvd
-  coprime_prod_primes
-  not_mem.*prime.*dvd
-  freshPrime
-  FreshPrimeFactor
-  prime_dvd_add
-  product_add
-  Euclid
-  escape
-
-Classification Goal:
-  DIRECT, WRAPPER, or COROLLARY
-
-If Missing:
-  proposed theorem should remain small and Nat-specific
+NOT FOUND AFTER SEARCH / MISSING. No completed exact theorem with
+`Nat.Coprime (∏ p ∈ S, p) u` and a supplied divisor was found. Proposed shape:
+
+```lean
+theorem prime_dvd_product_add_coprime_not_mem
+    {S : Finset ℕ} {u q : ℕ}
+    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
+    (hqPrime : Nat.Prime q)
+    (hqDiv : q ∣ (∏ p ∈ S, p) + u) : q ∉ S
 ```

----
+Notably, `∀ p ∈ S, Nat.Prime p` is not logically required for exclusion.

 ### MAP-008 — Existence of a Prime Divisor

-```text
-Audit Status:
-  TO AUDIT
-
-Required Fact:
-  1 < n → ∃ q, Nat.Prime q ∧ q ∣ n
-
-Likely Source:
-  Mathlib Nat prime-divisor API
-
-Search Terms:
-  exists_prime_and_dvd
-  exists_prime_dvd
-  minFac
-  prime_minFac
-  prime_dvd_iff
-
-Questions:
-  What is the shortest proposition-valued existence theorem?
-  Does it require n ≠ 1 rather than 1 < n?
-  Does it expose an explicit minFac witness?
-  Is classical reasoning involved?
-
-Preferred Classification:
-  DIRECT
-```
-
----
+CONFIRMED / DIRECT. From `1 < n`, derive `n ≠ 1`, then apply
+`Nat.ne_one_iff_exists_prime_dvd`. This exact theorem supplies the witness.

 ### MAP-009 — Existence of a Fresh Prime Factor

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem:
-  1 < P + u
-  Nat.Coprime P u
-  P = product S
-  all members of S prime
-  →
-  ∃ q, Nat.Prime q ∧ q ∣ P + u ∧ q ∉ S
-
-Expected Construction:
-  prime-divisor existence
-  +
-  supplied-divisor freshness
-
-Preferred Classification:
-  COROLLARY or WRAPPER
-
-Questions:
-  Is primality of every member of S logically required for exclusion?
-  Is it required only to justify the phrase finite prime set?
-  Can a stronger theorem exclude every member q of S when each q > 1?
-```
-
----
+PARTIAL / COROLLARY. Compose MAP-008 and MAP-007. Neither `S.Nonempty`,
+`0 < u`, nor `0 < P` is needed once `1 < P + u` is assumed.

 ### MAP-010 — Universal Freshness of All Prime Divisors

-```text
-Audit Status:
-  TO AUDIT
-
-Required Meaning:
-  ∀ q, Nat.Prime q → q ∣ P + u → q ∉ S
-
-Expected Use:
-  prove both 13 and 17 fresh through one general API
-
-Preferred Classification:
-  WRAPPER or COROLLARY
-
-Meaning Boundary:
-  does not state uniqueness
-  does not state every outside prime divides P + u
-```
-
----
+PARTIAL / WRAPPER. This is the universal closure of MAP-007 and needs no new
+mathematics.

 ## 8. Freshness and Primitive-Factor Map

 ### MAP-011 — Existing `FreshPrimeFactor` Predicate

-```text
-Audit Status:
-  TO AUDIT
-
-Required Predicate Meaning:
-  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
-
-Search Terms:
-  FreshPrimeFactor
-  freshPrime
-  outsidePrime
-  prime_not_mem
-  newPrimeFactor
-
-Questions:
-  Does an exact predicate already exist?
-  Is it specialized to a sequence or primitive divisor?
-  Does it use Set rather than Finset?
-  Does it include multiplicity or valuation data?
-
-Decision Rule:
-  use an existing predicate only if its semantics match exactly
-
-If Not Found:
-  a small hackathon-local predicate may be proposed
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING. Searches covered direct source,
+`__theorems-heading.txt`, and the compressed source database. Proposed local
+predicate: `Nat.Prime q ∧ q ∣ n ∧ q ∉ S`.

 ### MAP-012 — Primitive Prime Divisor APIs

-```text
-Audit Status:
-  TO AUDIT FOR REJECTION OR OPTIONAL REUSE
-
-Potential DkMath Areas:
-  PrimitiveSet
-  Petal
-  BezoutBridge
-  ErdosBridge
-  Zsigmondy-related modules
-  primitive-factor APIs
-
-Purpose of Audit:
-  determine whether any theorem specializes cleanly to finite-set freshness
-
-Required Caution:
-  sequence-relative primitiveness is stronger and semantically different
-
-Likely Classification:
-  REJECTED for public terminology
-  possibly DIRECT or COROLLARY for an internal proof only if exact hypotheses align
-
-Prohibited Action:
-  rename the finite escape theorem as primitive merely because a primitive API is reused
-```
-
----
+REJECTED. `DkMath.NumberTheory.PrimitiveSet.PrimitiveOn` is a divisibility
+antichain, while `PrimitivePrimeFactorOfDiffPow`, Petal/Zsigmondy bridges, and
+`PrimitivePrimeDivisor` are sequence/exponent-relative. None means finite-set
+freshness; their broad imports and hypotheses are also unsuitable.

 ### MAP-013 — Finite Prime Universe Existing Structure

-```text
-Audit Status:
-  TO AUDIT
-
-Required Decision:
-  documentation-only term
-  or existing formal DkMath object
-
-Search Terms:
-  PrimeUniverse
-  FinitePrimeUniverse
-  PrimeWorld
-  PrimitiveSet
-  PrimeFamily
-  Finset prime product
-
-Preferred Outcome:
-  retain as project terminology unless an exact existing object is clearly useful
-
-Avoid:
-  introducing a formal universe structure for the MVP
-```
-
----
+NOT FOUND / REJECTED as unnecessary. `Finset ℕ` plus a prime-membership
+hypothesis is the correct MVP representation.

 ## 9. Cosmic Formula Map

 ### MAP-014 — Core Cosmic Formula Module Family

-```text
-Audit Status:
-  TO AUDIT
-
-Known Conceptual Target:
-  Big = Body + Gap
-
-Candidate Module Families:
-  DkMath.CosmicFormula.*
-  other DkMath algebraic split modules
-
-Search Terms:
-  CosmicFormula
-  Big
-  Body
-  Gap
-  body_add_gap
-  big_eq
-  CoreBeamGap
-  Residual
-  Split
-
-Required Audit Output:
-  exact module names
-  primary structures
-  number domains
-  relevant theorem names
-  import relationships
-```
-
----
+CONFIRMED. `DkMath.CosmicFormula.Defs` defines real-valued `Big`, `Body`, and
+`Gap`; `DkMath.CosmicFormulaBinom` defines generic `CommRing` versions and
+`big_is_body_and_gap`; `DkMath.CosmicFormula.CoreBeamGap` gives a generic
+`CommSemiring` decomposition through `BigN`, `BodyN`, and `Gap`.

 ### MAP-015 — Square Completion Identity

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem:
-  P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
-
-Search Terms:
-  square
-  add_sq
-  pow_two
-  cosmic
-  body gap
-  Gnomon
-  completion
-
-Preferred Reuse Order:
-  DIRECT existing theorem
-  WRAPPER specialization
-  COROLLARY from generic Cosmic Formula
-  local ring proof
-
-Acceptable Fallback:
-  theorem proved by ring
-
-Meaning Boundary:
-  arithmetic equality only
-  no formal Euclidean dissection required
-```
+PARTIAL / COROLLARY. `DkMath.Samples.Prime.B.cosmic_identity_ring` states the
+same polynomial as a subtraction-equals-zero theorem over `CommRing`, but the
+module imports all of `Mathlib` and contains unrelated unfinished declarations.
+For the Nat facade, the narrow and safe recommendation is a local theorem
+proved by `ring`:

----
+```lean
+P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
+```

 ### MAP-016 — Existing Big Definition

-```text
-Audit Status:
-  TO AUDIT
-
-Required Intended Value:
-  (P + u) ^ 2
-
-Questions:
-  Does DkMath define Big as a field of a structure?
-  Is Big generic over exponent d?
-  Is the square case directly available?
-  Is the domain Nat, Int, or a semiring?
-  Would reuse obscure the public theorem?
-
-Decision Possibilities:
-  DIRECT
-  WRAPPER
-  REJECTED for the facade while retaining the algebraic theorem
-```
-
----
+CONFIRMED / BRIDGE. `CosmicFormulaBinom.Big d x u = (x + u)^d` is generic;
+specialize `d = 2`. The public Nat equality need not expose this definition.

 ### MAP-017 — Existing Body Definition

-```text
-Audit Status:
-  TO AUDIT
-
-Required Intended Value:
-  P * (P + 2 * u)
-
-Questions:
-  Is Body represented as Big - Gap?
-  Is there a subtraction-free Nat theorem?
-  Does an existing generic power-difference Body specialize to d = 2?
-  Is GN used internally?
-
-Preferred Public Form:
-  additive equality in Nat
-```
-
----
+CONFIRMED / BRIDGE. `CosmicFormulaBinom.Body d x u = x * G d x u`; its square
+specialization normalizes to `x * (x + 2*u)`, but that normalization lacks the
+thin exact public theorem desired here.

 ### MAP-018 — Existing Gap Definition

-```text
-Audit Status:
-  TO AUDIT
-
-Required Intended Value:
-  u ^ 2
-
-Questions:
-  Is Gap generic as u ^ d?
-  Is there an existing UnitKernel or GapKernel?
-  Does the existing type require a structure wrapper?
-
-Meaning Boundary:
-  square Gap is not the normalized linear Gap coordinate
-```
-
----
+CONFIRMED / DIRECT. `CosmicFormulaBinom.Gap d u = u^d`; at `d = 2` it is the
+required square Gap.

 ### MAP-019 — Generic Exponent Cosmic Formula

-```text
-Audit Status:
-  TO AUDIT
-
-Potential Generic Identity:
-  (x + u) ^ d = Body_d(x, u) + u ^ d
-
-Potential DkMath Relation:
-  GN
-  binomial expansion
-  Body / Gap split
-  Gnomon band
-
-Purpose:
-  determine whether the square theorem should be a specialization
-
-Questions:
-  Does specialization to d = 2 simplify cleanly?
-  Would importing the generic theory materially expand the facade?
-  Is a local square theorem clearer for judges?
-
-Decision Rule:
-  prefer the cleanest sound public surface, not maximal abstraction
-```
-
----
+CONFIRMED / DIRECT. `DkMath.CosmicFormulaBinom.big_is_body_and_gap`:
+`Big d x u = Body d x u + Gap d u` over any `CommRing`.
+`CoreBeamGap.big_eq_body_add_gap` provides the subtraction-free
+`CommSemiring` analogue.

 ### MAP-020 — GN Identity

-```text
-Audit Status:
-  TO AUDIT
-
-Known Conceptual Identity:
-  (x + u) ^ d - u ^ d = x * GN_d(x, u)
-
-Potential Square Specialization:
-  GN_2(P, u) = P + 2u
-
-Possible Use:
-  bridge Body to existing GN machinery
-  show Body = P * GN_2(P, u)
-
-Questions:
-  Does an exact theorem already exist?
-  Is GN required by the MVP?
-  Does it improve the inverse-projection story?
-  Does it create an unnecessarily deep import?
-
-Likely Outcome:
-  optional COROLLARY or DEFERRED
-```
-
----
+PARTIAL / DEFERRED. `Body_eq_GZ`, `mul_G_eq_GZ`, and the generic binomial
+identity connect Body to the canonical kernel. GN/GZ naming and imports make
+this unnecessary for the public square facade; use it only in later bridges.

 ### MAP-021 — Gnomon / GnomonBand APIs

-```text
-Audit Status:
-  TO AUDIT
-
-Potential Concept:
-  (P + u)² - u² = P(P + 2u)
-
-Purpose:
-  visual interpretation of Body around Gap
-
-Questions:
-  Is a formal GnomonBand already implemented?
-  Is it stable enough for public reuse?
-  Is it only planned documentation?
-
-Preferred MVP Outcome:
-  arithmetic wrapper only
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING as a relevant stable public API. Arithmetic
+completion suffices; no geometry should be introduced.

 ## 10. Normalized Cosmic Formula Map

 ### MAP-022 — Existing Normalization API

-```text
-Audit Status:
-  TO AUDIT
-
-Required Identity:
-  P(P + 2u) / (P + u)²
-  +
-  u² / (P + u)²
-  =
-  1
-
-Preferred Domain:
-  ℚ
-
-Search Terms:
-  normalized
-  normalize
-  ratio
-  bodyRatio
-  gapRatio
-  unitInterval
-  conservation
-  div_sq
-
-Questions:
-  Does DkMath already normalize Big to one?
-  Which domain is used?
-  Is denominator positivity already packaged?
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING for the stated rational Body/Gap conservation.
+It is a small future rational corollary requiring a nonzero denominator.

 ### MAP-023 — Linear Gap Coordinate

-```text
-Audit Status:
-  TO AUDIT
-
-Candidate:
-  u / (P + u)
-
-Required Relation:
-  (u / (P + u))² = u² / (P + u)²
-
-Questions:
-  Does DkMath distinguish linear Gap scale and square Gap mass?
-  Is there an existing unit-coordinate abstraction?
-  Are Units or SilverRatio modules relevant, or unrelated?
-
-Decision:
-  do not reuse by name alone
-```
-
----
+NOT FOUND / MISSING. Existing Units/KUS uses different semantics.

 ### MAP-024 — Normalized Body

-```text
-Audit Status:
-  TO AUDIT
-
-Candidate:
-  P(P + 2u) / (P + u)²
-
-Alternative Identity:
-  1 - (u / (P + u))²
-
-Questions:
-  Which form is easiest to connect to existing DkMath APIs?
-  Does Nat-to-rational coercion already have wrappers?
-```
-
----
+NOT FOUND / MISSING. This should remain a later `ℚ` definition/corollary.

 ## 11. Projection Map

 ### MAP-025 — Existing Projection Definitions

-```text
-Audit Status:
-  TO AUDIT
-
-Candidate Unsigned Projection:
-  P / (P + u)
-
-Candidate Signed Projection:
-  -P / (P + u)
-
-Known Decision:
-  primary convention remains deferred until audit
-
-Search Terms:
-  Projection
-  inverseProjection
-  normalizedCoordinate
-  bounded
-  unitInterval
-  signed projection
-  DkReal projection
-
-Required Audit Output:
-  exact existing formulas
-  domains and codomains
-  endpoint conventions
-  inverse theorems
-  DkReal compatibility
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING. `DkMath.Samples.Projection` is a real-valued
+curvature/Body demo and does not define either `P/(P+u)` or `-P/(P+u)`.
+The CF2D inverse action is matrix/level-set semantics and is unrelated.

 ### MAP-026 — Unsigned Projection Interval Bound

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem:
-  0 ≤ P / (P + u) < 1
-
-Domain:
-  ℚ preferred
-
-Hypotheses:
-  P ≥ 0
-  u > 0
-
-Likely Source:
-  Mathlib ordered-field division lemmas
-  possible DkMath normalization API
-
-Classification Goal:
-  COROLLARY or BRIDGE
-```
-
----
+PARTIAL / COROLLARY from ordered-field division lemmas; no DkMath wrapper.
+Its image lies in `[0,1)` when `0 ≤ P` and `0 < u`.

 ### MAP-027 — Signed Projection Interval Bound

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem:
-  -1 < -P / (P + u) ≤ 0
-
-Purpose:
-  compare with existing DkMath inverse-projection conventions
-
-Classification:
-  AUDIT ONLY until ADR selects a convention
-```
-
----
+PARTIAL / COROLLARY; no DkMath wrapper. Its image lies in `(-1,0]` under the
+same hypotheses.

 ### MAP-028 — Exact Unsigned Inverse

-```text
-Audit Status:
-  TO AUDIT
-
-Forward:
-  x = P / (P + u)
-
-Inverse:
-  P = u * x / (1 - x)
-
-Required Conditions:
-  u > 0
-  x in the forward image
-  1 - x ≠ 0
-
-Search Terms:
-  leftInverse
-  rightInverse
-  injective
-  fractionalLinear
-  mobius
-  ratio inverse
-
-Preferred Domain:
-  ℚ
-```
-
----
+NOT FOUND / MISSING. Proposed rational formula `u*x/(1-x)` with `x ≠ 1`.

 ### MAP-029 — Exact Signed Inverse

-```text
-Audit Status:
-  TO AUDIT
-
-Forward:
-  x = -P / (P + u)
-
-Inverse:
-  P = -u * x / (1 + x)
-
-Purpose:
-  compare with existing DkMath interval convention
-
-Classification:
-  AUDIT ONLY until projection decision
-```
-
----
+NOT FOUND / MISSING. Proposed rational formula `-u*x/(1+x)` with `x ≠ -1`.

 ### MAP-030 — Projection Injectivity for Fixed `u`

-```text
-Audit Status:
-  TO AUDIT
-
-Required Meaning:
-  fixed positive u
-  projection P₁ = projection P₂
-  → P₁ = P₂
-
-Possible Proof:
-  exact left inverse
-  monotonicity
-  cross multiplication
-
-Questions:
-  Is there an existing strict monotonicity theorem?
-  Is left-inverse proof shorter?
-```
-
----
+NOT FOUND / COROLLARY once either exact inverse is proved.

 ### MAP-031 — Projection Image Characterization

-```text
-Audit Status:
-  TO AUDIT
-
-Potential Requirement:
-  characterize values attained by natural P
-
-MVP Requirement:
-  none
+DEFERRED. No MVP requirement; do not claim surjectivity onto a full interval.

-Preferred Milestone:
-  inverse only on the image
-
-Risk:
-  accidental claim of surjectivity onto a closed interval
-
-Likely Classification:
-  DEFERRED
-```
-
----
+The unsigned convention is the better first candidate because current DkReal
+arithmetic is explicitly nonnegative. The signed convention requires a signed
+DkReal layer that the repository itself says is deferred.

 ## 12. DkReal Map

 ### MAP-032 — DkReal Core Type

-```text
-Audit Status:
-  TO AUDIT
-
-Known Conceptual Role:
-  computable or nested rational representation of real values
-
-Candidate Module Family:
-  DkMath.DkReal.*
-
-Required Audit Output:
-  exact primary type
-  constructors
-  coercions
-  equality notion
-  order instances
-  interval representation
-```
-
----
+CONFIRMED / DIRECT. `DkMath.Analysis.DkReal.Basic` defines
+`DkMath.Analysis.DkReal` with `interval : ℕ → GapInterval`, stepwise nesting,
+and widths tending to zero; `DkReal.ofRat` embeds rationals.

 ### MAP-033 — GapInterval

-```text
-Audit Status:
-  TO AUDIT
-
-Known Conceptual Candidate:
-  nested interval or interval-gap structure
-
-Search Terms:
-  GapInterval
-  nested
-  width
-  interval
-  shrink
-  zero width
-  contains
-
-Questions:
-  Is GapInterval the correct public bridge?
-  What are endpoint types?
-  Is interval inclusion explicit?
-  Is width represented directly?
-```
-
----
+CONFIRMED / DIRECT. `DkMath.Analysis.DkReal.Interval.GapInterval` has rational
+`lo`, `hi`, and `lo ≤ hi`; `singleton`, interval addition, nonnegative
+multiplication, power, and separation APIs exist.

 ### MAP-034 — Nested Interval Theorems

-```text
-Audit Status:
-  TO AUDIT
-
-Required Properties:
-  I_{n+1} ⊆ I_n
-  projected value belongs to every I_n
-  widths shrink
-
-Search Terms:
-  antitone
-  nested
-  subset
-  contains
-  tendsto
-  width_zero
-  diameter
-
-Classification Goal:
-  DIRECT or BRIDGE
-```
-
----
+CONFIRMED / DIRECT. Use `DkReal.interval_succ_subset`,
+`interval_subset_of_le`, and `tendsto_width_zero`. Semantic membership in all
+cast intervals is supplied later by `DkReal.Semantic.semanticValue_mem_Icc`.

 ### MAP-035 — Width Definition

-```text
-Audit Status:
-  TO AUDIT
-
-Required Meaning:
-  upper endpoint - lower endpoint
-
-Questions:
-  Does the existing interval type expose width?
-  Is width in ℚ, ℝ, or NNReal?
-  Are nonnegativity theorems available?
-```
-
----
+CONFIRMED / DIRECT. `GapInterval.width I = I.hi - I.lo`, with
+`width_nonneg`, `lo_add_width`, and arithmetic width lemmas.

 ### MAP-036 — Mapping Intervals Through a Monotone Function

-```text
-Audit Status:
-  TO AUDIT
-
-Required Later Use:
-  apply inverse projection to projected interval endpoints
-
-Required Properties:
-  monotonicity of inverse
-  endpoint ordering
-  image interval containment
-
-Search Terms:
-  mapInterval
-  image_Icc
-  monotoneOn
-  intervalMap
-  map_lower_upper
-
-Potential First Genuine Obstruction:
-  no compatible interval-map API
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING. Existing interval power is specialized to a
+nonnegative natural power, not a fractional-linear inverse map. This is the
+first likely DkReal representation bridge.

 ### MAP-037 — Width Transport Through Inverse Map

-```text
-Audit Status:
-  TO AUDIT
-
-Required Later Goal:
-  bound width of inverse-mapped interval
-
-Possible Tools:
-  exact endpoint subtraction
-  monotonicity
-  derivative / Lipschitz bound
-  rational algebra
-  local denominator lower bound
-
-Risk:
-  becomes a new analysis program
-
-Expected Classification:
-  likely BRIDGE or MISSING
-```
-
----
+NOT FOUND AFTER SEARCH / MISSING. No fractional-linear endpoint-width bound
+was found.

 ### MAP-038 — Width Less Than One Implies At Most One Integer

-```text
-Audit Status:
-  TO AUDIT
-
-Required Theorem Meaning:
-  interval width < 1
-  → at most one integer lies inside
-
-Potential Sources:
-  Mathlib Int floor / ceil
-  interval cardinality
-  order lemmas
-  existing DkMath discretization bridge
-
-Search Terms:
-  unique integer
-  atMostOne
-  width_lt_one
-  floor
-  ceil
-  Int.cast
-  Nat.cast
-  Icc integers
-
-Classification Goal:
-  DIRECT, COROLLARY, or BRIDGE
-```
-
----
+NOT FOUND AFTER DkMath and Mathlib theorem-index/source searches / COROLLARY.
+Basic ordered-ring facts can prove it, but an exact reusable packaged theorem
+was not located.

 ### MAP-039 — Integer Existence in an Interval

-```text
-Audit Status:
-  TO AUDIT
-
-Required Distinction:
-  at-most-one does not imply existence
-
-Possible Later Requirement:
-  prove the original P lies in every reconstructed interval
-
-Preferred Route:
-  transport membership from the exact projected value
-
-Questions:
-  Can existence be obtained without floor / ceil?
-```
-
----
+PARTIAL / BRIDGE. It should come from transported membership of the original
+`P`, not from width or floor/ceil alone.

 ### MAP-040 — Unique Macro-Integer Reconstruction

-```text
-Audit Status:
-  TO AUDIT
-
-Required Final Meaning:
-  original P lies in reconstructed interval
-  reconstructed interval has width < 1
-  therefore P is the unique integer candidate
-
-Expected Composition:
-  membership
-  +
-  at-most-one integer theorem
-
-Likely Classification:
-  BRIDGE
-
-Stretch Only:
-  not required for MVP
-```
-
----
+NOT FOUND / BRIDGE. Compose inverse-map membership, MAP-037, and MAP-038;
+this is stretch work, not MVP.

 ## 13. Demo Arithmetic Map

 ### MAP-041 — Demo Prime Set Evaluation

-```text
-Audit Status:
-  EXPECTED DEMO_ONLY
-
-Required Fact:
-  product {2, 3, 5, 7} = 210
-
-Likely Proof:
-  norm_num
-  decide
-  simp
-
-Questions:
-  Which Finset literal notation is stable and readable?
-```
-
----
+DEMO_ONLY: prove `∏ p ∈ {2,3,5,7}, p = 210` with `norm_num`/`decide`.

 ### MAP-042 — Demo Coprimality

-```text
-Audit Status:
-  EXPECTED DEMO_ONLY
-
-Required Fact:
-  Nat.Coprime 210 11
-
-Likely Proof:
-  norm_num
-  decide
-```
-
----
+DEMO_ONLY: `Nat.Coprime 210 11` by `norm_num`/`decide`.

 ### MAP-043 — Demo Boundary

-```text
-Audit Status:
-  EXPECTED DEMO_ONLY
-
-Required Fact:
-  210 + 11 = 221
-
-Likely Proof:
-  norm_num
-```
-
----
+DEMO_ONLY: `210 + 11 = 221` by `norm_num`.

 ### MAP-044 — Demo Factorization

-```text
-Audit Status:
-  EXPECTED DEMO_ONLY
-
-Required Fact:
-  221 = 13 * 17
-
-Likely Proof:
-  norm_num
-```
-
----
+DEMO_ONLY: `221 = 13 * 17` by `norm_num`.

 ### MAP-045 — Demo Prime Proofs

-```text
-Audit Status:
-  EXPECTED DEMO_ONLY
-
-Required Facts:
-  Nat.Prime 13
-  Nat.Prime 17
-
-Likely Proof:
-  norm_num
-  decide
-```
-
----
+DEMO_ONLY: `Nat.Prime 13` and `Nat.Prime 17` by `norm_num`/`decide`.

 ### MAP-046 — Demo Freshness

-```text
-Audit Status:
-  GENERAL THEOREM REUSE REQUIRED
-
-Required Facts:
-  13 ∉ demoPrimeSet
-  17 ∉ demoPrimeSet
-
-Preferred Proof:
-  use the general finite-prime escape theorem
-
-Acceptable Supporting Automation:
-  norm_num or decide for divisibility and explicit membership facts
-
-Prohibited:
-  prove all public freshness results only by deciding finite membership
-```
-
----
+WRAPPER: use the general supplied-divisor exclusion theorem for both `13` and
+`17`; automation may discharge concrete primality/divisibility.

 ### MAP-047 — Demo Cosmic Completion

-```text
-Audit Status:
-  GENERAL THEOREM REUSE REQUIRED
-
-Required Fact:
-  210 * 232 + 11 ^ 2 = 221 ^ 2
-
-Preferred Proof:
-  apply or specialize the general Cosmic Completion theorem
-
-Acceptable Supporting Automation:
-  norm_num to normalize displayed constants
-```
-
----
+WRAPPER: specialize the general Nat completion theorem at `210` and `11`, then
+normalize displayed constants.

 ## 14. Candidate DkMath Module Families

-The following module families are candidates only.
-
-Their exact relevance must be confirmed by audit.
-
-```text
-DkMath.CosmicFormula.*
-  expected relevance:
-    Big / Body / Gap
-    general completion identities
-    GN bridges
-
-DkMath.DkReal.*
-  expected relevance:
-    nested rational intervals
-    width and reconstruction
-
-DkMath.NumberTheory.*
-  expected relevance:
-    prime, divisibility, gcd, finite products
-
-DkMath.Petal.*
-  possible relevance:
-    GN
-    primitive factors
-    product structures
-
-DkMath.ABC.*
-  possible relevance:
-    valuation and primitive-factor bridges
-  likely not required by MVP
-
-DkMath.KUS.*
-  possible relevance:
-    bounded or projected coordinate systems
-  must not be assumed
-
-DkMath.Units.*
-  possible relevance:
-    normalization or unit-coordinate interpretation
-  audit exact semantics before reuse
-
-DkMath.SilverRatio.*
-  likely unrelated to MVP
-  inspect only if directly referenced by a projection API
-```
-
-Codex must not perform a full audit of every listed family.
-
-Search should remain concept-driven.
-
----
+CosmicFormula is semantically relevant; NumberTheory supplies standard
+arithmetic precedents. PrimitiveSet, Petal, KUS, Units, SilverRatio, and CF2D
+are rejected or deferred for the MVP because their meanings or dependency
+costs do not match the contract.

 ## 15. Mathlib Fallback Map

-When DkMath has no project-specific theorem, prefer standard Mathlib APIs.
-
-### Finset
-
-```text
-membership
-product
-product divisibility
-filter
-image
-cardinality
-```
-
-### Nat
-
-```text
-Prime
-Coprime
-gcd
-divisibility
-prime divisor existence
-minFac
-```
-
-### Algebra
-
-```text
-ring
-ring_nf
-field_simp
-nlinarith
-```
-
-### Ordered Fields
-
-```text
-division inequalities
-positivity
-interval membership
-monotonicity
-```
-
-### Int / Floor / Ceiling
-
-```text
-integer interval bounds
-at-most-one candidate
-floor and ceil characterization
-```
-
-DkMath wrappers are preferred only when they add genuine project meaning or connect to later DkMath phases.
-
----
+The selected fallback surface is Finset product divisibility, Nat gcd/Coprime,
+Nat prime-divisor existence, divisibility of sums, and `ring`. Ordered-field
+and floor/ceil APIs remain later projection/reconstruction tools.

 ## 16. Import Audit Table

-Codex should fill this table after locating exact declarations.
-
-| Hackathon module | Candidate import | Required declaration | Import cost | Decision |
-|---|---|---|---:|---|
-| `FinitePrimeEscape.lean` | `TO AUDIT` | product-member divisibility | unknown | pending |
-| `FinitePrimeEscape.lean` | `TO AUDIT` | prime-divisor existence | unknown | pending |
-| `FinitePrimeEscape.lean` | `TO AUDIT` | coprime exclusion | unknown | pending |
-| `CosmicCompletion.lean` | `TO AUDIT` | Cosmic Formula identity | unknown | pending |
-| `CosmicCompletion.lean` | `TO AUDIT` | Big / Body / Gap bridge | unknown | pending |
-| `Demo.lean` | hackathon modules only | public facade | low | expected |
-| optional projection | `TO AUDIT` | rational normalization | unknown | deferred |
-| optional DkReal bridge | `TO AUDIT` | nested interval API | unknown | deferred |
+| Hackathon module | Proposed import | Use | Risk |
+|---|---|---|---|
+| `FinitePrimeEscape.lean` | narrow Mathlib Finset/Nat prime-gcd modules, or `Mathlib` initially | product, divisibility, gcd, prime existence | low |
+| `CosmicCompletion.lean` | `Mathlib` for `ring` | local Nat polynomial identity | low |
+| `Demo.lean` | the two hackathon modules | facade and concrete arithmetic | low |
+| later projection | ordered-field Mathlib only | rational bounds/inverse | low |
+| later DkReal bridge | `DkMath.Analysis.DkReal.Basic` plus interval module | interval representation | moderate |

-The audit should state when `import Mathlib` is being used temporarily rather than as the final narrow dependency.
-
----
+Do not import `DkMath.Samples.Prime.B`: it is broad, global-namespace sample
+code and includes unfinished Coprime theorems. Do not import PrimitiveSet,
+Petal, Zsigmondy, KUS, Units, or CF2D for the MVP. The smallest `hack-002`
+surface is `FinitePrimeEscape.lean` only: define the exact local predicate if
+desired, prove supplied-divisor exclusion, and derive fresh-prime existence.

 ## 17. Proposed Minimum Implementation Surface

-This section is provisional until the audit is complete.
-
-### `FinitePrimeEscape.lean`
-
-Possible minimal additions:
-
-```lean
-/-- A prime divisor outside the original finite reference set. -/
-def FreshPrimeFactor
-    (S : Finset ℕ) (n q : ℕ) : Prop :=
-  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
-```
-
-Only add this if no equivalent exists.
-
-Possible theorem surface:
-
-```lean
-theorem prime_dvd_product_add_coprime_not_mem
-    {S : Finset ℕ} {u q : ℕ}
-    (hS : ∀ p ∈ S, Nat.Prime p)
-    (hu : Nat.Coprime (∏ p ∈ S, p) u)
-    (hqPrime : Nat.Prime q)
-    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
-    q ∉ S
-```
-
-```lean
-theorem exists_fresh_prime_factor
-    {S : Finset ℕ} {u : ℕ}
-    (hS : ∀ p ∈ S, Nat.Prime p)
-    (hu : Nat.Coprime (∏ p ∈ S, p) u)
-    (hgt : 1 < (∏ p ∈ S, p) + u) :
-    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
-```
-
-Exact binder syntax must follow the audited product API.
-
----
-
-### `CosmicCompletion.lean`
-
-Possible minimal addition:
-
-```lean
-theorem cosmicCompletion
-    (P u : ℕ) :
-    P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2 := by
-  ring
-```
-
-Preferred replacement:
-
-```text
-thin wrapper around an existing DkMath theorem
-```
-
-if one is exact and architecturally suitable.
-
----
-
-### `Demo.lean`
-
-Possible public surface:
-
-```lean
-def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}
-
-def demoP : ℕ := 210
-
-def demoU : ℕ := 11
-
-def demoBoundary : ℕ := 221
-```
-
-```lean
-theorem demo_product :
-    ∏ p ∈ demoPrimeSet, p = demoP
-```
-
-```lean
-theorem demo_thirteen_fresh :
-    FreshPrimeFactor demoPrimeSet demoBoundary 13
-```
-
-```lean
-theorem demo_seventeen_fresh :
-    FreshPrimeFactor demoPrimeSet demoBoundary 17
-```
-
-```lean
-theorem demo_cosmic_completion :
-    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
-      (demoP + demoU) ^ 2
-```
-
-These names and shapes remain provisional until audit review.
-
----
+For `hack-002`, edit only `FinitePrimeEscape.lean`; add the local
+`FreshPrimeFactor` predicate if accepted, the supplied-divisor exclusion
+theorem, and the existence corollary. Later checkpoints may add a local `ring`
+wrapper in `CosmicCompletion.lean` and concrete facts in `Demo.lean`.

 ## 18. Audit Questions Requiring Explicit Answers

-The first Codex report must answer all of the following.
-
-### Arithmetic
-
-```text
-1. What exact theorem proves a Finset member divides its product?
-2. What exact theorem proves prime-divisor existence for n > 1?
-3. What is the shortest Coprime-based exclusion route?
-4. Is primality of every member of S logically needed?
-5. Does an exact finite-prime escape theorem already exist?
-6. Does FreshPrimeFactor already exist?
-```
-
-### Cosmic Formula
-
-```text
-7. What exact DkMath modules define Big, Body, and Gap?
-8. Is the square identity already implemented?
-9. Is the square identity a specialization of a generic exponent theorem?
-10. Is GN useful for the public facade?
-11. What is the narrowest safe import?
-```
-
-### Projection
-
-```text
-12. Does DkMath already define the signed or unsigned projection?
-13. Which convention matches current DkReal interval APIs?
-14. Does an exact inverse theorem already exist?
-15. Is projection formalized over ℚ, ℝ, or another type?
-```
-
-### DkReal
-
-```text
-16. What is the primary nested-interval type?
-17. Is interval width already defined?
-18. Can intervals be mapped through a monotone inverse?
-19. Is width transport available?
-20. Is width < 1 integer uniqueness already proved?
-```
-
-### Architecture
-
-```text
-21. Which candidate APIs would create undesirable dependencies?
-22. Can the MVP remain a thin three-module facade?
-23. What is the first genuinely missing theorem?
-24. What exact files should the first implementation checkpoint edit?
-```
-
----
+All 24 required questions are answered by MAP-001 through MAP-047 and the
+checkpoint report. The decisive answers are: the exact finite escape theorem
+and predicate are missing; the generic Cosmic split exists; the public square
+wrapper should be local; neither projection exists; DkReal has the carrier,
+nesting, and width entry points but lacks inverse interval mapping and width
+transport.

 ## 19. First Audit Report Requirements

-The first audit report must be written to:
-
-```text
-docs/hackathon/cosmic-formula-inversion-260715/
-  report-hack-001.md
-```
-
-It must contain:
-
-```text
-Status
-Search scope
-Modules inspected
-Exact reusable declarations
-Rejected near matches
-Proposed imports
-Proposed theorem wrappers
-Genuinely missing lemmas
-Dependency risks
-Smallest Phase 2 implementation surface
-No-source-edit confirmation
-Stopping point
-```
-
-It must also update this map or provide a patch proposal for it.
-
----
-
-## 20. Audit Stopping Rule
-
-The audit stops when:
-
-```text
-the finite-prime theorem route is mapped
-the Cosmic Formula route is mapped
-candidate projection and DkReal entry points are identified
-the first implementation surface is unambiguous
-the first genuinely missing theorem is named
-```
-
-The audit must stop before:
-
-```text
-editing Lean source
-proving a missing theorem
-creating projection files
-refactoring existing modules
-implementing the demo
-```
-
----
-
-## 21. Post-Audit Acceptance Criteria
+The completed detailed record is `report-hack-001.md` in this directory.

-This map is considered audit-complete when:
-
-```text
-every MVP concept has at least one confirmed declaration or MISSING record
-every selected declaration has an exact module and name
-every selected declaration has a semantic note
-import costs are recorded
-dangerous dependencies are identified
-the proposed Phase 2 file set is bounded
-open projection and DkReal decisions are clearly separated from MVP work
-```
-
----
-
-## 22. Known Pre-Audit Conclusions
-
-The following project-level conclusions are already fixed and do not require rediscovery.
-
-```text
-The public demo uses:
-  S = {2, 3, 5, 7}
-  P = 210
-  u = 11
-  P + u = 221
-  fresh factors 13 and 17
-
-The main arithmetic theorem concerns:
-  freshness relative to a finite set
-
-It does not concern:
-  sequence-relative primitive prime divisors
-
-The main Cosmic Formula identity is:
-  P(P + 2u) + u² = (P + u)²
-
-The MVP does not require:
-  formal Euclidean dissection
-  DkReal reconstruction
-  projection surjectivity
-  open-problem results
-
-Core DkMath must not depend on:
-  DkMath.Hackathon.*
-```
-
-The audit determines implementation reuse, not project meaning.
-
----
-
-## 23. Map Update Rules
-
-When Codex updates this document:
-
-```text
-preserve section identifiers MAP-001, MAP-002, ...
-do not reuse identifiers
-replace TO AUDIT with exact findings
-include exact declaration names
-include module paths
-include concise normalized theorem types
-record rejected near matches
-record import cost
-record final reuse decision
-```
-
-If multiple declarations support one concept, list each and identify the preferred one.
-
-Historical rejected candidates should remain recorded after audit.
-
----
-
-## 24. Final Map Goal
-
-The completed map should make the first implementation instruction possible without broad repository exploration.
-
-The ideal post-audit route should look like:
-
-```text
-FinitePrimeEscape.lean
-
-existing theorem A:
-  member divides Finset product
-
-existing theorem B:
-  Coprime exclusion
-
-existing theorem C:
-  prime divisor exists
-
-new wrapper D:
-  supplied prime divisor is fresh
-
-new corollary E:
-  fresh prime factor exists
-```
-
-```text
-CosmicCompletion.lean
-
-existing theorem F:
-  generic Body + Gap = Big
-
-new specialization G:
-  P(P + 2u) + u² = (P + u)²
-```
-
-```text
-Demo.lean
-
-general theorem D
-+
-general theorem G
-+
-concrete norm_num facts
-```
+## 20. Audit Stopping Rule and Searches Performed

-If the audit produces this level of clarity, the next Codex implementation session should not need to rediscover the same theorem surface.
+Exact and semantic searches were run over `DkMath/`,
+`logs/summary_report/__theorems-heading.txt`,
+`logs/__dkmath-all.lean.txt.gz`, the summary-report archive listing, direct
+candidate modules, and Mathlib sources. Terms included `FreshPrimeFactor`,
+prime/divisor/product/Coprime variants, `Big`, `Body`, `Gap`, `GN`, projection,
+inverse, normalization, DkReal, GapInterval, map interval, width transport,
+floor/ceil, `AtMostOne`, and integer uniqueness.
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-001.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-001.md
new file mode 100644
index 00000000..5e9debe7
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-001.md
@@ -0,0 +1,364 @@
+# Report — Checkpoint hack-001
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
+Checkpoint: hack-001
+Session class: AUDIT
+Model: GPT-5 Codex
+Reasoning level: not recorded
+Session identifier: not recorded
+Start: not recorded
+End: 2026-07-15 07:23 JST
+Elapsed: not recorded
+Starting credits: not recorded
+Ending credits: not recorded
+Credits consumed: not recorded
+```
+
+## Primary Goal
+
+Audit DkMath and Mathlib for the smallest dependency route from a finite prime
+set and coprime offset to a fresh prime factor, connect the arithmetic to the
+Cosmic Formula square completion, and identify only the entry points for later
+rational projection and DkReal work.
+
+## Stable Documents Read
+
+The following were read in the prescribed order:
+
+1. `README.md`
+2. `PROJECT.md`
+3. `MATHEMATICAL_CONTRACT.md`
+4. `ROADMAP.md`
+5. `ARCHITECTURE.md`
+6. `GLOSSARY.md`
+7. `DECISIONS.md`
+8. `RISKS_AND_STOPPING_RULES.md`
+9. `EXISTING_DKMATH_MAP.md`
+10. `VISUAL_STORYBOARD.md`
+11. `DEMO_CONTRACT.md`
+12. `CHECKPOINTS.md`
+13. `CODEX_PLAN.md`
+14. `__next_Instructions.md`
+
+`1st_PLAN.md` was treated as historical context and the empty UUID tracking
+anchor was not inspected.
+
+## Repository Instructions Read
+
+- `/README.md`
+- `/AGENT.md`
+- `/lean/dk_math/README.md`
+- `/lean/dk_math/notes/chatgpt_projects/cosmic_formula_lean/SUMMARY.md`
+
+The repository rule relevant here is the one-way dependency path from research
+code toward stable library surfaces. The hackathon facade must remain
+downstream of existing DkMath and Mathlib.
+
+## Search Sources
+
+- Lean source root: `/lean/dk_math`
+- DkMath module root: `/lean/dk_math/DkMath`
+- theorem heading index:
+  `/logs/summary_report/__theorems-heading.txt`
+- compressed source database:
+  `/logs/__dkmath-all.lean.txt.gz`
+- second located compressed source database:
+  `/lean/dk_math/logs/__dkmath-all.lean.txt.gz`
+- summary archive:
+  `/logs/__summary_report_data.tar.gz`
+- Mathlib source:
+  `/lean/dk_math/.lake/packages/mathlib/Mathlib`
+- direct DkMath modules listed below
+
+The compressed database was searched in place; it was not unpacked or
+duplicated. The summary archive was listed without bulk extraction.
+
+## Modules Inspected
+
+- `DkMath.Hackathon.FinitePrimeEscape`
+- `DkMath.Hackathon.CosmicCompletion`
+- `DkMath.Hackathon.Demo`
+- `DkMath.Samples.Prime.A`
+- `DkMath.Samples.Prime.B`
+- `DkMath.CosmicFormula.Defs`
+- `DkMath.CosmicFormula.CosmicFormulaBinom`
+- `DkMath.CosmicFormula.CoreBeamGap`
+- `DkMath.NumberTheory.PrimitiveSet.Basic`
+- `DkMath.Petal.PrimitiveBridge`
+- `DkMath.Petal.BezoutBridge`
+- `DkMath.Samples.Projection`
+- `DkMath.Analysis.DkReal.Interval`
+- `DkMath.Analysis.DkReal.Basic`
+- `DkMath.Analysis.DkReal.Semantic`
+- relevant DkReal arithmetic, order, and CF2D search hits
+- Mathlib Finset product, Nat gcd, Nat prime, and divisibility sources
+
+## Finite Prime Route
+
+The exact proposed path remains entirely in `ℕ`:
+
+```text
+q ∈ S
+→ Finset.dvd_prod_of_mem
+→ q ∣ P
+q ∣ P + u and q ∣ P
+→ dvd_add_right
+→ q ∣ u
+q ∣ P and q ∣ u
+→ Nat.dvd_gcd
+Nat.Coprime P u
+→ Nat.gcd P u = 1
+Nat.Prime q
+→ q ∤ 1
+→ contradiction
+→ q ∉ S
+```
+
+For existence, `1 < P + u` implies `P + u ≠ 1`, so
+`Nat.ne_one_iff_exists_prime_dvd` supplies a prime divisor. Applying the
+supplied-divisor exclusion theorem produces a fresh prime factor.
+
+Explicit answers:
+
+- No matching `FreshPrimeFactor` predicate exists.
+- No completed exact supplied-divisor exclusion theorem with the requested
+  Coprime surface exists.
+- No completed exact fresh-prime existence theorem with the requested
+  hypotheses exists.
+- Primality of every member of `S` is not logically required for exclusion.
+- `S.Nonempty` is not required.
+- `0 < u` is not required for exclusion or for existence when `1 < P + u` is
+  supplied separately.
+- `Nat.ne_one_iff_exists_prime_dvd` is the exact prime-divisor existence API.
+
+## Cosmic Formula Route
+
+The generic structure exists:
+
+```text
+DkMath.CosmicFormulaBinom.big_is_body_and_gap
+Big d x u = Body d x u + Gap d u
+```
+
+and `CoreBeamGap.big_eq_body_add_gap` gives a generic subtraction-free
+semiring route. At `d = 2`, these specialize mathematically to the desired
+square. However, the exact public Nat identity
+
+```lean
+P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
+```
+
+is not exposed by a narrow stable theorem. `cosmic_identity_ring` in
+`DkMath.Samples.Prime.B` is a subtraction-equals-zero near match, but importing
+that broad sample module would also import unrelated and unfinished material.
+The recommended implementation is therefore a thin local theorem proved by
+`ring`. GN/GZ need not appear in the public MVP facade.
+
+## Projection Entry Points
+
+No existing DkMath definition matches either candidate projection:
+
+```text
+unsigned: P / (P + u), image [0,1)
+signed:  -P / (P + u), image (-1,0]
+```
+
+No exact inverse theorem was found. The future rational formulas are
+`u*x/(1-x)` and `-u*x/(1+x)`, with nonzero-denominator conditions. The unsigned
+convention is architecturally preferable for a first bridge because the
+current DkReal arithmetic is nonnegative; this is a recommendation, not an
+implementation decision. `DkMath.Samples.Projection` and CF2D inverse actions
+have different semantics and are rejected as reuse candidates.
+
+## DkReal Entry Points
+
+The primary carrier is `DkMath.Analysis.DkReal`, a nested sequence of rational
+`GapInterval`s with widths tending to zero. `GapInterval` has rational
+endpoints, validity, width, singleton, addition, nonnegative multiplication,
+natural-power images, and separation. Relevant direct theorems include
+`interval_succ_subset`, `interval_subset_of_le`, `tendsto_width_zero`, and
+`GapInterval.width_nonneg`; `DkReal.ofRat` supplies exact rational embedding.
+
+No compatible fractional-linear interval-map operation, inverse width
+transport theorem, or packaged width-less-than-one integer uniqueness theorem
+was found. The first likely representation bridge is an inverse-projection
+endpoint map producing a valid `GapInterval` and transporting membership.
+
+## Confirmed Reusable Declarations
+
+### `Finset.dvd_prod_of_mem`
+
+- Module: `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
+- Type: `(ha : a ∈ s) → f a ∣ ∏ i ∈ s, f i`
+- Classification: DIRECT
+- Intended role: a member of `S` divides its product.
+
+### `dvd_add_right`
+
+- Module: `Mathlib.Algebra.Ring.Divisibility.Basic`
+- Type: `(h : a ∣ b) → (a ∣ b + c ↔ a ∣ c)`
+- Classification: DIRECT
+- Intended role: derive `q ∣ u` from `q ∣ P` and `q ∣ P + u`.
+
+### `Nat.dvd_gcd` and `Nat.coprime_iff_gcd_eq_one`
+
+- Module: Mathlib Nat gcd API
+- Types: common divisibility implies divisibility of `Nat.gcd`; Coprime is
+  equivalent to gcd one.
+- Classification: DIRECT
+- Intended role: contradict a prime common divisor.
+
+### `Nat.Prime.not_dvd_one`
+
+- Module: Mathlib Nat prime API
+- Type: `Nat.Prime q → ¬ q ∣ 1`
+- Classification: DIRECT
+- Intended role: final contradiction.
+
+### `Nat.ne_one_iff_exists_prime_dvd`
+
+- Module: `Mathlib.Data.Nat.Prime.Basic`
+- Type: `n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n`
+- Classification: DIRECT
+- Intended role: prime-divisor existence from `1 < n`.
+
+### `DkMath.CosmicFormulaBinom.big_is_body_and_gap`
+
+- Module: `DkMath.CosmicFormula.CosmicFormulaBinom`
+- Type: for a `CommRing R`,
+  `Big d x u = Body d x u + Gap d u`
+- Classification: DIRECT for generic Cosmic semantics; BRIDGE for the Nat
+  public square formula.
+- Intended role: confirm that the local square identity matches existing
+  Big/Body/Gap architecture.
+
+### DkReal interval declarations
+
+- Modules: `DkMath.Analysis.DkReal.Interval` and `.Basic`
+- Declarations: `GapInterval.width`, `DkReal.interval_subset_of_le`,
+  `DkReal.tendsto_width_zero`, `DkReal.ofRat`
+- Classification: DIRECT entry points
+- Intended role: later nested-interval reconstruction, not this MVP.
+
+## Rejected Near Matches
+
+- `exists_prime_not_mem_dvd_prod_add_unit` in `DkMath.Samples.Prime.B` uses
+  positivity and per-member nondivisibility rather than the requested Coprime
+  theorem surface. It is a useful proof precedent, not the chosen dependency.
+- `exists_prime_not_mem_dvd_prod_add_unit_of_coprime'` has the desired surface
+  but its proof is `sorry`; it cannot be reused.
+- `DkMath.CosmicFormula.exists_prime_not_mem_dvd_prod_succ` is specialized to
+  offset `1`, not arbitrary coprime `u`.
+- `PrimitiveOn`, `PrimitivePrimeFactorOfDiffPow`, Petal primitive bridges, and
+  Zsigmondy predicates have divisibility-antichain or sequence-relative
+  meanings. They are not finite-set freshness.
+- `cosmic_identity_ring` is mathematically suitable but lives in a broad
+  sample module with unfinished declarations.
+- `DkMath.Samples.Projection` and CF2D inverse kernels are semantically
+  unrelated to the candidate rational projection.
+
+## Dangerous Dependencies
+
+- Importing `DkMath.Samples.Prime.B` would couple the facade to global sample
+  declarations and unfinished proofs.
+- PrimitiveSet/Petal/Zsigmondy imports are broad and would misstate the
+  semantics as primitive-divisor theory.
+- KUS, Units, and CF2D imports would add unrelated abstraction and risk reverse
+  architectural pressure.
+- Existing `DkMath.CosmicFormula.Defs` uses real-only Big/Body/Gap definitions;
+  forcing the Nat MVP through them adds coercions and hides a trivial identity.
+
+## Genuinely Missing Lemmas
+
+The smallest missing MVP theorem is:
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
+The first later DkReal obstruction is an interval map for the selected
+fractional-linear inverse, including endpoint order and membership transport.
+
+## Proposed `hack-002` Implementation Surface
+
+- Exact file permitted to change:
+  `lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean`
+- Proposed imports: narrow Mathlib Finset product, Nat gcd, and Nat prime
+  modules; `import Mathlib` is acceptable initially if narrowing is deferred.
+- Proposed definition: hackathon-local `FreshPrimeFactor S n q :=
+  Nat.Prime q ∧ q ∣ n ∧ q ∉ S`, since no exact predicate exists.
+- Proposed theorems:
+  `prime_dvd_product_add_coprime_not_mem`,
+  `exists_fresh_prime_factor`, and optionally a universal wrapper.
+- Required build commands from `lean/dk_math`:
+  `lake build DkMath.Hackathon.FinitePrimeEscape`, followed by
+  `lake build` if the checkpoint requires full regression.
+
+No change to `CosmicCompletion.lean` or `Demo.lean` belongs in `hack-002` unless
+a later instruction explicitly expands that checkpoint.
+
+## Assumption Audit
+
+| Assumption | Exclusion | Existence | Reason |
+|---|---:|---:|---|
+| all members of `S` prime | not needed | not needed logically | only validates the phrase finite prime set |
+| `S.Nonempty` | not needed | not needed | empty product is `1` |
+| `0 < u` | not needed | not needed with `1 < P + u` | no subtraction or positivity route required |
+| `0 < P` | not needed | not needed with `1 < P + u` | boundary hypothesis is sufficient |
+| `Nat.Coprime P u` | required | required for freshness | excludes common divisors |
+| `1 < P + u` | not needed | required | supplies a prime divisor |
+| `Nat.Prime q` | required | supplied by existence theorem | excludes `q ∣ 1` |
+| `q ∣ P + u` | required | supplied by existence theorem | boundary divisor premise |
+
+## Files Changed
+
+- `EXISTING_DKMATH_MAP.md`
+- `report-hack-001.md`
+
+## No-Source-Edit Confirmation
+
+```text
+No Lean source file was edited.
+```
+
+## First Genuine Obstruction
+
+None for completing this audit. The first missing MVP theorem is the small
+supplied-divisor exclusion lemma stated above; its absence is a normal audit
+finding, not a checkpoint obstruction.
+
+## Out-of-Scope Routes Not Taken
+
+- no Lean theorem or predicate was implemented;
+- no scaffold source was edited;
+- no projection convention was formalized;
+- no DkReal interval map or width theorem was implemented;
+- no Euclidean geometry or Manim work was begun;
+- no primitive-divisor theorem was repurposed;
+- no later checkpoint was started;
+- no build was run merely to simulate progress.
+
+## Next Permitted Action
+
+Wise Wolf review of checkpoint hack-001.
+
+## Stop Confirmation
+
+```text
+The checkpoint stopped after the audit report.
+No Lean implementation was begun.
+No later checkpoint work was begun.
+```
````
`````
