# PPW-011 — Mathlib von Mangoldt / safe-half-plane LSeries bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-010 canonical q-fold Green
Lean toolchain: v4.32.2
```

PPW-010 により、有限 prime-power PHZ は canonical natural-number index へ exact に折り畳まれた。

現在 Green の最終形は概念的に

```text
pascalPrimePowerPHZFiniteUpTo X s
  ↔ canonical q-indexed finite Dirichlet polynomial
```

であり、canonical coefficient は

```text
canonicalPrimePowerShadowCost q
```

である。

PPW-011 の目的は、この DkMath finite shadow coefficient が Mathlib の古典的 von Mangoldt 関数と exact に一致することを証明し、その有限和を Mathlib `LSeries` の部分和として読み替え、`s.re > 1` の安全領域に限って cutoff 極限を

$$
-\frac{\zeta'(s)}{\zeta(s)}
$$

へ接続することである。

この checkpoint は **critical strip への解析接続を行わない**。`s.re > 1` での古典的 identity を既存 Mathlib theorem に接続するところまでとする。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalVonMangoldtLSeriesBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. Mathlib API audit

Lean 4.32.2 系の Mathlib で次を利用できることを前提とする。実装時には実際の imported API と型を `#check` してから使用すること。

### 3.1 Prime-power predicate

Mathlib:

```lean
IsPrimePow q
isPrimePow_nat_iff q
not_isPrimePow_zero
not_isPrimePow_one
```

`isPrimePow_nat_iff` は概念的に

```text
IsPrimePow q
  ↔ ∃ p k, Nat.Prime p ∧ 0 < k ∧ p ^ k = q
```

を与える。

DkMath の既存 predicate:

```lean
IsPrimePowerLabel q
```

は

```text
∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k
```

という向きなので、両者の差は equality orientation のみである。

### 3.2 Classical von Mangoldt

Mathlib:

```lean
ArithmeticFunction.vonMangoldt
ArithmeticFunction.vonMangoldt_apply
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime
ArithmeticFunction.vonMangoldt_eq_zero_iff
ArithmeticFunction.vonMangoldt_ne_zero_iff
```

`vonMangoldt` は prime power `p^k` に `Real.log p`、prime power でない自然数に `0` を返す classical arithmetic function である。

### 3.3 LSeries

Mathlib:

```lean
LSeries.term
LSeries.term_def₀
LSeries
LSeriesSummable
LSeriesSummable.LSeriesHasSum
```

係数 `f 0 = 0` のとき、`LSeries.term_def₀` は

```text
LSeries.term f s n
  ↔ f n * (n : ℂ) ^ (-s)
```

の exact rewrite を与える。

### 3.4 von Mangoldt LSeries

Mathlib:

```lean
ArithmeticFunction.LSeriesSummable_vonMangoldt
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

後者は `hs : 1 < s.re` の下で

```lean
LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
  - deriv riemannZeta s / riemannZeta s
```

を既に与える。

**この定理を再証明しないこと。** PPW-011 は DkMath finite PHZ をこの既存 theorem の左辺へ接続する。

### 3.5 Partial sums

Mathlib:

```lean
HasSum.tendsto_sum_nat
Summable.tendsto_sum_tsum_nat
```

が `Finset.range n` の有限部分和の収束を与える。

---

## 4. Phase A — prime-power predicate bridge

まず DkMath predicate と Mathlib predicate を完全に一致させる。

目標 theorem:

```lean
theorem isPrimePowerLabel_iff_isPrimePow (q : ℕ) :
    IsPrimePowerLabel q ↔ IsPrimePow q := by
  ...
```

証明は `isPrimePow_nat_iff` を用いて equality orientation を反転するだけでよい。

この theorem は後続の zero/nonzero case split で共通 bridge として使用する。

### 禁止

`IsPrimePowerLabel` を廃止したり、PPW-010 の canonical fold を Mathlib predicate へ全面置換しない。

PPW-010 は Green checkpoint として保持し、PPW-011 は bridge layer を追加するだけにする。

---

## 5. Phase B — canonical shadow coefficient = classical von Mangoldt

PPW-011 の最重要 arithmetic theorem。

```lean
theorem canonicalPrimePowerShadowCost_eq_vonMangoldt (q : ℕ) :
    canonicalPrimePowerShadowCost q =
      ArithmeticFunction.vonMangoldt q := by
  ...
```

### prime-power case

`hq : IsPrimePowerLabel q` から witness

```text
q = p ^ j
Nat.Prime p
0 < j
```

を取得する。

DkMath 側は既存 theorem

```lean
canonicalPrimePowerShadowCost_eq_log_of_witness
```

で `Real.log p` へ落とす。

Mathlib 側は

```lean
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime
```

で同じ `Real.log p` へ落とす。

### non-prime-power case

`¬ IsPrimePowerLabel q` を `isPrimePowerLabel_iff_isPrimePow` で

```text
¬ IsPrimePow q
```

へ移し、Mathlib の

```lean
ArithmeticFunction.vonMangoldt_eq_zero_iff
```

を使って右辺を `0` にする。

DkMath 側も `canonicalPrimePowerShadowCost` の negative branch から `0` にする。

### 成功条件

この theorem が Green になった時点で、`canonicalPrimePowerShadowCost` は単なる類似 shadow ではなく、**Mathlib の classical von Mangoldt coefficient と extensionally equal** である。

ただし既存 API 名は互換性のため残す。rename や大規模 refactor は PPW-011 の仕事ではない。

---

## 6. Phase C — finite canonical PHZ を standard Λ finite sum へ rewrite

目標:

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_vonMangoldt_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ q ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt q : ℂ) *
          ((q : ℂ) ^ (-s)) := by
  ...
```

これは `canonicalPrimePowerShadowCost_eq_vonMangoldt` を有限和の各項へ適用するだけでよい。

さらに PPW-010 の exact fold と合成して、元の pair-based finite PHZ に対しても同じ theorem を作る。

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      ∑ q ∈ Finset.range (X + 1),
        (ArithmeticFunction.vonMangoldt q : ℂ) *
          ((q : ℂ) ^ (-s)) := by
  ...
```

ここは finite identity であり、`s.re > 1` 仮定は不要。

---

## 7. Phase D — LSeries partial-sum bridge

係数関数は必要なら local abbreviation / definition を置いてよい。

候補:

```lean
noncomputable def vonMangoldtComplexCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)
```

ただし theorem statement が冗長にならない限り、無理に新定義を作らなくてもよい。

まず `LSeries.term_def₀` 用に係数 `0` が `0` であることを固定する。

候補:

```lean
@[simp] theorem vonMangoldtComplexCoeff_zero :
    (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
  ...
```

`vonMangoldt_apply` と `not_isPrimePow_zero`、または既存 simp API で閉じる。

次に term bridge:

```lean
theorem vonMangoldt_LSeries_term_eq
    (s : ℂ) (n : ℕ) :
    LSeries.term
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        ((n : ℂ) ^ (-s)) := by
  ...
```

そのうえで finite partial sum theorem:

```lean
theorem pascalPrimePowerPHZCanonicalUpTo_eq_LSeries_partialSum
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo X s =
      ∑ n ∈ Finset.range (X + 1),
        LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  ...
```

同様に元の `pascalPrimePowerPHZFiniteUpTo` 版も作ってよい。

---

## 8. Phase E — `s.re > 1` で cutoff 極限を LSeries へ接続

ここから初めて解析的仮定

```lean
hs : 1 < s.re
```

を導入する。

Mathlib の

```lean
ArithmeticFunction.LSeriesSummable_vonMangoldt hs
```

から `LSeriesSummable.LSeriesHasSum` を得て、さらに

```lean
HasSum.tendsto_sum_nat
```

で `Finset.range n` 部分和の極限を得る。

cutoff 側は `Finset.range (X + 1)` なので、`X ↦ X + 1` の `atTop` 収束を `simpa` / `filter_upwards` / 既存 Nat tendsto API で処理する。

目標 theorem:

```lean
theorem tendsto_pascalPrimePowerPHZCanonicalUpTo_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun X => pascalPrimePowerPHZCanonicalUpTo X s)
      atTop
      (nhds
        (LSeries
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)) := by
  ...
```

さらに PPW-010 fold から元の finite PHZ 版:

```lean
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun X => pascalPrimePowerPHZFiniteUpTo X s)
      atTop
      (nhds
        (LSeries
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)) := by
  ...
```

---

## 9. Phase F — safe-half-plane log-derivative bridge

Mathlib の既存 theorem をそのまま使用する。

```lean
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
```

最終目標:

```lean
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun X => pascalPrimePowerPHZFiniteUpTo X s)
      atTop
      (nhds (- deriv riemannZeta s / riemannZeta s)) := by
  ...
```

canonical 版も同様に置いてよい。

必要なら theorem-facing wrapper として

```lean
theorem pascalVonMangoldtLSeries_eq_neg_deriv_riemannZeta_div
    {s : ℂ} (hs : 1 < s.re) :
    LSeries
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      - deriv riemannZeta s / riemannZeta s := by
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
```

を追加してもよいが、単なる alias で価値が薄いなら不要。

---

## 10. 必須監査ポイント

1. `canonicalPrimePowerShadowCost_eq_vonMangoldt` が全自然数 `q` で成り立つこと。prime-power case だけの theorem で終わらせない。
2. finite sum identity には `s.re > 1` を付けない。有限和なので不要。
3. LSeries / limit theorem で初めて `1 < s.re` を導入する。
4. `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` を再証明しない。
5. `-ζ'/ζ` の identity を critical strip へ自動延長しない。
6. finite PHZ の零点を zeta zero と同一視しない。
7. `LSeries` の `n = 0` convention を明示的に処理する。
8. `sorry` / `axiom` / `admit` を追加しない。
9. PPW-010 の Green theorem を壊す refactor をしない。
10. `Complex.arg`、偏角、三角関数は不要。導入しない。

---

## 11. 非目標

PPW-011 では以下を証明しない。

```text
critical strip での -ζ'/ζ Dirichlet series convergence
analytic continuation of the finite PHZ cutoff
zeta zero ↔ PHZ zero
zero-locus collapse
RH
CFBRC interaction assimilation provider
```

特に `s.re > 1` は zeta の通常 Dirichlet/Euler 領域であり、今回の bridge は **arithmetic consistency audit** である。

これは重要な Green checkpoint だが、RH の off-critical exclusion そのものではない。

---

## 12. 推奨実装順

```text
A. IsPrimePowerLabel ↔ IsPrimePow
B. canonical shadow cost = Mathlib vonMangoldt
C. canonical finite PHZ = finite Λ Dirichlet sum
D. finite Λ sum = LSeries partial sum
E. s.re > 1 で partial sums → LSeries
F. Mathlib theorem で LSeries = -ζ'/ζ
G. 元の pair-based finite PHZ まで compose
```

各段階で小さく build し、最後に全体 build を行う。

---

## 13. 完了条件

最低限、次の theorem 群が Green になること。

```lean
isPrimePowerLabel_iff_isPrimePow
canonicalPrimePowerShadowCost_eq_vonMangoldt
pascalPrimePowerPHZCanonicalUpTo_eq_vonMangoldt_sum
pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
vonMangoldt_LSeries_term_eq
pascalPrimePowerPHZCanonicalUpTo_eq_LSeries_partialSum
tendsto_pascalPrimePowerPHZCanonicalUpTo_LSeries
tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries
tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
```

実際の Mathlib theorem の型に合わせて名前や中間補題は調整してよい。

検証:

```text
lake build DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
lake build DkMath.RH
git diff --check
```

公開 import を追加した場合は `DkMath.RH` Green まで確認する。

---

## 14. PPW-012 への出口

PPW-011 が Green になっても、次に単純な「解析接続」で critical strip へ進めてはならない。

PPW-012 ではまず、次のどちらを theorem-facing research object にするか audit する。

```text
A. completed-zeta / explicit-formula bridge
B. Weil / Li positivity bridge
```

prime-side `Λ` と zero-side data を同一の正値二次形式・explicit formula の中で結ぶ経路を優先する。

PPW-011 の最終 theorem は `s.re > 1` の境界線として明示的に残し、その境界を越える theorem は別 checkpoint とする。
