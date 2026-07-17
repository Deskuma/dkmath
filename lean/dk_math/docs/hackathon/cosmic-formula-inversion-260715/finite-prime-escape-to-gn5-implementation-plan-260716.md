# Finite Prime Escape → GN5 実装設計メモ

作成日: 2026-07-16

## 目的

ハッカソン向けの軽量デモ `DkMath.Hackathon.FinitePrimeEscape` を、宇宙式 `GN`・原始素因子・局所 no-lift・付値障害へ接続する。

最小目標は FLT5 全体を即座に閉じることではない。まず、FLT の高指数分岐で必要になる次の機構を、具体例 `GN 5 1 1 = 31` 上で一本の Lean 定理列として動かす。

```text
有限な既知素数集合
→ 積 + coprime offset
→ 集合外の新しい素数
→ GN の素因子へ着地
→ primitive channel
→ local no-lift
→ 付値 1
→ 完全五乗との衝突
```

この最小模型が閉じれば、ハッカソン用デモが未解決問題形式化の核心部品へ変わったことを、検証可能な形で示せる。

## 既存部品

### 1. Finite Prime Escape

対象:

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
```

既存 API:

```lean
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

```lean
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hboundary : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
```

これは「有限集合の外へ出る素数」を供給する脱出装置である。

### 2. GN5 の具体例

対象:

```text
lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
```

既存観測:

```text
GN 5 (2 - 1) 1 = GN 5 1 1 = 31
```

また、`31` は `2^5 - 1` の primitive prime channel であり、次の local no-lift が既に例示されている。

```lean
¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1
```

この仮定から `diffMass 31 2 1 5 ≤ 1` も既存 API で得られる。

### 3. Valuation Flow / ABC bridge

対象:

```text
lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean
```

主要 API:

```lean
theorem noLift_beam_bounds_local_load
```

```lean
theorem squarefree_beam_bounds_local_load_local
```

重要点は、GN 全体の squarefree を要求する必要がないことである。対象となる原始素数 `q` についてのみ、`q^2 ∤ GN` が得られればよい。

## 最小デモの算術核

有限集合を次で固定する。

```lean
({2, 3, 5} : Finset ℕ)
```

その積は `30` であり、offset を `1` とすれば境界は `31` になる。

$$\prod_{p\in\{2,3,5\}}p+1=30+1=31=GN(5,1,1)$$

したがって `FinitePrimeEscape` から得られる fresh prime factor は、そのまま `GN 5 1 1` の素因子へ着地する。

この具体例では着地橋が複雑な一般定理ではなく、数値等式 `30 + 1 = GN 5 1 1` で済む。

## 新規モジュール案

実装先候補:

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscapeGN5.lean
```

namespace:

```lean
namespace DkMath.Hackathon
```

推奨 import:

```lean
import DkMath.Hackathon.FinitePrimeEscape
import DkMath.ABC.ValuationFlowBridge
import DkMath.NumberTheory.PrimitiveBeamExamples
```

必要に応じて `DkMath.CosmicFormula.CosmicFormulaBinom` または既存 import 経路を追加する。

## 定理列

### Phase A: Escape を GN5 へ着地

第一目標:

```lean
theorem finitePrimeEscape_hits_GN5 :
    ∃ q,
      FreshPrimeFactor
        ({2, 3, 5} : Finset ℕ)
        (DkMath.CosmicFormulaBinom.GN 5 1 1)
        q := by
  ...
```

実装方針:

1. `exists_fresh_prime_factor` を `S := {2,3,5}`, `u := 1` で呼ぶ。
2. 積と `1` の coprime を `simp` または `decide` で閉じる。
3. 境界の非自明性を `norm_num` / `decide` で閉じる。
4. `GN 5 1 1 = 31` と有限積 `= 30` を計算し、結果を `simpa` で輸送する。

### Phase B: fresh prime を 31 に固定

第二目標:

```lean
theorem freshPrimeFactor_GN5_eq_31
    {q : ℕ}
    (hq : FreshPrimeFactor
      ({2, 3, 5} : Finset ℕ)
      (DkMath.CosmicFormulaBinom.GN 5 1 1)
      q) :
    q = 31 := by
  ...
```

実装方針:

1. `hq.1 : Nat.Prime q` と `hq.2.1 : q ∣ GN 5 1 1` を取り出す。
2. `GN 5 1 1 = 31` へ書き換える。
3. 素数 `31` の約数である素数 `q` は `31` に等しいことを `Nat.dvd_prime` 系 API で閉じる。

この定理は必須ではないが、後段の no-lift witness を既存の `31` の例へ接続しやすくする。

### Phase C: clean GN5 channel

第三目標:

```lean
theorem finitePrimeEscape_hits_clean_GN5_channel :
    ∃ q,
      Nat.Prime q ∧
      q ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
      q ∉ ({2, 3, 5} : Finset ℕ) ∧
      ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 := by
  ...
```

実装方針:

1. `finitePrimeEscape_hits_GN5` から `q` を得る。
2. `freshPrimeFactor_GN5_eq_31` で `q = 31` を得る。
3. 既存例と同じ計算により `¬ 31^2 ∣ GN 5 1 1` を閉じる。
4. `subst q` 後にまとめる。

この theorem がハッカソン展示上の中心となる。

### Phase D: 局所付値障害

第四目標は二案ある。

#### 案 D1: ValuationFlow の既存例へ接続

`PrimitivePrimeFlowWitness 31 2 1 5` を公開または同モジュールで再構成し、次を得る。

```lean
theorem finitePrimeEscape_GN5_diffMass_le_one :
    diffMass 31 2 1 5 ≤ 1 := by
  ...
```

#### 案 D2: 完全五乗一般障害を直接作る

再利用性の高い補題候補:

```lean
theorem not_fifth_power_of_prime_dvd_of_not_sq_dvd
    {N q : ℕ}
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ N)
    (hqNoLift : ¬ q ^ 2 ∣ N) :
    ¬ ∃ x : ℕ, N = x ^ 5 := by
  ...
```

数学核:

- `q ∣ N` と `q^2 ∤ N` から `v_q(N) = 1`。
- `N = x^5` なら `v_q(N) = 5 * v_q(x)`。
- `1` は `5` の倍数ではない。

`padicValNat` または `Nat.factorization` のうち、既存補題が短く接続できる側を選ぶ。

### Phase E: GN5 は完全五乗でない

最終デモ目標:

```lean
theorem GN_five_one_one_not_fifth_power :
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5 := by
  ...
```

`finitePrimeEscape_hits_clean_GN5_channel` と Phase D の一般補題を合成する。

## 展示用ストーリー

```text
{2,3,5} という有限素数世界を作る
→ 全積 30 に単位 1 を加える
→ 31 が有限世界の外へ脱出する
→ 31 は GN(5,1,1) そのものへ着地する
→ 31 は一度だけ GN を割り、二重化しない
→ したがって GN(5,1,1) は完全五乗になれない
```

説明文の核:

> A lightweight finite-prime escape demo unexpectedly instantiated the clean valuation channel required by our formal FLT route.

日本語:

> 有限素数集合から脱出する軽量デモが、FLT 高指数ルートで必要だった clean valuation channel の最小実働模型になった。

## FLT5 本線への一般化

この具体例だけでは FLT5 は閉じない。一般反例から生じる `GN 5 u y` に対して、同じ clean channel を供給する必要がある。

一般化ターゲット候補:

```lean
abbrev CleanGNChannelTarget : Prop :=
  ∀ {u y : ℕ},
    <FLT5 counterexample conditions> →
    ∃ q,
      Nat.Prime q ∧
      q ∣ DkMath.CosmicFormulaBinom.GN 5 u y ∧
      ¬ q ∣ u ∧
      ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 u y
```

そのために必要な橋:

```text
有限悪素数集合 S_bad
→ 全悪因子を product 側へ吸収
→ coprime offset を構成
→ product + offset が GN を割る、または GN と一致
→ FinitePrimeEscape で S_bad 外の素数を取る
→ local no-lift を回収
```

本当の研究難所は `product + offset` を一般の `GN 5 u y` へ着地させる構造定理である。

## 7月20日までの短期工程

### 7月16日夜〜17日

- `FinitePrimeEscapeGN5.lean` を作成。
- Phase A を閉じる。
- 可能なら Phase B まで閉じる。

### 7月18日

- Phase C の clean channel を閉じる。
- ValuationFlow への接続または完全五乗一般障害を実装する。

### 7月19日

- `GN_five_one_one_not_fifth_power` を閉じる。
- スタンドアローン版または最小 import 版を用意する。
- README / デモ説明 / theorem dependency 図を整える。

### 7月20日

- 提出用確認。
- Lean Comparator Live で通せる theorem shape があればカスタム Challenge 化する。
- 予備修正と発表文の調整。

## 完了条件

最低完了:

```text
finitePrimeEscape_hits_GN5
```

標準完了:

```text
finitePrimeEscape_hits_clean_GN5_channel
```

理想完了:

```text
GN_five_one_one_not_fifth_power
```

研究上の追加成果:

```text
一般 BadSet → CleanGNChannel bridge の theorem shape 固定
```

## 注意点

- `FinitePrimeEscape` が返すのは集合外の素数であり、自動的に primitive / no-lift まで返すわけではない。
- 具体例では `GN 5 1 1 = 31` によってすべてが短絡する。
- 一般 FLT5 では GN landing bridge が必要。
- global squarefree を目標にしない。必要なのは一つの local no-lift channel である。
- ハッカソン締切では完全 FLT5 よりも、再現可能な最小実働模型を優先する。

## 一行要約

**脱出装置は完成している。まず `30 + 1 = GN(5,1,1)` へ接続し、有限素数世界から飛び出した `31` が完全五乗を阻止するところまでを Lean で一本化する。**
