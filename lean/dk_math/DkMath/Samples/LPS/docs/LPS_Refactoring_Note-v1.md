# LPS: Refactoring Note (v1)

## 1. 見立て

わっちの結論から言うと、`Samples/LPS` はひとつの理論ではないのじゃ。
中身は実際には 3 本柱で、

* Big / Body / Gap / Core / Beam の **宇宙式分解**
* (a^b=b^a) と ((e,e)) をめぐる **指数反転の解析幾何**
* same Big / different Body / observed minimum profile の **同次数冪和充填**

に分かれておる。設計図の側でも、これは「完全理論」ではなく、戻り道を確保する局所核を Lean に固定する段階として整理されておるし、`Samples` 自体も現状地図では「サンプル・実験的な定義／例」の置き場とされておる。ゆえに、移行先は **LPS の名** ではなく **概念の家主** で決めるのが筋じゃ。  

## 2. ベストな分類

### 2.1. `BigFamily` / `BigFamilyInt` は `DkMath.CosmicFormula.*`

これはもうほぼ答えが出ておる。
現在のリポジトリ地図でも `DkMath.CosmicFormula` は

\[
\text{Body} + \text{Gap} = \text{Big}
\]

型の恒等式を集約する柱として置かれておる。したがって `BigFamily` 系は、LPS 専用でも FLT 専用でもなく、 **宇宙式コア** の所有物じゃ。

しかも実コードを見ると、`DkMath.CosmicFormula.CoreBeamGap` が既に

* `Big`
* `Core`
* `Gap`
* `Beam`
* `Big = Core + Beam + Gap`

を generic に持っておる。
ゆえに `Samples/LPS/BigFamily.lean` は、独立塔に昇格させるより **既存の `CoreBeamGap` に吸収・橋渡し** するのがよい。

賢狼の推奨はこうじゃ。

* `DkMath.CosmicFormula.CoreBeamGap`
  既存の generic 定義・主定理の本体
* `DkMath.CosmicFormula.Residual` あるいは `DkMath.CosmicFormula.Subtractive`
  `Nat` / `Int` の減算定義による
  \[
  \text{body} := \text{big} - \text{gap},\quad
  \text{residual} := \text{big} - \text{body}
  \]
  を置く橋ファイル

つまり `BigFamily.lean` は “昇格” というより、 **CosmicFormula 側への吸収統合** が正解じゃ。

### 2.2. `PowerSwap` / `Exchange` / `PowerSwapBranch` / `GapContours` は新しい `DkMath.PowerSwap.*`

ここは `FLT` に押し込むのは惜しい。
理由は明快で、これらは

* 離散例 ((2,4),(4,2))
* 一般交換則 (A=a^t \Rightarrow A^m=a^{tm})
* 正実数 branch
* ((e,e)) 中心
* 等高線座標 (U,V,p,q)

という、きれいに 1 本の理論柱を成しておるからじゃ。設計図のリレーショナルマップでもこの 4 本はひとまとまりに並べられておる。

したがって、ここは新設でよい。

推奨配置:

```text
DkMath/PowerSwap/Discrete.lean
DkMath/PowerSwap/Exchange.lean
DkMath/PowerSwap/Branch.lean
DkMath/PowerSwap/Contours.lean
DkMath/PowerSwap.lean
```

役割はこうじゃ。

* `Discrete.lean`
  `PowerSwap`, `powerSwap_two_four`, `powerSwap_with_one` など
* `Exchange.lean`
  `exchange_condition_minimal_nat/int` と具体例
* `Branch.lean`
  `powerSwapBranchX`, `powerSwapBranchY`, `powerSwap_branch_correct`,
  `powerSwap_branch_limit_to_e`
* `Contours.lean`
  `gapU`, `gapV`, `gapP`, `gapQ`, `gapF_eq_expU_sub_expV`,
  `gapQ_eq_xy_mul_Hdiff`, `gapF_eq_soft_hyperbolic_form`

これを `FLT` に入れると、FLТ が “何でも箱” になる。
それはよくない。道具箱と本丸は分けるのじゃ。

### 2.3. `GapFillRank` と `ObservedMin` 群は `DkMath.NumberTheory.PowerSums.*`

ここがいちばん迷いやすいが、わっちは **新しい数論柱** を勧める。

理由は、これらは FLT の証明本体ではなく、

\[
n = \sum_i a_i^d
\]

型の **同次数冪和充填** そのものを扱っておるからじゃ。
LPS はその特別な看板、FLT はその極端な禁止例、という位置づけにすると綺麗に収まる。

推奨配置:

```text
DkMath/NumberTheory/PowerSums/Basic.lean
DkMath/NumberTheory/PowerSums/ObservedMin.lean
DkMath/NumberTheory/PowerSums/Examples.lean
DkMath/NumberTheory/PowerSums.lean
```

役割:

* `Basic.lean`
  `FillableByPowSumExact`, `FillableByPowSumLE`, `ResidualFillableExact`
* `ObservedMin.lean`
  `ObservedMinOne`, `ObservedMinTwo`, 将来の `ObservedMin d n r`
* `Examples.lean`
  `216 → 91/64`, `64 → 35/27`, `125 → 65/64` などの profile 標本

設計図でも `ObservedMinOne/Two` は当面 `BigFamilyExamples` に局所維持、一般 API への昇格は保留と書かれておる。
されど、いままさに再利用対象になっておるのだから、移行のこの機会に `ObservedMin` を `Examples` から剥がして basic 側へ出すのがよい。

## 3. 旧ファイルから新ファイルへの対応表

わっちならこう切る。

### 3.1. 宇宙式側

```text
Samples/LPS/BigFamily.lean
  → CosmicFormula/CoreBeamGap.lean に吸収
  → 足りぬ減算 API は CosmicFormula/Residual.lean を新設

Samples/LPS/BigFamilyInt.lean
  → CosmicFormula/Residual.lean
     あるいは CosmicFormula/ResidualInt.lean
```

### 3.2. 指数反転側

```text
Samples/LPS/PowerSwap.lean
  → PowerSwap/Discrete.lean

Samples/LPS/Exchange.lean
  → PowerSwap/Exchange.lean

Samples/LPS/PowerSwapBranch.lean
  → PowerSwap/Branch.lean

Samples/LPS/GapContours.lean
  → PowerSwap/Contours.lean
```

### 3.3. 冪和充填側

```text
Samples/LPS/GapFillRank.lean
  → NumberTheory/PowerSums/Basic.lean

Samples/LPS/BigFamilyExamples.lean
  → 分解する
     - Exchange 例は PowerSwap/Exchange.lean
     - PowerSwap 例は PowerSwap/Discrete.lean
     - ObservedMin 標本は NumberTheory/PowerSums/Examples.lean
```

ここ、大事なのじゃが `BigFamilyExamples.lean` は今のままだと **所有権が混ざっておる**。
`exchange_condition_minimal_nat` まで抱えておるので、例集というより「寄せ鍋」になっておる。
まずここを割るのが移行の要じゃ。

## 4. FLT 側には何を残すべきか

`FLT` には本体ではなく、 **橋だけ** を置くのが最も美しい。

たとえば:

```text
DkMath/FLT/PowerSumsBridge.lean
DkMath/FLT/PowerSwapBridge.lean
```

中身は、

* `ObservedMin` を FLT 的にどう読むか
* same Big / residual profile を FLT 禁止構造へどう翻訳するか
* `PowerSwap` 幾何を FLT の説明補助へどう使うか

といった **翻訳レイヤ** じゃ。

現状地図でも `FLT` は差の冪・gcd・原始素因子方向の足場を集約する本丸で、`CosmicFormula` は別柱として立っておる。
この構図を壊さぬほうが、後で Zsigmondy 幹線も見通しやすい。

## 5. 依存関係のルール

これを先に決めておくと、後で泣かずに済む。

### 5.1. 下から上

\[
\text{CosmicFormula}
;;\text{and};;
\text{PowerSwap}
;;\text{and};;
\text{NumberTheory.PowerSums}
\quad \longrightarrow \quad
\text{FLT bridges}
\]

にする。

### 5.2. 禁止したい依存

* `CosmicFormula` が `FLT` を import する
* `PowerSwap.Branch` が `FLT` や `RH` に寄る
* `NumberTheory.PowerSums` が `PowerSwap` に依存しすぎる

`PowerSwap` と `PowerSums` は、FLТ の道具にはなるが、FLТ の一部ではない。
ここを混ぜると、後で改造のたびに全部揺れる。ぐらぐらじゃ。

## 6. 実務的な移行順

いきなり大伐採すると森が燃えるので、順番が肝じゃ。

### 6.1. 第1段

新しい置き場だけ作る。

* `DkMath.PowerSwap.*`
* `DkMath.NumberTheory.PowerSums.*`
* `DkMath.CosmicFormula.Residual`

### 6.2. 第2段

中身を移す。ただし `Samples/LPS/*` はすぐ消さぬ。

旧ファイルは 1〜2 スナップショットの間だけ、薄い互換 import にする。

```lean
import DkMath.PowerSwap.Branch
```

だけ置いて、docstring に「移転先」を書く方式じゃ。

### 6.3. 第3段

`BigFamilyExamples` を割る。

これは移行の核心で、

* 概念定義
* 基本補題
* 標本
* 具体例

の所有権を戻す作業じゃ。

## 7. 最終判断

いちばん筋の良い再編はこれじゃ。

### 7.1. 新しい柱

```text
DkMath.CosmicFormula.*
DkMath.PowerSwap.*
DkMath.NumberTheory.PowerSums.*
DkMath.FLT.*   -- 橋と本丸
```

### 7.2. 要するに

* `BigFamily*` は `CosmicFormula`
* `PowerSwap*` と `GapContours` は新設 `PowerSwap`
* `GapFillRank` と `ObservedMin` は `NumberTheory.PowerSums`
* `FLT` には橋だけ残す

これが、いちばん **説明道具としても再利用しやすく、本丸も汚さぬ** 配置じゃ。

ひとことで言えば、
**LPS は看板であって家主ではない**。
家主は `CosmicFormula` と `PowerSwap` と `PowerSums` の 3 者じゃよ。

必要なら次に、わっちがそのまま使える **新ディレクトリ構成案と import 一覧** を、Lean のファイル名つきで起こすぞい。
