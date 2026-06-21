# DkMath.PowerSwap 実装計画書・設計書

DkMath.PowerSwap Implementation Plan and Design Document

> **Document status (2026-06-21): historical design baseline**
>
> The mathematical direction remains valid, but the module names and
> implementation order no longer describe the current workspace. New work
> should follow
> [the feasible implementation plan](./DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md)
> while using this document for the original mathematical motivation.

## Current alignment note

The current package already contains `Basic`, `Exchange`, `NormalForm`,
`Branch`, and `Contours`. The `Nat`-specific normal form and analytic real
branch were implemented before the generic structural middle layer proposed
here. The remaining work is therefore an insertion, not a restart:

```text
NatPowerFrame
NormalizesTo
same-degree comparison specifications
CosmicPowerFrame
DkNNRealQ bridge
finite representative observation
```

The existing types have distinct roles. `DkNNReal` is an interval
representative used by finite executable observation. `DkNNRealQ` is the
quotient value used by public equality, order, and power comparison. Full
quotient order is total as a proposition, but no global `DecidableLE`,
`DecidableEq`, or `LinearOrder` is planned.

## 0. 目的

`DkMath.PowerSwap.*` は、冪構造を比較・正規化するための独立した基盤層として実装する。

主目的は、異なる形で現れた冪構造を、同じ観測次元、つまり同じ `d-frame` に揃えることである。

中心となる考えは次である。

$$
a^b=b^a
$$

この関係を PowerSwap と呼ぶ。

この関係は、底と次数の交換可能性を表す。
対数で見ると、次の等高線条件に対応する。

$$
\frac{\log a}{a}=\frac{\log b}{b}
$$

したがって PowerSwap Framework は、値そのものを直接比較する前に、冪表現を同じ構造へそろえるための正規化装置となる。

DkNNRealQ との接続は後段の Bridge とする。
まずは `DkMath.PowerSwap.*` に、型非依存の純粋な構造核を実装する。

## 1. 設計方針

PowerSwap 側では、最初から `DkNNRealQ`、`Real`、`NNReal` に依存しない。

まず扱うのは、次の抽象構造である。

```text
base
degree
power value
swap relation
level
branch
normal frame
```

DkNNRealQ のような実数解析層へは、後で Bridge を作る。

層の分離は次のようにする。

```text
DkMath.PowerSwap.*
  PowerSwap の純粋核
  冪構造
  swap 関係
  等高線構造
  d-frame 正規化

DkMath.Analysis.DkReal.*
  DkNNRealQ
  DkReal
  Gap
  Order
  StrictOrder

DkMath.Analysis.DkReal.PowerSwapBridge
  PowerSwap frame と DkNNRealQ の接続
```

この分離により、PowerSwap は解析層に閉じ込められず、GN、Petal、整数論、実数解析、指数比較の共通基盤として使える。

## 2. 数学的核

PowerSwap の基本式は次である。

$$
a^b=b^a
$$

正の実数範囲で対数を取れば、次の形になる。

$$
b\log a=a\log b
$$

両辺を `ab` で割ると、次の等高線条件になる。

$$
\frac{\log a}{a}=\frac{\log b}{b}
$$

ここで関数を定義する。

$$
\Phi(t)=\frac{\log t}{t}
$$

この `Φ` の等高線上にある二点 `a`, `b` は PowerSwap 関係を持つ。

`Φ(t)` は `t=e` で最大値を取る。
したがって PowerSwap の中心点は次である。

$$
(e,e)
$$

この中心からの距離、または等高線値の差を、正規化精度・分岐制御・比較安定性の指標として利用する。

## 3. 実装対象の段階分け

PowerSwap 実装は、いきなり `log` や `e` を入れない。
まず algebraic / structural な核から始める。

### Stage 1: Core

目的は、PowerSwap の構文的・代数的な枠を作ること。

想定ファイル。

```text
DkMath/PowerSwap/Core.lean
```

定義候補。

```lean
structure PowerFrame (α : Type u) where
  base : α
  degree : α
```

自然数次数版も別に用意する。

```lean
structure NatPowerFrame (α : Type u) where
  base : α
  degree : ℕ
```

PowerSwap relation。

```lean
def PowerSwapRel [Pow α α] (A B : PowerFrame α) : Prop :=
  A.base ^ A.degree = B.base ^ B.degree
```

ただし Lean の `Pow α α` は一般には重い可能性があるため、最初は演算を明示的に渡す設計も候補にする。

```lean
structure PowerOp (α : Type u) where
  pow : α → α → α
```

または自然数冪に限定するなら、既存の `Pow α ℕ` を使う。

```lean
def NatPowerValue [Pow α ℕ] (A : NatPowerFrame α) : α :=
  A.base ^ A.degree
```

基本 theorem 候補。

```lean
theorem PowerFrame.ext_base_degree
theorem NatPowerFrame.ext_base_degree
theorem NatPowerValue_congr
theorem PowerSwapRel.refl
theorem PowerSwapRel.symm
theorem PowerSwapRel.trans
```

まずは PowerSwap を「冪値が等しい」という同値関係として扱えるようにする。

## 4. Stage 2: Swap

目的は、底と次数を交換する構造を明示すること。

想定ファイル。

```text
DkMath/PowerSwap/Swap.lean
```

定義候補。

```lean
def swap (A : PowerFrame α) : PowerFrame α where
  base := A.degree
  degree := A.base
```

定理候補。

```lean
theorem swap_swap (A : PowerFrame α) :
    swap (swap A) = A
```

```lean
theorem swap_base (A : PowerFrame α) :
    (swap A).base = A.degree
```

```lean
theorem swap_degree (A : PowerFrame α) :
    (swap A).degree = A.base
```

PowerSwap 本体は、次の形で表す。

```lean
def IsPowerSwap [Pow α α] (a b : α) : Prop :=
  a ^ b = b ^ a
```

基本定理。

```lean
theorem IsPowerSwap.symm
theorem IsPowerSwap.refl
```

ここではまだ `log` は不要。
単に `a^b=b^a` という関係だけを構造化する。

## 5. Stage 3: Level

目的は、PowerSwap の等高線構造を抽象化すること。

解析的には `Φ(t)=log t/t` を使うが、最初は `level` 関数を抽象的に扱う。

想定ファイル。

```text
DkMath/PowerSwap/Level.lean
```

定義候補。

```lean
structure LevelFunction (α β : Type u) where
  level : α → β
```

PowerSwap の等高線。

```lean
def SameLevel (L : LevelFunction α β) (a b : α) : Prop :=
  L.level a = L.level b
```

基本定理。

```lean
theorem SameLevel.refl
theorem SameLevel.symm
theorem SameLevel.trans
```

後で解析層に接続するとき、`level` に次を入れる。

$$
\Phi(t)=\frac{\log t}{t}
$$

しかし PowerSwap core では、`level` は抽象関数のままにする。

## 6. Stage 4: Branch

目的は、中心点 `(e,e)` の左右分岐を扱う準備をすること。

PowerSwap 等高線は、一般に中心 `e` を境に左右の枝を持つ。

```text
left branch:
  t < e

center:
  t = e

right branch:
  e < t
```

Core 側では `e` を直接持たず、抽象的な中心点を扱う。

想定ファイル。

```text
DkMath/PowerSwap/Branch.lean
```

定義候補。

```lean
inductive Branch where
  | left
  | center
  | right
```

中心つき構造。

```lean
structure CenteredLevel (α β : Type u) where
  center : α
  level : α → β
```

分岐判定は、最初は Prop として外から与える。

```lean
structure BranchWitness (α : Type u) where
  point : α
  branch : Branch
```

後で順序構造がある型に対して、

```text
point < center
point = center
center < point
```

から branch を構成する Bridge を作る。

この段階では、branch は正規化の追加情報として持つだけでよい。

## 7. Stage 5: d-frame 正規化

目的は、異なる冪構造を共通の観測次元 `d` に揃えるための仕様を作ること。

想定ファイル。

```text
DkMath/PowerSwap/Normalize.lean
```

正規化 relation。改訂計画では正規化専用の frame 型を重複して作らず、
source と target の両方に `NatPowerFrame` を用いる。

```lean
structure NormalizesTo [Pow α ℕ]
    (source target : NatPowerFrame α) : Prop where
  value_eq : source.eval = target.eval
```

この段階では、正規化関数そのものを必ずしも作らない。
まずは「正規化できた」という証拠 relation を作る。

理由は、任意の値を任意の `d` に揃えるには根や対数が必要になるためである。

したがって最初は次を実装する。

```text
normalize function ではなく
normalization witness を実装する
```

つまり、

```lean
NormalizesTo A N
```

を持てば、`A` は `N` と同じ値を表すと扱える。

## 8. Stage 6: 同一 d-frame 比較

目的は、同じ次数に揃った冪構造を底比較へ落とすこと。

非負世界では、同じ自然数次数 `d` のもとで、底の順序から冪の順序を得られる。

PowerSwap core では、順序と冪単調性を仮定として抽象化する。

想定ファイル。

```text
DkMath/PowerSwap/Compare.lean
```

同一次数の比較 relation。

```lean
def SameDegree (A B : NatPowerFrame α) : Prop :=
  A.degree = B.degree
```

抽象 theorem の形。

```lean
theorem value_le_of_base_le_same_degree
    [Preorder α] [Pow α ℕ]
    {A B : NatPowerFrame α}
    (hd : A.degree = B.degree)
    (hbase : A.base ≤ B.base)
    (hpow : ∀ n, A.base ≤ B.base → A.base ^ n ≤ B.base ^ n) :
    A.base ^ A.degree ≤ B.base ^ B.degree
```

ただし実際には、`hpow` は型ごとの Bridge に置く方が自然である。

PowerSwap core では、次のような「比較仕様」を作るだけでもよい。

```lean
structure SameDegreeComparison [LE α] (A B : NatPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  base_le : A.base ≤ B.base
```

厳密比較では次数 0 による値 `1` への退化を除くため、正次数を証拠として
持つ。

```lean
structure SameDegreeStrictComparison [LT α]
    (A B : NatPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  degree_pos : 0 < A.degree
  base_lt : A.base < B.base
```

Bridge 側で、これを実値比較に変換する。

## 9. Stage 7: Cosmic decomposition

目的は、正規化された底をさらに `x+u` に分ける構造を作ること。

PowerSwap 正規化の最終形は、DkMath 的には次である。

$$
(x+u)^d
$$

ただし `PowerSwap` core 側では、加法と冪だけを抽象化する。

想定ファイル。

```text
DkMath/PowerSwap/CosmicFrame.lean
```

定義候補。

```lean
structure CosmicPowerFrame (α : Type u) where
  core : α
  gap : α
  degree : ℕ
```

値。

```lean
def CosmicPowerFrame.value [Add α] [Pow α ℕ]
    (A : CosmicPowerFrame α) : α :=
  (A.core + A.gap) ^ A.degree
```

基本定理。

```lean
theorem CosmicPowerFrame.value_congr
theorem CosmicPowerFrame.same_core_same_gap_same_degree
```

比較用 frame。

```lean
structure SameCosmicDegreeComparison [Add α] [LE α]
    (A B : CosmicPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  base_le : A.core + A.gap ≤ B.core + B.gap
```

DkMath 的な意味は次である。

```text
d:
  観測次元

x:
  Core / Body 側

u:
  Gap / Unit 側

x + u:
  正規化された底

(x + u)^d:
  観測された Big
```

## 10. 依存関係の設計

改訂後の推奨 module 構成。

```text
DkMath.PowerSwap.Basic
DkMath.PowerSwap.Exchange
DkMath.PowerSwap.NormalForm
DkMath.PowerSwap.Frame
DkMath.PowerSwap.Normalize
DkMath.PowerSwap.Compare
DkMath.PowerSwap.CosmicFrame
DkMath.PowerSwap.Core

DkMath.PowerSwap.Branch
DkMath.PowerSwap.Contours
DkMath.PowerSwap.Analytic

DkMath.PowerSwap
```

`DkMath.PowerSwap.Core` は軽量な structural entry point とする。

```lean
import DkMath.PowerSwap.Basic
import DkMath.PowerSwap.Exchange
import DkMath.PowerSwap.NormalForm
import DkMath.PowerSwap.Frame
import DkMath.PowerSwap.Normalize
import DkMath.PowerSwap.Compare
import DkMath.PowerSwap.CosmicFrame
```

解析的な `log`、`exp`、`e` を含む既存モジュールには薄い入口を追加する。

```text
DkMath.PowerSwap.Analytic
```

既存 `DkMath.PowerSwap` は互換 umbrella として `Core + Analytic` を
re-export する。新規の非解析 consumer は `DkMath.PowerSwap.Core` を
import する。

## 11. DkNNRealQ Bridge の後続計画

PowerSwap core が整った後、DkNNRealQ 側に Bridge を作る。

候補ファイル。

```text
DkMath/Analysis/DkReal/PowerSwapBridge.lean
```

Bridge の役割。

```text
NatPowerFrame DkNNRealQ
  を DkNNRealQ の冪値として読む

CosmicPowerFrame DkNNRealQ
  を (x+u)^d として読む

SameDegreeComparison
  を DkNNRealQ の順序比較へ変換する

NormalizesTo
  を DkNNRealQ 等号へ変換する
```

定義候補。

```lean
def NatPowerFrame.evalDk
    (A : NatPowerFrame DkNNRealQ) : DkNNRealQ :=
  A.base ^ A.degree
```

```lean
def CosmicPowerFrame.evalDk
    (A : CosmicPowerFrame DkNNRealQ) : DkNNRealQ :=
  (A.x + A.u) ^ A.degree
```

定理候補。

```lean
theorem evalDk_eq_of_NormalizesTo
```

```lean
theorem evalDk_le_of_sameDegree_base_le
```

```lean
theorem cosmic_evalDk_le_of_same_degree_base_le
```

DkNNRealQ では既に `pow_le_pow` があるため、同じ `d` に揃った後の比較はかなり簡単になる。

## 12. 実装上の重要な注意点

### 12.1 任意の値を任意の次数へ正規化しない

任意の値 `v` を `base^d` へ正規化するには、一般に `d` 乗根が必要になる。

$$
base=v^{1/d}
$$

これは `DkNNRealQ` core ではまだ重い。
したがって最初は、正規化関数ではなく正規化証拠を扱う。

```lean
NormalizesTo A N
```

この relation を使えば、無理に根を構成せずに PowerSwap 正規化の API を作れる。

### 12.2 `log` と `e` は後段に隔離する

PowerSwap の解析的解釈では `log` と `e` が重要だが、core に入れると依存が重くなる。

最初は次の抽象構造で十分である。

```text
level : α → β
center : α
branch : Branch
```

`Φ(t)=log t/t` は、後で Real Bridge または Analytic module で具体化する。

### 12.3 完全比較器ではなく正規化器として始める

PowerSwap は、DkNNRealQ 全体の comparison を一撃で解くものではない。

まずの役割は次である。

```text
異なる冪構造を同じ d-frame へ揃える
```

そこから DkNNRealQ Bridge が、既存の order API に渡す。

## 13. 次に作るべき最小 API

既存 `Basic / Exchange / NormalForm / Branch / Contours` を維持し、次の
structural middle layer を追加する。

```text
NatPowerFrame
NatPowerFrame.eval
NatPowerFrame.power
NormalizesTo
SameDegree
SameDegreeComparison
SameDegreeStrictComparison
CosmicPowerFrame
CosmicPowerFrame.value
CosmicPowerFrame.toNatPowerFrame
```

`NatPowerFrame` のデータ定義と `eval` は `[Pow α ℕ]` でよい。
`eval_power` のように `pow_mul` を使う定理は `[Monoid α]` を要求する。

```text
definitions:
  [Pow α ℕ]

power-law theorems:
  [Monoid α]
```

既存 `PowNormalForm` は置換せず、`NatPowerFrame ℕ` との変換を追加する。

## 14. 第二コミット候補

比較仕様と DkNNRealQ Bridge を分離する。

```text
PowerSwap core:
  SameDegree
  SameDegreeComparison
  SameDegreeStrictComparison

DkReal bridge:
  eval equality
  same-degree non-strict comparison
  same-degree strict comparison with 0 < degree
```

core は `DkNNRealQ` に依存しない。Bridge が既存の `pow_le_pow` と
strict ordered-semiring API へ渡す。

## 15. 第三コミット候補

`DkMath.Analysis.DkReal.PowerSwapBridge` を追加する。

```lean
def NatPowerFrame.evalDk
def CosmicPowerFrame.evalDk
theorem evalDk_eq_of_NormalizesTo
theorem evalDk_le_of_sameDegree_base_le
theorem evalDk_lt_of_sameDegree_base_lt
theorem cosmic_evalDk_le_of_same_degree_base_le
```

strict theorem は `degree ≠ 0` ではなく `0 < degree` を主仮定にする。

## 16. 第四コミット候補

有限観測比較と import 境界を追加する。

```text
StageComparison
compareAt on DkNNReal representatives
compareUpTo with finite fuel
StrictCertificate
DkMath.PowerSwap.Core
DkMath.PowerSwap.Analytic
```

`compareAt` は代表元の rational endpoint を読むため `DkNNReal` 上に置く。
soundness theorem は `DkNNRealQ.mk` の strict order を結論とする。
`none` は検索範囲内で分離が見つからなかったことだけを表し、等号を意味しない。

解析実装はすでに `Branch` と `Contours` に存在する。新設する
`DkMath.PowerSwap.Analytic` は両者をまとめる薄い入口とする。

## 17. DkMath 的な解釈

PowerSwap Framework は、比較前の構造整列である。

```text
入力:
  base₁ ^ d₁
  base₂ ^ d₂

PowerSwap:
  共通 d-frame へ寄せる

出力:
  base₁' ^ d
  base₂' ^ d

比較:
  base₁' と base₂' を比較する

宇宙式分解:
  base = x + u

最終比較:
  x, u, d の三要素構造を比較する
```

この流れにより、異なる入口から入ってきた冪表現を、同じ観測次元の標準姿へ近づけられる。

DkMath 的には、PowerSwap は次の役割を持つ。

$$
\boxed{\text{PowerSwap は、底と次数の揺らぎを同じ }d\text{-frame に整列する正規化核である。}}
$$

さらに Cosmic decomposition まで進めると、次になる。

$$
\boxed{\text{PowerSwap 正規化後、底を }x+u\text{ に分け、}d,x,u\text{ の三要素比較へ落とす。}}
$$

## 18. 最終目標

最終的に欲しい姿は次である。

```text
PowerSwap core:
  冪構造の正規化

CosmicPowerFrame:
  (x+u)^d への構造分解

DkNNRealQ Bridge:
  DkNNRealQ の順序・冪単調性へ接続

Comparison support:
  同じ d-frame の値は底比較へ落とす

Analytic layer:
  log(t)/t と中心 (e,e) による branch / precision 制御
```

これにより、DkMath の比較設計は次の形になる。

```text
左右どちらから入る
PowerSwap で d を揃える
底を見る
底を x+u に分ける
Core / Beam / Gap として比較する
```

これが `DkMath.PowerSwap.*` 側の実装計画である。
