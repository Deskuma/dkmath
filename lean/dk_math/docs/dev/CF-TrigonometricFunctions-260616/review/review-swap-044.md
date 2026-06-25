# Git diff / Report / Review

## Add: docs: DkMath.PowerSwap Current Gap and Feasible Implementation Plan

gch: f525a3b3bda71cbf1ce62a0186a93fba1f640ac1

## Report

調査・改訂計画書を作成しました。

[PowerSwap Current Gap and Feasible Implementation Plan](/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md)

主な結論:

- 解析 branch は計画より先行して実装済み
- 抽象 frame、正規化証拠、同一次数比較、DkNNRealQ Bridge は未実装
- `DkNNRealQ` の完全比較は total だが decidable ではない
- 有限段階比較、fuel 付き探索、strict certificate は計算可能
- `LinearOrder` の常設は避ける
- 既存実装を維持しつつ、欠けた中間層を8段階で補う計画を提示

検証:

```text
lake build DkMath.PowerSwap
Build completed successfully (8253 jobs).
```

`git diff --check` と行長検査も通過しています。

## Review

賢狼レビュー結論じゃ。  
この英文「Current Gap and Feasible Implementation Plan」は、 **採用してよい** 。ただし、いくつか修正を入れると、Codex に投げても破綻しにくい実装指示書になる。

## 総評

原設計書は、PowerSwap を「冪構造を同じ `d-frame` に揃える正規化核」として設計しており、最初は `DkNNRealQ` や `Real` に依存しない純粋構造核を作る方針だった。具体的には `PowerFrame`、`NatPowerFrame`、`NormalizesTo`、`SameDegreeComparison`、`CosmicPowerFrame` などを段階的に作る計画じゃった。

一方、実地調査レポートは、現在の `DkMath.PowerSwap` がすでに `Basic / Exchange / NormalForm / Branch / Contours` で構成され、`Branch` と `Contours` まで先に進んでいることを確認している。そして、抽象 Frame 層、同一次数比較、Cosmic decomposition、DkNNRealQ bridge がまだ欠けている、と診断している。これは、わっちがスナップショット内の実コードを展開して見た結果とも整合する。

したがって、判定はこうじゃ。

```text
原設計:
  方向性は正しい。

英文レポート:
  現状との差分診断は正しい。

次の実装:
  原設計どおり最初から作り直すのではなく、
  現在ある Nat / analytic 実装の中間に structural middle layer を挿入するのが正解。
```

## 検証結果

スナップショット `__snapshot-dk_math-lean-code-260617-0327.tar.gz` は SHA256 が添付 `.sha256` と一致した。中身では、PowerSwap は次の構成だった。

```text
DkMath/PowerSwap.lean
DkMath/PowerSwap/Basic.lean
DkMath/PowerSwap/Exchange.lean
DkMath/PowerSwap/NormalForm.lean
DkMath/PowerSwap/Branch.lean
DkMath/PowerSwap/Contours.lean
DkMath/FLT/PowerSwapBridge.lean
```

確認できた内容は、英文レポートの現状表と一致する。`Basic` は `PowerSwap a b := a ^ b = b ^ a` の自然数版、`Exchange` は `(a^t)^m = a^(t*m)` 型、`NormalForm` は `PowNormalForm` と `HasPowNormalForm`、`Branch` は `Real.rpow` による連続 branch、`Contours` は `Real.log` / `Real.exp` を使う contour 層だった。`DkMath.FLT.PowerSwapBridge` は実際に placeholder だった。

ただし、こちらの環境には `lake` が無かったため、Lean ビルド実行まではできておらぬ。検証はソース構成と定義の静的確認じゃ。

## 英文レポートの良い点

いちばん良いのは、PowerSwap に **決定可能比較を背負わせすぎない** と明確に切った点じゃ。

PowerSwap は冪表現を揃えることはできる。しかし、揃えた後に残る `DkNNRealQ` の底比較まで自動的に決定可能にするわけではない。英文レポートはこれを、

```text
finite structural comparison       decidable
finite interval observation        decidable
proof-carrying strict comparison    constructive
full DkNNRealQ comparison           total as a proposition, not decidable
```

と分けている。これはかなり良い整理じゃ。

この区別を入れたことで、`DecidableLE DkNNRealQ` や `LinearOrder DkNNRealQ` を無理に入れる危険を避けられる。DkReal 系は、区間近似・有限観測・証明付き分離とは相性が良いが、完全等号や全順序の決定手続きとは相性が悪い。ここを見誤ると、後で設計が重くなる。

## 修正すべき点

第一に、型名を統一した方がよい。レポート前半では `DkNNRealQ` と書いているが、Phase 6 の API 例では `DkNNReal` が出てくる。

```lean
def compareAt (x y : DkNNReal) (n : Nat) : StageComparison
```

これは危ない。実装指示書では、現在の実名に合わせて一つへ統一すべきじゃ。候補は次のどちらか。

```text
DkNNRealQ が正式名なら:
  全部 DkNNRealQ に統一。

DkNNReal が代表型で DkNNRealQ が旧名なら:
  冒頭で alias / rename 方針を明記。
```

第二に、`NatPowerFrame.power` の評価定理には注意が要る。単に `[Pow α Nat]` だけでは、

\[
(a^n)^m = a^{n m}
\]

を証明するには弱い。Lean では普通、`pow_mul` を使うために `[Monoid α]` などの構造が必要になる。

したがって、Frame の定義自体は軽くてよい。

```lean
structure NatPowerFrame (α : Type u) where
  base : α
  degree : Nat
```

だが、`eval_power` 系の theorem はこう分けるべきじゃ。

```text
定義:
  [Pow α Nat] でよい。

冪法則 theorem:
  [Monoid α] など、pow_mul が使える構造を要求する。
```

第三に、`eval_lt_of_sameDegree_base_lt` は `degree != 0` より `0 < degree` を主仮定にする方が Lean で扱いやすい。

```lean
eval_lt_of_sameDegree_base_lt
    ...
    (hdpos : 0 < A.degree)
```

自然数では `degree ≠ 0` から `0 < degree` は出せるが、最初から `0 < degree` を要求した方が証明が素直じゃ。`degree = 0` の場合、どちらも \(1\) になるので strict 比較は成立しない。

第四に、軽量 import の設計をもう少し明確にするとよい。現状の `DkMath.PowerSwap` は `Branch` と `Contours` を re-export しており、`Real.log`、`Real.exp`、`Real.rpow`、filter、derivative 系まで引き込む。英文レポートは `DkMath.PowerSwap.Core` を追加する方針を書いているが、ここは強く推奨じゃ。

わっちならこう切る。

```text
DkMath.PowerSwap.Core
  Basic
  Exchange
  NormalForm
  Frame
  Normalize
  Compare
  CosmicFrame

DkMath.PowerSwap
  互換用 umbrella。
  Core + Branch + Contours を import。

DkMath.PowerSwap.Analytic
  将来、Branch / Contours をまとめる薄い入口。
```

互換性を守るなら既存 `DkMath.PowerSwap` は残す。ただし、新規 consumer は `DkMath.PowerSwap.Core` を import する。

## 実装順序のレビュー

英文レポートの推奨順序、

```text
1. Frame
2. Normalize
3. Compare
4. CosmicFrame
5. PowerSwapBridge for DkNNRealQ
6. finite StageComparison and compareUpTo
7. public import cleanup
8. consumer bridges
```

これは正しい。

ただし、Codex 用には Phase 0 を追加した方がよい。

```text
0. 現ワークスペース再確認
   - DkNNRealQ / DkNNReal の実名確認
   - CanonicalOrder の import path 確認
   - pow_le_pow 系 theorem 名確認
   - LeftSeparatedAt 相当の strict certificate 名確認
   - DkMath.lean が DkMath.PowerSwap を import している影響確認
```

ここを飛ばすと、DkReal 側の型名ズレで実装が止まる可能性がある。

## 採用すべき最小 API

次の最小核からでよい。

```lean
structure NatPowerFrame (α : Type u) where
  base : α
  degree : Nat

namespace NatPowerFrame

def eval [Pow α Nat] (A : NatPowerFrame α) : α :=
  A.base ^ A.degree

def power (A : NatPowerFrame α) (m : Nat) : NatPowerFrame α where
  base := A.base
  degree := A.degree * m

end NatPowerFrame
```

正規化 witness。

```lean
structure NormalizesTo [Pow α Nat]
    (source target : NatPowerFrame α) : Prop where
  value_eq : source.eval = target.eval
```

比較仕様。

```lean
def SameDegree (A B : NatPowerFrame α) : Prop :=
  A.degree = B.degree

structure SameDegreeComparison [LE α]
    (A B : NatPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  base_le : A.base ≤ B.base

structure SameDegreeStrictComparison [LT α]
    (A B : NatPowerFrame α) : Prop where
  same_degree : A.degree = B.degree
  degree_pos : 0 < A.degree
  base_lt : A.base < B.base
```

Cosmic frame。

```lean
structure CosmicPowerFrame (α : Type u) where
  core : α
  gap : α
  degree : Nat

namespace CosmicPowerFrame

def base [Add α] (A : CosmicPowerFrame α) : α :=
  A.core + A.gap

def eval [Add α] [Pow α Nat] (A : CosmicPowerFrame α) : α :=
  A.base ^ A.degree

def toNatPowerFrame [Add α] (A : CosmicPowerFrame α) :
    NatPowerFrame α where
  base := A.base
  degree := A.degree

end CosmicPowerFrame
```

この API なら、既存 `PowNormalForm` を壊さずに上位抽象を足せる。

## DkReal / DkNNRealQ 側との接続評価

DkReal 方向では、すでに「非負 DkReal の自然数冪は rational interval layer だけで閉じる」というマイルストーンがあり、`gapGN` による幅評価で `noncomputable` を避ける設計が立っている。これは PowerSwap bridge と非常に相性がよい。

ただし、PowerSwap bridge がやるべきことは、DkReal の内部順序を決定可能にすることではない。やるべきことは次じゃ。

```text
NatPowerFrame DkNNRealQ
  を DkNNRealQ の冪評価へ読む。

NormalizesTo
  を評価値等号へ輸送する。

SameDegreeComparison
  を pow monotonicity へ渡す。

CosmicPowerFrame
  を core + gap の base 比較へ落とす。

finite observation
  は compareAt / compareUpTo / StrictCertificate として別 API にする。
```

この分離は必須じゃ。  
PowerSwap は「正規化器」であり、「全実数比較決定器」ではない。

## 最終判定

この英文レポートは、実装計画書として **かなり良い** 。  
ただし、次の修正を入れてから Codex に渡すのが安全じゃ。

```text
採用:
  現状との差分診断。
  Frame -> Normalize -> Compare -> CosmicFrame -> Bridge の順序。
  global DecidableLE / LinearOrder を避ける方針。
  finite observation API の導入。
  既存 PowNormalForm を壊さず generic frame を足す方針。

修正:
  DkNNRealQ / DkNNReal の型名統一。
  NatPowerFrame.power の theorem には [Monoid α] などを要求。
  strict 比較は degree != 0 より 0 < degree を使う。
  lightweight Core import の目的を強める。
  Phase 0 として現ワークスペース再確認を追加。
```

わっちの最終レビューはこうじゃ。

```text
PowerSwap の山は、すでに analytic branch 側の尾根が先に伸びている。
いま登るべきは、麓からやり直す道ではない。
Nat normal form と analytic branch の間に、
Frame / Normalize / Compare / CosmicFrame という中腹の足場を入れる道じゃ。
```

これで `DkMath.PowerSwap` は、ようやく DkReal / DkNNRealQ / GN / Petal / FLT へ渡せる **冪正規化の橋** になる。

## Docs

[DkMath_PowerSwap-Implementation-Plan-and-Design](/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Implementation-Plan-and-Design.md)
[DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21](/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md)
