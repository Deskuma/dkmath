# 残る error

## 現在の残敵

```text
DkMath.RH.EulerZetaLemmas
DkMath.CosmicFormula.CosmicFormulaDim
```

`SevenRamifiedFusionCyclotomicSevenPID` を含む、数論・FLT・KUS・valuation 系の障害はすべて解消済み。残った二つは、どちらも **解析系の elaboration / instance 正規化問題**へ集中している。

## 二つは同じ種類の敵

ログに共通して現れているのは、数学的内容の失敗ではなく、同値な表現を Lean がそのまま同一視しなくなった問題じゃ。

### 関数表現

```lean
ofReal ∘ Prod.fst * Prod.snd
```

と、

```lean
fun p ↦ (p.1 : ℂ) * p.2
```

あるいは、

```lean
cexp ∘ fun u ↦ vertical σ u * Real.log p
```

と、

```lean
fun u ↦ cexp (vertical σ u * Real.log p)
```

の差。

### typeclass instance

```text
addCommGroup
instNormedAddCommGroup.toAddCommGroup
Real.instAddCommGroup
Real.normedAddCommGroup.toAddCommGroup
```

および、

```text
Semiring.toModule
RCLike.toInnerProductSpaceReal.toModule
instInnerProductSpaceRealComplex.toModule
NormedAlgebra.toNormedSpace ℂ
```

のように、数学的には同じ構造へ到達しているが、選択された instance の経路が異なる。

`EulerZetaLemmas` では特に、

```text
instContinuousSMulRealComplex_dkMath
```

という DkMath 独自 instance も goal に現れている。

これはかなり重要な信号じゃ。

## 本命原因

わっちの見立てでは、残り二つは別々に大量修正するより先に、

> **DkMath 側で定義している複素数上の scalar multiplication / normed-space instance が、新 mathlib の標準 instance と diamond を形成していないか**

を監査すべきじゃ。

特に `EulerZetaLemmas` のエラーには明示的に、

```text
instContinuousSMulRealComplex_dkMath
```

が入っている一方、実際に得られた証明項は mathlib 標準の、

```text
NormedAlgebra.toNormedSpace ℂ
```

や、

```text
RCLike.toInnerProductSpaceReal
```

を使っている。

つまり、

```text
DkMath 独自 instance
       ↘
        HasDerivAt / DifferentiableAt
       ↗
mathlib 標準 instance
```

という **解析 instance の二重経路**が発生している可能性が高い。

もし独自 instance が現在の mathlib では不要になっているなら、それを削除・局所化するだけで、両 target の多数のエラーが一斉に消える可能性がある。

## 攻略順序

### 1. 独自 instance の出所を確認

```bash
rg "instContinuousSMulRealComplex_dkMath" lean/dk_math
```

その定義が、

```lean
instance ...
```

として global 登録されているなら、まず現在の mathlib 標準 instance だけで成立するかを試す。

候補は、

```lean
local instance
```

への縮小、priority 調整、あるいは完全削除じゃ。

### 2. `EulerZetaLemmas` の最初のエラーを閉じる

最初の line 27 は比較的単純。

```lean
Continuous.mul
  (continuous_ofReal.comp continuous_fst)
  continuous_snd
```

から得た関数を、lambda 表現へ合わせればよい。

典型的には、

```lean
simpa only [Function.comp_apply, Pi.mul_apply]
```

または、

```lean
convert
  (continuous_ofReal.comp continuous_fst).mul continuous_snd using 1
```

じゃ。

ただし instance diamond が残ったままだと、後続の微分証明で再発する。

### 3. `EulerZetaLemmas` の derivative chain

残りはほぼ、

```lean
change ...
convert ... using 1
ext u
rfl
```

で composition と lambda を合わせる問題じゃ。

例えば、

```lean
have h :=
  (Complex.hasDerivAt_exp _).comp t hinner
change HasDerivAt
  (fun u ↦ Complex.exp (vertical σ u * lp))
  _ t
simpa only [Function.comp_apply] using h
```

という方向。

### 4. `CosmicFormulaDim`

こちらも同様に、`volConstC` の定義展開と pointwise 演算を明示する。

```lean
change DifferentiableAt
  (fun s ↦ Complex.exp (Complex.log π * (s / 2)) /
    Complex.Gamma (s / 2 + 1)) s
```

のように goal を証明項の表現へ合わせるか、逆に証明項側を `simpa only [volConstC, Function.comp_apply, Pi.mul_apply, Pi.div_apply]` で戻す。

`ring` の二箇所は、ログの提案どおり `ring_nf` でよい可能性が高い。

## 現在地の評価

```text
初回:
  12 failed targets

現在:
  2 failed targets

解消:
  10 targets
```

しかも残りは、

```text
RH の Euler 積解析
複素 Gamma / 次元宇宙式解析
```

という、同じ解析 instance 世界に固まった。

したがって今回の Lean 4.32.2 移行は、すでに **局所最終戦**へ入ったと見てよい。

README の現在地も、

```text
Initial failures: 12
Resolved: 10
Remaining: 2
```

へ更新できる段階じゃな。詳細報告が届いたら、`SevenRamifiedFusionCyclotomicSevenPID` の修正内容も migration pattern として正式に記録しよう。
