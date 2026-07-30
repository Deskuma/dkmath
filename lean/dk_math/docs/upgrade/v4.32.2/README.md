# DkMath Lean v4.32.2 Upgrade

## 1. 概要

本ディレクトリは、DkMath の Lean / mathlib 環境を次のバージョンへ更新する作業記録である。

```text
旧環境:
  Lean v4.29.0

新環境:
  Lean v4.32.2
```

今回の更新は、単なる新機能・新補題への追随ではない。

Lean v4.32.2 には、kernel soundness に関係する修正が含まれている。したがって本作業は、既存の DkMath 定理群を修正済み kernel 上で再検査し、ライブラリ全体を再認証する意味を持つ。

また、mathlib の更新に伴い、次の変化も想定する。

```text
- theorem / lemma API の追加・変更
- 引数順や implicit argument の変更
- simp / simpa / rw の挙動変化
- 型クラス推論の変化
- 関数表現の elaboration の厳密化
- linter と style rule の追加
- 数体、Ideal、解析系 API の更新
```

本作業は数学内容の変更を目的としない。

既存の証明内容を維持したまま、Lean v4.32.2 と対応する mathlib 上で再び全体 build を成立させることを目標とする。

---

## 2. 作業方針

この更新は、通常の数学研究 branch とは分離した upgrade 専用 branch で行う。

```text
develop
  ↓
Lean v4.32.2 upgrade branch
```

upgrade branch では、原則として次だけを扱う。

```text
- lean-toolchain の更新
- mathlib および依存 package の更新
- lake-manifest.json の更新
- Lean option の更新
- API 変更への追随
- elaboration failure の修正
- linter warning の整理
- 全体 build の再成立
```

FLT、ABC、Collatz、CosmicFormula などの数学的な新規実装は、この branch では進めない。

数学開発と version migration を混ぜず、変更理由を追跡可能な状態に保つ。

---

## 3. Lean option

Lean v4.32.2 への更新に先立ち、`lakefile.toml` の option を次の形にする。

```toml
[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
weak.linter.style.header = false
```

特に重要なのは次である。

```toml
weak.linter.style.header = false
```

DkMath は mathlib 本体への統合を目的としない独立プロジェクトである。

そのため、mathlib standard header に関する次の警告は upgrade 判定の対象外とする。

```text
- license header の形式
- copyright 表記
- Authors 表記
- header の配置
- mathlib upstream 向け style
```

DkMath 独自の license / author 記述は維持する。

header warning を先に無効化することで、API 変更、型クラス推論、elaboration、kernel 再検査など、本当に確認すべき migration failure を明確にする。

---

## 4. 初回 build

Lean v4.32.2 環境への更新後、DkMath 全体 build を実行した。

```bash
lake build
```

初回 build は全体で次の規模となった。

```text
total jobs:
  9318
```

大部分の target は正常に build された。

最終的に失敗した required target は 12 件である。

```text
1.  DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID
2.  DkMath.DHNT.DHNT_Base
3.  DkMath.ABC.PadicValNat
4.  DkMath.CosmicFormula.CosmicFormulaDim
5.  DkMath.RH.Lemmas
6.  DkMath.UnitCycle.RelPolygon
7.  DkMath.CosmicFormula.CosmicDerivativeBasic
8.  DkMath.FLT.Five.Reduction
9.  DkMath.CosmicFormula.CosmicFormulaTrominoLink
10. DkMath.NumberTheory.GdcDivD
11. DkMath.ABC.RatioBound
12. DkMath.KUS.Mul
```

したがって、今回の更新によって DkMath 全体が崩壊したわけではない。

主要モジュールの大部分は既に Lean v4.32.2 上で再検査を通過している。

特に次の大規模系列は、多くのモジュールが正常に通過した。

```text
- DkMath ABC / ABC-GN
- DkMath Collatz / PetalBridge / FloatWindow
- DkMath FLT5
- DkMath FLT7
- DkMath JacobianCounterexample3
- DkMath CosmicFormula
- DkMath Analysis / DkReal
- DkMath PrimitiveSet / Kernel
- DkMath KUS の大部分
```

現在の migration は、12 個の局所的な互換性障害を修正する段階にある。

---

## 5. 初回 failure の分類

### 5.1. 表現・簡約・定義展開の変化

次の target は、主として `simp`、`simpa`、`rw`、projection、関数表現の変化によるものと考えられる。

```text
DkMath.DHNT.DHNT_Base
DkMath.RH.Lemmas
DkMath.UnitCycle.RelPolygon
DkMath.FLT.Five.Reduction
DkMath.CosmicFormula.CosmicFormulaTrominoLink
DkMath.NumberTheory.GdcDivD
DkMath.ABC.RatioBound
DkMath.KUS.Mul
```

代表的な差異は次である。

```text
f * g
```

と、

```text
fun u ↦ f u * g u
```

の同一視。

または、

```text
g.gcd n
```

と、

```text
gcd g n
```

の表示差。

その他、structure projection や subtype の展開後に、以前の `simpa` だけでは goal が閉じなくなった箇所がある。

想定される修正手段は次である。

```lean
change ...
simpa only [...]
rw [...]
ext
rfl
```

数学的 theorem statement は維持し、必要な定義展開を明示する。

---

### 5.2. theorem API の引数変更

対象：

```text
DkMath.ABC.PadicValNat
```

初回 failure：

```text
Application type mismatch:
the argument `ha` has type `a ≠ 0`
but is expected to have type `ℕ`
in the application `padicValNat.pow d ha`
```

`padicValNat.pow` の現在の引数構造が旧環境と異なる。

現在の `#check padicValNat.pow` を確認し、named argument または新しい theorem shape に合わせる。

この問題は数学的な valuation 議論の変更ではなく、API 呼び出し方法の更新とみなす。

---

### 5.3. 解析系 elaboration の変化

対象：

```text
DkMath.CosmicFormula.CosmicFormulaDim
DkMath.CosmicFormula.CosmicDerivativeBasic
DkMath.RH.Lemmas
```

確認された問題：

```text
- DifferentiableAt の instance 表現差
- HasDerivAt の instance 表現差
- id と fun x ↦ x の差
- f * g と fun x ↦ f x * g x の差
- complex NormedSpace / Module instance の表現差
- composition と lambda 展開の差
```

これらは解析内容の変更ではなく、関数表現と型クラス instance の正規化が以前より厳密になったことによるものと考えられる。

必要に応じて次を用いる。

```lean
change ...
convert ... using 1
simpa only [...]
fun_prop
ring_nf
```

`ring` で閉じなくなった箇所については、Lean 自身が `ring_nf` を提案している。

---

### 5.4. 数体・Ideal API

対象：

```text
DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID
```

主な failure：

```text
failed to synthesize instance of type class
  CommRing ↥P
```

加えて、素数 `2` および `3` に関する residue degree / order の証明箇所で metavariable が未解決となっている。

```text
⊢ ?m % 2 = 1

⊢ ¬3 ∣ ?m
```

この target は初回 failure の中で最も重い。

関連する可能性がある範囲：

```text
- Ideal subtype
- prime ideal
- LiesOver
- residue field
- quotient ring
- number field
- cyclotomic extension
- Minkowski bound
- class number
```

mathlib の Ideal / NumberField API の変更を調査し、他の軽微な migration failure と分離して修正する。

---

## 6. 修正順序

依存関係と難度を考慮し、次の順序で修正する。

### Phase 1 — 小規模な表現修正

```text
DkMath.DHNT.DHNT_Base
DkMath.RH.Lemmas
DkMath.UnitCycle.RelPolygon
DkMath.FLT.Five.Reduction
DkMath.CosmicFormula.CosmicFormulaTrominoLink
DkMath.NumberTheory.GdcDivD
DkMath.ABC.RatioBound
DkMath.KUS.Mul
```

### Phase 2 — valuation API

```text
DkMath.ABC.PadicValNat
```

### Phase 3 — 解析系

```text
DkMath.CosmicFormula.CosmicDerivativeBasic
DkMath.CosmicFormula.CosmicFormulaDim
```

### Phase 4 — 数体・Ideal 系

```text
DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID
```

### Phase 5 — 全体再 build

```bash
lake build
```

すべての required target が成功するまで繰り返す。

---

## 7. warning の扱い

初回 build では、error 以外にも新しい linter warning が確認された。

例：

```text
Definition `succ_sub_self` is a proposition;
use `theorem` instead of `def`
```

```text
try `simp` instead of `simpa`
```

```text
Variable name `hd0` is not explicitly referenced
```

これらは migration failure とは分離する。

優先順位は次の通り。

```text
1. build error の解消
2. 全体 build の成立
3. theorem の再認証
4. linter warning の整理
```

`defProp`、`unnecessarySimpa`、`unusedVariables` などは、全体 build が成立した後に別 checkpoint として処理する。

警告を無条件に無効化するのではなく、DkMath にとって意味のある警告かを個別に判断する。

---

## 8. dependency build の warning

ProofWidgets の JavaScript dependency build 中に、npm audit warning が出力された。

```text
10 vulnerabilities
  4 moderate
  6 high
```

また、次の dependency warning も確認された。

```text
glob
three-mesh-bvh
mathjax-full
fsevents install script
circular dependencies
```

これらは ProofWidgets 側の依存 package に由来する。

DkMath の Lean source failure とは分離し、今回の Lean migration の直接的な blocker にはしない。

`npm audit fix --force` は breaking change を伴う可能性があるため、DkMath 側から独断では実行しない。

---

## 9. 完了条件

Lean v4.32.2 upgrade の完了条件は次である。

```text
- lean-toolchain が v4.32.2
- mathlib と依存 package が対応 version
- lake-manifest.json が更新済み
- 全 required target が build 成功
- DkMath 全体 build が成功
- migration による新規 sorry / admit / axiom がない
- 既存 theorem statement の意味が維持されている
- 主要公開 facade が正常に build される
- git diff --check が成功
```

追加確認対象：

```text
DkMath
DkMath.ABC
DkMath.FLT
DkMath.FLT.Five
DkMath.FLT.Seven
DkMath.Collatz.PetalBridge
DkMath.Hackathon.JacobianCounterexample3
DkMath.CosmicFormula
DkMath.Analysis
DkMath.KUS
```

---

## 10. 現在地

```text
Lean v4.32.2 toolchain update:
  complete

mathlib / dependency update:
  complete

initial full build:
  complete

total failed required targets:
  12

migration fixes:
  in progress
```

現在は、初回 build で判明した 12 target の互換性障害を順に修正する段階である。

本 upgrade は実行可能と判断する。

DkMath の大部分は既に Lean v4.32.2 上で再認証されており、残っている問題は局所的な API / elaboration / instance resolution の差異に限定されている。

---

## 11. Initial build log

初回 build log は、同ディレクトリ内に保存する。

ファイル名：

```text
Lean4-v4_32_2-1st_build.log
```

このログを upgrade の基準点とし、各修正 checkpoint で failure 数と内容の変化を追跡する。
