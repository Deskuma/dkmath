# FLT Kummer branch の設計

うむ。では、そのまま **新規 Kummer branch を切って着工できる設計書** としてまとめるぞい。
今回は、**何を branch の責務にするか**、**どこまでを abstract target にするか**、**どの順で Lean に落とすか** を、今の到達点に合わせて固定する。

いま確定している土台は次の 3 点じゃ。

* `2m-pure` は `descentExistence_iff_gnReduction` により、**descent existence そのもの** と formal に結び付いた。
* `2m-global` と `2m-pure` は一般には非同値で、その formal gap は `q | gap, q ≠ p` branch にある。
* actual DescentChain では `CyclotomicExistenceTarget` が `¬ q ∣ (z-y)` を出すので、**本線では distinguished prime 上で witness 条件が自動充足** する。したがって A ルート、すなわち `2m-global` を攻める方針は正しい。

## 1. 目的

この branch の目的は、primitive 側で最後に残った genuinely global な open content、

$$
\text{Stage 2: } z' \bmod q^p \;\longrightarrow\; z' \in \mathbb{Z}
$$

を、**Kummer 理論 / ideal class group 語彙へ抽象化して DkMath 幹線に接続すること** じゃ。
現在の解析では Stage 1 は local で concrete、Stage 2 だけが global で、そこが Kummer 側に自然に帰着すると整理されておる。

## 2. この branch でやらないこと

この branch では、いきなり全部はやらぬ。

やらないものは次の 2 つじゃ。

* いきなり \(\mathbb{Q}(\zeta_p)\) の full ideal class group を concrete に全部 formalize すること
* FLT 幹線そのものを Kummer 語彙で置き換えること

やるのは、**abstract Kummer target を置き、それが `2m-global-gap` を落とす bridge を先に作ること** じゃ。
これは戻り道のある設計で、今の DkMath 本線を壊さぬ。

## 3. 数学的な責務の切り分け

この branch で固定するべき数学像は、これじゃ。

### 3.1. 既に concrete なもの

$$
\text{Stage 1 (LOCAL)}
$$

すなわち q-adic / Hensel 的な局所 witness 供給。
これは `2m-local` が担当済みと整理されておる。

### 3.2. この branch の本丸

$$
\text{Stage 2 (GLOBAL)}
$$

すなわち、局所的に見えている descent residue から、実際の整数 \(z'\) または \(g'\) の存在へ飛ぶ部分。
ここが `2m-global` の concrete 化で最後に残る genuinely global な跳躍点じゃ。

### 3.3. classical translation

古典語彙では、

* local 側: 円分的 / q-adic witness
* global 側: ideal の \(p\) 乗性から principal \(p\) 乗性へ落とす問題
* 障害: ideal class group の \(p\)-torsion

という対応になる。
この branch は、まさにこの global 側を扱う。

## 4. branch 名とディレクトリ方針

branch 名は、わっちならこうする。

```text id="t3pe68"
feature/kummer-stage2-global
```

あるいは、もう少し DkMath 風に

```text id="s1ibfj"
feature/flt-kummer-classgroup-bridge
```

※2026/04/04 20:44 実際は `feature/flt-kummer-classgroup-bridge-260404-v0` で作成

ファイル配置は、FLT 本体に直書きせず、まず別柱を立てるのがよい。

```text id="v907p5"
lean/dk_math/DkMath/FLT/Kummer/Basic.lean
lean/dk_math/DkMath/FLT/Kummer/GapDivisibleBranch.lean
lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean
lean/dk_math/DkMath/FLT/Kummer/RegularPrimeRoute.lean
lean/dk_math/DkMathTest/FLT/Kummer/*.lean
docs/feature/flt-kummer-classgroup-bridge-<date>/History.md
```

`History.md` はこの branch の開発履歴を記録するファイルじゃ。
重要なのは、**最初は `docs/feature/flt-kummer-classgroup-bridge-<date>/History.md` を作って、そこに開発履歴を記録していくこと** じゃ。
この branch で何をやったか、どの順でやったか、どこでつまづいたか、どこで突破口が見えたか、などを、**日時と内容をセットで** で記録していくこと。
この記録は、後で振り返るときに非常に重要じゃ。

* １作業毎に日時と内容を記録していくこと。タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。
* 続けて作業する場合は、その都度、追記するカタチで更新すること。コミット単位に寄らない。

役割は次の通りじゃ。

* `Basic.lean`
  abstract target 定義と最小補題群
* `GapDivisibleBranch.lean`
  `q | (z-y), q ≠ p` branch の isolate
* `CyclotomicPrincipalization.lean`
  Kummer 的 principalization 仮定
* `ClassGroupBridge.lean`
  class-group 仮定 → principalization 仮定
* `RegularPrimeRoute.lean`
  regular-prime style 条件から FLT 幹線へ戻す橋

## 5. 新設する target

ここは branch の心臓じゃ。
最初に **定義だけ** 置く。

### 5.1. gap-divisible branch の isolate

```lean id="u9fobd"
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p
```

これは今の formal gap が集中している branch の isolate 版じゃ。
`2m-global` 全体ではなく、この branch だけを open kernel として扱う。これは今回の session の最重要整理と一致する。

### 5.2. Kummer principalization 仮定

```lean id="ywq6qg"
abbrev CyclotomicPrincipalizationTarget : Prop := 
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    Nat.Prime q →
    q ∣ x →
    q ≠ p →
    q ∣ (z - y) →
    ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p
```

最初はこれでよい。
つまり「ideal 的に見えている \(p\) 乗性が principal 化されるなら、gap-divisible branch が閉じる」と読む abstract target じゃ。

### 5.3. class-group 仮定

```lean id="cy7oqk"
abbrev CyclotomicClassGroupPTorsionFreeTarget : Prop := Prop
```

最初は中身を空でもよい。
ここでは「どういう条件から principalization が従うか」を載せる器だけを作る。
後で regular prime route へ分けてよい。

## 6. 最初に通す theorem

この branch で最初に通すべき theorem は 3 本で十分じゃ。

### 6.1. `2m-pure` の existential 版

これは本 branch でも useful じゃ。
fixed \(g'\) 版は既に通っておるので、次は存在版へ上げる。

```lean id="lmqwlz"
theorem descentExistence_exists_iff_gnReduction_exists
    (p y xq : ℕ) :
    (∃ g' : ℕ, g' * GN p g' y = xq ^ p) ↔
    (∃ z' : ℕ, z' ^ p = xq ^ p + y ^ p) := by
  ...
```

これが通ると、以後 Kummer 側では `g'` 語彙でも `z'` 語彙でも自由に書ける。

### 6.2. gap-divisible branch への bridge

```lean id="jlwmn5"
theorem qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (hKummer : CyclotomicPrincipalizationTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget := by
  ...
```

この theorem が通れば、Kummer 側の abstract 条件が primitive 幹線に刺さる。

### 6.3. class-group 仮定から principalization

```lean id="0v1otb"
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget) :
    CyclotomicPrincipalizationTarget := by
  ...
```

この theorem は最初は `by sorry` でもよい。
大事なのは **依存の向き** を先に固定することじゃ。

## 7. regular branch は先に閉じる

今回の session で、actual path では distinguished prime \(q\) が

$$
\neg q \mid (z-y)
$$

を満たすと見えた。
だから Kummer branch に入る前に、こちらは先に FLT 本線側で閉じてよい。

別ファイルでよいから、こういう theorem を入れる。

```lean id="4hxjlk"
theorem qAdicGapReductionPure_of_global_of_regularBranch
    (hGlobal : PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget := by
  ...
```

これで Kummer branch の責務は、**regular branch 以外** へ限定される。
かなり見通しが良くなるぞい。

## 8. 実装順

順番はこれでよい。

## 8.1. 第1週相当

* branch 作成
* `Basic.lean` 追加
* `GapDivisibleBranchTarget` 追加
* `CyclotomicPrincipalizationTarget` 追加
* `descentExistence_exists_iff_gnReduction_exists` 着手

## 8.2. 第2週相当

* `qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`
* テストファイル追加
* History 更新

## 8.3. 第3週以降

* `CyclotomicClassGroupPTorsionFreeTarget` の concrete meaning を詰める
* regular prime route を抽象 theorem として置く
* 必要なら円分体 / ideal / class group の concrete 化を段階的に導入

## 9. 最初の Done 条件

この branch で最初に「進んだ」と言える基準は、full class group 実装ではない。
まずは次の 3 つで十分じゃ。

### 9.1

新 target 群が導入されている。

### 9.2

`CyclotomicPrincipalizationTarget ⇒ GapDivisibleBranchTarget` が theorem として存在する。

### 9.3

`GapDivisibleBranchTarget` が既存 primitive 幹線へ接続されている。

ここまで行けば、Kummer branch は **研究メモではなく DkMath 本線に刺さる開発 branch** になる。

## 10. 設計書の短いまとめ

一文で言えば、こうじゃ。

**新規 Kummer branch の責務は、`2m-global` 全体を置き換えることではなく、`q | (z-y), q ≠ p` という gap-divisible branch だけを isolate し、その genuinely global な Stage 2 を `CyclotomicPrincipalizationTarget` と `CyclotomicClassGroupPTorsionFreeTarget` という abstract Kummer target へ接続することじゃ。**

必要なら次に、この設計書をそのまま **branch 開始用の `README.md` 雛形** に落として出すぞい。
