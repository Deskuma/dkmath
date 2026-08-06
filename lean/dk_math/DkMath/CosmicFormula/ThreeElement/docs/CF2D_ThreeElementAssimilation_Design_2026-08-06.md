# CF2D 三要素同化・宇宙式極限 実装設計書

実装完了: 2026/08/06 19:38
マージ: `develop`

作成日: 2026-08-06
正本言語: 日本語
対象 repository: `Deskuma/dkmath`
推奨作業 branch: `feature/CF2D-three-element-assimilation-260806-v0`
推奨派生元: 最新 `develop`

---

## 0. 文書の目的

本設計書は、Core・Beam・Gap の三要素が保存総量 Big の内部状態として振る舞い、状態遷移または極限によって各要素が Big 全量を担う「同化・魔核化」を Lean 4 で形式化するための実装計画である。

この理論は RH 専用にしない。最初に一般の宇宙式・CF2D ライブラリとして構築し、RH、ゼータ関数、Collatz、FLT、保存量を持つ離散力学などへの接続は、別の応用 bridge として実装する。

本実装が狙うのは、単なる二項展開の証明ではない。次の意味を明確に分離する。

1. 有限状態における三要素の exact decomposition
2. 任意の非負 Big が各要素形で表現できる静的実現可能性
3. 数列・流れが各要素の Big 状態へ近づく動的同化
4. 同じ対象が相反する同化先を要求されたときの same-object collision
5. CF2D の `q2_star` 保存則との接続
6. 個別問題が同化条件を供給する application provider

---

## 1. 実装目的

### 1.1 一般目的

二成分状態 `(x,u)` に付随する量を次のように分ける。

- Core term: `x^2`
- interaction Beam term: `2*x*u`
- Gap term: `u^2`
- square mass: `x^2 + u^2`
- plus whole: `(x+u)^2`
- minus whole: `(x-u)^2`

有限状態では次が exact に成立する。

```text
plus whole
  = Core + interaction Beam + Gap

minus whole
  = Core - interaction Beam + Gap

square mass
  = Core + Gap
```

plus whole と minus whole の差は interaction Beam を抽出する。

```text
plus whole - minus whole
  = 2 * interaction Beam
```

plus whole と minus whole の平均は square mass を抽出する。

```text
(plus whole + minus whole) / 2
  = square mass
```

この構造を、環上の多項式恒等式と実数上の極限定理に分けて形式化する。

### 1.2 動的目的

同じ target Big `B` に対して plus whole と minus whole がともに収束するなら、両者の差はゼロへ収束する。従って interaction Beam もゼロへ収束する。

一方、同じ interaction Beam が Big `B` へ同化すると証明されるなら、極限一意性から `B = 0` が導かれる。さらに `B ≠ 0` があれば矛盾となる。

この collision は次の形である。

```text
plus whole  → B
minus whole → B
────────────────
interaction Beam → 0

interaction Beam → B
────────────────────
B = 0

B ≠ 0
─────
False
```

重要なのは、すべてが同じ interaction Beam 列、同じ filter、同じ target Big を参照することである。

### 1.3 CF2D 接続目的

既存 CF2D の `Vec R` は `(core, beam)` の二成分状態を持ち、`Vec.q2` は `core^2 + beam^2` を表す。`Vec.star` と `Vec.q2_star` により、square mass の乗法保存が既に形式化されている。

新実装では `Vec.core` と `Vec.beam` を二つの基底値として読み、interaction Beam を `2 * z.core * z.beam` と定義する。

ここで名称衝突を避けるため、Lean コード上では次の呼び分けを徹底する。

```text
Vec.beam
  CF2D の第二座標

interactionBeam
  Core 座標と Beam 座標の公差項 2*x*u
```

---

## 2. 意味の分離

### 2.1 有限分解

有限分解は、多項式恒等式である。

```text
(x+u)^2 = x^2 + 2*x*u + u^2
(x-u)^2 = x^2 - 2*x*u + u^2
```

ここでは Core、interaction Beam、Gap は plus whole または minus whole を構成する項である。

### 2.2 静的魔核表現

非負実数 `B` に対し、各要素形は Big `B` を単独で表現できる。

```text
Core form:
  (sqrt B)^2 = B

Gap form:
  (sqrt B)^2 = B

interaction Beam form:
  2 * sqrt(B/2) * sqrt(B/2) = B
```

これは「表現可能である」という存在証明であり、実際の数列がその状態へ近づくことを意味しない。

### 2.3 動的同化

動的同化は `Tendsto` による極限命題である。

```text
Core assimilation:
  coreTerm k → B

Gap assimilation:
  gapTerm k → B

interaction Beam assimilation:
  interactionBeam k → B
```

静的魔核表現から動的同化を自動的に導いてはならない。実際の application は、同化を生む独立した構造、対称性、再帰、cycle schedule、保存則などを供給しなければならない。

### 2.4 Big の三つの用法

「Big」という語を Lean 名で過剰使用しない。次の三つを分ける。

```text
squareMass:
  Core + Gap
  CF2D の q2 に対応する保存平方量

plusWhole / minusWhole:
  squareMass ± interactionBeam
  正負二つの観測全体

targetBig:
  極限先として指定される意味値 B
```

概念上はいずれも Big の状態として読めるが、Lean 上では別名にして型誤認を防ぐ。

### 2.5 同時等式と状態遷移

`coreTerm = gapTerm = targetBig` を同一有限状態へ要求しない。

本理論が表すのは次である。

```text
Core chart の終端:
  Core が target Big を担う

Gap chart の終端:
  Gap が target Big を担う

interaction chart の終端:
  interaction Beam が target Big を担う
```

各 chart は同じ保存核の異なる観測状態であり、同一時点の三項同時等式とは限らない。

---

## 3. 非目標

一般 Core 実装では次を行わない。

- RH やリーマンゼータ関数を import しない
- `NontrivialRiemannZetaZero` を定義や仮定に含めない
- `Complex.arg`、偏角、三角関数を用いない
- 既存 `Rotation`／`Transverse` 名の一括変更を行わない
- 静的な平方根 witness だけから動的同化を主張しない
- `eventually positive` と `tends to zero` だけを矛盾とみなさない
- 異なる列、異なる index shift、異なる filter の極限を同一視しない
- Big の非零性を暗黙に仮定しない
- RH と同値な既存 contract を一般 theorem の証明に利用しない

---

## 4. 推奨モジュール構成

```text
DkMath/
  CosmicFormula/
    ThreeElement/
      Basic.lean
      MagicCore.lean
      Assimilation.lean
      Collision.lean
    Rotation/
      CF2D/
        ThreeElementBridge.lean
    docs/
      ThreeElementAssimilation-Design.md

DkMathTest/
  CosmicFormula/
    ThreeElement/
      Basic.lean
      MagicCore.lean
      Assimilation.lean
      Collision.lean
    Rotation/
      CF2D/
        ThreeElementBridge.lean
```

### 4.1 import 境界

`ThreeElement.Basic`:

```lean
import Mathlib
```

可能なら安定後に import を絞る。

`ThreeElement.MagicCore`:

```lean
import DkMath.CosmicFormula.ThreeElement.Basic
```

`ThreeElement.Assimilation`:

```lean
import DkMath.CosmicFormula.ThreeElement.Basic
import DkMath.Analysis.DkLimit
```

`ThreeElement.Collision`:

```lean
import DkMath.CosmicFormula.ThreeElement.Assimilation
```

`CF2D.ThreeElementBridge`:

```lean
import DkMath.CosmicFormula.ThreeElement.Collision
import DkMath.CosmicFormula.Rotation.CF2D.Basic
```

一般 Core から RH 方向への import は禁止する。

---

## 5. Phase A: 純代数 Core

### 5.1 具体状態

最初は抽象 structure を増やしすぎず、二つの基底値から定義する。

```lean
namespace DkMath.CosmicFormula.ThreeElement

variable {R : Type*}

def coreTerm [Semiring R] (x : R) : R :=
  x ^ 2

def interactionBeam [Semiring R] (x u : R) : R :=
  2 * x * u

def gapTerm [Semiring R] (u : R) : R :=
  u ^ 2

def squareMass [Semiring R] (x u : R) : R :=
  coreTerm x + gapTerm u

def plusWhole [Semiring R] (x u : R) : R :=
  (x + u) ^ 2

def minusWhole [Ring R] (x u : R) : R :=
  (x - u) ^ 2
```

### 5.2 必須 theorem

```lean
theorem plusWhole_eq_core_add_beam_add_gap
    [CommSemiring R] (x u : R) :
    plusWhole x u =
      coreTerm x + interactionBeam x u + gapTerm u
```

```lean
theorem minusWhole_eq_core_sub_beam_add_gap
    [CommRing R] (x u : R) :
    minusWhole x u =
      coreTerm x - interactionBeam x u + gapTerm u
```

```lean
theorem plusWhole_sub_minusWhole_eq_two_mul_interactionBeam
    [CommRing R] (x u : R) :
    plusWhole x u - minusWhole x u =
      2 * interactionBeam x u
```

```lean
theorem plusWhole_add_minusWhole_eq_two_mul_squareMass
    [CommRing R] (x u : R) :
    plusWhole x u + minusWhole x u =
      2 * squareMass x u
```

```lean
theorem squareMass_swap
    [CommSemiring R] (x u : R) :
    squareMass x u = squareMass u x
```

```lean
theorem interactionBeam_swap
    [CommSemiring R] (x u : R) :
    interactionBeam x u = interactionBeam u x
```

```lean
theorem core_gap_swap
    [Semiring R] (x u : R) :
    coreTerm x = gapTerm x
```

最後の theorem は名前を慎重にする。Core と Gap は役割が異なるが、同じ引数を与えたときの式形が同じであることだけを表す。状態上の同一視ではない。

### 5.3 受入条件

- 全 theorem が `sorry` なし
- `ring` または `ring_nf` で証明可能
- topology、limit、RH、Complex を import しない
- `#print axioms` で追加公理なし
- test では `ℤ`、`ℚ`、`ℝ` の例を置く

---

## 6. Phase B: 静的魔核表現

### 6.1 目的

非負 `B : ℝ` が Core、interaction Beam、Gap の各形式で実現可能であることを witness 付きで示す。

### 6.2 定義候補

```lean
structure MagicCoreRealization (B : ℝ) where
  coreRoot : ℝ
  beamLeftRoot : ℝ
  beamRightRoot : ℝ
  gapRoot : ℝ
  core_realizes :
    coreTerm coreRoot = B
  interaction_realizes :
    interactionBeam beamLeftRoot beamRightRoot = B
  gap_realizes :
    gapTerm gapRoot = B
```

equal-root Beam を正本にするなら、より狭い構造でもよい。

```lean
structure SymmetricMagicCoreRealization (B : ℝ) where
  coreRoot : ℝ
  interactionRoot : ℝ
  gapRoot : ℝ
  core_realizes :
    coreTerm coreRoot = B
  interaction_realizes :
    interactionBeam interactionRoot interactionRoot = B
  gap_realizes :
    gapTerm gapRoot = B
```

### 6.3 必須 theorem

```lean
theorem core_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    coreTerm (Real.sqrt B) = B
```

```lean
theorem gap_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    gapTerm (Real.sqrt B) = B
```

```lean
theorem symmetric_interaction_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    interactionBeam
      (Real.sqrt (B / 2))
      (Real.sqrt (B / 2)) = B
```

```lean
def symmetricMagicCoreRealization
    (B : ℝ) (hB : 0 ≤ B) :
    SymmetricMagicCoreRealization B
```

### 6.4 監査 theorem

静的実現可能性が動的同化を意味しないことを型設計で守る。`MagicCoreRealization` に `Tendsto` field を入れない。

ドキュメントコメントに次を明記する。

```text
This structure supplies algebraic witnesses only.
It does not assert that an existing flow converges to these witnesses.
```

---

## 7. Phase C: 動的同化極限

### 7.1 一般 flow

index 型と filter を一般化し、値域は最初は `ℝ` に固定する。

```lean
structure ThreeElementFlow (ι : Type*) where
  core : ι → ℝ
  interaction : ι → ℝ
  gap : ι → ℝ
  squareMass : ι → ℝ
  plusWhole : ι → ℝ
  minusWhole : ι → ℝ

  squareMass_eq :
    ∀ i, squareMass i = core i + gap i

  plusWhole_eq :
    ∀ i, plusWhole i = squareMass i + interaction i

  minusWhole_eq :
    ∀ i, minusWhole i = squareMass i - interaction i
```

具体的な二乗状態から flow を作る constructor を別に置く。

```lean
def quadraticFlow
    {ι : Type*} (x u : ι → ℝ) :
    ThreeElementFlow ι
```

### 7.2 同化 provider

正負 whole の同化と interaction の同化を分ける。

```lean
structure PairWholeAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  plus_tendsto :
    Filter.Tendsto F.plusWhole l (nhds B)
  minus_tendsto :
    Filter.Tendsto F.minusWhole l (nhds B)
```

```lean
structure InteractionAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  interaction_tendsto :
    Filter.Tendsto F.interaction l (nhds B)
```

必要に応じて Core／Gap provider も追加するが、Phase C の最小実装では後回しでよい。

### 7.3 必須 theorem

```lean
theorem interaction_tendsto_zero_of_pairWholeAssimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {B : ℝ}
    (h : PairWholeAssimilation F l B) :
    Filter.Tendsto F.interaction l (nhds 0)
```

証明は `plusWhole - minusWhole = 2 * interaction` を用いる。flow の fields から exact identity を先に得る。

```lean
theorem plusWhole_sub_minusWhole_eq_two_mul_interaction
    (F : ThreeElementFlow ι) (i : ι) :
    F.plusWhole i - F.minusWhole i =
      2 * F.interaction i
```

同じ interaction が `0` と `B` の双方へ収束するなら、極限一意性から `B = 0`。

```lean
theorem target_eq_zero_of_pairWhole_and_interaction_assimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [NeBot l]
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B) :
    B = 0
```

非零 Big なら collision。

```lean
theorem false_of_nonzero_pairWhole_and_interaction_assimilation
    {ι : Type*}
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    [NeBot l]
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B)
    (hB : B ≠ 0) :
    False
```

### 7.4 補助 theorem

```lean
theorem squareMass_tendsto_of_core_gap
```

```lean
theorem plusWhole_tendsto_of_squareMass_interaction
```

```lean
theorem minusWhole_tendsto_of_squareMass_interaction
```

```lean
theorem core_tendsto_big_of_squareMass_and_gap_zero
```

```lean
theorem gap_tendsto_big_of_squareMass_and_core_zero
```

これらは「消えた量が失われる」のではなく、保存総量が残る要素へ同化することを表す基本 API になる。

### 7.5 DkLimit との関係

Core theorem は Mathlib の `Filter.Tendsto` を正本にする。

次の convenience wrapper は、一般 theorem が Green になった後に追加する。

```lean
theorem interaction_dkTendstoAtTop_zero_of_pairAssimilation
```

```lean
theorem interaction_dkGapCollapsesTo_zero_of_pairAssimilation
```

既存 `DkLimit` は語彙ラッパーであり、新理論を `DkLimit.lean` 内へ直接書かない。

---

## 8. Phase D: CF2D bridge

### 8.1 状態変換

```lean
def ofCF2DVec
    (z : Rotation.CF2D.Vec ℝ) :
    ThreeElementState ℝ
```

`ThreeElementState` を作らない設計なら、直接各量を定義する。

```lean
def cf2dCoreTerm
    (z : CF2D.Vec ℝ) : ℝ :=
  z.core ^ 2

def cf2dInteractionBeam
    (z : CF2D.Vec ℝ) : ℝ :=
  2 * z.core * z.beam

def cf2dGapTerm
    (z : CF2D.Vec ℝ) : ℝ :=
  z.beam ^ 2

def cf2dPlusWhole
    (z : CF2D.Vec ℝ) : ℝ :=
  (z.core + z.beam) ^ 2

def cf2dMinusWhole
    (z : CF2D.Vec ℝ) : ℝ :=
  (z.core - z.beam) ^ 2
```

### 8.2 `q2` 接続

```lean
theorem cf2d_squareMass_eq_q2
    (z : CF2D.Vec ℝ) :
    squareMass z.core z.beam =
      CF2D.Vec.q2 z
```

```lean
theorem cf2d_q2_act_preserved
    (r : CF2D.UnitKernel ℝ)
    (z : CF2D.Vec ℝ) :
    squareMass
      (CF2D.UnitKernel.act r z).core
      (CF2D.UnitKernel.act r z).beam =
    squareMass z.core z.beam
```

これは既存 `UnitKernel.q2_act` から導く。

### 8.3 conjugation と正負 branch

CF2D conjugation は第二座標の符号を反転するため、interaction Beam の符号だけが反転する。

```lean
theorem cf2dInteractionBeam_conj
    (z : CF2D.Vec ℝ) :
    cf2dInteractionBeam (CF2D.Vec.conj z) =
      -cf2dInteractionBeam z
```

```lean
theorem cf2dPlusWhole_conj_eq_minusWhole
    (z : CF2D.Vec ℝ) :
    cf2dPlusWhole (CF2D.Vec.conj z) =
      cf2dMinusWhole z
```

```lean
theorem cf2dMinusWhole_conj_eq_plusWhole
    (z : CF2D.Vec ℝ) :
    cf2dMinusWhole (CF2D.Vec.conj z) =
      cf2dPlusWhole z
```

これにより「正負 Big」は外部から導入された二世界ではなく、CF2D 内部の conjugate pair として生成できる。

### 8.4 CF2D flow constructor

```lean
def cf2dThreeElementFlow
    {ι : Type*}
    (z : ι → CF2D.Vec ℝ) :
    ThreeElementFlow ι
```

以後の application は実際の carrier 列 `z k` を渡すだけで、一般 collision theorem を利用できる。

---

## 9. Phase E: application provider interface

一般理論は、各問題に必要な同化を証明しない。応用側は次の provider を供給する。

### 9.1 Pair whole provider

```lean
def ProvidesPairWholeAssimilation
    {ι : Type*}
    (z : ι → CF2D.Vec ℝ)
    (l : Filter ι)
    (B : ℝ) : Prop :=
  PairWholeAssimilation (cf2dThreeElementFlow z) l B
```

意味:

```text
正状態と conjugate 負状態が同じ target Big へ同化する。
```

### 9.2 Interaction provider

```lean
def ProvidesInteractionAssimilation
    {ι : Type*}
    (z : ι → CF2D.Vec ℝ)
    (l : Filter ι)
    (B : ℝ) : Prop :=
  InteractionAssimilation (cf2dThreeElementFlow z) l B
```

意味:

```text
公差項 interaction Beam 自身が同じ target Big を担う。
```

### 9.3 Noncollapse provider

```lean
def ProvidesNonzeroTarget (B : ℝ) : Prop :=
  B ≠ 0
```

### 9.4 application closure

一般 theorem は次だけを要求する。

```lean
theorem no_nontrivial_threeElement_collision
    (hpair : ProvidesPairWholeAssimilation z l B)
    (hint : ProvidesInteractionAssimilation z l B)
    (hB : ProvidesNonzeroTarget B) :
    False
```

RH、Collatz、FLT その他は、この三 provider をどう供給するかだけを個別 module で研究する。

---

## 10. RH 応用層の扱い

RH 接続は一般 Core 完成後の別 module とする。

推奨 path:

```text
DkMath/RH/CFBRC/
  EtaCriticalMirrorPairedFrameThreeElementAssimilationBridge.lean
```

この module だけが以下を import してよい。

```text
completed-zeta carrier
critical mirror
dominant Euler half endpoint
existing noncollapse
moving-line / cycle schedule
```

RH adapter が調べる対象は二つに限定する。

```text
A. plus/minus whole assimilation provider
B. interaction Beam magic-core assimilation provider
```

一般 Core の theorem を RH と同値な既存 `TransverseCollapse` から証明してはならない。そうすると循環する。

RH adapter では `#print axioms` と import graph を必ず監査する。

---

## 11. 実装順

### Gate 0: branch と既存 API の確認

```bash
git switch develop
git pull --ff-only
git switch -c feature/CF2D-three-element-assimilation-260806-v0
```

確認対象:

```text
DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
DkMath/Analysis/DkLimit.lean
DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean
```

### Gate 1: `ThreeElement.Basic`

完了条件:

- pure algebra theorem が Green
- RH import なし
- topology import なし
- test Green

### Gate 2: `ThreeElement.MagicCore`

完了条件:

- 非負 Big の三形式 witness
- 静的表現と動的同化を型で分離
- test Green

### Gate 3: `ThreeElement.Assimilation`

完了条件:

- `ThreeElementFlow`
- pair whole assimilation
- interaction → 0 theorem
- Core／Gap 保存 collapse
- test Green

### Gate 4: `ThreeElement.Collision`

完了条件:

- same-object limit uniqueness
- target `B = 0`
- `B ≠ 0` から `False`
- `[NeBot l]` を明示
- test Green

### Gate 5: `CF2D.ThreeElementBridge`

完了条件:

- `squareMass = Vec.q2`
- unit action で square mass 保存
- conjugation で interaction のみ符号反転
- CF2D flow constructor
- test Green

### Gate 6: application experiment

一般 Core を変更せず、別 module で provider 候補を接続する。

最初の application が閉じなくても、次のいずれかとして残す。

```text
named provider gap
named obstruction
insufficient-assumption audit
```

---

## 12. テスト計画

### 12.1 代数回帰

```lean
example (x u : ℤ) :
    plusWhole x u =
      coreTerm x + interactionBeam x u + gapTerm u := by
  ...
```

```lean
example (x u : ℚ) :
    plusWhole x u - minusWhole x u =
      2 * interactionBeam x u := by
  ...
```

### 12.2 数値 witness

```lean
example :
    interactionBeam (Real.sqrt 2) (Real.sqrt 2) = 4 := by
  ...
```

### 12.3 極限回帰

明示的な例を作る。

```text
x k → sqrt B
u k → 0
```

このとき Core は `B`、interaction と Gap は `0`、plus/minus whole は `B` へ収束する。

別例:

```text
x k → sqrt(B/2)
u k → sqrt(B/2)
```

interaction は `B` へ収束するが、plus/minus whole が同じ `B` へ行くとは限らない。この例により、静的 Beam 魔核化だけでは pair assimilation が出ないことを監査する。

### 12.4 CF2D 回帰

- neutral kernel action
- conjugate action
- arbitrary unit-kernel `q2` preservation
- plus/minus conjugate exchange
- interaction sign flip

### 12.5 公理監査

各公開 theorem に対して必要に応じて次を置く。

```lean
#print axioms interaction_tendsto_zero_of_pairWholeAssimilation
#print axioms target_eq_zero_of_pairWhole_and_interaction_assimilation
#print axioms false_of_nonzero_pairWhole_and_interaction_assimilation
#print axioms cf2d_q2_act_preserved
```

---

## 13. 失敗しやすい点

### 13.1 Beam の名称衝突

`Vec.beam` と `2*x*u` を同じ Lean 名で扱わない。

推奨:

```text
Vec.beam
interactionBeam
```

### 13.2 Big の混同

`squareMass`、`plusWhole`、`minusWhole`、`targetBig` を分ける。

### 13.3 factor 2

`interactionBeam = 2*x*u` と定義した場合、

```text
plusWhole - minusWhole
  = 2 * interactionBeam
```

である。`plusWhole - minusWhole = interactionBeam` ではない。

### 13.4 同一 filter

極限一意性を使う theorem では、同じ filter `l` と `[NeBot l]` が必要。

### 13.5 index shift

応用で `k`、`k+1`、`2*k+1` などが現れる場合、eventual equality または shift theorem を明示する。

### 13.6 非零性

collision は target `B ≠ 0` がなければ `B = 0` を得るだけで矛盾ではない。

### 13.7 静的 witness の過大解釈

`sqrt` による realization は任意の `B ≥ 0` について成立するため、それ自体は特定問題を制約しない。実際の carrier がその witness 状態へ同化する theorem が別途必要。

---

## 14. 完成判定

一般理論の完成は RH の成否とは独立に判定する。

```text
Basic:
  exact algebra Green

MagicCore:
  static realizability Green

Assimilation:
  same-target pair collapse Green

Collision:
  same-object zero/nonzero collision Green

CF2D Bridge:
  q2_star / conjugation bridge Green
```

この五層が `sorry` なしなら、一般ライブラリは完成である。

その後の application は、provider の供給可否を個別に判定する。

---

## 15. 新しい会話の開始文

```text
DkMath の一般ライブラリとして CF2D 三要素同化・宇宙式極限を実装する。

Repository:
  Deskuma/dkmath

推奨 branch:
  feature/CF2D-three-element-assimilation-260806-v0

派生元:
  最新 develop

正本設計:
  CF2D_ThreeElementAssimilation_Design_2026-08-06.md

目的:
  Core、interaction Beam、Gap の exact decomposition、
  非負 Big の静的魔核表現、
  plus/minus whole の共通極限から interaction Beam → 0、
  interaction Beam → nonzero Big との same-object collision、
  CF2D q2_star / conjugation bridge
  を一般 theorem として形式化する。

重要:
  RH 専用にしない。
  DkMath.CosmicFormula.ThreeElement を一般 Core とする。
  RH、ゼータ、completed-zeta を Core から import しない。
  Complex.arg、偏角、三角関数を使わない。
  Vec.beam 座標と interactionBeam = 2*x*u を混同しない。
  squareMass、plusWhole、minusWhole、targetBig を分ける。
  静的な sqrt witness から動的同化を推論しない。
  同じ Lean object、同じ filter、同じ target 上の極限だけを衝突させる。
  target 非零性を独立に要求する。
  失敗経路は named obstruction / audit として残す。

最初に GitHub で次を確認する。
  DkMath/CosmicFormula/Rotation/CF2D/Basic.lean
  DkMath/Analysis/DkLimit.lean
  DkMath/CosmicFormula/CosmicDerivativePowerLimit.lean

実装順:
  1. ThreeElement/Basic.lean
  2. ThreeElement/MagicCore.lean
  3. ThreeElement/Assimilation.lean
  4. ThreeElement/Collision.lean
  5. Rotation/CF2D/ThreeElementBridge.lean
  6. 対応する DkMathTest

各 Gate ごとに build 対象を提示し、ユーザー環境の Green を待って次へ進む。
既存 Green 層を大改造しない。
```

---

## 16. 最終的な研究上の意味

この実装は「Beam を誤差として消す」理論ではない。

有限状態では Core、interaction Beam、Gap が whole を構成する。状態同化では、そのいずれもが target Big 全量を担う魔核表現になり得る。

plus state と minus state が同じ Big へ同化すれば、公差項 interaction Beam は相殺されてゼロへ行く。一方で interaction Beam 自身が同じ非零 Big へ魔核化すると、同じ対象に `0` と `B` の二つの極限が要求される。

この same-object collision を一般 theorem として確立することが、本設計の中心である。

個別の数学問題は、一般 collision theorem を再証明するのではなく、次の三 provider を供給する。

```text
pair whole assimilation
interaction assimilation
nonzero target
```

これにより、宇宙式の内部保存・同化・衝突機構を、特定予想から独立した DkMath の再利用可能な基盤として残す。
