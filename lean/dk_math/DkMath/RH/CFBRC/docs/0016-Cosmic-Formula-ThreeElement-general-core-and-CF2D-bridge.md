# 0016 — Cosmic Formula ThreeElement general Core と CF2D bridge

## 1. 目的

本書は、`0015-Three-element-assimilation-and-same-object-collision-boundary.md` で RH 専用 carrier に適用した three-element assimilation の一般 Core を、その依存元まで戻って整理する。

対象は主に次の三層である。

```text
DkMath.CosmicFormula.ThreeElement.Basic
DkMath.CosmicFormula.ThreeElement.Assimilation
DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
```

この層には RH、Riemann zeta、eta、complex phase、角度、三角関数の仮定は入らない。

したがってここで得られる theorem は、RH 専用の補助命題ではなく、DkMath の一般 Cosmic Formula ライブラリとして再利用可能な Core である。

---

## 2. 二つの base value から三要素を作る

`ThreeElement.Basic` は二つの値 `x` と `u` から、二次式の三要素を定義する。

```lean
def coreTerm [Semiring R] (x : R) : R :=
  x ^ 2

def interactionBeam [Semiring R] (x u : R) : R :=
  2 * x * u

def gapTerm [Semiring R] (u : R) : R :=
  u ^ 2
```

数学的には

$$
\operatorname{Core}=x^2
$$

$$
\operatorname{Interaction}=2xu
$$

$$
\operatorname{Gap}=u^2
$$

である。

ここで重要なのは `interactionBeam` が `u` そのものではないことである。

CF2D では第二座標に `beam` という名前が付くが、three-element algebra の interaction Beam は二座標から生成される cross term `2*x*u` である。

この区別は以後も維持される。

---

## 3. squareMass と plus / minus whole

三要素から次を定義する。

```lean
def squareMass [Semiring R] (x u : R) : R :=
  coreTerm x + gapTerm u


def plusWhole [Semiring R] (x u : R) : R :=
  (x + u) ^ 2


def minusWhole [Ring R] (x u : R) : R :=
  (x - u) ^ 2
```

したがって

$$
\operatorname{squareMass}=x^2+u^2
$$

であり、二つの whole は

$$
\operatorname{plusWhole}=(x+u)^2
$$

$$
\operatorname{minusWhole}=(x-u)^2
$$

となる。

Lean では exact に

```lean
theorem plusWhole_eq_core_add_beam_add_gap ...

theorem minusWhole_eq_core_sub_beam_add_gap ...
```

が証明され、

```text
plusWhole  = Core + Interaction + Gap
minusWhole = Core - Interaction + Gap
```

という符号反転構造を持つ。

これは DkMath の三要素構造の最も基本的な algebraic Core である。

---

## 4. 和と差で何が抽出されるか

二つの whole の差は interaction Beam だけを抽出する。

```lean
theorem plusWhole_sub_minusWhole_eq_two_mul_interactionBeam ...
```

すなわち

$$
\operatorname{plusWhole}-\operatorname{minusWhole}=2\operatorname{Interaction}
$$

である。

一方、和は square mass を抽出する。

```lean
theorem plusWhole_add_minusWhole_eq_two_mul_squareMass ...
```

すなわち

$$
\operatorname{plusWhole}+\operatorname{minusWhole}=2\operatorname{squareMass}
$$

となる。

このため plus / minus pair は、同一二次状態を「symmetric mass」と「antisymmetric interaction」に分解する観測対として読むことができる。

---

## 5. ThreeElementFlow

`ThreeElement.Assimilation` は静的恒等式を indexed dynamic state へ持ち上げる。

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

ここでは六つの observation を別々の field として保持し、その間の exact relation を structure に含める。

重要なのは `Big` のような一語へ全部を押し込まず、

```text
Core
Interaction
Gap
SquareMass
PlusWhole
MinusWhole
```

を明示的に区別している点である。

これは後の collision audit で「同じ object を比較しているか」を Lean の型で追跡しやすくする。

---

## 6. quadraticFlow

二つの実関数 `x,u : ι → ℝ` から標準的な flow を作る constructor が

```lean
def quadraticFlow
    {ι : Type*} (x u : ι → ℝ) :
    ThreeElementFlow ι
```

である。

各 index `i` で

```text
core        = x(i)^2
interaction = 2*x(i)*u(i)
gap         = u(i)^2
squareMass  = x(i)^2 + u(i)^2
plusWhole   = (x(i)+u(i))^2
minusWhole  = (x(i)-u(i))^2
```

を同時に記録する。

これは pure algebraic construction であり、極限や解析接続はまだ使わない。

---

## 7. PairWholeAssimilation

動的極限として最初に導入されるのが

```lean
structure PairWholeAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  plus_tendsto :
    Filter.Tendsto F.plusWhole l (nhds B)
  minus_tendsto :
    Filter.Tendsto F.minusWhole l (nhds B)
```

である。

意味は、同じ flow の plus whole と minus whole が、同じ filter に沿って同じ target `B` に収束することである。

概念的には

$$
\operatorname{plusWhole}\to B
$$

かつ

$$
\operatorname{minusWhole}\to B
$$

である。

ここで「同じ flow・同じ filter・同じ target」という条件が構造上固定される。

---

## 8. pair assimilation だけで interaction はゼロへ行く

二つの whole の差が exact に `2 * interaction` なので、pair assimilation から interaction collapse が自動的に得られる。

```lean
theorem interaction_tendsto_zero_of_pairWholeAssimilation
    ...
    (h : PairWholeAssimilation F l B) :
    Filter.Tendsto F.interaction l (nhds 0)
```

すなわち

$$
\operatorname{PairWholeAssimilation}(B)
\Longrightarrow
\operatorname{Interaction}\to0
$$

である。

この theorem は target `B` の値には依存しない。

したがって pair assimilation は「interaction が同じ `B` へ行く」ことを意味しない。

むしろ exact opposite であり、pair assimilation が与える無条件結論は interaction の zero limit である。

この distinction が `0015` の same-object collision の核となる。

---

## 9. InteractionAssimilation は独立 provider

interaction が target `B` へ収束することは別 structure として定義される。

```lean
structure InteractionAssimilation
    {ι : Type*} (F : ThreeElementFlow ι)
    (l : Filter ι) (B : ℝ) : Prop where
  interaction_tendsto :
    Filter.Tendsto F.interaction l (nhds B)
```

したがって

```text
PairWholeAssimilation F l B
```

と

```text
InteractionAssimilation F l B
```

は別の主張である。

前者から interaction は `0` へ行く。
後者では interaction は `B` へ行く。

同じ object に対して両者が成立すれば、極限の一意性から `B = 0` が強制される。

`ThreeElement.Collision` はこの一般事実を same-object collision theorem として package している。

---

## 10. squareMass / Core / Gap の極限 API

一般 Core には、個々の component limits を組み替える theorem も用意されている。

```lean
theorem squareMass_tendsto_of_core_gap ...
```

は

$$
\operatorname{Core}\to C,
\qquad
\operatorname{Gap}\to G
$$

から

$$
\operatorname{squareMass}\to C+G
$$

を与える。

また

```lean
theorem core_tendsto_big_of_squareMass_and_gap_zero ...
```

は square mass が `B` へ行き Gap が `0` へ潰れると Core が `B` へ同化することを表す。

対称的に

```lean
theorem gap_tendsto_big_of_squareMass_and_core_zero ...
```

も存在する。

ここでも target `B` は一つの observation limit であり、Core / Gap / interaction の semantic role は混同されない。

---

## 11. CF2D bridge

`DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge` は、CF2D の

```lean
Vec ℝ
```

の二座標を three-element algebra の base values として読む。

```lean
def cf2dCoreTerm (z : Vec ℝ) : ℝ :=
  coreTerm z.core


def cf2dInteractionBeam (z : Vec ℝ) : ℝ :=
  interactionBeam z.core z.beam


def cf2dGapTerm (z : Vec ℝ) : ℝ :=
  gapTerm z.beam
```

再び、`Vec.beam` と `cf2dInteractionBeam` は別物である。

```text
Vec.beam            = CF2D の第二座標
cf2dInteractionBeam = 2 * z.core * z.beam
```

この区別は load-bearing である。

---

## 12. squareMass は既存 CF2D q2 と一致する

bridge の重要 theorem は

```lean
theorem cf2d_squareMass_eq_q2 (z : Vec ℝ) :
    squareMass z.core z.beam = Vec.q2 z :=
  rfl
```

である。

つまり three-element の unsigned square mass は、新しい量ではなく既存 CF2D quadratic invariant `Vec.q2` そのものである。

したがって CF2D の既存 theorem

```text
q2_star
UnitKernel.q2_act
```

を three-element square mass へそのまま輸送できる。

実際に

```lean
theorem cf2d_squareMass_star ...

theorem cf2d_q2_act_preserved ...
```

が実装されている。

---

## 13. CF2D conjugation と interaction 符号反転

CF2D conjugation は Core と Gap を保存し、interaction Beam だけの符号を反転する。

```lean
@[simp] theorem cf2dCoreTerm_conj ...
@[simp] theorem cf2dGapTerm_conj ...
@[simp] theorem cf2dInteractionBeam_conj ...
```

したがって

```text
Core        → Core
Gap         → Gap
Interaction → -Interaction
```

となる。

その結果、plus whole と minus whole は交換される。

```lean
@[simp] theorem cf2dPlusWhole_conj_eq_minusWhole ...
@[simp] theorem cf2dMinusWhole_conj_eq_plusWhole ...
```

この構造は mirror / conjugation 系の CFBRC 応用と整合するが、この一般 bridge 自身は RH や zeta を知らない。

---

## 14. cf2dThreeElementFlow

CF2D state sequence

```lean
z : ι → Vec ℝ
```

から一般 `ThreeElementFlow` を作る入口が

```lean
def cf2dThreeElementFlow
    {ι : Type*} (z : ι → Vec ℝ) :
    ThreeElementFlow ι
```

である。

これは

```lean
quadraticFlow
  (fun i => (z i).core)
  (fun i => (z i).beam)
```

として定義される。

そのため、既存 CF2D carrier を sequence として与えるだけで、一般 assimilation / collision API を利用できる。

`0015` の RH 専用

```lean
etaCriticalMirrorDominantLocalThreeElementFlow
```

もこの bridge を通して構築されている。

---

## 15. 一般 Core と RH 専用層の境界

ここまでの一般依存関係は次のように整理できる。

```text
Two base values x,u
  ↓
ThreeElement.Basic
  Core = x^2
  Interaction = 2xu
  Gap = u^2
  ↓
plusWhole / minusWhole / squareMass
  ↓
ThreeElementFlow
  ↓
PairWholeAssimilation
  ↓
Interaction → 0
```

CF2D 側では

```text
Vec(core, beam)
  ↓
cf2dThreeElementFlow
  ↓
一般 ThreeElement API
```

となる。

この chain 全体は RH 非依存 Core である。

RH 専用になるのは、その flow に

```text
etaCriticalMirrorDominantLocalCF2DCarrier
```

を代入してからである。

---

## 16. audit 判定

### Core

次は一般 theorem として証明済みである。

```text
Core / Interaction / Gap の exact quadratic decomposition
plus / minus whole の exact identity
plus-minus difference から interaction の抽出
plus+minus sum から squareMass の抽出
ThreeElementFlow
PairWholeAssimilation
InteractionAssimilation
pair assimilation → interaction → 0
squareMass / Core / Gap の limit transport
CF2D squareMass = Vec.q2
CF2D conjugationによる interaction sign flip
cf2dThreeElementFlow bridge
```

### Gap

この一般 Core 自身には未解決数学はない。

ただし特定応用で

```text
InteractionAssimilation F l B
```

を独立に供給できるかは application-specific obligation である。

RH 応用では、この provider が `0015` で RH-equivalent と判定されている。

---

## 17. 重要な firewall

### 17.1 `Vec.beam` と interaction Beam は同一ではない

```text
Vec.beam : base coordinate
interactionBeam : 2 * core * beam
```

である。

### 17.2 pair assimilation は interaction assimilation ではない

pair assimilation が与えるのは

$$
\operatorname{Interaction}\to0
$$

であり、同じ target `B` への assimilation ではない。

### 17.3 same target が collision を作る

interaction がさらに同じ `B` へ行くとき初めて

$$
B=0
$$

が強制される。

したがって target nonzero と組み合わせて contradiction が生じる。

### 17.4 一般 Core は RH を含まない

`ThreeElement.Basic`、`Assimilation`、`CF2D.ThreeElementBridge` には RH、zeta、eta、critical line の仮定はない。

RH の難しさは一般 collision theorem ではなく、具体 carrier について missing provider を独立に供給するところにある。

---

## 18. 現時点の依存地図

```text
ThreeElement.Basic
  ↓
ThreeElement.Assimilation
  ↓
ThreeElement.Collision
  ↑
CF2D.ThreeElementBridge
  ↑
eta critical-mirror dominant local carrier
  ↓
pair assimilation + nonzero target: CLOSED
interaction assimilation: RH-equivalent boundary
```

この分離により、一般 algebra / topology と RH 固有解析の境界は明確である。

---

## 19. 次の文書への接続

次に確認すべき自然な層は、general ThreeElement Core の静的 counterpart である `MagicCore` と、その square-root / nonnegative Big 表現である。

ここを整理すると、dynamic assimilation で使われる `B` が、DkMath の「非負 Big / 魔核」語彙とどのように接続されているかを、RH から独立して説明できる。
