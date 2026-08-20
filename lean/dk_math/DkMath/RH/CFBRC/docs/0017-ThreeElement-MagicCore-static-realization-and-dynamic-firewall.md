# 0017 — ThreeElement MagicCore: static realization and dynamic firewall

## 1. この文書の目的

`0016-Cosmic-Formula-ThreeElement-general-core-and-CF2D-bridge.md` では、一般 `ThreeElement` Core の動的側を整理した。

そこでは一つの `ThreeElementFlow` が

- `core`
- `interaction`
- `gap`
- `squareMass`
- `plusWhole`
- `minusWhole`

という六つの観測を持ち、同じ flow・同じ filter・同じ target に対する `PairWholeAssimilation` が interaction を `0` へ強制することを確認した。

本書ではその静的 counterpart である

```text
DkMath.CosmicFormula.ThreeElement.MagicCore
```

を監査する。

中心となる問いは二つである。

1. 任意の非負 target `B` は、Core / interaction Beam / Gap の各形式で代数的に実現できるか。
2. その静的実現可能性から、既存の動的 flow が実際に `B` へ同化すると結論してよいか。

結論は明確である。

```text
static representability : CLOSED

dynamic assimilation    : NOT IMPLIED
```

後者を取り違えると、RH 専用側で未証明の `interaction → B` を、単なる平方根 witness から不当に供給することになる。

---

## 2. source of truth

対象 module:

```text
DkMath.CosmicFormula.ThreeElement.MagicCore
```

直接依存:

```text
DkMath.CosmicFormula.ThreeElement.Basic
```

この module は純粋な代数 witness 層であり、RH、zeta、complex phase、filter、limit を import しない。

module comment 自身も、ここで与えるものは algebraic witnesses のみであり、既存 flow の convergence を主張しないと明記している。

---

## 3. 三要素の基本形

`ThreeElement.Basic` における二次三要素は、実数の場合には次の形である。

$$
\operatorname{Core}(x)=x^2
$$

$$
\operatorname{Interaction}(x,u)=2xu
$$

$$
\operatorname{Gap}(u)=u^2
$$

ここで重要なのは、`interactionBeam` が単なる第二座標ではないことである。

```text
Vec.beam
```

は CF2D state の第二座標であり、

```text
interactionBeam x u
```

は二つの base coordinate から生成される quadratic cross term `2*x*u` である。

MagicCore が扱うのは後者である。

---

## 4. 非負 Big の Core realization

任意の `B : ℝ` に対して `0 ≤ B` とする。

Core form は平方なので、canonical witness は `sqrt B` である。

Lean theorem:

```lean
core_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    coreTerm (Real.sqrt B) = B
```

数学的には、

$$
(\sqrt B)^2=B
$$

をそのまま `coreTerm` に読んだだけである。

したがって、非負 target は常に Core form で静的に表現可能である。

この事実は target の存在可能性を示すが、ある動的 sequence `x_k` が `sqrt B` へ近づくことを意味しない。

---

## 5. 非負 Big の Gap realization

Gap form も同じ平方形なので、同じ `sqrt B` が canonical witness になる。

Lean theorem:

```lean
gap_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    gapTerm (Real.sqrt B) = B
```

数学的には、

$$
(\sqrt B)^2=B
$$

である。

したがって静的な algebraic shape としては、Core と Gap は同じ target `B` をそれぞれ単独で担うことができる。

ただしこれは、同じ有限状態で

```text
Core = Gap = B
```

が要求されるという意味ではない。

Core と Gap は semantic role が異なる。

`coreTerm_eq_gapTerm_same_input` が同じ polynomial form を持つことを示しても、二つの役割や状態を同一視してはならない。

---

## 6. interaction Beam の symmetric realization

interaction Beam は

$$
2xu
$$

なので、Core や Gap のように単一平方ではない。

しかし symmetric witness

$$
x=u=\sqrt{\frac B2}
$$

を選べば、

$$
2xu
=2\left(\sqrt{\frac B2}\right)^2
=B
$$

となる。

Lean theorem:

```lean
symmetric_interaction_sqrt_realizes
    {B : ℝ} (hB : 0 ≤ B) :
    interactionBeam
      (Real.sqrt (B / 2))
      (Real.sqrt (B / 2)) = B
```

これは DkMath で「interaction Beam も Big 全量を内部表現できる」と語るときの正確な代数核である。

ただし、ここでも主張は存在 witness に限られる。

```text
there exists / canonical witness exists
```

と

```text
the actual interaction observation of my flow tends to B
```

は全く別の命題である。

---

## 7. `SymmetricMagicCoreRealization`

三つの canonical witness は一つの structure にまとめられている。

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

そして非負 target に対して、

```lean
symmetricMagicCoreRealization
    (B : ℝ) (hB : 0 ≤ B) :
    SymmetricMagicCoreRealization B
```

が canonical package を構成する。

具体的な root は、

```text
coreRoot        = sqrt B
interactionRoot = sqrt (B / 2)
gapRoot         = sqrt B
```

である。

これは三要素すべてが同じ target `B` に対して algebraic realization を持つことを、型として一つに束ねたものと言える。

---

## 8. 「魔核」の正確な意味

DkMath の語彙でこの structure を「MagicCore」と呼ぶ場合、数学的には次の意味に限定して読むべきである。

```text
一つの非負 target B が、
Core form / interaction form / Gap form の
それぞれに canonical internal witness を持つ。
```

したがって MagicCore は、

```text
Big を各要素形で再表現可能である
```

ことを表す。

これは通常の有限分解

$$
\operatorname{plusWhole}
=
\operatorname{Core}
+
\operatorname{Interaction}
+
\operatorname{Gap}
$$

とは別の statement である。

有限分解は、一つの状態 `(x,u)` の三項が足し合わされて whole を作る exact identity である。

MagicCore realization は、target `B` に対して各 element form がそれぞれ別の canonical witness を持つという existence statement である。

よって、

```text
Core + Interaction + Gap = Big
```

から

```text
Core = Big
Interaction = Big
Gap = Big
```

を同じ状態について同時に結論してはならない。

---

## 9. dynamic firewall

この module で最も重要な監査点は、source comment が明示している次の boundary である。

```text
MagicCore supplies algebraic witnesses only.
It does not assert that an existing flow converges to them.
```

実際、`SymmetricMagicCoreRealization` には `Filter.Tendsto` field が存在しない。

したがって、次のような推論は不正である。

```text
B ≥ 0
→ interactionBeam (sqrt(B/2)) (sqrt(B/2)) = B
→ arbitrary existing flow.interaction → B
```

最後の矢印は全く供給されていない。

動的同化を主張したければ、`ThreeElement.Assimilation` の

```lean
InteractionAssimilation F l B
```

を、その具体的 `F`, `l`, `B` について独立に構成しなければならない。

---

## 10. RH bridge での意味

`0015` で確認した RH 専用 three-element bridge では、off-critical hypothetical zero に対する concrete flow

```text
etaCriticalMirrorDominantLocalThreeElementFlow s
```

と非零 target

```text
etaCriticalMirrorDominantLocalThreeElementTarget s
```

が定義されている。

そこで無条件に閉じているものは、

```text
PairWholeAssimilation                         : CLOSED
NonzeroTargetProvider                        : CLOSED
squareMass → explicit nonzero target          : CLOSED
```

である。

一方、未解決の load-bearing provider は、

```text
InteractionAssimilation
```

である。

MagicCore は、この target が interaction form で**表現可能**であることの一般代数的背景を与える。

しかし concrete RH flow の interaction sequence が実際にその target へ収束することは証明しない。

ここを混同すると、

```text
static realization
```

を

```text
dynamic assimilation
```

へすり替えることになり、RH-equivalent provider を暗黙に仮定する循環となる。

---

## 11. same-object collision との関係

一般 collision theorem は、同じ `ThreeElementFlow F`、同じ filter `l`、同じ target `B` に対して、

```text
PairWholeAssimilation F l B
InteractionAssimilation F l B
B ≠ 0
```

が揃えば contradiction を得る。

ここで MagicCore が供給するのは、`B` が interaction form に algebraically realizable であるという静的 fact だけである。

collision に必要なのは、同じ actual observation

```text
F.interaction
```

の limit theorem である。

したがって、same-object 原則を守るなら、MagicCore witness の interactionRoot と RH flow の各時点の `(core, beam)` を暗黙に同一視してはならない。

これは非常に重要な firewall である。

---

## 12. Core / Beam / Gap audit

### Core

以下は一般数学として Lean-proven。

```text
B ≥ 0
→ coreTerm (sqrt B) = B

B ≥ 0
→ gapTerm (sqrt B) = B

B ≥ 0
→ interactionBeam (sqrt(B/2)) (sqrt(B/2)) = B

B ≥ 0
→ SymmetricMagicCoreRealization B
```

### Beam

MagicCore の静的 witness と、具体的応用の dynamic flow の間に、別途 assimilation theorem を置くという設計。

### Gap

具体的 flow について、

```text
interaction observation → target B
```

を何から導くか。

MagicCore はこの Gap を埋めない。

### Obstruction

```text
static representability
≠
dynamic convergence
```

この区別を破る推論は不正。

---

## 13. 重要な比較表

| 概念 | 内容 | MagicCore が供給するか |
|---|---|---|
| `coreTerm x = B` witness | 静的代数表現 | Yes |
| `interactionBeam x x = B` witness | 静的代数表現 | Yes |
| `gapTerm u = B` witness | 静的代数表現 | Yes |
| `F.core → B` | 動的極限 | No |
| `F.interaction → B` | 動的極限 | No |
| `F.gap → B` | 動的極限 | No |
| `PairWholeAssimilation F l B` | 動的 whole 同化 | No |
| `InteractionAssimilation F l B` | 動的 interaction 同化 | No |
| same-object collision | 動的 collision theorem | 別 module |

---

## 14. 数学的解釈

MagicCore の意義は「三要素がすでに同化済み」ということではない。

より正確には、

> 非負保存 target `B` に対して、Core / interaction / Gap のどの algebraic channel にも `B` を担う内部状態が存在する。

という statement である。

したがって研究課題は、representation の存在ではなく、

> 実際の source-derived flow がどの channel へ動的に同化するか。

へ移る。

この違いは RH route で本質的である。

RH bridge では pair-whole 側が `interaction → 0` を強制するため、独立な source が同じ interaction を nonzero `B` へ同化させれば same-object collision が完成する。

MagicCore はその nonzero target が algebraically nonsensical ではないことを示すが、その independent source の役割を代替しない。

---

## 15. 現在地

一般 ThreeElement 系をここまで整理すると、層は次のように分離される。

```text
ThreeElement.Basic
  finite exact algebra
        ↓
ThreeElement.MagicCore
  static target realizability
        ↓
ThreeElement.Assimilation
  dynamic same-flow limits
        ↓
ThreeElement.Collision
  same-object nonzero collision
        ↓
CF2D.ThreeElementBridge
  CF2D q2 / conjugation transport
        ↓
RH-specific bridge
  concrete source providers
```

この依存順を守る限り、静的 witness を RH の動的 provider と取り違える危険はない。

---

## 16. 次の文書への接続

次に自然なのは、一般 `ThreeElement` 系をもう一段広い DkMath 原型へ戻し、

```text
CoreBeamGap
Big = Body + Gap
Body = Core + Beam
```

と `ThreeElement` 二次特殊化の関係を整理することである。

これにより、

```text
Cosmic Formula general-degree decomposition
        ↓
quadratic ThreeElement specialization
        ↓
CF2D q2 / conjugation
        ↓
RH carrier
```

という一般度数から RH 具体化までの依存鎖が一本になる。
