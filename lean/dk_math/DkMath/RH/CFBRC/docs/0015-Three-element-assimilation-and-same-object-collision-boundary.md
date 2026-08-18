# 0015 — Three-element assimilation と same-object collision boundary

## 1. 目的

本書は、`0014-Completed-zeta-slope-global-line-and-dominant-Euler-half-boundary.md` で RH と論理同値まで圧縮された研究境界を、DkMath の一般 `ThreeElement` Core がどのように **same-object collision** として読み替えているかを記録する。

主対象は次の二層である。

```text
DkMath.CosmicFormula.ThreeElement.Collision
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameThreeElementAssimilationBridge
```

結論を先に述べる。

現行実装では、hypothetical nonreal off-critical zero から得られる explicit local dominant carrier について、

- pair-whole assimilation は Core として証明済み、
- target の nonzero は Core として証明済み、
- square mass が同じ target へ収束することも Core として証明済み、
- interaction assimilation は未解決 provider、
- difference whole collapse はその幾何的な代替 provider、
- interaction provider も difference-whole provider も RH と論理同値、

となっている。

したがって three-element 化は unresolved step を弱めるものではない。

それは、残る一点を

```text
same flow
+ same filter
+ same nonzero target
```

に対する forbidden collision として、構造的に露出させる役割を持つ。

---

## 2. 一般 ThreeElement Core

`DkMath.CosmicFormula.ThreeElement.Collision` は RH や zeta に依存しない一般 theorem である。

中心定理は次である。

```lean
theorem target_eq_zero_of_pairWhole_and_interaction_assimilation
    {F : ThreeElementFlow ι}
    {l : Filter ι}
    {B : ℝ}
    (hpair : PairWholeAssimilation F l B)
    (hint : InteractionAssimilation F l B) :
    B = 0
```

この theorem の意味は単純である。

pair-whole assimilation が成立すると、同じ flow の interaction は $0$ へ収束する。

一方 interaction assimilation は、その同じ interaction が target $B$ へ収束すると要求する。

極限の一意性により、

$$
B=0
$$

が強制される。

したがって別に

```lean
hB : B ≠ 0
```

があれば矛盾する。

これが

```lean
false_of_nonzero_pairWhole_and_interaction_assimilation
```

である。

さらに、三つの義務を見失わないために

```lean
structure SameObjectCollisionObstruction
```

として package されている。

重要な audit firewall は、この theorem が

- 異なる flow、
- 異なる interaction、
- 異なる filter、
- 異なる target

を比較していないことである。

**same-object collision** とは文字通り、同じ対象に二つの incompatible asymptotic descriptions を与えることを意味する。

---

## 3. complex carrier から CF2D state へ

RH 専用 bridge では、complex carrier

```lean
z : ℂ
```

を

```lean
etaComplexCF2DState z : Vec ℝ
```

として読む。

これは実部と虚部を

```text
core = z.re
beam = z.im
```

とする CF2D state である。

そして explicit local dominant carrier から

```lean
etaCriticalMirrorDominantLocalThreeElementFlow s
```

を構成する。

ここで使う local carrier は `0012` で確認した dominant normalized endpoint を pair-left frame へ transport したものと同じ系統である。

---

## 4. explicit local limit

現行 bridge は side-aware local limit

```lean
etaCriticalMirrorDominantLocalCarrierLimit s
```

を定義する。

左側では original tail constant、右側では mirror tail constant の符号付き値が選ばれる。

この limit について、

```lean
etaCriticalMirrorDominantLocalCarrierLimit_im_eq_zero
etaCriticalMirrorDominantLocalCarrierLimit_ne_zero
etaCriticalMirrorDominantLocalCarrierLimit_re_ne_zero
```

が証明済みである。

したがって local carrier は off-critical zero の仮定下で、非零の実数方向へ asymptotically settle する。

その実部平方を target として

```lean
etaCriticalMirrorDominantLocalThreeElementTarget s
```

を定義する。

そして

```lean
etaCriticalMirrorDominantLocalThreeElementTarget_ne_zero
```

により target noncollapse が閉じている。

---

## 5. pair-whole assimilation は閉じている

一般補題

```lean
pairWholeAssimilation_of_complex_tendsto_real_limit
```

は、complex sequence が実数 limit $L$ に収束するとき、対応する CF2D flow の plus whole と minus whole がともに

$$
L.re^2
$$

へ収束することを示す。

この補題を explicit local carrier に適用して、

```lean
theorem etaCriticalMirrorThreeElementPairAssimilationProvider :
    EtaCriticalMirrorThreeElementPairAssimilationProvider
```

が証明されている。

したがって hypothetical nonreal off-critical zero の下で、pair-whole assimilation は **Core** である。

---

## 6. interaction の自然な local limit は zero

同じ real-limit input から、一般補題

```lean
interaction_tendsto_zero_of_complex_tendsto_real_limit
```

も証明されている。

CF2D state を $(x_k,y_k)$ とすれば interaction は

$$
2x_ky_k
$$

である。

local carrier は

$$
x_k\to L.re,
\qquad
y_k\to0
$$

なので、interaction は $0$ へ収束する。

ここが same-object collision の片側である。

---

## 7. missing interaction assimilation provider

一方、same-object collision を起こすには、その同じ interaction が nonzero target

```lean
etaCriticalMirrorDominantLocalThreeElementTarget s
```

へも収束する必要がある。

その義務が

```lean
def EtaCriticalMirrorThreeElementInteractionAssimilationProvider : Prop :=
  ... InteractionAssimilation
      (etaCriticalMirrorDominantLocalThreeElementFlow s)
      atTop (etaCriticalMirrorDominantLocalThreeElementTarget s)
```

である。

これは現行 Core からは証明されていない。

もしこれが与えられれば、

```lean
riemannHypothesis_of_threeElementInteractionAssimilation
```

によって RH が従う。

理由は、off-critical zero を仮定すると、同じ flow・同じ filter・同じ nonzero target に対して

```text
pair-whole assimilation
interaction assimilation
nonzero target
```

が同時に成立し、generic same-object collision theorem に反するからである。

---

## 8. difference whole collapse という幾何形

interaction provider の代わりに、より幾何的な form として

```lean
def EtaCriticalMirrorThreeElementDifferenceWholeCollapseProvider : Prop :=
  ... Tendsto
      (etaCriticalMirrorDominantLocalThreeElementFlow s).minusWhole
      atTop (nhds 0)
```

が定義されている。

ここで minus whole は、CF2D の core と beam の差を使う whole であり、概念的には

$$
(core-beam)^2
$$

に対応する。

同時に square mass は explicit nonzero target へ収束することが

```lean
etaCriticalMirrorDominantLocalThreeElementFlow_squareMass_tendsto_target
```

で証明済みである。

そのため minus whole が $0$ へ collapse すれば、square mass との差から interaction が target へ assimilate する。

これが

```lean
etaCriticalMirrorThreeElementInteractionAssimilationProvider_of_differenceWholeCollapse
```

である。

つまり difference-whole collapse は missing interaction provider の幾何的読み替えである。

---

## 9. RH-equivalence audit

現行 bridge はさらに一歩進み、

```lean
theorem etaCriticalMirrorThreeElementInteractionAssimilationProvider_iff_riemannHypothesis :
    EtaCriticalMirrorThreeElementInteractionAssimilationProvider ↔
      RiemannHypothesis
```

および

```lean
theorem etaCriticalMirrorThreeElementDifferenceWholeCollapseProvider_iff_riemannHypothesis :
    EtaCriticalMirrorThreeElementDifferenceWholeCollapseProvider ↔
      RiemannHypothesis
```

を証明している。

したがってこの二つは、独立に弱い補題ではない。

それらをそのまま仮定して collision を閉じても、RH を仮定して RH を得ることと論理的には同じである。

この audit は非常に重要である。

three-element representation は、remaining Gap を隠していない。

むしろ、

```text
pair side        : CLOSED
nonzero target   : CLOSED
interaction side : RH-EQUIVALENT OPEN BOUNDARY
```

と、未解決箇所を一点へ圧縮している。

---

## 10. `Big = Core + Beam + Gap` 観点での読み方

この層を DkMath の構造語彙で読むと、次のように整理できる。

### Core

- explicit dominant local carrier
- nonzero real asymptotic limit
- CF2D state 化
- pair-whole assimilation
- interaction の zero limit
- nonzero target
- square-mass target limit
- generic same-object collision theorem

### Beam

- normalized endpoint asymptoticから three-element flow への bridge
- difference whole collapse から interaction assimilation への変換
- interaction assimilation から RH contradiction への bridge

### Gap

- interaction を同じ nonzero target へ assimilate させる独立な解析的理由

または同値に、

- difference whole を $0$ へ collapse させる独立な解析的理由

### Obstruction

- pair-whole assimilation と interaction assimilation が same nonzero target で同時成立すること

これは generic theorem によって禁止されている。

---

## 11. 数学的意味

この formulation が示しているのは、単に「何かが $0$ へ行く」という話ではない。

むしろ off-critical zero を仮定すると、一つの explicit local carrier が非零 real limit を持つため、pair side は nonzero target を保持する。

その同じ対象について interaction side まで同じ target を要求できれば、

```text
interaction → 0
interaction → B ≠ 0
```

という同一対象・同一極限系の真正な衝突になる。

ここでは positive sequence tending to zero のような擬似矛盾ではない。

極限の一意性を使う same-object contradiction である。

---

## 12. 現時点の証明状態

この three-element 層だけを見ると、状態は次である。

```text
explicit local CF2D carrier                       CLOSED
local carrier → nonzero real limit               CLOSED
pair-whole assimilation                          CLOSED
nonzero target                                   CLOSED
interaction → 0 from local real limit            CLOSED
square mass → same target                        CLOSED
difference whole collapse → interaction target   CLOSED AS IMPLICATION
interaction assimilation provider                RH-EQUIVALENT OPEN BOUNDARY
difference whole collapse provider               RH-EQUIVALENT OPEN BOUNDARY
same-object collision theorem                     CLOSED
RH from interaction provider                      CLOSED AS IMPLICATION
```

したがって、three-element framework は RH を解決したのではない。

しかし unresolved theorem を「同じ nonzero target に二種類の観測が同化するか」という一つの構造問題へ正確に翻訳している。

---

## 13. 次の文書

次に追うべき自然な層は、three-element bridge の背後で使われる **CF2D three-element general Core** である。

特に、

```text
cf2dThreeElementFlow
PairWholeAssimilation
InteractionAssimilation
minusWhole
squareMass
```

の exact algebraic decomposition を確認すれば、RH 専用 bridge が一般 Cosmic Formula theorem の単なる instance であることを明確にできる。
