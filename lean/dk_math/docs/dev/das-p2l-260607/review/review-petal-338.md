# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon

gch: 39ee6aa87fedbef5d1373abbb1375f729f981cb4

## Report

(24m34s)

Checkpoint 338 を実装しました。

確定した主な事実:

- `H = 0` の frontier increment は `max (-queueBefore) endpointAccountingTerm`。
- successor drift が負なら二段和は非正、ゼロなら `1`、正なら `1 + drift`。
- `n = 123` が「successor drift ≤ 0 なら非正」という主張への反例。必要条件は厳密な負です。
- 成熟した saturated block では predecessor は carry-two にならず、`H = 1` frontier increment は常に `0`。
- horizon deficit を有限 pre-block carry carrier の濃度として正確に表現。
- uniform source-age bound と carrier の有限被覆条件を同値化。

コードは [CanonicalSourceAgeHorizon.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean)、詳細は [report-petal-338.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-338.md) に記録しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon`
- `lake build DkMath.Collatz.PetalBridge`
- no `sorry` / `admit` / `axiom`
- `git diff --check` 通過

なお、有限 carrier の構造は確定しましたが、全体を覆う horizon の存在までは主張していません。
次は reachable signature の有限化と、frontier weight がその signature だけで決まるかを調べる段階です。

## Review

(5m0s)

# cp-338 実装レビュー

## 結論

**全面採用。今回の詰将棋は、かなり鋭く決まった。**

commit `39ee6aa87fedbef5d1373abbb1375f729f981cb4` と提出された diff/report は一致している。

cp-338 で、これまで曖昧だった局所枝が次の exact theorem に整理された。

- $H=0$ frontier は reflected queue と endpoint drift の `max`
- saturated successor の二 block 和は drift の符号で完全分類
- drift $=0$ は返済ではなく、未払い $+1$ を保存
- mature saturated block は $H=1$ で必ず中立
- positive horizon は pre-block carry mass による coboundary
- uniform source age は finite pre-block carrier の cardinal coverage と同値

数学的破綻、循環仮定、空な前提は見つからなかった。

ただし、次の certificate 構築へ入る前に、二つの意味境界を固定しておく必要がある。

> 同じ signature edge で frontier weight が異なることは、exact deterministic weight recovery の反例にすぎず、sound upper-weight certificate の反例ではない。

> $H=1$ successor の「消費が predecessor unit を相殺する」は scalar accounting であり、その特定 source identity が実際に消費されたことまでは証明していない。

---

## 1. Root `123` の zero-drift obstruction

`n=123,m=0` について、今回も数値監査の結果をそのまま theorem にせず、

- initial block length $2$
- claim depths ${1,2}$
- terminal valuation $1$
- initial block saturation
- successor endpoint drift $0$

を個別に Lean で再構築している。

したがって、

$$\operatorname{Saturated}(123,0)$$

$$\operatorname{endpointAccountingTerm}(123,1)=0$$

$$W_0(0,2)=1$$

が正式に証明された。

これにより、

$$\operatorname{successorDrift}\le0\Longrightarrow W_0(m,2)\le0$$

は偽であり、正しい境界は厳密な、

$$\operatorname{successorDrift}<0$$

であることが確定した。

これは良い反例 theorem じゃ。有限監査で見つけ、Lean で境界を鋭く切り分けている。

---

## 2. Crossing block の余分な境界仮定を除去

cp-337 で残っていた、

```lean
H ≤ canonicalBlockStartTime n
  (canonicalAgeCrossingBlockOfSource n H i)
```

が除去された。

$i+H$ を含む canonical blockを $m$ とすると、

$$b_m\le i+H<b_{m+1}$$

から Nat subtraction の標準補題だけで、

$$b_m-H\le i<b_{m+1}-H$$

が得られる。

これで、

```lean
CarryTwoDebtAt n i
```

だけから、source $i$ が必ずその age-crossing block の carrier に入る。

origin や underflow 領域も含む全域 theoremになった。

cp-337 で見つけた意味境界が、正しく消えた。

---

## 3. $H=0$ frontier の exact `max` 正規形

今回の中心 theorem の一つは、

$$F_0(m)=\max(-Q_m,\Delta_m)$$

じゃ。

ここで、

$$Q_m=\operatorname{queueBeforeBlock}(m)$$

$$\Delta_m=\operatorname{endpointAccountingTerm}(m)=A_m-S_m$$

である。

これは、

$$F_0(m)=A_m-\min(Q_m+A_m,S_m)$$

の exact signed normal formじゃ。

二つの枝は明瞭である。

### Available mass が service 以下

$$Q_m+A_m\le S_m$$

なら全 available claim が消費され、

$$F_0(m)=-Q_m$$

となる。

### Service が available mass 以下

$$S_m\le Q_m+A_m$$

なら service が全て使われ、

$$F_0(m)=A_m-S_m=\Delta_m$$

となる。

この二枝を `max` が一つにまとめている。

---

## 4. $H=0$ trichotomy

`max` 正規形から、次が正確に証明された。

$$Q_m\ge1\land\Delta_m<0\Longrightarrow F_0(m)\le-1$$

$$\Delta_m=0\Longrightarrow F_0(m)=0$$

$$\Delta_m>0\Longrightarrow F_0(m)=\Delta_m$$

これは極めて重要じゃ。

特に正 drift branch では、queue がどれほど大きくても frontier increment は正 drift をそのまま通す。

したがって、

> positive-pressure block に actual consumption の一段下界を追加すれば返済できる

という方針は、$H=0$ の一段 repayment には使えない。

service は既に完全消費されており、それでも demand が service を上回っているからじゃ。

positive branchには、

- さらに長い時間窓
- 正の horizon
- pressure 用の別 potential

のいずれかが必要になる。

---

## 5. Saturated successor の二 block 完全分類

saturated block は最初の block で、

$$F_0(m)=1$$

を発生させる。

successor を含む二 block sum は、

$$W_0(m,2)=1+\max(-Q_{m+1},\Delta_{m+1})$$

となった。

ここから三枝が完全に分かれる。

$$\Delta_{m+1}<0\Longrightarrow W_0(m,2)\le0$$

$$\Delta_{m+1}=0\Longrightarrow W_0(m,2)=1$$

$$\Delta_{m+1}>0\Longrightarrow W_0(m,2)=1+\Delta_{m+1}$$

これで saturated successor の $H=0$ 二段問題は完全に解かれた。

もはや zero-drift branch や positive branchに「追加 consumption があるかもしれない」と期待する余地はない。

- negative branchだけが二段返済
- zero branchは厳密に未払い
- positive branchはさらに借金増加

じゃ。

---

## 6. Mature saturated horizon の一般式

$H\le b_m$ の mature regimeでは、saturated blockの crossing interval は長さ二であり、

$$\operatorname{Crossing}*H(m)={b_m-H,\ b_m-H+1}*{\mathrm{carry}}$$

となる。

従って、

$$F_H(m)=\mathbf1_{\mathrm{carry}(b_m-H)}+\mathbf1_{\mathrm{carry}(b_m-H+1)}-1$$

が証明された。

これにより mature saturated branchでは常に、

$$-1\le F_H(m)\le1$$

となる。

特に、

$$F_0(m)=1$$

であり、今回の predecessor obstructionを使うと、

$$F_1(m)=0$$

となる。

$H=0$ で必ず発生した saturated charge が、$H=1$ では block 自身の位置から完全に消えた。

---

## 7. Predecessor carry obstruction

今回最も数学的に強い新 theorem は、

```lean
CanonicalSaturatedBorderBlock.predecessor_not_carryTwo
```

じゃ。

$$0<b_m\Longrightarrow\neg\operatorname{CarryTwoDebtAt}(n,b_m-1)$$

が証明された。

証明の核は residue だけではない。

saturated start stateを $x$ とすると、まず、

$$3\cdot2^{\operatorname{bitWidth}(x)-1}<2x$$

を導いている。

これは $x$ が自身の binary window の上位四分の一、すなわち $3/4$ 境界より上にあることを示す。

直前 stateを $y$ として carry two を仮定すると、

$$3y+1=2^{s(y)}x$$

および bit-width balanceから、

$$\bigl(\operatorname{bitWidth}(x)-1\bigr)+\bigl(s(y)-1\bigr)=\operatorname{bitWidth}(y)$$

が得られる。

上の $x$ の下界を scaleすると、

$$3\cdot2^{\operatorname{bitWidth}(y)}<3y+1$$

となる。

しかし、

$$y<2^{\operatorname{bitWidth}(y)}$$

なので右辺は $3\cdot2^{\operatorname{bitWidth}(y)}$ より小さくなければならず、矛盾する。

証明経路に循環性はない。

saturated normal formと一段 predecessor transitionから直接、禁止 patternを抽出している。

---

## 8. Mature saturated block は $H=1$ で中立

cp-337 では、

$$F_1(m)=\mathbf1_{\mathrm{carry}(b_m-1)}$$

までだった。

今回、

$$\neg\operatorname{carry}(b_m-1)$$

が証明されたので、

$$F_1(m)=0$$

が一般 theoremになった。

これは有限監査の観測を正しく数学へ昇格させた成果じゃ。

ただし、saturated block 自体が neutralになっても、その successor が正になる場合は残る。

実際、監査で見えていた `[0,1]` は、その successor側の別の carry massによる。

---

## 9. $H=1$ successor の exact balance

saturated block の successorについて、

$$F_1(m+1)=1+A_{m+1}-I_{\mathrm{final}}-C_{m+1}$$

が証明された。

ここで、

- 先頭の $1$ は saturated block の final source が successor crossing の predecessor boundaryになること
- $A_{m+1}$ は successor demand
- $I_{\mathrm{final}}$ は successor block の final source indicator
- $C_{m+1}$ は actual consumption

を表す。

さらに、

$$F_1(m+1)=1\iff A_{m+1}=C_{m+1}+I_{\mathrm{final}}$$

も得られた。

actual consumption は正なので、$F_1=1$ なら、

$$1+I_{\mathrm{final}}\le A_{m+1}$$

であり、final source以外にも少なくとも一つ carry claimが存在する。

### 意味上の注意

ここで「actual consumption が predecessor unitを相殺する」とは、**cardinality accounting 上の相殺**じゃ。

現在の theoremは、

> saturated final sourceそのものが successor blockで消費された

とは証明していない。

以前から queue が残っていれば、FIFO はさらに古い sourceを先に消費する可能性がある。

したがって report の「predecessor unit is cancelled」は、source identity paymentではなく signed countの相殺として読む必要がある。

---

## 10. Horizon telescope

reverse-offset carry mass、

```lean
canonicalRecentCarryMassBeforeStart n H m
```

により、mature regimeでは、

$$D_H(m)=D_0(m)-R_H(m)$$

$$D_H(m)=Q_m-R_H(m)$$

が証明された。

frontierについても、

$$F_H(m)=F_0(m)+R_H(m)-R_H(m+1)$$

となる。

これは $H>0$ frontierが $H=0$ frontierへ加えられた **exact coboundary** である。

この見方は非常に重要じゃ。

正の horizon は新しい総 debtを作るのではない。

> 同じ charge を時間軸上の別 blockへ移動する。

saturated $+1$ が $H=1$ で消えたのも、その charge が successor側や別 boundaryへ移ったためじゃ。

---

## 11. Finite pre-block carry carrier

```lean
canonicalPreBlockCarryCarrier n H m
```

は既存の recent-source carrierを、certificate-facing の名前で公開したものじゃ。

exact identityは、

$$D_H(m)=Q_m-\left|\operatorname{PreBlockCarryCarrier}_H(m)\right|$$

である。

従って、

$$\operatorname{UniformSourceAge}(H)\iff\forall m,\ Q_m\le\left|\operatorname{PreBlockCarryCarrier}_H(m)\right|$$

となる。

これは良い challenge surfaceじゃ。

右辺の carrier は有限であり、cardinalityは高々 $H$。

残る target は、

> outstanding queue が、直前 $H$ source-time に存在する carry massを一度も上回らない

という有限窓被覆問題になった。

### 小さな API 補強候補

mature regimeで、

$$R_H(m)=\left|\operatorname{PreBlockCarryCarrier}_H(m)\right|$$

を明示 theorem にしておくとよい。

現在は両方の deficit formulaから導けるが、reverse-offset sumと actual carrier cardinalityの直接 bridgeが公開されていない。

---

## 12. 次の report 方針に一つ重要な補正

report は次 checkpoint案として、

> 同じ proposed signatureを持ちながら、異なる next frontier weightを持つ二履歴を obstruction theoremにする

と述べている。

ここは区別が必要じゃ。

同じ signature edgeで、

$$w_1\ne w_2$$

であっても、projected edge weightを、

$$\widehat w(s,t)\ge\max(w_1,w_2)$$

と置けば sound certificateは作り得る。

従って weight collision が否定するのは、

```text
signature pairからactual weightが一意に復元できる
```

という deterministic recoveryだけじゃ。

finite potential certificateを本当に否定するには、次のどちらかが必要になる。

1. 同一 signature edge fiber上で actual weightsが上に非有界
2. realized signature graph上に正の total weightを持つ閉路がある

cp-333〜335 で fixed-low signaturesを倒したのは、単なる collisionではなく positive projected cycleだったことを維持すべきじゃ。

---

## 13. Finite certificate が要求する隠れた必要条件

現在の finite certificateが存在すれば、frontier incrementには一様な上界が存在する。

`Signature` が有限なので potentialの最小値が存在し、任意の actual edgeについて、

$$F_H(m)\le\Phi(\sigma_{m+1})-\Phi(\sigma_m)\le\Phi(\sigma_0)-\min_s\Phi(s)$$

となるからじゃ。

従って次には、generic theoremとして、

```lean
CanonicalFiniteSourceAgeFrontierPotentialCertificate
  → ∃ B, ∀ m, canonicalSourceAgeFrontierIncrement n H m ≤ B
```

を証明すべきである。

これは強力な事前監査になる。

frontier incrementがある symbolic family上で非有界なら、現在形式の有限 potential certificate routeはその時点で不可能じゃ。

uniform source-age targetそのものは、individual incrementの一様有界性を必ずしも要求しない。大きな正 incrementが、それ以前の大きな負 creditで相殺される可能性があるからじゃ。

したがって finite certificateは targetより強い方法である。

---

## 14. Coboundary と positive cycle

今回の、

$$F_H(m)=F_0(m)+R_H(m)-R_H(m+1)$$

を有限 pathで足すと、

$$W_H(q,L)=W_0(q,L)+R_H(q)-R_H(q+L)$$

となる。

始点と終点の full signatureが等しく、$R_H$ がその signatureから決まるなら、

$$R_H(q)=R_H(q+L)$$

なので、

$$W_H(q,L)=W_0(q,L)$$

じゃ。

つまり positive horizonの carry coboundaryは、

> closed-signature cycle の total weightを変えない。

horizonは chargeの置き場所を変えるが、閉路全体の総量までは変えない。

ただし recent carry wordを signatureへ追加すると state partitionそのものが細かくなり、以前の偽閉路を分離できる可能性はある。

この二つは区別すべきじゃ。

- coboundary reweightingだけでは positive cycleは消えない
- carry wordによる signature refinementなら cycleが分裂する可能性がある

---

## 15. 現在地

source-age routeは現在、

```text
actual carry source
→ FIFO owned queue
→ global newest-tail normal form
→ source-age deficit
→ frontier signed flow
→ horizon coboundary
→ finite pre-block carry coverage
→ some H satisfies all prefix nonpositivity        [未証明]
→ uniform queue bound
→ endpoint-width bound
```

まで閉じた。

今回の最大成果は、saturated branchの挙動が曖昧な例外ではなくなったことじゃ。

```text
H = 0 : +1
H = 1 mature : 0
successor H = 0 :
  negative drift → repayment
  zero drift     → +1 retained
  positive drift → further growth
```

ここまで完全に確定した。

---

## 判定まとめ

### Root `123` zero-drift witness

**完成。**

### Crossing-block boundary removal

**完成。**

### $H=0$ `max` normal form

**完成。**

### $H=0$ drift trichotomy

**完成。**

### Saturated two-block trichotomy

**完成。**

### Mature saturated general horizon formula

**完成。**

### Predecessor carry obstruction

**完成。今回の中心的算術成果。**

### Mature saturated $H=1$ neutralization

**完成。**

### $H=1$ successor balance

**完成。source identity paymentとは区別が必要。**

### Horizon telescope / coboundary

**完成。**

### Uniform age / finite carrier coverage

**完成。**

### Uniform horizon $H$ の存在

**未証明。**

### Finite structural certificate

**未構築。**

### Report の次 obstruction 判定

**weight collisionだけでは弱い。positive cycleまたはedge-fiber非有界性が必要。**

### cp-338 総合判定

**全面採用。次は finite signatureを作る前に、certificateの必要条件と coboundary不変性を固定する。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-338.

The cp-338 implementation is accepted.

It completed:

    the exact H = 0 reflected max normal form;

    the sharp negative / zero / positive successor trichotomy;

    a formal root-123 zero-drift obstruction;

    the mature saturated predecessor-carry exclusion;

    exact H = 1 neutralization of every mature saturated block;

    the horizon coboundary formula;

    the finite pre-block carry coverage characterization of uniform age.

The next checkpoint must prepare the finite-certificate boundary without
confusing deterministic weight recovery with sound projected upper weights.

Stage A — direct recent-mass/carrier bridge

For H <= canonicalBlockStartTime n m, prove:

    canonicalRecentCarryMassBeforeStart n H m
      =
    card (canonicalPreBlockCarryCarrier n H m).

Also prove an all-regime padded-word version that does not alias underflowed
source addresses.

Stage B — padded finite pre-block carry word

For fixed H define a finite Boolean word, preferably:

    canonicalPreBlockCarryWord n H m : Fin H -> Bool

where offset r represents source:

    canonicalBlockStartTime n m - (r + 1)

only when r + 1 <= blockStart; otherwise the bit is false.

Prove:

    the number of true bits
      =
    card (canonicalPreBlockCarryCarrier n H m).

Do not use raw Nat subtraction in a way that repeats source zero in the
underflow regime.

Stage C — horizon-window coboundary

For every mature finite window prove:

    frontierWindowSum H q L
      =
    frontierWindowSum 0 q L
        + recentCarryMass H q
        - recentCarryMass H (q + L).

Derive:

    closed endpoints with equal recent carry words
      ->
    H-window total weight = H0-window total weight.

Stage D — generic coboundary reweighting API

In `FiniteSignedTransition.lean`, formalize a generic edge reweighting:

    weight' a b = weight a b + correction a - correction b.

Prove:

    path weights differ only by endpoint correction;

    closed-path weights are invariant;

    a positive closed-signature obstruction survives every correction that is
    determined by the signature.

This is the correct interpretation of the positive-horizon carry coboundary.

Stage E — finite-certificate pointwise-bound necessity

Prove generically that every:

    CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature

implies:

    exists B : Int,
      forall m, canonicalSourceAgeFrontierIncrement n H m <= B.

Use the finite minimum of the potential.

Record explicitly:

    this uniform pointwise bound is necessary for the current finite-potential
    method;

    it is not implied merely by the uniform-prefix target in an arbitrary
    signed flow.

Stage F — frontier increment boundedness audit

Before designing a signature, investigate whether for a fixed H the actual
frontier increments are uniformly bounded above.

Separate:

    saturated branch, already bounded in {-1, 0, 1};

    zero-drift branch;

    positive-pressure branch.

Attempt either:

    a symbolic global upper bound;

or:

    a symbolic family with unbounded positive frontier increment.

Finite numerical maxima are discovery evidence only.

If an unbounded family is found, formalize it and conclude that the present
finite-potential certificate shape cannot exist for that H.

Stage G — exact weight collision is diagnostic only

Define a candidate finite signature only after Stage F.

For each proposed signature distinguish three outcomes:

    exact-weight collision:
      same signature edge, different actual weights;

    upper-bound obstruction:
      actual weights on one signature edge are unbounded above;

    potential obstruction:
      a realized positive closed-signature path or cycle.

Prove and document:

    exact-weight collision refutes deterministic weight recovery only;

    it does not refute a sound projected upper-weight certificate.

Do not label an ordinary collision as a certificate impossibility theorem.

Stage H — finite reachable-signature framework

Define a genuinely finite projected model containing:

    a finite signature type;

    a finite reachable-signature carrier;

    a projected edge relation;

    a projected integer upper weight;

    an initial signature;

    closure of the reachable carrier under projected edges.

Keep the all-time arithmetic obligations separate:

    every canonical block maps into the reachable carrier;

    every canonical successor maps to a projected edge;

    every actual frontier weight is bounded by the projected edge weight.

Stage I — potential verification on the projected graph

For the finite projected graph, expose finite conditions:

    projected edge weight <= potential target - potential source;

    potential of every reachable signature <= initial potential.

Derive the existing
`CanonicalFiniteSourceAgeFrontierPotentialCertificate`.

Do not require the initial potential to dominate unreachable signatures.

Stage J — H = 1 successor residual form

For a saturated block define:

    successorNonfinalDemand
      =
    successor demand - successor final-source indicator;

    successorExtraConsumed
      =
    successor actual consumption - 1.

Use the proved positivity of successor consumption and the fact that the final
indicator is contained in demand.

Prove the exact signed identity:

    frontierIncrement 1 (m + 1)
      =
    successorNonfinalDemand - successorExtraConsumed.

State carefully:

    this is a scalar balance;

    it does not prove that the saturated final-source identity itself was
    consumed in the successor block.

Stage K — finite-word saturated transitions

Using `canonicalPreBlockCarryWord`, express every mature saturated frontier
weight as the sum of the two appropriate word bits minus one.

Recover:

    H = 0 saturated weight = 1;

    H = 1 mature saturated weight = 0.

Determine what finite word update is required across a saturated block and its
successor.

Stage L — candidate signature audit

Only after Stages A–K, propose the first finite frontier signature.

A reasonable candidate may include:

    the padded pre-block carry word of length H;

    a finite queue cap or overflow marker;

    the local block grammar class;

    the final-source carry indicator;

    the finite information needed for the projected edge upper bound.

Do not include:

    source-age deficit;

    future prefix sums;

    a potential defined from the desired bound.

A capped queue observable is allowed only if its transition soundness is
proved without assuming the target queue bound.

Stage M — challenge-facing boundary

Keep these statements separate:

    target:
      exists H, every frontier prefix at H is nonpositive;

    sufficient finite method:
      a sound finite projected graph with an initial-max potential;

    possible obstruction:
      unbounded edge fibers or positive projected cycles;

    later global tasks:
      endpoint-to-all-time width transport;
      finite-state periodicity;
      nontrivial-cycle elimination;
      raw Collatz translation.

Stopping rule

Stop at the first genuine obstruction among:

    padded carry-word cardinality fails at the origin;

    the coboundary window theorem fails;

    closed-cycle weight invariance fails;

    finite certificates do not imply a pointwise frontier upper bound;

    a fixed-H frontier increment family is unbounded;

    no finite projected edge upper weight can cover one candidate edge fiber;

    a positive reachable projected cycle survives the candidate refinement;

    queue-cap transition soundness requires the target bound itself.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-339.md
```

今回で saturated block の局所詰将棋は、ほぼ詰んだ。

次は盤面を有限 signature graphへ移す前に、**その駒組みで本当に全 frontier edgeを上から押さえられるか**を確認する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
index 8a3f7a20..ce03f7d0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
@@ -117,6 +117,153 @@ theorem exists_canonicalSaturatedBorderBlock :
     ∃ n m, CanonicalSaturatedBorderBlock n m :=
   ⟨fiftyNineSaturatedOdd, 0, canonicalSaturatedBorderBlock_fiftyNine_zero⟩
 
+/-! ## Concrete zero-drift successor witness -/
+
+/-- Root 123 is the first bounded-audit witness whose saturated initial block
+is followed by raw endpoint drift zero.  All facts used below are rechecked in
+Lean; the audit only identified the candidate. -/
+def oneTwentyThreeSaturatedOdd : OddNat := ⟨123, by norm_num⟩
+
+private lemma oneTwentyThree_v2_124 : v2 124 = 2 := by
+  have h62 := (DkMath.ABC.padic_val_two_of_even 62).2 (by decide)
+  have h31 := (DkMath.ABC.padic_val_two_of_even 31).2 (by decide)
+  have hv31 : v2 31 = 0 := v2_odd 31 (by decide)
+  have hv62 : v2 62 = 1 := by simpa [v2, hv31] using h31
+  simpa [v2, hv62] using h62
+
+private lemma oneTwentyThree_v2_140 : v2 140 = 2 := by
+  have h70 := (DkMath.ABC.padic_val_two_of_even 70).2 (by decide)
+  have h35 := (DkMath.ABC.padic_val_two_of_even 35).2 (by decide)
+  have hv35 : v2 35 = 0 := v2_odd 35 (by decide)
+  have hv70 : v2 70 = 1 := by simpa [v2, hv35] using h35
+  simpa [v2, hv70] using h70
+
+private lemma oneTwentyThree_v2_370 : v2 370 = 1 := by
+  have h185 := (DkMath.ABC.padic_val_two_of_even 185).2 (by decide)
+  simpa [v2, v2_odd 185 (by decide)] using h185
+
+private lemma oneTwentyThree_v2_556 : v2 556 = 2 := by
+  have h278 := (DkMath.ABC.padic_val_two_of_even 278).2 (by decide)
+  have h139 := (DkMath.ABC.padic_val_two_of_even 139).2 (by decide)
+  have hv139 : v2 139 = 0 := v2_odd 139 (by decide)
+  have hv278 : v2 278 = 1 := by simpa [v2, hv139] using h139
+  simpa [v2, hv278] using h278
+
+private lemma oneTwentyThree_v2_418 : v2 418 = 1 := by
+  have h209 := (DkMath.ABC.padic_val_two_of_even 209).2 (by decide)
+  simpa [v2, v2_odd 209 (by decide)] using h209
+
+private lemma oneTwentyThree_v2_628 : v2 628 = 2 := by
+  have h314 := (DkMath.ABC.padic_val_two_of_even 314).2 (by decide)
+  have h157 := (DkMath.ABC.padic_val_two_of_even 157).2 (by decide)
+  have hv157 : v2 157 = 0 := v2_odd 157 (by decide)
+  have hv314 : v2 314 = 1 := by simpa [v2, hv157] using h157
+  simpa [v2, hv314] using h314
+
+private lemma oneTwentyThree_v2_278 : v2 278 = 1 := by
+  have h139 := (DkMath.ABC.padic_val_two_of_even 139).2 (by decide)
+  simpa [v2, v2_odd 139 (by decide)] using h139
+
+private theorem oneTwentyThree_endpoint_zero :
+    paymentEndpointSeq oneTwentyThreeSaturatedOdd 0 = 1 := by
+  norm_num [paymentEndpointSeq, orbitPaymentTarget, orbitExactDepth,
+    ResidualAllOnesDepth, oddOrbitLabel, iterateT,
+    oneTwentyThreeSaturatedOdd, mkOddNat, oneTwentyThree_v2_124]
+
+private theorem oneTwentyThree_endpoint_one :
+    paymentEndpointSeq oneTwentyThreeSaturatedOdd 1 = 3 := by
+  rw [show paymentEndpointSeq oneTwentyThreeSaturatedOdd 1 =
+    orbitPaymentTarget oneTwentyThreeSaturatedOdd
+      (paymentEndpointSeq oneTwentyThreeSaturatedOdd 0 + 1) by rfl]
+  rw [oneTwentyThree_endpoint_zero]
+  norm_num [orbitPaymentTarget, orbitExactDepth, ResidualAllOnesDepth,
+    oddOrbitLabel, iterateT, T, oneTwentyThreeSaturatedOdd, mkOddNat,
+    threeNPlusOne, pow2, oneTwentyThree_v2_370,
+    oneTwentyThree_v2_556, oneTwentyThree_v2_140]
+
+private theorem oneTwentyThree_paymentBlockLength_zero :
+    canonicalPaymentBlockLength oneTwentyThreeSaturatedOdd 0 = 2 := by
+  rw [canonicalPaymentBlockLength_eq_endpoint_sub_start_add_one,
+    universalPaymentBlockStart_paymentEndpointSeq_zero,
+    oneTwentyThree_endpoint_zero]
+
+@[simp] theorem canonicalBlockLength_oneTwentyThree_zero :
+    canonicalBlockLength oneTwentyThreeSaturatedOdd 0 = 2 :=
+  oneTwentyThree_paymentBlockLength_zero
+
+private theorem canonicalBlockStartState_oneTwentyThree_zero :
+    canonicalBlockStartState oneTwentyThreeSaturatedOdd 0 = 123 := by
+  unfold canonicalBlockStartState canonicalBlockStartTime
+    canonicalEndpointBlockStart
+  rfl
+
+private theorem canonicalBlockOddCore_oneTwentyThree_zero :
+    canonicalBlockOddCore oneTwentyThreeSaturatedOdd 0 = 31 := by
+  rw [canonicalBlockOddCore, canonicalBlockStartState_oneTwentyThree_zero,
+    canonicalBlockLength_oneTwentyThree_zero]
+  norm_num
+
+@[simp] theorem canonicalBlockTerminalValuation_oneTwentyThree_zero :
+    canonicalBlockTerminalValuation oneTwentyThreeSaturatedOdd 0 = 1 := by
+  rw [canonicalBlockTerminalValuation, canonicalBlockTerminalCarrier,
+    canonicalBlockLength_oneTwentyThree_zero,
+    canonicalBlockOddCore_oneTwentyThree_zero]
+  norm_num [oneTwentyThree_v2_278]
+
+private theorem oneTwentyThree_carry_zero :
+    CarryTwoDebtAt oneTwentyThreeSaturatedOdd 0 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, oneTwentyThreeSaturatedOdd, mkOddNat]
+
+private theorem oneTwentyThree_carry_one :
+    CarryTwoDebtAt oneTwentyThreeSaturatedOdd 1 := by
+  norm_num [CarryTwoDebtAt, stateUpperCarry, upperCarry3n1, bitWidth,
+    iterateT, T, oneTwentyThreeSaturatedOdd, mkOddNat, threeNPlusOne,
+    pow2, oneTwentyThree_v2_370]
+
+theorem canonicalPaymentClaimDepths_oneTwentyThree_zero :
+    canonicalPaymentClaimDepths oneTwentyThreeSaturatedOdd 0 = {1, 2} := by
+  classical
+  ext d
+  rw [mem_canonicalPaymentClaimDepths_iff,
+    oneTwentyThree_paymentBlockLength_zero]
+  unfold canonicalPaymentSourceAtDepth
+  rw [oneTwentyThree_endpoint_zero]
+  simp only [Finset.mem_insert, Finset.mem_singleton]
+  constructor
+  · rintro ⟨hd1, hd2, hcarry⟩
+    interval_cases d <;> simp_all
+  · rintro (rfl | rfl) <;>
+      simp [oneTwentyThree_carry_zero, oneTwentyThree_carry_one]
+
+@[simp] theorem canonicalBlockClaimCount_oneTwentyThree_zero :
+    canonicalBlockClaimCount oneTwentyThreeSaturatedOdd 0 = 2 := by
+  rw [canonicalBlockClaimCount_eq_claimDepths_card,
+    canonicalPaymentClaimDepths_oneTwentyThree_zero]
+  decide
+
+/-- Root 123 starts with a formally checked saturated canonical block. -/
+theorem canonicalSaturatedBorderBlock_oneTwentyThree_zero :
+    CanonicalSaturatedBorderBlock oneTwentyThreeSaturatedOdd 0 := by
+  rw [canonicalSaturatedBorderBlock_iff_length_and_claims]
+  simp
+
+/-- The successor of root 123's initial saturated block has raw drift zero. -/
+theorem endpointAccountingTerm_oneTwentyThree_one :
+    endpointAccountingTerm oneTwentyThreeSaturatedOdd 1 = 0 := by
+  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt]
+  rw [universalPaymentBlockSignedDriftAt_eq_bitWidth_sub
+    oneTwentyThreeSaturatedOdd
+    (paymentEndpointSeq oneTwentyThreeSaturatedOdd 1)
+    (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq
+      oneTwentyThreeSaturatedOdd 1)]
+  rw [universalPaymentBlockStart_paymentEndpointSeq_succ,
+    oneTwentyThree_endpoint_zero, oneTwentyThree_endpoint_one]
+  norm_num [iterateT, T, oneTwentyThreeSaturatedOdd, mkOddNat,
+    threeNPlusOne, pow2, bitWidth, oneTwentyThree_v2_370,
+    oneTwentyThree_v2_556, oneTwentyThree_v2_418,
+    oneTwentyThree_v2_628]
+
 /-- Horizon-zero pointwise nonpositivity is formally false, not merely
 conditionally obstructed. -/
 theorem not_forall_sourceAgeFrontierIncrement_zero_nonpos :
@@ -167,7 +314,10 @@ previous module, this structure contains no all-time prefix field: with a
 `Fintype Signature`, `potential_le_initial` is a finite verification problem.
 
 The signature, transition relation, and potential remain externally supplied.
-Defining them from the source-age deficit would still be circular. -/
+Defining them from the source-age deficit would still be circular.  Only the
+finite maximum field becomes a finite-state check once `Signature` is finite;
+`step_succ` and `actualWeight_succ` remain all-time arithmetic soundness
+obligations and are not made decidable merely by `Fintype Signature`. -/
 structure CanonicalFiniteSourceAgeFrontierPotentialCertificate
     (n : OddNat) (H : ℕ) (Signature : Type*) [Fintype Signature] where
   certificate :
@@ -671,32 +821,24 @@ theorem shiftedSource_mem_canonicalAgeCrossingBlockOfSource
   (Classical.choose_spec
     (existsUnique_mem_canonicalPaymentBlock n (i + H))).1
 
-/-- Subject to the exact non-underflow condition, a carry-two source belongs
-to the age-`H` crossing carrier of the block containing its shifted source
-time. -/
+/-- A carry-two source belongs to the age-`H` crossing carrier of the unique
+block containing its shifted source time.  The Nat subtraction laws handle
+the origin regime directly; no separate non-underflow hypothesis is needed. -/
 theorem mem_crossingClaims_canonicalAgeCrossingBlockOfSource
-    {n : OddNat} {H i : ℕ} (hiCarry : CarryTwoDebtAt n i)
-    (hboundary : H ≤ canonicalBlockStartTime n
-      (canonicalAgeCrossingBlockOfSource n H i)) :
+    {n : OddNat} {H i : ℕ} (hiCarry : CarryTwoDebtAt n i) :
     i ∈ canonicalSourceAgeHorizonCrossingClaims n H
       (canonicalAgeCrossingBlockOfSource n H i) := by
   let m := canonicalAgeCrossingBlockOfSource n H i
-  change H ≤ canonicalBlockStartTime n m at hboundary
   have hiBlock : i + H ∈ canonicalPaymentBlock n m := by
     exact shiftedSource_mem_canonicalAgeCrossingBlockOfSource n H i
   have hiRange := Finset.mem_Ico.mp
     (mem_canonicalPaymentBlock_startTime_interval hiBlock)
-  have hmono : canonicalBlockStartTime n m ≤
-      canonicalBlockStartTime n (m + 1) :=
-    canonicalBlockStartTime_mono n (by omega)
-  have hnextBoundary : H ≤ canonicalBlockStartTime n (m + 1) :=
-    hboundary.trans hmono
-  have hleftEq := Nat.sub_add_cancel hboundary
-  have hrightEq := Nat.sub_add_cancel hnextBoundary
   change i ∈ canonicalSourceAgeHorizonCrossingClaims n H m
   rw [canonicalSourceAgeHorizonCrossingClaims,
     mem_carryTwoPositions_iff]
-  exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
+  refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hiCarry⟩
+  · exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using hiRange.1)
+  · exact Nat.lt_sub_iff_add_lt.mpr (by simpa using hiRange.2)
 
 /-! ## Short-window frontier sums -/
 
@@ -756,6 +898,488 @@ theorem CanonicalSaturatedBorderBlock.sourceAgeFrontierWindowSum_one_one
   rw [canonicalSourceAgeFrontierWindowSum_one,
     h.sourceAgeFrontierIncrement_one_eq_indicator hstart]
 
+/-! ## Exact horizon-zero reflected-frontier normal form -/
+
+/-- At horizon zero, actual frontier flow is the larger of the negative
+outstanding queue and the raw endpoint drift.  This is the exact signed form
+of `demand - min (queue + demand) service`. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_eq_max
+    (n : OddNat) (m : ℕ) :
+    canonicalSourceAgeFrontierIncrement n 0 m =
+      max (-(canonicalOutstandingClaimQueueBeforeBlock n m : ℤ))
+        (endpointAccountingTerm n m) := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed,
+    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
+  change (canonicalQueueDemand n m : ℤ) -
+      (min
+        (canonicalOutstandingClaimQueueBeforeBlock n m +
+          canonicalQueueDemand n m)
+        (canonicalQueueService n m) : ℕ) =
+    max (-(canonicalOutstandingClaimQueueBeforeBlock n m : ℤ))
+      ((canonicalQueueDemand n m : ℤ) - canonicalQueueService n m)
+  by_cases havailable :
+      canonicalOutstandingClaimQueueBeforeBlock n m +
+          canonicalQueueDemand n m ≤ canonicalQueueService n m
+  · rw [Nat.min_eq_left havailable, max_eq_left]
+    · push_cast
+      ring
+    · omega
+  · have hservice : canonicalQueueService n m ≤
+        canonicalOutstandingClaimQueueBeforeBlock n m +
+          canonicalQueueDemand n m := Nat.le_of_not_ge havailable
+    rw [Nat.min_eq_right hservice, max_eq_right]
+    omega
+
+/-- Negative raw drift forces at least one unit of negative frontier flow when
+the reflected queue already contains a unit. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_le_neg_one_of_drift_neg
+    {n : OddNat} {m : ℕ}
+    (hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n m)
+    (hnegative : endpointAccountingTerm n m < 0) :
+    canonicalSourceAgeFrontierIncrement n 0 m ≤ -1 := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_max, max_le_iff]
+  constructor <;> omega
+
+/-- Zero raw drift gives exactly zero horizon-zero frontier flow, independent
+of the current queue. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_eq_zero_of_drift_eq_zero
+    {n : OddNat} {m : ℕ}
+    (hzero : endpointAccountingTerm n m = 0) :
+    canonicalSourceAgeFrontierIncrement n 0 m = 0 := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_max, hzero, max_eq_right]
+  omega
+
+/-- Positive raw drift is transmitted unchanged through the reflected queue
+at horizon zero. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_eq_drift_of_drift_pos
+    {n : OddNat} {m : ℕ}
+    (hpositive : 0 < endpointAccountingTerm n m) :
+    canonicalSourceAgeFrontierIncrement n 0 m = endpointAccountingTerm n m := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_max, max_eq_right]
+  omega
+
+/-! ## Mature saturated-horizon normal form -/
+
+namespace CanonicalSaturatedBorderBlock
+
+/-- For a mature horizon, a length-two block exposes exactly its two shifted
+source boundaries.  The hypothesis prevents Nat subtraction from aliasing an
+underflowed source with source zero. -/
+theorem sourceAgeHorizonCrossingClaims_eq_two_singletons
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeHorizonCrossingClaims n H m =
+      carryTwoPositions n {canonicalBlockStartTime n m - H} ∪
+        carryTwoPositions n {canonicalBlockStartTime n m - H + 1} := by
+  classical
+  ext i
+  simp only [canonicalSourceAgeHorizonCrossingClaims,
+    mem_carryTwoPositions_iff, Finset.mem_Ico, Finset.mem_union,
+    Finset.mem_singleton]
+  rw [canonicalBlockStartTime_succ, h.length_eq_two]
+  constructor
+  · rintro ⟨⟨hiLo, hiHi⟩, hiCarry⟩
+    have hi : i = canonicalBlockStartTime n m - H ∨
+        i = canonicalBlockStartTime n m - H + 1 := by omega
+    exact hi.elim (fun hi => Or.inl ⟨hi, hiCarry⟩)
+      (fun hi => Or.inr ⟨hi, hiCarry⟩)
+  · rintro (⟨rfl, hiCarry⟩ | ⟨rfl, hiCarry⟩) <;>
+      exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+
+private theorem disjoint_saturated_mature_crossing_singletons
+    {n : OddNat} {H m : ℕ} :
+    Disjoint
+      (carryTwoPositions n {canonicalBlockStartTime n m - H})
+      (carryTwoPositions n {canonicalBlockStartTime n m - H + 1}) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro i hiLeft hiRight
+  have hiLeftEq := (mem_carryTwoPositions_iff.mp hiLeft).1
+  have hiRightEq := (mem_carryTwoPositions_iff.mp hiRight).1
+  simp only [Finset.mem_singleton] at hiLeftEq hiRightEq
+  omega
+
+/-- Exact mature-horizon formula for a saturated block.  It remains valid for
+all `H ≤ start`; the separate `H > start` regime is intentionally excluded. -/
+theorem sourceAgeFrontierIncrement_eq_indicators
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n H m =
+      (canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n m - H) : ℤ) +
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n m - H + 1) - 1 := by
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [h.sourceAgeHorizonCrossingClaims_eq_two_singletons hH,
+    Finset.card_union_of_disjoint
+      disjoint_saturated_mature_crossing_singletons,
+    card_carryTwoPositions_singleton,
+    card_carryTwoPositions_singleton,
+    h.canonicalQueueConsumed_eq_one]
+  push_cast
+  ring
+
+/-- Saturation places the start word strictly above three quarters of its
+binary window.  This quantitative form is what excludes a carry-two
+predecessor; the residue normal form alone is not sufficient. -/
+private theorem startState_three_mul_leading_lt_two_mul
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    3 * 2 ^ (bitWidth (canonicalBlockStartState n m) - 1) <
+      2 * canonicalBlockStartState n m := by
+  let u := canonicalBlockOddCore n m
+  let x := canonicalBlockStartState n m
+  let z := canonicalBlockNextStartState n m
+  change 3 * 2 ^ (bitWidth x - 1) < 2 * x
+  have hu : 0 < u := canonicalBlockOddCore_pos n m
+  have hx : x = 4 * u - 1 := h.startState_eq_four_mul_core_sub_one
+  have hz : z = (9 * u - 1) / 2 := h.nextStartState_eq
+  have hdvd : 2 ∣ 9 * u - 1 := by
+    have hdvd := h.pow_length_sub_one_dvd_terminalCarrier
+    simpa [u, canonicalBlockTerminalCarrier, h.length_eq_two] using hdvd
+  have hzDouble : 2 * z = 9 * u - 1 := by
+    rw [hz]
+    have := Nat.div_mul_cancel hdvd
+    omega
+  have hzpos : 0 < z := by omega
+  have hwidth : bitWidth z = bitWidth x + 1 := by
+    simpa [x, z] using h.nextStart_bitWidth_eq_start_add_one
+  have hlead := pow_bitWidth_sub_one_le hzpos
+  rw [hwidth] at hlead
+  have hpow : 2 ^ bitWidth x ≤ z := by simpa using hlead
+  have hxpos : 0 < x := by omega
+  have hxwidth : 0 < bitWidth x := by
+    rw [bitWidth_eq_log_two_add_one hxpos.ne']
+    omega
+  have hpowSplit : 2 ^ bitWidth x =
+      2 * 2 ^ (bitWidth x - 1) := by
+    conv_lhs => rw [show bitWidth x = (bitWidth x - 1) + 1 by omega]
+    rw [pow_succ]
+    ring
+  rw [hpowSplit] at hpow
+  have hfour : 4 * 2 ^ (bitWidth x - 1) ≤ 9 * u - 1 := by
+    omega
+  have hu3 : 3 ≤ u := by
+    have hu4 := h.oddCore_mod_four_eq_three
+    change u % 4 = 3 at hu4
+    omega
+  omega
+
+/-- A mature saturated block cannot be immediately preceded by a carry-two
+source.  The proof combines the exact predecessor transition, the saturated
+upper-window lower bound, and one-step width conservation. -/
+theorem predecessor_not_carryTwo
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    ¬ CarryTwoDebtAt n (canonicalBlockStartTime n m - 1) := by
+  intro hcarry
+  let t := canonicalBlockStartTime n m
+  let y : OddNat := iterateT (t - 1) n
+  let x := canonicalBlockStartState n m
+  have ht : t - 1 + 1 = t := by omega
+  have hTy : T y = iterateT t n := by
+    rw [← iterateT_succ_eq_T_iterateT]
+    exact congrArg (fun j => iterateT j n) ht
+  have hcarryY : stateUpperCarry y.1 = 2 := by
+    simpa [CarryTwoDebtAt, y, t] using hcarry
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry y
+  rw [hTy, hcarryY] at hbalance
+  change s y + bitWidth x = bitWidth y.1 + 2 at hbalance
+  have hspos : 0 < s y := s_pos y
+  have hraw := threeNPlusOne_eq_pow_height_mul_T y
+  rw [hTy] at hraw
+  change 3 * y.1 + 1 = 2 ^ s y * x at hraw
+  have htop := h.startState_three_mul_leading_lt_two_mul
+  change 3 * 2 ^ (bitWidth x - 1) < 2 * x at htop
+  have hscalePos : 0 < (2 : ℕ) ^ (s y - 1) :=
+    pow_pos (by norm_num) _
+  have hscaled :
+      (3 * 2 ^ (bitWidth x - 1)) * 2 ^ (s y - 1) <
+        (2 * x) * 2 ^ (s y - 1) :=
+    (Nat.mul_lt_mul_right hscalePos).2 htop
+  have hsSplit : 2 ^ s y = 2 * 2 ^ (s y - 1) := by
+    conv_lhs => rw [show s y = (s y - 1) + 1 by omega]
+    rw [pow_succ]
+    ring
+  have hxMod : x % 2 = 1 := by
+    simpa [x, canonicalBlockStartState, t] using (iterateT t n).2
+  have hxpos : 0 < x := by omega
+  have hxwidth : 0 < bitWidth x := by
+    rw [bitWidth_eq_log_two_add_one hxpos.ne']
+    omega
+  have hexp : (bitWidth x - 1) + (s y - 1) = bitWidth y.1 := by
+    omega
+  have hyOdd := y.2
+  have hypos : 0 < y.1 := by omega
+  have hyUpper := lt_pow_bitWidth hypos
+  rw [Nat.mul_assoc, ← pow_add, hexp] at hscaled
+  have hscaled' : 3 * 2 ^ bitWidth y.1 < 2 ^ s y * x := by
+    calc
+      3 * 2 ^ bitWidth y.1 < 2 * x * 2 ^ (s y - 1) := hscaled
+      _ = 2 ^ s y * x := by rw [hsSplit]; ring
+  omega
+
+/-- Consequently every mature saturated block is neutral at horizon one. -/
+theorem sourceAgeFrontierIncrement_one_eq_zero
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n 1 m = 0 := by
+  rw [h.sourceAgeFrontierIncrement_one_eq_indicator hstart]
+  have hindicator : canonicalCarryTwoIndicator n
+      (canonicalBlockStartTime n m - 1) = 0 :=
+    (canonicalCarryTwoIndicator_eq_zero_iff n _).2
+      (h.predecessor_not_carryTwo hstart)
+  exact_mod_cast hindicator
+
+/-- The horizon-one successor flow is an exact four-term balance.  The leading
+unit is the saturated block's final-source carry, now seen as the successor's
+predecessor boundary. -/
+theorem sourceAgeFrontierIncrement_one_succ_eq_boundary_balance
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierIncrement n 1 (m + 1) =
+      1 + (canonicalQueueDemand n (m + 1) : ℤ) -
+        canonicalCarryTwoIndicator n
+          (canonicalBlockStartTime n (m + 2) - 1) -
+        canonicalQueueConsumed n (m + 1) := by
+  have hstart : 0 < canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    have hlength := one_le_canonicalBlockLength n m
+    omega
+  have hpredEq : canonicalBlockStartTime n (m + 1) - 1 =
+      paymentEndpointSeq n m := by
+    rw [canonicalBlockStartTime_succ]
+    exact canonicalBlockStartTime_add_length_sub_one_eq_endpoint n m
+  have hendpointMem : paymentEndpointSeq n m ∈ canonicalPaymentBlock n m := by
+    rw [canonicalPaymentBlock_eq_sourceFiber]
+    exact endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)
+  have hpredCarry : CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - 1) := by
+    rw [hpredEq]
+    exact h.carryTwo_of_mem hendpointMem
+  have hpredIndicator : canonicalCarryTwoIndicator n
+      (canonicalBlockStartTime n (m + 1) - 1) = 1 :=
+    (canonicalCarryTwoIndicator_eq_one_iff n _).2 hpredCarry
+  unfold canonicalSourceAgeFrontierIncrement
+  rw [int_card_sourceAgeHorizonCrossingClaims_one hstart,
+    hpredIndicator]
+  push_cast
+  ring
+
+/-- A successor value `+1` is exactly equality between its demand and the sum
+of actual consumption and its final-source boundary indicator. -/
+theorem sourceAgeFrontierIncrement_one_succ_eq_one_iff
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierIncrement n 1 (m + 1) = 1 ↔
+      canonicalQueueDemand n (m + 1) =
+        canonicalQueueConsumed n (m + 1) +
+          canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n (m + 2) - 1) := by
+  rw [h.sourceAgeFrontierIncrement_one_succ_eq_boundary_balance]
+  constructor <;> intro hEq <;> omega
+
+/-- If the horizon-one successor is `+1`, at least one nonfinal carry remains
+after removing its final-source indicator.  The inherited predecessor unit is
+not the cause by itself: positive actual consumption already cancels it. -/
+theorem one_add_finalIndicator_le_successorDemand_of_frontier_one
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hfrontier : canonicalSourceAgeFrontierIncrement n 1 (m + 1) = 1) :
+    1 + canonicalCarryTwoIndicator n
+        (canonicalBlockStartTime n (m + 2) - 1) ≤
+      canonicalQueueDemand n (m + 1) := by
+  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
+    rw [h.queueBeforeBlock_succ_eq_add_one]
+    omega
+  have havailable : 1 ≤
+      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
+        canonicalQueueDemand n (m + 1) := by omega
+  have hservice : 1 ≤ canonicalQueueService n (m + 1) := by
+    unfold canonicalQueueService
+    rw [canonicalBlockCapacityCount_eq_terminalValuation]
+    exact one_le_canonicalBlockTerminalValuation n (m + 1)
+  have hconsumed : 0 < canonicalQueueConsumed n (m + 1) := by
+    unfold canonicalQueueConsumed
+    exact lt_of_lt_of_le Nat.zero_lt_one (le_min havailable hservice)
+  have hEq :=
+    h.sourceAgeFrontierIncrement_one_succ_eq_one_iff.mp hfrontier
+  omega
+
+end CanonicalSaturatedBorderBlock
+
+/-! ## Horizon telescope and recent carry carrier -/
+
+/-- Carry mass in the `H` source positions immediately before a block start,
+written in the reverse offset coordinates used by the horizon derivative. -/
+noncomputable def canonicalRecentCarryMassBeforeStart
+    (n : OddNat) (H m : ℕ) : ℤ :=
+  ∑ r ∈ Finset.range H,
+    (canonicalCarryTwoIndicator n
+      (canonicalBlockStartTime n m - r - 1) : ℤ)
+
+/-- In the mature regime, the age deficit is the horizon-zero deficit minus
+the carry boundaries crossed while moving the horizon. -/
+theorem canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeDeficit n H m =
+      canonicalSourceAgeDeficit n 0 m -
+        canonicalRecentCarryMassBeforeStart n H m := by
+  induction H with
+  | zero => simp [canonicalRecentCarryMassBeforeStart]
+  | succ H ih =>
+      have hlt : H < canonicalBlockStartTime n m := by omega
+      rw [canonicalSourceAgeDeficit_succ_horizon_of_lt_start hlt,
+        ih (by omega)]
+      simp only [canonicalRecentCarryMassBeforeStart,
+        Finset.sum_range_succ]
+      ring
+
+/-- Queue-facing form of the mature horizon telescope. -/
+theorem canonicalSourceAgeDeficit_eq_queue_sub_recentCarryMass
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeDeficit n H m =
+      canonicalOutstandingClaimQueueBeforeBlock n m -
+        canonicalRecentCarryMassBeforeStart n H m := by
+  rw [canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hH,
+    canonicalSourceAgeDeficit_zero_horizon]
+
+/-- A positive horizon adds an exact carry-boundary coboundary to the
+horizon-zero frontier flow. -/
+theorem canonicalSourceAgeFrontierIncrement_eq_zero_add_recentCarryCoboundary
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n H m =
+      canonicalSourceAgeFrontierIncrement n 0 m +
+        canonicalRecentCarryMassBeforeStart n H m -
+          canonicalRecentCarryMassBeforeStart n H (m + 1) := by
+  have hHnext : H ≤ canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    omega
+  have hcurrent := canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hH
+  have hnext := canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hHnext
+  have hflowH := canonicalSourceAgeDeficit_succ n H m
+  have hflowZero := canonicalSourceAgeDeficit_succ n 0 m
+  omega
+
+/-- Petal-facing name for the existing recent source-time carry carrier. -/
+noncomputable def canonicalPreBlockCarryCarrier
+    (n : OddNat) (H m : ℕ) : Finset ℕ :=
+  canonicalRecentSourceClaimCarrier n H m
+
+theorem canonicalPreBlockCarryCarrier_eq
+    (n : OddNat) (H m : ℕ) :
+    canonicalPreBlockCarryCarrier n H m =
+      carryTwoPositions n
+        (Finset.Ico (canonicalBlockStartTime n m - H)
+          (canonicalBlockStartTime n m)) := by
+  rfl
+
+/-- Exact carrier form: deficit is outstanding queue minus recent carry mass. -/
+theorem canonicalSourceAgeDeficit_eq_queue_sub_preBlockCarryCarrier_card
+    (n : OddNat) (H m : ℕ) :
+    canonicalSourceAgeDeficit n H m =
+      canonicalOutstandingClaimQueueBeforeBlock n m -
+        (canonicalPreBlockCarryCarrier n H m).card := by
+  simpa [canonicalSourceAgeDeficit, canonicalPreBlockCarryCarrier] using
+    canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent
+      n H m
+
+/-- Uniform source age is exactly cardinal coverage by the finite pre-block
+carry carrier. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_preBlockCarry
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤
+        (canonicalPreBlockCarryCarrier n H m).card := by
+  rw [canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_deficit_nonpos]
+  constructor <;> intro h m
+  · have hdef := h m
+    rw [canonicalSourceAgeDeficit_eq_queue_sub_preBlockCarryCarrier_card]
+      at hdef
+    omega
+  · rw [canonicalSourceAgeDeficit_eq_queue_sub_preBlockCarryCarrier_card]
+    have hle := h m
+    omega
+
+/-! ## Exact saturated-successor two-block normal form -/
+
+namespace CanonicalSaturatedBorderBlock
+
+theorem sourceAgeFrontierWindowSum_zero_two_eq
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 2 =
+      1 + max
+        (-(canonicalOutstandingClaimQueueBeforeBlock n (m + 1) : ℤ))
+        (endpointAccountingTerm n (m + 1)) := by
+  rw [canonicalSourceAgeFrontierWindowSum_two,
+    h.sourceAgeFrontierIncrement_zero_eq_one,
+    canonicalSourceAgeFrontierIncrement_zero_eq_max]
+
+/-- Strictly negative successor drift repays the saturated unit within the
+exact two-block horizon-zero window. -/
+theorem sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_drift_neg
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hnegative : endpointAccountingTerm n (m + 1) < 0) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 2 ≤ 0 := by
+  rw [canonicalSourceAgeFrontierWindowSum_two,
+    h.sourceAgeFrontierIncrement_zero_eq_one]
+  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
+    rw [h.queueBeforeBlock_succ_eq_add_one]
+    omega
+  have hnext :=
+    canonicalSourceAgeFrontierIncrement_zero_le_neg_one_of_drift_neg
+      hqueue hnegative
+  omega
+
+/-- Zero successor drift leaves the saturated unit exactly unpaid over the
+two-block horizon-zero window. -/
+theorem sourceAgeFrontierWindowSum_zero_two_eq_one_of_successor_drift_eq_zero
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hzero : endpointAccountingTerm n (m + 1) = 0) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 2 = 1 := by
+  rw [canonicalSourceAgeFrontierWindowSum_two,
+    h.sourceAgeFrontierIncrement_zero_eq_one,
+    canonicalSourceAgeFrontierIncrement_zero_eq_zero_of_drift_eq_zero hzero]
+  norm_num
+
+/-- Positive successor drift is added unchanged to the saturated unit. -/
+theorem sourceAgeFrontierWindowSum_zero_two_eq_add_drift_of_successor_drift_pos
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hpositive : 0 < endpointAccountingTerm n (m + 1)) :
+    canonicalSourceAgeFrontierWindowSum n 0 m 2 =
+      1 + endpointAccountingTerm n (m + 1) := by
+  rw [canonicalSourceAgeFrontierWindowSum_two,
+    h.sourceAgeFrontierIncrement_zero_eq_one,
+    canonicalSourceAgeFrontierIncrement_zero_eq_drift_of_drift_pos hpositive]
+
+end CanonicalSaturatedBorderBlock
+
+/-! ## Root-123 zero-drift obstruction -/
+
+/-- The exact horizon-zero pattern at root 123 is `[1, 0]`: the saturated
+unit survives the following zero-drift block. -/
+theorem canonicalSourceAgeFrontierWindowSum_oneTwentyThree_zero_zero_two :
+    canonicalSourceAgeFrontierWindowSum
+      oneTwentyThreeSaturatedOdd 0 0 2 = 1 := by
+  have hsat := canonicalSaturatedBorderBlock_oneTwentyThree_zero
+  exact hsat.sourceAgeFrontierWindowSum_zero_two_eq_one_of_successor_drift_eq_zero
+    endpointAccountingTerm_oneTwentyThree_one
+
+/-- Nonpositive successor drift is not sufficient for two-block repayment.
+The strict inequality in the negative-drift theorem is therefore sharp. -/
+theorem not_forall_saturated_nonpos_successor_drift_two_block_nonpos :
+    ¬ ∀ (n : OddNat) (m : ℕ),
+      CanonicalSaturatedBorderBlock n m →
+        endpointAccountingTerm n (m + 1) ≤ 0 →
+          canonicalSourceAgeFrontierWindowSum n 0 m 2 ≤ 0 := by
+  intro h
+  have hnonpos := h oneTwentyThreeSaturatedOdd 0
+    canonicalSaturatedBorderBlock_oneTwentyThree_zero
+    (by rw [endpointAccountingTerm_oneTwentyThree_one])
+  rw [canonicalSourceAgeFrontierWindowSum_oneTwentyThree_zero_zero_two]
+    at hnonpos
+  omega
+
 /-! ## Saturated-successor actual-consumption bridge -/
 
 /-- Saturation leaves at least one queued claim for the successor, while every
@@ -787,45 +1411,30 @@ theorem
     {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
     (hnegative : endpointAccountingTerm n (m + 1) < 0) :
     canonicalSourceAgeFrontierWindowSum n 0 m 2 ≤ 0 := by
-  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
-    n (m + 1)
-  change endpointAccountingTerm n (m + 1) =
-      (canonicalQueueDemand n (m + 1) : ℤ) -
-        canonicalQueueService n (m + 1) at hdrift
-  have hservice : canonicalQueueDemand n (m + 1) + 1 ≤
-      canonicalQueueService n (m + 1) := by omega
-  have hqueue : 1 ≤ canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
-    rw [h.queueBeforeBlock_succ_eq_add_one]
-    omega
-  have havailable : canonicalQueueDemand n (m + 1) + 1 ≤
-      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
-        canonicalQueueDemand n (m + 1) := by omega
-  have hconsumed : canonicalQueueDemand n (m + 1) + 1 ≤
-      canonicalQueueConsumed n (m + 1) := by
-    unfold canonicalQueueConsumed
-    exact le_min havailable hservice
-  rw [canonicalSourceAgeFrontierWindowSum_two,
-    h.sourceAgeFrontierIncrement_zero_eq_one,
-    canonicalSourceAgeFrontierIncrement_zero_eq_demand_sub_consumed]
-  omega
+  exact h.sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_drift_neg
+    hnegative
 
 /-!
 ## Conditional challenge-facing boundary
 
-The positive route now has an exact public chain:
+The source-age challenge is now separated into three levels:
 
-1. externally construct a noncircular
-   `CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature`;
-2. obtain all nonpositive frontier prefixes;
-3. obtain uniform actual source age `H`;
-4. obtain queue bound `H` and endpoint-width bound `bitWidth n + H`.
+1. target: exhibit some `H` whose every actual frontier prefix is
+   nonpositive;
+2. one sufficient route: externally construct a noncircular finite structural
+   certificate whose realized weights are the actual frontier increments;
+3. later global work: endpoint-to-all-time width transport, finite-state
+   periodicity, nontrivial-cycle elimination, and translation to the raw
+   challenge.
 
 This module does **not** construct such a signature/certificate or prove that
-some horizon `H` works.  The bounded audit is discovery evidence only.  The
-saturated-successor split supplies positive successor consumption, and its
-strictly-negative branch supplies a two-block repayment theorem, but the
-zero-drift and positive-pressure branches do not currently give the uniform
-window consumption lower bound required for the global certificate.
+some horizon `H` works.  Certificate construction is not claimed to be the
+only logically possible proof of uniform source age.  The exact H0 max normal
+form also proves that positive endpoint drift is transmitted unchanged, so a
+one-step consumption lower bound cannot repay that branch at H0; a longer
+future window, positive horizon, or separate pressure potential is required.
+At H1, mature saturated blocks are neutral, while successor flow is governed
+by the explicit predecessor/demand/final-boundary/consumption balance above.
 -/
 
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-338.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-338.md
new file mode 100644
index 00000000..b08df4ff
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-338.md
@@ -0,0 +1,218 @@
+# Petal / Collatz implementation report: checkpoint 338
+
+Date: 2026-07-17
+
+## Status
+
+Checkpoint 338 is complete.  Every requested local arithmetic stage closed in
+Lean without `sorry`, including the predecessor-carry obstruction that had
+previously been supported only by the bounded audit.
+
+The implementation is in:
+
+```text
+DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
+```
+
+## Implemented results
+
+### Crossing-block boundary removal
+
+`mem_crossingClaims_canonicalAgeCrossingBlockOfSource` now requires only
+`CarryTwoDebtAt n i`.  The proof uses the exact block containing `i + H` and
+the natural subtraction equivalences directly.  It also covers the origin and
+underflow regime; the former auxiliary boundary hypothesis was unnecessary.
+
+### Exact horizon-zero reflected normal form
+
+The new theorem
+
+```text
+canonicalSourceAgeFrontierIncrement_zero_eq_max
+```
+
+proves
+
+```text
+frontier(0,m) = max (-queueBefore(m)) endpointDrift(m).
+```
+
+It yields the exact trichotomy:
+
+- negative drift and a nonempty queue give frontier at most `-1`;
+- zero drift gives frontier exactly `0`;
+- positive drift is transmitted unchanged.
+
+Thus one-step actual consumption cannot erase positive endpoint drift at
+horizon zero.  Such repayment needs a longer window, a positive horizon, or a
+separate potential.
+
+### Saturated two-block trichotomy and root 123
+
+For a saturated block, the exact two-block expression is
+
+```text
+1 + max (-queueBefore(successor)) endpointDrift(successor).
+```
+
+The strict branches are now formal:
+
+- successor drift `< 0` implies a nonpositive two-block sum;
+- successor drift `= 0` gives sum exactly `1`;
+- successor drift `> 0` gives `1 + drift`.
+
+Root 123 was reconstructed entirely in Lean.  The implementation proves:
+
+```text
+CanonicalSaturatedBorderBlock oneTwentyThreeSaturatedOdd 0
+endpointAccountingTerm oneTwentyThreeSaturatedOdd 1 = 0
+canonicalSourceAgeFrontierWindowSum oneTwentyThreeSaturatedOdd 0 0 2 = 1
+```
+
+Consequently, the universal claim with merely nonpositive successor drift is
+formally false.  The negative theorem is sharp at `< 0`.
+
+### Mature saturated horizons
+
+For `H <= canonicalBlockStartTime n m`, a saturated length-two block has the
+exact carrier decomposition into two shifted singleton boundaries.  Therefore
+
+```text
+frontier(H,m)
+  = indicator(start-H) + indicator(start-H+1) - 1.
+```
+
+The `H > start` regime remains explicitly separate because natural
+subtraction would otherwise alias underflowed addresses.
+
+### Predecessor-carry obstruction
+
+The bounded observation has become a general theorem:
+
+```text
+CanonicalSaturatedBorderBlock.predecessor_not_carryTwo
+```
+
+For every mature saturated block, the immediately preceding source is not a
+carry-two source.  The proof is not a residue-only argument.  Saturation first
+places the start state strictly above three quarters of its binary window.
+Assuming a carry-two predecessor, the exact predecessor transition
+
+```text
+3*y + 1 = 2^(s y) * x
+```
+
+and the one-step binary-width balance place `y` in an incompatible window.
+This contradiction proves the obstruction.
+
+The direct consequence is:
+
+```text
+CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_one_eq_zero
+```
+
+Every mature saturated block is exactly neutral at horizon one.  This is now
+a theorem, not numerical evidence.
+
+### Horizon-one successor balance
+
+The successor of a saturated block satisfies an exact four-term identity:
+
+```text
+successor frontier at H=1
+  = predecessor boundary unit
+      + successor demand
+      - successor final-source indicator
+      - successor actual consumption.
+```
+
+The predecessor unit is always present, but successor actual consumption is
+positive and cancels that unit.  Therefore a remaining successor value `+1`
+requires at least one nonfinal current-block carry.  It is not caused by the
+inherited predecessor boundary alone.
+
+### Horizon telescope and finite carrier
+
+`canonicalRecentCarryMassBeforeStart` gives the reverse-offset finite sum of
+carry indicators.  In the mature regime:
+
+```text
+deficit(H,m) = deficit(0,m) - recentCarryMass(H,m)
+             = queueBefore(m) - recentCarryMass(H,m).
+```
+
+The corresponding frontier identity is the exact coboundary formula:
+
+```text
+frontier(H,m)
+  = frontier(0,m)
+      + recentCarryMass(H,m)
+      - recentCarryMass(H,m+1).
+```
+
+`canonicalPreBlockCarryCarrier` exposes the existing recent source carrier
+under the requested name.  Uniform source age is exactly equivalent to
+
+```text
+forall m, queueBefore(m) <= card (preBlockCarryCarrier H m).
+```
+
+No anonymous queue elements were identified with source addresses; this is
+the existing FIFO/cardinality theorem, reused through an honest bridge.
+
+## Facts now fixed
+
+1. Horizon-zero frontier flow is a reflected maximum, not raw endpoint drift.
+2. Zero successor drift does not repay a saturated unit.
+3. Mature saturated blocks are always neutral at horizon one.
+4. A horizon-one successor `+1` comes from nonfinal successor carry mass after
+   actual consumption, not from the predecessor unit alone.
+5. Positive horizon changes frontier flow by an exact finite carry
+   coboundary.
+6. The source-age target can be stated entirely as finite recent-carrier
+   cardinal coverage at each block.
+
+## Honest boundary
+
+This checkpoint does not prove that some uniform horizon exists.  It also does
+not construct a finite structural potential certificate.  A finite signature
+makes only the potential-maximum field finite-state checkable; transition
+realization and actual-weight soundness remain all-time arithmetic
+obligations.
+
+The source-age target and one sufficient certificate method remain distinct.
+Later global work still includes endpoint-to-all-time width transport,
+finite-state periodicity, nontrivial-cycle elimination, and translation to the
+raw challenge.
+
+## Suggested next implementation
+
+The local horizon algebra is now sufficiently normalized.  The next useful
+checkpoint should work at the certificate-construction boundary rather than
+add more aliases:
+
+1. define a genuinely finite reachable signature carrier for the frontier
+   state;
+2. separate finite reachability from all-time step realization;
+3. test whether the horizon coboundary and pre-block carry carrier determine
+   enough state to make the actual frontier weight local;
+4. if not, produce the exact pair of histories with equal proposed signature
+   and different next frontier weight as an obstruction theorem.
+
+The failure mode should be formalized rather than hidden by adding deficit or
+future-prefix data to the signature, because either would make the proposed
+certificate circular.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|admit|axiom" \
+  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
+git diff --check
+```
+
+The `rg` check returned no matches.
````
`````
