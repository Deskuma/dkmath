# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource

gch: 3f9168214ecee49432ec002ccb848fde06a610b3

## Report

(13m15s)

checkpoint 329 を完了しました。

主な成果:

- block-core word と隣接深度 recurrence を定理化
- saturated successor の rigid profile を固定
- 三分岐の局所 discharge 証明を統合
- length-one successor の返済則と mod 16 分岐を証明
- carry が `2 → 1 → 2` と再上昇する反例を Lean で固定
- 非循環な amortized-resource 遷移モデルを新設
- 累積 replenishment 上界から queue、endpoint width 上界を導出

重要な結論は、局所 successor 理論は閉じましたが、大域化には「時間方向の資源所有」と「累積 replenishment 上界」が必要だということです。単点ごとの replenishment 上界だけでは線形成長を許すため不十分です。これは現在の真正な境界としてコードコメントにも記録しています。

検証はすべて成功しています。

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 変更対象に `sorry`、`maxHeartbeats` なし

詳細は [report-petal-329.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md) にまとめました。

## Review

## 結論

snapshot の SHA-256 は提示値、

```text
69d2786fc502f1009b2b398a400590e9f9288000097dc354c199743536fe6e11
```

と完全一致した。最新 snapshot の実コードを基準に精査している。

判定は二分される。

- **block-core API、rigid successor、局所 abstract discharge は採用**
- **`CanonicalNoncircularGlobalAmortizationLaw` の「非循環」という解釈は差し戻し**

したがって checkpoint 全体としては、**条件付き採用**じゃ。

cp-329 は、局所 saturated-successor 理論をきれいに閉じた。一方、新設された amortized law は現状、uniform queue bound から自明に構成できるため、存在命題としては queue bound の言い換えになっている。report が述べる temporal ownership の不足自体は正しいが、その不足を新 structure はまだ表現できていない。

---

## 1. Block-core word API

```lean
canonicalBlockCoreWordAtDepth
iterateT_sourceAtDepth_eq_coreWordAtDepth
mem_claimDepths_iff_coreWordAtDepth_carryTwo
```

の追加は非常によい。

有効 depth $d$ について、

$$\operatorname{CoreWord}(d)=2^d3^{L-d}u-1$$

となり、実際の orbit state と一致する。

さらに claim membership が、

$$d\in\operatorname{Claims}\iff\operatorname{stateUpperCarry}(\operatorname{CoreWord}(d))=2$$

として固定された。

これで claim profile は、

```text
orbit time の定義
→ block length / odd core / depth の有限算術
```

へ完全に移された。

これは今後の residue grammar、carry pattern、hole density の主力 API になる。

---

## 2. 隣接 depth recurrence

今回、

$$3(\operatorname{CoreWord}(d+1)+1)=2(\operatorname{CoreWord}(d)+1)$$

および、

$$\operatorname{SourceAtDepth}(d+1)+1=\operatorname{SourceAtDepth}(d)$$

が証明された。

前者は state 値の $3:2$ 遷移、後者は orbit address の一歩遷移じゃ。

この二本を同時に持ったことで、

```text
算術 state transition
orbit source transition
claim / hole transition
```

を同じ depth step で追える。

ここは完全採用でよい。

---

## 3. Carry alternation witness

```lean
coreWordRecurrence_carry_alternation_witness
```

は、

$$53\longrightarrow35\longrightarrow23$$

という recurrence 上で、

$$2\longrightarrow1\longrightarrow2$$

の carry pattern が起こることを示した。

これは recurrence だけから carry monotonicityを導けないことを確定する。

しかも、この数値列は偶然の抽象反例ではない。

$$53+1=2^1\cdot3^2\cdot3$$

$$35+1=2^2\cdot3^1\cdot3$$

$$23+1=2^3\cdot3^0\cdot3$$

なので、$L=3,u=3$ の exact core-word profile そのものじゃ。

したがって次には、root $23$ の canonical block regression として、

```lean
blockLength = 3
oddCore = 3
claimDepths = {1, 3}
claimHoles = {2}
```

まで package するとよい。

ただし、この反例が止めたのは **monotonicity route** だけじゃ。

```text
carry が単調ではない
```

から、

```text
claim-hole density に一様下界が存在しない
```

までは従わない。

report の「Route 1 stops」は、

> recurrence 単独による単調 claim-density route は停止した

と限定するのが正確じゃ。

有限状態 grammar や bounded-gap route はまだ残っている。

---

## 4. Rigid successor profile

saturated predecessor の successor について、次が閉じた。

### Zero-carrier balanced successor

$$L=2,\qquad v=1,\qquad A=1$$

さらに、

$$\operatorname{ClaimHoles}={2}$$

$$\operatorname{ClaimDepths}={1}$$

となる。

full-balanced branch は deepest hole の存在と矛盾するため消滅した。

### Tight valuation-one positive successor

唯一の hole は最深 depth になる。

$$\operatorname{ClaimHoles}={L}$$

$$\operatorname{ClaimDepths}=\operatorname{Icc}(1,L-1)$$

これは非常に強い。

以前の「一個だけ hole がある」という匿名的な情報が、

> block start に対応する最深 depth だけが hole

まで固定された。

ここも全面採用じゃ。

---

## 5. Unified local discharge

```lean
CanonicalSaturatedSuccessorAbstractDischarge
```

は三分岐を正しくまとめている。

### Negative

$$D_{k+1}<0$$

かつ、

$$D_k+D_{k+1}\le0$$

### Zero

$$D_{k+1}=0,\qquad L_{k+1}\ge2$$

かつ、

```lean
Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1)
```

### Positive

$$D_{k+1}>0$$

かつ successor は nonsaturated で、

- saturated unit は lower slots
- successor demand は upper half

へ入り、像は非交差。

この inductive certificate は、各符号分岐に必要な局所証明を一箇所へ集約している。

report が明記する通り、三 constructor は同じ種類の大域 resource を与えているわけではない。

- negative branch は scalar cancellation
- zero / positive branch は abstract dyadic embedding

じゃ。

したがって「局所 discharge」という統一語は使えるが、一つの global carrier へそのまま和を取ることはできない。この意味境界も守られている。

---

## 6. Length-one successor

length-one successor について、

$$A_{k+1}=0$$

$$D_{k+1}\le-1$$

$$D_k+D_{k+1}\le0$$

が統合 theorem になった。

さらに、

$$u\equiv11\pmod{16}\Longrightarrow D_k+D_{k+1}=0$$

$$u\equiv3\pmod{16}\Longrightarrow D_k+D_{k+1}\le-1$$

まで閉じている。

これで cp-327 にあった exceptional persistence narrative は完全に置き換えられた。

局所 successor 理論は閉じたと評価してよい。

---

## 7. Amortized law の決定的問題

新 structure は次の形じゃ。

```lean
structure CanonicalAmortizedResourceTransition (n : OddNat) where
  State : ℕ → Type
  state : (k : ℕ) → State k
  potential : ℕ → ℕ
  queue : ℕ → ℕ
  demand : ℕ → ℕ
  consumed : ℕ → ℕ
  replenishment : ℕ → ℕ
  demand_le_consumed_add_nextQueue : ...
  step_conservation : ...
```

そして、

```lean
CanonicalNoncircularGlobalAmortizationLaw
```

は queue observable を canonical queue に一致させ、potential と cumulative replenishment の上界を要求する。

見た目は非循環に見える。

しかし実際には、uniform queue bound からこの structure を自明に構成できる。

---

## 8. Queue bound からの自明構成

uniform queue bound、

$$Q_k\le C$$

を仮定する。

次のように置く。

$$P_k:=C-Q_k$$

$$\operatorname{demand}_k:=0$$

$$\operatorname{consumed}_k:=0$$

$$\operatorname{replenishment}_k:=0$$

`State k` は `PUnit` でよい。

$Q_k\le C$ なので、

$$Q_k+P_k=C$$

である。

したがって一段保存則は、

$$Q_{k+1}+P_{k+1}+0=C=Q_k+P_k+0$$

となる。

`demand_le_consumed_add_nextQueue` も、

$$0\le0+Q_{k+1}$$

なので自明じゃ。

potential は常に $C$ 以下で、累積 replenishment は常に $0$。

よって、

```lean
CanonicalOutstandingClaimQueueUniformUpperBound n C
```

から、

```lean
CanonicalNoncircularGlobalAmortizationLaw n C 0
```

を構成できる。

Lean の形では概ねこうなる。

```lean
noncomputable def trivialAmortizedTransitionOfQueueBound
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    CanonicalAmortizedResourceTransition n where
  State := fun _ => PUnit
  state := fun _ => PUnit.unit
  potential := fun k => C - canonicalOutstandingClaimQueue n k
  queue := canonicalOutstandingClaimQueue n
  demand := fun _ => 0
  consumed := fun _ => 0
  replenishment := fun _ => 0
  demand_le_consumed_add_nextQueue := by
    intro k
    simp
  step_conservation := by
    intro k
    have hk := hC k
    have hk1 := hC (k + 1)
    omega
```

---

## 9. Existential levelでは同値

cp-329 は既に、

$$\operatorname{AmortizationLaw}(P,R)\Longrightarrow\operatorname{QueueBound}(Q_0+P+R)$$

を証明している。

今示した逆向きと合わせると、

$$\left(\exists P,R,\ \operatorname{AmortizationLaw}(P,R)\right)\iff\left(\exists C,\ \operatorname{QueueBound}(C)\right)$$

となる。

つまり、Collatz Challenge へ必要な existential uniform bound の水準では、

```text
CanonicalNoncircularGlobalAmortizationLaw
```

は queue bound の別表現じゃ。

論理矛盾はない。

しかし、

> 目的の queue bound を仮定せずに置ける、独立した非循環 resource law

にはまだなっていない。

---

## 10. Structure 内の未接続フィールド

この問題は API の使われ方にも現れている。

### `State` と `state`

どの theorem でも使用されていない。

`PUnit` で埋められるため、resource state の意味を何も制約しない。

### `demand`

queue bound の証明に一度も使われない。

常に $0$ と置ける。

canonical claim count、positive drift、dyadic demand のいずれにも接続していない。

### `consumed`

`step_conservation` に現れるが、実 source incidence や abstract discharge certificate には接続していない。

常に $0$ と置ける。

### `replenishment`

負 drift、width decrease、claim hole、actual source carrierのいずれにも接続していない。

任意の自然数列として置ける。

### `n`

structure parameter にあるが、field の型や法則に具体的な Collatz データを要求していない。

したがって structure 自体は、実質的に任意の自然数列 queue に対する抽象 accounting structure じゃ。

---

## 11. Potential ceiling の仮定も過剰

```lean
queue_le_of_potential_and_cumulative_replenishment_bounds
```

は、

```lean
hpotential : ∀ k, A.potential k ≤ P
```

を仮定する。

しかし証明中で使っているのは、

```lean
hpotential 0
```

だけじゃ。

finite-prefix theorem は、

$$Q_m+P_m\le Q_0+P_0+\sum_{k<m}R_k$$

を与える。

$P_m\ge0$ は `Nat` なので自動的に成立する。

従って queue bound に必要なのは、

$$P_0\le P$$

だけじゃ。

正確な theorem 名と statement は、

```lean
queue_le_of_initialPotential_and_cumulativeReplenishment_bounds
```

の方になる。

$$Q_m\le Q_0+P_0+R$$

で十分じゃ。

「uniform potential ceiling が queue bound を与える」という現在の説明は、証明内容より強い。

---

## 12. Generic theorem としては有効

差し戻すのは数学そのものではない。

次は有効な一般補題じゃ。

```lean
queue_add_potential_le_initial_add_sum
```

一段保存則を telescope して、

$$Q_m+P_m\le Q_0+P_0+\sum_{k<m}R_k$$

を得る theorem は正しい。

また、cumulative replenishment 上界が必要で、pointwise 上界だけでは線形成長を許すという診断も正しい。

したがって新モジュールは、

```text
generic amortized inequality library
```

としては残せる。

ただし、

```text
Canonical
Noncircular
Global
```

という三語は、現在の field surface では強すぎる。

---

## 13. Import / module 層も分離すべき

`UniversalPaymentAmortizedResource.lean` は `UniversalPaymentAmplitude` を import しているが、新 module 内では、

```lean
CanonicalSaturatedSuccessorAbstractDischarge
canonicalBlockCoreWordAtDepth
abstract dyadic carrier
```

などを一度も使用していない。

実際に使っている Collatz 固有対象は、

- `canonicalOutstandingClaimQueue`
- uniform queue bound
- endpoint width bound

だけじゃ。

したがって現在は、

```text
局所 discharge theorem
Global amortized interface
```

が import によって隣り合っているだけで、定理としては接続されていない。

推奨分割は、

```text
FiniteAmortizedResource.lean
  汎用 telescope theorem

CanonicalOwnedAmortizedResource.lean
  Collatz の具体的 demand / service / source carrier への接続
```

じゃ。

汎用 structure からは `n : OddNat` も外せる。

---

## 14. 本当に必要な ownership law

非循環にするには、field 名を増やすだけでは足りない。

少なくとも次を具体的に固定する必要がある。

### Demand

$$\operatorname{demand}(k)=\operatorname{canonicalBlockClaimCount}(n,k)$$

または対象を positive drift に限定するなら、その exact carrier cardinality。

### Queue

$$\operatorname{queue}(k)=\operatorname{canonicalOutstandingClaimQueue}(n,k)$$

### Consumption

actual service token または actual source incidence の image cardinality。

### Potential

任意の自然数列ではなく、具体的な未使用 resource Finset の cardinality。

### Replenishment

負 drift や width decrease という scalar 値ではなく、発生源を保持した実 carrier の cardinality。

### Ownership

同じ resource atom が二 block で消費されないこと。

### Temporal transition

$$\operatorname{Available}_{k+1}=(\operatorname{Available}_k\setminus\operatorname{Consumed}_k)\cup\operatorname{Replenished}_k$$

に相当する actual carrier identity。

---

## 15. arbitrary finite carrier を field にしても不十分

次のような structure を置くだけでは、同じ問題が残る。

```lean
GlobalResource : Type
[Fintype GlobalResource]
```

なぜなら queue bound $C$ を仮定して、

```lean
GlobalResource := Fin C
```

と選べるからじゃ。

本当に非循環にするには、resource carrier が、

```text
初期値 n から既に定義されている具体的型
```

でなければならない。

例えば将来、

```lean
canonicalInitialUpperResourceCarrier n
```

のような object が実装されたなら、その型を field ではなく definition として固定する。

その上で、

```text
各 block-local demand
→ canonicalInitialUpperResourceCarrier n の未使用部分
```

という ownership theorem を証明する必要がある。

---

## 16. 真正な現在地

cp-329 の local side は確実に進んだ。

```text
saturated successor の全符号分岐
→ 局所 scalar / abstract dyadic discharge
```

が閉じたからじゃ。

しかし global side は、

```text
queue bound
→ artificial complement potential
→ amortization law
```

という逆構成を許す。

したがって新 law は、まだ global obstruction を一段越えたものではない。

現在の真正な境界は、report が述べた通り、

> actual temporal ownership を持つ concrete resource transition

じゃ。

ただしその境界は、新 structure によって形式化済みなのではなく、**次に形式化すべき対象として正しく特定された**段階じゃ。

---

## 17. Challenge への距離

現在の正確な幹線は、

```text
block-core exact profile
→ saturated local discharge
→ concrete temporally-owned resource transition  [未実装]
→ cumulative nonreuse theorem                    [未実装]
→ uniform scalar queue bound
→ endpoint width bound
→ finite-state eventual periodicity
→ nontrivial cycle elimination
→ accelerated convergence
→ standard Collatz theorem
```

cp-329 は最初の二段を強くした。

第三段を abstract structure 名だけで越えたとは、まだ評価できない。

---

## 判定まとめ

### Block-core word API

**完成。**

### Adjacent depth recurrence

**完成。**

### Rigid successor profile

**完成。**

### Unified local abstract discharge

**完成。**

### Length-one repayment

**完成。**

### Carry monotonicity

**反例により否定。**

### Claim-density route

**monotonicity route は停止。一般 density route は未決。**

### Generic amortized telescope

**完成。**

### `CanonicalNoncircularGlobalAmortizationLaw`

**queue bound と existentially equivalent。非循環という解釈は差し戻し。**

### Concrete temporal ownership

**未実装。真の次戦線。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-329.

The cp-329 local block-core and saturated-successor results are accepted.

The interpretation of `CanonicalNoncircularGlobalAmortizationLaw` is not
accepted.  Its current field surface permits a trivial construction from the
desired uniform queue bound.

The next checkpoint must first formalize this circularity audit, then separate
the valid generic telescope lemma from a genuinely owned Collatz resource
transition.

## Stage A — prove the reverse construction

Assume:

    hC : CanonicalOutstandingClaimQueueUniformUpperBound n C.

Construct:

    trivialAmortizedTransitionOfQueueBound hC :
      CanonicalAmortizedResourceTransition n

using:

    State k        := PUnit
    state k        := PUnit.unit
    queue k        := canonicalOutstandingClaimQueue n k
    potential k    := C - canonicalOutstandingClaimQueue n k
    demand k       := 0
    consumed k     := 0
    replenishment k := 0.

Prove the one-step conservation from:

    queue k <= C
    queue (k + 1) <= C.

Derive:

    CanonicalOutstandingClaimQueueUniformUpperBound n C
      ->
    CanonicalNoncircularGlobalAmortizationLaw n C 0.

## Stage B — expose the existential equivalence

Prove:

    (
      exists P R,
        CanonicalNoncircularGlobalAmortizationLaw n P R
    )
      <->
    (
      exists C,
        CanonicalOutstandingClaimQueueUniformUpperBound n C
    ).

Use the existing forward theorem and Stage A for the reverse implication.

This theorem is a mandatory semantic regression.  It records that the current
law does not yet reduce the global problem.

## Stage C — correct names and documentation

Rename the current predicate to a neutral name such as:

    CanonicalAbstractAmortizationCertificate

or:

    CanonicalQueuePotentialCertificate.

Keep `CanonicalNoncircularGlobalAmortizationLaw` only as a deprecated
compatibility alias if necessary.

Remove claims that the current existential predicate is noncircular.

Correct report-petal-329 accordingly.

## Stage D — simplify the generic telescope layer

Move the generic structure and telescope theorem into a Collatz-independent
module, for example:

    DkMath/Collatz/PetalBridge/FloatWindow/FiniteAmortizedResource.lean

or a lower combinatorics namespace.

Remove the unused `n : OddNat` parameter from the generic structure.

Audit `State` and `state`:

    either remove them;
    or make potential, demand, consumption, and replenishment actual
    observables of the state.

Do not retain phantom state fields.

## Stage E — correct the potential-bound theorem

The current queue-bound proof uses only `hpotential 0`.

Prove the sharper theorem:

    queue m <= queue 0 + potential 0 + cumulativeReplenishment m.

Then provide:

    queue_le_of_initialPotential_and_cumulativeReplenishment_bounds

with hypotheses:

    potential 0 <= P
    cumulative replenishment <= R.

Keep the old uniform-potential theorem as a corollary if compatibility is
useful.

Do not describe a uniform potential ceiling as logically necessary.

## Stage F — connect demand to the canonical queue

Before using the word `Canonical`, define exact canonical observables.

At minimum expose:

    canonical demand k
      = canonicalBlockClaimCount n k;

    canonical service k
      = canonicalBlockCapacityCount n k;

    canonical consumed k
      = min
          (canonicalOutstandingClaimQueue n k + canonical demand k)
          (canonical service k).

Prove the exact queue conservation:

    queue (k + 1) + consumed k
      =
    queue k + canonical demand k.

This theorem should come from the existing reflected-queue recurrence.

## Stage G — do not permit arbitrary potential complements

A future owned potential must be the cardinality or weight of a concrete
resource object.

Do not allow:

    potential k := C - queue k

as a valid canonical instance unless `C` and the resource object are already
constructed independently from the initial Collatz state.

Define a placeholder specification only after identifying a concrete carrier:

    canonicalInitialUpperResourceCarrier n

or another actual resource type.

The carrier must be a definition from `n`, not an existential field chosen
after assuming a queue bound.

## Stage H — source-bearing ownership transition

Design the concrete transition around actual finite carriers.

It should eventually include:

    available resource carrier at block k;
    consumed subcarrier;
    replenished carrier with an actual origin;
    next available carrier;
    disjointness of old-unconsumed and newly replenished atoms;
    injective ownership of every consumed unit;
    temporal nonreuse.

Seek a carrier identity of the form:

    Available (k + 1)
      ≃
    (Available k \ Consumed k)
      Sum
    Replenished k.

Do not assert that such a Collatz instance exists yet.

## Stage I — connect local discharge to the owned layer

The current new module imports `UniversalPaymentAmplitude` but uses none of
the local discharge certificates.

Once an actual resource carrier exists, connect:

    CanonicalSaturatedSuccessorAbstractDischarge

to one transition step.

Until that theorem exists, do not describe local discharge and global
amortization as formally connected.

## Stage J — canonical carry-alternation regression

Strengthen the numeric witness `53, 35, 23` into a canonical block regression.

Use the odd root `23` and prove at its first block:

    block length = 3;
    odd core = 3;
    core words at depths 1, 2, 3 are 53, 35, 23;
    claim depths are {1, 3};
    claim holes are {2}.

Record:

    carry monotonicity fails inside an actual canonical block.

Do not conclude that every claim-density bound fails.

## Stage K — refine the route boundary

State separately:

    adjacent recurrence alone does not imply monotone carry;

    a bounded-gap or density theorem may still use additional canonical
    residue and width information.

Do not close the entire claim-density route from the single alternation
regression.

## Stage L — genuine stopping rule

Stop at the first genuine obstruction among:

    the reverse trivial amortization construction fails;
    existential equivalence cannot be proved;
    exact canonical queue consumption identity fails;
    no concrete initial resource carrier can be defined;
    replenishment events have no unique temporal origin;
    the same resource atom can be consumed more than once;
    any proposed owned law remains constructible from an assumed queue bound.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-330.md
```

cp-329 で局所会計はよく締まった。

しかし global law はまだ「資源保存の証明」ではなく、**queue bound を potential に隠せる器**じゃ。

次はこの循環を Lean 自身に暴かせ、そのうえで本当に所有権を持つ resource state を作るのが正攻法じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index bc18ca77..4c7a4327 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -26,6 +26,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
new file mode 100644
index 00000000..6a01fbfb
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
@@ -0,0 +1,119 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource"
+
+namespace DkMath.Collatz
+
+/-!
+# Transition-based amortized resource interface
+
+This module states the global resource contract without assuming a global
+injection into a pre-existing finite carrier.  A resource state evolves at
+each block.  The only accounting axiom is a one-step conservation inequality.
+
+The replenishment hypothesis below is cumulative.  A merely pointwise bound
+on replenishment would allow linear growth and cannot imply a uniform queue
+bound.  No Collatz instance of this interface is asserted here.
+-/
+
+/-- A dynamic resource state with an explicit queue, potential, demand,
+consumption, and derived replenishment stream. -/
+structure CanonicalAmortizedResourceTransition (n : OddNat) where
+  State : ℕ → Type
+  state : (k : ℕ) → State k
+  potential : ℕ → ℕ
+  queue : ℕ → ℕ
+  demand : ℕ → ℕ
+  consumed : ℕ → ℕ
+  replenishment : ℕ → ℕ
+  demand_le_consumed_add_nextQueue :
+    ∀ k, demand k ≤ consumed k + queue (k + 1)
+  step_conservation :
+    ∀ k, queue (k + 1) + potential (k + 1) + consumed k ≤
+      queue k + potential k + replenishment k
+
+namespace CanonicalAmortizedResourceTransition
+
+/-- Iterating one-step conservation gives the exact finite-prefix resource
+ceiling. -/
+theorem queue_add_potential_le_initial_add_sum
+    {n : OddNat} (A : CanonicalAmortizedResourceTransition n) (m : ℕ) :
+    A.queue m + A.potential m ≤
+      A.queue 0 + A.potential 0 + ∑ k ∈ Finset.range m, A.replenishment k := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      have hstep := A.step_conservation m
+      rw [Finset.sum_range_succ]
+      omega
+
+/-- A uniform potential ceiling and a cumulative replenishment ceiling imply
+a uniform queue ceiling. -/
+theorem queue_le_of_potential_and_cumulative_replenishment_bounds
+    {n : OddNat} (A : CanonicalAmortizedResourceTransition n)
+    {P R : ℕ} (hpotential : ∀ k, A.potential k ≤ P)
+    (hreplenishment : ∀ m,
+      ∑ k ∈ Finset.range m, A.replenishment k ≤ R) (m : ℕ) :
+    A.queue m ≤ A.queue 0 + P + R := by
+  have hprefix := A.queue_add_potential_le_initial_add_sum m
+  have hp0 := hpotential 0
+  have hr := hreplenishment m
+  omega
+
+end CanonicalAmortizedResourceTransition
+
+/--
+Noncircular conditional interface for the canonical queue.  It asks for a
+transition law whose queue observable is the existing canonical queue, plus
+independently stated potential and cumulative-replenishment ceilings.  It does
+not include the desired queue bound as a field.
+-/
+def CanonicalNoncircularGlobalAmortizationLaw
+    (n : OddNat) (P R : ℕ) : Prop :=
+  ∃ A : CanonicalAmortizedResourceTransition n,
+    (∀ m, A.queue m = canonicalOutstandingClaimQueue n m) ∧
+      (∀ k, A.potential k ≤ P) ∧
+        ∀ m, ∑ k ∈ Finset.range m, A.replenishment k ≤ R
+
+/-- The noncircular amortization law yields a named uniform scalar queue
+bound. -/
+theorem CanonicalNoncircularGlobalAmortizationLaw.to_queueUniformUpperBound
+    {n : OddNat} {P R : ℕ}
+    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n
+      (canonicalOutstandingClaimQueue n 0 + P + R) := by
+  rcases h with ⟨A, hqueue, hpotential, hreplenishment⟩
+  intro m
+  rw [← hqueue m, ← hqueue 0]
+  exact A.queue_le_of_potential_and_cumulative_replenishment_bounds
+    hpotential hreplenishment m
+
+/-- Conditional challenge-facing chain from amortization to endpoint width. -/
+theorem CanonicalNoncircularGlobalAmortizationLaw.to_endpointWidthUniformUpperBound
+    {n : OddNat} {P R : ℕ}
+    (h : CanonicalNoncircularGlobalAmortizationLaw n P R) :
+    CanonicalEndpointWidthUniformUpperBound n
+      (bitWidth n.1 + (canonicalOutstandingClaimQueue n 0 + P + R)) :=
+  h.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
+
+/-!
+## Proven frontier
+
+Route 1 stops at a concrete obstruction: exact adjacent core-word recurrence
+permits carry alternation, so it supplies no monotone claim-density estimate.
+
+Route 2 is now logically sound but conditional.  The first missing theorem is
+an actual Collatz construction of `CanonicalNoncircularGlobalAmortizationLaw`
+with a cumulative replenishment ceiling.  Current width decreases and negative
+local drift do not yet carry temporal ownership, so the same replenishment
+event could be reused without a proved multiplicity bound.  Replacing this
+missing construction by a queue ceiling would be circular.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index 063715f9..6251f9b2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -1712,6 +1712,76 @@ theorem mem_canonicalPaymentClaimDepths_iff_stateUpperCarry_coreWord
     unfold CarryTwoDebtAt
     simpa [hstate] using hcarry
 
+/-- Exact block-core word observed at positive depth `d`. -/
+noncomputable def canonicalBlockCoreWordAtDepth
+    (n : OddNat) (k d : ℕ) : ℕ :=
+  2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
+    canonicalBlockOddCore n k - 1
+
+/-- Caller-facing form of the exact source-state formula. -/
+theorem iterateT_sourceAtDepth_eq_coreWordAtDepth
+    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
+    (hdL : d ≤ canonicalBlockLength n k) :
+    (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 =
+      canonicalBlockCoreWordAtDepth n k d := by
+  unfold canonicalBlockCoreWordAtDepth
+  have h := canonicalPaymentSourceAtDepth_iterate_add_one_eq n k d hd1 hdL
+  omega
+
+/-- Caller-facing claim test through the exact block-core word. -/
+theorem mem_claimDepths_iff_coreWordAtDepth_carryTwo
+    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
+    (hdL : d ≤ canonicalBlockLength n k) :
+    d ∈ canonicalPaymentClaimDepths n k ↔
+      stateUpperCarry (canonicalBlockCoreWordAtDepth n k d) = 2 := by
+  simpa [canonicalBlockCoreWordAtDepth] using
+    mem_canonicalPaymentClaimDepths_iff_stateUpperCarry_coreWord n k d hd1 hdL
+
+/-- Adjacent core words satisfy the exact internal `3:2` recurrence. -/
+theorem canonicalBlockCoreWordAtDepth_succ_recurrence
+    (n : OddNat) (k d : ℕ) (_hd1 : 1 ≤ d)
+    (hdL : d < canonicalBlockLength n k) :
+    3 * (canonicalBlockCoreWordAtDepth n k (d + 1) + 1) =
+      2 * (canonicalBlockCoreWordAtDepth n k d + 1) := by
+  unfold canonicalBlockCoreWordAtDepth
+  have hu := canonicalBlockOddCore_pos n k
+  have hpow : canonicalBlockLength n k - d =
+      (canonicalBlockLength n k - (d + 1)) + 1 := by omega
+  rw [hpow, pow_succ]
+  rw [pow_succ]
+  have hposS : 0 < 2 ^ d * 2 *
+      3 ^ (canonicalBlockLength n k - (d + 1)) *
+        canonicalBlockOddCore n k := by positivity
+  have hposD : 0 < 2 ^ d *
+      (3 ^ (canonicalBlockLength n k - (d + 1)) * 3) *
+        canonicalBlockOddCore n k := by positivity
+  rw [Nat.sub_add_cancel hposS, Nat.sub_add_cancel hposD]
+  ring
+
+/-- Increasing depth by one walks one source-time step backwards. -/
+theorem canonicalPaymentSourceAtDepth_succ_add_one
+    (n : OddNat) (k d : ℕ) (_hd1 : 1 ≤ d)
+    (hdL : d < canonicalBlockLength n k) :
+    canonicalPaymentSourceAtDepth n k (d + 1) + 1 =
+      canonicalPaymentSourceAtDepth n k d := by
+  unfold canonicalPaymentSourceAtDepth
+  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+  omega
+
+/--
+The exact adjacent recurrence alone does not make carry profiles monotone.
+The words `53, 35, 23` satisfy the same consecutive `3:2` recurrence while
+their own-width carries alternate `2, 1, 2`.  Additional canonical-block
+information is therefore required for any claim-hole density theorem.
+-/
+theorem coreWordRecurrence_carry_alternation_witness :
+    3 * (35 + 1) = 2 * (53 + 1) ∧
+      3 * (23 + 1) = 2 * (35 + 1) ∧
+        stateUpperCarry 53 = 2 ∧
+          stateUpperCarry 35 = 1 ∧
+            stateUpperCarry 23 = 2 := by
+  norm_num [stateUpperCarry, upperCarry3n1, bitWidth]
+
 /-- Positive depths in the block which do not carry a canonical payment
 claim. -/
 noncomputable def canonicalBlockClaimHoles
@@ -2175,6 +2245,114 @@ theorem exceptionalLengthTwoBalanced_claimDepths_eq_erase_missing
   canonicalPaymentClaimDepths_eq_Icc_erase_missingDepth
     (claimHoles_card_eq_one_of_exceptional_length_two_balanced hL hclaim)
 
+/-- A zero-carrier balanced successor of a saturated block is forced into the
+exceptional length-two branch; the full-balanced branch is excluded by the
+successor's mandatory deepest hole. -/
+theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_exact_data
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
+    canonicalBlockLength n (k + 1) = 2 ∧
+      canonicalBlockTerminalValuation n (k + 1) = 1 ∧
+        canonicalBlockClaimCount n (k + 1) = 1 := by
+  rcases (canonicalZeroCarrierBalancedBorderBlock_iff n (k + 1)).1 hzero with
+    hfull | hexceptional
+  · have hholes := claimHoles_card_eq_zero_of_full_balanced hfull.1 hfull.2
+    have hnonempty := h.one_le_next_claimHoles_card
+    omega
+  · exact ⟨hexceptional.2.1, hexceptional.1, hexceptional.2.2⟩
+
+/-- The exceptional successor holes consist exactly of its deepest depth. -/
+theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_claimHoles_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
+    canonicalBlockClaimHoles n (k + 1) = {2} := by
+  have hdata := h.zeroCarrierBalanced_next_exact_data hzero
+  have hcard := claimHoles_card_eq_one_of_exceptional_length_two_balanced
+    hdata.1 hdata.2.2
+  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
+  have hmem := h.next_length_mem_claimHoles
+  rw [hdata.1, ha] at hmem
+  simp only [Finset.mem_singleton] at hmem
+  simpa [hmem] using ha
+
+/-- The exceptional successor claim carrier is the singleton endpoint depth. -/
+theorem CanonicalSaturatedBorderBlock.zeroCarrierBalanced_next_claimDepths_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hzero : CanonicalZeroCarrierBalancedBorderBlock n (k + 1)) :
+    canonicalPaymentClaimDepths n (k + 1) = {1} := by
+  classical
+  have hdata := h.zeroCarrierBalanced_next_exact_data hzero
+  have hholes := h.zeroCarrierBalanced_next_claimHoles_eq hzero
+  ext d
+  constructor
+  · intro hd
+    have hi := (mem_canonicalPaymentClaimDepths_iff.mp hd)
+    have hiL : d ≤ canonicalBlockLength n (k + 1) := by
+      simpa [canonicalBlockLength] using hi.2.1
+    have hne : d ≠ 2 := by
+      intro heq
+      have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) := by
+        rw [hholes, heq]
+        simp
+      exact (Finset.mem_sdiff.mp hhole).2 hd
+    simp only [Finset.mem_singleton]
+    omega
+  · intro hd
+    simp only [Finset.mem_singleton] at hd
+    subst d
+    by_contra hnot
+    have hhole : 1 ∈ canonicalBlockClaimHoles n (k + 1) :=
+      Finset.mem_sdiff.mpr ⟨by simp [hdata.1], hnot⟩
+    rw [hholes] at hhole
+    simp at hhole
+
+/-- A tight valuation-one positive successor misses exactly its deepest depth. -/
+theorem CanonicalSaturatedBorderBlock.tightValOne_next_claimHoles_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (htight : CanonicalTightValuationOnePositiveBlock n (k + 1)) :
+    canonicalBlockClaimHoles n (k + 1) =
+      {canonicalBlockLength n (k + 1)} := by
+  have hcard :=
+    ((canonicalTightValuationOnePositiveBlock_iff_claimHoles_card_eq_one
+      n (k + 1)).1 htight).2.2.2
+  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
+  have hmem := h.next_length_mem_claimHoles
+  rw [ha] at hmem
+  simp only [Finset.mem_singleton] at hmem
+  simpa [hmem] using ha
+
+/-- A tight valuation-one positive successor claims every depth strictly below
+its deepest depth. -/
+theorem CanonicalSaturatedBorderBlock.tightValOne_next_claimDepths_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (htight : CanonicalTightValuationOnePositiveBlock n (k + 1)) :
+    canonicalPaymentClaimDepths n (k + 1) =
+      Finset.Icc 1 (canonicalBlockLength n (k + 1) - 1) := by
+  classical
+  have hholes := h.tightValOne_next_claimHoles_eq htight
+  ext d
+  constructor
+  · intro hd
+    have hi := mem_canonicalPaymentClaimDepths_iff.mp hd
+    have hiL : d ≤ canonicalBlockLength n (k + 1) := by
+      simpa [canonicalBlockLength] using hi.2.1
+    have hne : d ≠ canonicalBlockLength n (k + 1) := by
+      intro heq
+      have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) := by
+        rw [hholes, heq]
+        simp
+      exact (Finset.mem_sdiff.mp hhole).2 hd
+    simp only [Finset.mem_Icc]
+    omega
+  · intro hd
+    simp only [Finset.mem_Icc] at hd
+    by_contra hnot
+    have hhole : d ∈ canonicalBlockClaimHoles n (k + 1) :=
+      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hd.1, by omega⟩, hnot⟩
+    rw [hholes] at hhole
+    simp only [Finset.mem_singleton] at hhole
+    omega
+
 /-! ## Saturated-successor source classification
 
 The five-way classification proposed at cp-325 omitted a logically possible
@@ -2652,9 +2830,13 @@ theorem canonicalBlockClaimCount_eq_one_iff_endpoint_carryTwo_of_length_one
     have hle := canonicalBlockClaimCount_le_length n k
     omega
 
-/-- The sole locally insufficient successor class after abstract dyadic
-discharge.  Saturation is a predecessor condition; residue and endpoint claim
-remain separate data. -/
+/--
+Compatibility-only name for the former balanced-carry exception.
+
+This predicate is impossible by
+`not_canonicalLengthOneBalancedCarrySuccessor`; new theorems must use
+`CanonicalLengthOneTerminalOneSuccessor` instead.
+-/
 def CanonicalLengthOneBalancedCarrySuccessor
     (n : OddNat) (k : ℕ) : Prop :=
   CanonicalSaturatedBorderBlock n k ∧
@@ -2984,6 +3166,99 @@ theorem abstractSaturatedUnitEmbeddingLowerHalf_ne_demandEmbeddingUpperHalf
     abstractDyadicDemandEmbeddingUpperHalf] at hval
   omega
 
+/-! ## Unified local saturated-successor discharge
+
+These constructors package abstract dyadic budget embeddings only.  They do
+not identify the finite slots with orbit bits, do not allocate a global root,
+and do not permit summing certificates across time.
+-/
+
+/-- Complete local abstract-discharge alternatives for one saturated
+predecessor and its immediate successor. -/
+inductive CanonicalSaturatedSuccessorAbstractDischarge
+    (n : OddNat) (k : ℕ) : Prop
+  | negative
+      (successor_neg : endpointAccountingTerm n (k + 1) < 0)
+      (combined_nonpos :
+        endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0)
+  | zero
+      (successor_zero : endpointAccountingTerm n (k + 1) = 0)
+      (length_ge_two : 2 ≤ canonicalBlockLength n (k + 1))
+      (unitEmbedding : Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1))
+  | positive
+      (successor_pos : 0 < endpointAccountingTerm n (k + 1))
+      (successor_nonsaturated : ¬ CanonicalSaturatedBorderBlock n (k + 1))
+      (unitEmbedding : Fin 2 ↪ CanonicalAbstractDyadicBudgetCarrier n (k + 1))
+      (demandEmbedding : CanonicalAbstractDyadicDemandCarrier n (k + 1) ↪
+        CanonicalAbstractDyadicBudgetCarrier n (k + 1))
+      (images_disjoint : ∀ i j, unitEmbedding i ≠ demandEmbedding j)
+
+/-- Every saturated predecessor has a complete local abstract-discharge
+certificate at its immediate successor. -/
+theorem CanonicalSaturatedBorderBlock.successorAbstractDischarge
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    CanonicalSaturatedSuccessorAbstractDischarge n k := by
+  by_cases hneg : endpointAccountingTerm n (k + 1) < 0
+  · exact .negative hneg
+      (h.drift_add_successor_drift_nonpos_of_negative hneg)
+  by_cases hzero : endpointAccountingTerm n (k + 1) = 0
+  · have hL : 2 ≤ canonicalBlockLength n (k + 1) := by
+      by_contra hnot
+      have hLone : canonicalBlockLength n (k + 1) = 1 := by
+        have hLpos := one_le_canonicalBlockLength n (k + 1)
+        omega
+      have hclaim := h.next_claimCount_eq_zero_of_length_one hLone
+      have hv := one_le_canonicalBlockTerminalValuation n (k + 1)
+      have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
+        n (k + 1)
+      rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaim, hzero] at hdrift
+      omega
+    exact .zero hzero hL (abstractZeroSuccessorUnitEmbedding hzero hL)
+  · have hpos : 0 < endpointAccountingTerm n (k + 1) := by omega
+    have hnot := h.not_succ
+    exact .positive hpos hnot
+      (abstractSaturatedUnitEmbeddingLowerHalf hpos hnot)
+      (abstractDyadicDemandEmbeddingUpperHalf hpos hnot)
+      (abstractSaturatedUnitEmbeddingLowerHalf_ne_demandEmbeddingUpperHalf
+        hpos hnot)
+
+/-- Length-one successors repay at least the predecessor's scalar unit. -/
+theorem CanonicalSaturatedBorderBlock.lengthOne_next_scalar_repayment
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockClaimCount n (k + 1) = 0 ∧
+      endpointAccountingTerm n (k + 1) ≤ -1 ∧
+        endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ 0 := by
+  have hclaim := h.next_claimCount_eq_zero_of_length_one hL
+  have hv := one_le_canonicalBlockTerminalValuation n (k + 1)
+  have hdrift := endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount
+    n (k + 1)
+  rw [canonicalBlockCapacityCount_eq_terminalValuation, hclaim] at hdrift
+  rw [h.netDrift_eq_one]
+  omega
+
+/-- Residue eleven modulo sixteen gives exact scalar cancellation. -/
+theorem CanonicalSaturatedBorderBlock.lengthOne_next_drift_sum_eq_zero_of_mod16_eleven
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1)
+    (hres : canonicalBlockOddCore n k % 16 = 11) :
+    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) = 0 := by
+  have hv :=
+    (h.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres
+  have hterm : CanonicalLengthOneTerminalOneSuccessor n k := ⟨h, hL, hv⟩
+  exact hterm.predecessorDrift_add_successorDrift_eq_zero
+
+/-- Residue three modulo sixteen repays the predecessor with at least one
+additional scalar unit. -/
+theorem CanonicalSaturatedBorderBlock.lengthOne_next_drift_sum_le_neg_one_of_mod16_three
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1)
+    (hres : canonicalBlockOddCore n k % 16 = 3) :
+    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) ≤ -1 := by
+  have hnext := h.nextDrift_le_neg_two_of_length_one_mod16_three hL hres
+  rw [h.netDrift_eq_one]
+  omega
+
 /-!
 ## Actual upper-boundary audit
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md
new file mode 100644
index 00000000..927fec89
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-329.md
@@ -0,0 +1,98 @@
+# Petal / FloatWindow implementation report - checkpoint 329
+
+## Result
+
+The local saturated-successor program is closed at the abstract dyadic level.
+The block-core claim API, rigid successor profiles, unified local discharge,
+and a noncircular conditional global interface are now formalized.
+
+## Block-core API
+
+`canonicalBlockCoreWordAtDepth` packages
+
+```text
+2^d * 3^(L-d) * u - 1.
+```
+
+The source state equals this word at every valid depth, and claim membership
+is exactly own-width carry two at this word.  Adjacent depths satisfy
+
+```text
+3 * (word (d+1) + 1) = 2 * (word d + 1),
+source (d+1) + 1 = source d.
+```
+
+## Rigid successor collapse
+
+For a saturated predecessor:
+
+- every successor misses its deepest depth;
+- a zero-carrier balanced successor is forced to `L=2`, terminal valuation
+  one, claim count one, claims `{1}`, and holes `{2}`;
+- the full-balanced zero-carrier branch is impossible;
+- a tight valuation-one positive successor has holes `{L}` and claims
+  `Icc 1 (L-1)`.
+
+## Unified local discharge
+
+`CanonicalSaturatedSuccessorAbstractDischarge` has exactly three constructors:
+
+- negative successor drift with scalar cancellation;
+- zero successor drift with `L >= 2` and a `Fin 2` abstract embedding;
+- positive nonsaturated successor with disjoint saturated-unit and demand
+  embeddings.
+
+Every saturated predecessor has this certificate.  It is explicitly not an
+allocation of actual orbit bits or a globally reusable resource.
+
+Length-one successors now have the definitive repayment surface:
+
+- claim count zero;
+- successor drift at most `-1`;
+- predecessor plus successor drift at most zero;
+- residue `11 mod 16` gives exact cancellation;
+- residue `3 mod 16` gives total drift at most `-1`.
+
+## Claim-transition audit
+
+The adjacent recurrence does not imply monotone carries.  Lean verifies the
+exact recurrence witness `53, 35, 23`, whose own-width carries are `2, 1, 2`.
+Thus recurrence alone cannot provide the required uniform claim-hole density.
+
+## Noncircular global interface
+
+`UniversalPaymentAmortizedResource.lean` introduces a transition state with
+queue, potential, demand, consumption, replenishment, and one-step
+conservation.  Finite-prefix conservation is proved by induction.
+
+A uniform potential ceiling together with a cumulative replenishment ceiling
+implies a uniform queue bound, which then implies the existing endpoint-width
+bound.  A merely pointwise replenishment bound is correctly rejected because
+it permits linear cumulative growth.
+
+## Genuine obstruction
+
+No Collatz instance of `CanonicalNoncircularGlobalAmortizationLaw` is asserted.
+The missing theorem must assign negative drift or width decrease to resource
+transitions with temporal ownership and prove a cumulative replenishment
+ceiling.  Existing scalar facts allow the same event to be reused across
+blocks unless a multiplicity bound is added.
+
+Route 1 therefore stops at carry alternation.  Route 2 stops at uncontrolled
+temporal reuse.  Replacing either missing theorem by a uniform queue or width
+bound would only rename the target and is rejected as circular.
+
+## Verification
+
+All required gates passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The changed Lean files contain no `sorry` or local `maxHeartbeats` override.
````
`````
