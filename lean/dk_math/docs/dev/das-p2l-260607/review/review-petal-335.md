# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal

gch: 2238adca684ad3263b064f0204da6d425a6bff65

## Report

(28m50s)

checkpoint 335 を完了しました。

主な確定事項:

- canonical owned FIFO queue の global newest-tail normal form
- source age、recent-cardinality、deficit、maximum age の同値性
- 同一 cardinality の source assignment に対する FIFO の最適性
- 一様 age bound を仮定した明示的な consumption block witness
- top-two signature は全 `r ≥ 1` で正の projected two-cycleを持つ
- その任意の finite coarsening も同じ obstruction を持つ
- top-three signature も `r = 1` で `89 → 67`, `39 → 59`, `59 → 89` の正の three-cycleを持つ

したがって、top-two/top-three の有限観測だけでは global bounded potential を構成できないことが Lean で確定しました。
一方、正方向に残る核心は次です。

```lean
∃ H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
```

実装内容と事実境界は [report-petal-335.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-335.md) にまとめています。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 変更対象に新規 `sorry` なし

## Review

(5m2s)

## cp-335 実装レビュー

## 結論

**全面採用。確定された。**

commit `2238adca684ad3263b064f0204da6d425a6bff65` と添付 report/diff は一致している。

cp-335 は、canonical FIFO queue を次の水準まで完成させた。

$$
\text{再帰的 source queue} = \text{全 historical claims の newest upper tail}
$$

さらに source age について、

$$
\text{actual age}\le H
\iff
\text{recent-cardinality coverage}
\iff
\text{source-age deficit}\le0
\iff
\text{maximum retained age}\le H
$$

が Lean 上で同一の条件として固定された。

否定側でも、

- normalized top-two bits は全 $r\ge1$ で失敗
- その任意の finite coarsening も失敗
- normalized top-three bits も $r=1$ で失敗

まで確定した。

今回の実装に数学的な破綻は見つからなかった。

ただし、今後の表現では次の二点を守るべきじゃ。

> $\exists H$ という uniform source-age bound は、source-age route の残課題である。queue boundedness 全体と同値だとはまだ証明されていない。

> top-three obstruction は現在 $r=1$ の theorem である。任意の上位 prefix 長に一般化されたわけではない。

---

## 1. Cumulative consumption の完全 no-reuse

新しい cumulative carrier は、

```lean
canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m
```

として、block $0,\ldots,m-1$ で実際に消費された source identity の集合を保持する。

membership は正確に、

$$
i\in\operatorname{CumulativeConsumed}(m) \iff \exists k<m,\ i\in\operatorname{ConsumedAtBlock}(k)
$$

となる。

さらに、一度消費された source は、

- 後の outstanding queue
- 後の available carrier
- 後の consumed carrier

のいずれにも再登場しない。

異なる block の consumed carriers は pairwise disjoint であり、累積 carrier の cardinality は scalar actual consumption の総和と一致する。

これは cp-334 の no-reappearance を、完全な **no double spending** へ昇格させた theorem じゃ。

---

## 2. Historical claims の exact partition

block $m$ より前に発生した全 carry-two source は、

```lean
canonicalHistoricalClaimSourceCarrier n m
```

として、

$$
\{i\in[0,b_m)\mid\operatorname{CarryTwoDebtAt}(n,i)\}
$$

により定義された。

そして source identity の集合として、

$$
\operatorname{HistoricalClaims}_m = \operatorname{CumulativeConsumed}_m \sqcup \operatorname{OwnedOutstanding}_m
$$

が証明された。

cardinality でも、

$$
|\operatorname{HistoricalClaims}_m| = \operatorname{CumulativeConsumedCount}_m+Q_m
$$

となる。

これは scalar prefix balance の単なる数値版ではない。

> 過去に発生した各 source identity は、消費済みか現在 outstanding かのどちらか一方に必ず所属する。

という完全な ownership partition じゃ。

---

## 3. Global FIFO ordering

累積 consumed source $x$ と outstanding source $y$ について、

$$
x\le y
$$

が証明された。

つまり、消費された全 source は、現在残っている全 source より古いか同時刻である。

これにより recursive FIFO queue は、全履歴を見た global ordering を持つ。

局所的に最古 source を消しているだけではなく、その局所操作の累積結果が、

> 全 historical claims の古い部分が consumed、新しい部分が outstanding

という一つの global cut を形成する。

---

## 4. Newest upper-tail normal form

cp-335 の中心 theorem は、

```lean
canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical
```

じゃ。

$$
\operatorname{OwnedOutstanding}_m = \operatorname{eraseOldestN} \left(\operatorname{CumulativeConsumedCount}_m,\operatorname{HistoricalClaims}_m\right)
$$

が証明された。

これは極めて強い。

recursive queue の結果を毎回再計算しなくても、

1. block $m$ までの全 historical claims を集める。
2. 実際に消費された総数だけ古い source から削る。

だけで、現在の owned queue が完全に復元される。

ここで削除数は total service ではなく **actual consumed count** じゃ。

unused service は未来へ保存されないため、normal form に混入していない。この判断も正しい。

---

## 5. Cardinal coverage が actual age と同値になった

cp-333 時点では、

$$
Q_m\le|\operatorname{RecentClaims}(H,m)|
$$

は匿名 cardinality inequalityにすぎなかった。

cp-335 では newest-tail normal form と threshold theorem により、

$$
\operatorname{ActualSourceAgeBound}(H) \iff \operatorname{CardCoveredByRecentSources}(H)
$$

まで強化された。

これは cp-334 の一方向、

$$
\text{actual age}\Longrightarrow\text{card coverage}
$$

に対する逆向きじゃ。

FIFO queue は歴史上最も新しい $Q_m$ 個を残すため、recent carrier に $Q_m$ 個以上の claim が存在すれば、FIFO remainder 全体が recent carrier に含まれる。

したがって cardinal coverage は、FIFO realization に限れば、もはや弱い匿名条件ではない。

> actual age の exact scalar characterization

になった。

---

## 6. Source-age deficit

old source carrier は、

$$
\operatorname{OldClaims}(H,m) = \{i\in[0,b_m-H)\mid\operatorname{CarryTwoDebtAt}(n,i)\}
$$

じゃ。

source-age deficit は、

$$
D_H(m) = |\operatorname{OldClaims}(H,m)| - \operatorname{CumulativeConsumedCount}(m)
$$

として定義された。

そして exact signed identity、

$$
D_H(m) = Q_m-|\operatorname{RecentClaims}(H,m)|
$$

が証明された。

従って、

$$
\text{block }m\text{ で全 outstanding age}\le H \iff D_H(m)\le0
$$

である。

uniform version は、

$$
\operatorname{UniformSourceAge}(H) \iff \forall m,\ D_H(m)\le0
$$

じゃ。

これで残る positive theorem は、queue や matching の言葉を使わず、

> old source demand が cumulative actual consumption を上回らない

という一つの signed inequalityへ落ちた。

---

## 7. Maximum age

owned queue が非空なら、その最小 source time が最古 outstanding sourceになる。

$$
\operatorname{MaximumAge}(m) = b_m - \min(\operatorname{OwnedQueue}_m)
$$

空なら $0$ と定義された。

そして、

$$
\operatorname{UniformSourceAge}(H) \iff \forall m,\ \operatorname{MaximumAge}(m)\le H
$$

が証明された。

したがって source-age route は現在、次のどれで攻めても同じになる。

```text
owned source membership
recent source cardinality
signed source-age deficit
maximum age
```

これらは別々の conjecture ではない。

---

## 8. FIFO optimality

`CanonicalAdmissibleOwnedRemainder` は、historical claims の任意の部分集合で、scalar outstanding queue と同じ cardinalityを持つものじゃ。

その任意の admissible remainder $u$ に対して、

$$
\min(u)\le\min(\operatorname{FIFOQueue})
$$

が証明された。

つまり FIFO は最小 retained source を最大化し、従って最大 source age を最小化する。

report の境界説明も正確じゃ。

これは、

> 同一時点で同一 cardinalityを持つ source assignment

間の比較である。

任意の alternative recursive policy の全履歴を構成した theorem ではない。ただし全 admissible subset という、実際の recursive policy より広い集合に対する最適性なので、source-age の下界評価には十分強い。

---

## 9. Conditional eventual consumption

uniform age bound $H$ を仮定すると、claim source $i$ は、

$$
b_m>i+H
$$

となった時点では outstanding queue に残れない。

その結果、block $k$ で発生した source は、

$$
j<k+H+2
$$

を満たす消費 block $j$ を持つことが証明された。

これは actual source-to-consumption-block witnessじゃ。

### 一段強化できる

現在の $k+H+2$ は安全だが、一 block 分だけ粗い。

block length が常に一以上なので、

$$
b_{k+H+1}\ge b_{k+1}+H
$$

である。

source $i$ は $i<b_{k+1}$ だから、

$$
i+H<b_{k+H+1}
$$

が既に従う。

従って次へ強化できる。

$$
\exists j<k+H+1,\ i\in\operatorname{ConsumedAtBlock}(j)
$$

---

## 10. Source-age bound は「十分条件」である

report の、

```text
∃ H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
```

が source-age route の核心である、という表現は正しい。

ただし、これを Collatz positive route 全体の唯一の残課題と同一視してはならない。

一般の FIFO queue では、

- queue cardinality は常に $1$
- 同じ source が永遠に残る

という状態があり得る。

この場合 queue は一様有界だが source age は無界じゃ。

したがって一般には、

$$
\operatorname{UniformSourceAge}\Longrightarrow\operatorname{UniformQueueBound}
$$

だが、逆向きは成立しない。

canonical Collatz queue で追加構造により逆向きが得られる可能性は残るが、現在は未証明である。

よって正確な表現は、

> source-age route を完成させる残課題は $\exists H$ である。

じゃ。

---

## 11. Top-two obstruction の全 $r$ 一般化

symbolic source、

$$
A_r=7\cdot2^{r+2}-1
$$

$$
B_r=5\cdot2^{r+2}-1
$$

が構成された。

その successors、widths、lower residues、heights、upper carries、top-two words、growth flags が全て exact に証明された。

signature graph 上では、

$$
\sigma(T(A_r))=\sigma(B_r)
$$

$$
\sigma(T(B_r))=\sigma(A_r)
$$

となる。

edge weights は、

$$
w(A_r,T(A_r))=1
$$

$$
w(B_r,T(B_r))=0
$$

なので、total weight $+1$ の projected two-cycleじゃ。

従って任意の $r\ge1$ について、

```lean
FixedLowUpperBoundarySignature r
```

では全 accelerated odd transitions を覆う bounded-potential certificate は存在しない。

その任意の finite coarsening も同じ obstruction を受ける。

これは cp-334 の `55/39` を数値例から symbolic familyへ昇格させた明確な成果じゃ。

---

## 12. Top-three obstruction の射程

top-three signature では $r=1$ において、

$$
89\to67
$$

$$
39\to59
$$

$$
59\to89
$$

が使われる。

weights は、

$$
0,\ 0,\ 1
$$

じゃ。

さらに、

$$
\sigma(67)=\sigma(39)
$$

であるため、projected graph 上で total weight $+1$ の three-cycle が閉じる。

従って、

```lean
FixedLowUpperBoundaryThreeSignature 1
```

も bounded potential を持てない。

ここで確定したのは **top-three、$r=1$** じゃ。

まだ次は言えない。

```text
全 r における top-three の失敗
任意の top-k prefix の失敗
全有限 upper-boundary signature の失敗
```

report はこの境界を守っている。

---

## 13. 次に見える actual expired carrier

source-age deficit は現在 scalar `Int` じゃが、global FIFO normal formから実 carrierへ戻せる。

次を定義する。

```lean
canonicalExpiredOutstandingClaims n H m :=
  canonicalOwnedOutstandingClaimsBeforeBlock n m ∩
    canonicalOldSourceClaimCarrier n H m
```

これは age $H$ を超えて現在も残っている actual source identities じゃ。

期待される exact theorem は、

$$
|\operatorname{ExpiredOutstanding}(H,m)| = \operatorname{Int.toNat}(D_H(m))
$$

である。

従って、

$$
D_H(m)\le0 \iff \operatorname{ExpiredOutstanding}(H,m)=\varnothing
$$

となる。

これにより signed deficit の正部分が、再び actual source-bearing residual carrierになる。

---

## 14. Source-age deficit の一段 recurrence

次の horizon-crossing carrier を定義する。

$$
\operatorname{Crossing}_H(m) = \{ i\in[b_m-H,b_{m+1}-H) \mid \operatorname{CarryTwoDebtAt}(n,i) \}
$$

これは block $m\to m+1$ の進行によって、新たに age horizon の外側へ出た claim source の集合じゃ。

old carrier は、

$$
\operatorname{OldClaims}(H,m+1) = \operatorname{OldClaims}(H,m) \sqcup \operatorname{Crossing}_H(m)
$$

となる。

cumulative consumed count は、

$$
C_{m+1}=C_m+\operatorname{Consumed}(m)
$$

だから、

$$
D_H(m+1) = D_H(m) + |\operatorname{Crossing}_H(m)| - \operatorname{Consumed}(m)
$$

が得られる。

これが次 checkpoint の中心式じゃ。

uniform age theorem は、

> horizon を越える claim の流入と、actual consumption の signed balance が、全 prefix で正にならない

という問題になる。

### 重要な注意

ここで deficit を各段ごとに `Nat` の zero reflection へ変えてはならない。

負の deficit は、

> claim が old になる前に既に消費された credit

を表す。

この負 credit は将来の horizon crossing を相殺できるため、`Int` のまま保存する必要がある。

---

## 15. Challenge への現在地

現在の正確な chain は、

```text
actual carry-two sources
→ recursive FIFO ownership
→ global newest-tail normal form
→ source-age deficit recurrence
→ uniform nonpositive deficit for some H        [未証明]
→ uniform actual source age
→ uniform queue bound
→ uniform endpoint-width bound
→ finite-state eventual periodicity
→ nontrivial cycle elimination
→ accelerated convergence
→ raw Collatz challenge
```

negative finite-signature routeは、

```text
fixed low
→ self-loop obstruction

fixed low + top two
→ symbolic positive two-cycle obstruction for all r

fixed low + top three
→ positive three-cycle obstruction at r = 1
```

まで確定した。

cp-335 は、source-age problemを「表現上の不足」から、明確な signed-flow theoremへ押し出した checkpointじゃ。

---

## 判定まとめ

### Historical source partition

**完成。**

### Complete no-reuse

**完成。**

### Global newest-tail normal form

**完成。**

### Actual age / cardinality equivalence

**完成。**

### Source-age deficit equivalence

**完成。**

### Maximum-age characterization

**完成。**

### FIFO assignment optimality

**完成。block 時点ごとの最適性。**

### Conditional consumption witness

**完成。$H+1$ block boundへ強化可能。**

### Uniform $H$ の存在

**未証明。source-age route の本体。**

### Top-two enriched signature

**全 $r\ge1$ で否定。coarsening も否定。**

### Top-three enriched signature

**$r=1$ で否定。一般 prefix theorem ではない。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-335.

The cp-335 implementation is accepted.

It completed the global newest-tail normal form of the canonical owned FIFO
queue and converted uniform actual source age into an exact signed deficit
condition.

The next checkpoint must turn that static deficit condition into a local
block-by-block signed-flow recurrence.

Do not continue directly to top-four prefix experiments before the positive
source-age frontier has been exposed.

# Stage A — semantic regression: age is stronger than cardinal boundedness

In the Collatz-independent FIFO module, record an abstract regression showing:

    a finite queue may have uniformly bounded cardinality;
    one persistent source may nevertheless have unbounded age.

This prevents documentation from treating uniform source age as equivalent to
uniform queue boundedness without additional Collatz-specific hypotheses.

State precisely:

    uniform source age is a sufficient positive route;
    it is not a generic necessary condition for queue boundedness.

# Stage B — expired outstanding carrier

Define:

    canonicalExpiredOutstandingClaims n H m :=
      canonicalOwnedOutstandingClaimsBeforeBlock n m
        ∩ canonicalOldSourceClaimCarrier n H m.

Prove:

    every member is an actual outstanding carry-two source;

    membership is equivalent to
      outstanding membership and age > H;

    the carrier is empty
      <->
    every outstanding source at block m has age <= H.

Prove the exact cardinal theorem:

    card canonicalExpiredOutstandingClaims
      =
    Int.toNat (canonicalSourceAgeDeficit n H m).

Do not prove only an inequality.

# Stage C — horizon-crossing claim carrier

Define:

    canonicalSourceAgeHorizonCrossingClaims n H m :=
      carryTwoPositions n
        (Ico
          (canonicalBlockStartTime n m - H)
          (canonicalBlockStartTime n (m + 1) - H)).

Prove:

    oldCarrier H (m + 1)
      =
    oldCarrier H m union horizonCrossing H m;

    the union is disjoint;

    card oldCarrier H (m + 1)
      =
    card oldCarrier H m + card horizonCrossing H m.

Handle the early regime where block start is less than H using Nat subtraction,
without adding an unnecessary side condition.

# Stage D — exact source-age deficit recurrence

Define the signed frontier increment:

    canonicalSourceAgeFrontierIncrement n H m :=
      card (canonicalSourceAgeHorizonCrossingClaims n H m)
        - canonicalQueueConsumed n m

in Int.

Prove:

    canonicalSourceAgeDeficit n H 0 = 0;

    canonicalSourceAgeDeficit n H (m + 1)
      =
    canonicalSourceAgeDeficit n H m
      + canonicalSourceAgeFrontierIncrement n H m;

    canonicalSourceAgeDeficit n H m
      =
    sum k in range m,
      canonicalSourceAgeFrontierIncrement n H k.

Keep the deficit signed.  Do not truncate negative credit at each step.

# Stage E — exact prefix formulation of uniform age

Prove:

    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
      <->
    forall m,
      sum k in range m,
        canonicalSourceAgeFrontierIncrement n H k <= 0.

This is the challenge-facing positive surface for the next arithmetic attack.

Also expose the carrier form:

    uniform age H
      <->
    every expired-outstanding carrier is empty.

# Stage F — boundary regressions and monotonicity

Prove:

    canonicalSourceAgeDeficit n 0 m
      =
    canonicalOutstandingClaimQueueBeforeBlock n m;

    canonicalSourceAgeHorizonCrossingClaims n 0 m
      =
    canonicalBlockClaimSourceCarrier n m;

    if canonicalBlockStartTime n m <= H, then
      old source carrier is empty and deficit is nonpositive;

    H1 <= H2 ->
      canonicalSourceAgeDeficit n H2 m
        <= canonicalSourceAgeDeficit n H1 m.

Derive monotonicity of expired outstanding carriers or at least their
cardinalities in the horizon.

# Stage G — sharpen the conditional block-lag witness

Strengthen:

    exists_consumptionBlock_before_add_of_sourceAgeAtMost

from:

    j < k + H + 2

to:

    j < k + H + 1.

Use:

    source i < blockStart (k + 1);
    blockStart (k + 1) + H <= blockStart (k + H + 1).

Keep the old theorem as a coarse compatibility corollary if needed.

# Stage H — FIFO threshold dominance

Strengthen the one-minimum optimality theorem.

For every admissible same-cardinality remainder u and every cutoff t, prove:

    card (u.filter (fun i => t <= i))
      <=
    card
      ((canonicalOwnedOutstandingClaimsBeforeBlock n m).filter
        (fun i => t <= i)).

Equivalently, FIFO minimizes the number of retained sources below every cutoff.

Derive the existing minimum / maximum-age optimality as corollaries.

This is a static assignment theorem; do not claim a comparison of complete
recursive alternative policies.

# Stage I — source-age deficit is the exact over-age residual

Prove the two complementary cases:

    deficit > 0 ->
      cumulative consumed carrier is contained in the old carrier;

    deficit <= 0 ->
      old carrier is contained in the cumulative consumed carrier.

Use the global lower-tail / upper-tail ordering.

Then prove the expired-carrier cardinal formula from these cases if Stage B
cannot close directly.

# Stage J — conditional signed-transition surface

Define a canonical structural certificate wrapper for a fixed horizon H whose
actual edge weight is definitionally:

    canonicalSourceAgeFrontierIncrement n H m.

Prove only the conditional theorem:

    a structurally predefined finite potential certificate
    whose every prefix potential change is nonpositive
      ->
    uniform actual source age H
      ->
    uniform queue and endpoint-width bounds.

Do not allow the signature or potential to be defined from the source-age
deficit itself; that would reproduce the earlier circularity.

# Stage K — arithmetic audit of the frontier increment

Inspect the two components separately:

    horizon-crossing carry-two sources;
    actual canonical consumption.

For the already classified saturated-successor branches, determine whether the
frontier increment can be shown nonpositive pointwise or over a fixed short
window.

Record exact successful subclasses and exact obstruction witnesses.

Do not infer a global H from finite numerical samples.

# Stage L — negative-route boundary

Retain the established facts:

    top-two enrichment fails for every r >= 1;
    every finite coarsening of top-two fails;
    top-three fails at r = 1.

Do not state that arbitrary normalized top-k observations fail.

Pause top-four experimentation unless it directly supplies information needed
by the source-age frontier signature.

# Stopping rule

Stop at the first genuine obstruction among:

    expired-outstanding cardinality is not Int.toNat deficit;

    the old carrier does not split by the moving horizon interval;

    the signed deficit recurrence fails under Nat cutoff truncation;

    negative deficit credit cannot be preserved in the prefix formula;

    FIFO threshold dominance fails;

    the H + 1 block witness cannot be proved;

    every structural frontier signature remains circular;

    frontier crossing claims cannot be related to existing block grammar.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-336.md
```

cp-335 で、source-age の静止画は完成した。

次はその境界を一 block ずつ動かし、**古くなる claim と実際に消える claim の差分運動**として捉える段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 9a4ed104..4506f93a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -32,6 +32,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueueGlobal.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueueGlobal.lean
new file mode 100644
index 00000000..46707e42
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalOwnedQueueGlobal.lean
@@ -0,0 +1,570 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal"
+
+namespace DkMath.Collatz
+
+/-!
+# Global normal form of the canonical source-owned queue
+
+The local recursion preserves source identity block by block.  This module
+proves that the same queue is globally the newest upper tail of every
+historical carry-two source, after removing the cumulative *actual* consumed
+count.  Unused service is deliberately absent from this normal form.
+-/
+
+/-- Every carry-two claim source born before canonical block `m`. -/
+noncomputable def canonicalHistoricalClaimSourceCarrier
+    (n : OddNat) (m : ℕ) : Finset ℕ :=
+  carryTwoPositions n (Finset.Ico 0 (canonicalBlockStartTime n m))
+
+/-- Source identities consumed in the strict block prefix `[0,m)`. -/
+noncomputable def canonicalOwnedCumulativeConsumedClaimsBeforeBlock
+    (n : OddNat) : ℕ → Finset ℕ
+  | 0 => ∅
+  | m + 1 =>
+      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
+        canonicalOwnedConsumedClaimsAtBlock n m
+
+/-- Scalar actual consumption in the strict block prefix `[0,m)`. -/
+noncomputable def canonicalCumulativeConsumedCountBeforeBlock
+    (n : OddNat) (m : ℕ) : ℕ :=
+  ∑ k ∈ Finset.range m, canonicalQueueConsumed n k
+
+@[simp] theorem canonicalOwnedCumulativeConsumedClaimsBeforeBlock_zero
+    (n : OddNat) :
+    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n 0 = ∅ := rfl
+
+@[simp] theorem canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ
+    (n : OddNat) (m : ℕ) :
+    canonicalOwnedCumulativeConsumedClaimsBeforeBlock n (m + 1) =
+      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
+        canonicalOwnedConsumedClaimsAtBlock n m := rfl
+
+/-- Membership in the cumulative carrier retains the exact consuming block. -/
+theorem mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff
+    {n : OddNat} {m i : ℕ} :
+    i ∈ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ↔
+      ∃ k < m, i ∈ canonicalOwnedConsumedClaimsAtBlock n k := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      rw [canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ,
+        Finset.mem_union, ih]
+      constructor
+      · rintro (⟨k, hkm, hi⟩ | hi)
+        · exact ⟨k, by omega, hi⟩
+        · exact ⟨m, by omega, hi⟩
+      · rintro ⟨k, hkm, hi⟩
+        by_cases hkmEq : k = m
+        · exact Or.inr (hkmEq ▸ hi)
+        · exact Or.inl ⟨k, by omega, hi⟩
+
+/-- A consumed source is a member of the claims available at that block. -/
+theorem mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
+    {n : OddNat} {k i : ℕ}
+    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k) :
+    i ∈ canonicalOwnedAvailableClaimsAtBlock n k :=
+  (Finset.mem_sdiff.mp hi).1
+
+/-- A consumed identity cannot occur in any later available carrier. -/
+theorem not_mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
+    {n : OddNat} {k m i : ℕ}
+    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n k)
+    (hkm : k < m) :
+    i ∉ canonicalOwnedAvailableClaimsAtBlock n m := by
+  intro hiLater
+  rcases Finset.mem_union.mp hiLater with hiOld | hiNew
+  · exact not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
+      hi hkm hiOld
+  · have hiLt := mem_canonicalOwnedConsumedClaimsAtBlock_lt_next_start hi
+    have hstart := canonicalBlockStartTime_mono n
+      (show k + 1 ≤ m by omega)
+    have hiGe := (Finset.mem_Ico.mp
+      (mem_canonicalBlockClaimSourceCarrier_interval hiNew)).1
+    omega
+
+/-- Consumed carriers belonging to different blocks are disjoint. -/
+theorem disjoint_canonicalOwnedConsumedClaimsAtBlock
+    {n : OddNat} {j k : ℕ} (hjk : j ≠ k) :
+    Disjoint (canonicalOwnedConsumedClaimsAtBlock n j)
+      (canonicalOwnedConsumedClaimsAtBlock n k) := by
+  wlog hjkOrder : j < k generalizing j k
+  · exact (this (Ne.symm hjk) (by omega)).symm
+  apply Finset.disjoint_left.mpr
+  intro i hij hik
+  exact not_mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed
+    hij hjkOrder (mem_canonicalOwnedAvailableClaimsAtBlock_of_consumed hik)
+
+/-- A consumed source cannot be consumed again at a later block. -/
+theorem not_mem_canonicalOwnedConsumedClaimsAtBlock_of_consumed
+    {n : OddNat} {j k i : ℕ}
+    (hi : i ∈ canonicalOwnedConsumedClaimsAtBlock n j)
+    (hjk : j < k) :
+    i ∉ canonicalOwnedConsumedClaimsAtBlock n k := by
+  exact fun hik => (Finset.disjoint_left.mp
+    (disjoint_canonicalOwnedConsumedClaimsAtBlock (by omega))) hi hik
+
+/-- The previous cumulative consumed carrier is disjoint from the next block's
+consumed carrier. -/
+theorem disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_consumed
+    (n : OddNat) (m : ℕ) :
+    Disjoint (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
+      (canonicalOwnedConsumedClaimsAtBlock n m) := by
+  apply Finset.disjoint_left.mpr
+  intro i hiCum hiNow
+  rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp hiCum with
+    ⟨k, hkm, hiK⟩
+  exact not_mem_canonicalOwnedConsumedClaimsAtBlock_of_consumed hiK hkm hiNow
+
+/-- The cumulative source carrier realizes the cumulative scalar consumption. -/
+theorem card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock
+    (n : OddNat) (m : ℕ) :
+    (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m).card =
+      canonicalCumulativeConsumedCountBeforeBlock n m := by
+  induction m with
+  | zero => simp [canonicalCumulativeConsumedCountBeforeBlock]
+  | succ m ih =>
+      rw [canonicalOwnedCumulativeConsumedClaimsBeforeBlock_succ,
+        Finset.card_union_of_disjoint
+          (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_consumed n m),
+        ih, card_canonicalOwnedConsumedClaimsAtBlock]
+      change (∑ k ∈ Finset.range m, canonicalQueueConsumed n k) +
+          canonicalQueueConsumed n m =
+        ∑ k ∈ Finset.range (m + 1), canonicalQueueConsumed n k
+      rw [Finset.sum_range_succ]
+
+/-- Historical claims split when one complete canonical block is appended. -/
+theorem canonicalHistoricalClaimSourceCarrier_succ
+    (n : OddNat) (m : ℕ) :
+    canonicalHistoricalClaimSourceCarrier n (m + 1) =
+      canonicalHistoricalClaimSourceCarrier n m ∪
+        canonicalBlockClaimSourceCarrier n m := by
+  ext i
+  simp only [canonicalHistoricalClaimSourceCarrier,
+    canonicalBlockClaimSourceCarrier, mem_carryTwoPositions_iff,
+    Finset.mem_union, Finset.mem_Ico]
+  constructor
+  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
+    by_cases hiOld : i < canonicalBlockStartTime n m
+    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
+    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
+  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
+    · have hmono : canonicalBlockStartTime n m ≤
+          canonicalBlockStartTime n (m + 1) :=
+        canonicalBlockStartTime_mono n (by omega)
+      exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩
+
+/-- Exact source-identity partition of historical claims into consumed and
+currently outstanding claims. -/
+theorem canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding
+    (n : OddNat) (m : ℕ) :
+    canonicalHistoricalClaimSourceCarrier n m =
+      canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m ∪
+        canonicalOwnedOutstandingClaimsBeforeBlock n m := by
+  induction m with
+  | zero =>
+      simp [canonicalHistoricalClaimSourceCarrier, canonicalBlockStartTime,
+        canonicalEndpointBlockStart, carryTwoPositions]
+  | succ m ih =>
+      rw [canonicalHistoricalClaimSourceCarrier_succ, ih,
+        Finset.union_assoc,
+        ← canonicalOwnedAvailableClaimsAtBlock,
+        ← canonicalOwnedConsumed_union_nextOutstanding,
+        ← Finset.union_assoc]
+      rfl
+
+/-- Cumulative consumed and outstanding identities are disjoint. -/
+theorem disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding
+    (n : OddNat) (m : ℕ) :
+    Disjoint (canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m)
+      (canonicalOwnedOutstandingClaimsBeforeBlock n m) := by
+  apply Finset.disjoint_left.mpr
+  intro i hiCum hiOut
+  rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp hiCum with
+    ⟨k, hkm, hiConsumed⟩
+  exact not_mem_canonicalOwnedOutstandingClaimsBeforeBlock_of_consumed
+    hiConsumed hkm hiOut
+
+/-- Exact cardinal form of the historical source partition. -/
+theorem card_canonicalHistoricalClaimSourceCarrier
+    (n : OddNat) (m : ℕ) :
+    (canonicalHistoricalClaimSourceCarrier n m).card =
+      canonicalCumulativeConsumedCountBeforeBlock n m +
+        canonicalOutstandingClaimQueueBeforeBlock n m := by
+  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding,
+    Finset.card_union_of_disjoint
+      (disjoint_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_outstanding n m),
+    card_canonicalOwnedCumulativeConsumedClaimsBeforeBlock,
+    card_canonicalOwnedOutstandingClaimsBeforeBlock]
+
+/-- The carrier partition is the source-bearing form of the existing scalar
+prefix balance. -/
+theorem card_canonicalHistoricalClaimSourceCarrier_eq_sum_demand
+    (n : OddNat) (m : ℕ) :
+    (canonicalHistoricalClaimSourceCarrier n m).card =
+      ∑ k ∈ Finset.range m, canonicalQueueDemand n k := by
+  exact (sum_canonicalQueueDemand_range_eq_sourceClaims_card n m).symm
+
+/-- Every historical source lies before the observation block. -/
+theorem mem_canonicalHistoricalClaimSourceCarrier_lt_start
+    {n : OddNat} {m i : ℕ}
+    (hi : i ∈ canonicalHistoricalClaimSourceCarrier n m) :
+    i < canonicalBlockStartTime n m :=
+  (Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hi).1).2
+
+/-- Global FIFO ordering: every consumed historical source is no later than
+every source still outstanding. -/
+theorem canonicalOwnedCumulativeConsumed_le_outstanding
+    (n : OddNat) (m : ℕ) :
+    ∀ x ∈ canonicalOwnedCumulativeConsumedClaimsBeforeBlock n m,
+      ∀ y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m, x ≤ y := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      intro x hx y hy
+      rcases Finset.mem_union.mp hx with hxOld | hxNow
+      · have hyAvail := mem_of_mem_eraseOldestN hy
+        rcases Finset.mem_union.mp hyAvail with hyOld | hyNew
+        · exact ih x hxOld y hyOld
+        · have hxHist : x ∈ canonicalHistoricalClaimSourceCarrier n m := by
+            rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+            exact Finset.mem_union_left _ hxOld
+          have hxLt := mem_canonicalHistoricalClaimSourceCarrier_lt_start hxHist
+          have hyGe := (Finset.mem_Ico.mp
+            (mem_canonicalBlockClaimSourceCarrier_interval hyNew)).1
+          omega
+      · exact consumedOldestN_le_eraseOldestN
+          (canonicalQueueService n m)
+          (canonicalOwnedAvailableClaimsAtBlock n m) x hxNow y hy
+
+/-- The recursive owned queue is globally the newest upper tail of all
+historical source identities after cumulative *actual* consumption. -/
+theorem canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical
+    (n : OddNat) (m : ℕ) :
+    canonicalOwnedOutstandingClaimsBeforeBlock n m =
+      eraseOldestN (canonicalCumulativeConsumedCountBeforeBlock n m)
+        (canonicalHistoricalClaimSourceCarrier n m) := by
+  symm
+  apply eraseOldestN_eq_of_subset_card_and_complement_le
+  · intro i hi
+    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    exact Finset.mem_union_right _ hi
+  · rw [card_eraseOldestN,
+      card_canonicalOwnedOutstandingClaimsBeforeBlock,
+      card_canonicalHistoricalClaimSourceCarrier]
+    omega
+  · intro x hx y hy
+    have hxHist := (Finset.mem_sdiff.mp hx).1
+    have hxNot := (Finset.mem_sdiff.mp hx).2
+    rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding] at hxHist
+    rcases Finset.mem_union.mp hxHist with hxConsumed | hxOutstanding
+    · exact canonicalOwnedCumulativeConsumed_le_outstanding n m x hxConsumed y hy
+    · exact False.elim (hxNot hxOutstanding)
+
+/-! ## Exact age and cardinality normal forms -/
+
+/-- Recent claims are exactly the cutoff-filtered part of the historical
+carrier. -/
+theorem canonicalRecentSourceClaimCarrier_eq_historical_filter
+    (n : OddNat) (H m : ℕ) :
+    canonicalRecentSourceClaimCarrier n H m =
+      (canonicalHistoricalClaimSourceCarrier n m).filter
+        (fun i => canonicalBlockStartTime n m - H ≤ i) := by
+  ext i
+  simp only [canonicalRecentSourceClaimCarrier,
+    canonicalHistoricalClaimSourceCarrier, mem_carryTwoPositions_iff,
+    Finset.mem_Ico, Finset.mem_filter]
+  constructor
+  · rintro ⟨⟨hiLow, hiTop⟩, hiCarry⟩
+    exact ⟨⟨⟨by omega, hiTop⟩, hiCarry⟩, hiLow⟩
+  · rintro ⟨⟨⟨_, hiTop⟩, hiCarry⟩, hiLow⟩
+    exact ⟨⟨hiLow, hiTop⟩, hiCarry⟩
+
+/-- At one block, a FIFO age bound is equivalent to inclusion in the recent
+source carrier. -/
+theorem owned_sourceAgeAtMost_iff_subset_recentCarrier
+    (n : OddNat) (H m : ℕ) :
+    (∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
+        canonicalBlockStartTime n m - i ≤ H) ↔
+      canonicalOwnedOutstandingClaimsBeforeBlock n m ⊆
+        canonicalRecentSourceClaimCarrier n H m := by
+  constructor
+  · intro h i hi
+    rw [canonicalRecentSourceClaimCarrier, mem_carryTwoPositions_iff]
+    have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
+    have hiAge := h i hi
+    have hiCarry :=
+      carryTwoDebtAt_of_mem_canonicalOwnedOutstandingClaimsBeforeBlock hi
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega, hiTop⟩, hiCarry⟩
+  · intro h i hi
+    have hiRecent := mem_carryTwoPositions_iff.mp (h hi)
+    have hiLow := (Finset.mem_Ico.mp hiRecent.1).1
+    omega
+
+/-- For the actual FIFO queue, scalar recent-source cardinal coverage is
+equivalent to genuine uniform source age. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_cardCovered
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H := by
+  constructor
+  · exact
+      CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost.to_cardCovered
+  · intro h m
+    rw [owned_sourceAgeAtMost_iff_subset_recentCarrier]
+    rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
+      canonicalRecentSourceClaimCarrier_eq_historical_filter]
+    apply (eraseOldestN_subset_filter_iff_card_le _ _ _).2
+    rw [← canonicalRecentSourceClaimCarrier_eq_historical_filter,
+      ← canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
+      card_canonicalOwnedOutstandingClaimsBeforeBlock]
+    exact h m
+
+/-- Carry-two sources older than the horizon cutoff at block `m`. -/
+noncomputable def canonicalOldSourceClaimCarrier
+    (n : OddNat) (H m : ℕ) : Finset ℕ :=
+  carryTwoPositions n
+    (Finset.Ico 0 (canonicalBlockStartTime n m - H))
+
+/-- Old and recent carriers partition the complete historical carrier. -/
+theorem canonicalHistoricalClaimSourceCarrier_eq_old_union_recent
+    (n : OddNat) (H m : ℕ) :
+    canonicalHistoricalClaimSourceCarrier n m =
+      canonicalOldSourceClaimCarrier n H m ∪
+        canonicalRecentSourceClaimCarrier n H m := by
+  ext i
+  simp only [canonicalHistoricalClaimSourceCarrier,
+    canonicalOldSourceClaimCarrier, canonicalRecentSourceClaimCarrier,
+    mem_carryTwoPositions_iff, Finset.mem_Ico, Finset.mem_union]
+  constructor
+  · rintro ⟨⟨_, hiTop⟩, hiCarry⟩
+    by_cases hiOld : i < canonicalBlockStartTime n m - H
+    · exact Or.inl ⟨⟨by omega, hiOld⟩, hiCarry⟩
+    · exact Or.inr ⟨⟨by omega, hiTop⟩, hiCarry⟩
+  · rintro (⟨⟨_, hiTop⟩, hiCarry⟩ | ⟨⟨_, hiTop⟩, hiCarry⟩)
+    · exact ⟨⟨by omega, by omega⟩, hiCarry⟩
+    · exact ⟨⟨by omega, hiTop⟩, hiCarry⟩
+
+/-- The old and recent source intervals are disjoint. -/
+theorem disjoint_canonicalOldSourceClaimCarrier_recent
+    (n : OddNat) (H m : ℕ) :
+    Disjoint (canonicalOldSourceClaimCarrier n H m)
+      (canonicalRecentSourceClaimCarrier n H m) := by
+  apply Finset.disjoint_left.mpr
+  intro i hiOld hiRecent
+  have hOld := Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hiOld).1
+  have hRecent := Finset.mem_Ico.mp (mem_carryTwoPositions_iff.mp hiRecent).1
+  omega
+
+/-- Exact signed deficit identity comparing old source mass with cumulative
+consumption, and outstanding mass with recent sources. -/
+theorem canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent
+    (n : OddNat) (H m : ℕ) :
+    ((canonicalOldSourceClaimCarrier n H m).card : ℤ) -
+        canonicalCumulativeConsumedCountBeforeBlock n m =
+      canonicalOutstandingClaimQueueBeforeBlock n m -
+        (canonicalRecentSourceClaimCarrier n H m).card := by
+  have hOldRecent :
+      (canonicalHistoricalClaimSourceCarrier n m).card =
+        (canonicalOldSourceClaimCarrier n H m).card +
+          (canonicalRecentSourceClaimCarrier n H m).card := by
+    rw [canonicalHistoricalClaimSourceCarrier_eq_old_union_recent,
+      Finset.card_union_of_disjoint
+        (disjoint_canonicalOldSourceClaimCarrier_recent n H m)]
+  have hConsumed := card_canonicalHistoricalClaimSourceCarrier n m
+  have hEq :
+      ((canonicalOldSourceClaimCarrier n H m).card : ℤ) +
+          (canonicalRecentSourceClaimCarrier n H m).card =
+        canonicalCumulativeConsumedCountBeforeBlock n m +
+          canonicalOutstandingClaimQueueBeforeBlock n m := by
+    exact_mod_cast (show
+      (canonicalOldSourceClaimCarrier n H m).card +
+          (canonicalRecentSourceClaimCarrier n H m).card =
+        canonicalCumulativeConsumedCountBeforeBlock n m +
+          canonicalOutstandingClaimQueueBeforeBlock n m by omega)
+  omega
+
+/-- The signed source-age deficit at block `m`. -/
+noncomputable def canonicalSourceAgeDeficit
+    (n : OddNat) (H m : ℕ) : ℤ :=
+  ((canonicalOldSourceClaimCarrier n H m).card : ℤ) -
+    canonicalCumulativeConsumedCountBeforeBlock n m
+
+/-- At one block, actual FIFO age is bounded exactly when the old-source
+deficit is nonpositive. -/
+theorem owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos
+    (n : OddNat) (H m : ℕ) :
+    (∀ i, i ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m →
+        canonicalBlockStartTime n m - i ≤ H) ↔
+      canonicalSourceAgeDeficit n H m ≤ 0 := by
+  rw [owned_sourceAgeAtMost_iff_subset_recentCarrier]
+  constructor
+  · intro hsub
+    have hcard := Finset.card_le_card hsub
+    unfold canonicalSourceAgeDeficit
+    rw [canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent]
+    rw [card_canonicalOwnedOutstandingClaimsBeforeBlock] at hcard
+    omega
+  · intro hdef
+    rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
+      canonicalRecentSourceClaimCarrier_eq_historical_filter]
+    apply (eraseOldestN_subset_filter_iff_card_le _ _ _).2
+    rw [← canonicalRecentSourceClaimCarrier_eq_historical_filter,
+      ← canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical,
+      card_canonicalOwnedOutstandingClaimsBeforeBlock]
+    unfold canonicalSourceAgeDeficit at hdef
+    rw [canonicalOldSourceClaim_card_sub_cumulativeConsumed_eq_queue_sub_recent]
+      at hdef
+    omega
+
+/-- Uniform source age is exactly uniform nonpositivity of the scalar deficit. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_deficit_nonpos
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      ∀ m, canonicalSourceAgeDeficit n H m ≤ 0 := by
+  constructor
+  · intro h m
+    exact (owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos n H m).mp (h m)
+  · intro h m
+    exact (owned_sourceAgeAtMost_iff_sourceAgeDeficit_nonpos n H m).mpr (h m)
+
+/-! ## Oldest source, maximum age, and policy optimality -/
+
+/-- Oldest retained source, with explicit value zero for an empty queue. -/
+noncomputable def canonicalOldestOutstandingSource
+    (n : OddNat) (m : ℕ) : ℕ :=
+  if h : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty then
+    (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' h
+  else
+    0
+
+/-- Maximum retained source age, explicitly zero for an empty queue. -/
+noncomputable def canonicalOwnedMaximumSourceAge
+    (n : OddNat) (m : ℕ) : ℕ :=
+  if h : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty then
+    canonicalBlockStartTime n m -
+      (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' h
+  else
+    0
+
+@[simp] theorem canonicalOwnedMaximumSourceAge_eq_zero_of_empty
+    {n : OddNat} {m : ℕ}
+    (h : canonicalOwnedOutstandingClaimsBeforeBlock n m = ∅) :
+    canonicalOwnedMaximumSourceAge n m = 0 := by
+  simp [canonicalOwnedMaximumSourceAge, h]
+
+/-- The maximum-age scalar exactly characterizes uniform actual source age. -/
+theorem canonicalOwnedOutstandingClaimsHaveSourceAgeAtMost_iff_maximumAge_le
+    (n : OddNat) (H : ℕ) :
+    CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H ↔
+      ∀ m, canonicalOwnedMaximumSourceAge n m ≤ H := by
+  constructor
+  · intro h m
+    by_cases hne :
+        (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty
+    · rw [canonicalOwnedMaximumSourceAge, dif_pos hne]
+      exact h m _ (Finset.min'_mem _ hne)
+    · simp [canonicalOwnedMaximumSourceAge, hne]
+  · intro h m i hi
+    have hne : (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty :=
+      ⟨i, hi⟩
+    have hmax := h m
+    rw [canonicalOwnedMaximumSourceAge, dif_pos hne] at hmax
+    have hmin := Finset.min'_le
+      (canonicalOwnedOutstandingClaimsBeforeBlock n m) i hi
+    exact (Nat.sub_le_sub_left hmin _).trans hmax
+
+/-- Any source assignment realizing the same scalar queue at block `m`. -/
+def CanonicalAdmissibleOwnedRemainder
+    (n : OddNat) (m : ℕ) (u : Finset ℕ) : Prop :=
+  u ⊆ canonicalHistoricalClaimSourceCarrier n m ∧
+    u.card = canonicalOutstandingClaimQueueBeforeBlock n m
+
+/-- FIFO maximizes the oldest retained source among every assignment realizing
+the same scalar queue. -/
+theorem canonicalOldestOutstandingSource_maximal
+    {n : OddNat} {m : ℕ} {u : Finset ℕ}
+    (hu : CanonicalAdmissibleOwnedRemainder n m u)
+    (huNonempty : u.Nonempty)
+    (hfifoNonempty :
+      (canonicalOwnedOutstandingClaimsBeforeBlock n m).Nonempty) :
+    u.min' huNonempty ≤
+      (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' hfifoNonempty := by
+  let y := (canonicalOwnedOutstandingClaimsBeforeBlock n m).min' hfifoNonempty
+  have hy : y ∈ canonicalOwnedOutstandingClaimsBeforeBlock n m :=
+    Finset.min'_mem _ hfifoNonempty
+  change u.min' huNonempty ≤ y
+  rw [canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
+    at hy
+  have hcard : u.card =
+      (eraseOldestN (canonicalCumulativeConsumedCountBeforeBlock n m)
+        (canonicalHistoricalClaimSourceCarrier n m)).card := by
+    rw [hu.2, ← card_canonicalOwnedOutstandingClaimsBeforeBlock,
+      canonicalOwnedOutstandingClaimsBeforeBlock_eq_eraseOldestN_historical]
+  rcases exists_le_of_card_eq_card_eraseOldestN hu.1 hcard hy with
+    ⟨x, hxU, hxy⟩
+  exact (Finset.min'_le u x hxU).trans hxy
+
+/-! ## Eventual consumption under a uniform age hypothesis -/
+
+/-- Once the observation time exceeds `i + H`, an age-`H` source cannot remain
+outstanding. -/
+theorem not_mem_ownedQueue_of_sourceAgeAtMost_of_time_gt
+    {n : OddNat} {H m i : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
+    (htime : i + H < canonicalBlockStartTime n m) :
+    i ∉ canonicalOwnedOutstandingClaimsBeforeBlock n m := by
+  intro hi
+  have hage := h m i hi
+  have hiTop := mem_canonicalOwnedOutstandingClaimsBeforeBlock_lt_start hi
+  omega
+
+/-- Advancing `L` canonical blocks advances source time by at least `L`. -/
+theorem canonicalBlockStartTime_add_le_startTime_add
+    (n : OddNat) (k L : ℕ) :
+    canonicalBlockStartTime n k + L ≤
+      canonicalBlockStartTime n (k + L) := by
+  induction L with
+  | zero => simp
+  | succ L ih =>
+      rw [show k + (L + 1) = (k + L) + 1 by omega,
+        canonicalBlockStartTime_succ]
+      have hlen := one_le_canonicalBlockLength n (k + L)
+      omega
+
+/-- Every source born in block `k` is consumed by some block strictly before
+`k + H + 2`, assuming the uniform actual source-age bound `H`. -/
+theorem exists_consumptionBlock_before_add_of_sourceAgeAtMost
+    {n : OddNat} {H k i : ℕ}
+    (h : CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H)
+    (hi : i ∈ canonicalBlockClaimSourceCarrier n k) :
+    ∃ j < k + H + 2, i ∈ canonicalOwnedConsumedClaimsAtBlock n j := by
+  let m := k + H + 2
+  have hiInterval := Finset.mem_Ico.mp
+    (mem_canonicalBlockClaimSourceCarrier_interval hi)
+  have hiCarry := carryTwoDebtAt_of_mem_canonicalBlockClaimSourceCarrier hi
+  have hadvance := canonicalBlockStartTime_add_le_startTime_add n (k + 1) (H + 1)
+  have hmEq : (k + 1) + (H + 1) = m := by simp [m]; omega
+  rw [hmEq] at hadvance
+  have htime : i + H < canonicalBlockStartTime n m := by omega
+  have hiHist : i ∈ canonicalHistoricalClaimSourceCarrier n m := by
+    rw [canonicalHistoricalClaimSourceCarrier, mem_carryTwoPositions_iff]
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hiCarry⟩
+  have hiNot := not_mem_ownedQueue_of_sourceAgeAtMost_of_time_gt h htime
+  rw [canonicalHistoricalClaimSourceCarrier_eq_consumed_union_outstanding]
+    at hiHist
+  rcases Finset.mem_union.mp hiHist with hiConsumed | hiOutstanding
+  · rcases mem_canonicalOwnedCumulativeConsumedClaimsBeforeBlock_iff.mp
+      hiConsumed with ⟨j, hjm, hij⟩
+    exact ⟨j, by simpa [m] using hjm, hij⟩
+  · exact False.elim (hiNot hiOutstanding)
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 76d3b47f..6f7035d9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -94,6 +94,49 @@ theorem false_of_step_of_signature_eq_of_actualWeight_pos
   simp only [sub_self] at hprojected
   omega
 
+/-- Two realized edges forming a projected two-cycle with positive total
+concrete weight contradict every sound bounded-potential certificate.  The
+four concrete states need not form one concrete orbit cycle. -/
+theorem false_of_two_step_projected_cycle_of_actualWeight_add_pos
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    {a a' b b' : State}
+    (hstepA : C.Step a a')
+    (hstepB : C.Step b b')
+    (hcloseA : C.signature a' = C.signature b)
+    (hcloseB : C.signature b' = C.signature a)
+    (hpos : 0 < C.actualWeight a a' + C.actualWeight b b') : False := by
+  have hA := (C.actual_le_projected a a' hstepA).trans
+    (C.projected_le_potential_diff (C.signature a) (C.signature a'))
+  have hB := (C.actual_le_projected b b' hstepB).trans
+    (C.projected_le_potential_diff (C.signature b) (C.signature b'))
+  rw [hcloseA] at hA
+  rw [hcloseB] at hB
+  omega
+
+/-- Three realized edges forming a projected three-cycle with positive total
+concrete weight contradict every sound bounded-potential certificate. -/
+theorem false_of_three_step_projected_cycle_of_actualWeight_add_pos
+    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
+    {a a' b b' c c' : State}
+    (hstepA : C.Step a a')
+    (hstepB : C.Step b b')
+    (hstepC : C.Step c c')
+    (hcloseA : C.signature a' = C.signature b)
+    (hcloseB : C.signature b' = C.signature c)
+    (hcloseC : C.signature c' = C.signature a)
+    (hpos : 0 < C.actualWeight a a' + C.actualWeight b b' +
+      C.actualWeight c c') : False := by
+  have hA := (C.actual_le_projected a a' hstepA).trans
+    (C.projected_le_potential_diff (C.signature a) (C.signature a'))
+  have hB := (C.actual_le_projected b b' hstepB).trans
+    (C.projected_le_potential_diff (C.signature b) (C.signature b'))
+  have hC := (C.actual_le_projected c c' hstepC).trans
+    (C.projected_le_potential_diff (C.signature c) (C.signature c'))
+  rw [hcloseA] at hA
+  rw [hcloseB] at hB
+  rw [hcloseC] at hC
+  omega
+
 /-- Concrete signed weight along a finite sequence of related transitions. -/
 def pathWeight
     (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
index a28f41e4..b5fc7804 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OldestFirstQueue.lean
@@ -156,4 +156,107 @@ theorem exists_le_of_card_eq_card_eraseOldestN
       _ < (eraseOldestN c s).card := hlt
   exact (Nat.lt_irrefl _ this)
 
+/-! ## Upper-tail characterization -/
+
+/-- The oldest-first remainder lies above a cutoff exactly when its cardinality
+fits inside the part of the original carrier above that cutoff. -/
+theorem eraseOldestN_subset_filter_iff_card_le
+    (c : ℕ) (s : Finset ℕ) (t : ℕ) :
+    eraseOldestN c s ⊆ s.filter (fun x => t ≤ x) ↔
+      (eraseOldestN c s).card ≤ (s.filter (fun x => t ≤ x)).card := by
+  constructor
+  · exact Finset.card_le_card
+  · intro hcard y hy
+    have hyS : y ∈ s := mem_of_mem_eraseOldestN hy
+    apply Finset.mem_filter.mpr
+    refine ⟨hyS, ?_⟩
+    by_contra hty
+    have hyLt : y < t := by omega
+    have hUpperSub : s.filter (fun x => t ≤ x) ⊆ eraseOldestN c s := by
+      intro x hx
+      have hxS := (Finset.mem_filter.mp hx).1
+      have htx := (Finset.mem_filter.mp hx).2
+      have hxUnion : x ∈ consumedOldestN c s ∪ eraseOldestN c s := by
+        rw [consumedOldestN_union_eraseOldestN]
+        exact hxS
+      rcases Finset.mem_union.mp hxUnion with hxConsumed | hxRemaining
+      · have hxy := consumedOldestN_le_eraseOldestN c s x hxConsumed y hy
+        omega
+      · exact hxRemaining
+    have hEq : s.filter (fun x => t ≤ x) = eraseOldestN c s :=
+      Finset.eq_of_subset_of_card_le hUpperSub hcard
+    have hyUpper : y ∈ s.filter (fun x => t ≤ x) := by
+      rw [hEq]
+      exact hy
+    exact hty (Finset.mem_filter.mp hyUpper).2
+
+/-- A same-cardinality subset is the oldest-first remainder whenever every
+discarded source is no later than every retained source.  This is the generic
+uniqueness theorem for the newest upper tail. -/
+theorem eraseOldestN_eq_of_subset_card_and_complement_le
+    {c : ℕ} {s u : Finset ℕ}
+    (hu : u ⊆ s)
+    (hcard : u.card = (eraseOldestN c s).card)
+    (horder : ∀ x ∈ s \ u, ∀ y ∈ u, x ≤ y) :
+    eraseOldestN c s = u := by
+  apply Finset.Subset.antisymm
+  · intro y hy
+    by_contra hyu
+    have hyS : y ∈ s := mem_of_mem_eraseOldestN hy
+    have hyComp : y ∈ s \ u := Finset.mem_sdiff.mpr ⟨hyS, hyu⟩
+    have hnotSub : ¬u ⊆ eraseOldestN c s := by
+      intro hsub
+      have hEq : u = eraseOldestN c s :=
+        Finset.eq_of_subset_of_card_le hsub (by omega)
+      exact hyu (by simpa [hEq] using hy)
+    have hex : ∃ z, z ∈ u ∧ z ∉ eraseOldestN c s := by
+      by_contra h
+      apply hnotSub
+      intro z hzU
+      by_contra hzNot
+      exact h ⟨z, hzU, hzNot⟩
+    rcases hex with ⟨z, hzU, hzNot⟩
+    have hzS : z ∈ s := hu hzU
+    have hzUnion : z ∈ consumedOldestN c s ∪ eraseOldestN c s := by
+      rw [consumedOldestN_union_eraseOldestN]
+      exact hzS
+    have hzConsumed : z ∈ consumedOldestN c s := by
+      rcases Finset.mem_union.mp hzUnion with hz | hz
+      · exact hz
+      · exact False.elim (hzNot hz)
+    have hzy := consumedOldestN_le_eraseOldestN c s z hzConsumed y hy
+    have hyz := horder y hyComp z hzU
+    have : y = z := Nat.le_antisymm hyz hzy
+    subst z
+    exact hzNot hy
+  · intro y hy
+    by_contra hyr
+    have hyS : y ∈ s := hu hy
+    have hyUnion : y ∈ consumedOldestN c s ∪ eraseOldestN c s := by
+      rw [consumedOldestN_union_eraseOldestN]
+      exact hyS
+    have hyConsumed : y ∈ consumedOldestN c s := by
+      rcases Finset.mem_union.mp hyUnion with hy' | hy'
+      · exact hy'
+      · exact False.elim (hyr hy')
+    have hnotSub : ¬eraseOldestN c s ⊆ u := by
+      intro hsub
+      have hEq : eraseOldestN c s = u :=
+        Finset.eq_of_subset_of_card_le hsub (by omega)
+      exact hyr (by simpa [hEq] using hy)
+    have hex : ∃ z, z ∈ eraseOldestN c s ∧ z ∉ u := by
+      by_contra h
+      apply hnotSub
+      intro z hzR
+      by_contra hzNot
+      exact h ⟨z, hzR, hzNot⟩
+    rcases hex with ⟨z, hzR, hzNot⟩
+    have hzS : z ∈ s := mem_of_mem_eraseOldestN hzR
+    have hzComp : z ∈ s \ u := Finset.mem_sdiff.mpr ⟨hzS, hzNot⟩
+    have hyz := consumedOldestN_le_eraseOldestN c s y hyConsumed z hzR
+    have hzy := horder z hzComp y hy
+    have : y = z := Nat.le_antisymm hyz hzy
+    subst z
+    exact hzNot hy
+
 end DkMath
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
index 56d372a2..e9499d61 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/RawLowSignatureObstruction.lean
@@ -412,14 +412,6 @@ theorem fixedLowUpperBoundarySignature_T_rawAllOnesWitness_ne
     normalizedTopTwoBits_rawAllOnesWitness_eq_three hr] at htop
   norm_num at htop
 
-/-! ## Enriched projected-cycle audit
-
-The old all-ones self-loop is gone, but the realized signature-pair graph still
-has a positive cycle.  Its two edges come from different concrete states,
-which is sufficient: projected potential inequalities are attached to
-signature pairs and therefore telescope around the projected cycle.
--/
-
 /-- An odd state congruent to three modulo four has exact height one. -/
 theorem s_eq_one_of_mod_four_eq_three
     {x : OddNat} (hmod : x.1 % 4 = 3) :
@@ -434,6 +426,396 @@ theorem s_eq_one_of_mod_four_eq_three
     omega
   omega
 
+/-! ## Symbolic top-two projected cycle -/
+
+/-- A positive coefficient times at least four, minus one, is `3 mod 4`. -/
+private theorem coeff_mul_pow_sub_one_mod_four_eq_three
+    {c e : ℕ} (hc : 0 < c) (he : 2 ≤ e) :
+    (c * 2 ^ e - 1) % 4 = 3 := by
+  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le he
+  rw [show 2 + q = q + 2 by omega, pow_add]
+  have hp : 0 < c * 2 ^ q := Nat.mul_pos hc (pow_pos (by norm_num) _)
+  have hmul : c * (2 ^ q * 4) = (c * 2 ^ q) * 4 := by ac_rfl
+  have hval : c * (2 ^ q * 2 ^ 2) - 1 =
+      (c * 2 ^ q - 1) * 4 + (4 - 1) := by
+    norm_num
+    rw [hmul]
+    omega
+  rw [hval]
+  exact mul_add_pred_mod_self (by norm_num)
+
+/-- Uniform width computation for the symbolic cycle coefficients. -/
+private theorem bitWidth_coeff_mul_pow_sub_one
+    {c r d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d)
+    (hloCoeff : 2 ^ (d - 1) < c) (hhiCoeff : c ≤ 2 ^ d) :
+    bitWidth (c * 2 ^ r - 1) = r + d := by
+  have hp : 2 ≤ 2 ^ r := by
+    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
+    rw [show 1 + q = q + 1 by omega, pow_succ]
+    have hq := pow_pos (by norm_num : 0 < (2 : ℕ)) q
+    omega
+  have hcPos : 0 < c := by
+    have hpowPos : 0 < 2 ^ (d - 1) := pow_pos (by norm_num) _
+    omega
+  have hscaled :
+      (2 ^ (d - 1) + 1) * 2 ^ r ≤ c * 2 ^ r := by
+    have hcoeff : 2 ^ (d - 1) + 1 ≤ c := by omega
+    exact Nat.mul_le_mul_right (2 ^ r) hcoeff
+  have hmulLow : 2 ^ (d - 1) * 2 ^ r + 2 ≤ c * 2 ^ r := by
+    rw [Nat.add_mul] at hscaled
+    omega
+  have hmulHigh : c * 2 ^ r ≤ 2 ^ d * 2 ^ r :=
+    Nat.mul_le_mul_right (2 ^ r) hhiCoeff
+  have hprodPos : 0 < c * 2 ^ r :=
+    Nat.mul_pos hcPos (pow_pos (by norm_num) _)
+  have hsub : c * 2 ^ r - 1 + 1 = c * 2 ^ r :=
+    Nat.sub_add_cancel hprodPos
+  have hlo : 2 ^ (r + d - 1) ≤ c * 2 ^ r - 1 := by
+    rw [show r + d - 1 = r + (d - 1) by omega, pow_add]
+    rw [Nat.mul_comm]
+    omega
+  have hhi : c * 2 ^ r - 1 < 2 ^ ((r + d - 1) + 1) := by
+    have hsubLt : c * 2 ^ r - 1 < c * 2 ^ r := by omega
+    have hscaledLt : c * 2 ^ r - 1 < 2 ^ d * 2 ^ r :=
+      lt_of_lt_of_le hsubLt hmulHigh
+    rw [show (r + d - 1) + 1 = r + d by omega, pow_add]
+    simpa [Nat.mul_comm] using hscaledLt
+  have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- First source of the symbolic top-two projected cycle. -/
+noncomputable def upperCycleA (r : ℕ) : OddNat := by
+  refine ⟨7 * 2 ^ (r + 2) - 1, ?_⟩
+  have hmod := coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 7) (e := r + 2) (by norm_num) (by omega)
+  omega
+
+/-- Second source of the symbolic top-two projected cycle. -/
+noncomputable def upperCycleB (r : ℕ) : OddNat := by
+  refine ⟨5 * 2 ^ (r + 2) - 1, ?_⟩
+  have hmod := coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 5) (e := r + 2) (by norm_num) (by omega)
+  omega
+
+@[simp] theorem upperCycleA_val (r : ℕ) :
+    (upperCycleA r).1 = 7 * 2 ^ (r + 2) - 1 := rfl
+
+@[simp] theorem upperCycleB_val (r : ℕ) :
+    (upperCycleB r).1 = 5 * 2 ^ (r + 2) - 1 := rfl
+
+/-- Both symbolic source states have exact height one. -/
+theorem s_upperCycleA_eq_one (r : ℕ) : s (upperCycleA r) = 1 := by
+  apply s_eq_one_of_mod_four_eq_three
+  exact coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 7) (e := r + 2) (by norm_num) (by omega)
+
+theorem s_upperCycleB_eq_one (r : ℕ) : s (upperCycleB r) = 1 := by
+  apply s_eq_one_of_mod_four_eq_three
+  exact coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 5) (e := r + 2) (by norm_num) (by omega)
+
+/-- Exact first successor of symbolic source `A`. -/
+theorem T_upperCycleA_val (r : ℕ) :
+    (T (upperCycleA r)).1 = 21 * 2 ^ (r + 1) - 1 := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_upperCycleA_eq_one r), upperCycleA_val]
+  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+  have hp := pow_pos (by norm_num : 0 < (2 : ℕ)) (r + 1)
+  omega
+
+/-- Exact first successor of symbolic source `B`. -/
+theorem T_upperCycleB_val (r : ℕ) :
+    (T (upperCycleB r)).1 = 15 * 2 ^ (r + 1) - 1 := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_upperCycleB_eq_one r), upperCycleB_val]
+  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+  have hp := pow_pos (by norm_num : 0 < (2 : ℕ)) (r + 1)
+  omega
+
+/-- Both first successors remain on the exact height-one channel. -/
+theorem s_T_upperCycleA_eq_one
+    {r : ℕ} (hr : 1 ≤ r) : s (T (upperCycleA r)) = 1 := by
+  apply s_eq_one_of_mod_four_eq_three
+  rw [T_upperCycleA_val]
+  exact coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 21) (e := r + 1) (by norm_num) (by omega)
+
+theorem s_T_upperCycleB_eq_one
+    {r : ℕ} (hr : 1 ≤ r) : s (T (upperCycleB r)) = 1 := by
+  apply s_eq_one_of_mod_four_eq_three
+  rw [T_upperCycleB_val]
+  exact coeff_mul_pow_sub_one_mod_four_eq_three
+    (c := 15) (e := r + 1) (by norm_num) (by omega)
+
+/-- Exact second successor of symbolic source `A`. -/
+theorem T_T_upperCycleA_val
+    {r : ℕ} (hr : 1 ≤ r) :
+    (T (T (upperCycleA r))).1 = 63 * 2 ^ r - 1 := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_T_upperCycleA_eq_one hr), T_upperCycleA_val, pow_succ]
+  have hp := pow_pos (by norm_num : 0 < (2 : ℕ)) r
+  omega
+
+/-- Exact second successor of symbolic source `B`. -/
+theorem T_T_upperCycleB_val
+    {r : ℕ} (hr : 1 ≤ r) :
+    (T (T (upperCycleB r))).1 = 45 * 2 ^ r - 1 := by
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
+    (s_T_upperCycleB_eq_one hr), T_upperCycleB_val, pow_succ]
+  have hp := pow_pos (by norm_num : 0 < (2 : ℕ)) r
+  omega
+
+/-- Exact widths of all six states in the symbolic projected cycle. -/
+theorem bitWidth_upperCycleA
+    {r : ℕ} (hr : 1 ≤ r) : bitWidth (upperCycleA r).1 = r + 5 := by
+  rw [upperCycleA_val, show r + 2 = r + 2 by rfl, pow_add]
+  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
+    (bitWidth_coeff_mul_pow_sub_one (c := 28) (d := 5) hr (by norm_num)
+      (by norm_num) (by norm_num))
+
+theorem bitWidth_upperCycleB
+    {r : ℕ} (hr : 1 ≤ r) : bitWidth (upperCycleB r).1 = r + 5 := by
+  rw [upperCycleB_val, show r + 2 = r + 2 by rfl, pow_add]
+  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
+    (bitWidth_coeff_mul_pow_sub_one (c := 20) (d := 5) hr (by norm_num)
+      (by norm_num) (by norm_num))
+
+theorem bitWidth_T_upperCycleA
+    {r : ℕ} (hr : 1 ≤ r) : bitWidth (T (upperCycleA r)).1 = r + 6 := by
+  rw [T_upperCycleA_val, pow_succ]
+  have hnormal : 21 * (2 ^ r * 2) = 42 * 2 ^ r := by ring
+  rw [hnormal]
+  exact
+    (bitWidth_coeff_mul_pow_sub_one (c := 42) (d := 6) hr (by norm_num)
+      (by norm_num) (by norm_num))
+
+theorem bitWidth_T_upperCycleB
+    {r : ℕ} (hr : 1 ≤ r) : bitWidth (T (upperCycleB r)).1 = r + 5 := by
+  rw [T_upperCycleB_val, pow_succ]
+  have hnormal : 15 * (2 ^ r * 2) = 30 * 2 ^ r := by ring
+  rw [hnormal]
+  exact
+    (bitWidth_coeff_mul_pow_sub_one (c := 30) (d := 5) hr (by norm_num)
+      (by norm_num) (by norm_num))
+
+theorem bitWidth_T_T_upperCycleA
+    {r : ℕ} (hr : 1 ≤ r) :
+    bitWidth (T (T (upperCycleA r))).1 = r + 6 := by
+  rw [T_T_upperCycleA_val hr]
+  exact bitWidth_coeff_mul_pow_sub_one (c := 63) (d := 6) hr (by norm_num)
+    (by norm_num) (by norm_num)
+
+theorem bitWidth_T_T_upperCycleB
+    {r : ℕ} (hr : 1 ≤ r) :
+    bitWidth (T (T (upperCycleB r))).1 = r + 6 := by
+  rw [T_T_upperCycleB_val hr]
+  exact bitWidth_coeff_mul_pow_sub_one (c := 45) (d := 6) hr (by norm_num)
+    (by norm_num) (by norm_num)
+
+/-- Every symbolic cycle value of the form `c * 2^r - 1` has the same
+all-ones lower `r`-window. -/
+private theorem coeff_mul_pow_sub_one_mod_pow
+    {c r : ℕ} (hc : 0 < c) :
+    (c * 2 ^ r - 1) % 2 ^ r = 2 ^ r - 1 := by
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have hval : c * 2 ^ r - 1 =
+      (c - 1) * 2 ^ r + (2 ^ r - 1) := by
+    have hprod : 0 < c * 2 ^ r := Nat.mul_pos hc hp
+    have hl : c * 2 ^ r - 1 + 1 = c * 2 ^ r :=
+      Nat.sub_add_cancel hprod
+    have hrhs : (c - 1) * 2 ^ r + (2 ^ r - 1) + 1 = c * 2 ^ r := by
+      rw [Nat.add_assoc, Nat.sub_add_cancel hp]
+      calc
+        (c - 1) * 2 ^ r + 2 ^ r = ((c - 1) + 1) * 2 ^ r := by
+          rw [Nat.add_mul]
+          simp
+        _ = c * 2 ^ r := by rw [Nat.sub_add_cancel hc]
+    omega
+  rw [hval]
+  exact mul_add_pred_mod_self hp
+
+/-- Upper carries along the symbolic two-cycle are `2,1,1,2`. -/
+theorem stateUpperCarry_upperCycleA_eq_two
+    {r : ℕ} (hr : 1 ≤ r) : stateUpperCarry (upperCycleA r).1 = 2 := by
+  have h := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (upperCycleA r)
+  rw [s_upperCycleA_eq_one, bitWidth_upperCycleA hr,
+    bitWidth_T_upperCycleA hr] at h
+  omega
+
+theorem stateUpperCarry_upperCycleB_eq_one
+    {r : ℕ} (hr : 1 ≤ r) : stateUpperCarry (upperCycleB r).1 = 1 := by
+  have h := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (upperCycleB r)
+  rw [s_upperCycleB_eq_one, bitWidth_upperCycleB hr,
+    bitWidth_T_upperCycleB hr] at h
+  omega
+
+theorem stateUpperCarry_T_upperCycleA_eq_one
+    {r : ℕ} (hr : 1 ≤ r) :
+    stateUpperCarry (T (upperCycleA r)).1 = 1 := by
+  have h := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (T (upperCycleA r))
+  rw [s_T_upperCycleA_eq_one hr, bitWidth_T_upperCycleA hr,
+    bitWidth_T_T_upperCycleA hr] at h
+  omega
+
+theorem stateUpperCarry_T_upperCycleB_eq_two
+    {r : ℕ} (hr : 1 ≤ r) :
+    stateUpperCarry (T (upperCycleB r)).1 = 2 := by
+  have h := bitWidth_T_add_height_eq_bitWidth_add_upperCarry (T (upperCycleB r))
+  rw [s_T_upperCycleB_eq_one hr, bitWidth_T_upperCycleB hr,
+    bitWidth_T_T_upperCycleB hr] at h
+  omega
+
+/-- The normalized top-two words along the symbolic cycle are `3,2,2,3`. -/
+theorem normalizedTopTwoBits_upperCycleA_eq_three
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (upperCycleA r).1 = 3 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_upperCycleA hr, show r + 5 - 2 = r + 3 by omega]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have h2 : 2 ^ (r + 2) = 4 * 2 ^ r := by rw [pow_add]; ring
+  have h3 : 2 ^ (r + 3) = 8 * 2 ^ r := by rw [pow_add]; ring
+  apply Nat.div_eq_of_lt_le
+  · rw [upperCycleA_val, h2, h3]
+    omega
+  · rw [upperCycleA_val, h2, h3]
+    omega
+
+theorem normalizedTopTwoBits_upperCycleB_eq_two
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (upperCycleB r).1 = 2 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_upperCycleB hr, show r + 5 - 2 = r + 3 by omega]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have h2 : 2 ^ (r + 2) = 4 * 2 ^ r := by rw [pow_add]; ring
+  have h3 : 2 ^ (r + 3) = 8 * 2 ^ r := by rw [pow_add]; ring
+  apply Nat.div_eq_of_lt_le
+  · rw [upperCycleB_val, h2, h3]
+    omega
+  · rw [upperCycleB_val, h2, h3]
+    omega
+
+theorem normalizedTopTwoBits_T_upperCycleA_eq_two
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (T (upperCycleA r)).1 = 2 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_T_upperCycleA hr, show r + 6 - 2 = r + 4 by omega]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have h1 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_add]; ring
+  have h4 : 2 ^ (r + 4) = 16 * 2 ^ r := by rw [pow_add]; ring
+  apply Nat.div_eq_of_lt_le
+  · rw [T_upperCycleA_val, h1, h4]
+    omega
+  · rw [T_upperCycleA_val, h1, h4]
+    omega
+
+theorem normalizedTopTwoBits_T_upperCycleB_eq_three
+    {r : ℕ} (hr : 1 ≤ r) :
+    normalizedTopTwoBits (T (upperCycleB r)).1 = 3 := by
+  unfold normalizedTopTwoBits upperPrefix
+  rw [bitWidth_T_upperCycleB hr, show r + 5 - 2 = r + 3 by omega]
+  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
+  have h1 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_add]; ring
+  have h3 : 2 ^ (r + 3) = 8 * 2 ^ r := by rw [pow_add]; ring
+  apply Nat.div_eq_of_lt_le
+  · rw [T_upperCycleB_val, h1, h3]
+    omega
+  · rw [T_upperCycleB_val, h1, h3]
+    omega
+
+/-- The symbolic edge weights are `+1` and `0`, hence have positive sum. -/
+theorem rawSignedWidthWeight_upperCycleA_eq_one
+    {r : ℕ} (hr : 1 ≤ r) :
+    rawSignedWidthWeight (upperCycleA r) (T (upperCycleA r)) = 1 := by
+  unfold rawSignedWidthWeight
+  rw [bitWidth_upperCycleA hr, bitWidth_T_upperCycleA hr]
+  omega
+
+theorem rawSignedWidthWeight_upperCycleB_eq_zero
+    {r : ℕ} (hr : 1 ≤ r) :
+    rawSignedWidthWeight (upperCycleB r) (T (upperCycleB r)) = 0 := by
+  unfold rawSignedWidthWeight
+  rw [bitWidth_upperCycleB hr, bitWidth_T_upperCycleB hr]
+  norm_num
+
+/-- The first symbolic edge lands in the enriched signature of `B`. -/
+theorem fixedLowUpperBoundarySignature_T_upperCycleA_eq_upperCycleB
+    {r : ℕ} (hr : 1 ≤ r) :
+    fixedLowUpperBoundarySignature r (T (upperCycleA r)) =
+      fixedLowUpperBoundarySignature r (upperCycleB r) := by
+  unfold fixedLowUpperBoundarySignature
+  congr 1
+  · unfold fixedLowRawSignature
+    congr 1
+    · apply Fin.ext
+      change (T (upperCycleA r)).1 % 2 ^ r = (upperCycleB r).1 % 2 ^ r
+      rw [T_upperCycleA_val, upperCycleB_val, pow_succ, pow_add]
+      norm_num
+      rw [show 21 * (2 ^ r * 2) = 42 * 2 ^ r by ring,
+        show 5 * (2 ^ r * 4) = 20 * 2 ^ r by ring,
+        coeff_mul_pow_sub_one_mod_pow (c := 42) (by norm_num),
+        coeff_mul_pow_sub_one_mod_pow (c := 20) (by norm_num)]
+    · apply Fin.ext
+      change stateUpperCarry (T (upperCycleA r)).1 =
+        stateUpperCarry (upperCycleB r).1
+      rw [stateUpperCarry_T_upperCycleA_eq_one hr,
+        stateUpperCarry_upperCycleB_eq_one hr]
+    · simp [s_T_upperCycleA_eq_one hr, s_upperCycleB_eq_one]
+    · change decide (bitWidth (T (T (upperCycleA r))).1 =
+          bitWidth (T (upperCycleA r)).1 + 1) =
+        decide (bitWidth (T (upperCycleB r)).1 =
+          bitWidth (upperCycleB r).1 + 1)
+      rw [bitWidth_T_upperCycleA hr, bitWidth_T_T_upperCycleA hr,
+        bitWidth_upperCycleB hr, bitWidth_T_upperCycleB hr]
+      norm_num
+  · apply Fin.ext
+    change normalizedTopTwoBits (T (upperCycleA r)).1 % 4 =
+      normalizedTopTwoBits (upperCycleB r).1 % 4
+    rw [normalizedTopTwoBits_T_upperCycleA_eq_two hr,
+      normalizedTopTwoBits_upperCycleB_eq_two hr]
+
+/-- The second symbolic edge closes the enriched signature cycle at `A`. -/
+theorem fixedLowUpperBoundarySignature_T_upperCycleB_eq_upperCycleA
+    {r : ℕ} (hr : 1 ≤ r) :
+    fixedLowUpperBoundarySignature r (T (upperCycleB r)) =
+      fixedLowUpperBoundarySignature r (upperCycleA r) := by
+  unfold fixedLowUpperBoundarySignature
+  congr 1
+  · unfold fixedLowRawSignature
+    congr 1
+    · apply Fin.ext
+      change (T (upperCycleB r)).1 % 2 ^ r = (upperCycleA r).1 % 2 ^ r
+      rw [T_upperCycleB_val, upperCycleA_val, pow_succ, pow_add]
+      norm_num
+      rw [show 15 * (2 ^ r * 2) = 30 * 2 ^ r by ring,
+        show 7 * (2 ^ r * 4) = 28 * 2 ^ r by ring,
+        coeff_mul_pow_sub_one_mod_pow (c := 30) (by norm_num),
+        coeff_mul_pow_sub_one_mod_pow (c := 28) (by norm_num)]
+    · apply Fin.ext
+      change stateUpperCarry (T (upperCycleB r)).1 =
+        stateUpperCarry (upperCycleA r).1
+      rw [stateUpperCarry_T_upperCycleB_eq_two hr,
+        stateUpperCarry_upperCycleA_eq_two hr]
+    · simp [s_T_upperCycleB_eq_one hr, s_upperCycleA_eq_one]
+    · change decide (bitWidth (T (T (upperCycleB r))).1 =
+          bitWidth (T (upperCycleB r)).1 + 1) =
+        decide (bitWidth (T (upperCycleA r)).1 =
+          bitWidth (upperCycleA r).1 + 1)
+      rw [bitWidth_T_upperCycleB hr, bitWidth_T_T_upperCycleB hr,
+        bitWidth_upperCycleA hr, bitWidth_T_upperCycleA hr]
+  · apply Fin.ext
+    change normalizedTopTwoBits (T (upperCycleB r)).1 % 4 =
+      normalizedTopTwoBits (upperCycleA r).1 % 4
+    rw [normalizedTopTwoBits_T_upperCycleB_eq_three hr,
+      normalizedTopTwoBits_upperCycleA_eq_three hr]
+
+/-! ## Enriched projected-cycle audit
+
+The old all-ones self-loop is gone, but the realized signature-pair graph still
+has a positive cycle.  Its two edges come from different concrete states,
+which is sufficient: projected potential inequalities are attached to
+signature pairs and therefore telescope around the projected cycle.
+-/
+
 /-- First exact edge identification in the enriched `r = 1` cycle audit. -/
 theorem fixedLowUpperBoundarySignature_T_55_eq_39 :
     fixedLowUpperBoundarySignature 1 (T (⟨55, by decide⟩ : OddNat)) =
@@ -556,6 +938,63 @@ def CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
     (∀ x, C.signature x = fixedLowUpperBoundarySignature 1 x) ∧
       (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
 
+/-- Depth-parametric coverage contract for the top-two enriched signature. -/
+def CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignatureAt
+    {r : ℕ}
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundarySignature r)) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = fixedLowUpperBoundarySignature r x) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/-- At every positive lower-window depth, the symbolic two-cycle has total
+realized width weight `+1`; no sound bounded potential on the enriched finite
+signature can cover all accelerated odd transitions. -/
+theorem not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignatureAt
+    {r : ℕ} (hr : 1 ≤ r)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundarySignature r)) :
+    ¬ CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignatureAt C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  apply C.false_of_two_step_projected_cycle_of_actualWeight_add_pos
+    (hstep (upperCycleA r)) (hstep (upperCycleB r))
+  · rw [hsignature, hsignature]
+    exact fixedLowUpperBoundarySignature_T_upperCycleA_eq_upperCycleB hr
+  · rw [hsignature, hsignature]
+    exact fixedLowUpperBoundarySignature_T_upperCycleB_eq_upperCycleA hr
+  · rw [hweight, hweight, rawSignedWidthWeight_upperCycleA_eq_one hr,
+      rawSignedWidthWeight_upperCycleB_eq_zero hr]
+    norm_num
+
+/-- Coverage through any finite coarsening of the top-two enriched signature. -/
+def CoversAllRawOddTransitionsThroughFixedLowUpperBoundarySignature
+    {r : ℕ} {Signature : Type*} [Fintype Signature]
+    (f : FixedLowUpperBoundarySignature r → Signature)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat Signature) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = f (fixedLowUpperBoundarySignature r x)) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/-- Factoring the enriched observation cannot remove its symbolic positive
+projected two-cycle. -/
+theorem not_coversAllRawOddTransitionsThroughFixedLowUpperBoundarySignature
+    {r : ℕ} (hr : 1 ≤ r)
+    {Signature : Type*} [Fintype Signature]
+    (f : FixedLowUpperBoundarySignature r → Signature)
+    (C : RelationalFiniteSignedTransitionPotentialCertificate OddNat Signature) :
+    ¬ CoversAllRawOddTransitionsThroughFixedLowUpperBoundarySignature f C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  apply C.false_of_two_step_projected_cycle_of_actualWeight_add_pos
+    (hstep (upperCycleA r)) (hstep (upperCycleB r))
+  · rw [hsignature, hsignature,
+      fixedLowUpperBoundarySignature_T_upperCycleA_eq_upperCycleB hr]
+  · rw [hsignature, hsignature,
+      fixedLowUpperBoundarySignature_T_upperCycleB_eq_upperCycleA hr]
+  · rw [hweight, hweight, rawSignedWidthWeight_upperCycleA_eq_one hr,
+      rawSignedWidthWeight_upperCycleB_eq_zero hr]
+    norm_num
+
 /-- The normalized top-two-bit enrichment rejects the old self-loop but still
 admits the positive projected cycle witnessed by `55 -> 83` and `39 -> 59`.
 Consequently it cannot support a global sound bounded potential. -/
@@ -563,26 +1002,8 @@ theorem not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
     (C : RelationalFiniteSignedTransitionPotentialCertificate
       OddNat (FixedLowUpperBoundarySignature 1)) :
     ¬ CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature C := by
-  rintro ⟨hstep, hsignature, hweight⟩
-  let a : OddNat := ⟨55, by decide⟩
-  let b : OddNat := ⟨39, by decide⟩
-  have hab : C.signature (T a) = C.signature b := by
-    rw [hsignature, hsignature]
-    exact fixedLowUpperBoundarySignature_T_55_eq_39
-  have hba : C.signature (T b) = C.signature a := by
-    rw [hsignature, hsignature]
-    exact fixedLowUpperBoundarySignature_T_39_eq_55
-  have hactualAB := C.actual_le_projected a (T a) (hstep a)
-  have hactualBA := C.actual_le_projected b (T b) (hstep b)
-  have hpotentialAB := C.projected_le_potential_diff
-    (C.signature a) (C.signature b)
-  have hpotentialBA := C.projected_le_potential_diff
-    (C.signature b) (C.signature a)
-  rw [hab] at hactualAB
-  rw [hba] at hactualBA
-  rw [hweight, rawSignedWidthWeight_55_eq_one] at hactualAB
-  rw [hweight, rawSignedWidthWeight_39_eq_zero] at hactualBA
-  linarith
+  exact not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignatureAt
+    (r := 1) (by norm_num) C
 
 /-!
 `CoversAllRawOddTransitionsWithFixedLowSignature` is intentionally stronger
@@ -669,4 +1090,149 @@ theorem not_exists_fixedLowRawSignature_globalCertificate
   rintro ⟨C, hC⟩
   exact not_coversAllRawOddTransitionsWithFixedLowSignature hr C hC
 
+/-! ## Top-three audit at depth one
+
+The symbolic top-two cycle proves that two normalized leading bits are
+insufficient at every positive low-window depth.  Adding a third leading bit
+also fails at depth one, but the obstruction changes shape: the projected
+graph contains the positive three-cycle represented by sources `89, 39, 59`.
+This is an exact finite audit, not a bounded-search assumption.
+-/
+
+/-- Exact normalized leading three-bit word. -/
+def normalizedTopThreeBits (x : ℕ) : ℕ :=
+  upperPrefix 3 x
+
+/-- Fixed low data enriched by the normalized leading three-bit word. -/
+structure FixedLowUpperBoundaryThreeSignature (r : ℕ) where
+  low : FixedLowRawSignature r
+  topThree : Fin 8
+  deriving DecidableEq, Fintype
+
+/-- The top-three observation used in the depth-one audit. -/
+noncomputable def fixedLowUpperBoundaryThreeSignature
+    (r : ℕ) (x : OddNat) : FixedLowUpperBoundaryThreeSignature r where
+  low := fixedLowRawSignature r x
+  topThree := ⟨normalizedTopThreeBits x.1 % 8,
+    Nat.mod_lt _ (by norm_num)⟩
+
+/-- Definitional value formula for `T`, retaining the exact observed height. -/
+private theorem T_val_eq_three_mul_add_one_div_pow_s (x : OddNat) :
+    (T x).1 = (3 * x.1 + 1) / 2 ^ (s x) := by
+  unfold T
+  simp [s, threeNPlusOne, pow2]
+
+/-- Exact concrete edges underlying the top-three projected cycle. -/
+theorem T_89_eq_67 :
+    T (⟨89, by decide⟩ : OddNat) = (⟨67, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨89, by decide⟩
+  have h268 : v2 268 = 1 + v2 134 :=
+    v2_step_of_even 268 (by decide) (by omega)
+  have h134 : v2 134 = 1 + v2 67 :=
+    v2_step_of_even 134 (by decide) (by omega)
+  have h67 : v2 67 = 0 := v2_odd 67 (by decide)
+  have ha : s a = 2 := by
+    change v2 268 = 2
+    rw [h268, h134, h67]
+  apply Subtype.ext
+  rw [T_val_eq_three_mul_add_one_div_pow_s a, ha]
+  norm_num [a]
+
+theorem T_39_eq_59 :
+    T (⟨39, by decide⟩ : OddNat) = (⟨59, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨39, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  apply Subtype.ext
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+  norm_num [a]
+
+theorem T_59_eq_89 :
+    T (⟨59, by decide⟩ : OddNat) = (⟨89, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨59, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  apply Subtype.ext
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+  norm_num [a]
+
+/-- The only non-definitional endpoint identification needed by the concrete
+three-cycle: `67` and `39` have the same depth-one top-three signature. -/
+theorem fixedLowUpperBoundaryThreeSignature_67_eq_39 :
+    fixedLowUpperBoundaryThreeSignature 1 (⟨67, by decide⟩ : OddNat) =
+      fixedLowUpperBoundaryThreeSignature 1 (⟨39, by decide⟩ : OddNat) := by
+  let a : OddNat := ⟨67, by decide⟩
+  let b : OddNat := ⟨39, by decide⟩
+  let c : OddNat := ⟨101, by decide⟩
+  let d : OddNat := ⟨59, by decide⟩
+  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hb : s b = 1 := s_eq_one_of_mod_four_eq_three (by decide)
+  have hTa : T a = c := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
+    norm_num [a, c]
+  have hTb : T b = d := by
+    apply Subtype.ext
+    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one b hb]
+    norm_num [b, d]
+  have wa : bitWidth a.1 = 7 := by decide
+  have wb : bitWidth b.1 = 6 := by decide
+  have wc : bitWidth c.1 = 7 := by decide
+  have wd : bitWidth d.1 = 6 := by decide
+  change fixedLowUpperBoundaryThreeSignature 1 a =
+    fixedLowUpperBoundaryThreeSignature 1 b
+  unfold fixedLowUpperBoundaryThreeSignature
+  congr 1
+  · unfold fixedLowRawSignature
+    congr 1
+    · apply Fin.ext
+      norm_num [a, b]
+    · apply Fin.ext
+      norm_num [stateUpperCarry, upperCarry3n1, wa, wb, a, b]
+    · simp [ha, hb]
+    · simp [hTa, hTb, wa, wb, wc, wd]
+  · apply Fin.ext
+    norm_num [normalizedTopThreeBits, upperPrefix, wa, wb, a, b]
+
+/-- The three concrete edges have weights `0, 0, +1`. -/
+theorem rawSignedWidthWeight_89_67_eq_zero :
+    rawSignedWidthWeight (⟨89, by decide⟩ : OddNat)
+      (⟨67, by decide⟩ : OddNat) = 0 := by decide
+
+theorem rawSignedWidthWeight_39_59_eq_zero :
+    rawSignedWidthWeight (⟨39, by decide⟩ : OddNat)
+      (⟨59, by decide⟩ : OddNat) = 0 := by decide
+
+theorem rawSignedWidthWeight_59_89_eq_one :
+    rawSignedWidthWeight (⟨59, by decide⟩ : OddNat)
+      (⟨89, by decide⟩ : OddNat) = 1 := by decide
+
+/-- Global transition coverage contract for the depth-one top-three audit. -/
+def CoversAllRawOddTransitionsWithFixedLowUpperBoundaryThreeSignature
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundaryThreeSignature 1)) : Prop :=
+  (∀ x, C.Step x (T x)) ∧
+    (∀ x, C.signature x = fixedLowUpperBoundaryThreeSignature 1 x) ∧
+      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))
+
+/-- Three normalized leading bits still admit a positive projected cycle at
+depth one, so they cannot carry a global sound bounded potential. -/
+theorem not_coversAllRawOddTransitionsWithFixedLowUpperBoundaryThreeSignature
+    (C : RelationalFiniteSignedTransitionPotentialCertificate
+      OddNat (FixedLowUpperBoundaryThreeSignature 1)) :
+    ¬ CoversAllRawOddTransitionsWithFixedLowUpperBoundaryThreeSignature C := by
+  rintro ⟨hstep, hsignature, hweight⟩
+  let a : OddNat := ⟨89, by decide⟩
+  let b : OddNat := ⟨39, by decide⟩
+  let c : OddNat := ⟨59, by decide⟩
+  apply C.false_of_three_step_projected_cycle_of_actualWeight_add_pos
+    (hstep a) (hstep b) (hstep c)
+  · rw [T_89_eq_67, hsignature, hsignature]
+    exact fixedLowUpperBoundaryThreeSignature_67_eq_39
+  · rw [T_39_eq_59]
+  · rw [T_59_eq_89]
+  · rw [hweight, hweight, hweight, T_89_eq_67, T_39_eq_59, T_59_eq_89,
+      rawSignedWidthWeight_89_67_eq_zero,
+      rawSignedWidthWeight_39_59_eq_zero,
+      rawSignedWidthWeight_59_89_eq_one]
+    norm_num
+
 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-335.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-335.md
new file mode 100644
index 00000000..f58ce14a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-335.md
@@ -0,0 +1,278 @@
+# Petal / FloatWindow implementation report - checkpoint 335
+
+## Result
+
+Checkpoint 335 closes both requested branches without `sorry`.
+
+The positive FIFO branch is now global rather than recursive-only: the owned
+queue before any canonical block is exactly the newest upper tail of all
+historical carry-two claims after deleting the cumulative *actual* consumed
+count.  This yields exact source-age, deficit, maximum-age, minimax, and
+conditional eventual-consumption theorems.
+
+The negative finite-signature branch is also globalized.  The normalized
+top-two enrichment fails at every lower-window depth `r >= 1`, and every finite
+coarsening of that enrichment fails with it.  A separate exact audit proves
+that normalized top-three data still fails at depth one.
+
+No theorem here proves that a uniform source-age bound exists.  No theorem is
+claimed for arbitrary upper-prefix length.
+
+## Global source-owned FIFO normal form
+
+The new module
+
+```text
+DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
+```
+
+defines the historical and cumulative carriers
+
+```text
+canonicalHistoricalClaimSourceCarrier
+canonicalOwnedCumulativeConsumedClaimsBeforeBlock
+canonicalCumulativeConsumedCountBeforeBlock.
+```
+
+Lean proves that consumed source carriers from distinct blocks are disjoint,
+that a consumed identity never reappears in a later available or consumed
+carrier, and that cumulative source cardinality equals cumulative scalar
+actual consumption.
+
+The exact historical partition is
+
+```text
+historical claims
+  = cumulative consumed identities union outstanding owned identities,
+```
+
+with a disjoint union.  Its cardinal form agrees with both the scalar queue
+and the existing demand prefix sum.
+
+The central global theorem is
+
+```text
+canonicalOwnedOutstandingClaimsBeforeBlock n m
+  = eraseOldestN
+      (canonicalCumulativeConsumedCountBeforeBlock n m)
+      (canonicalHistoricalClaimSourceCarrier n m).
+```
+
+The deletion count is actual consumption.  Unused service is not carried into
+the normal form.
+
+## Generic oldest-first threshold theorem
+
+`OldestFirstQueue.lean` now proves the generic equivalence
+
+```text
+eraseOldestN c s subset filter (t <= .) s
+  <->
+card (eraseOldestN c s) <= card (filter (t <= .) s).
+```
+
+The reverse direction uses the fact that `eraseOldestN` is the newest upper
+tail, including the empty-remainder case.  A uniqueness theorem also says
+that a same-cardinality subset lying entirely in the complement of the
+discarded lower prefix must be the FIFO remainder itself.
+
+## Exact source-age characterizations
+
+Using the global normal form and the generic threshold theorem, Lean proves
+
+```text
+CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
+  <->
+CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H.
+```
+
+Thus the earlier scalar cardinal condition is now an exact characterization
+of actual FIFO source age, not merely a consequence of it.
+
+The old-source carrier and signed deficit are also explicit:
+
+```text
+oldSourceClaims.card - cumulativeConsumed
+  = outstandingQueue - recentSourceClaims.card
+```
+
+in `Int`, and
+
+```text
+owned source age <= H at block m
+  <-> canonicalSourceAgeDeficit n H m <= 0.
+```
+
+The global version quantifies this condition over every canonical block.
+
+## Oldest source, maximum age, and FIFO optimality
+
+The API now contains
+
+```text
+canonicalOldestOutstandingSource
+canonicalOwnedMaximumSourceAge
+CanonicalAdmissibleOwnedRemainder.
+```
+
+The maximum age of an empty queue is explicitly zero.  Uniform actual source
+age is equivalent to bounding this maximum age at every block.
+
+For every admissible subset of historical claims having the scalar queue's
+cardinality, FIFO maximizes the minimum retained source.  Equivalently, it
+minimizes the maximum source age among source assignments realizing the same
+scalar outstanding queue.  This is a comparison of assignments at one block;
+it does not model an arbitrary alternative recursive policy.
+
+## Conditional eventual consumption
+
+Assuming a uniform actual source-age bound `H`, every source older than `H` is
+absent from the owned queue.  Since every canonical block has positive length,
+a source born in block `k` has a consuming block witness before
+
+```text
+k + H + 2.
+```
+
+This is a genuine source-to-consumption-block result, but remains conditional
+on the uniform age hypothesis.  The existence of such an `H` is still the
+primary positive Gap.
+
+## Reusable projected-cycle obstruction
+
+`FiniteSignedTransition.lean` now exposes generic positive projected-cycle
+contradictions for both two and three realized edges.  Concrete source states
+need not form an orbit cycle; only their projected endpoint signatures must
+close, while their realized weights have positive total.
+
+This isolates the exact logical obstruction:
+
+```text
+closed projected cycle + positive actual total weight
+  -> no sound bounded-potential certificate covering those edges.
+```
+
+## Symbolic top-two obstruction at every depth
+
+For every `r >= 1`, the symbolic sources are
+
+```text
+A_r = 7 * 2^(r + 2) - 1
+B_r = 5 * 2^(r + 2) - 1.
+```
+
+Lean proves their first and second successor values, all six exact binary
+widths, lower residues, heights, upper carries, normalized top-two words, and
+width-growth flags.  The endpoint signatures close as
+
+```text
+signature (T A_r) = signature B_r
+signature (T B_r) = signature A_r,
+```
+
+while the two realized signed-width weights are `+1` and `0`.
+
+Therefore, for every `r >= 1`, no global bounded-potential certificate using
+
+```text
+FixedLowUpperBoundarySignature r
+```
+
+can cover all accelerated odd transitions.  The former `r = 1` witnesses
+`55` and `39` remain as concrete regressions, and their obstruction theorem is
+now a corollary of the depth-parametric result.
+
+The same obstruction survives every finite factor
+
+```text
+f : FixedLowUpperBoundarySignature r -> Signature.
+```
+
+This rejects coarsenings only.  A strict refinement carrying genuinely new
+upper information is outside the theorem.
+
+## Top-three depth-one audit
+
+The next enrichment retains normalized top-three bits.  At `r = 1`, Lean
+proves the exact concrete transitions
+
+```text
+89 -> 67
+39 -> 59
+59 -> 89
+```
+
+with signed-width weights `0`, `0`, and `+1`.  It also proves every coordinate
+needed for the nontrivial identification
+
+```text
+fixedLowUpperBoundaryThreeSignature 1 67
+  = fixedLowUpperBoundaryThreeSignature 1 39.
+```
+
+The other two cycle links are exact concrete endpoint equalities.  Hence the
+top-three depth-one observation also cannot support a global sound bounded
+potential covering every accelerated odd edge.
+
+This does not justify an arbitrary-prefix theorem.  It establishes one exact
+three-bit obstruction and shows that adding one more normalized leading bit
+does not by itself resolve the information loss.
+
+## What is now fact
+
+The following statements are formally established:
+
+1. The recursive canonical owned queue is globally the newest historical
+   upper tail after cumulative actual consumption.
+2. FIFO source age `<= H`, recent-source cardinal coverage, nonpositive
+   source-age deficit, and maximum source age `<= H` are equivalent views of
+   the same condition.
+3. FIFO is source-age optimal among same-cardinality assignments of historical
+   claims.
+4. A uniform source-age bound would force every source to be consumed within
+   an explicit finite block lag.
+5. Fixed-low plus normalized top-two data fails for every `r >= 1`, including
+   every finite coarsening of that observation.
+6. Fixed-low plus normalized top-three data fails at `r = 1`.
+
+The remaining positive problem is not representation bookkeeping.  It is the
+actual arithmetic theorem
+
+```text
+exists H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H.
+```
+
+Nothing in this checkpoint assumes or proves that statement.
+
+## Verification
+
+All changed Collatz/FloatWindow files contain no new `sorry`.
+
+Successful build gates:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
+lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+```
+
+## Suggested continuation
+
+The next positive route should target `canonicalSourceAgeDeficit` directly.
+The global queue theory has reduced actual age boundedness to the signed
+inequality
+
+```text
+old source demand <= cumulative actual consumption.
+```
+
+A useful next checkpoint would search for an arithmetic amortization theorem
+that controls this deficit without replacing actual consumption by total
+service.
+
+On the negative route, further upper-prefix experiments should first locate
+and then exactly prove a projected cycle for each proposed strict refinement.
+The top-three result alone must not be extrapolated to arbitrary prefix length.
````
`````
