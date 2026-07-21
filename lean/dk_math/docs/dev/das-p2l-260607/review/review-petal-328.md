# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: e72bf85e63f6b4f9bc50d076fb1309c575169527

## Report

(11m24s)

cp-328 の主要登頂を完了しました。

**証明された事実**

- 飽和 block の次の開始状態は必ず `stateUpperCarry = 1`
- successor の最深 depth は block 開始座標と一致
- その最深 depth は必ず claim hole
- successor の claim 数は `length - 1` 以下
- 長さ 1 の successor の claim 数は `0`
- `CanonicalLengthOneBalancedCarrySuccessor` は存在しない
- 非空な `CanonicalLengthOneTerminalOneSuccessor` を新設
- この successor は drift `-1` で、predecessor の drift `1` と相殺
- 別の `mod 16 = 3` 分岐では successor drift は `-2` 以下
- 任意の有効 depth について次の完全な内部状態式を証明

```text
iterateT(sourceAtDepth d) + 1 = 2^d * 3^(L-d) * oddCore
```

さらに、claim depth であることと、その exact core word の upper carry が `2` であることの同値も固定しました。

本当の停止点は局所算術ではなく、有限 root への subtree ownership、temporal ownership、非再利用または一様 multiplicity bound が未構成であることです。同じ upper-boundary resource を複数回使用していないことを証明できるまでは、局所 budget を安全に大域加算できません。

結果は [report-petal-328.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-328.md) に記録し、cp-327 の古い停止診断にも訂正を追記しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

変更箇所に `sorry`、`maxHeartbeats` はありません。

## Review

## 結論

**全面採用。局所 saturated-successor 解析は閉じた。**

cp-328 は、cp-327 で例外候補とされた length-one balanced-carry successor を消滅させた。

核心は、

```lean
CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one
```

じゃ。

saturated block の次の開始状態は、successor の length や terminal valuation に関係なく、必ず own-width carry $1$ になる。したがって、successor の最深 depth は必ず claim hole であり、長さ $1$ なら claim count は $0$ となる。

これにより、

```lean
CanonicalLengthOneBalancedCarrySuccessor
```

は空であることが証明された。

さらに任意の block 内部について、

$$\operatorname{iterateT}(\operatorname{sourceAtDepth}(d))+1=2^d3^{L-d}u$$

という完全な core-word 表現が得られ、claim membership もこの exact word の upper carry だけで判定できるようになった。

現在の本当の境界が局所算術ではなく、大域的な resource ownership にあるという診断は正しい。

ただし、次へ進む前に二点整理すべきじゃ。

- `CanonicalLengthOneTerminalOneSuccessor` は「非空と証明された」わけではない。
- finite initial root による resource model は、uniform width bound を仮定に埋め込む循環構造にならないよう設計する必要がある。

---

## 1. Saturated next-start carry obstruction

saturated block の start state を $x$、odd core を $u$、successor start を $y$ とする。

既存 normal form から、

$$x=4u-1$$

$$y=\frac{9u-1}{2}$$

が得られる。

さらに $u\equiv3\pmod4$ なので $u\ge3$。

このとき、

$$3y+1<4x$$

となる。

一方、saturated block の exact unit drift により、

$$\operatorname{bitWidth}(y)=\operatorname{bitWidth}(x)+1$$

である。

$x<2^{\operatorname{bitWidth}(x)}$ と合わせると、

$$3y+1<2^{\operatorname{bitWidth}(y)+1}$$

となり、carry-two threshold に到達しない。

したがって、

$$\operatorname{stateUpperCarry}(y)=1$$

じゃ。

この theorem は、単に「連続 saturation がない」より強い。

> saturated block の直後の block start は、claim source にならない。

という exact source obstruction である。

---

## 2. Deepest depth は block start

```lean
canonicalPaymentSourceAtDepth_length_eq_startTime
```

により、

$$\operatorname{sourceAtDepth}(L)=\operatorname{blockStartTime}$$

が証明された。

したがって saturated predecessor の successor では、最深 depth $L$ における source state の upper carry が $1$ となる。

よって、

$$L\in\operatorname{ClaimHoles}$$

が得られた。

これから直ちに、

$$H\ge1$$

$$A\le L-1$$

が従う。

これは cp-327 で不足していると思われた claim-transport theorem そのものじゃった。

claim count を predecessor residue から遠回りして運ぶ必要はなく、

```text
saturated width shift
→ successor start carry one
→ deepest depth is a hole
```

という短い橋で閉じた。

---

## 3. Length-one balanced-carry successor の消滅

successor length が $1$ なら、depth interval は ${1}$ だけになる。

そしてその唯一の depth は最深 depthであり、必ず claim hole。

したがって、

$$A_{k+1}=0$$

じゃ。

よって、

```lean
CanonicalLengthOneBalancedCarrySuccessor
```

が要求していた、

$$A_{k+1}=1$$

とは両立しない。

```lean
not_canonicalLengthOneBalancedCarrySuccessor
```

によって、この predicate は完全に消滅した。

これは大きい。

cp-327 の persistence obstruction は、未解決だったのではなく、対象そのものが存在しなかった。

---

## 4. 古い vacuous API の扱い

現在も互換性のため、

```lean
canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
```

や旧 namespace 内の theorem が残っている可能性がある。

これらは論理的には正しいが、前提が空なので数学的には vacuous じゃ。

削除せず残す場合は、少なくとも doc comment で明示すべきである。

```text
Historical compatibility theorem.

The premise `CanonicalLengthOneBalancedCarrySuccessor` is impossible by
`not_canonicalLengthOneBalancedCarrySuccessor`.  Do not use this theorem as a
nonempty persistence surface.
```

今後の実装では旧 predicate を premise に使わず、

```lean
CanonicalLengthOneTerminalOneSuccessor
```

へ移行するべきじゃ。

---

## 5. `CanonicalLengthOneTerminalOneSuccessor` の意味

新 predicate は、

- predecessor が saturated
- successor length が $1$
- successor terminal valuation が $1$

だけを要求する。

claim count $1$ は要求しない。

この条件は、

$$u\equiv11\pmod{16}$$

と同値である。

また successor claim count は $0$ なので、

$$D_{k+1}=0-1=-1$$

となる。

saturated predecessor の drift は $1$ なので、

$$D_k+D_{k+1}=0$$

じゃ。

つまり、この residue class は局所例外ではなく、

> saturated unit を次 block で正確に返済する equality branch

である。

ただし「非空な predicate」という report の表現は少し強い。

現在証明されたのは、

> 以前の明白な矛盾を含まない、正しい conditional surface

であって、実際にこの predicate を満たす orbit block が存在する theorem ではない。

「nonvacuous」より、

```text
non-contradictory conditional grammar
```

または、

```text
claim-free residue grammar
```

と表現する方が正確じゃ。

---

## 6. 別の residue class

successor length が $1$ で、

$$u\equiv3\pmod{16}$$

なら、terminal valuation は $1$ ではない。

terminal valuation は常に正なので、

$$v_{k+1}\ge2$$

となる。

claim count は同じく $0$ だから、

$$D_{k+1}\le-2$$

じゃ。

したがって、

$$D_k+D_{k+1}\le-1$$

となり、strict repayment が成立する。

length-one successor は residue にかかわらず全て返済 branch になった。

---

## 7. Generic block-core normal form

今回の最も再利用価値が高い theorem は、

```lean
canonicalPaymentSourceAtDepth_iterate_add_one_eq
```

じゃ。

任意の有効 depth $1\le d\le L$ について、

$$x_d+1=2^d3^{L-d}u$$

となる。

ここで、

$$x_d=(\operatorname{iterateT}(\operatorname{sourceAtDepth}(d)),n).1$$

じゃ。

したがって、

$$x_d=2^d3^{L-d}u-1$$

である。

claim membership も、

$$d\in\operatorname{Claims}\iff\operatorname{stateUpperCarry}(2^d3^{L-d}u-1)=2$$

となった。

これによって claim-depth carrier は、orbit time の複雑な定義を毎回展開せず、$L,u,d$ の三変数による有限算術 profile として研究できる。

---

## 8. Core word を定義として切り出すべき

現在、長い式、

```lean
2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
  canonicalBlockOddCore n k - 1
```

が theorem statement に直接現れる。

次にはこれを API 化するのがよい。

```lean
def canonicalBlockCoreWordAtDepth
    (n : OddNat) (k d : ℕ) : ℕ :=
  2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
    canonicalBlockOddCore n k - 1
```

そして既存 theorem を次の形へラップする。

```lean
theorem iterateT_sourceAtDepth_eq_coreWordAtDepth ...

theorem mem_claimDepths_iff_coreWordAtDepth_carryTwo ...
```

これにより、今後の residue・width・carry profile theorem が大幅に読みやすくなる。

---

## 9. 隣接 depth の exact recurrence

core word を $W_d$ と置く。

$$W_d+1=2^d3^{L-d}u$$

なので、$d<L$ なら、

$$3(W_{d+1}+1)=2(W_d+1)$$

が成立する。

これは重要な次段 theorem じゃ。

```lean
theorem three_mul_coreWordAtDepth_succ_add_one_eq_two_mul
    (hd1 : 1 ≤ d)
    (hdL : d < canonicalBlockLength n k) :
    3 * (canonicalBlockCoreWordAtDepth n k (d + 1) + 1) =
      2 * (canonicalBlockCoreWordAtDepth n k d + 1)
```

この recurrence は、claim profile の隣接遷移を直接扱う入口になる。

```text
carry one / carry two
bit width
claim / hole
```

の変化を、同じ block 内で一段ずつ輸送できる。

global resource routeとは独立に進められる、有力な local grammar API じゃ。

---

## 10. Zero-carrier balanced successor の圧縮

cp-326 では zero-carrier balanced block は、

- full balanced branch
- exceptional length-two branch

の二種類だった。

しかし saturated successor には最深 hole が必ず存在するため、hole 数 $0$ の full balanced branch は不可能。

したがって saturated successor が zero-carrier balanced なら必ず、

$$L=2$$

$$v=1$$

$$A=1$$

$$H=1$$

となる。

さらに唯一の hole は最深 depth $2$ なので、

$$\operatorname{Claims}={1}$$

じゃ。

この theorem は cp-328 の自然な直後に置ける。

---

## 11. Tight valuation-one successor の穴位置

tight valuation-one positive block は $H=1$。

saturated successor では最深 depth $L$ が hole。

hole が一個しかないので、

$$d_{\mathrm{missing}}=L$$

となる。

したがって、

$$\operatorname{Claims}=\operatorname{Icc}(1,L-1)$$

じゃ。

これにより tight successor の claim profile は完全に固定される。

```text
全ての内部・endpoint-side depth は claim
block start に対応する最深 depth だけ hole
```

この profile は source-incidence 層で no-spare だが、positive nonsaturated なので既存 abstract dyadic half-budget では処理できる。

---

## 12. Saturated predecessor の局所 discharge は閉じる

successor drift の符号で分ければよい。

### Negative successor

scalar repayment。

$$1+D_{k+1}\le0$$

### Zero successor

length $1$ なら claim count $0$ かつ terminal valuation は正なので drift は負になり、zero ではない。

したがって zero successor なら、

$$L\ge2$$

となる。

よって `abstractZeroSuccessorUnitEmbedding` が使える。

### Positive successor

consecutive saturation はないので nonsaturated。

既存 theorem により、

- saturated unit を lower two slots
- successor demand を upper half

へ disjoint に埋め込める。

したがって、

> saturated predecessor の unit は、全 successor branch で abstract dyadic budget 内に局所 discharge できる。

局所不足候補は完全に消えた。

---

## 13. Genuine obstruction の精密化

report の、

> finite initial-root carrier、subtree ownership、temporal ownership、nonreuse がない

という診断は方向として正しい。

しかし、設計上の注意がある。

有限自然数は上位に無限の zero padding を持つ。

したがって、

```text
上位 zero bit は有限個しかない
```

という資源モデルは使えない。

また、

```text
初期値から決まる有限 root に、全 block budget を互いに素に埋め込める
```

という structure を仮定すると、その仮定自体が uniform bound をほぼ内包してしまう可能性がある。

既存 scalar queue 層では既に、

$$\exists C,\ Q_m\le C\quad\Longleftrightarrow\quad\exists B,\ \operatorname{endpointWidth}_m\le B$$

が得られている。

したがって finite global resource structure が単に全 demand の有限 injection を公理として持つなら、求めたい width bound を別名で仮定しただけになる。

---

## 14. Global interface に必要な非循環性

次の global resource interface は、結果を直接仮定してはならない。

安全な候補は **状態遷移型** じゃ。

各 block 時点に有限 resource state $R_k$ を持ち、

```text
initial resource:
  initial natural numberから具体的に構成

transition:
  local Collatz block dataから R_k → R_{k+1} を構成

consumption:
  block demand は R_k の一部を消費

conservation:
  potential(R_{k+1}) + consumed ≤ potential(R_k) + explicit replenishment

replenishment:
  新規発行ではなく、negative drift / width decrease 等から導出
```

という形が必要になる。

これなら finite bound を初めから公理として入れず、local transition theorem の累積から大域 bound を得られる。

---

## 15. 二つの次ルート

ここからは二路並行がよい。

### Route A: claim-profile grammar

core word recurrenceを使い、

- claim/hole の隣接遷移
- hole 数の下界
- tight profile の persistence 不可
- positive block 後の必須 hole

を直接攻める。

これは scalar queue の arrivals を制限する方向じゃ。

### Route B: amortized global potential

abstract dyadic budget を、有限初期 stock ではなく、

- current width
- running width minimum
- negative drift repayment
- claim-hole service

を含む動的 potential へ接続する。

こちらは queue の高さを直接抑える方向じゃ。

今の段階では、abstract forest を先に大量実装するより、どちらの route が非循環な保存則を持てるかを design theorem で比較すべきじゃ。

---

## 16. Lean Comparator Challenge への現在地

最終形は、

```lean
theorem collatz_conjecture (n : ℕ) (hn : n > 0) :
  ∃ m, collatzStep^[m] n = 1
```

じゃ。

cp-328 で局所 saturated unit は全 branch で処理可能になった。

現在の幹線は、

```text
exact block-core claim profile
→ local abstract discharge
→ global amortized/nonreuse law
→ uniform scalar queue bound
→ uniform endpoint bit-width bound
→ finite-state eventual periodicity
→ nontrivial cycle elimination
→ accelerated convergence
→ standard Collatz bridge
```

となる。

局所 arithmetic の穴は埋まった。

次は、局所証明を大域へ足してよい理由そのものを作る段階じゃ。

## 判定まとめ

### Saturated next-start carry one

**完成。非常に強い中心 theorem。**

### Deepest successor claim hole

**完成。**

### Length-one balanced-carry exception

**消滅。**

### Length-one terminal-one residue grammar

**完成。ただし実在性までは未証明。**

### Generic claim-profile core word

**完成。今後の主力 API。**

### Local saturated abstract discharge

**ほぼ完成。統合 theorem が未実装。**

### Global ownership

**未完成。本当の次戦線。**

### 注意点

**finite resource を仮定に直接埋め込む循環を避ける必要がある。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-328.

The cp-328 implementation is accepted.

The former local exceptional successor is impossible.  Saturated-successor
local discharge is now complete at the abstract dyadic level.

Before constructing a global forest, clean the vacuous compatibility surface,
package the generic block-core profile, and prove the unified local discharge
theorem.

## Stage A — vacuous API cleanup

Keep `CanonicalLengthOneBalancedCarrySuccessor` only for compatibility.

Add documentation that it is impossible by:

    not_canonicalLengthOneBalancedCarrySuccessor.

Do not use it in any new theorem.

Move or duplicate all useful arithmetic theorems under:

    CanonicalLengthOneTerminalOneSuccessor.

Avoid saying that this new predicate is inhabited unless an explicit existence
theorem is proved.

## Stage B — block-core word API

Define:

    canonicalBlockCoreWordAtDepth n k d :=
      2^d * 3^(blockLength - d) * oddCore - 1.

Add wrappers:

    iterateT_sourceAtDepth_eq_coreWordAtDepth;

    mem_claimDepths_iff_coreWordAtDepth_carryTwo.

Keep the existing expanded theorem names for compatibility.

## Stage C — adjacent-depth recurrence

For `1 <= d < blockLength`, prove:

    3 * (coreWordAtDepth (d + 1) + 1)
      =
    2 * (coreWordAtDepth d + 1).

Also prove the matching source-time adjacency:

    sourceAtDepth (d + 1) + 1
      =
    sourceAtDepth d.

Use these as the generic internal claim-transport surface.

## Stage D — rigid successor profile refinement

For a saturated predecessor prove:

    successor deepest depth is a claim hole.

Then derive:

    a zero-carrier balanced successor must satisfy
      length = 2,
      terminal valuation = 1,
      claim count = 1,
      claim depths = {1},
      claim holes = {2};

    a tight valuation-one positive successor has
      unique missing depth = block length,
      claim depths = Icc 1 (block length - 1).

Eliminate the full-balanced zero-carrier branch from saturated successors.

## Stage E — unified local saturated discharge

Prove one theorem splitting the successor into:

    negative drift;

    zero drift with length at least two;

    positive nonsaturated drift.

For each branch package the existing discharge certificate:

    negative:
      predecessor drift + successor drift <= 0;

    zero:
      Fin 2 embeds into the successor abstract budget;

    positive:
      Fin 2 and successor demand embed disjointly into the successor abstract
      budget.

Define a proposition or structure:

    CanonicalSaturatedSuccessorAbstractDischarge.

Prove every saturated block has such a certificate.

State explicitly that this is not an actual bit-resource allocation.

## Stage F — local length-one repayment theorem

For every saturated block whose successor has length one, prove:

    successor claim count = 0;

    successor drift <= -1;

    predecessor drift + successor drift <= 0.

Refine:

    core mod 16 = 11 -> exact sum = 0;

    core mod 16 = 3 -> sum <= -1.

This theorem should replace the old exceptional persistence narrative.

## Stage G — claim-profile transition audit

Using the adjacent core-word recurrence, investigate how carry one/two changes
between depths.

Seek exact implications of the form:

    carry two at depth d and arithmetic condition
      ->
    carry one at depth d + 1;

    long consecutive claim run
      ->
    a residue restriction on oddCore.

Do not assume monotonicity of claim depths.

Record counterexamples if claim/hole patterns can alternate.

## Stage H — noncircular global resource interface

Do not define a structure whose axioms already include a global injection of
all block demands into a finite carrier.

Instead define a transition-based interface containing:

    resource state at each block;
    an initial state constructed from the initial natural number;
    local consumption by the current block demand;
    explicit transition to the next resource state;
    a natural-valued potential;
    a one-step conservation inequality;
    any replenishment term derived from an already proved negative drift or
    width decrease.

Prove generically:

    a uniform potential ceiling plus bounded replenishment
      ->
    a uniform causal queue bound.

Do not assert that the Collatz instance exists.

## Stage I — compare two global routes

Route 1:
    derive stronger claim-hole density from the core-word recurrence.

Route 2:
    instantiate a dynamic amortized resource transition from width and drift.

For each route, identify the first theorem that is not already equivalent to
the desired uniform width bound.

Reject any hypothesis that merely renames:

    CanonicalOutstandingClaimQueueUniformUpperBound
    or
    CanonicalEndpointWidthUniformUpperBound.

## Stage J — conditional challenge-facing surface

Prove a conditional chain with named hypotheses:

    noncircular global amortization law
      ->
    uniform scalar queue bound
      ->
    uniform endpoint-width bound.

Stop there.

Do not yet infer eventual periodicity, cycle elimination, or convergence unless
their separate bridge theorems are present.

## Stopping rule

Stop at the first genuine obstruction among:

    core-word adjacent recurrence fails;
    rigid successor profile does not collapse as predicted;
    unified local discharge cannot be packaged;
    claim profile has unrestricted alternating patterns;
    every proposed global resource law is equivalent to the desired queue
    bound;
    width-based replenishment admits uncontrolled repeated reuse.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-329.md
```

cp-328 で、saturated block の局所借金は全て処理できるところまで来た。

次は「有限資源を置く」のではなく、**資源が一歩ごとにどう保存・消費・回復するか**を作る番じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
index 4d41fe3e..063715f9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmplitude.lean
@@ -1635,6 +1635,83 @@ noncomputable def oneEmbedding_canonicalSelectedDriftSpareCarrier

 /-! ### Claim-hole accounting normal form -/

+/-- The deepest block depth is exactly the block's start time. -/
+theorem canonicalPaymentSourceAtDepth_length_eq_startTime
+    (n : OddNat) (k : ℕ) :
+    canonicalPaymentSourceAtDepth n k (canonicalBlockLength n k) =
+      canonicalBlockStartTime n k := by
+  unfold canonicalPaymentSourceAtDepth
+  have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+  have hL := one_le_canonicalBlockLength n k
+  omega
+
+/--
+Exact state at a valid block depth.  Depth counts backwards from the endpoint,
+so the dyadic exponent is `d` while the ternary exponent is `L - d`.
+-/
+theorem canonicalPaymentSourceAtDepth_iterate_add_one_eq
+    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
+    (hdL : d ≤ canonicalBlockLength n k) :
+    (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 + 1 =
+      2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
+        canonicalBlockOddCore n k := by
+  let L := canonicalBlockLength n k
+  let t := L - d
+  have ht : t < L := by omega
+  have htd : t + d = L := by omega
+  have hsource : canonicalPaymentSourceAtDepth n k d =
+      canonicalBlockStartTime n k + t := by
+    unfold canonicalPaymentSourceAtDepth
+    have hend := canonicalBlockStartTime_add_length_sub_one_eq_endpoint n k
+    dsimp [L, t]
+    omega
+  have hnormal :=
+    canonicalBlock_iterate_add_one_eq_pow_mul_pow_mul_oddCore n k t (by
+      simpa [L] using ht)
+  rw [← hsource] at hnormal
+  have hpow : 2 ^ canonicalBlockLength n k = 2 ^ t * 2 ^ d := by
+    have htd' : t + d = canonicalBlockLength n k := by
+      simpa [L] using htd
+    rw [← htd']
+    exact pow_add 2 t d
+  rw [hpow] at hnormal
+  have hcancel :
+      2 ^ t * ((iterateT (canonicalPaymentSourceAtDepth n k d) n).1 + 1) =
+        2 ^ t * (2 ^ d * 3 ^ t * canonicalBlockOddCore n k) := by
+    calc
+      _ = 3 ^ t * (2 ^ t * 2 ^ d * canonicalBlockOddCore n k) := hnormal
+      _ = 2 ^ t * (2 ^ d * 3 ^ t * canonicalBlockOddCore n k) := by ring
+  have htpos : 0 < 2 ^ t := pow_pos (by norm_num) t
+  have hresult := Nat.eq_of_mul_eq_mul_left htpos hcancel
+  simpa [L, t] using hresult
+
+/-- Generic claim-profile transport in block-core coordinates. -/
+theorem mem_canonicalPaymentClaimDepths_iff_stateUpperCarry_coreWord
+    (n : OddNat) (k d : ℕ) (hd1 : 1 ≤ d)
+    (hdL : d ≤ canonicalBlockLength n k) :
+    d ∈ canonicalPaymentClaimDepths n k ↔
+      stateUpperCarry
+        (2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
+          canonicalBlockOddCore n k - 1) = 2 := by
+  rw [mem_canonicalPaymentClaimDepths_iff]
+  have hform := canonicalPaymentSourceAtDepth_iterate_add_one_eq
+    n k d hd1 hdL
+  have hstate :
+      (iterateT (canonicalPaymentSourceAtDepth n k d) n).1 =
+        2 ^ d * 3 ^ (canonicalBlockLength n k - d) *
+          canonicalBlockOddCore n k - 1 := by
+    omega
+  have hdL' : d ≤ canonicalPaymentBlockLength n k := by
+    simpa [canonicalBlockLength] using hdL
+  constructor
+  · rintro ⟨_, _, hcarry⟩
+    unfold CarryTwoDebtAt at hcarry
+    simpa [hstate] using hcarry
+  · intro hcarry
+    refine ⟨hd1, hdL', ?_⟩
+    unfold CarryTwoDebtAt
+    simpa [hstate] using hcarry
+
 /-- Positive depths in the block which do not carry a canonical payment
 claim. -/
 noncomputable def canonicalBlockClaimHoles
@@ -1682,6 +1759,45 @@ theorem canonicalBlockClaimCount_add_claimHoles_card
   have hL := one_le_canonicalBlockLength n k
   omega

+/-- The successor of a saturated block always misses its deepest claim.
+
+The missing depth is structural: it is the successor start coordinate, whose
+own-width carry is one by the saturated predecessor width obstruction.
+-/
+theorem CanonicalSaturatedBorderBlock.next_length_mem_claimHoles
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockLength n (k + 1) ∈
+      canonicalBlockClaimHoles n (k + 1) := by
+  classical
+  apply Finset.mem_sdiff.mpr
+  constructor
+  · exact Finset.mem_Icc.mpr
+      ⟨one_le_canonicalBlockLength n (k + 1), le_rfl⟩
+  · intro hclaim
+    have hcarry := (mem_canonicalPaymentClaimDepths_iff.mp hclaim).2.2
+    unfold CarryTwoDebtAt at hcarry
+    rw [canonicalPaymentSourceAtDepth_length_eq_startTime] at hcarry
+    change stateUpperCarry (canonicalBlockStartState n (k + 1)) = 2 at hcarry
+    rw [h.nextStart_stateUpperCarry_eq_one] at hcarry
+    omega
+
+/-- A saturated predecessor forces a nonempty claim-hole carrier in its
+successor. -/
+theorem CanonicalSaturatedBorderBlock.one_le_next_claimHoles_card
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    1 ≤ (canonicalBlockClaimHoles n (k + 1)).card :=
+  Finset.one_le_card.mpr ⟨_, h.next_length_mem_claimHoles⟩
+
+/-- A saturated predecessor prevents its successor from claiming every block
+depth. -/
+theorem CanonicalSaturatedBorderBlock.next_claimCount_le_length_sub_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    canonicalBlockClaimCount n (k + 1) ≤
+      canonicalBlockLength n (k + 1) - 1 := by
+  have hpartition := canonicalBlockClaimCount_add_claimHoles_card n (k + 1)
+  have hhole := h.one_le_next_claimHoles_card
+  omega
+
 /-- Primary signed block-accounting normal form: drift is block length minus
 terminal capacity minus the missing claim depths. -/
 theorem endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles
@@ -2546,6 +2662,128 @@ def CanonicalLengthOneBalancedCarrySuccessor
       canonicalBlockTerminalValuation n (k + 1) = 1 ∧
         canonicalBlockClaimCount n (k + 1) = 1

+/-- A length-one successor of a saturated block has no marked claim depths. -/
+theorem CanonicalSaturatedBorderBlock.next_claimCount_eq_zero_of_length_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1) :
+    canonicalBlockClaimCount n (k + 1) = 0 := by
+  have hle := h.next_claimCount_le_length_sub_one
+  omega
+
+/-- The former length-one balanced-carry exception is empty. -/
+theorem not_canonicalLengthOneBalancedCarrySuccessor
+    (n : OddNat) (k : ℕ) :
+    ¬ CanonicalLengthOneBalancedCarrySuccessor n k := by
+  rintro ⟨hsat, hL, _, hclaim⟩
+  have hzero := hsat.next_claimCount_eq_zero_of_length_one hL
+  omega
+
+/--
+Nonvacuous length-one successor grammar: terminal valuation one, without the
+impossible carry-two claim.  This is the correct home for the residue and
+following-start arithmetic formerly stated under the empty balanced-carry
+predicate.
+-/
+def CanonicalLengthOneTerminalOneSuccessor
+    (n : OddNat) (k : ℕ) : Prop :=
+  CanonicalSaturatedBorderBlock n k ∧
+    canonicalBlockLength n (k + 1) = 1 ∧
+      canonicalBlockTerminalValuation n (k + 1) = 1
+
+/-- Terminal valuation one in a length-one successor is exactly predecessor
+odd-core residue eleven modulo sixteen. -/
+theorem canonicalLengthOneTerminalOneSuccessor_iff_residue
+    (n : OddNat) (k : ℕ) :
+    CanonicalLengthOneTerminalOneSuccessor n k ↔
+      CanonicalSaturatedBorderBlock n k ∧
+        canonicalBlockLength n (k + 1) = 1 ∧
+          canonicalBlockOddCore n k % 16 = 11 := by
+  constructor
+  · rintro ⟨hsat, hL, hv⟩
+    exact ⟨hsat, hL,
+      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv⟩
+  · rintro ⟨hsat, hL, hres⟩
+    exact ⟨hsat, hL,
+      (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).2 hres⟩
+
+namespace CanonicalLengthOneTerminalOneSuccessor
+
+/-- The successor carries no claim. -/
+theorem claimCount_eq_zero
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
+    canonicalBlockClaimCount n (k + 1) = 0 :=
+  h.1.next_claimCount_eq_zero_of_length_one h.2.1
+
+/-- The length-one terminal-one successor has drift exactly minus one. -/
+theorem successorDrift_eq_neg_one
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
+    endpointAccountingTerm n (k + 1) = -1 := by
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
+    canonicalBlockCapacityCount_eq_terminalValuation, h.claimCount_eq_zero,
+    h.2.2]
+  norm_num
+
+/-- The predecessor unit and successor drift cancel as integers. -/
+theorem predecessorDrift_add_successorDrift_eq_zero
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
+    endpointAccountingTerm n k + endpointAccountingTerm n (k + 1) = 0 := by
+  rw [h.1.2.2, h.successorDrift_eq_neg_one]
+  norm_num
+
+/-- The following block starts at the exact eighth-word `(27*u-1)/8`.
+Unlike the historical balanced-carry version, this theorem has a nonempty
+hypothesis surface. -/
+theorem followingStartState_eq
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
+    canonicalBlockStartState n (k + 2) =
+      (27 * canonicalBlockOddCore n k - 1) / 8 := by
+  rcases h with ⟨hsat, hL, hv⟩
+  have hnext := canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation
+    n (k + 1)
+  have hsucc := canonicalBlockStartState_succ_eq_nextStartState n (k + 1)
+  have hc := hsat.nextTerminalCarrier_eq_quarter_twentySeven_core_sub_one hL
+  let u := canonicalBlockOddCore n k
+  have hu16 :=
+    (hsat.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
+  have hu : u = 16 * (u / 16) + 11 := by
+    have := Nat.mod_add_div u 16
+    omega
+  rw [show k + 2 = k + 1 + 1 by omega, hsucc, hnext, hv]
+  norm_num
+  dsimp [u] at hu hu16 ⊢
+  rw [hc]
+  omega
+
+/-- The nonvacuous modulo-sixteen class has the two expected refinements
+modulo thirty-two. -/
+theorem core_mod_thirtyTwo_eq_eleven_or_twentySeven
+    {n : OddNat} {k : ℕ} (h : CanonicalLengthOneTerminalOneSuccessor n k) :
+    canonicalBlockOddCore n k % 32 = 11 ∨
+      canonicalBlockOddCore n k % 32 = 27 := by
+  have hres := (canonicalLengthOneTerminalOneSuccessor_iff_residue n k).1 h |>.2.2
+  omega
+
+end CanonicalLengthOneTerminalOneSuccessor
+
+/-- In the other length-one residue class, the successor has at least two
+units of negative drift. -/
+theorem CanonicalSaturatedBorderBlock.nextDrift_le_neg_two_of_length_one_mod16_three
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k)
+    (hL : canonicalBlockLength n (k + 1) = 1)
+    (hres : canonicalBlockOddCore n k % 16 = 3) :
+    endpointAccountingTerm n (k + 1) ≤ -2 := by
+  have hclaim := h.next_claimCount_eq_zero_of_length_one hL
+  have hvpos := one_le_canonicalBlockTerminalValuation n (k + 1)
+  have hvne : canonicalBlockTerminalValuation n (k + 1) ≠ 1 := by
+    intro hv
+    have h11 :=
+      (h.nextTerminalValuation_eq_one_iff_core_mod_sixteen_eq_eleven hL).1 hv
+    omega
+  have hv : 2 ≤ canonicalBlockTerminalValuation n (k + 1) := by omega
+  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
+    canonicalBlockCapacityCount_eq_terminalValuation, hclaim]
+  omega
+
 /-- Residue/carry presentation of the length-one balanced successor. -/
 theorem canonicalLengthOneBalancedCarrySuccessor_iff_residue_and_endpoint_carry
     (n : OddNat) (k : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean
index 94626a32..14cbd294 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentSaturatedSuccessor.lean
@@ -226,6 +226,56 @@ theorem canonicalBlockStartState_succ_eq_nextStartState
   rw [canonicalBlockStartTime_eq_universalPaymentBlockStart,
     universalPaymentBlockStart_paymentEndpointSeq_succ]

+/--
+The block following a saturated block starts with own-width carry one.
+
+This is stronger than excluding a consecutive saturated block: the exact
+length-two normal form leaves the raw word `3*y+1` strictly below the next
+binary boundary at the successor start, independently of the successor
+block's length or terminal valuation.
+-/
+theorem CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one
+    {n : OddNat} {k : ℕ} (h : CanonicalSaturatedBorderBlock n k) :
+    stateUpperCarry (canonicalBlockStartState n (k + 1)) = 1 := by
+  let u := canonicalBlockOddCore n k
+  let x := canonicalBlockStartState n k
+  let y := canonicalBlockStartState n (k + 1)
+  have hu : 0 < u := canonicalBlockOddCore_pos n k
+  have hu4 := h.oddCore_mod_four_eq_three
+  have hu3 : 3 ≤ u := by omega
+  have hx : x = 4 * u - 1 := h.startState_eq_four_mul_core_sub_one
+  have hy : y = (9 * u - 1) / 2 := by
+    dsimp [y]
+    rw [canonicalBlockStartState_succ_eq_nextStartState]
+    exact h.nextStartState_eq
+  have hdvd : 2 ∣ 9 * u - 1 := by
+    have hdvd := h.pow_length_sub_one_dvd_terminalCarrier
+    simpa [u, canonicalBlockTerminalCarrier, h.length_eq_two] using hdvd
+  have hyDouble : 2 * y = 9 * u - 1 := by
+    rw [hy]
+    have := Nat.div_mul_cancel hdvd
+    omega
+  have hraw : 3 * y + 1 < 4 * x := by omega
+  have hxpos : 0 < x := by omega
+  have hypos : 0 < y := by omega
+  have hwidth : bitWidth y = bitWidth x + 1 := by
+    simpa [x, y, canonicalBlockStartState_succ_eq_nextStartState] using
+      h.nextStart_bitWidth_eq_start_add_one
+  have hxpow := lt_pow_bitWidth hxpos
+  have hbelow : 3 * y + 1 < 2 ^ (bitWidth y + 1) := by
+    calc
+      3 * y + 1 < 4 * x := hraw
+      _ < 4 * 2 ^ bitWidth x := by omega
+      _ = 2 ^ (bitWidth y + 1) := by
+        rw [hwidth]
+        simp [pow_succ]
+        ring
+  rcases stateUpperCarry_one_or_two hypos with hone | htwo
+  · exact hone
+  · have hcross :=
+      (stateUpperCarry_eq_two_iff_pow_succ_le_threeNPlusOne hypos).1 htwo
+    omega
+
 /-- A two-bit width increase forces more than a doubling of positive words. -/
 private theorem two_mul_lt_of_bitWidth_eq_add_two
     {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md
index ff76568f..1293f9fc 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-327.md
@@ -89,6 +89,14 @@ Lean proves:

 ## Genuine obstruction

+> **cp-328 correction.** This diagnosis is superseded.  The predicate
+> `CanonicalLengthOneBalancedCarrySuccessor` is empty: a saturated
+> predecessor forces own-width carry one at the successor start, which is the
+> deepest successor source coordinate.  Thus that depth is a claim hole, and
+> a length-one successor has claim count zero.  The modulo formulas remain
+> arithmetically useful, but their nonvacuous hypothesis is now
+> `CanonicalLengthOneTerminalOneSuccessor`.
+
 The `% 32 = 27` branch is not decided by arithmetic length data.  Saturation
 of the following block additionally needs its terminal valuation and claim
 count.  No existing theorem transports those claim facts from the predecessor
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-328.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-328.md
new file mode 100644
index 00000000..ecafde8e
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-328.md
@@ -0,0 +1,89 @@
+# Petal / FloatWindow implementation report - checkpoint 328
+
+## Result
+
+The revised width obstruction is proved.  The former length-one balanced
+carry exception is impossible, and the local claim grammar now has a generic
+block-core normal form.
+
+## Saturated next-start obstruction
+
+`CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one` proves that
+the next block starts with own-width carry one.  The proof uses the exact
+saturated forms
+
+```text
+x = 4*u - 1
+y = (9*u - 1)/2
+bitWidth y = bitWidth x + 1
+```
+
+and derives `3*y + 1 < 4*x`, hence the carry-two threshold cannot hold.
+
+## Deepest claim hole
+
+The general coordinate theorem
+
+```text
+canonicalPaymentSourceAtDepth n k (canonicalBlockLength n k)
+  = canonicalBlockStartTime n k
+```
+
+identifies the deepest source with the block start.  Therefore every successor
+of a saturated block misses its deepest claim depth.  Lean derives:
+
+- the successor hole carrier is nonempty;
+- successor claim count is at most `length - 1`;
+- a length-one successor has claim count zero;
+- `CanonicalLengthOneBalancedCarrySuccessor` is empty.
+
+## Nonvacuous residue grammar
+
+`CanonicalLengthOneTerminalOneSuccessor` retains saturation, successor length
+one, and terminal valuation one, but drops the impossible claim.  It is
+equivalent to predecessor odd-core residue `11 mod 16`.  On this surface Lean
+proves:
+
+- successor claim count is zero;
+- successor drift is `-1`;
+- predecessor and successor drift sum to zero;
+- the following start is `(27*u - 1)/8`;
+- the residue refines to `11` or `27 mod 32`.
+
+For the alternate length-one residue `3 mod 16`, successor drift is at most
+`-2`.
+
+## Generic claim-profile API
+
+For every valid depth `1 <= d <= L`, Lean now proves
+
+```text
+iterateT (canonicalPaymentSourceAtDepth n k d) n + 1
+  = 2^d * 3^(L-d) * u.
+```
+
+Consequently membership in `canonicalPaymentClaimDepths` is equivalent to
+carry two at the exact core word
+
+```text
+2^d * 3^(L-d) * u - 1.
+```
+
+This removes the need for residue-specific claim transport inside one block.
+
+## First genuine obstruction
+
+The local arithmetic obstruction did not survive formalization.  The remaining
+boundary is global resource ownership.  Existing width and carry APIs do not
+provide a finite initial-root carrier together with subtree assignment,
+temporal ownership, and a proved nonreuse or uniform multiplicity bound.
+
+The abstract local embeddings therefore cannot yet be summed globally without
+risk of charging the same upper-boundary resource multiple times.  A future
+conditional interface may state that such ownership data imply a finite total
+demand bound, but existence of that data must not be asserted.
+
+## Verification
+
+The focused modules build without `sorry` or heartbeat overrides.  Final
+top-level gates are recorded in the completion response for this checkpoint.
````
`````
