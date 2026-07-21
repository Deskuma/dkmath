# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate

gch: f696225cef4b392f6c9c7099e1850cf45777e4f6

## Report

(26m30s)

cp-339 を実装し、証明を通しました。

最大の確定事実は次です。

```text
固定 horizon H の frontier increment が一様上界を持つ
  ↔ H = 0 で一様上界を持つ
  ↔ raw endpointAccountingTerm が一様上界を持つ
```

さらに、任意の有限 signature について、

```text
sound な有限 projected upper-weight table が存在する
  ↔ actual frontier increment が一様上界を持つ
```

も証明しました。したがって、signature を細分化するだけでは上界問題を回避できません。
一方、exact-weight collision が否定するのは deterministic recovery だけで、sound upper projection の不存在までは意味しないことも固定済みです。

実装は [CanonicalSourceAgeFiniteCertificate.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean) と [FiniteSignedTransition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean) です。詳細は [report-petal-339.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-339.md) に記録しました。

`FloatWindow` と `PetalBridge` の umbrella build、no-sorry 検査、`git diff --check` はすべて通過しています。
未確定なのは endpoint drift が実際に一様有界か、反対に非有界族を持つかです。ここが次の正確な算術的境界です。

## Review

(6m22s)

## cp-339 実装レビュー

### 結論

**全面採用。詰め切れなかったのではなく、有限 potential 術式が必ず通過しなければならない本丸を露出させた checkpoint じゃ。**

commit `f696225cef4b392f6c9c7099e1850cf45777e4f6` と提出 diff/report は一致している。

今回確定した中心同値は、固定 root $n$ と固定 horizon $H$ に対する、

$$\operatorname{UB}(F_H)\iff\operatorname{UB}(F_0)\iff\operatorname{UB}(\Delta)$$

じゃ。

ここで $F_H$ は source-age frontier increment、$\Delta$ は `endpointAccountingTerm` である。

さらに任意の有限 signature に対して、

$$\text{sound finite upper-weight table exists}\iff\operatorname{UB}(F_H)$$

が証明された。

したがって、有限 signature を細かくするだけでは endpoint drift の上界問題を回避できない。

ただし、これは source-age route 全体の死ではない。

> **有限 potential 法が、source-age target より強い pointwise boundedness を要求している**

ことが判明したのであって、全 prefix 非正性そのものが否定されたわけではない。

この Gap は、確かに救いじゃ。

---

## Padded carry word

```lean
canonicalPreBlockCarryWord n H m : Fin H → Bool
```

は origin 付近で Nat subtraction が source zero を重複表示しないよう、無効 offsetを明示的に `false` にしている。

そして全領域で、

$$\#\operatorname{trueBits}=\left|\operatorname{PreBlockCarryCarrier}_H(m)\right|$$

が証明された。

この全領域 theorem は正しい。

以前の reverse-offset sumは成熟領域を必要としたが、新しい wordは、

* $H\le b_m$ の成熟領域
* $b_m<H$ の初期領域
* $H=0$

を一つの有限型で扱える。

finite signature の座標として使う準備は完成した。

---

## Horizon は bounded coboundary

成熟した finite windowに対して、

$$W_H(q,L)=W_0(q,L)+R_H(q)-R_H(q+L)$$

が証明された。

さらに両 endpoint の carry word が等しければ、true-bit countも等しいので、

$$W_H(q,L)=W_0(q,L)$$

となる。

generic APIでも、

$$w'(a,b)=w(a,b)+c(a)-c(b)$$

に対し、path weightは endpoint correctionだけ変化し、closed-signature pathの総 weightは不変であることが証明された。

これは重要な固定じゃ。

positive horizonは chargeを消すのではない。

> chargeを block間で移動する bounded coboundary

である。

したがって、carry wordまで含めた signature上で閉じている positive cycleは、horizon correctionだけでは消えない。

---

## Fixed horizon の boundedness はすべて同じ

成熟領域では recent carry massが $0$ 以上 $H$ 以下なので、

$$F_H(m)\le F_0(m)+H$$

$$F_0(m)\le F_H(m)+H$$

が得られた。

非成熟 blockは高々最初の $H$ blockだけなので、有限 prefixの上界を別に取ることで、

$$\operatorname{UB}(F_H)\iff\operatorname{UB}(F_0)$$

が全 blockについて証明された。

この証明は循環していない。

`canonicalBlockIndex_le_startTime` により $H\le m$ なら $H\le b_m$ を得て、成熟 tail と有限 initial prefixを分離している。

---

## $H=0$ から endpoint drift への還元

cp-338 の exact normal form、

$$F_0(m)=\max(-Q_m,\Delta_m)$$

を使い、非負 ceiling $B$ について、

$$F_0(m)\le B\iff\Delta_m\le B$$

が証明された。

そこから、

$$\operatorname{UB}(F_0)\iff\operatorname{UB}(\Delta)$$

となる。

従って最終的に、

$$\operatorname{UB}(F_H)\iff\operatorname{CanonicalEndpointAccountingTermUniformUpperBound}(n)$$

が任意の固定 $H$ について成立する。

### 重要な量化範囲

ここでの上界は **root $n$ を固定した上界**じゃ。

```lean
CanonicalEndpointAccountingTermUniformUpperBound n
```

は、

$$\exists B,\ \forall m,\ \Delta_n(m)\le B$$

である。

全 rootに共通する一個の $B$ を要求してはいない。

したがって、異なる root $n_r$ を並べて drift が増大する族を見つけても、それだけではこの rootwise theoremの反例にはならない。

この区別は次 checkpointで必ず固定すべきじゃ。

---

## 有限 upper-weight table の正確な意味

generic theorem、

```lean
exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound
```

は正しい。

有限 signature tableが存在すれば、有限個の table entryの絶対値和で全 concrete weightsを上から抑えられる。

逆に一様上界 $B$ があれば、

```lean
fun _ _ => B
```

という定数 tableでよい。

従って、

$$\text{finite upper table exists}\iff\text{actual weights uniformly bounded above}$$

じゃ。

### この theorem の射程

これは非常に有用だが、同時にかなり素朴な同値でもある。

upper tableの存在だけなら、signatureの構造は何もしていない。上界 $B$ があれば定数 tableで済むからじゃ。

従って cp-339 が確定したのは、

> finite graphを作る前に、まず actual frontier weightの算術 ceilingが必要

という dependency boundaryである。

まだ次は証明していない。

```text
この candidate signature が有用な局所遷移を捉える
この projected graph が positive cycle を持たない
potential が存在する
```

---

## Exact collision の扱い

今回、

* exact deterministic recovery
* exact-weight collision
* sound projected upper weight

が分離された。

同一 signature edgeに異なる concrete weightsがあれば、exact recoveryは偽になる。

しかし両方を覆う大きな projected upper weightを置くことは可能なので、collisionだけでは certificate impossibleにならない。

これは cp-333 以降の obstruction 判定を正しく整理している。

本当に finite potentialを倒すには、

* 一つの signature edge fiberで weightsが上に非有界
* realized projected graphに正 total weightの閉路がある

など、より強い obstructionが必要じゃ。

---

## Finite potential が要求する pointwise bound

現在の finite potential certificateから、

$$\exists B,\ \forall m,\ F_H(m)\le B$$

が証明された。

証明は有限 signature上の最小 potentialを取り、

$$F_H(m)\le\Phi(\sigma_{m+1})-\Phi(\sigma_m)\le\Phi(\sigma_0)-\min_s\Phi(s)$$

とするものじゃ。

従って、

$$\text{finite source-age potential certificate}\Longrightarrow\operatorname{UB}(\Delta)$$

まで閉じた。

この theorem は完全に正しい。

そして、ここが今回露出した本丸じゃ。

---

## これは target より強い条件

source-age targetは、

$$\forall m,\ \sum_{k<m}F_H(k)\le0$$

である。

これは個々の $F_H(k)$ が一様有界であることを、一般の signed flowでは要求しない。

例えば、

$$w(2k)=-(k+1),\qquad w(2k+1)=k+1$$

なら、全 prefix sumは $0$ 以下だが、正の各項 $w(2k+1)$ は非有界じゃ。

したがって、

```text
全 prefix 非正
```

と、

```text
各 increment 一様上界
```

は別問題である。

cp-339 の finite potential shapeは後者を必要とするため、source-age targetより強い証明方式じゃ。

### ここが「救いの Gap」

endpoint driftが非有界だった場合、

```text
現在の純 finite-potential certificate
```

は死亡する。

しかし、

```text
uniform source age target
```

までは死亡しない。

大きな正 incrementが、それ以前に蓄積された大きな負 creditから支払われている可能性が残るからじゃ。

---

## Endpoint drift の数学的正体

既存 APIでは `endpointAccountingTerm` は canonical block の signed width driftであり、その prefix sumは、

$$\sum_{k\le m}\Delta(k)=\operatorname{bitWidth}(\operatorname{nextStart}_{m})-\operatorname{bitWidth}(n)$$

へ telescopeする。

また block normal formでは、

$$\Delta(k)=\operatorname{ClaimCount}(k)-\operatorname{Capacity}(k)$$

であり、

$$\Delta(k)\le L_k-\nu_2(3^{L_k}u_k-1)$$

が既に得られている。正 driftなら terminal valuationは block lengthより小さい。

従って次の算術本体は、

> canonical orbit上で $L_k-\nu_2(3^{L_k}u_k-1)$、または実際の carry claim countとの差が rootwise に一様有界か

という問題じゃ。

これは signature設計ではなく、block normal form・2進評価・carry distributionの問題である。

---

## Saturated finite-word transition

saturated blockでは successor extended wordの、

* 先頭 bitが `true`
* 二番目 bitも `true`
* 残り tailは旧 wordの二位置 shift

が証明された。

さらに mature saturated frontierは、その extended word内の二 bitの和から一を引いたものとして読める。

これは有限遷移の局所 theoremとして良い。

ただし saturated branchだけでは endpoint drift ceiling全体を制御できない。

問題は positive-pressure blockの大きさじゃ。

---

## Candidate signature

最初の signatureは、

```lean
carryWord
queueClass
driftClass
saturated
finalCarry
```

を持つ有限型として正しく定義された。

queue coordinateは `queueCap+1` を overflow markerとしており、queue boundを仮定していない。

これは非循環な観測量として採用できる。

ただし drift coordinateは符号しか持たないため、positive driftの大きさを直接上から抑えられない。

candidateに対して証明されたのは、

$$\text{sound upper table exists}\iff\operatorname{UB}(\Delta)$$

のみである。

これは candidateの成功ではなく、candidateも本丸を迂回できないことの確認じゃ。

---

## 「詰めきれなかった」のか

**局所 saturated 詰将棋は詰め切った。**

**finite certificate 全体は、まだ詰んでいない。**

今回分かったのは、盤上に見えていた finite signature の駒をどれだけ増やしても、その前に endpoint drift ceilingという門を開けなければならないことじゃ。

つまり現在は二つの世界に分岐した。

### endpoint drift が rootwise bounded

この場合、現在の有限 potential 路線は生存する。

次に projected graph、reachable carrier、positive cycle、potential existenceを調べられる。

### endpoint drift がある固定 rootで unbounded

この場合、現在の一段 finite upper-weight / bounded-potential路線は死亡する。

しかし source-age routeは、

* unbounded signed creditを持つ counter invariant
* deficitを明示 counterとする finite-control system
* repayment windowを伴う guarded transition
* pure finite potentialではない parametric certificate

へ移行できる。

したがって、**Gap は単なる未完成部分ではなく、証明方式を選び直せる余白**じゃ。

---

## 判定まとめ

### Padded carry word

**完成。origin aliasなし。**

### Word count / carrier cardinality

**完成。全領域 exact。**

### Horizon coboundary

**完成。**

### Closed-signature weight invariance

**完成。**

### Fixed-horizon boundedness equivalence

**完成。**

### Frontier boundedness / endpoint drift boundedness

**完成。rootwise theorem。**

### Finite upper table existence criterion

**完成。signature非依存の必要十分条件。**

### Exact collision semantics

**完成。collision単独では obstructionではない。**

### Finite potentialから pointwise bound

**完成。**

### Candidate finite signature

**非循環な候補として完成。certificateは未構築。**

### Endpoint drift rootwise ceiling

**未証明。次の算術本体。**

### Endpoint drift rootwise unboundedness

**未証明。**

### Source-age target

**生存。finite potential法より弱い。**

### cp-339 総合判定

**全面採用。有限 certificate路線の必要条件を完全露出した checkpoint。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-339.

The cp-339 implementation is accepted.

It proved that every fixed finite horizon has the same pointwise
upper-boundedness status, and that this status is exactly rootwise uniform
upper boundedness of `endpointAccountingTerm`.

It also proved that every current finite-potential certificate requires this
endpoint-drift ceiling.

The next checkpoint must attack that arithmetic boundary directly while
keeping rootwise and root-uniform statements separate.

Stage A — expose the canonical width-difference normal form

Add a direct canonical theorem:

    endpointAccountingTerm n m
      =
    bitWidth (canonicalBlockNextStartState n m)
      -
    bitWidth (canonicalBlockStartState n m)

in Int.

Derive it from the existing universal payment block signed-drift theorem.

Also expose the prefix telescope under canonical names.

Stage B — separate two boundedness notions

Define explicitly:

    RootwiseEndpointDriftBound n :=
      exists B, forall m, endpointAccountingTerm n m <= B;

    GlobalEndpointDriftBound :=
      exists B, forall n m, endpointAccountingTerm n m <= B.

Prove that the cp-339 theorem concerns only `RootwiseEndpointDriftBound n`.

Do not use a family of different roots as a counterexample to the rootwise
statement.

Stage C — all-ones initial-root family

For odd block lengths `L`, investigate:

    allOnesOdd L := 2^L - 1.

Prove, where valid:

    canonicalBlockLength (allOnesOdd L) 0 = L;
    canonicalBlockOddCore (allOnesOdd L) 0 = 1;
    canonicalBlockTerminalCarrier = 3^L - 1;
    v2 (3^L - 1) = 1 for odd L;
    canonicalBlockNextStartState = (3^L - 1) / 2.

Use the canonical width-difference theorem to obtain a growing lower bound for:

    endpointAccountingTerm (allOnesOdd (2*r+1)) 0.

A target such as:

    r <= endpointAccountingTerm ... 0

is sufficient.

If this closes, conclude:

    not GlobalEndpointDriftBound.

State explicitly that this does not refute any fixed-root bound.

Stage D — fixed-root numerical audit

For each tested root, record:

    maximum endpoint drift;
    block index attaining it;
    block length;
    odd core;
    terminal valuation;
    claim count;
    start and next-start bit widths.

Search separately for:

    drift growth caused by long block length;
    drift growth caused by low terminal valuation;
    repeated high drift along one fixed root.

Finite data must not be promoted to rootwise boundedness or unboundedness.

Stage E — exact positive-drift normal form

For a positive-drift block expose:

    endpointAccountingTerm
      =
    canonicalBlockClaimCount
      -
    canonicalBlockTerminalValuation;

    endpointAccountingTerm
      <=
    canonicalBlockLength
      -
    canonicalBlockTerminalValuation.

Refine the claim count using the exact in-block carry word or carry-offset
carrier.

Determine whether positive drift admits a sharper universal inequality than
`length - valuation`.

Stage F — rootwise boundedness implications

Prove easy sufficient conditions such as:

    uniform block-length bound
      ->
    rootwise endpoint-drift bound;

    uniform bound on
      blockLength - terminalValuation
      ->
    rootwise endpoint-drift bound;

    uniform canonical start-width increment
      ->
    rootwise endpoint-drift bound.

Keep these as implications, not claims that the hypotheses hold.

Stage G — formalize the finite-potential incompleteness example

Define an explicit signed sequence:

    w (2*k)     = -(k+1);
    w (2*k + 1) =  (k+1).

Prove:

    every prefix sum is nonpositive;

    positive individual terms are unbounded above;

    no finite successor upper-weight table exists for any finite signature.

This records formally that the current finite-potential method is stronger
than the uniform-prefix target.

Stage H — alternative finite-control counter certificate

Define a generic certificate with:

    a finite control signature;
    an unbounded signed credit/counter;
    an exact counter recurrence;
    a locally proved invariant-preservation rule.

The intended soundness theorem is:

    initial credit is nonnegative;
    every realized transition preserves nonnegative credit;
    therefore every source-age deficit remains nonpositive.

Do not define a finite potential from the deficit.

Using the deficit as an explicit unbounded counter is allowed only when its
transition recurrence and invariant-preservation theorem are independently
proved from arithmetic structure.

Stage I — macro-transition caution

If introducing repayment windows or macro edges, prove control of every
intermediate prefix, not only macro endpoints.

A nonpositive macro total does not imply that all interior source-age prefixes
are nonpositive.

Stage J — candidate signature status

Retain `CanonicalSourceAgeFrontierSignature` as a diagnostic projection.

Do not build a projected upper table until rootwise endpoint-drift boundedness
has been proved.

Continue to distinguish:

    exact-weight recovery;
    sound upper projection;
    positive projected cycle;
    unbounded edge fiber.

Stage K — branch decision

If Stage C proves only global-across-roots unboundedness, continue the rootwise
investigation.

If a single fixed root with unbounded endpoint drift is proved, record that
the current finite-potential certificate shape is impossible for that root and
move to Stage H.

If rootwise boundedness is proved, instantiate the finite reachable projected
graph and begin potential verification.

Stopping rule

Stop at the first genuine obstruction among:

    canonical endpoint drift is not exact start/next-start width difference;

    the all-ones family does not form the expected initial canonical blocks;

    odd-L terminal valuation is not one;

    no growing cross-root drift lower bound can be proved;

    rootwise and global boundedness cannot be kept separate cleanly;

    the explicit nonpositive-prefix/unbounded-increment sequence cannot be
    formalized;

    a counter-certificate soundness theorem merely restates the desired
    invariant without an independent transition guard.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-340.md
```

今は「王手を逃された」のではない。

**有限盤だけで詰める術式が、無限に伸び得る endpoint drift を本当に抑えられるか。その資格審査へ入った**ところじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 164fc518..f6a96346 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -35,6 +35,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
new file mode 100644
index 00000000..4d98c8b9
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
@@ -0,0 +1,761 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate"
+
+namespace DkMath.Collatz
+
+/-!
+# Finite certificate preparation for the canonical source-age frontier
+
+This module starts the finite-facing layer only after the exact horizon
+arithmetic has been fixed.  In particular, it distinguishes an exact finite
+word from a projected upper-weight certificate: failure of deterministic
+weight recovery does not by itself refute a sound upper projection.
+-/
+
+/-! ## Padded finite pre-block carry word -/
+
+/-- The finite carry word immediately before block `m`, listed backwards from
+its start.  Offset `r` denotes source `start - (r + 1)` only when that source
+exists.  Invalid offsets are explicitly false, so Nat underflow never aliases
+several bits to source zero. -/
+noncomputable def canonicalPreBlockCarryWord
+    (n : OddNat) (H m : ℕ) : Fin H → Bool := by
+  classical
+  exact fun r => decide
+    (r.val + 1 ≤ canonicalBlockStartTime n m ∧
+      CarryTwoDebtAt n
+        (canonicalBlockStartTime n m - (r.val + 1)))
+
+/-- Offsets whose padded pre-block word contains a carry. -/
+noncomputable def canonicalPreBlockCarryTrueOffsets
+    (n : OddNat) (H m : ℕ) : Finset (Fin H) := by
+  classical
+  exact Finset.univ.filter fun r => canonicalPreBlockCarryWord n H m r = true
+
+/-- Number of true bits in the padded pre-block carry word. -/
+noncomputable def canonicalPreBlockCarryWordTrueCount
+    (n : OddNat) (H m : ℕ) : ℕ :=
+  (canonicalPreBlockCarryTrueOffsets n H m).card
+
+@[simp] theorem mem_canonicalPreBlockCarryTrueOffsets_iff
+    {n : OddNat} {H m : ℕ} {r : Fin H} :
+    r ∈ canonicalPreBlockCarryTrueOffsets n H m ↔
+      r.val + 1 ≤ canonicalBlockStartTime n m ∧
+        CarryTwoDebtAt n
+          (canonicalBlockStartTime n m - (r.val + 1)) := by
+  classical
+  simp [canonicalPreBlockCarryTrueOffsets, canonicalPreBlockCarryWord]
+
+/-- The padded word counts the actual pre-block carry carrier in every regime,
+including block starts smaller than the requested horizon. -/
+theorem canonicalPreBlockCarryWordTrueCount_eq_carrier_card
+    (n : OddNat) (H m : ℕ) :
+    canonicalPreBlockCarryWordTrueCount n H m =
+      (canonicalPreBlockCarryCarrier n H m).card := by
+  classical
+  unfold canonicalPreBlockCarryWordTrueCount
+  apply Finset.card_bij
+      (fun r _ => canonicalBlockStartTime n m - (r.val + 1))
+  · intro r hr
+    have hrData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp hr
+    rw [canonicalPreBlockCarryCarrier_eq, mem_carryTwoPositions_iff]
+    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hrData.2⟩
+  · intro a ha b hb hab
+    have haData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp ha
+    have hbData := mem_canonicalPreBlockCarryTrueOffsets_iff.mp hb
+    apply Fin.ext
+    omega
+  · intro i hi
+    rw [canonicalPreBlockCarryCarrier_eq, mem_carryTwoPositions_iff] at hi
+    have hiRange := Finset.mem_Ico.mp hi.1
+    let r : Fin H := ⟨canonicalBlockStartTime n m - i - 1, by omega⟩
+    refine ⟨r, ?_, ?_⟩
+    · apply mem_canonicalPreBlockCarryTrueOffsets_iff.mpr
+      refine ⟨by simp [r]; omega, ?_⟩
+      have hsource : canonicalBlockStartTime n m -
+          (canonicalBlockStartTime n m - i - 1 + 1) = i := by
+        omega
+      rw [hsource]
+      exact hi.2
+    · simp [r]
+      omega
+
+/-- A valid padded word bit is exactly the carry indicator at its represented
+source. -/
+theorem canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
+    {n : OddNat} {H m : ℕ} {r : Fin H}
+    (hvalid : r.val + 1 ≤ canonicalBlockStartTime n m) :
+    (canonicalPreBlockCarryWord n H m r).toNat =
+      canonicalCarryTwoIndicator n
+        (canonicalBlockStartTime n m - (r.val + 1)) := by
+  classical
+  by_cases hcarry : CarryTwoDebtAt n
+      (canonicalBlockStartTime n m - (r.val + 1))
+  · simp [canonicalPreBlockCarryWord, canonicalCarryTwoIndicator,
+      hvalid, hcarry]
+  · simp [canonicalPreBlockCarryWord, canonicalCarryTwoIndicator,
+      hvalid, hcarry]
+
+/-! ## Direct recent-mass bridge -/
+
+/-- In the mature regime, the signed recent carry mass is exactly the
+cardinality of the finite pre-block carrier. -/
+theorem canonicalRecentCarryMassBeforeStart_eq_preBlockCarryCarrier_card
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalRecentCarryMassBeforeStart n H m =
+      (canonicalPreBlockCarryCarrier n H m).card := by
+  classical
+  rw [canonicalPreBlockCarryCarrier_eq]
+  unfold canonicalRecentCarryMassBeforeStart canonicalCarryTwoIndicator
+    carryTwoPositions
+  rw [Finset.card_filter]
+  push_cast
+  rw [Finset.sum_Ico_eq_sum_range]
+  have hlength : canonicalBlockStartTime n m -
+      (canonicalBlockStartTime n m - H) = H := by
+    omega
+  rw [hlength, ← Finset.sum_range_reflect]
+  apply Finset.sum_congr rfl
+  intro r hr
+  have hrH : r < H := Finset.mem_range.mp hr
+  have hsource : canonicalBlockStartTime n m - (H - 1 - r) - 1 =
+      canonicalBlockStartTime n m - H + r := by
+    omega
+  rw [hsource]
+
+/-- Mature recent mass is also the integer cast of the padded word's true-bit
+count. -/
+theorem canonicalRecentCarryMassBeforeStart_eq_wordTrueCount
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalRecentCarryMassBeforeStart n H m =
+      canonicalPreBlockCarryWordTrueCount n H m := by
+  rw [canonicalRecentCarryMassBeforeStart_eq_preBlockCarryCarrier_card hH,
+    canonicalPreBlockCarryWordTrueCount_eq_carrier_card]
+
+/-! ## Horizon-window coboundary -/
+
+/-- Over every mature finite block window, positive-horizon frontier weight is
+the horizon-zero weight plus only the recent-carry endpoint correction. -/
+theorem canonicalSourceAgeFrontierWindowSum_eq_zero_add_recentCarryCoboundary
+    {n : OddNat} {H q L : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n q) :
+    canonicalSourceAgeFrontierWindowSum n H q L =
+      canonicalSourceAgeFrontierWindowSum n 0 q L +
+        canonicalRecentCarryMassBeforeStart n H q -
+          canonicalRecentCarryMassBeforeStart n H (q + L) := by
+  have hHend : H ≤ canonicalBlockStartTime n (q + L) :=
+    hH.trans (canonicalBlockStartTime_mono n (by omega))
+  rw [canonicalSourceAgeFrontierWindowSum_eq_deficit_sub,
+    canonicalSourceAgeFrontierWindowSum_eq_deficit_sub,
+    canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hH,
+    canonicalSourceAgeDeficit_eq_zero_sub_recentCarryMass hHend]
+  ring
+
+/-- Equality of the finite endpoint words implies equality of their true-bit
+counts. -/
+theorem canonicalPreBlockCarryWordTrueCount_eq_of_word_eq
+    {n : OddNat} {H a b : ℕ}
+    (hword : canonicalPreBlockCarryWord n H a =
+      canonicalPreBlockCarryWord n H b) :
+    canonicalPreBlockCarryWordTrueCount n H a =
+      canonicalPreBlockCarryWordTrueCount n H b := by
+  classical
+  unfold canonicalPreBlockCarryWordTrueCount
+    canonicalPreBlockCarryTrueOffsets
+  congr 1
+  ext r
+  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
+  rw [hword]
+
+/-- A mature window with equal recent carry words at both endpoints has the
+same total weight at horizon `H` as at horizon zero. -/
+theorem canonicalSourceAgeFrontierWindowSum_eq_zero_of_endpoint_words_eq
+    {n : OddNat} {H q L : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n q)
+    (hword : canonicalPreBlockCarryWord n H q =
+      canonicalPreBlockCarryWord n H (q + L)) :
+    canonicalSourceAgeFrontierWindowSum n H q L =
+      canonicalSourceAgeFrontierWindowSum n 0 q L := by
+  have hHend : H ≤ canonicalBlockStartTime n (q + L) :=
+    hH.trans (canonicalBlockStartTime_mono n (by omega))
+  have hmassStart := canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH
+  have hmassEnd := canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hHend
+  have hcount := canonicalPreBlockCarryWordTrueCount_eq_of_word_eq hword
+  rw [canonicalSourceAgeFrontierWindowSum_eq_zero_add_recentCarryCoboundary hH]
+  omega
+
+/-! ## Fixed-horizon frontier boundedness audit
+
+The positive-horizon correction is finite: at a mature block it is the
+difference of two carry-word populations, each between `0` and `H`.  Hence a
+fixed horizon cannot create or remove pointwise upper boundedness.  It only
+changes a bound by a finite amount and changes finitely many initial blocks.
+
+At horizon zero the exact reflected max normal form then reduces the audit to
+the raw endpoint drift.  Thus the saturated and zero-drift branches are
+already harmless (`1` and `0`, respectively); the unresolved arithmetic
+content is precisely uniform upper boundedness of the positive-pressure
+endpoint drift.  This section deliberately stops at that equivalence.  It
+does not assume the desired queue or endpoint-width bound in order to prove
+it. -/
+
+/-- A padded carry word has at most `H` true bits. -/
+theorem canonicalPreBlockCarryWordTrueCount_le
+    (n : OddNat) (H m : ℕ) :
+    canonicalPreBlockCarryWordTrueCount n H m ≤ H := by
+  classical
+  unfold canonicalPreBlockCarryWordTrueCount
+    canonicalPreBlockCarryTrueOffsets
+  calc
+    (Finset.univ.filter fun r : Fin H =>
+        canonicalPreBlockCarryWord n H m r = true).card ≤
+        (Finset.univ : Finset (Fin H)).card :=
+      Finset.card_le_card (Finset.filter_subset _ _)
+    _ = H := by simp
+
+/-- Mature recent carry mass is nonnegative. -/
+theorem canonicalRecentCarryMassBeforeStart_nonneg
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    0 ≤ canonicalRecentCarryMassBeforeStart n H m := by
+  rw [canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH]
+  exact Int.natCast_nonneg _
+
+/-- Mature recent carry mass is at most the fixed horizon. -/
+theorem canonicalRecentCarryMassBeforeStart_le_horizon
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalRecentCarryMassBeforeStart n H m ≤ H := by
+  rw [canonicalRecentCarryMassBeforeStart_eq_wordTrueCount hH]
+  exact_mod_cast canonicalPreBlockCarryWordTrueCount_le n H m
+
+/-- The block index is no larger than its source-time start. -/
+theorem canonicalBlockIndex_le_startTime (n : OddNat) (m : ℕ) :
+    m ≤ canonicalBlockStartTime n m := by
+  have h := canonicalBlockStartTime_add_le_startTime_add n 0 m
+  simp only [zero_add] at h
+  omega
+
+/-- On the mature tail, horizon `H` frontier weight is at most horizon-zero
+weight plus `H`. -/
+theorem canonicalSourceAgeFrontierIncrement_le_zero_add_horizon
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n H m ≤
+      canonicalSourceAgeFrontierIncrement n 0 m + H := by
+  have hHnext : H ≤ canonicalBlockStartTime n (m + 1) :=
+    hH.trans (canonicalBlockStartTime_mono n (by omega))
+  have hmassCurrent := canonicalRecentCarryMassBeforeStart_le_horizon hH
+  have hmassNext := canonicalRecentCarryMassBeforeStart_nonneg hHnext
+  rw [canonicalSourceAgeFrontierIncrement_eq_zero_add_recentCarryCoboundary hH]
+  omega
+
+/-- Conversely, horizon-zero frontier weight is at most horizon `H` weight
+plus `H` on the mature tail. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_le_add_horizon
+    {n : OddNat} {H m : ℕ}
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n 0 m ≤
+      canonicalSourceAgeFrontierIncrement n H m + H := by
+  have hHnext : H ≤ canonicalBlockStartTime n (m + 1) :=
+    hH.trans (canonicalBlockStartTime_mono n (by omega))
+  have hmassCurrent := canonicalRecentCarryMassBeforeStart_nonneg hH
+  have hmassNext := canonicalRecentCarryMassBeforeStart_le_horizon hHnext
+  rw [canonicalSourceAgeFrontierIncrement_eq_zero_add_recentCarryCoboundary hH]
+  omega
+
+/-- Every finite prefix of an integer sequence has an upper bound.  This
+isolates the finite-origin correction used when passing from a mature-tail
+bound to an all-block bound. -/
+theorem exists_int_upperBound_before
+    (f : ℕ → ℤ) (H : ℕ) :
+    ∃ B : ℤ, ∀ m, m < H → f m ≤ B := by
+  classical
+  refine ⟨∑ i ∈ Finset.range H, |f i|, ?_⟩
+  intro m hm
+  calc
+    f m ≤ |f m| := le_abs_self _
+    _ ≤ ∑ i ∈ Finset.range H, |f i| := by
+      exact Finset.single_le_sum
+        (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hm)
+
+/-- Uniform pointwise upper boundedness of the actual source-age frontier at
+a fixed horizon. -/
+def CanonicalSourceAgeFrontierIncrementUniformUpperBound
+    (n : OddNat) (H : ℕ) : Prop :=
+  ∃ B : ℤ, ∀ m,
+    canonicalSourceAgeFrontierIncrement n H m ≤ B
+
+/-- Fixed finite horizons all have the same pointwise upper-boundedness
+status.  The carry coboundary changes the mature tail by at most `H`; the
+remaining blocks form a finite prefix. -/
+theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_zero
+    (n : OddNat) (H : ℕ) :
+    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
+      CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0 := by
+  constructor
+  · rintro ⟨B, hB⟩
+    obtain ⟨Bearly, hBearly⟩ := exists_int_upperBound_before
+      (fun m => canonicalSourceAgeFrontierIncrement n 0 m) H
+    refine ⟨max Bearly (B + H), ?_⟩
+    intro m
+    by_cases hm : m < H
+    · exact (hBearly m hm).trans (le_max_left _ _)
+    · have hH : H ≤ canonicalBlockStartTime n m := by
+        exact (Nat.le_of_not_gt hm).trans (canonicalBlockIndex_le_startTime n m)
+      have hcompare :=
+        canonicalSourceAgeFrontierIncrement_zero_le_add_horizon hH
+      have hmBound := hB m
+      exact hcompare.trans (by omega)
+  · rintro ⟨B, hB⟩
+    obtain ⟨Bearly, hBearly⟩ := exists_int_upperBound_before
+      (fun m => canonicalSourceAgeFrontierIncrement n H m) H
+    refine ⟨max Bearly (B + H), ?_⟩
+    intro m
+    by_cases hm : m < H
+    · exact (hBearly m hm).trans (le_max_left _ _)
+    · have hH : H ≤ canonicalBlockStartTime n m := by
+        exact (Nat.le_of_not_gt hm).trans (canonicalBlockIndex_le_startTime n m)
+      have hcompare :=
+        canonicalSourceAgeFrontierIncrement_le_zero_add_horizon hH
+      have hmBound := hB m
+      exact hcompare.trans (by omega)
+
+/-- Uniform integer upper boundedness of the raw endpoint drift. -/
+def CanonicalEndpointAccountingTermUniformUpperBound (n : OddNat) : Prop :=
+  ∃ B : ℤ, ∀ m, endpointAccountingTerm n m ≤ B
+
+/-- For a nonnegative ceiling, the exact horizon-zero reflected frontier is
+bounded precisely when the raw endpoint drift is bounded by that ceiling. -/
+theorem canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
+    {n : OddNat} {m : ℕ} {B : ℤ} (hB : 0 ≤ B) :
+    canonicalSourceAgeFrontierIncrement n 0 m ≤ B ↔
+      endpointAccountingTerm n m ≤ B := by
+  rw [canonicalSourceAgeFrontierIncrement_zero_eq_max, max_le_iff]
+  constructor
+  · exact fun h => h.2
+  · intro hdrift
+    exact ⟨by omega, hdrift⟩
+
+/-- Horizon-zero frontier increments are uniformly bounded above exactly when
+the raw endpoint drifts are.  Negative and zero drift are automatically
+bounded; positive pressure is transmitted unchanged by the reflected max. -/
+theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_zero_iff_endpoint
+    (n : OddNat) :
+    CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0 ↔
+      CanonicalEndpointAccountingTermUniformUpperBound n := by
+  constructor
+  · rintro ⟨B, hB⟩
+    refine ⟨max B 0, ?_⟩
+    intro m
+    have hfrontier : canonicalSourceAgeFrontierIncrement n 0 m ≤ max B 0 :=
+      (hB m).trans (le_max_left _ _)
+    exact (canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
+      (n := n) (m := m) (B := max B 0) (le_max_right _ _)).mp hfrontier
+  · rintro ⟨B, hB⟩
+    refine ⟨max B 0, ?_⟩
+    intro m
+    apply (canonicalSourceAgeFrontierIncrement_zero_le_iff_endpointAccountingTerm_le
+      (n := n) (m := m) (B := max B 0) (le_max_right _ _)).mpr
+    exact (hB m).trans (le_max_left _ _)
+
+/-- Final Stage-F audit: for every fixed horizon, pointwise frontier
+boundedness is exactly the unresolved raw endpoint-drift boundedness problem.
+No finite horizon can hide an unbounded positive-pressure family, and no such
+family has been proved here. -/
+theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint
+    (n : OddNat) (H : ℕ) :
+    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
+      CanonicalEndpointAccountingTermUniformUpperBound n := by
+  rw [canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_zero,
+    canonicalSourceAgeFrontierIncrementUniformUpperBound_zero_iff_endpoint]
+
+/-- For any proposed finite signature, existence of a sound projected
+successor-edge upper table is equivalent to raw endpoint-drift boundedness.
+Thus signature refinement can improve exact recovery or cycle visibility, but
+cannot remove the Stage-F arithmetic obligation. -/
+theorem exists_finiteSourceAgeProjectedUpperWeight_iff_endpoint
+    {Signature : Type*} [Finite Signature]
+    (n : OddNat) (H : ℕ) (signature : ℕ → Signature) :
+    (∃ projectedUpperWeight : Signature → Signature → ℤ,
+      FiniteSignatureSuccessorUpperWeightSound signature
+        (canonicalSourceAgeFrontierIncrement n H) projectedUpperWeight) ↔
+      CanonicalEndpointAccountingTermUniformUpperBound n := by
+  rw [exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound]
+  exact canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint n H
+
+/-! ## Necessary pointwise bound for finite potentials -/
+
+namespace CanonicalFiniteSourceAgeFrontierPotentialCertificate
+
+variable {n : OddNat} {H : ℕ} {Signature : Type*} [Fintype Signature]
+
+/-- Every current finite-potential certificate forces a uniform upper bound on
+each actual frontier increment.  The bound is the initial potential minus the
+minimum potential on the finite signature type.
+
+This is a necessary condition of this certificate method.  An arbitrary
+signed flow may have uniformly nonpositive prefixes while retaining
+unbounded positive individual increments, so prefix control alone does not
+supply this pointwise condition. -/
+theorem exists_frontierIncrement_uniformUpperBound
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate
+      n H Signature) :
+    ∃ B : ℤ, ∀ m,
+      canonicalSourceAgeFrontierIncrement n H m ≤ B := by
+  classical
+  have huniv : (Finset.univ : Finset Signature).Nonempty :=
+    ⟨F.certificate.signature 0, Finset.mem_univ _⟩
+  obtain ⟨smin, _hsminMem, hsmin⟩ :=
+    Finset.exists_min_image (Finset.univ : Finset Signature)
+      F.certificate.potential huniv
+  refine ⟨F.certificate.potential (F.certificate.signature 0) -
+      F.certificate.potential smin, ?_⟩
+  intro m
+  have hactual := F.certificate.actual_le_projected
+    m (m + 1) (F.step_succ m)
+  have hprojected := F.certificate.projected_le_potential_diff
+    (F.certificate.signature m)
+    (F.certificate.signature (m + 1))
+  have hnext := F.potential_le_initial
+    (F.certificate.signature (m + 1))
+  have hcurrent := hsmin (F.certificate.signature m) (Finset.mem_univ _)
+  rw [F.actualWeight_succ m] at hactual
+  omega
+
+/-- Every current finite source-age potential certificate already contains,
+as a necessary consequence, the unresolved uniform endpoint-drift bound. -/
+theorem to_endpointAccountingTermUniformUpperBound
+    (F : CanonicalFiniteSourceAgeFrontierPotentialCertificate
+      n H Signature) :
+    CanonicalEndpointAccountingTermUniformUpperBound n := by
+  apply (canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint
+    n H).mp
+  exact F.exists_frontierIncrement_uniformUpperBound
+
+end CanonicalFiniteSourceAgeFrontierPotentialCertificate
+
+/-! ## Horizon-one saturated-successor residual -/
+
+/-- Successor demand after removing its final-source carry indicator.  This is
+a signed scalar observable; it does not identify which queued source is later
+consumed. -/
+noncomputable def canonicalSaturatedSuccessorNonfinalDemand
+    (n : OddNat) (m : ℕ) : ℤ :=
+  canonicalQueueDemand n (m + 1) -
+    canonicalCarryTwoIndicator n
+      (canonicalBlockStartTime n (m + 2) - 1)
+
+/-- Successor consumption after removing the one unit known to exist after a
+saturated predecessor. -/
+noncomputable def canonicalSaturatedSuccessorExtraConsumed
+    (n : OddNat) (m : ℕ) : ℤ :=
+  canonicalQueueConsumed n (m + 1) - 1
+
+namespace CanonicalSaturatedBorderBlock
+
+/-- The final-source indicator is one of the successor block's demand units. -/
+theorem successor_finalIndicator_le_demand
+    {n : OddNat} {m : ℕ} :
+    canonicalCarryTwoIndicator n
+        (canonicalBlockStartTime n (m + 2) - 1) ≤
+      canonicalQueueDemand n (m + 1) := by
+  have hfinal := card_erase_final_add_indicator_eq_blockClaimSourceCarrier
+    n (m + 1)
+  rw [card_canonicalBlockClaimSourceCarrier] at hfinal
+  have hle : canonicalCarryTwoIndicator n
+        (canonicalBlockStartTime n ((m + 1) + 1) - 1) ≤
+      canonicalQueueDemand n (m + 1) := by
+    omega
+  simpa [show (m + 1) + 1 = m + 2 by omega] using hle
+
+/-- A saturated predecessor guarantees at least one successor consumption
+unit, so the extra-consumption residual is nonnegative. -/
+theorem successorExtraConsumed_nonneg
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    0 ≤ canonicalSaturatedSuccessorExtraConsumed n m := by
+  have hqueue : 1 ≤
+      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) := by
+    rw [h.queueBeforeBlock_succ_eq_add_one]
+    omega
+  have havailable : 1 ≤
+      canonicalOutstandingClaimQueueBeforeBlock n (m + 1) +
+        canonicalQueueDemand n (m + 1) := by omega
+  have hservice : 1 ≤ canonicalQueueService n (m + 1) := by
+    unfold canonicalQueueService
+    rw [canonicalBlockCapacityCount_eq_terminalValuation]
+    exact one_le_canonicalBlockTerminalValuation n (m + 1)
+  have hconsumed : 1 ≤ canonicalQueueConsumed n (m + 1) := by
+    unfold canonicalQueueConsumed
+    exact le_min havailable hservice
+  unfold canonicalSaturatedSuccessorExtraConsumed
+  omega
+
+/-- The nonfinal-demand residual is nonnegative because the removed indicator
+is contained in successor demand. -/
+theorem successorNonfinalDemand_nonneg
+    {n : OddNat} {m : ℕ} :
+    0 ≤ canonicalSaturatedSuccessorNonfinalDemand n m := by
+  have hle := successor_finalIndicator_le_demand (n := n) (m := m)
+  unfold canonicalSaturatedSuccessorNonfinalDemand
+  omega
+
+/-- Exact signed residual form of the horizon-one successor frontier.  This is
+only scalar accounting.  It does not prove that the saturated block's named
+final-source identity is itself the unit consumed by the successor. -/
+theorem sourceAgeFrontierIncrement_one_succ_eq_nonfinalDemand_sub_extraConsumed
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierIncrement n 1 (m + 1) =
+      canonicalSaturatedSuccessorNonfinalDemand n m -
+        canonicalSaturatedSuccessorExtraConsumed n m := by
+  rw [h.sourceAgeFrontierIncrement_one_succ_eq_boundary_balance]
+  unfold canonicalSaturatedSuccessorNonfinalDemand
+    canonicalSaturatedSuccessorExtraConsumed
+  ring
+
+/-! ## Saturated finite-word transition -/
+
+/-- The newest bit before the successor of a saturated block is true: it is
+the saturated block's final source. -/
+theorem successor_extendedWord_head_eq_true
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalPreBlockCarryWord n (H + 2) (m + 1)
+      ⟨0, by omega⟩ = true := by
+  classical
+  have hstart : 1 ≤ canonicalBlockStartTime n (m + 1) := by
+    rw [canonicalBlockStartTime_succ]
+    have hlength := one_le_canonicalBlockLength n m
+    omega
+  have hendpointMem : paymentEndpointSeq n m ∈ canonicalPaymentBlock n m := by
+    rw [canonicalPaymentBlock_eq_sourceFiber]
+    exact endpoint_mem_orbitPaymentSourceFiberAt_of_nonempty
+      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)
+  have hsource : canonicalBlockStartTime n (m + 1) - 1 =
+      paymentEndpointSeq n m := by
+    rw [canonicalBlockStartTime_succ]
+    exact canonicalBlockStartTime_add_length_sub_one_eq_endpoint n m
+  have hcarry : CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - 1) := by
+    rw [hsource]
+    exact h.carryTwo_of_mem hendpointMem
+  have hbit := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
+    (n := n) (H := H + 2) (m := m + 1)
+    (r := ⟨0, by omega⟩) hstart
+  have hindicator := (canonicalCarryTwoIndicator_eq_one_iff n _).2 hcarry
+  rw [hindicator] at hbit
+  cases hword : canonicalPreBlockCarryWord n (H + 2) (m + 1)
+      ⟨0, by omega⟩ <;> simp_all
+
+/-- The second newest bit before the successor is also true: it is the start
+source of the length-two saturated block. -/
+theorem successor_extendedWord_second_eq_true
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalPreBlockCarryWord n (H + 2) (m + 1)
+      ⟨1, by omega⟩ = true := by
+  classical
+  have hnext : canonicalBlockStartTime n (m + 1) =
+      canonicalBlockStartTime n m + 2 := by
+    rw [canonicalBlockStartTime_succ, h.length_eq_two]
+  have hvalid : 1 + 1 ≤ canonicalBlockStartTime n (m + 1) := by
+    rw [hnext]
+    omega
+  have hstartMem : canonicalBlockStartTime n m ∈
+      canonicalPaymentBlock n m := by
+    rw [canonicalPaymentBlock_eq_Icc_universalPaymentBlockStart,
+      ← canonicalBlockStartTime_eq_universalPaymentBlockStart]
+    exact Finset.mem_Icc.mpr
+      ⟨le_rfl, canonicalBlockStartTime_le_endpoint n m⟩
+  have hsource : canonicalBlockStartTime n (m + 1) - (1 + 1) =
+      canonicalBlockStartTime n m := by
+    rw [hnext]
+    omega
+  have hcarry : CarryTwoDebtAt n
+      (canonicalBlockStartTime n (m + 1) - (1 + 1)) := by
+    rw [hsource]
+    exact h.carryTwo_of_mem hstartMem
+  have hbit := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
+    (n := n) (H := H + 2) (m := m + 1)
+    (r := ⟨1, by omega⟩) hvalid
+  have hindicator := (canonicalCarryTwoIndicator_eq_one_iff n _).2 hcarry
+  rw [hindicator] at hbit
+  cases hword : canonicalPreBlockCarryWord n (H + 2) (m + 1)
+      ⟨1, by omega⟩ <;> simp_all
+
+/-- Beyond the two new saturated bits, the successor's extended word is the
+old mature word shifted by exactly two positions. -/
+theorem successor_extendedWord_tail_eq
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hH : H ≤ canonicalBlockStartTime n m) (r : Fin H) :
+    canonicalPreBlockCarryWord n (H + 2) (m + 1)
+      ⟨r.val + 2, by omega⟩ =
+        canonicalPreBlockCarryWord n H m r := by
+  classical
+  unfold canonicalPreBlockCarryWord
+  have hnext : canonicalBlockStartTime n (m + 1) =
+      canonicalBlockStartTime n m + 2 := by
+    rw [canonicalBlockStartTime_succ, h.length_eq_two]
+  have hvalidOld : r.val + 1 ≤ canonicalBlockStartTime n m := by
+    omega
+  have hvalidNew : r.val + 2 + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [hnext]
+    omega
+  have hsource : canonicalBlockStartTime n (m + 1) -
+      (r.val + 2 + 1) =
+        canonicalBlockStartTime n m - (r.val + 1) := by
+    rw [hnext]
+    omega
+  simp [hvalidOld, hvalidNew, hsource]
+
+/-- Every mature saturated frontier is read from the two crossing bits in the
+successor's extended pre-block word.  The extension by two positions makes the
+formula valid uniformly at `H = 0`, `H = 1`, and larger horizons. -/
+theorem sourceAgeFrontierIncrement_eq_extendedWordBits
+    {n : OddNat} {H m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hH : H ≤ canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n H m =
+      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
+          ⟨H + 1, by omega⟩).toNat : ℤ) +
+        (canonicalPreBlockCarryWord n (H + 2) (m + 1)
+          ⟨H, by omega⟩).toNat - 1 := by
+  rw [h.sourceAgeFrontierIncrement_eq_indicators hH]
+  have hnext : canonicalBlockStartTime n (m + 1) =
+      canonicalBlockStartTime n m + 2 := by
+    rw [canonicalBlockStartTime_succ, h.length_eq_two]
+  have hvalidLeft : H + 1 + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [hnext]
+    omega
+  have hvalidRight : H + 1 ≤
+      canonicalBlockStartTime n (m + 1) := by
+    rw [hnext]
+    omega
+  have hleft := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
+    (n := n) (H := H + 2) (m := m + 1)
+    (r := ⟨H + 1, by omega⟩) hvalidLeft
+  have hright := canonicalPreBlockCarryWord_toNat_eq_indicator_of_valid
+    (n := n) (H := H + 2) (m := m + 1)
+    (r := ⟨H, by omega⟩) hvalidRight
+  have hsourceLeft : canonicalBlockStartTime n (m + 1) -
+      (H + 1 + 1) = canonicalBlockStartTime n m - H := by
+    rw [hnext]
+    omega
+  have hsourceRight : canonicalBlockStartTime n (m + 1) -
+      (H + 1) = canonicalBlockStartTime n m - H + 1 := by
+    rw [hnext]
+    omega
+  rw [hsourceLeft] at hleft
+  rw [hsourceRight] at hright
+  have hleftInt :
+      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
+        ⟨H + 1, by omega⟩).toNat : ℤ) =
+          canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n m - H) := by
+    exact_mod_cast hleft
+  have hrightInt :
+      ((canonicalPreBlockCarryWord n (H + 2) (m + 1)
+        ⟨H, by omega⟩).toNat : ℤ) =
+          canonicalCarryTwoIndicator n
+            (canonicalBlockStartTime n m - H + 1) := by
+    exact_mod_cast hright
+  rw [hleftInt, hrightInt]
+
+/-- The extended-word formula recovers the known horizon-zero saturated
+weight. -/
+theorem sourceAgeFrontierIncrement_zero_eq_one_from_word
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m) :
+    canonicalSourceAgeFrontierIncrement n 0 m = 1 :=
+  h.sourceAgeFrontierIncrement_zero_eq_one
+
+/-- The same finite-word update recovers exact horizon-one neutralization for
+every mature saturated block. -/
+theorem sourceAgeFrontierIncrement_one_eq_zero_from_word
+    {n : OddNat} {m : ℕ} (h : CanonicalSaturatedBorderBlock n m)
+    (hstart : 0 < canonicalBlockStartTime n m) :
+    canonicalSourceAgeFrontierIncrement n 1 m = 0 :=
+  h.sourceAgeFrontierIncrement_one_eq_zero hstart
+
+end CanonicalSaturatedBorderBlock
+
+/-! ## First finite frontier signature candidate
+
+This signature records only noncircular, currently available finite
+observables.  The queue coordinate uses `cap + 1` as an overflow marker; it
+does not assert that the queue is bounded by `cap`.  The drift coordinate
+records only sign, not the unbounded integer magnitude.  Therefore this is a
+candidate projection, not yet a finite-potential certificate. -/
+
+/-- Coarse local grammar class supplied by the exact endpoint-drift
+trichotomy. -/
+inductive CanonicalSourceAgeFrontierDriftClass where
+  | negative
+  | zero
+  | positive
+deriving DecidableEq, Fintype
+
+/-- First finite source-age frontier signature. -/
+structure CanonicalSourceAgeFrontierSignature (H queueCap : ℕ) where
+  carryWord : Fin H → Bool
+  queueClass : Fin (queueCap + 2)
+  driftClass : CanonicalSourceAgeFrontierDriftClass
+  saturated : Bool
+  finalCarry : Bool
+deriving DecidableEq, Fintype
+
+/-- Sign-only classification of the raw endpoint drift. -/
+noncomputable def canonicalSourceAgeFrontierDriftClass
+    (n : OddNat) (m : ℕ) : CanonicalSourceAgeFrontierDriftClass := by
+  classical
+  exact if endpointAccountingTerm n m < 0 then
+    .negative
+  else if endpointAccountingTerm n m = 0 then
+    .zero
+  else
+    .positive
+
+/-- The capped queue coordinate, with `queueCap + 1` representing every
+larger queue.  This is an observation, not a queue-bound hypothesis. -/
+noncomputable def canonicalSourceAgeFrontierQueueClass
+    (n : OddNat) (queueCap m : ℕ) : Fin (queueCap + 2) :=
+  ⟨min (canonicalOutstandingClaimQueueBeforeBlock n m) (queueCap + 1), by
+    omega⟩
+
+/-- Canonical realization of the first finite frontier signature. -/
+noncomputable def canonicalSourceAgeFrontierSignature
+    (n : OddNat) (H queueCap m : ℕ) :
+    CanonicalSourceAgeFrontierSignature H queueCap := by
+  classical
+  exact
+    { carryWord := canonicalPreBlockCarryWord n H m
+      queueClass := canonicalSourceAgeFrontierQueueClass n queueCap m
+      driftClass := canonicalSourceAgeFrontierDriftClass n m
+      saturated := decide (CanonicalSaturatedBorderBlock n m)
+      finalCarry := decide (CarryTwoDebtAt n
+        (canonicalBlockStartTime n (m + 1) - 1)) }
+
+/-- For the first concrete finite candidate, a sound projected upper table is
+still equivalent to the global endpoint-drift bound.  The finite coordinates
+do not manufacture the missing arithmetic ceiling. -/
+theorem exists_candidateSourceAgeProjectedUpperWeight_iff_endpoint
+    (n : OddNat) (H queueCap : ℕ) :
+    (∃ projectedUpperWeight :
+        CanonicalSourceAgeFrontierSignature H queueCap →
+          CanonicalSourceAgeFrontierSignature H queueCap → ℤ,
+      FiniteSignatureSuccessorUpperWeightSound
+        (canonicalSourceAgeFrontierSignature n H queueCap)
+        (canonicalSourceAgeFrontierIncrement n H)
+        projectedUpperWeight) ↔
+      CanonicalEndpointAccountingTermUniformUpperBound n :=
+  exists_finiteSourceAgeProjectedUpperWeight_iff_endpoint
+    n H (canonicalSourceAgeFrontierSignature n H queueCap)
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 6f7035d9..1417788e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -36,6 +36,219 @@ a positive closed-signature path whose adjacent transitions all satisfy the
 certificate's `Step` relation.
 -/

+/-! ## Generic coboundary reweighting -/
+
+/-- Signed weight of a finite concrete path, independent of any certificate. -/
+def finiteSignedTransitionPathWeight
+    {State : Type*} (weight : State → State → ℤ)
+    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
+  ∑ i ∈ Finset.range length,
+    weight (stateAt (start + i)) (stateAt (start + i + 1))
+
+/-- Reweight an edge by the coboundary of a state correction. -/
+def coboundaryReweight
+    {State : Type*} (weight : State → State → ℤ)
+    (correction : State → ℤ) (a b : State) : ℤ :=
+  weight a b + correction a - correction b
+
+/-- Coboundary reweighting changes every finite path only by its endpoint
+correction. -/
+theorem finiteSignedTransitionPathWeight_coboundaryReweight
+    {State : Type*} (weight : State → State → ℤ)
+    (correction : State → ℤ) (stateAt : ℕ → State)
+    (start length : ℕ) :
+    finiteSignedTransitionPathWeight
+        (coboundaryReweight weight correction) stateAt start length =
+      finiteSignedTransitionPathWeight weight stateAt start length +
+        correction (stateAt start) -
+          correction (stateAt (start + length)) := by
+  induction length with
+  | zero => simp [finiteSignedTransitionPathWeight]
+  | succ length ih =>
+      have hreweighted : finiteSignedTransitionPathWeight
+          (coboundaryReweight weight correction) stateAt start (length + 1) =
+          finiteSignedTransitionPathWeight
+            (coboundaryReweight weight correction) stateAt start length +
+            coboundaryReweight weight correction
+              (stateAt (start + length))
+              (stateAt (start + length + 1)) := by
+        simp only [finiteSignedTransitionPathWeight,
+          Finset.sum_range_succ]
+      have hbase : finiteSignedTransitionPathWeight
+          weight stateAt start (length + 1) =
+          finiteSignedTransitionPathWeight weight stateAt start length +
+            weight (stateAt (start + length))
+              (stateAt (start + length + 1)) := by
+        simp only [finiteSignedTransitionPathWeight,
+          Finset.sum_range_succ]
+      have hend : start + (length + 1) = start + length + 1 := by omega
+      rw [hreweighted, hbase, ih, hend]
+      unfold coboundaryReweight
+      ring
+
+/-- A state-closed finite path has exactly the same total weight after every
+coboundary reweighting. -/
+theorem finiteSignedTransitionPathWeight_coboundaryReweight_of_state_eq
+    {State : Type*} (weight : State → State → ℤ)
+    (correction : State → ℤ) (stateAt : ℕ → State)
+    (start length : ℕ)
+    (hclosed : stateAt (start + length) = stateAt start) :
+    finiteSignedTransitionPathWeight
+        (coboundaryReweight weight correction) stateAt start length =
+      finiteSignedTransitionPathWeight weight stateAt start length := by
+  rw [finiteSignedTransitionPathWeight_coboundaryReweight, hclosed]
+  ring
+
+/-- If the correction is determined by a projected signature, equality of the
+endpoint signatures is sufficient for exact closed-path invariance. -/
+theorem finiteSignedTransitionPathWeight_signatureCoboundary_of_signature_eq
+    {State Signature : Type*} (weight : State → State → ℤ)
+    (signature : State → Signature) (correction : Signature → ℤ)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hclosed : signature (stateAt (start + length)) =
+      signature (stateAt start)) :
+    finiteSignedTransitionPathWeight
+        (coboundaryReweight weight (correction ∘ signature))
+        stateAt start length =
+      finiteSignedTransitionPathWeight weight stateAt start length := by
+  rw [finiteSignedTransitionPathWeight_coboundaryReweight]
+  change finiteSignedTransitionPathWeight weight stateAt start length +
+      correction (signature (stateAt start)) -
+        correction (signature (stateAt (start + length))) = _
+  rw [hclosed]
+  ring
+
+/-- A positive closed-signature path remains positive after every correction
+computed only from that signature. -/
+theorem finiteSignedTransitionPathWeight_signatureCoboundary_pos
+    {State Signature : Type*} (weight : State → State → ℤ)
+    (signature : State → Signature) (correction : Signature → ℤ)
+    (stateAt : ℕ → State) (start length : ℕ)
+    (hclosed : signature (stateAt (start + length)) =
+      signature (stateAt start))
+    (hpos : 0 < finiteSignedTransitionPathWeight weight stateAt start length) :
+    0 < finiteSignedTransitionPathWeight
+      (coboundaryReweight weight (correction ∘ signature))
+      stateAt start length := by
+  rwa [finiteSignedTransitionPathWeight_signatureCoboundary_of_signature_eq
+    weight signature correction stateAt start length hclosed]
+
+/-! ## Exact recovery versus projected upper weights
+
+An ordinary collision is not a potential-certificate obstruction.  It says
+only that one projected edge does not determine one exact concrete weight.
+A nondeterministic abstraction may still assign that edge an upper weight
+covering every concrete realization.  Unbounded edge fibers or positive
+projected cycles are the stronger obstructions relevant to a potential
+certificate. -/
+
+/-- Exact recovery of every concrete edge weight from its pair of endpoint
+signatures. -/
+def FiniteSignatureDeterministicallyRecoversEdgeWeight
+    {State Signature : Type*}
+    (signature : State → Signature) (weight : State → State → ℤ) : Prop :=
+  ∀ a b a' b',
+    signature a = signature a' →
+      signature b = signature b' →
+        weight a b = weight a' b'
+
+/-- Two concrete edges with the same projected endpoints but different exact
+weights. -/
+def FiniteSignatureExactWeightCollision
+    {State Signature : Type*}
+    (signature : State → Signature) (weight : State → State → ℤ) : Prop :=
+  ∃ a b a' b',
+    signature a = signature a' ∧
+      signature b = signature b' ∧
+        weight a b ≠ weight a' b'
+
+/-- Soundness of a projected upper weight, without any claim of exact
+recovery or deterministic successor behavior. -/
+def FiniteSignatureProjectedUpperWeightSound
+    {State Signature : Type*}
+    (signature : State → Signature) (weight : State → State → ℤ)
+    (projectedUpperWeight : Signature → Signature → ℤ) : Prop :=
+  ∀ a b,
+    weight a b ≤ projectedUpperWeight (signature a) (signature b)
+
+/-- An exact-weight collision refutes deterministic weight recovery. -/
+theorem not_deterministicallyRecoversEdgeWeight_of_exactWeightCollision
+    {State Signature : Type*}
+    {signature : State → Signature} {weight : State → State → ℤ}
+    (hcollision : FiniteSignatureExactWeightCollision signature weight) :
+    ¬ FiniteSignatureDeterministicallyRecoversEdgeWeight signature weight := by
+  rintro hrecover
+  rcases hcollision with ⟨a, b, a', b', hsource, htarget, hne⟩
+  exact hne (hrecover a b a' b' hsource htarget)
+
+/-- The same collision remains compatible with a sound projected upper
+weight: both unequal realizations are bounded by the common projected edge
+weight.  Thus collision alone is not a certificate impossibility theorem. -/
+theorem exactWeightCollision_compatible_with_projectedUpperWeight
+    {State Signature : Type*}
+    {signature : State → Signature} {weight : State → State → ℤ}
+    {projectedUpperWeight : Signature → Signature → ℤ}
+    (hcollision : FiniteSignatureExactWeightCollision signature weight)
+    (hsound : FiniteSignatureProjectedUpperWeightSound
+      signature weight projectedUpperWeight) :
+    ∃ a b a' b',
+      signature a = signature a' ∧
+        signature b = signature b' ∧
+          weight a b ≠ weight a' b' ∧
+            weight a b ≤
+              projectedUpperWeight (signature a) (signature b) ∧
+              weight a' b' ≤
+                projectedUpperWeight (signature a) (signature b) := by
+  rcases hcollision with ⟨a, b, a', b', hsource, htarget, hne⟩
+  refine ⟨a, b, a', b', hsource, htarget, hne, hsound a b, ?_⟩
+  simpa [hsource, htarget] using hsound a' b'
+
+/-- Soundness of a finite projected upper-weight table for a concrete
+successor sequence. -/
+def FiniteSignatureSuccessorUpperWeightSound
+    {Signature : Type*}
+    (signature : ℕ → Signature) (weight : ℕ → ℤ)
+    (projectedUpperWeight : Signature → Signature → ℤ) : Prop :=
+  ∀ m,
+    weight m ≤ projectedUpperWeight (signature m) (signature (m + 1))
+
+/-- A finite projected successor-edge upper table exists exactly when the
+concrete successor weights have a uniform pointwise upper bound.  The forward
+direction uses the finite sum of absolute table entries as a coarse bound;
+the reverse direction uses a constant table.
+
+Consequently, changing or refining a finite signature cannot by itself evade
+an unbounded concrete edge family. -/
+theorem exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound
+    {Signature : Type*} [Finite Signature]
+    (signature : ℕ → Signature) (weight : ℕ → ℤ) :
+    (∃ projectedUpperWeight : Signature → Signature → ℤ,
+      FiniteSignatureSuccessorUpperWeightSound
+        signature weight projectedUpperWeight) ↔
+      ∃ B : ℤ, ∀ m, weight m ≤ B := by
+  classical
+  letI := Fintype.ofFinite Signature
+  constructor
+  · rintro ⟨upper, hupper⟩
+    refine ⟨∑ s : Signature, ∑ t : Signature, |upper s t|, ?_⟩
+    intro m
+    have hinner : |upper (signature m) (signature (m + 1))| ≤
+        ∑ t : Signature, |upper (signature m) t| := by
+      exact Finset.single_le_sum
+        (fun t _ => abs_nonneg (upper (signature m) t))
+        (Finset.mem_univ _)
+    have houter : (∑ t : Signature, |upper (signature m) t|) ≤
+        ∑ s : Signature, ∑ t : Signature, |upper s t| := by
+      exact Finset.single_le_sum
+        (fun s _ => Finset.sum_nonneg fun t _ => abs_nonneg (upper s t))
+        (Finset.mem_univ _)
+    exact (hupper m).trans
+      ((le_abs_self (upper (signature m) (signature (m + 1)))).trans
+        (hinner.trans houter))
+  · rintro ⟨B, hB⟩
+    refine ⟨fun _ _ => B, ?_⟩
+    exact hB
+
 /--
 A sound finite signed abstraction equipped with a bounded potential.  Concrete
 edge weight is bounded by projected edge weight, and projected edge weight is
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-339.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-339.md
new file mode 100644
index 00000000..647d6c25
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-339.md
@@ -0,0 +1,305 @@
+# Petal / Collatz implementation report: checkpoint 339
+
+Date: 2026-07-17
+
+## Status
+
+Checkpoint 339 reached the finite-certificate boundary and stopped at an
+exactly identified arithmetic obligation.  All new Lean declarations compile
+without `sorry`.
+
+The implementation is in:
+
+```text
+DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
+DkMath/Collatz/PetalBridge/FloatWindow.lean
+```
+
+The new `CanonicalSourceAgeFiniteCertificate` module keeps the certificate
+preparation work out of the already large horizon arithmetic module.
+
+## Padded carry word
+
+The new finite word
+
+```text
+canonicalPreBlockCarryWord n H m : Fin H -> Bool
+```
+
+represents the `H` source addresses immediately before block `m`.  Offset `r`
+represents `start - (r + 1)` only when `r + 1 <= start`; invalid offsets are
+false.  Thus early blocks do not duplicate source zero through natural-number
+underflow.
+
+The following all-regime identity is proved:
+
+```text
+canonicalPreBlockCarryWordTrueCount n H m
+  = card (canonicalPreBlockCarryCarrier n H m).
+```
+
+In the mature regime this also gives the requested direct mass bridge:
+
+```text
+canonicalRecentCarryMassBeforeStart n H m
+  = card (canonicalPreBlockCarryCarrier n H m)
+  = canonicalPreBlockCarryWordTrueCount n H m.
+```
+
+The true-bit population is proved to lie between `0` and `H`.
+
+## Window coboundary
+
+Every mature block window satisfies:
+
+```text
+frontierWindowSum(H,q,L)
+  = frontierWindowSum(0,q,L)
+      + recentMass(H,q)
+      - recentMass(H,q+L).
+```
+
+Equal padded carry words at both endpoints imply equal word populations and
+therefore equality of the horizon-`H` and horizon-zero window weights.
+
+This is an endpoint correction, not an independent source of accumulated
+weight.
+
+## Generic coboundary API
+
+`FiniteSignedTransition.lean` now contains a generic finite-path API:
+
+```text
+weight'(a,b) = weight(a,b) + correction(a) - correction(b).
+```
+
+Lean proves:
+
+- path weights differ only by endpoint correction;
+- state-closed path weights are invariant;
+- signature-closed path weights are invariant when the correction is
+  determined by the signature;
+- a positive closed-signature path remains positive after such reweighting.
+
+Thus a positive-horizon carry correction cannot erase a positive closed cycle
+when the endpoint carry state is part of the signature.
+
+## Pointwise necessity of finite potentials
+
+Every
+
+```text
+CanonicalFiniteSourceAgeFrontierPotentialCertificate n H Signature
+```
+
+now yields an integer `B` such that every actual frontier increment is at most
+`B`.  The proof takes a minimum of the potential on the finite signature type.
+
+This pointwise bound is necessary for the current finite-potential method.  It
+does not follow merely from nonpositive prefixes for an arbitrary signed flow.
+
+## Frontier boundedness audit
+
+This checkpoint obtained a stronger reduction than a numerical audit.
+
+For every mature block:
+
+```text
+frontier(H,m) <= frontier(0,m) + H
+frontier(0,m) <= frontier(H,m) + H.
+```
+
+Because block `m` starts no earlier than source time `m`, only the first `H`
+blocks can be non-mature.  Every finite integer prefix has an upper bound, so
+Lean proves the global equivalence:
+
+```text
+CanonicalSourceAgeFrontierIncrementUniformUpperBound n H
+  <->
+CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0.
+```
+
+The exact reflected max normal form at horizon zero then gives:
+
+```text
+CanonicalSourceAgeFrontierIncrementUniformUpperBound n 0
+  <->
+CanonicalEndpointAccountingTermUniformUpperBound n.
+```
+
+Therefore, for every fixed finite horizon:
+
+```text
+frontier increments are uniformly bounded above
+  <->
+raw endpoint drifts are uniformly bounded above.
+```
+
+This separates the branches precisely:
+
+- saturated blocks are already bounded, with horizon-zero value `1`;
+- zero-drift blocks have horizon-zero value `0`;
+- positive-pressure blocks transmit raw endpoint drift unchanged at horizon
+  zero;
+- a fixed positive horizon adds only a bounded coboundary and cannot hide an
+  unbounded positive-pressure family.
+
+No symbolic unbounded endpoint-drift family was proved in this checkpoint.
+Accordingly, the report does not claim that a finite certificate is
+impossible.
+
+## Exact collisions versus upper projections
+
+The generic API now distinguishes:
+
+```text
+FiniteSignatureDeterministicallyRecoversEdgeWeight
+FiniteSignatureExactWeightCollision
+FiniteSignatureProjectedUpperWeightSound
+```
+
+An exact collision formally refutes deterministic exact-weight recovery.
+However, if a sound projected upper table is supplied, both unequal concrete
+weights remain bounded by their common projected edge entry.  Therefore an
+ordinary collision is diagnostic only; it is not a certificate impossibility
+theorem.
+
+The stronger generic theorem is:
+
+```text
+exists finite successor upper-weight table
+  <->
+exists uniform upper bound on concrete successor weights.
+```
+
+The forward proof bounds all finite table entries by a finite sum of their
+absolute values.  The reverse proof uses a constant upper table.
+
+## Horizon-one residual and saturated word update
+
+For a saturated predecessor the following nonnegative scalar residuals were
+defined:
+
+```text
+successorNonfinalDemand
+successorExtraConsumed.
+```
+
+The exact identity is:
+
+```text
+frontier(1,m+1)
+  = successorNonfinalDemand - successorExtraConsumed.
+```
+
+This is scalar accounting only.  It does not identify the saturated final
+source as the concrete source consumed by the successor.
+
+For a mature saturated block, the successor pre-block word extended by two
+bits has:
+
+- first bit true;
+- second bit true;
+- remaining tail equal to the old word shifted by two positions.
+
+The frontier weight is the sum of the two crossing extended-word bits minus
+one.  This single formula recovers horizon-zero weight `1` and mature
+horizon-one weight `0`.
+
+## First candidate signature
+
+The finite type
+
+```text
+CanonicalSourceAgeFrontierSignature H queueCap
+```
+
+contains:
+
+- the padded carry word;
+- a capped queue coordinate with `queueCap + 1` as an overflow marker;
+- negative, zero, or positive endpoint-drift class;
+- saturated-block indicator;
+- final-source carry indicator.
+
+The cap is only an observable.  It does not assume a queue bound.
+
+For this concrete candidate Lean proves:
+
+```text
+exists sound projected successor upper-weight table
+  <->
+CanonicalEndpointAccountingTermUniformUpperBound n.
+```
+
+The same theorem holds for every finite candidate signature.  Refining the
+signature may improve collision diagnostics and cycle visibility, but it
+cannot manufacture the missing arithmetic ceiling.
+
+## Facts now fixed
+
+1. The padded carry word is correct even at the origin and exactly counts the
+   finite pre-block carrier.
+2. Positive horizon is a bounded endpoint coboundary of horizon zero.
+3. All fixed finite horizons have the same pointwise upper-boundedness status.
+4. That status is exactly uniform upper boundedness of raw endpoint drift.
+5. Every current finite-potential certificate implies the endpoint-drift
+   bound as a necessary consequence.
+6. Exact signature collisions refute only deterministic exact recovery.
+7. A sound finite upper-weight table exists exactly when the concrete edge
+   sequence is uniformly bounded above.
+8. The first finite signature candidate is genuinely finite and noncircular,
+   but its sound upper-weight obligation is not yet discharged.
+
+## Honest stopping boundary
+
+Stages A-G, J, K, and the Stage-L candidate signature are implemented.
+Stages H-I were not instantiated unconditionally.
+
+The reason is now a theorem rather than a design concern: before any finite
+reachable projected graph can receive a sound integer upper weight on all
+realized successor edges, one must prove
+
+```text
+CanonicalEndpointAccountingTermUniformUpperBound n.
+```
+
+Supplying that upper table without this proof would hide the main arithmetic
+obligation inside the certificate.  Using the queue cap as if it were an
+actual queue bound would likewise assume the desired conclusion.
+
+This is not a proof of unboundedness and not a proof that finite certificates
+cannot exist.  It is the exact dependency boundary for the present method.
+
+## Suggested next implementation
+
+Attack the endpoint-drift ceiling directly, especially the positive-pressure
+branch.  Two honest routes remain:
+
+1. prove a symbolic global upper bound for `endpointAccountingTerm n m` at
+   fixed `n`;
+2. construct a symbolic unbounded family, which would refute every finite
+   projected upper table for that root and every fixed horizon.
+
+Only after the first route succeeds should the reachable projected graph and
+potential verification stages be instantiated.  If the second route
+succeeds, the current pointwise finite-potential shape must be replaced rather
+than refined by more signature bits.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b|\badmit\b" \
+  DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean \
+  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeFiniteCertificate.lean
+git diff --check
+```
+
+The `rg` check returned no matches.
````
`````
