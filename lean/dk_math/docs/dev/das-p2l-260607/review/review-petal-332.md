# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: 5610d6351910ac8433b90fd63ef203108a5f84af

## Report

(6m17s)

cp-332 を完了しました。

- 過去窓を厳密な `[m-L, m)` に修正。未来の arrival を参照しません。
- lag だけでは不十分で、各 arrival 上限または recent-window mass 上限が別途必要だと定理化。
- canonical queue の正確な prefix balance を証明。
- canonical finite signature から queue／endpoint width bound を導く専用 certificate を実装。
- cp-331 の誤解を招く lag 説明も訂正。
- [report-petal-332.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-332.md) に結果と停止地点を記録。

Lean が認めた重要な事実は次です。

```text
queue = cumulative demand - cumulative consumption
```

また、有限署名経路では、potential 探索より先に「同じ signature edge に属する具体的重みが一様に上から抑えられること」が必須です。現在の真正な障害は、canonical recent-demand bound と具体的 signature の edgewise boundedness が未証明である点です。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath
git diff --check
```

変更した Lean ファイルに `sorry`、`maxHeartbeats` の追加はありません。

## Review

## cp-332 実装レビュー

## 結論

**cp-332 は採用。しかも、ここからは本当に「未証明を証明しに行く」段階へ入れる。**

checkpoint 332 は、

- causal な recent window
- exact canonical prefix balance
- finite signed-transition の challenge-facing bridge

を正しく完成させた。GitHub の commit `5610d635…` と添付差分も一致している。

ただし、未証明二候補をそのまま攻める前に重要な監査が一つある。

> 現在の `CanonicalFiniteSignedTransitionPotentialCertificate` も、抽象的な「存在」だけなら queue bound から人工的に作れる。

つまり、cp-330 の scalar potential と同型の循環が、finite signature 側にも再発し得る。

その一方で、現在の API だけから**直ちに証明できる非自明な新定理**も見つかった。

> canonical demand は、block 数ではなく orbit source-time 幅によって支配できる。

さらに raw-step route では、

> 任意の固定 low-bit 幅に対して、正 drift の closed-signature edge を作る all-ones witness

も形式化できる。

この二本を次 checkpoint で実際に Lean に通すのがよい。

---

## 1. cp-332 の採用点

### Recent window

旧定義の未来参照を除去し、

$$\operatorname{RecentMass}(L,m)=\sum_{k\in[m-L,m)}a_k$$

へ修正された。

$m<L$ では $[0,m)$、$m\ge L$ では正確に $L$ slot となる。境界 regression も十分じゃ。

### Exact prefix balance

一段保存則を telescope して、

$$Q_m+\sum_{k<m}C_k=\sum_{k<m}A_k$$

が得られた。

したがって、

$$Q_m=\sum_{k<m}A_k-\sum_{k<m}C_k$$

じゃ。

queue は potential 的な比喩ではなく、**累積 demand と実 consumption の未決済差額そのもの**になった。

### Canonical signed certificate

finite signature certificate から、

$$\text{全 window drift 上界}\Longrightarrow\text{queue 上界}\Longrightarrow\text{endpoint width 上界}$$

までの条件付き chain が完成した。

この接続 theorem 自体は正しい。

---

## 2. Finite certificate にも循環構成がある

uniform queue bound、

$$Q_k\le C$$

を仮定する。

signature type を、

```lean
Fin (C + 1)
```

とし、block $k$ の signature を処理直前 queue とする。

$$\sigma(k)=Q^{\mathrm{before}}_k$$

potential は、

$$\Phi(s)=s$$

projected weight は、

$$\widehat w(s,t)=t-s$$

と置く。

reflected queue の exact conservationから、

$$D_k\le Q^{\mathrm{before}}_{k+1}-Q^{\mathrm{before}}_k$$

が成立する。

理由は、

$$Q^{\mathrm{after}}_k+C_k=Q^{\mathrm{before}}_k+A_k$$

かつ、

$$C_k\le S_k$$

なので、

$$A_k-S_k\le Q^{\mathrm{after}}_k-Q^{\mathrm{before}}_k$$

となるからじゃ。

そして、

$$Q^{\mathrm{before}}_{k+1}=Q^{\mathrm{after}}_k$$

である。

従って、queue bound から、

```lean
CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1))
```

を構成できる。

逆向きは cp-332 で既に証明済み。

よって抽象的存在水準では、

$$\exists\text{ finite certificate}\iff\exists\text{ uniform queue bound}$$

となる。

これは certificate theorem の誤りではない。

ただし、

> 何らかの finite signature が存在する

では問題は簡約されない。

本当に必要なのは、

> queue や目的の上界から逆算せず、block の有限な局所算術から先に固定された signature

じゃ。

---

## 3. 次に本当に証明できる theorem

既に次がある。

```lean
canonicalBlockClaimCount_le_length
```

すなわち、

$$A_k\le L_k$$

じゃ。canonical claim は block source の部分集合なので、当然ながら block length を超えない。

さらに canonical blocks は source time 上で隙間なく隣接している。

次を証明できる。

$$b_{k+1}=b_k+L_k$$

ここで $b_k$ は `canonicalBlockStartTime n k`。

従って、

$$\sum_{k=q}^{m-1}L_k=b_m-b_q$$

となる。

以上から、

$$\sum_{k=q}^{m-1}A_k\le b_m-b_q$$

が得られる。

cp-332 の recent window へ入れると、

$$\operatorname{RecentDemand}(L,m)\le b_m-b_{m-L}$$

じゃ。

これは完全に現在の API だけで証明可能である。

---

## 4. Block 数 lag より source-time lag

block 数 lag では、各 block の length が大きくなり得るため、別途 arrival mass 上界が必要だった。

しかし source time で測れば、一時刻には claim は高々一件しかない。

source-time 幅 $H$ の区間、

$$[b_m-H,b_m)$$

には高々 $H$ 個の source address しかない。

したがって、

```lean
canonicalRecentSourceClaimCarrier n H m :=
  (Finset.Ico
    (canonicalBlockStartTime n m - H)
    (canonicalBlockStartTime n m)).filter
      (CarryTwoDebtAt n)
```

と置けば、

$$|\operatorname{RecentSourceClaims}(H,m)|\le H$$

は直ちに証明できる。

そして、

```lean
CanonicalOutstandingQueueCoveredByRecentSourceClaims n H
```

を、

$$Q^{\mathrm{before}}_m\le|\operatorname{RecentSourceClaims}(H,m)|$$

と定義すれば、

$$Q^{\mathrm{before}}_m\le H$$

が一仮定だけで従う。

つまり、

```text
block lag L
+
recent block demand bound B
```

という二条件を、

```text
source-time claim age H
```

という一条件へまとめられる。

もちろん一様な $H$ 自体はまだ未証明じゃ。

だが、未証明命題の形が一段鋭くなる。

---

## 5. Fixed low-bit signature は all-ones witness で攻撃できる

finite-signature routeでは、具体的候補を一つずつ試すより、固定 low-bit 型を一括で倒せる可能性がある。

$r\ge1$ として、

$$x_r=2^{r+2}-1$$

と置く。

これは上位まで全て $1$ の有限自然数じゃ。

accelerated step は、

$$T(x_r)=3\cdot2^{r+1}-1$$

となる。

両者は、

$$x_r\equiv T(x_r)\equiv-1\pmod{2^r}$$

を満たす。

さらに、

$$s(x_r)=1$$

$$s(T(x_r))=1$$

$$\operatorname{stateUpperCarry}(x_r)=2$$

$$\operatorname{stateUpperCarry}(T(x_r))=2$$

であり、二つの step はとも width growth $+1$ になる。

特に、

$$\operatorname{bitWidth}(T(x_r))=\operatorname{bitWidth}(x_r)+1$$

じゃ。

したがって signature が、

- residue modulo $2^r$
- carry one/two
- height one / at least two
- growth flag

だけで作られているなら、$x_r$ と $T(x_r)$ は同じ signature を持つ。

しかしその edge weight は $+1$。

つまり finite graph 上に、

$$s\xrightarrow{+1}s$$

という正の self-loop が実現する。

bounded potential なら closed-signature path の weight は非正でなければならないため、矛盾する。

これは、

> 固定 low-bit 窓だけでは eventually-zero upper boundary を識別できない

ことの exact theorem になる。

DkMath が以前から見ていた、

```text
有限自然数:
  ...000001111

2-adic all-ones limit:
  ...111111111
```

の差が、finite-signature obstruction として現れるわけじゃ。

---

## 6. どの未証明を先に攻めるか

### Uniform per-block demand bound

直接は勧めない。

既存 theorem は、

$$A_k\le L_k$$

までであり、block length は局所データとして無界候補だからじゃ。

### Block-level finite signature

現在の abstract existence は queue bound と同値になる。

まず queue 非依存の具体的 signature を固定しなければならない。

### Raw low-bit signature

all-ones witness による一般的な正 self-loop obstructionを証明できる。

これは明確な前進になる。

### Source-time lag

block-arrival mass の問題を source-address の有限性へ変換できる。

現在最も建設的な route じゃ。

---

## 7. report の停止文の補正

cp-332 report の、

> first applicable stopping condition is the absence of a canonical recent-demand bound

は route 全体の停止条件としては強い。

recent-demand route と finite-signature route は独立している。

正確には、

```text
repayment-lag route:
  recent demand / source-time age theoremで停止

finite-signature route:
  fixed structural signature の edgewise bound または正 cycle obstructionで停止
```

じゃ。

一方が止まっても、他方は進める。

---

## 判定まとめ

### Exact recent window

**完成。**

### Canonical prefix balance

**完成。**

### Canonical certificate conditional chain

**完成。**

### Abstract finite-certificate existence

**queue bound から人工構成可能。単独では簡約にならない。**

### Source-time demand bound

**現在の API だけで証明可能。次の実証目標。**

### Fixed low-bit finite signature

**all-ones familyによる正 self-loop obstructionを証明可能。**

### 真の次戦線

**source-time age と eventually-zero boundary を signature にどう入れるか。**

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-332.

This checkpoint is not another interface-only checkpoint.

It must prove two substantive facts:

    canonical demand is bounded by actual orbit source-time span;

    every fixed low-bit raw signature of the audited form has an all-ones
    positive closed-signature obstruction.

It must also record the circular reverse construction for the current abstract
canonical finite certificate.

## Stage A — finite-certificate circularity regression

Prove the reflected increment inequality:

    endpointAccountingTerm n k
      <=
    (canonicalOutstandingClaimQueueBeforeBlock n (k + 1) : Int)
      -
    canonicalOutstandingClaimQueueBeforeBlock n k.

Use:

    canonicalOutstandingClaimQueue_add_consumed;
    canonicalQueueConsumed_le_service;
    endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount.

Then, from:

    hC : CanonicalOutstandingClaimQueueUniformUpperBound n C

construct:

    canonicalFiniteSignedCertificateOfQueueBound hC :
      CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)).

Use:

    signature k = queueBeforeBlock k;
    projectedUpperWeight s t = (t.val : Int) - s.val;
    potential s = s.val;
    bound = C.

Prove a semantic regression saying that unrestricted existential certificate
existence is equivalent to existential queue boundedness, or at minimum prove
both explicit implications.

Document:

    only a structurally predefined signature independent of `hC` is
    noncircular.

Do not withdraw the valid conditional certificate theorem.

## Stage B — exact block-start recurrence

Prove:

    canonicalBlockStartTime n (k + 1)
      =
    canonicalBlockStartTime n k + canonicalBlockLength n k.

Use:

    canonicalBlockStartTime_add_length_sub_one_eq_endpoint;
    canonicalBlockStartTime;
    canonicalEndpointBlockStart.

Then prove:

    sum k in Finset.range m, canonicalBlockLength n k
      =
    canonicalBlockStartTime n m.

And for q <= m:

    sum k in Finset.Ico q m, canonicalBlockLength n k
      =
    canonicalBlockStartTime n m - canonicalBlockStartTime n q.

## Stage C — canonical demand versus source-time span

Use the existing:

    canonicalBlockClaimCount_le_length

to prove:

    sum k in Finset.Ico q m, canonicalQueueDemand n k
      <=
    canonicalBlockStartTime n m - canonicalBlockStartTime n q.

Specialize to the corrected recent block window:

    recentArrivalMass (canonicalQueueDemand n) L m
      <=
    canonicalBlockStartTime n m
      - canonicalBlockStartTime n (m - L).

This theorem is unconditional and must be completed.

## Stage D — source-time recent claim carrier

Define:

    canonicalRecentSourceClaimCarrier n H m

as source times in:

    Ico
      (canonicalBlockStartTime n m - H)
      (canonicalBlockStartTime n m)

that satisfy `CarryTwoDebtAt n`.

Prove:

    card canonicalRecentSourceClaimCarrier <= H.

Add exact early-time and `H = 0` regressions.

## Stage E — source-time lag consequence

Define:

    CanonicalOutstandingQueueCoveredByRecentSourceClaims n H

to mean:

    queueBeforeBlock m
      <=
    card (canonicalRecentSourceClaimCarrier n H m)

for every m.

Prove:

    CanonicalOutstandingQueueCoveredByRecentSourceClaims n H
      ->
    forall m, queueBeforeBlock m <= H.

Translate this to:

    CanonicalOutstandingClaimQueueUniformUpperBound n H

with the correct before/after index shift.

Record that the sole missing input on this refined route is now a uniform
source-time claim-age theorem.

Do not claim such an H exists.

## Stage F — connect block recent demand to source claims

Using the carrier-level canonical block-window theorem, prove that:

    sum of canonicalQueueDemand over blocks q .. m-1

equals the number of carry-two claim source times in:

    Ico (canonicalBlockStartTime n q)
        (canonicalBlockStartTime n m).

At minimum prove both cardinalities are equal.

This identifies block arrivals with actual source addresses rather than only
using the coarse `claimCount <= length` inequality.

## Stage G — all-ones raw witness

For r >= 1 define:

    rawAllOnesWitness r : OddNat
      := 2^(r + 2) - 1.

Prove:

    T (rawAllOnesWitness r) = 3 * 2^(r + 1) - 1;

    s (rawAllOnesWitness r) = 1;

    s (T (rawAllOnesWitness r)) = 1;

    bitWidth (T (rawAllOnesWitness r))
      =
    bitWidth (rawAllOnesWitness r) + 1;

    bitWidth (T (T (rawAllOnesWitness r)))
      =
    bitWidth (T (rawAllOnesWitness r)) + 1;

    both source and target are congruent to `2^r - 1` modulo `2^r`;

    both source and target have upper carry two.

Keep all exponent side conditions explicit.

## Stage H — reject the fixed low-window signature family

Define a concrete finite raw signature containing only:

    residue modulo 2^r;
    upper carry;
    height class one / at least two;
    width-growth flag.

Prove that the source and target from Stage G have equal signatures.

The realized edge has signed width weight `+1`.

Use `pathWeight_nonpos_of_signature_eq`, or the potential-difference axiom
directly, to prove:

    no sound bounded-potential certificate using this signature can cover all
    positive odd states.

This should be a theorem parameterized by r >= 1, not a table of examples.

Interpretation:

    every fixed low-bit observation confuses a sufficiently long finite
    all-ones prefix with the 2-adic all-ones continuation.

## Stage I — route decision

After Stages A-H, compare:

    source-time lag route;
    fixed low-bit finite-signature route;
    signatures enriched by an upper-boundary / eventually-zero coordinate.

The fixed low-bit route should be marked rejected if Stage H closes.

Do not conclude that every finite signature is impossible.  A signature that
contains a finite upper-boundary coordinate or a dynamically decreasing rank
remains open.

## Stage J — challenge-facing boundary

Keep the exact chain visible:

    uniform source-time claim age
      ->
    queue bound
      ->
    endpoint width bound.

And separately:

    structurally fixed finite certificate
      ->
    queue bound
      ->
    endpoint width bound.

State that unrestricted abstract certificate existence is circular, while a
specific arithmetic certificate remains legitimate.

## Stopping rule

Stop at the first genuine obstruction among:

    queue drift cannot be bounded by queue increment;
    block starts do not telescope by block length;
    canonical block demand does not equal actual source claim count;
    source-time recent carrier does not have cardinality <= H;
    all-ones witness fails to preserve the proposed low signature;
    the all-ones edge is not a positive closed-signature path;
    an upper-boundary coordinate cannot be finitely formulated.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-333.md
```

うむ。今回は「未証明を別名で包む」のではない。

**一つは実際に証明し、一つは反例族として実際に倒す。**

その両方を Lean に裁かせる checkpoint にできるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean
index d3ef1cd1..ff30b15f 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/BoundedRepaymentLag.lean
@@ -4,6 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
 import Mathlib.Algebra.Order.BigOperators.Group.Finset
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag"
@@ -13,43 +14,126 @@ namespace DkMath.Collatz
 /-!
 # Generic bounded repayment lag
 
-The predicate below is the scalar consequence of an owned statement saying
-that every outstanding arrival at time `m` was born in one of the preceding
-`L` slots.  It is independent of Collatz and deliberately does not manufacture
-claim ownership.
+The recent window is the half-open interval `[m-L,m)`.  Unlike the former
+shifted-range formula, it never refers to arrivals after observation time `m`.
 -/
 
-/-- Outstanding work is covered by arrivals in the preceding `L` slots. -/
+/-- Total arrivals in the at-most-`L` slots immediately preceding `m`. -/
+def recentArrivalMass (arrivals : ℕ → ℕ) (L m : ℕ) : ℕ :=
+  ∑ k ∈ Finset.Ico (m - L) m, arrivals k
+
+/-- Before the lag horizon is filled, the recent window is the full prefix. -/
+theorem recentArrivalMass_eq_sum_range_of_lt
+    (arrivals : ℕ → ℕ) {L m : ℕ} (hm : m < L) :
+    recentArrivalMass arrivals L m = ∑ k ∈ Finset.range m, arrivals k := by
+  unfold recentArrivalMass
+  rw [Nat.sub_eq_zero_of_le hm.le, Nat.Ico_zero_eq_range]
+
+/-- After the horizon is filled, the exact past window has `L` shifted slots. -/
+theorem recentArrivalMass_eq_sum_range_of_le
+    (arrivals : ℕ → ℕ) {L m : ℕ} (hL : L ≤ m) :
+    recentArrivalMass arrivals L m =
+      ∑ j ∈ Finset.range L, arrivals (m - L + j) := by
+  unfold recentArrivalMass
+  rw [Finset.sum_Ico_eq_sum_range]
+  have hlen : m - (m - L) = L := by omega
+  rw [hlen]
+
+/-- The recent half-open interval contains at most `L` indices. -/
+theorem card_recentArrivalWindow_le (L m : ℕ) :
+    (Finset.Ico (m - L) m).card ≤ L := by
+  simp
+  omega
+
+/-- Correct scalar lag surface: outstanding work is covered by actual past
+arrivals in the recent half-open window. -/
+def OutstandingBeforeQueueCoveredByRecentArrivals
+    (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
+  ∀ m, queue m ≤ recentArrivalMass arrivals L m
+
+/-- Coarse compatibility predicate from cp-331.  It may include future slots
+when `m < L`; new proofs should use
+`OutstandingBeforeQueueCoveredByRecentArrivals`. -/
+@[deprecated OutstandingBeforeQueueCoveredByRecentArrivals (since := "2026-07-16")]
 def OutstandingQueueHasRepaymentLag
     (queue arrivals : ℕ → ℕ) (L : ℕ) : Prop :=
   ∀ m, queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j)
 
-/-- A lag bound `L` and per-slot arrival bound `A` imply queue bound `L*A`. -/
-theorem queue_le_mul_of_repaymentLag_of_arrivals_le
-    {queue arrivals : ℕ → ℕ} {L A : ℕ}
-    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
+/-- A direct recent-window mass ceiling gives the same queue ceiling. -/
+theorem queue_le_of_recentArrivalMass_le
+    {queue arrivals : ℕ → ℕ} {L B : ℕ}
+    (hlag : OutstandingBeforeQueueCoveredByRecentArrivals queue arrivals L)
+    (hmass : ∀ m, recentArrivalMass arrivals L m ≤ B) (m : ℕ) :
+    queue m ≤ B := (hlag m).trans (hmass m)
+
+/-- Per-slot arrival bound `A` controls each exact recent window by `L*A`. -/
+theorem recentArrivalMass_le_mul_of_arrivals_le
+    {arrivals : ℕ → ℕ} {L A : ℕ}
     (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
-    queue m ≤ L * A := by
+    recentArrivalMass arrivals L m ≤ L * A := by
+  unfold recentArrivalMass
   calc
-    queue m ≤ ∑ j ∈ Finset.range L, arrivals (m - L + j) := hlag m
-    _ ≤ ∑ _j ∈ Finset.range L, A :=
-      Finset.sum_le_sum fun j _ => harrivals (m - L + j)
-    _ = L * A := by simp
+    (∑ k ∈ Finset.Ico (m - L) m, arrivals k) ≤
+        ∑ _k ∈ Finset.Ico (m - L) m, A :=
+      Finset.sum_le_sum fun k _ => harrivals k
+    _ = (Finset.Ico (m - L) m).card * A := by simp
+    _ ≤ L * A := Nat.mul_le_mul_right A (card_recentArrivalWindow_le L m)
 
-/-- Caller-facing uniform form of the generic lag theorem. -/
-theorem repaymentLag_uniformUpperBound
+/-- Correct lag plus per-slot arrivals yields a uniform queue bound. -/
+theorem queue_le_mul_of_recentCoverage_of_arrivals_le
     {queue arrivals : ℕ → ℕ} {L A : ℕ}
-    (hlag : OutstandingQueueHasRepaymentLag queue arrivals L)
-    (harrivals : ∀ k, arrivals k ≤ A) :
-    ∀ m, queue m ≤ L * A :=
-  fun m => queue_le_mul_of_repaymentLag_of_arrivals_le hlag harrivals m
+    (hlag : OutstandingBeforeQueueCoveredByRecentArrivals queue arrivals L)
+    (harrivals : ∀ k, arrivals k ≤ A) (m : ℕ) :
+    queue m ≤ L * A :=
+  (hlag m).trans (recentArrivalMass_le_mul_of_arrivals_le harrivals m)
+
+/-! ## Boundary regressions -/
+
+@[simp] theorem recentArrivalMass_zero (arrivals : ℕ → ℕ) (L : ℕ) :
+    recentArrivalMass arrivals L 0 = 0 := by simp [recentArrivalMass]
+
+theorem recentArrivalMass_early
+    (arrivals : ℕ → ℕ) {L m : ℕ} (hm : m < L) :
+    recentArrivalMass arrivals L m = ∑ k ∈ Finset.range m, arrivals k :=
+  recentArrivalMass_eq_sum_range_of_lt arrivals hm
+
+theorem recentArrivalMass_at_horizon (arrivals : ℕ → ℕ) (L : ℕ) :
+    recentArrivalMass arrivals L L = ∑ k ∈ Finset.range L, arrivals k := by
+  simpa using recentArrivalMass_eq_sum_range_of_le arrivals (le_rfl : L ≤ L)
+
+@[simp] theorem recentArrivalMass_lag_zero (arrivals : ℕ → ℕ) (m : ℕ) :
+    recentArrivalMass arrivals 0 m = 0 := by simp [recentArrivalMass]
+
+/-! ## Canonical conditional surfaces -/
+
+/-- Conditional lag coverage for the actual canonical reflected queue. -/
+def CanonicalOutstandingQueueCoveredByRecentDemand
+    (n : OddNat) (L : ℕ) : Prop :=
+  OutstandingBeforeQueueCoveredByRecentArrivals
+    (canonicalOutstandingClaimQueueBeforeBlock n) (canonicalQueueDemand n) L
+
+/-- Canonical lag plus a per-block demand ceiling gives an explicit queue
+ceiling.  Neither hypothesis is currently known uniformly. -/
+theorem canonicalQueueBound_of_recentDemandCoverage_of_demand_le
+    {n : OddNat} {L A : ℕ}
+    (hlag : CanonicalOutstandingQueueCoveredByRecentDemand n L)
+    (hdemand : ∀ k, canonicalQueueDemand n k ≤ A) :
+    ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤ L * A :=
+  fun m => queue_le_mul_of_recentCoverage_of_arrivals_le hlag hdemand m
+
+/-- Canonical lag plus a direct recent-demand mass ceiling gives the sharper
+queue ceiling `B`. -/
+theorem canonicalQueueBound_of_recentDemandCoverage_of_mass_le
+    {n : OddNat} {L B : ℕ}
+    (hlag : CanonicalOutstandingQueueCoveredByRecentDemand n L)
+    (hmass : ∀ m, recentArrivalMass (canonicalQueueDemand n) L m ≤ B) :
+    ∀ m, canonicalOutstandingClaimQueueBeforeBlock n m ≤ B :=
+  fun m => queue_le_of_recentArrivalMass_le hlag hmass m
 
 /-!
-For the canonical Collatz queue, the missing theorem is not the generic
-counting argument above.  It is an owned statement that each actual claim is
-consumed within one uniform number of later canonical blocks.  The current
-residue and saturated-successor grammar proves repayment for selected local
-branches, but no theorem supplies a uniform lag for all canonical claims.
+No uniform canonical `L`, per-block `A`, or recent-window `B` is proved.  The
+owned claim carrier remains a possible mechanism for proving lag, but lag and
+recent-demand mass control are logically separate obligations.
 -/
 
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index df465e4d..3f0f8075 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -226,6 +226,73 @@ theorem relationalFiniteSignedCertificate_to_endpointWidthUniformUpperBound
   (relationalFiniteSignedCertificate_to_queueUniformUpperBound
     n C hstep hweight).to_endpointWidthUniformUpperBound
 
+/-! ## Canonical finite projection wrapper -/
+
+/-- Candidate-facing finite signature certificate specialized to canonical
+block edges and their exact endpoint accounting weights. -/
+structure CanonicalFiniteSignedTransitionPotentialCertificate
+    (n : OddNat) (Signature : Type*) [Fintype Signature] where
+  signature : ℕ → Signature
+  projectedUpperWeight : Signature → Signature → ℤ
+  potential : Signature → ℤ
+  bound : ℕ
+  actual_le_projected : ∀ k,
+    endpointAccountingTerm n k ≤
+      projectedUpperWeight (signature k) (signature (k + 1))
+  projected_le_potential_diff : ∀ s t,
+    projectedUpperWeight s t ≤ potential t - potential s
+  potential_nonneg : ∀ s, 0 ≤ potential s
+  potential_le_bound : ∀ s, potential s ≤ bound
+
+namespace CanonicalFiniteSignedTransitionPotentialCertificate
+
+variable {n : OddNat} {Signature : Type*} [Fintype Signature]
+
+/-- Forgetting specialization yields the generic relational certificate. -/
+noncomputable def toRelational
+    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
+    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature where
+  Step a b := b = a + 1
+  signature := C.signature
+  actualWeight a _ := endpointAccountingTerm n a
+  projectedUpperWeight := C.projectedUpperWeight
+  potential := C.potential
+  bound := C.bound
+  actual_le_projected := by
+    intro a b hab
+    subst b
+    exact C.actual_le_projected a
+  projected_le_potential_diff := C.projected_le_potential_diff
+  potential_nonneg := C.potential_nonneg
+  potential_le_bound := C.potential_le_bound
+
+/-- A canonical finite projection directly bounds the reflected queue. -/
+theorem to_queueUniformUpperBound
+    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n C.bound := by
+  apply relationalFiniteSignedCertificate_to_queueUniformUpperBound
+    n C.toRelational
+  · intro k
+    rfl
+  · intro k
+    rfl
+
+/-- A canonical finite projection directly bounds completed endpoint widths. -/
+theorem to_endpointWidthUniformUpperBound
+    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
+    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + C.bound) :=
+  C.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound
+
+/-!
+Before searching for `potential`, a candidate signature must establish that
+all realized canonical edges sharing one signature pair have a finite common
+upper weight.  Exact drift collisions are harmless when such an upper bound
+exists; an unbounded positive collision rejects the candidate immediately.
+No currently audited low-bit signature has this edgewise theorem yet.
+-/
+
+end CanonicalFiniteSignedTransitionPotentialCertificate
+
 namespace FiniteSignedTransitionPotentialCertificate
 
 variable {State Signature : Type*} [Fintype Signature]
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
index a8dd9538..e55cf1d4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentAmortizedResource.lean
@@ -234,6 +234,32 @@ theorem canonicalOutstandingClaimQueue_eq_available_sub_consumed
   have hle := canonicalQueueConsumed_le_available n k
   omega
 
+/-! ## Exact canonical prefix balance -/
+
+/-- Exact telescoping equality for every prefix of canonical blocks. -/
+theorem canonicalQueueBefore_add_sum_consumed_eq_sum_demand
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueueBeforeBlock n m +
+        ∑ k ∈ Finset.range m, canonicalQueueConsumed n k =
+      ∑ k ∈ Finset.range m, canonicalQueueDemand n k := by
+  induction m with
+  | zero => simp
+  | succ m ih =>
+      rw [Finset.sum_range_succ, Finset.sum_range_succ,
+        canonicalOutstandingClaimQueueBeforeBlock_succ]
+      have hstep := canonicalOutstandingClaimQueue_add_consumed n m
+      omega
+
+/-- The queue before block `m` is cumulative demand minus cumulative actual
+consumption. -/
+theorem canonicalQueueBefore_eq_sum_demand_sub_sum_consumed
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueueBeforeBlock n m =
+      (∑ k ∈ Finset.range m, canonicalQueueDemand n k) -
+        ∑ k ∈ Finset.range m, canonicalQueueConsumed n k := by
+  have h := canonicalQueueBefore_add_sum_consumed_eq_sum_demand n m
+  omega
+
 /-!
 ## Owned-resource frontier
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md
index cd3b72ad..aac1393c 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-331.md
@@ -89,9 +89,11 @@ with a sound projected upper edge weight and bounded potential.  Existing
 low-bit collision evidence rules out exact deterministic recovery, but does
 not by itself rule out a nondeterministic upper-weight projection.
 
-## Bounded repayment-lag route
+## Bounded repayment-lag route (corrected by checkpoint 332)
 
-`BoundedRepaymentLag.lean` proves the generic implication:
+Checkpoint 331 introduced the route, but its shifted early-time window could
+include indices at or after the observation time.  Checkpoint 332 replaces it
+with the exact past interval `[m-L,m)` and proves the corrected implication:
 
 ```text
 all outstanding work lies among the previous L arrival slots
@@ -100,9 +102,10 @@ each slot creates at most A arrivals
 queue m <= L * A.
 ```
 
-The first missing Collatz theorem is a uniform lag for all actual canonical
-claims.  Current saturated-successor results repay selected local subclasses,
-but do not provide such a global lag.
+The route has two independent missing canonical inputs: uniform lag coverage
+and a uniform bound on demand accumulated in each recent window (or a
+per-block demand bound).  Current saturated-successor results repay selected
+local subclasses, but provide neither complete global obligation.
 
 ## Owned-carrier route
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-332.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-332.md
new file mode 100644
index 00000000..63114df0
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-332.md
@@ -0,0 +1,122 @@
+# Petal / FloatWindow implementation report - checkpoint 332
+
+## Result
+
+This checkpoint repairs the repayment-lag window, strengthens canonical scalar
+accounting to an exact prefix identity, and exposes a canonical finite signed
+projection certificate with no arbitrary actual-weight bookkeeping.
+
+The branch stops at an honest obstruction: no uniform canonical recent-demand
+window bound is currently proved, and no proposed finite block signature has
+yet established edgewise boundedness.  Consequently neither route may be
+reported as an unconditional endpoint-width theorem.
+
+## Exact recent-arrival window
+
+The corrected window is
+
+```text
+recentArrivalMass arrivals L m
+  = sum k in [m-L,m), arrivals k.
+```
+
+It contains no future index.  Lean proves that it is the full prefix when
+`m < L`, the expected shifted range when `L <= m`, and has at most `L` slots.
+Regressions cover `m = 0`, `m < L`, `m = L`, and `L = 0`.
+
+The old `OutstandingQueueHasRepaymentLag` remains only as a deprecated coarse
+compatibility predicate.  New callers use
+`OutstandingBeforeQueueCoveredByRecentArrivals`.
+
+## What lag actually proves
+
+Lag coverage alone is not a queue bound.  Lean now separates the required
+second obligation:
+
+```text
+queue covered by recent L arrivals
++ each arrival slot <= A
+----------------------------------
+queue m <= L * A
+```
+
+Alternatively, a direct recent-window mass bound `B` yields `queue m <= B`.
+For the canonical queue these become two conditional interfaces.  No uniform
+canonical `L`, `A`, or `B` is claimed.
+
+## Exact canonical prefix balance
+
+The block conservation identity telescopes exactly to
+
+```text
+canonicalQueueBefore m + sum(consumed, range m)
+  = sum(demand, range m).
+```
+
+Hence the reflected queue is exactly cumulative demand minus cumulative
+consumption.  This confirms that bounded total demand is unnecessary; bounded
+net inflow is the relevant scalar quantity.
+
+## Canonical finite signed projection
+
+`CanonicalFiniteSignedTransitionPotentialCertificate` specializes the generic
+relational certificate to the actual edge
+
+```text
+k -> k + 1
+weight = endpointAccountingTerm n k.
+```
+
+A constructor supplies only a finite signature, a projected upper edge weight,
+a bounded potential, and proofs that concrete edges lie below projected edges
+and projected edges lie below potential differences.  Lean then derives:
+
+```text
+canonical queue <= certificate.bound
+canonical endpoint width <= bitWidth n + certificate.bound.
+```
+
+Before any potential search, every candidate signature must prove that all
+realized concrete edges sharing a signature pair have a finite common upper
+bound.  Exact drift collisions are not themselves fatal; unbounded positive
+collisions are.
+
+## Route status
+
+The current conditional routes are:
+
+1. finite signed transition: the shortest complete conditional chain, missing
+   a concrete finite signature with edgewise boundedness and a potential;
+2. bounded repayment lag: missing both canonical lag coverage and recent-demand
+   mass control;
+3. owned claim carrier: potentially useful for source identity, claim age, and
+   lag, but not assumed to be an initial finite upper resource;
+4. raw-step projection: still a legitimate fallback if block signatures fail,
+   but no uncontrolled-cycle claim has been made.
+
+The first applicable stopping condition is therefore the absence of a proved
+canonical recent-window demand bound.  Candidate signature auditing cannot
+soundly advance to cycle or potential search until its independent edgewise
+boundedness obligation is established.
+
+## Verification
+
+The targeted modules were checked first:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+```
+
+The complete gate passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
+lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath
+git diff --check
+```
+
+The changed FloatWindow Lean files contain no `sorry` and no local heartbeat
+override.
````
`````
