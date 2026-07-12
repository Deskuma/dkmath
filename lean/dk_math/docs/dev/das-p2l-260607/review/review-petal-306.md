# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock

gch: c8d00b87b570c48b18102a1ecc4675c3444d6c13

## Report

実装を進めました。

新たに確定した事実:

- `orbitPaymentTarget` は source 以上で、target を再適用しても不変。
- fixed point は `height ≥ 2` と同値。
- height-one の次時刻は同じ target を保つ。
- extra-height 時刻の次 target は厳密に先へ進む。
- 非空 universal source fiber は厳密に
  `Icc (universalPaymentBlockStart ...) j`
  という連続区間。
- 内部はすべて height `1`、endpoint は height `≥ 2`。
- block 内の exact-depth profile は
  `orbitExactDepth n i = j - i + 1`。

これは cp-305 で保留した universal fiber contiguity を、既存の forward staircase theorem から閉じたものです。

レポート: [report-petal-306.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-306.md)

`UniversalPaymentBlock` の targeted build と `git diff --check` は成功し、変更 Lean ファイルに `sorry` / `axiom` はありません。

## Review

# cp-306 実装レビュー

## 結論

**Lean 実装と数学内容は採用。checkpoint handoff は条件付き採用じゃ。**

cp-306 は、universal payment target を単なる関数から、

- source 以上へ進む
- payment endpoint 上では固定される
- height-one 区間では一定
- extra-height endpoint を越えると厳密に次へ進む
- 各 fiber が連続区間になる

という **block 射影**へ完成させた。

特に、

```lean
orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart
```

によって、

$$
\operatorname{Fiber}(j)=\operatorname{Icc}(b,j)
$$

が Lean 上で確定した。

ここで $b$ は `universalPaymentBlockStart` じゃ。

cp-305 で誤って「新しい逆向き staircase が必要」とされた境界も、既存の forward theorem を使って正しく突破している。

ただし二点、checkpoint を完全採用とする前に直すべきものがある。

1. `UniversalPaymentBlock.lean` 末尾のコメントが cp-305 の古い状態のまま残っている。
2. 今回の report では targeted build と `git diff --check` だけが報告され、`FloatWindow`、`PetalBridge`、トップレベル `DkMath` の build が記載されていない。

コードの論理問題ではないが、report/source の整合性と検証 gate が未完じゃ。

---

## 独立検証

基準 snapshot、

```text
19752c9b3cba9cc8e36e6d69237d9a4cb6ad08e9700f60ad6f0ee491863f9b5d
```

へ cp-304、cp-305、cp-306 の差分を順に適用した。

結果は、

```text
cp-304: clean apply
cp-305: clean apply
cp-306: clean apply
```

だった。

変更後の、

```text
DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
```

を直接検索し、`sorry` / `axiom` が存在しないことも確認した。

この環境には `lake` / `lean` 実行系がないため、わっち自身による build 再実行はできていない。

---

## target lower bound

```lean
le_orbitPaymentTarget
```

は、任意の時刻 $i$ に対して、

$$
i\le\tau(i)
$$

を示す。

ここで、

$$
\tau(i)=i+A_i-1
$$

であり、$A_i$ は exact all-ones depth じゃ。

証明は軌道時刻を次の二枝へ分けている。

```text
height = 1:
  target は厳密に未来

height >= 2:
  target は現在時刻
```

odd orbit では height が常に正なので、この二分岐は完全である。

---

## fixed point の完全特徴づけ

```lean
orbitPaymentTarget_eq_self_iff_two_le_orbitWindowHeight
```

により、

$$
\tau(i)=i\Longleftrightarrow2\le h_i
$$

が確定した。

したがって target map の fixed point 集合は、正確に extra-height event 集合じゃ。

これは今後、payment endpoint を subtype 化する際の中心定理になる。

```lean
def PaymentEndpoint (n : OddNat) :=
  {j : ℕ // 2 ≤ orbitWindowHeight n j}
```

のような型へ自然に移せる。

---

## 一歩の target dynamics

今回追加された二本は非常に強い。

### Height-one step

```lean
orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one
```

$$
h_i=1\Longrightarrow\tau(i+1)=\tau(i)
$$

### Extra-height step

```lean
orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
```

$$
2\le h_i\Longrightarrow\tau(i)<\tau(i+1)
$$

つまり target sequence は、

```text
height-one:
  水平に進む

extra-height:
  次の target へ跳ぶ
```

という階段関数になった。

この二本から直ちに、

$$
\tau(i)\le\tau(i+1)
$$

が導ける。

したがって、次に明示的な theorem として、

```lean
theorem monotone_orbitPaymentTarget
    (n : OddNat) :
    Monotone (orbitPaymentTarget n)
```

を追加する価値が高い。

さらに完全分類として、

```lean
orbitPaymentTarget_succ_eq_iff_height_eq_one
orbitPaymentTarget_lt_succ_iff_height_two_le
```

も導ける。

---

## retraction の完成

```lean
orbitPaymentTarget_target
```

は、

$$
\tau(\tau(i))=\tau(i)
$$

を証明する。

target $j=\tau(i)$ は必ず extra-height endpoint なので、再度 target を取っても自分自身になる。

したがって `orbitPaymentTarget` は、

```text
全軌道時刻
  ↓
extra-height endpoint 集合
```

への retraction じゃ。

より完全には、

$$
\operatorname{Image}(\tau)=\operatorname{FixedPoints}(\tau)={j\mid2\le h_j}
$$

となる。

この構造があるため、payment block は人為的な分割ではない。

**target map の fiber として自然に生じる。**

---

## universal fiber の区間閉包

中心定理は、

```lean
orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart
```

じゃ。

非空 fiber に対して、

$$
\operatorname{Fiber}(j)=\operatorname{Icc}(b,j)
$$

が成立する。

証明は正しい。

### 順方向

fiber member $i$ なら、

- $i\le j$
- $b$ は fiber の最小元なので $b\le i$

したがって $i\in[b,j]$。

### 逆方向

$b\le i<j$ なら、$b$ から始まる既存 pre-payment chain によって exact depth が一段ずつ減る。

そのため target は変化せず、

$$
\tau(i)=j
$$

となる。

$i=j$ では endpoint が extra-height なので、

$$
\tau(j)=j
$$

じゃ。

cp-305 で保留された問題は、今回完全に閉じた。

---

## universal block 内部

```lean
orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
```

は、

$$
b\le i<j\Longrightarrow h_i=1
$$

を示す。

endpoint については既存 theorem により、

$$
2\le h_j
$$

じゃ。

したがって universal block は厳密に、

```text
[b, j):
  height one

j:
  extra height
```

という形になる。

これは maximal first-payment staircase そのものじゃ。

---

## exact-depth profile

```lean
orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
```

は block 全域について、

$$
A_i=j-i+1
$$

を証明した。

したがって block の exact-depth profile は、

$$
j-b+1,j-b,\ldots,3,2,1
$$

となる。

endpoint で深度 $1$。

一つ前で深度 $2$。

block start で最大深度 $j-b+1$ じゃ。

この結果から、すぐ次も得られる。

$$
\#\operatorname{Fiber}(j)=j-b+1=A_b
$$

つまり、

> universal fiber の cardinality は、block start の exact depth そのもの

である。

候補 theorem は、

```lean
orbitPaymentSourceFiberAt_card_eq_orbitExactDepth_universalStart
```

じゃ。

これは pressure の depth histogram へ接続する重要な API になる。

---

## 古い footer コメント

現在の `UniversalPaymentBlock.lean` 末尾には、まだ次の趣旨のコメントが残っている。

```text
fiber を interval と同定するには reverse closure が未証明
interval contiguity はまだ主張しない
```

しかし cp-306 では、その直前に既に、

```lean
orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart
```

が証明されている。

したがって source comment が現在の実装と矛盾している。

これは必ず更新すべきじゃ。

新しい frontier は、

```text
universal block geometry is closed
next:
  universal block ledger
  block-family enumeration
  finite-prefix coverage
  boundary suffix
```

となる。

---

## 検証 gate

report で明記されているのは、

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
git diff --check
```

の成功までじゃ。

前回指示にあった次の gate は、今回 report では確認できない。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
```

対象 module の build が通っているので実装上の危険は低いが、checkpoint handoff としては実行して report に追記すべきじゃ。

---

## 次の核心は debt block ではなく universal block ledger

ここが今回最も重要な一歩先推論じゃ。

cp-304 の block ledger は、

```lean
h : (floatGrowthDebtFiberAt n j).Nonempty
```

を要求している。

したがって delayed growth debt を持つ block だけが対象だった。

しかし cp-306 では、全ての payment endpoint に対して universal block が構成できる。

これにより次は、cp-304 theorem を debt block から transport するだけではなく、

> **全 universal payment block に対する ledger を直接証明すべき**

じゃ。

### なぜ直接 universal ledger が必要か

delayed growth debt を一つも持たない block も存在し得る。

そのような block は、

- interior に carry-two がない
- endpoint に immediate carry-two があるかもしれない
- あるいは carry-two claim が一つもない
- capacity surplus により width を減少させる可能性が高い

これらは大域 telescope に不可欠な下降 block じゃ。

debt-supported theorem だけでは、最も重要な返済側 block が抜け落ちる。

---

## universal claim fiber の完全同定

非空 universal fiber に対して、次が証明できる。

$$
i\in\operatorname{CarryTwoClaimFiber}(j)\Longleftrightarrow i\in[b,j]\land\operatorname{CarryTwoDebtAt}(n,i)
$$

### 左から右

claim が delayed なら、

- height one
- target $j$

なので universal fiber に属する。

claim が immediate なら $i=j$。

### 右から左

$i<j$ なら universal block interior なので height one。

carry-two と height oneから delayed claim になる。

$i=j$ なら endpoint は extra-height なので immediate claimになる。

これにより、

$$
Q_j=\#\{i\in[b,j]\mid c_i=2\}
$$

が全 universal block で成立する。

---

## universal block ledger

generic shifted ledger を $b$ から $j+1$ まで適用する。

interior の extra capacity はゼロで、endpoint capacity だけが残る。

したがって、全 payment endpoint について、

$$
w_{j+1}+P_j=w_b+Q_j
$$

が得られる。

この theorem は cp-304 の ledger を真に一般化する。

```lean
theorem bitWidth_iterateT_universalPaymentBlock_eq_claimFiber_card
```

のような名前がよい。

さらに signed form は、

$$
Q_j-P_j=w_{j+1}-w_b
$$

じゃ。

この universal theorem が完成すれば、debt-supported start $a$ との比較は compatibility theorem へ降格できる。

---

## proof 引数の整理

現在、

```lean
universalPaymentBlockStart n j h
```

は fiber nonempty の証明 `h` を引数に持つ。

単体 theorem では問題ないが、block family を作ると proof argument が頻繁に現れる。

ここで `PaymentEndpoint` subtype が有効じゃ。

```lean
def PaymentEndpoint (n : OddNat) :=
  {j : ℕ // 2 ≤ orbitWindowHeight n j}
```

endpoint $e$ に対し、$e$ 自身が fiber member なので、canonical nonempty proof を内部で作れる。

```lean
noncomputable def PaymentEndpoint.blockStart
    (e : PaymentEndpoint n) : ℕ :=
  universalPaymentBlockStart n e.1
    (by exact ⟨e.1, ...⟩)
```

これなら block-family の要素に毎回外部証明を渡さずに済む。

併せて、

$$
\operatorname{Fiber}(j)\ne\varnothing\Longleftrightarrow2\le h_j
$$

も証明するとよい。

順方向は既に存在する。

逆方向は endpoint 自身を fiber に入れればよい。

---

## payment endpoint sequence

universal target の dynamics から、canonical endpoint 列を定義できる。

最初の endpoint を、

$$
e_0=\tau(0)
$$

次を、

$$
e_{m+1}=\tau(e_m+1)
$$

とする。

extra-height endpoint $e_m$ の次時刻では target が厳密に進むため、

$$
e_m<e_{m+1}
$$

じゃ。

block は、

```text
first block:
  [0, e_0]

next block:
  [e_m + 1, e_{m+1}]
```

となる。

これにより universal fibers を任意 `Finset` として集めるのではなく、自然な時系列で列挙できる。

各 block は連続し、互いに素で、隙間を持たない。

有限 prefix が block の途中で切れた場合だけ、unfinished suffix が残る。

---

## pressure への接続

block $B=[b,j]$ の長さを、

$$
L=j-b+1
$$

とする。

cp-306 により block 内では exact depth が $L,L-1,\ldots,1$ と一度ずつ現れる。

したがって fixed depth $d$ に対して、

- recovery count は $L\ge d$ の block ごとに一つ
- continuation count は各 block から $\max(L-d,0)$ 個

となる。

有限 block family $\mathcal B$ について概念的には、

$$
E_d=#{B\in\mathcal B\mid d\le L_B}
$$

$$
C_d=\sum_{B\in\mathcal B}\max(L_B-d,0)
$$

となる。

よって pressure margin は、

$$
M_d=C_d-E_d
$$

として、完全に block-length histogram の量へ変換される。

これは cp-300 から探してきた Float / Pressure bridge の具体形じゃ。

ただし finite prefix の unfinished suffix contribution を必ず別項として残す必要がある。

---

## 判定まとめ

### target dynamics

**完成。**

### target retraction

**完成。**

### universal fiber interval closure

**完成。**

### maximal payment staircase

**完成。**

### exact-depth profile

**完成。**

### source footer

**要修正。古い未完説明が残っている。**

### validation

**追加 gate が必要。**

### universal block ledger

**次の最優先。**

### block-family partition

**直結可能。**

### pressure histogram bridge

**構造が明確に見えた。**

---

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge Float-window branch after
report-petal-306.

The cp-306 mathematics is accepted.

Universal payment coordinates now form a retraction onto extra-height
endpoints, and every nonempty target fiber is exactly one contiguous interval
with a descending exact-depth profile.

Before new implementation, correct the stale source footer and complete the
full validation gates.

# Immediate cleanup

Update the final module comment in:

    DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean

It still says fiber interval closure is missing. That statement is obsolete
after:

    orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart

Replace it with the current frontier:

    universal block geometry is complete;
    universal block accounting and finite block-family coverage remain.

Run and report:

    lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
    lake build DkMath.Collatz.PetalBridge.FloatWindow
    lake build DkMath.Collatz.PetalBridge
    lake build DkMath
    git diff --check

# Stage A — complete target dynamics API

Prove:

    orbitPaymentTarget n i <= orbitPaymentTarget n (i + 1)

and package:

    Monotone (orbitPaymentTarget n)

Also prove the exact cases:

    orbitPaymentTarget n (i + 1) = orbitPaymentTarget n i
      ↔ orbitWindowHeight n i = 1

    orbitPaymentTarget n i < orbitPaymentTarget n (i + 1)
      ↔ 2 <= orbitWindowHeight n i

Reuse the cp-306 equality and strict-growth theorems.

# Stage B — endpoint characterization

Prove:

    (orbitPaymentSourceFiberAt n j).Nonempty
      ↔ 2 <= orbitWindowHeight n j

The forward direction already exists.

For the reverse direction, use endpoint self-targeting.

Introduce a proof-carrying endpoint type when useful:

    def PaymentEndpoint (n : OddNat) :=
      {j : Nat // 2 <= orbitWindowHeight n j}

Provide a proof-independent block-start API on this subtype.

# Stage C — block cardinality and depth profile

For a nonempty universal fiber with start `b`, prove:

    (orbitPaymentSourceFiberAt n j).card = j - b + 1

and:

    (orbitPaymentSourceFiberAt n j).card =
      orbitExactDepth n b

Prove that every depth from `1` through the block length occurs exactly once in
the universal block.

These are the first direct block-length / depth-histogram bridge theorems.

# Stage D — universal claim-fiber identification

For every nonempty universal payment fiber, not only blocks containing delayed
growth debt, prove:

    i in carryTwoPaymentClaimFiberAt n j
      <->
    i in Finset.Icc b j and CarryTwoDebtAt n i

where:

    b = universalPaymentBlockStart n j h

Handle the two cases explicitly:

    i < j:
      universal interior height is one, hence carry two is delayed

    i = j:
      endpoint height is at least two, hence carry two is immediate

Derive the Finset equality and cardinality theorem.

# Stage E — universal endpoint capacity

Prove that all extra-height capacity in the universal block is concentrated at
its endpoint:

    extraPaymentCapacityOn n (Finset.Icc b j)
      =
    extraPaymentCapacityAt n j

Reuse:

    orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior

# Stage F — exact universal block ledger

Apply the generic shifted ledger directly from universal start `b` through
`j + 1`.

Prove for every nonempty universal fiber:

    bitWidth (iterateT (j + 1) n).1
        + extraPaymentCapacityAt n j
      =
    bitWidth (iterateT b n).1
        + (carryTwoPaymentClaimFiberAt n j).card

This theorem must not require:

    (floatGrowthDebtFiberAt n j).Nonempty

It must include blocks with no delayed carry-two debt, because those
capacity-surplus blocks are essential for cumulative decay.

Add the signed form:

    claim card - capacity
      =
    width after universal block - width before universal block

and the overload / balance / surplus trichotomy.

# Stage G — compatibility with the debt-supported block

Only after the direct universal ledger is complete, relate it to the cp-304
debt-supported theorem.

For endpoints with a nonempty delayed-growth debt fiber, prove that the prefix
between universal start `b` and debt start `a` has:

    height one
    carry one
    zero width drift

Then prove the universal and debt-supported block ledgers are compatible.

Do not use this restricted route as the definition of the universal ledger.

# Stage H — canonical endpoint sequence

Define the successive payment endpoints:

    e(0) = orbitPaymentTarget n 0
    e(k + 1) = orbitPaymentTarget n (e(k) + 1)

Prove:

    e(k) < e(k + 1)

and identify their blocks:

    first block = Icc 0 (e 0)
    next block  = Icc (e k + 1) (e (k + 1))

Prove consecutive blocks are disjoint and adjacent.

# Stage I — finite-prefix decomposition

For a finite orbit prefix, decompose it into:

    completed universal payment blocks
    plus one explicit unfinished height-one suffix

Do not discard the suffix or assume the prefix ends at a payment endpoint.

# Stage J — cumulative signed ledger

Sum the universal block signed drifts over all completed blocks.

Prove that internal bit widths telescope.

Add the unfinished suffix contribution explicitly and recover the existing
orbit-prefix width ledger.

# Stage K — block-length pressure bridge

For each completed universal block of length `L`, use the cp-306 profile:

    L, L - 1, ..., 2, 1

to prove finite-family formulas for:

    exact-depth recovery counts
    continuation counts
    source pressure margin

Preserve the unfinished suffix as a separate boundary term.

Do not infer ambient positive pressure until every completed block and the
boundary term are included.

# Autonomous continuation

The stages above are minimum targets, not stopping boundaries.

Continue while:

    universal ledgers include blocks with no delayed growth debt
    target fibers remain exact function fibers
    endpoint proofs do not create proof-argument friction
    block intervals are adjacent and disjoint
    incomplete suffixes remain explicit
    no sorry or axiom is introduced
    builds remain green

Stop only at a genuine mathematical obstruction or an unresolved API
dependency conflict.

Record the full continuation in:

    docs/dev/das-p2l-260607/review/report-petal-307.md
```

cp-306 によって、payment block の「形」は完全に閉じた。

次は、その全ての block に会計を載せ、軌道を block 列へ圧縮する段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
index c7f45140..de423879 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentBlock.lean
@@ -46,6 +46,63 @@ theorem orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
   have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 hheight
   omega
 
+/-- Every canonical payment target is at or after its source time. -/
+theorem le_orbitPaymentTarget
+    (n : OddNat) (i : ℕ) :
+    i ≤ orbitPaymentTarget n i := by
+  by_cases hheight : orbitWindowHeight n i = 1
+  · exact (lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hheight).le
+  · have htwo : 2 ≤ orbitWindowHeight n i := by
+      have hone := orbitWindowHeight_one_le n i
+      omega
+    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
+
+/-- A time is a target fixed point exactly when it is an extra-height event. -/
+theorem orbitPaymentTarget_eq_self_iff_two_le_orbitWindowHeight
+    (n : OddNat) (i : ℕ) :
+    orbitPaymentTarget n i = i ↔ 2 ≤ orbitWindowHeight n i := by
+  constructor
+  · intro htarget
+    by_contra hnot
+    have hone : orbitWindowHeight n i = 1 := by
+      have hpos := orbitWindowHeight_one_le n i
+      omega
+    have hlt := lt_orbitPaymentTarget_of_orbitWindowHeight_eq_one hone
+    omega
+  · exact orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+
+/-- A height-one step preserves its eventual canonical payment target. -/
+theorem orbitPaymentTarget_succ_eq_of_orbitWindowHeight_eq_one
+    {n : OddNat} {i : ℕ}
+    (hheight : orbitWindowHeight n i = 1) :
+    orbitPaymentTarget n (i + 1) = orbitPaymentTarget n i := by
+  have hdepth := (orbitWindowHeight_eq_one_iff_two_le_orbitExactDepth n i).1 hheight
+  have hexact : OrbitDepthRecoversExactlyAt n i (orbitExactDepth n i) := by rfl
+  by_cases hd2 : orbitExactDepth n i = 2
+  · have hnext : 2 ≤ orbitWindowHeight n (i + 1) := by
+      simpa [hd2] using
+        orbitDepthRecoversExactlyAt_delayed_height_two_le n i (orbitExactDepth n i)
+          hdepth hexact
+    rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hnext]
+    unfold orbitPaymentTarget
+    omega
+  · have hd3 : 3 ≤ orbitExactDepth n i := by omega
+    have hnextExact := orbitDepthRecoversExactlyAt_succ_of_three_le
+      n i (orbitExactDepth n i) hd3 hexact
+    have hnextDepth : orbitExactDepth n (i + 1) = orbitExactDepth n i - 1 := by
+      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth] using hnextExact
+    unfold orbitPaymentTarget
+    omega
+
+/-- An extra-height step moves strictly to a later canonical payment target. -/
+theorem orbitPaymentTarget_lt_succ_of_two_le_orbitWindowHeight
+    {n : OddNat} {i : ℕ}
+    (hheight : 2 ≤ orbitWindowHeight n i) :
+    orbitPaymentTarget n i < orbitPaymentTarget n (i + 1) := by
+  rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight hheight]
+  have hle := le_orbitPaymentTarget n (i + 1)
+  omega
+
 /-- Every orbit time targets a genuine extra-height payment slot. -/
 theorem two_le_orbitWindowHeight_orbitPaymentTarget
     (n : OddNat) (i : ℕ) :
@@ -61,6 +118,13 @@ theorem two_le_orbitWindowHeight_orbitPaymentTarget
     rw [orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight htwo]
     exact htwo
 
+/-- Canonical payment targets are fixed points of the target map. -/
+theorem orbitPaymentTarget_target
+    (n : OddNat) (i : ℕ) :
+    orbitPaymentTarget n (orbitPaymentTarget n i) = orbitPaymentTarget n i := by
+  apply orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+  exact two_le_orbitWindowHeight_orbitPaymentTarget n i
+
 /-- All sources at most `j` whose canonical payment target is `j`. -/
 noncomputable def orbitPaymentSourceFiberAt (n : OddNat) (j : ℕ) : Finset ℕ := by
   classical
@@ -157,6 +221,113 @@ theorem universalPaymentBlockStart_le_floatPaymentBlockStart
   exact mem_orbitPaymentSourceFiberAt_of_mem_floatGrowthDebtFiberAt
     (floatPaymentBlockStart_mem_growthDebtFiber n j h)
 
+/--
+Every strict interior point after a universal block start has the endpoint as
+its canonical payment target.
+-/
+theorem orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt
+    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
+    (hstart : universalPaymentBlockStart n j h ≤ i) (hij : i < j) :
+    orbitPaymentTarget n i = j := by
+  let b := universalPaymentBlockStart n j h
+  have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
+  have hbtarget : orbitPaymentTarget n b = j :=
+    (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
+  have hbj : b < j := lt_of_le_of_lt hstart hij
+  have hdepth : 2 ≤ orbitExactDepth n b := by
+    unfold orbitPaymentTarget at hbtarget
+    omega
+  have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
+  rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
+      hdepth hexact with ⟨hchain, _⟩
+  have hoff : i - b < orbitExactDepth n b - 1 := by
+    unfold orbitPaymentTarget at hbtarget
+    dsimp [b] at hstart hbj hbtarget ⊢
+    omega
+  have hiExact := (hchain (i - b) hoff).1
+  have hdepthi : orbitExactDepth n i = orbitExactDepth n b - (i - b) := by
+    simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
+      show b + (i - b) = i by omega] using hiExact
+  unfold orbitPaymentTarget at hbtarget ⊢
+  dsimp [b] at hstart hbj hdepthi hbtarget ⊢
+  omega
+
+/-- A nonempty universal source fiber is exactly its minimum-to-endpoint interval. -/
+theorem orbitPaymentSourceFiberAt_eq_Icc_universalPaymentBlockStart
+    (n : OddNat) (j : ℕ) (h : (orbitPaymentSourceFiberAt n j).Nonempty) :
+    orbitPaymentSourceFiberAt n j =
+      Finset.Icc (universalPaymentBlockStart n j h) j := by
+  ext i
+  constructor
+  · intro hi
+    rcases mem_orbitPaymentSourceFiberAt_iff.mp hi with ⟨hij, _⟩
+    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hi, hij⟩
+  · intro hi
+    rcases Finset.mem_Icc.mp hi with ⟨hstart, hij⟩
+    rw [mem_orbitPaymentSourceFiberAt_iff]
+    constructor
+    · exact hij
+    · rcases hij.eq_or_lt with rfl | hijlt
+      · exact orbitPaymentTarget_eq_self_of_two_le_orbitWindowHeight
+          (two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h)
+      · exact orbitPaymentTarget_eq_endpoint_of_universalStart_le_lt hstart hijlt
+
+/-- Strict universal-block interior points have exact observed height one. -/
+theorem orbitWindowHeight_eq_one_of_mem_universalPaymentBlockInterior
+    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
+    (hi : i ∈ Finset.Ico (universalPaymentBlockStart n j h) j) :
+    orbitWindowHeight n i = 1 := by
+  rcases Finset.mem_Ico.mp hi with ⟨hstart, hij⟩
+  let b := universalPaymentBlockStart n j h
+  have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
+  have hbtarget : orbitPaymentTarget n b = j :=
+    (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
+  have hdepth : 2 ≤ orbitExactDepth n b := by
+    unfold orbitPaymentTarget at hbtarget
+    dsimp [b] at hstart hij hbtarget ⊢
+    omega
+  have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
+  rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
+      hdepth hexact with ⟨hchain, _⟩
+  have hoff : i - b < orbitExactDepth n b - 1 := by
+    unfold orbitPaymentTarget at hbtarget
+    dsimp [b] at hstart hij hbtarget ⊢
+    omega
+  simpa [show b + (i - b) = i by omega] using (hchain (i - b) hoff).2
+
+/-- The exact-depth profile on a universal payment block is the descending staircase to one. -/
+theorem orbitExactDepth_eq_endpoint_sub_add_one_of_mem_universalPaymentBlock
+    {n : OddNat} {j i : ℕ} {h : (orbitPaymentSourceFiberAt n j).Nonempty}
+    (hi : i ∈ Finset.Icc (universalPaymentBlockStart n j h) j) :
+    orbitExactDepth n i = j - i + 1 := by
+  rcases Finset.mem_Icc.mp hi with ⟨hstart, hij⟩
+  rcases hij.eq_or_lt with rfl | hijlt
+  · have htwo := two_le_orbitWindowHeight_of_orbitPaymentSourceFiberAt_nonempty h
+    have hdepth := (two_le_orbitWindowHeight_iff_orbitExactDepth_eq_one n i).1 htwo
+    omega
+  · let b := universalPaymentBlockStart n j h
+    have hbmem := universalPaymentBlockStart_mem_sourceFiber n j h
+    have hbtarget : orbitPaymentTarget n b = j :=
+      (mem_orbitPaymentSourceFiberAt_iff.mp hbmem).2
+    have hdepth : 2 ≤ orbitExactDepth n b := by
+      unfold orbitPaymentTarget at hbtarget
+      dsimp [b] at hstart hijlt hbtarget ⊢
+      omega
+    have hexact : OrbitDepthRecoversExactlyAt n b (orbitExactDepth n b) := by rfl
+    rcases orbitDepthRecoversExactlyAt_prePayment_chain n b (orbitExactDepth n b)
+        hdepth hexact with ⟨hchain, _⟩
+    have hoff : i - b < orbitExactDepth n b - 1 := by
+      unfold orbitPaymentTarget at hbtarget
+      dsimp [b] at hstart hijlt hbtarget ⊢
+      omega
+    have hiExact := (hchain (i - b) hoff).1
+    have hdepthi : orbitExactDepth n i = orbitExactDepth n b - (i - b) := by
+      simpa [OrbitDepthRecoversExactlyAt, orbitExactDepth,
+        show b + (i - b) = i by omega] using hiExact
+    unfold orbitPaymentTarget at hbtarget
+    dsimp [b] at hstart hijlt hbtarget hdepthi ⊢
+    omega
+
 /-!
 ## Next closure requirement
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-306.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-306.md
new file mode 100644
index 00000000..9a5d13f0
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-306.md
@@ -0,0 +1,42 @@
+# cp-306 Universal Payment Block Closure
+
+## Closed result
+
+The cp-305 boundary was not a logical obstruction.  Applying the existing
+forward exact-depth staircase theorem to the minimum source in a nonempty
+universal fiber proves interval closure.
+
+For a nonempty `orbitPaymentSourceFiberAt n j`, Lean now proves:
+
+```text
+fiber(j) = Icc (universalPaymentBlockStart n j h) j
+```
+
+Every strict interior point has height one.  The endpoint has height at least
+two.  The exact-depth profile throughout the closed block is:
+
+```text
+orbitExactDepth n i = j - i + 1
+```
+
+for every `i` in that interval.
+
+## Target dynamics
+
+The target map has also been strengthened:
+
+- `i <= orbitPaymentTarget n i`;
+- targets are fixed points under a second target application;
+- fixed points are exactly extra-height times;
+- a height-one step preserves its target;
+- an extra-height step moves to a strictly later target.
+
+These facts establish the canonical target as a retraction onto its
+extra-height endpoint image.
+
+## Scope
+
+The new result is a single universal payment-block geometry theorem.  It does
+not yet provide finite-family coverage, a cumulative block ledger, or a
+pressure conclusion.  Those require explicit handling of successive target
+fibers and unfinished boundary suffixes.
````
`````
