# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge

gch: 491957fd6022fc7feaec022667ffaf4f312fc076

## Report

cp-303 では block reindexing の基礎を追加しました。

[PaymentBlockBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean) に以下を固定しています。

- `orbitWindowHeight (iterateT a n) t = orbitWindowHeight n (a + t)`
- `extraPaymentCapacityOn` による有限 source set 上の capacity
- debt-supported block の endpoint 算術
  - `a + (j + 1 - a) = j + 1`
  - shifted `Ico` が canonical `Icc a j` と一致

これで recursive prefix ledger と global block interval を接続する座標系は揃いました。

残る本質は二つの有限 reindexing 定理です。

- shifted carry-two count = global block の carry-two filter card
- shifted extra-height sum = endpoint `j` の extra capacity

これらが通れば、block width balance、overload と block growth の同値、credit/decrease 分岐へ進めます。debt-supported suffix と maximal staircase は引き続き分離しています。

結果は [report-petal-303.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-303.md) に記録しました。対象モジュール、`PetalBridge`、トップレベル `DkMath`、`git diff --check` は通過し、新規変更に `sorry` / `axiom` はありません。

## Review

## 結論

**実装内容は採用。だが停止地点は早すぎる。**

追加された三つの基礎 API は正しく、block reindexing の座標系は揃った。

```lean
orbitWindowHeight_shift_eq
extraPaymentCapacityOn
floatPaymentBlock_Ico_eq_withEndpoint
```

しかし Codex 自身が、

```text
残っているのは semantic gap ではなく、有限 count / sum の transport
```

と認識している。

これは「真正な行き止まり」ではない。今回の自律継続方針なら、そのまま二つの reindexing theorem、block ledger、overload と width growth の同値まで進むべきだった。

したがって判定は、

```text
数学・実装:
  採用

自律推進:
  不足。次 checkpoint へ切る必然性なし
```

じゃ。

添付報告では対象モジュール、`PetalBridge`、トップレベル `DkMath`、`git diff --check` が通り、新規 `sorry` / `axiom` なしとされている。

## 1. shifted height theorem

```lean
theorem orbitWindowHeight_shift_eq
    (n : OddNat) (a t : ℕ) :
    orbitWindowHeight (iterateT a n) t =
      orbitWindowHeight n (a + t)
```

これは必要十分な座標輸送じゃ。

意味は、

$$
h_t(T^a(n))=h_{a+t}(n)
$$

である。

既存の、

```lean
orbitWindowHeight_eq_s_iterateT
iterateT_add_eq_iterateT_from_shift
```

だけで閉じており、重複した帰納を作っていない。

今後、

```text
shifted prefix 上の recursive count
```

を、

```text
元の軌道上の区間 [a,a+len)
```

へ戻すための中心 rewrite になる。

**採用。**

## 2. `extraPaymentCapacityOn`

```lean
noncomputable def extraPaymentCapacityOn
    (n : OddNat) (S : Finset ℕ) : ℕ :=
  ∑ i ∈ S, orbitWindowHeight n i - 1
```

これは安全な一般化じゃ。

任意の有限時刻集合 $S$ に対し、

$$
E(S)=\sum_{i\in S}(h_i-1)
$$

を定義している。

以前、任意 `Finset` 上の localized pressure を先に作ることには注意が必要だと述べたが、この定義は pressure ではない。

- recovery を恣意的に捨てていない
- positive margin を主張していない
- 単に exact extra-height capacity を加算している

したがって任意 `Finset` 上に置いて問題ない。

ただし theorem 名では、単なる「capacity」より、

```text
extra-height capacity
```

であることを維持した方が意味が明瞭じゃ。

## 3. endpoint arithmetic

```lean
floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
```

は、$a<j$ を使って、

$$
a+(j+1-a)=j+1
$$

を固定した。

Nat subtraction を含むため、この補題を明示したのは良い。

以後の theorem で毎回 `omega` に endpoint arithmetic を解かせずに済む。

## 4. `Ico` と `Icc` の一致

```lean
floatPaymentBlock_Ico_eq_withEndpoint
```

は、

$$
[a,a+(j+1-a))=[a,j]
$$

を `Finset` 上で固定する。

すなわち、

$$
\operatorname{Ico}(a,j+1)=\operatorname{Icc}(a,j)
$$

じゃ。

これにより shifted ledger の半開区間と、canonical block の endpoint-inclusive interval が正確に一致した。

この theorem も正しい。

## 5. cp-303 で揃った座標系

現在、次の三つが接続された。

```text
shifted recursive index:
  t = 0,1,...,len-1

global orbit index:
  a+t

canonical block index:
  i ∈ Icc a j
```

対応関係は、

$$
i=a+t
$$

$$
0\le t<j+1-a
$$

$$
a\le i\le j
$$

じゃ。

したがって、残る count / sum reindexing は技術的には一本道である。

## 6. 残る carry count reindexing

目標は、

$$
\operatorname{shiftedOrbitCarryTwoCount}(n,a,\ell)=#{i\in[a,a+\ell)\mid c_i=2}
$$

じゃ。

`orbitWindowUpperCarryCountEqTwo` は再帰的に、

```lean
count k + if carry at iterateT k = 2 then 1 else 0
```

と定義されている。

右辺の `Finset.Ico` filter も、区間末尾を一つ追加すると同じ再帰になる。

したがって `len` 帰納で素直に閉じる。

必要な輸送は、

```lean
iterateT_add_eq_iterateT_from_shift
```

だけじゃ。

これは数学的障害ではない。

## 7. 残る extra-height sum reindexing

目標は、

$$
\operatorname{shiftedExtraPaymentCapacity}(n,a,\ell)=\sum_{i=a}^{a+\ell-1}(h_i-1)
$$

じゃ。

左辺の `sumExtraHeight` は、

```lean
sumExtraHeight n (k + 1)
  =
sumExtraHeight n k + (s (iterateT k n) - 1)
```

という再帰を持つ。

右辺も `Ico` の末尾追加で同じ再帰になる。

ここでは今回追加された、

```lean
orbitWindowHeight_shift_eq
```

が直接使える。

これも `len` 帰納で閉じるはずじゃ。

## 8. block endpoint capacity

block interior では既に、

$$
a\le i<j\Longrightarrow h_i=1
$$

が証明されている。

したがって、

$$
h_i-1=0
$$

じゃ。

endpoint だけが残り、

$$
\sum_{i=a}^{j}(h_i-1)=h_j-1
$$

となる。

つまり、

$$
\operatorname{extraPaymentCapacityOn}(n,[a,j])=\operatorname{extraPaymentCapacityAt}(n,j)
$$

である。

この証明も本質的には `Finset.sum_eq_single j`、または interior / endpoint 分割で閉じる。

## 9. exact block ledger

二つの reindexing が通れば、既存 shifted ledger から直ちに、

$$
w_{j+1}+(h_j-1)=w_a+\#Q_j
$$

を得る。

ここで $Q_j$ は complete carry-two claim fiber じゃ。

Lean の形では、

```lean
bitWidth (iterateT (j + 1) n).1
    + extraPaymentCapacityAt n j
  =
bitWidth (iterateT a n).1
    + (carryTwoPaymentClaimFiberAt n j).card
```

となる。

これが cp-302 から待っている中心定理じゃ。

## 10. overload / balance / credit

block ledger から、三分岐が完全に出る。

### Overload

$$
h_j-1<\#Q_j\Longleftrightarrow w_a<w_{j+1}
$$

### Balance

$$
h_j-1=\#Q_j\Longleftrightarrow w_a=w_{j+1}
$$

### Credit

$$
\#Q_j<h_j-1\Longleftrightarrow w_{j+1}<w_a
$$

これは一歩ごとの width drift を、payment cycle 一個の drift へ圧縮したものじゃ。

```text
claims > capacity:
  block growth

claims = capacity:
  block preservation

claims < capacity:
  block decrease
```

ここまでが一つの自然な checkpoint であり、cp-303 の追加だけで止める場所ではなかった。

## 11. さらに見えた統一――payment target は全時刻に使える

ここが今回の一歩先推論じゃ。

現在の、

```lean
floatDebtPaymentTarget n i :=
  i + orbitExactDepth n i - 1
```

は名前上は Float debt 専用だが、式自体は全軌道時刻に対して意味を持つ。

odd state では、次の二分岐が期待できる。

$$
h_i=1\Longleftrightarrow 2\le A_i
$$

$$
2\le h_i\Longleftrightarrow A_i=1
$$

ここで、

$$
A_i=\operatorname{ResidualAllOnesDepth}(\operatorname{oddOrbitLabel}(n,i))
$$

じゃ。

したがって payment target、

$$
\tau(i)=i+A_i-1
$$

は、

```text
height = 1:
  将来の最初の payment endpoint

height >= 2:
  A_i = 1 なので target = i
```

となる。

つまり `floatDebtPaymentTarget` は、本質的には debt 専用ではなく、

> **全軌道時刻に対する canonical payment target**

である可能性が高い。

## 12. universal target fiber

この一般化が通れば、endpoint $j$ に対して、

```lean
orbitPaymentSourceFiberAt n j
```

を、

$$
\{i\le j\mid\tau(i)=j\}
$$

として定義できる。

この fiber は carry に依存しない。

- carry-one / height-one source
- carry-two / height-one debt
- endpoint 自身

を全て含む。

その最小値を $b$ とすれば、

```text
[b,j):
  maximal height-one staircase

j:
  height >= 2
```

となる。

現在の debt-supported start $a$ とは、

$$
b\le a
$$

である。

さらに $[b,a)$ に carry-two があれば、それは $a$ より早い debt source になるため矛盾する。

したがって、

$$
b\le i<a\Longrightarrow c_i=1
$$

かつ、

$$
b\le i<a\Longrightarrow h_i=1
$$

なので、

$$
w_b=w_a
$$

となる。

これは、現在の debt-supported block ledger を maximal staircase 全体へ無損失で拡張する橋になる。

## 13. 実装上の軽微な注意

### `h` への依存

```lean
floatPaymentBlockStart n j h
```

は `Finset.Nonempty` の証明 `h` を引数に持つ。

Lean の proof irrelevance により数学的値は同じだが、異なる証明引数を持つ block API を比較する段階で rewrite が煩雑になる可能性がある。

必要になった時点で、

```lean
floatPaymentBlockStart_proof_irrel
floatPaymentBlockInterior_proof_irrel
floatPaymentBlockWithEndpoint_proof_irrel
```

のような補題を用意すればよい。

今すぐ変更する必要はない。

### report の表現

report の、

```text
残る本質は二つの有限 reindexing 定理
```

は不正確じゃ。

正しくは、

```text
残る作業は二つの有限 reindexing 定理
```

である。

本質的な数学 Gap ではない。

## 14. 判定

### コード

**採用。**

追加された補題はいずれも次の ledger に必要で、設計も正しい。

### 数学

**新しい主定理はまだ増えていない。**

今回の役割は座標変換 API の整備じゃ。

### 停止判断

**不採用。早すぎる。**

真正な障害がないまま、薄い transport 層の途中で切れている。

### 次の攻め筋

```text
generic reindexing
  ↓
block-specialized count / capacity
  ↓
exact block ledger
  ↓
overload / balance / credit
  ↓
universal payment target
  ↓
maximal staircase
```

じゃ。

## 15. 次の Codex 指示

````text
You are continuing the DkMath Collatz / PetalBridge Float-window branch after
report-petal-303.

The cp-303 additions are accepted:

```text
shifted orbit-height transport
finite-set extra-height capacity
payment-block endpoint arithmetic
Ico/Icc block interval identification
```

However, cp-303 stopped before a genuine obstruction. The remaining count and
sum transports are routine finite reindexing work and are not a checkpoint
boundary.

Continue autonomously through the exact block ledger, the overload trichotomy,
and the universal payment-target / maximal-staircase layer when the proofs
close.

# Primary file

Continue in:

```text
DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
```

Split out a generic reindexing module only when the declarations are useful
outside PaymentBlockBridge.

# Stage A — shifted carry-two count reindexing

Prove a reusable theorem equivalent to:

```lean
shiftedOrbitCarryTwoCount n a len =
  (carryTwoPositions n (Finset.Ico a (a + len))).card
```

Use induction on `len`.

At the successor step, expose the final global index `a + len` explicitly and
reuse:

```lean
iterateT_add_eq_iterateT_from_shift
```

Do not leave this as a report-only boundary.

# Stage B — shifted extra-height sum reindexing

Prove:

```lean
shiftedExtraPaymentCapacity n a len =
  extraPaymentCapacityOn n (Finset.Ico a (a + len))
```

Use induction on `len` and:

```lean
orbitWindowHeight_shift_eq
```

Keep Nat subtraction as the exact quantity `height - 1`; do not convert to
integers unless needed for a later signed drift theorem.

# Stage C — block-specialized carry count

For:

```text
a = floatPaymentBlockStart n j h
len = j + 1 - a
```

prove:

```lean
shiftedOrbitCarryTwoCount n a len =
  (carryTwoPaymentClaimFiberAt n j).card
```

Use:

```lean
floatPaymentBlock_Ico_eq_withEndpoint
carryTwoPaymentClaimFiberAt_card_eq_floatPaymentBlockWithEndpoint_carryTwo_card
```

# Stage D — block-specialized capacity

Prove:

```lean
shiftedExtraPaymentCapacity n a len =
  extraPaymentCapacityAt n j
```

First identify the shifted sum with:

```lean
extraPaymentCapacityOn n (floatPaymentBlockWithEndpoint n j h)
```

Then show that every interior contribution is zero and the endpoint
contribution is exactly:

```text
orbitWindowHeight n j - 1
```

Reuse:

```lean
orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
two_le_orbitWindowHeight_floatPaymentBlock_endpoint
```

# Stage E — exact payment-block balance

Prove the subtraction-free theorem:

```lean
bitWidth (iterateT (j + 1) n).1
    + extraPaymentCapacityAt n j
  =
bitWidth (iterateT (floatPaymentBlockStart n j h) n).1
    + (carryTwoPaymentClaimFiberAt n j).card
```

Also provide an integer drift form when it gives a clean reusable API:

```text
width after block - width before block
  =
claim count - capacity
```

# Stage F — overload trichotomy

Prove:

```lean
CarryTwoPaymentOverloadAt n j
  <->
bitWidth (iterateT (floatPaymentBlockStart n j h) n).1 <
  bitWidth (iterateT (j + 1) n).1
```

Also prove the exact balance and credit branches:

```text
claim card = capacity
  <->
block width preserved

claim card < capacity
  <->
block width decreases
```

A bundled trichotomy theorem is encouraged.

# Stage G — universal payment target

Audit the stronger fact suggested by the current exact-depth API.

Prove the equivalences:

```text
orbitWindowHeight n i = 1
  <->
2 <= orbitExactDepth n i

2 <= orbitWindowHeight n i
  <->
orbitExactDepth n i = 1
```

Reuse the existing mod-four and residual-all-ones-depth characterizations.

Introduce a semantic alias when appropriate:

```lean
orbitPaymentTarget n i :=
  i + orbitExactDepth n i - 1
```

The existing `floatDebtPaymentTarget` may remain as a compatibility alias.

Prove:

```text
height = 1 -> i < orbitPaymentTarget n i
height >= 2 -> orbitPaymentTarget n i = i
```

and prove that every time targets an actual payment slot.

# Stage H — universal payment-source fiber

Define the complete source fiber:

```text
orbitPaymentSourceFiberAt n j =
  { i in Finset.range (j + 1) | orbitPaymentTarget n i = j }
```

For an endpoint with a nonempty delayed-growth debt fiber, prove that this
universal fiber is nonempty and contains `j`.

Let its minimum be the maximal staircase start `b`.

Prove that the universal target fiber is exactly a contiguous block:

```text
orbitPaymentSourceFiberAt n j = Finset.Icc b j
```

or prove the corresponding membership equivalence first.

Expose:

```text
for b <= t < j:
  height(t) = 1

at j:
  height(j) >= 2
```

# Stage I — relate maximal staircase to debt-supported suffix

Let:

```text
a = floatPaymentBlockStart n j h
b = universal payment-block start
```

Prove:

```text
b <= a
```

and:

```text
for b <= t < a:
  height(t) = 1
  carry(t) = 1
```

Therefore prove:

```text
bitWidth (iterateT b n).1 =
  bitWidth (iterateT a n).1
```

This transports the exact debt-supported block ledger to the full maximal
payment staircase without changing its drift.

# Stage J — pressure preparation

Use the universal maximal staircase, not only the debt-supported suffix, for
exact-depth profiles.

Expose:

```text
at time b + t:
  orbitExactDepth = j - (b + t) + 1
```

for the interior.

Investigate how universal payment-block lengths contribute to:

```lean
orbitDepthRecoveryFiberCount
orbitDepthContinuationFiberCount
sourcePressureMarginInt_eq_continuationFiber_sub_recoveryFiber
```

Do not infer ambient positive pressure by dropping unrelated blocks.

# Autonomous continuation

The stages above are minimum directions, not stopping boundaries.

Continue while:

```text
all statements follow from current Lean facts
finite reindexing is completed rather than reported as an obstruction
debt-supported and universal maximal blocks remain distinct
claim count is not confused with final allocation
all interval endpoints are explicit
no sorry or axiom is introduced
builds remain green
```

Stop only at a genuine logical obstruction or an unresolved API dependency
conflict.

# Validation

Run:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

Record the full autonomous continuation in:

```text
docs/dev/das-p2l-260607/review/report-petal-304.md
```
````

cp-303 の三補題は正しい。

だが、ここは橋脚を一本立てたところで止まっておる。次は橋を渡り切り、block 一個の width 会計を閉じるところまで一気に進むべきじゃ。

## Issue / re-review

# 最新 snapshot 徹底検証

## 結論

**わっちの前回レビューにも問題があった。**

数学的な見立て、

```text
残っているのは本質的障害ではなく有限 reindexing
```

自体は正しい。

しかし実装指示では、

```text
recursive prefix count
  -> global Finset.Ico filter card
```

を直接つなぐ経路へ寄せすぎた。

そのため Codex は、

- recursive count の successor 展開
- `Finset.Ico` の右端追加
- `filter` の更新
- `card` の更新
- shifted index の輸送

を一度に処理することになった。

これは Lean にとって不必要に難しい正規形じゃ。

**Codex が未完成 theorem を削除して green に戻した判断は正しい。**
一方で、数学的には別表現を選べば先へ進める。停止理由は数学的行き止まりではなく、証明表現の選択ミスじゃ。

---

## snapshot 検証結果

指定された最新 snapshot を直接検査した。

```text
19752c9b3cba9cc8e36e6d69237d9a4cb6ad08e9700f60ad6f0ee491863f9b5d
__snapshot-dk_math-lean-code-260713-0213.tar.gz
```

実ファイルの SHA-256 は、指定値および `.sha256` ファイルと完全一致した。

展開先の実体は、

```text
dk_math/
  DkMath/
  DkMath.lean
  lake-manifest.json
  lean-toolchain
  docs/
```

という Lean package root だった。

### FloatWindow の現在量

最新 snapshot には次の九ファイルがある。

```text
Core.lean
WidthBalance.lean
DyadicFloat.lean
OrbitBalance.lean
PatternLedger.lean
DriftBridge.lean
PressureIncidenceBridge.lean
PaymentMultiplicityBridge.lean
PaymentBlockBridge.lean
```

合計は 2011 行。

`PaymentBlockBridge.lean` は 314 行で、

- `def` 7件
- `theorem` 19件

を持つ。

`FloatWindow.lean` から全九モジュールが公開され、さらに、

```lean
DkMath.Collatz.PetalBridge.lean
```

から `FloatWindow` が import されている。

### sorry / axiom

次の範囲を直接検索した。

```text
DkMath/Collatz/PetalBridge/FloatWindow/
DkMath/Collatz/PetalBridge/FloatWindow.lean
```

結果は、

```text
sorry: 0
axiom: 0
unsafe declaration: 0
```

だった。

### build の再検証について

この検査環境には `lake` と `lean` の実行ファイルがないため、わっち自身による再 build は行えなかった。

したがって build について確認できるのは、

- 添付 report の green 報告
- snapshot が未完成 theorem を含まないこと
- import surface と依存関係に破綻が見えないこと

までじゃ。

cp-303 report でも、残件は semantic gap ではなく finite card / sum transport だと明記されている。

---

## snapshot に残っている実装

今回の試作で失敗した theorem は snapshot には残っていない。

`PaymentBlockBridge.lean` の末尾は、次の four-piece で止まっている。

```lean
theorem orbitWindowHeight_shift_eq
noncomputable def extraPaymentCapacityOn
theorem floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
theorem floatPaymentBlock_Ico_eq_withEndpoint
```

その後に既存の、

```lean
shiftedOrbitCarryTwoCount
shiftedExtraPaymentCapacity
bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
```

がある。

つまり現在は、

```text
shifted prefix ledger: 完成
global block interval: 完成
両者の count/sum transport: 未完成
```

という、報告どおりの状態じゃ。

また、snapshot 内には、

```text
__next_implementation.md
```

は存在しなかった。

これは Codex の作業用・外部指示用ファイルであり、snapshot に保存されるリポジトリ成果物ではなかったと見られる。

---

## Codex が詰まった正確な理由

### recursive count の形

`orbitWindowUpperCarryCountEqTwo` は `Finset` ではなく、自然数再帰で定義されている。

```lean
noncomputable def orbitWindowUpperCarryCountEqTwo : OddNat → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 =>
      orbitWindowUpperCarryCountEqTwo n k +
        if stateUpperCarry (iterateT k n).1 = 2 then 1 else 0
```

これは offset 座標、

```text
0, 1, ..., len - 1
```

に自然に対応する。

一方、わっちが直接要求した右辺は、

```lean
carryTwoPositions n (Finset.Ico a (a + len))
```

であり、最初から global 座標、

```text
a, a + 1, ..., a + len - 1
```

を使っている。

### 一度に必要となった変換

帰納法の successor step では、次を全て同時に処理する必要があった。

```text
iterateT len (iterateT a n)
  =
iterateT (a + len) n
```

```text
Ico a (a + len + 1)
  =
insert (a + len) (Ico a (a + len))
```

```text
filter predicate at a + len
```

```text
filtered Finset card の +1 / +0
```

ところが `Ico` の右端追加は、simp や interval 正規化の途中で `Icc` 表現へ変わり得る。

そこで Codex が書いた step lemma の左辺と、Lean が生成した目標の interval 表現が一致しなくなった。

Mathlib では `Finset.range n` が正確に `0` から `n-1` の集合として設計され、`List.range_succ` も末尾 `n` の追加として公開されている。再帰 count の証明は、この局所 offset 表現へ合わせるのが自然じゃ。([Leanコミュニティ][1])

---

## わっちのレビューで悪かった点

### 1. `Ico` を早く持ち込みすぎた

前回の指示は、

```lean
shiftedOrbitCarryTwoCount n a len =
  (carryTwoPositions n (Finset.Ico a (a + len))).card
```

を直接要求した。

数学的には正しい。

しかし Lean 実装としては、一段中間層を挟むべきだった。

正しい順番は、

```text
recursive count
  -> local offset Finset.range count
  -> translation by t ↦ a + t
  -> global interval count
```

じゃ。

### 2. 「routine」と判定しながら実装核を示さなかった

わっちは「薄い transport」と評価した。

それ自体は正しいが、薄い transport にも **適切な正規形** がある。

今回はそれを指定せず、

```text
Ico の右端更新を証明せよ
```

という不安定な道へ押してしまった。

### 3. Stage G 以降まで一度に積みすぎた

指示には、

- reindexing
- block ledger
- overload trichotomy
- universal target
- maximal staircase
- pressure preparation

まで入れていた。

Codex を止めない方針は正しいが、最初の proof engineering に必要な焦点が薄くなった。

ブレーキを掛ける必要はない。

ただし、**最初に攻略すべき表現変更**は明確に示すべきだった。

---

## 正しい実装経路

`Finset.Ico` を直接帰納しない。

まず local offset set を置く。

```lean
noncomputable def shiftedCarryTwoOffsets
    (n : OddNat) (a len : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range len).filter fun t =>
    CarryTwoDebtAt n (a + t)
```

そして最初の theorem を、次にする。

```lean
theorem shiftedOrbitCarryTwoCount_eq_offset_card
    (n : OddNat) (a len : ℕ) :
    shiftedOrbitCarryTwoCount n a len =
      (shiftedCarryTwoOffsets n a len).card := by
  ...
```

この帰納では右辺が `Finset.range len` なので、recursive count と同じ末尾 `len` が現れる。

$$
\operatorname{range}(len+1)=\operatorname{range}(len)\cup{len}
$$

global index への変換は、その後に別定理として行う。

```lean
theorem shiftedCarryTwoOffsets_card_eq_global_Ico
    (n : OddNat) (a len : ℕ) :
    (shiftedCarryTwoOffsets n a len).card =
      (carryTwoPositions n (Finset.Ico a (a + len))).card := by
  ...
```

ここでは帰納法ではなく、写像、

$$
t\longmapsto a+t
$$

による有限集合の全単射を使う。

逆写像は、

$$
i\longmapsto i-a
$$

じゃ。

これなら interval の successor 更新は一切不要になる。

---

## extra-height 側も同様

local offset sum を先に証明する。

```lean
theorem shiftedExtraPaymentCapacity_eq_sum_range
    (n : OddNat) (a len : ℕ) :
    shiftedExtraPaymentCapacity n a len =
      ∑ t in Finset.range len, orbitWindowHeight n (a + t) - 1 := by
  ...
```

これは `len` 帰納で、

```lean
orbitWindowHeight_shift_eq
```

を使えばよい。

次に global interval へ移す必要すらない。

block 専用 theorem では、local offset のまま endpoint contribution を取り出せる。

block start を $a$、長さを、

$$
\ell=j+1-a
$$

と置く。

最後の offset は、

$$
\ell-1=j-a
$$

であり、

$$
a+(\ell-1)=j
$$

じゃ。

それ以前の offset では、

$$
a+t<j
$$

なので interior height theorem から contribution はゼロ。

$$
h_{a+t}-1=0
$$

最後だけが、

$$
h_j-1
$$

を与える。

したがって、

$$
\sum_{t<\ell}(h_{a+t}-1)=h_j-1
$$

が直接出る。

この方法なら `extraPaymentCapacityOn` と `Icc` の sum transport も、中心定理には必須ではない。

`extraPaymentCapacityOn` は後から global API として接続すればよい。

---

## block claim card の接続

local offset carry filter と claim fiber の cardinality は、次の全単射で結ぶ。

$$
t\longmapsto a+t
$$

local 側の条件は、

```text
t < j + 1 - a
carry two at a + t
```

global 側では、

```text
a <= i
i <= j
carry two at i
```

となる。

既に、

```lean
mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
```

があるので、全単射の codomain membership は閉じている。

逆方向は $t=i-a$ と置き、`omega` で処理できる。

したがって必要なのは `Ico` の insert lemma ではなく、cardinality bijection theorem じゃ。

---

## 中心 ledger までの最短列

修正版の証明列は次になる。

```text
1. recursive carry count = local offset filter card

2. recursive extra height = local offset sum

3. local offset carry card = canonical claim fiber card

4. local offset extra-height sum = endpoint capacity

5. shifted width ledger へ代入

6. overload / balance / credit を omega で導出
```

中心等式は、

$$
\operatorname{bitWidth}(T^{j+1}(n))+\operatorname{extraPaymentCapacityAt}(n,j)=\operatorname{bitWidth}(T^a(n))+#\operatorname{ClaimFiber}(n,j)
$$

じゃ。

これが得られれば、

$$
\operatorname{claims}>\operatorname{capacity}\Longleftrightarrow\operatorname{widthBefore}<\operatorname{widthAfter}
$$

$$
\operatorname{claims}=\operatorname{capacity}\Longleftrightarrow\operatorname{widthBefore}=\operatorname{widthAfter}
$$

$$
\operatorname{claims}<\operatorname{capacity}\Longleftrightarrow\operatorname{widthAfter}<\operatorname{widthBefore}
$$

が出る。

---

## 最新 snapshot に対する判定

### cp-303 のコード

**採用。**

追加された基礎は全て有効で、削除すべきものはない。

### Codex の rollback

**正しい。**

未完成 theorem や無理な rewrite を残さず、green 状態に戻した。

### Codex の停止

**実装上は理解できる。**

ただし数学的障害ではなく、直接 `Ico` route に固執した結果じゃ。

### わっちのレビュー

**部分的に修正が必要。**

「先へ進める」という判定は正しい。

しかし、

```text
どの表現なら進めるか
```

の指示が悪かった。

---

## 修正版 Codex 指示

````text
Continue from the verified snapshot:

19752c9b3cba9cc8e36e6d69237d9a4cb6ad08e9700f60ad6f0ee491863f9b5d
__snapshot-dk_math-lean-code-260713-0213.tar.gz

The previous direct attempt to identify the recursive shifted count with a
filtered `Finset.Ico` encountered interval-normalization friction.

Do not continue fighting the `Ico` successor normal form.

The mathematics is unchanged, but the proof representation must be changed.

# Immediate strategy

Use local offset coordinates first:

```text
t in Finset.range len
global time = a + t
```

Only after the recursive count and sum are expressed over `Finset.range len`
should they be transported to the canonical global block.

# Stage A — local offset carry set

Add a local offset carrier, or an equivalent theorem-facing expression:

```lean
noncomputable def shiftedCarryTwoOffsets
    (n : OddNat) (a len : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range len).filter fun t =>
    CarryTwoDebtAt n (a + t)
```

Prove:

```lean
theorem shiftedOrbitCarryTwoCount_eq_offset_card
    (n : OddNat) (a len : ℕ) :
    shiftedOrbitCarryTwoCount n a len =
      (shiftedCarryTwoOffsets n a len).card
```

Use induction on `len`.

The successor step should use `Finset.range_succ`, not `Finset.Ico`.

Reuse:

```lean
iterateT_add_eq_iterateT_from_shift
```

to identify the final local predicate with:

```text
CarryTwoDebtAt n (a + len)
```

# Stage B — local offset extra-height sum

Prove:

```lean
theorem shiftedExtraPaymentCapacity_eq_sum_range
    (n : OddNat) (a len : ℕ) :
    shiftedExtraPaymentCapacity n a len =
      ∑ t in Finset.range len,
        orbitWindowHeight n (a + t) - 1
```

Use induction on `len`, `Finset.sum_range_succ`, and:

```lean
orbitWindowHeight_shift_eq
```

Do not route this proof through `Finset.Ico`.

# Stage C — offset/global carry cardinality

For the canonical debt-supported block, let:

```text
a = floatPaymentBlockStart n j h
len = j + 1 - a
```

Prove a finite bijection between:

```text
local offsets t < len with carry two at a + t
```

and:

```text
carryTwoPaymentClaimFiberAt n j
```

Use:

```text
t -> a + t
i -> i - a
```

and reuse:

```lean
mem_carryTwoPaymentClaimFiber_iff_mem_floatPaymentBlockWithEndpoint_and_carryTwo
floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
```

Do not prove this by repeatedly rewriting `Ico` successor insertions.

The target theorem is:

```lean
shiftedOrbitCarryTwoCount n a len =
  (carryTwoPaymentClaimFiberAt n j).card
```

# Stage D — endpoint-only local sum

Still using local offsets, prove:

```lean
shiftedExtraPaymentCapacity n a len =
  extraPaymentCapacityAt n j
```

The final local offset is:

```text
len - 1 = j - a
```

and maps to global endpoint `j`.

For every earlier offset, use:

```lean
orbitWindowHeight_eq_one_of_mem_floatPaymentBlockInterior
```

to show the summand is zero.

At the last offset use:

```lean
two_le_orbitWindowHeight_floatPaymentBlock_endpoint
```

and the definition of `extraPaymentCapacityAt`.

A direct `Finset.sum_eq_single` proof or a split of
`Finset.range len` into its final index and the earlier range is acceptable.

# Stage E — exact block ledger

Substitute the two specialized identities into:

```lean
bitWidth_iterateT_add_shiftedExtraPaymentCapacity_eq_shiftedCarryTwo
```

and prove:

```lean
bitWidth (iterateT (j + 1) n).1
    + extraPaymentCapacityAt n j
  =
bitWidth (iterateT a n).1
    + (carryTwoPaymentClaimFiberAt n j).card
```

# Stage F — trichotomy

Derive:

```text
overload iff block width grows
claim card equals capacity iff block width is preserved
claim card below capacity iff block width decreases
```

Use the subtraction-free block equality and `omega`.

# Autonomous continuation

After the block trichotomy builds, continue into the universal payment target
and maximal staircase layers when they close.

Do not stop merely because one Finset normal form is inconvenient.

Change the intermediate representation instead.

Stop only at a genuine logical obstruction, not at an `Ico`/`Icc`
normalization mismatch.

# Validation

Run:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

Confirm no new `sorry` or `axiom`.

Record the result in:

```text
docs/dev/das-p2l-260607/review/report-petal-304.md
```
````

今回は明確に言える。

**数学の道は閉じておらぬ。わっちが、Lean に対して不利な座標を選ばせてしまった。**

次は offset 座標へ戻してから global block へ写す。これが正しい攻略法じゃ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Range.html?utm_source=chatgpt.com "Mathlib.Data.Finset.Range - Lean community"

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
index dbc3a8ef..964ca9c3 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PaymentBlockBridge.lean
@@ -244,6 +244,35 @@ theorem iterateT_add_eq_iterateT_from_shift
         _ = iterateT len (iterateT (a + 1) n) := by
           rw [iterateT_succ_eq_T_iterateT]

+/-- Observation height in a shifted orbit is the global height at the shifted index. -/
+theorem orbitWindowHeight_shift_eq
+    (n : OddNat) (a t : ℕ) :
+    orbitWindowHeight (iterateT a n) t = orbitWindowHeight n (a + t) := by
+  rw [orbitWindowHeight_eq_s_iterateT, orbitWindowHeight_eq_s_iterateT,
+    ← iterateT_add_eq_iterateT_from_shift]
+
+/-- Total extra-height capacity over an explicit finite source set. -/
+noncomputable def extraPaymentCapacityOn (n : OddNat) (S : Finset ℕ) : ℕ :=
+  ∑ i ∈ S, orbitWindowHeight n i - 1
+
+/-- Endpoint arithmetic for a nonempty debt-supported payment block. -/
+theorem floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h) = j + 1 := by
+  have hlt := floatPaymentBlockStart_lt_endpoint n j h
+  omega
+
+/-- The shifted block interval is exactly the endpoint-inclusive canonical block. -/
+theorem floatPaymentBlock_Ico_eq_withEndpoint
+    (n : OddNat) (j : ℕ) (h : (floatGrowthDebtFiberAt n j).Nonempty) :
+    Finset.Ico (floatPaymentBlockStart n j h)
+      (floatPaymentBlockStart n j h + (j + 1 - floatPaymentBlockStart n j h)) =
+      floatPaymentBlockWithEndpoint n j h := by
+  rw [floatPaymentBlockStart_add_endpointLength_eq_endpoint_succ]
+  unfold floatPaymentBlockWithEndpoint
+  ext i
+  simp
+
 /-- Carry-two count on the half-open orbit segment `[a, a + len)`. -/
 noncomputable def shiftedOrbitCarryTwoCount
     (n : OddNat) (a len : ℕ) : ℕ :=
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-303.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-303.md
new file mode 100644
index 00000000..547580e2
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-303.md
@@ -0,0 +1,37 @@
+# cp-303: Payment-block reindexing foundations
+
+## Added facts
+
+`PaymentBlockBridge` now exposes the first exact reindexing primitives:
+
+```text
+orbitWindowHeight (iterateT a n) t = orbitWindowHeight n (a + t)
+iterateT (a + len) n = iterateT len (iterateT a n)
+```
+
+It also defines `extraPaymentCapacityOn` for a finite set of global orbit
+indices and proves the endpoint arithmetic for a debt-supported block:
+
+```text
+a + (j + 1 - a) = j + 1
+Ico a (a + (j + 1 - a)) = Icc a j
+```
+
+where `a = floatPaymentBlockStart n j h`.
+
+## Current boundary
+
+The shifted width ledger is proven.  The remaining central block balance needs
+two finite reindexing identities: transport the recursive carry-two prefix
+count to the global `Icc a j` filter, and transport `sumExtraHeight` to
+`extraPaymentCapacityOn` over the same interval.  These are not semantic
+gaps; they are explicit finite-sum/card transport lemmas.
+
+No overload-to-width conclusion is asserted before those two identities are
+available.  The code continues to distinguish a debt-supported suffix from a
+future maximal height-one staircase.
+
+## Verification
+
+`PaymentBlockBridge` builds after these additions.  The final module and
+top-level build gates are run as part of the checkpoint handoff.
````
`````
