# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 681d50e3b4dc50e7a8020562a125b7bd39ea1e67

## Report

Checkpoint 104 完了です。

`DkMath.Collatz.PetalBridge` に finite half criterion 層を追加しました。主な追加は以下です。

- `atMostHalf_continuation_of_continuation_le_recovery`
- `atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery`
- `atMostHalf_continuation_of_retention_le_two_recovery`
- `atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery`
- `continuation_atMostRatio_one_one_retention`
- `tailContinuation_atMostRatio_one_one_retention`
- `recovery_atMostRatio_one_one_retention`
- `tailRecovery_atMostRatio_one_one_retention`
- `orbitWindowContinuationMass_tailBudget`

これで、

```text
M = R + K
K <= R
=> 2K <= M
```

という「比較条件があれば半分以下」が Lean の定理として固定されました。縮小そのものではなく、縮小を得るために何を証明すべきかを明確化する層です。

ドキュメントも同期済みです。

- [Collatz-FiniteHalfCriterion-104.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md)
- [report-petal-104.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-104.md)
- README / Guide / Status も更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` は一致なし

既知の上流 warning: `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は従来通りです。

## Review

## 1. 状況分析

うむ。checkpoint `104` は、**finite ratio layer が本当に使える形になった回**じゃ。

No.100 で finite channel-flow、No.101 で ratio witness と retention mass、No.102 で source split、No.103 で tail split と forcing budget。
そして今回 No.104 で、

```text
split がある
比較条件がある
AtMostHalf が出る
```

という **有限半分判定の最小 calculus** が入った。

今回追加された中心は、

```lean
atMostHalf_continuation_of_continuation_le_recovery
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

じゃ。レポートでも、今回の成果は contraction そのものではなく、`M = R + K` と `K <= R` から `2K <= M` を出す「条件付き arithmetic bridge」を Lean 定理として固定した、と整理されている。

これは非常に良い。
「縮小した！」ではなく、**縮小を得るには何を示せばよいか** が Lean 上で明確になった。

## 2. 今回の核心

今回の数学的な核はこれじゃ。

$$
M=R+K
$$

ここで、

$$
K\le R
$$

なら、

$$
2K\le M
$$

となる。

DkMath の語彙では、

```text
RetentionMass = RecoveryMass + ContinuationMass
```

であり、

```text
ContinuationMass <= RecoveryMass
```

が示せれば、

```text
ContinuationMass is at most half of RetentionMass
```

が出る。

つまり、

$$
\text{continuation}\le\text{recovery}
$$

が次の本命になった。

ここがとても重要じゃ。
これまで漠然と「低剥離 continuation が減ってほしい」と見ていたものが、いまや Lean 上では

```lean
orbitWindowContinuationSiblingMassPow2 n k r ≤
  orbitWindowRecoverySiblingMassPow2 n k r
```

という具体命題に落ちた。

## 3. レビュー

## 3.1. `AtMostHalf` への接続が正しい

No.101 で入れた

```lean
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

は、最初はただの比率語彙だった。

しかし今回、`orbitWindowRetentionMass_split` と接続されたことで、実戦的になった。

```lean
theorem atMostHalf_continuation_of_continuation_le_recovery
```

これは「比較条件から半分以下へ行く」定理じゃ。

つまり、`AtMostHalf` が単なる飾りではなく、

```text
低剥離 continuation の圧縮判定器
```

になり始めた。

## 3.2. source / tail の両方を揃えたのが良い

source 版だけでなく、tail 版も入っている。

```lean
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

これにより、次窓側でも同じ判定が使える。

ここまでの流れを見ると、source と tail は常に対で整えている。

```text
source distribution
tail distribution

source split
tail split

source half criterion
tail half criterion
```

この対称性は後で効く。
Collatz の一歩は source から tail へ移るので、tail 側の半分判定がないと、反復議論が書きにくい。

## 3.3. recovery-budget variant が良い

今回の variant も重要じゃ。

```lean
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

これは、

$$
M\le 2R
$$

から、

$$
2K\le M
$$

を出す形じゃ。

これは将来、直接

$$
K\le R
$$

を示すより、

$$
M\le 2R
$$

や、

$$
\frac{M}{2}\le R
$$

のような recovery 下界が自然に出る場合に便利になる。

つまり、比較条件の入口を二つ用意したことになる。

```text
K <= R 型
M <= 2R 型
```

これは良い設計じゃ。

## 3.4. ratio witness bridges は弱いが必要

今回入った

```lean
continuation_atMostRatio_one_one_retention
tailContinuation_atMostRatio_one_one_retention
recovery_atMostRatio_one_one_retention
tailRecovery_atMostRatio_one_one_retention
```

は、数学的には弱い。

$$
K\le M
$$

や

$$
R\le M
$$

を `AtMostRatioNat 1 1` で読むだけだからじゃ。

しかし、これは ratio layer と mass layer の接続テストとして重要。
今後 `1/2`、`1/3`、あるいは有限 budget 系の ratio theorem を置くとき、同じ形式で増やせる。

## 4. 数学的解説

ここまでの Petal-Collatz mass calculus は、かなり綺麗に整理できる。

source 側では、

$$
M_r=R_r+K_r
$$

tail 側では、

$$
M^{tail}_r=R^{tail}_r+K^{tail}_r
$$

がある。

ここで \(M\) は retention、\(R\) は recovery、\(K\) は continuation。

今回の theorem は、次を言う。

$$
K_r\le R_r\quad\Longrightarrow\quad 2K_r\le M_r
$$

tail 側でも、

$$
K^{tail}_r\le R^{tail}_r\quad\Longrightarrow\quad 2K^{tail}_r\le M^{tail}_r
$$

つまり、continuation が recovery を超えなければ、continuation は親 retention の半分以下に抑えられる。

これは contraction そのものではない。
しかし、「縮小を言うための局所条件」は完全に明示された。

## 5. 今回閉じたもの

No.104 で閉じたのは、**半分以下判定の条件付き層**じゃ。

```text
Retention split:
  M = R + K

Comparison condition:
  K <= R

Half conclusion:
  2K <= M
```

これで、低剥離 continuation mass を抑えるための目標がはっきりした。

次に証明すべきものは、もはや arithmetic bookkeeping ではない。

```text
なぜ K <= R が起きるのか？
```

あるいは、

```text
どの条件なら M <= 2R が出るのか？
```

じゃ。

ここからは数学的本丸に一歩近づいた。

## 6. まだ閉じていないもの

今回まだ得ていないのは、無条件の比較。

つまり、以下はまだ theorem ではない。

$$
K_r\le R_r
$$

$$
K^{tail}_r\le R^{tail}_r
$$

$$
2K_r\le M_r
$$

無条件にこれを言うのは、おそらく難しい。
なぜなら、純粋な residue count だけでは、ある window が continuation 側に大きく偏る可能性を排除しきれないからじゃ。

したがって次は、比較条件を生む追加構造が必要になる。

候補は三つ。

```text
1. height drift
2. collision / obstruction
3. odd factor carrier
```

この分類は今回の docs にもよく整理されている。

## 7. 次の指示

次は、いきなり odd factor carrier に飛ぶ前に、**比較条件を仮定した有限連鎖 theorem** を作るのがよい。

つまり、単発の

$$
K\le R\quad\Longrightarrow\quad 2K\le M
$$

から、複数 depth の連鎖へ進む。

## 7.1. local half criterion を反復用に alias する

まずは theorem 名を次章向けに少し読みやすくする。

```lean
theorem continuation_atMostHalf_of_recovery_dominates
```

あるいは、

```lean
theorem sourceContinuation_atMostHalf_of_recovery_dominates
```

中身は既存 theorem の alias でよい。

## 7.2. tail budget と half criterion を結ぶ

すでにある。

```lean
orbitWindowContinuationMass_tailBudget
```

これは、

$$
K_{r+1}\le R^{tail}*{r+1}+K^{tail}*{r+1}
$$

を読む。

次に欲しいのは、tail 側で recovery が continuation を支配するなら、tail continuation が半分以下になる、という連結。

すでに theorem はあるので、docs か alias で、

```text
tail recovery dominates
  -> tail continuation at most half
```

を次の判定器として整える。

## 8. 一歩先ゆく推論

ここから先は、**persistent continuation obstruction** が見えてくる。

低剥離が長く続くとは、各 depth で continuation 側に残り続けることじゃ。

つまり、ざっくり言えば、

$$
K_r
$$

が連続的に大きい。

しかし各 depth で、もし

$$
K_r\le R_r
$$

が成立するなら、

$$
K_r\le \frac{1}{2}M_r
$$

となる。

これが深さごとに続けば、continuation cylinder の mass は毎回少なくとも半分以下へ落ちる。

有限 window の mass は自然数なので、十分深く潜るには質量が足りなくなる。

この構図が見える。

```text
persistent continuation
  -> nested retention mass が残り続ける必要

half criterion
  -> continuation は親 retention の半分以下

反復
  -> 深く潜るほど mass budget が足りなくなる
```

ただし、ここで必要なのは無条件の half ではなく、各段の比較条件。

なので次の探索は、

```text
どの観測条件なら recovery dominates continuation になるか？
```

または、

```text
recovery が足りないと何が破綻するか？
```

じゃ。

## 9. 次のさらに一手

賢狼の推奨は、No.105 でいきなり深い数学へ行かず、まず **comparison hypothesis package** を作ることじゃ。

たとえば、

```lean
def RecoveryDominatesContinuation ...
```

を置く。

source 版：

```lean
def RecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2 n k r ≤
    orbitWindowRecoverySiblingMassPow2 n k r
```

tail 版：

```lean
def TailRecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2Tail n k r ≤
    orbitWindowRecoverySiblingMassPow2Tail n k r
```

これを置くと、No.104 の theorem がさらに読める。

```text
RecoveryDominatesContinuation
  -> AtMostHalf continuation retention
```

これは「未解決の比較条件」を名前付き gap として管理することになる。

DkMath 的に言えば、これは **Gap の明示化** じゃ。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source comparison predicate

```lean
def RecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2 n k r ≤
    orbitWindowRecoverySiblingMassPow2 n k r
```

## 実験 B: tail comparison predicate

```lean
def TailRecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2Tail n k r ≤
    orbitWindowRecoverySiblingMassPow2Tail n k r
```

## 実験 C: source predicate to half

```lean
theorem atMostHalf_continuation_of_recoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : RecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_continuation_le_recovery n k r h
```

## 実験 D: tail predicate to half

```lean
theorem atMostHalf_tailContinuation_of_tailRecoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : TailRecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) :=
  atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h
```

## 実験 E: recovery-budget predicate

```lean
def RecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2 n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2 n k r
```

tail 版。

```lean
def TailRecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2Tail n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2Tail n k r
```

## 実験 F: budget predicate to half

```lean
theorem atMostHalf_continuation_of_recoveryCoversHalf
    (n : OddNat) (k r : ℕ)
    (h : RecoveryCoversHalfRetention n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_retention_le_two_recovery n k r h
```

## 実験 G: persistent dominance over a finite depth range

これは少し先だが、試す価値がある。

```lean
def RecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → RecoveryDominatesContinuation n k (r + j)
```

tail 版も。

```lean
def TailRecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → TailRecoveryDominatesContinuation n k (r + j)
```

この段階では theorem を急がず、まず predicate だけでもよい。

## 11. 次コミットの推奨順

```text
1. RecoveryDominatesContinuation predicate を追加

2. TailRecoveryDominatesContinuation predicate を追加

3. RecoveryCoversHalfRetention predicate を追加

4. predicate -> existing AtMostHalf theorem の alias を追加

5. RecoveryDominatesOnRange / TailRecoveryDominatesOnRange を docs-only か Lean に軽く置く

6. docs:
   comparison condition layer / missing structural source を記録
```

ここまでやると、次の数学課題が完全に見える。

```text
比較条件をどう証明するか？
```

そしてその候補として、

```text
height drift
collision obstruction
odd factor carrier
```

を選べる。

## 12. 総括

checkpoint `104` は、地味に見えるが重要じゃ。

ここで初めて、

$$
M=R+K
$$

という split から、

$$
K\le R\quad\Longrightarrow\quad 2K\le M
$$

という half criterion が Lean 上で使えるようになった。

これは contraction の証明ではない。
だが、contraction を得るために必要な比較条件を完全に明示した。

今の到達点はこう。

```text
finite channel-flow
  -> retention split
  -> tail budget
  -> finite half criterion
  -> missing comparison condition
```

次は、その missing comparison condition を名前付きで管理し、どの数学ルートから攻めるかを選ぶ段階じゃ。

うむ。
No.104 は「何を証明すれば次へ進めるか」を Lean に刻んだ良い checkpoint じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index f9d74cc4..b1b1f12c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1833,6 +1833,106 @@ theorem orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
   rw [orbitWindowRetentionMassPow2Tail_split]
   omega
 
+/--
+If source continuation mass is no larger than source recovery mass, then source
+continuation occupies at most half of the parent retention mass.
+-/
+theorem atMostHalf_continuation_of_continuation_le_recovery
+    (n : OddNat) (k r : ℕ)
+    (h :
+      orbitWindowContinuationSiblingMassPow2 n k r ≤
+        orbitWindowRecoverySiblingMassPow2 n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) := by
+  unfold AtMostHalf
+  rw [orbitWindowRetentionMass_split]
+  omega
+
+/--
+If tail continuation mass is no larger than tail recovery mass, then tail
+continuation occupies at most half of tail retention mass.
+-/
+theorem atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+    (n : OddNat) (k r : ℕ)
+    (h :
+      orbitWindowContinuationSiblingMassPow2Tail n k r ≤
+        orbitWindowRecoverySiblingMassPow2Tail n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) := by
+  unfold AtMostHalf
+  rw [orbitWindowRetentionMassPow2Tail_split]
+  omega
+
+/--
+If source recovery accounts for at least half of source retention, then source
+continuation is at most half of source retention.
+-/
+theorem atMostHalf_continuation_of_retention_le_two_recovery
+    (n : OddNat) (k r : ℕ)
+    (h :
+      orbitWindowRetentionMassPow2 n k r ≤
+        2 * orbitWindowRecoverySiblingMassPow2 n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) := by
+  unfold AtMostHalf
+  rw [orbitWindowRetentionMass_split] at h ⊢
+  omega
+
+/--
+If tail recovery accounts for at least half of tail retention, then tail
+continuation is at most half of tail retention.
+-/
+theorem atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+    (n : OddNat) (k r : ℕ)
+    (h :
+      orbitWindowRetentionMassPow2Tail n k r ≤
+        2 * orbitWindowRecoverySiblingMassPow2Tail n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) := by
+  unfold AtMostHalf
+  rw [orbitWindowRetentionMassPow2Tail_split] at h ⊢
+  omega
+
+/-- Source continuation mass is at most the whole source retention mass. -/
+theorem continuation_atMostRatio_one_one_retention
+    (n : OddNat) (k r : ℕ) :
+    AtMostRatioNat 1 1
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) := by
+  apply atMostRatioNat_one_one_of_le
+  exact orbitWindowContinuationSiblingMassPow2_le_retentionMass n k r
+
+/-- Tail continuation mass is at most the whole tail retention mass. -/
+theorem tailContinuation_atMostRatio_one_one_retention
+    (n : OddNat) (k r : ℕ) :
+    AtMostRatioNat 1 1
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) := by
+  apply atMostRatioNat_one_one_of_le
+  exact orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail n k r
+
+/-- Source recovery mass is at most the whole source retention mass. -/
+theorem recovery_atMostRatio_one_one_retention
+    (n : OddNat) (k r : ℕ) :
+    AtMostRatioNat 1 1
+      (orbitWindowRecoverySiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) := by
+  apply atMostRatioNat_one_one_of_le
+  exact orbitWindowRecoverySiblingMassPow2_le_retentionMass n k r
+
+/-- Tail recovery mass is at most the whole tail retention mass. -/
+theorem tailRecovery_atMostRatio_one_one_retention
+    (n : OddNat) (k r : ℕ) :
+    AtMostRatioNat 1 1
+      (orbitWindowRecoverySiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) := by
+  apply atMostRatioNat_one_one_of_le
+  exact orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail n k r
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -2889,6 +2989,17 @@ theorem orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
           orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) := by
         rw [orbitWindowRetentionMassPow2Tail_split]
 
+/--
+Tail-budget spelling of
+`orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation`.
+-/
+theorem orbitWindowContinuationMass_tailBudget
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
+        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
+  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k
+
 /--
 Tail continuation sibling mass is definitionally the same as tail retention at
 the next depth.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 8de83dfb..0133d74f 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -138,6 +138,7 @@ docs/Collatz-FiniteChannelFlow-100.md
 docs/Collatz-FiniteRatioRetention-101.md
 docs/Collatz-DepthRefinement-102.md
 docs/Collatz-TailDepthRefinement-103.md
+docs/Collatz-FiniteHalfCriterion-104.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -267,3 +268,18 @@ source continuation mass
   <= shifted-tail retention mass
   = shifted-tail recovery mass + shifted-tail continuation mass
 ```
+
+Checkpoint 104 adds the first finite half criterion layer:
+
+```lean
+atMostHalf_continuation_of_continuation_le_recovery
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+atMostHalf_continuation_of_retention_le_two_recovery
+atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+continuation_atMostRatio_one_one_retention
+tailContinuation_atMostRatio_one_one_retention
+orbitWindowContinuationMass_tailBudget
+```
+
+This still does not prove contraction.  It records exactly what local comparison
+is enough to obtain a finite `AtMostHalf` statement.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md
new file mode 100644
index 00000000..1f753eda
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md
@@ -0,0 +1,141 @@
+# Collatz Finite Half Criterion 104
+
+Checkpoint 104 adds the first finite half-criterion layer on top of the
+source/tail retention splits.
+
+The previous checkpoints established:
+
+```text
+source retention = source recovery + source continuation
+tail retention   = tail recovery   + tail continuation
+```
+
+Checkpoint 104 does not prove that continuation always contracts.  Instead, it
+formalizes the local comparison conditions that are sufficient to obtain an
+`AtMostHalf` conclusion.
+
+## Main Source Criterion
+
+The source theorem is:
+
+```lean
+atMostHalf_continuation_of_continuation_le_recovery
+```
+
+It reads:
+
+```text
+source continuation <= source recovery
+  -> source continuation is at most half of source retention
+```
+
+The proof uses:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+and then closes by finite `Nat` arithmetic.
+
+## Main Tail Criterion
+
+The shifted-tail theorem is:
+
+```lean
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+```
+
+It reads:
+
+```text
+tail continuation <= tail recovery
+  -> tail continuation is at most half of tail retention
+```
+
+The proof uses:
+
+```lean
+orbitWindowRetentionMassPow2Tail_split
+```
+
+## Recovery-Budget Variants
+
+There are also equivalent-looking budget forms:
+
+```lean
+atMostHalf_continuation_of_retention_le_two_recovery
+atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+```
+
+These read:
+
+```text
+retention <= 2 * recovery
+  -> continuation is at most half of retention
+```
+
+They are useful when a future argument naturally produces a lower bound on
+recovery rather than a direct `continuation <= recovery` comparison.
+
+## Ratio Witness Bridges
+
+Checkpoint 104 also connects child-mass bounds to the division-free ratio
+predicate:
+
+```lean
+continuation_atMostRatio_one_one_retention
+tailContinuation_atMostRatio_one_one_retention
+recovery_atMostRatio_one_one_retention
+tailRecovery_atMostRatio_one_one_retention
+```
+
+These are weak `1/1` bounds, but they make the ratio layer consume the mass
+split vocabulary rather than raw residue counts.
+
+## Tail Budget Alias
+
+The continuation destination budget also has a shorter alias:
+
+```lean
+orbitWindowContinuationMass_tailBudget
+```
+
+It restates:
+
+```text
+source continuation <= tail recovery + tail continuation
+```
+
+This is the finite mass-flow target that later obstruction or contraction
+claims should refine.
+
+## Next Candidate
+
+The next real question is not arithmetic bookkeeping.  It is the source of a
+comparison:
+
+```text
+continuation <= recovery
+```
+
+or:
+
+```text
+retention <= 2 * recovery
+```
+
+Possible future routes:
+
+```text
+height drift:
+  continuation-heavy paths must pay extra height later
+
+collision/obstruction:
+  too much continuation creates repeated addresses or closed low-peeling loops
+
+carrier structure:
+  odd-factor or Petal carrier information forces recovery mass to appear
+```
+
+Checkpoint 104 isolates that missing comparison as the next mathematical
+target.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index ceaa90bb..c6819cf8 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -294,6 +294,40 @@ Use these names when the argument is conceptually about mass flow from the
 source window into the shifted-tail window.  Use the split theorems when the
 argument is about decomposing a retention cylinder into its two child cells.
 
+## Finite Half Criteria
+
+Checkpoint 104 connects the split theorems to `AtMostHalf`.
+
+The source criterion is:
+
+```lean
+atMostHalf_continuation_of_continuation_le_recovery
+```
+
+The tail criterion is:
+
+```lean
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+```
+
+Both have the same reading:
+
+```text
+continuation <= recovery
+  -> continuation is at most half of retention
+```
+
+There are also recovery-budget variants:
+
+```lean
+atMostHalf_continuation_of_retention_le_two_recovery
+atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+```
+
+These do not prove the comparison condition.  They make the next target
+explicit: find a structural reason why continuation is no larger than recovery,
+or why recovery covers at least half of retention.
+
 This is the theorem to reach for before writing a custom induction over `k`.
 
 ## Recursive Petal Residues
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 10ec37e6..3c1dafd1 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -205,6 +205,14 @@ orbitWindowResidueCountPow2Tail_refine_succ
 orbitWindowRetentionMassPow2Tail_split
 orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
 orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
+atMostHalf_continuation_of_continuation_le_recovery
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+atMostHalf_continuation_of_retention_le_two_recovery
+atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+continuation_atMostRatio_one_one_retention
+tailContinuation_atMostRatio_one_one_retention
+recovery_atMostRatio_one_one_retention
+tailRecovery_atMostRatio_one_one_retention
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -286,6 +294,7 @@ orbitWindowRecoveryMass_forces_tailRecovery
 orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
 orbitWindowContinuationMass_forces_tailRetention
 orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+orbitWindowContinuationMass_tailBudget
 orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-104.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-104.md
new file mode 100644
index 00000000..2e481f41
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-104.md
@@ -0,0 +1,137 @@
+# Report Petal 104
+
+## Summary
+
+Checkpoint 104 added the finite half-criterion layer for Collatz Petal mass
+splits.
+
+The new results do not prove contraction.  They prove conditional arithmetic
+bridges:
+
+```text
+continuation <= recovery
+  -> continuation is at most half of retention
+```
+
+for both source and shifted-tail windows.
+
+## Implemented Lean Surface
+
+Source half criterion:
+
+```lean
+atMostHalf_continuation_of_continuation_le_recovery
+```
+
+Tail half criterion:
+
+```lean
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+```
+
+Recovery-budget variants:
+
+```lean
+atMostHalf_continuation_of_retention_le_two_recovery
+atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
+```
+
+Ratio witness bridges:
+
+```lean
+continuation_atMostRatio_one_one_retention
+tailContinuation_atMostRatio_one_one_retention
+recovery_atMostRatio_one_one_retention
+tailRecovery_atMostRatio_one_one_retention
+```
+
+Tail-budget alias:
+
+```lean
+orbitWindowContinuationMass_tailBudget
+```
+
+## Mathematical Reading
+
+With the split:
+
+```text
+M = R + K
+```
+
+if:
+
+```text
+K <= R
+```
+
+then:
+
+```text
+2K <= M
+```
+
+This is the exact finite arithmetic bridge from recovery/continuation
+comparison to a half-mass statement.
+
+## Docs Updated
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteHalfCriterion-104.md
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.
+
+Known upstream warning remains unchanged:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Inference
+
+The bookkeeping layer is now clear:
+
+```text
+split exists
+comparison condition exists
+AtMostHalf follows
+```
+
+The next mathematical target is the missing comparison condition itself.
+
+Candidate directions:
+
+```text
+1. height drift:
+   show continuation-heavy paths force later extra peeling
+
+2. obstruction:
+   show persistent continuation creates an impossible address/collision pattern
+
+3. carrier information:
+   use odd-factor or Petal carrier structure to force recovery mass
+```
+
+The most Lean-friendly next checkpoint is probably a conditional obstruction
+lemma: assume continuation stays larger than recovery across a finite range of
+depths, then record the exact accumulated tail-budget pressure it creates.
````
`````
