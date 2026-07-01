# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 36ce362510eaad092233409fabb0b1d87cc78304

## Report

Checkpoint 105 完了です。

`DkMath.Collatz.PetalBridge` に comparison condition layer を追加しました。今回の主目的は、未解決の比較条件を名前付き predicate として固定し、今後の obstruction / drift / carrier 方面へ渡せる形にすることです。

追加した主な Lean surface:

- `RecoveryDominatesContinuation`
- `TailRecoveryDominatesContinuation`
- `RecoveryCoversHalfRetention`
- `TailRecoveryCoversHalfRetention`
- `RecoveryDominatesOnRange`
- `TailRecoveryDominatesOnRange`
- `atMostHalf_continuation_of_recoveryDominates`
- `atMostHalf_tailContinuation_of_tailRecoveryDominates`
- `atMostHalf_continuation_of_recoveryCoversHalf`
- `atMostHalf_tailContinuation_of_tailRecoveryCoversHalf`
- `atMostHalf_continuation_of_recoveryDominatesOnRange`
- `atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange`

おまけで obstruction 側の failure-mode predicate も追加しました。

- `ContinuationOutrunsRecovery`
- `TailContinuationOutrunsRecovery`
- `ContinuationOutrunsRecoveryOnRange`
- `TailContinuationOutrunsRecoveryOnRange`

これで次の未解決点はかなり明確です。

```text
structural observation
  -> RecoveryDominatesContinuation
```

または逆側として、

```text
ContinuationOutrunsRecoveryOnRange
  -> height drift / address collision / finite budget pressure
```

ドキュメントも同期済みです。

- [Collatz-ComparisonPredicates-105.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md)
- [report-petal-105.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-105.md)
- README / Guide / Status も更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` は一致なし

既知の上流 warning: `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は従来通りです。

## Review

## 1. 状況分析

うむ。checkpoint `105` は、いままでの bookkeeping / finite mass calculus から、**次に証明すべき未解決条件を名前付きで固定した回**じゃ。

ここまでの流れはこうだった。

```text
No.100:
  finite channel-flow

No.101:
  retention / recovery / continuation mass

No.102:
  source retention split

No.103:
  tail retention split and forcing budget

No.104:
  finite half criterion

No.105:
  missing comparison condition を predicate 化
```

今回の主目的は、無条件に縮小を証明することではない。
むしろ、

```text
どの条件が証明できれば縮小に進めるのか
```

を Lean 上で明確にした。

追加された中心 predicate は、

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

そして、逆側の failure-mode として、

```lean
ContinuationOutrunsRecovery
TailContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
TailContinuationOutrunsRecoveryOnRange
```

も入った。レポートでも、今回の目的は未解決の比較条件を名前付き predicate として固定し、今後の obstruction / drift / carrier 方面へ渡せる形にすることだと整理されている。

これはかなり良い。
「縮小を示せ」ではなく、

```text
structural observation -> RecoveryDominatesContinuation
```

または、

```text
ContinuationOutrunsRecoveryOnRange -> obstruction / drift / pressure
```

という形まで問題が鋭くなった。

## 2. レビュー

## 2.1. predicate 化の判断は正しい

No.104 で得た finite half criterion は、

$$
M=R+K
$$

と、

$$
K\le R
$$

から、

$$
2K\le M
$$

を得るものだった。

しかし、まだ \(K\le R\) は証明されていない。
ここで無理に証明へ突っ込むのではなく、

```lean
RecoveryDominatesContinuation
```

として名前を与えたのは正解じゃ。

これは DkMath 的には、**Gap を名前付きで隔離した** ことになる。

```text
現在の有限質量 calculus:
  M = R + K
  K <= R -> AtMostHalf K M

残る Gap:
  K <= R をどこから得るか
```

この Gap が theorem 名を持った。
これにより、以後の開発で「何を渡せばよいか」が明確になる。

## 2.2. source / tail / range が揃っている

今回良いのは、local predicate だけで止まらず、tail 版と range 版も入っていることじゃ。

```lean
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

これは重要。

Collatz の低剥離 path は、単発の depth ではなく、深さ方向へ潜る構造だった。

$$
7\pmod 8,\quad 15\pmod {16},\quad 31\pmod {32},\quad 63\pmod {64},\ldots
$$

したがって本当に欲しいのは、一点の比較ではなく、

$$
\forall j < len,\;K_{r+j}\le R_{r+j}
$$

という有限 depth range の比較である。

これが `RecoveryDominatesOnRange` として入った。
これは次章にかなり効く。

## 2.3. failure-mode predicate が良い

今回の「おまけ」が実は重要じゃ。

```lean
ContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
```

これは、証明できない場合の反対側を明示する。

つまり、

```text
recovery が continuation を支配できない
```

なら、

```text
continuation が recovery を上回る
```

という失敗モードを、obstruction route の入力にできる。

これがあると、次にこういう分岐設計が可能になる。

```text
Case 1:
  RecoveryDominatesContinuation
  -> AtMostHalf
  -> contraction-like estimate

Case 2:
  ContinuationOutrunsRecovery
  -> pressure / collision / drift obstruction
```

これは非常に DkMath らしい。
正しい道だけでなく、**行き止まりになる道も theorem/predicate として名前を付ける** 方針じゃ。

## 3. 数学的解説

いまの有限質量 calculus は次の形になっている。

Retention mass を \(M\)、recovery mass を \(R\)、continuation mass を \(K\) と読む。

$$
M=R+K
$$

ここで、

$$
K\le R
$$

が成り立てば、

$$
2K\le M
$$

となる。

DkMath の定理名では、

```lean
RecoveryDominatesContinuation
```

が \(K\le R\) を表す。

そして、

```lean
atMostHalf_continuation_of_recoveryDominates
```

が、

$$
K\le R\quad\Longrightarrow\quad 2K\le M
$$

を消費する。

tail 側も同じ。

$$
M^{tail}=R^{tail}+K^{tail}
$$

$$
K^{tail}\le R^{tail}\quad\Longrightarrow\quad 2K^{tail}\le M^{tail}
$$

この構造により、今後は生の residue count を展開せず、

```text
RecoveryDominatesContinuation を証明する
```

だけで、半分以下の conclusion へ入れる。

## 4. 今回閉じたもの

今回閉じたのは、**未解決比較条件の API 化**じゃ。

```text
比較条件:
  RecoveryDominatesContinuation

予算条件:
  RecoveryCoversHalfRetention

range 条件:
  RecoveryDominatesOnRange

failure 条件:
  ContinuationOutrunsRecoveryOnRange
```

これで、次の proof obligation はかなり明確になった。

以前は、

```text
縮小を示す
```

という曖昧な目標だった。

今は、

```text
structural observation -> RecoveryDominatesContinuation
```

または、

```text
ContinuationOutrunsRecoveryOnRange -> contradiction/pressure
```

である。

これは大きな前進じゃ。

## 5. 注意点

## 5.1. `RecoveryDominatesContinuation` はまだ仮定

今回の predicate は、あくまで hypothesis package じゃ。
無条件 theorem ではない。

したがって、現時点で言えるのは、

```text
比較条件があれば AtMostHalf が出る
```

であって、

```text
比較条件は常に成り立つ
```

ではない。

ここは文書でも明確にしておくのがよい。

## 5.2. failure-mode の排中律はまだない

`RecoveryDominatesContinuation` と `ContinuationOutrunsRecovery` は直感的には補集合に見える。

しかし Nat の線形順序では、

$$
K\le R
$$

でなければ、

$$
R<K
$$

が言えるはず。

これを theorem 化すると、次の case split が使いやすくなる。

```lean
RecoveryDominatesContinuation n k r ∨
  ContinuationOutrunsRecovery n k r
```

これは次の小補題としてかなり有用じゃ。

## 6. 次の指示

次 checkpoint では、**comparison predicate の case split と failure-mode の弱い帰結**を作るのが良い。

いきなり height drift や odd factor carrier に突入するより、まずは

```text
dominates か outruns か
```

の分岐を Lean で扱いやすくする。

## 6.1. local dichotomy theorem

source 版。

```lean
theorem recoveryDominates_or_continuationOutruns
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ∨
      ContinuationOutrunsRecovery n k r := by
  unfold RecoveryDominatesContinuation ContinuationOutrunsRecovery
  omega
```

tail 版。

```lean
theorem tailRecoveryDominates_or_tailContinuationOutruns
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ∨
      TailContinuationOutrunsRecovery n k r := by
  unfold TailRecoveryDominatesContinuation TailContinuationOutrunsRecovery
  omega
```

これで、各 depth で必ず「良い側」か「失敗側」に分けられる。

## 6.2. range の point extraction

`ContinuationOutrunsRecoveryOnRange` から各 depth の失敗を取り出す theorem も欲しい。

```lean
theorem continuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    ContinuationOutrunsRecovery n k (r + j) :=
  h j hj
```

これは薄いが、後続でかなり便利じゃ。

## 6.3. failure から recovery not dominates

failure-mode が `R < K` なら、`K <= R` は否定される。

```lean
theorem not_recoveryDominates_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    ¬ RecoveryDominatesContinuation n k r := by
  unfold ContinuationOutrunsRecovery RecoveryDominatesContinuation at h ⊢
  omega
```

tail 版も同様。

## 7. 一歩先ゆく推論

ここから先の本丸は、`ContinuationOutrunsRecoveryOnRange` の意味づけじゃ。

もし、ある範囲でずっと

$$
R_{r+j}<K_{r+j}
$$

が続くなら、各 depth で continuation が親 retention の半分を超える。

なぜなら、

$$
M=R+K
$$

かつ、

$$
R<K
$$

なら、

$$
M<2K
$$

となる。

これは `AtMostHalf` の逆側である。

つまり failure-mode は、

```text
continuation is more than half of retention
```

を意味する。

これを theorem 化すると良い。

source 版の命題は、

```lean
def MoreThanHalf (count k : ℕ) : Prop :=
  k < 2 * count
```

として、

```lean
theorem moreThanHalf_continuation_of_continuationOutruns
```

を作る。

数学的には、

$$
R<K,\quad M=R+K\quad\Longrightarrow\quad M<2K
$$

じゃ。

これにより、比較条件が失敗した場合も、単なる失敗ではなく、

```text
continuation が親 retention の半分を超えている
```

という「圧力」として読める。

これは次の obstruction route にかなり効く。

## 8. さらに次の一手

No.106 で一番良さそうなのは、**MoreThanHalf / Outruns pressure layer** じゃ。

これにより、比較条件の二分岐がこうなる。

```text
RecoveryDominatesContinuation
  -> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

つまり、各 depth で continuation は、

```text
半分以下
```

か、

```text
半分超え
```

のどちらかとして読める。

ここまで行くと、finite mass calculus が非常に美しい。

$$
K\le R\quad\Longrightarrow\quad 2K\le M
$$

$$
R<K\quad\Longrightarrow\quad M<2K
$$

これが source / tail / range で揃う。

その後で初めて、

```text
MoreThanHalf が連続すると何が起こるか？
```

を問える。

## 9. 賢狼が試して欲しい実験補題

## 実験 A: MoreThanHalf predicate

```lean
/--
Finite natural-number witness that a count occupies more than half of a window.
This is the strict counterpart of `AtMostHalf`.
-/
def MoreThanHalf (count k : ℕ) : Prop :=
  k < 2 * count
```

## 実験 B: AtMostHalf / MoreThanHalf dichotomy

```lean
theorem atMostHalf_or_moreThanHalf
    (count k : ℕ) :
    AtMostHalf count k ∨ MoreThanHalf count k := by
  unfold AtMostHalf MoreThanHalf
  omega
```

## 実験 C: recovery dominance dichotomy

```lean
theorem recoveryDominates_or_continuationOutruns
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ∨
      ContinuationOutrunsRecovery n k r := by
  unfold RecoveryDominatesContinuation ContinuationOutrunsRecovery
  omega
```

## 実験 D: tail dominance dichotomy

```lean
theorem tailRecoveryDominates_or_tailContinuationOutruns
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ∨
      TailContinuationOutrunsRecovery n k r := by
  unfold TailRecoveryDominatesContinuation TailContinuationOutrunsRecovery
  omega
```

## 実験 E: continuation outruns gives MoreThanHalf

```lean
theorem moreThanHalf_continuation_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold MoreThanHalf
  unfold ContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMass_split]
  omega
```

## 実験 F: tail continuation outruns gives MoreThanHalf

```lean
theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold MoreThanHalf
  unfold TailContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega
```

## 実験 G: range extraction for failure mode

```lean
theorem continuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    ContinuationOutrunsRecovery n k (r + j) :=
  h j hj
```

```lean
theorem tailContinuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    TailContinuationOutrunsRecovery n k (r + j) :=
  h j hj
```

## 実験 H: range failure gives MoreThanHalf at each depth

```lean
theorem moreThanHalf_continuation_of_outRunsOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  moreThanHalf_continuation_of_continuationOutruns
    n k (r + j) (h j hj)
```

tail 版も同様。

## 10. 次コミットの推奨順

```text
1. MoreThanHalf を追加

2. AtMostHalf / MoreThanHalf の dichotomy を追加

3. RecoveryDominates / ContinuationOutruns の dichotomy を追加

4. ContinuationOutruns -> MoreThanHalf を source / tail で追加

5. OnRange extraction theorem を追加

6. OnRange failure -> MoreThanHalf at each depth を追加

7. docs:
   ComparisonPredicates-106 / MoreThanHalfPressure を追加
```

## 11. 総括

checkpoint `105` は、かなり良い「Gap 命名」回じゃ。

ここで、次の未解決点が Lean 上で明確になった。

$$
\text{structural observation}\quad\Longrightarrow\quad\text{RecoveryDominatesContinuation}
$$

または、逆に、

$$
\text{ContinuationOutrunsRecoveryOnRange}\quad\Longrightarrow\quad\text{pressure / obstruction}
$$

次は、failure-mode を単なる失敗ではなく、

$$
\text{MoreThanHalf pressure}
$$

として読む層を作るのがよい。

これにより、各 depth で、

```text
AtMostHalf 側
```

か、

```text
MoreThanHalf 側
```

かに分岐できる。

うむ。
これはいよいよ、Collatz.PetalBridge が「有限質量予算の分岐論理」へ入る入口じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index b1b1f12c..2a6fef01 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1933,6 +1933,143 @@ theorem tailRecovery_atMostRatio_one_one_retention
   apply atMostRatioNat_one_one_of_le
   exact orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail n k r
 
+/--
+Source comparison predicate: recovery mass dominates continuation mass.
+
+This names the local comparison condition that is sufficient for the source
+`AtMostHalf` criterion.  It is intentionally a hypothesis package, not an
+unconditional theorem.
+-/
+def RecoveryDominatesContinuation
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowContinuationSiblingMassPow2 n k r ≤
+    orbitWindowRecoverySiblingMassPow2 n k r
+
+/--
+Tail comparison predicate: tail recovery mass dominates tail continuation mass.
+-/
+def TailRecoveryDominatesContinuation
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowContinuationSiblingMassPow2Tail n k r ≤
+    orbitWindowRecoverySiblingMassPow2Tail n k r
+
+/--
+Source budget predicate: recovery covers at least half of retention.
+
+This is often the natural form when a later argument produces a lower bound on
+recovery rather than a direct comparison with continuation.
+-/
+def RecoveryCoversHalfRetention
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowRetentionMassPow2 n k r ≤
+    2 * orbitWindowRecoverySiblingMassPow2 n k r
+
+/-- Tail budget predicate: tail recovery covers at least half of tail retention. -/
+def TailRecoveryCoversHalfRetention
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowRetentionMassPow2Tail n k r ≤
+    2 * orbitWindowRecoverySiblingMassPow2Tail n k r
+
+/--
+Finite-depth range form of source recovery dominance.
+
+This keeps the persistent-comparison hypothesis explicit without proving it.
+-/
+def RecoveryDominatesOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  ∀ j, j < len → RecoveryDominatesContinuation n k (r + j)
+
+/-- Finite-depth range form of tail recovery dominance. -/
+def TailRecoveryDominatesOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  ∀ j, j < len → TailRecoveryDominatesContinuation n k (r + j)
+
+/--
+Failure-mode predicate: source continuation strictly outruns recovery.
+
+This is the obstruction-facing complement direction to
+`RecoveryDominatesContinuation`.
+-/
+def ContinuationOutrunsRecovery
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowRecoverySiblingMassPow2 n k r <
+    orbitWindowContinuationSiblingMassPow2 n k r
+
+/-- Tail failure-mode predicate: tail continuation strictly outruns tail recovery. -/
+def TailContinuationOutrunsRecovery
+    (n : OddNat) (k r : ℕ) : Prop :=
+  orbitWindowRecoverySiblingMassPow2Tail n k r <
+    orbitWindowContinuationSiblingMassPow2Tail n k r
+
+/-- Finite-depth range form of source continuation outrunning recovery. -/
+def ContinuationOutrunsRecoveryOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  ∀ j, j < len → ContinuationOutrunsRecovery n k (r + j)
+
+/-- Finite-depth range form of tail continuation outrunning recovery. -/
+def TailContinuationOutrunsRecoveryOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  ∀ j, j < len → TailContinuationOutrunsRecovery n k (r + j)
+
+/--
+Predicate-facing source half criterion.
+
+This is the readable version of
+`atMostHalf_continuation_of_continuation_le_recovery`.
+-/
+theorem atMostHalf_continuation_of_recoveryDominates
+    (n : OddNat) (k r : ℕ)
+    (h : RecoveryDominatesContinuation n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) :=
+  atMostHalf_continuation_of_continuation_le_recovery n k r h
+
+/-- Predicate-facing tail half criterion. -/
+theorem atMostHalf_tailContinuation_of_tailRecoveryDominates
+    (n : OddNat) (k r : ℕ)
+    (h : TailRecoveryDominatesContinuation n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) :=
+  atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h
+
+/-- Predicate-facing source half criterion from recovery budget coverage. -/
+theorem atMostHalf_continuation_of_recoveryCoversHalf
+    (n : OddNat) (k r : ℕ)
+    (h : RecoveryCoversHalfRetention n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) :=
+  atMostHalf_continuation_of_retention_le_two_recovery n k r h
+
+/-- Predicate-facing tail half criterion from tail recovery budget coverage. -/
+theorem atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
+    (n : OddNat) (k r : ℕ)
+    (h : TailRecoveryCoversHalfRetention n k r) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) :=
+  atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery n k r h
+
+/-- A range dominance hypothesis yields the source half criterion at each depth. -/
+theorem atMostHalf_continuation_of_recoveryDominatesOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : RecoveryDominatesOnRange n k r len) (hj : j < len) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+      (orbitWindowRetentionMassPow2 n k (r + j)) :=
+  atMostHalf_continuation_of_recoveryDominates n k (r + j) (h j hj)
+
+/-- A tail range dominance hypothesis yields the tail half criterion at each depth. -/
+theorem atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : TailRecoveryDominatesOnRange n k r len) (hj : j < len) :
+    AtMostHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
+  atMostHalf_tailContinuation_of_tailRecoveryDominates n k (r + j) (h j hj)
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 0133d74f..7651efe2 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -139,6 +139,7 @@ docs/Collatz-FiniteRatioRetention-101.md
 docs/Collatz-DepthRefinement-102.md
 docs/Collatz-TailDepthRefinement-103.md
 docs/Collatz-FiniteHalfCriterion-104.md
+docs/Collatz-ComparisonPredicates-105.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -283,3 +284,18 @@ orbitWindowContinuationMass_tailBudget
 
 This still does not prove contraction.  It records exactly what local comparison
 is enough to obtain a finite `AtMostHalf` statement.
+
+Checkpoint 105 names that missing local comparison as a first-class predicate:
+
+```lean
+RecoveryDominatesContinuation
+TailRecoveryDominatesContinuation
+RecoveryCoversHalfRetention
+TailRecoveryCoversHalfRetention
+RecoveryDominatesOnRange
+TailRecoveryDominatesOnRange
+```
+
+These are deliberately hypothesis packages.  They mark the exact gap between
+the current finite budget calculus and a future structural contraction
+argument.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md
new file mode 100644
index 00000000..5dbf723c
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md
@@ -0,0 +1,186 @@
+# Collatz Comparison Predicates 105
+
+Checkpoint 105 names the missing comparison conditions in the finite Collatz
+Petal mass calculus.
+
+Previous checkpoints established:
+
+```text
+M = R + K
+K <= R -> AtMostHalf K M
+M <= 2R -> AtMostHalf K M
+```
+
+What remains open is the structural source of either comparison:
+
+```text
+K <= R
+```
+
+or:
+
+```text
+M <= 2R
+```
+
+Checkpoint 105 does not prove those comparisons unconditionally.  It packages
+them as explicit predicates so later arguments can state exactly which gap they
+close.
+
+## Local Comparison Predicates
+
+Source comparison:
+
+```lean
+RecoveryDominatesContinuation
+```
+
+Tail comparison:
+
+```lean
+TailRecoveryDominatesContinuation
+```
+
+These read:
+
+```text
+continuation mass <= recovery mass
+```
+
+for the source or shifted-tail window.
+
+## Budget Coverage Predicates
+
+Source budget predicate:
+
+```lean
+RecoveryCoversHalfRetention
+```
+
+Tail budget predicate:
+
+```lean
+TailRecoveryCoversHalfRetention
+```
+
+These read:
+
+```text
+retention mass <= 2 * recovery mass
+```
+
+This form is useful when an argument produces a lower bound on recovery mass
+rather than a direct comparison with continuation mass.
+
+## Predicate-Facing Half Criteria
+
+The source comparison predicate feeds:
+
+```lean
+atMostHalf_continuation_of_recoveryDominates
+```
+
+The tail comparison predicate feeds:
+
+```lean
+atMostHalf_tailContinuation_of_tailRecoveryDominates
+```
+
+The budget predicates feed:
+
+```lean
+atMostHalf_continuation_of_recoveryCoversHalf
+atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
+```
+
+Thus later proofs can remain at the conceptual level:
+
+```text
+prove the comparison predicate
+  -> obtain AtMostHalf
+```
+
+without unfolding the raw residue counts.
+
+## Range Predicates
+
+Persistent comparison over a finite depth range is named by:
+
+```lean
+RecoveryDominatesOnRange
+TailRecoveryDominatesOnRange
+```
+
+These are deliberately thin:
+
+```text
+for all j < len, comparison holds at depth r+j
+```
+
+The point is not to prove persistence yet.  The point is to name the exact
+hypothesis that an obstruction, drift, or carrier theorem must supply.
+
+The current extraction theorems are:
+
+```lean
+atMostHalf_continuation_of_recoveryDominatesOnRange
+atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
+```
+
+They give the corresponding half criterion at each depth in the finite range.
+
+## Failure-Mode Predicates
+
+The obstruction-facing side is named as well:
+
+```lean
+ContinuationOutrunsRecovery
+TailContinuationOutrunsRecovery
+ContinuationOutrunsRecoveryOnRange
+TailContinuationOutrunsRecoveryOnRange
+```
+
+These predicates record the opposite observation:
+
+```text
+recovery < continuation
+```
+
+They do not prove a contradiction.  They give the future obstruction route a
+precise input shape.
+
+## Next Mathematical Target
+
+The next step is to find a source for the comparison predicate.
+
+Candidate routes:
+
+```text
+height drift:
+  continuation-heavy paths force extra 2-adic height later
+
+collision / obstruction:
+  persistent continuation creates repeated addresses or closed low-peeling loops
+
+odd factor carrier:
+  an additional arithmetic carrier forces recovery mass to appear
+```
+
+Checkpoint 105 isolates the missing theorem shape.  This is the formal gap:
+
+```text
+structural observation -> RecoveryDominatesContinuation
+```
+
+or, in budget form:
+
+```text
+structural observation -> RecoveryCoversHalfRetention
+```
+
+The corresponding obstruction target is:
+
+```text
+ContinuationOutrunsRecoveryOnRange
+  -> height drift / address collision / finite budget pressure
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index c6819cf8..e72ffd37 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -328,6 +328,31 @@ These do not prove the comparison condition.  They make the next target
 explicit: find a structural reason why continuation is no larger than recovery,
 or why recovery covers at least half of retention.
 
+## Comparison Predicates
+
+Checkpoint 105 names the missing comparison conditions:
+
+```lean
+RecoveryDominatesContinuation
+TailRecoveryDominatesContinuation
+RecoveryCoversHalfRetention
+TailRecoveryCoversHalfRetention
+RecoveryDominatesOnRange
+TailRecoveryDominatesOnRange
+```
+
+The predicate-facing half criteria are:
+
+```lean
+atMostHalf_continuation_of_recoveryDominates
+atMostHalf_tailContinuation_of_tailRecoveryDominates
+atMostHalf_continuation_of_recoveryCoversHalf
+atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
+```
+
+Use these names when a later proof has produced a comparison hypothesis and
+wants to consume it without unfolding recovery/continuation counts.
+
 This is the theorem to reach for before writing a custom induction over `k`.
 
 ## Recursive Petal Residues
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 3c1dafd1..5634b157 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -213,6 +213,22 @@ continuation_atMostRatio_one_one_retention
 tailContinuation_atMostRatio_one_one_retention
 recovery_atMostRatio_one_one_retention
 tailRecovery_atMostRatio_one_one_retention
+RecoveryDominatesContinuation
+TailRecoveryDominatesContinuation
+RecoveryCoversHalfRetention
+TailRecoveryCoversHalfRetention
+RecoveryDominatesOnRange
+TailRecoveryDominatesOnRange
+ContinuationOutrunsRecovery
+TailContinuationOutrunsRecovery
+ContinuationOutrunsRecoveryOnRange
+TailContinuationOutrunsRecoveryOnRange
+atMostHalf_continuation_of_recoveryDominates
+atMostHalf_tailContinuation_of_tailRecoveryDominates
+atMostHalf_continuation_of_recoveryCoversHalf
+atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
+atMostHalf_continuation_of_recoveryDominatesOnRange
+atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-105.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-105.md
new file mode 100644
index 00000000..60179aed
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-105.md
@@ -0,0 +1,165 @@
+# Report Petal 105
+
+## Summary
+
+Checkpoint 105 introduced comparison-condition predicates for the Collatz
+Petal finite mass calculus.
+
+The goal was not to prove unconditional contraction.  The goal was to name the
+missing local comparison that would imply contraction-like `AtMostHalf`
+statements.
+
+## Implemented Lean Surface
+
+Local comparison predicates:
+
+```lean
+RecoveryDominatesContinuation
+TailRecoveryDominatesContinuation
+```
+
+Budget coverage predicates:
+
+```lean
+RecoveryCoversHalfRetention
+TailRecoveryCoversHalfRetention
+```
+
+Finite range predicates:
+
+```lean
+RecoveryDominatesOnRange
+TailRecoveryDominatesOnRange
+```
+
+Predicate-facing half criteria:
+
+```lean
+atMostHalf_continuation_of_recoveryDominates
+atMostHalf_tailContinuation_of_tailRecoveryDominates
+atMostHalf_continuation_of_recoveryCoversHalf
+atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
+```
+
+Range extraction theorems:
+
+```lean
+atMostHalf_continuation_of_recoveryDominatesOnRange
+atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
+```
+
+Failure-mode predicates:
+
+```lean
+ContinuationOutrunsRecovery
+TailContinuationOutrunsRecovery
+ContinuationOutrunsRecoveryOnRange
+TailContinuationOutrunsRecoveryOnRange
+```
+
+## Mathematical Reading
+
+The current finite calculus is:
+
+```text
+M = R + K
+K <= R -> 2K <= M
+```
+
+Checkpoint 105 turns `K <= R` into a named hypothesis:
+
+```text
+RecoveryDominatesContinuation
+```
+
+and turns the range form into:
+
+```text
+RecoveryDominatesOnRange
+```
+
+This makes the next gap precise:
+
+```text
+what structural observation proves RecoveryDominatesContinuation?
+```
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-ComparisonPredicates-105.md
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
+## Additional Inference
+
+This checkpoint makes the future proof obligation sharper.
+
+Before 105, the missing step was vague:
+
+```text
+show contraction
+```
+
+After 105, the missing step is a named bridge:
+
+```text
+structural observation -> RecoveryDominatesContinuation
+```
+
+or:
+
+```text
+structural observation -> RecoveryCoversHalfRetention
+```
+
+## Next Candidate
+
+The obstruction-style predicate for the opposite case was small enough to add
+in this checkpoint:
+
+```text
+ContinuationOutrunsRecovery
+```
+
+If recovery does not dominate, then continuation is strictly larger than
+recovery.  Naming that failure mode would give the False/obstruction path a
+target:
+
+```text
+ContinuationOutrunsRecovery on a range
+  -> address pressure / height drift / collision pressure
+```
+
+This fits the current project style: prove truth where possible, and name the
+failure condition when the proof needs another structure.
+
+The next checkpoint can now try to attach a first weak consequence to
+`ContinuationOutrunsRecoveryOnRange`, probably not a contradiction yet, but an
+accumulated pressure statement over the finite range.
````
`````
