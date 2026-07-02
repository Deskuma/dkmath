# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 1343a1039e1aa6e3dc71711d499fbc6f146da4d0

## Report

Checkpoint 103 完了です。

`DkMath.Collatz.PetalBridge` に tail 側の対称補題を追加しました。主な追加は以下です。

- `orbitWindowResidueCountPow2Tail_refine_succ`
- `orbitWindowRetentionMassPow2Tail_split`
- `orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail`
- `orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail`
- `orbitWindowRecoveryMass_forces_tailRecovery`
- `orbitWindowContinuationMass_forces_tailRetention`
- おまけ: `orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation`

これで

```text
source continuation <= tail retention
tail retention = tail recovery + tail continuation
```

を Lean 定理として直接読めるようになりました。

ドキュメントも同期済みです。

- [Collatz-TailDepthRefinement-103.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md)
- [report-petal-103.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-103.md)
- README / Guide / Status も更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` は一致なし

既知の上流 warning: `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は従来通りです。

## Review

## 1. 状況分析

うむ。checkpoint `103` は、No.102 の自然な完成形じゃ。

No.102 では source window 側で、

$$
M_r=R_r+K_r
$$

つまり、

$$
\text{retention mass}=\text{recovery sibling mass}+\text{continuation sibling mass}
$$

が閉じた。
今回 No.103 では、その **shifted-tail 側の対称版** が閉じた。

主な追加は、

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_forces_tailRetention
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

じゃ。レポートでも、source window と shifted-tail window の両方で recursive Petal split が使えるようになり、`source continuation <= tail retention = tail recovery + tail continuation` を Lean 定理として直接読めるようになった、と整理されている。

これはかなり重要。
これで **source 側の分解** と **tail 側の受け皿分解** が揃った。

## 2. 今回の核心

今回閉じた式はこれじゃ。

$$
M^{tail}_r(n,k)=R^{tail}_r(n,k)+K^{tail}_r(n,k)
$$

source 版と並べると、

$$
M_r(n,k)=R_r(n,k)+K_r(n,k)
$$

$$
M^{tail}_r(n,k)=R^{tail}_r(n,k)+K^{tail}_r(n,k)
$$

となる。

ここで、

$$
M_r
$$

は source retention mass、

$$
M^{tail}_r
$$

は shifted-tail retention mass じゃ。

そして今回の forcing alias により、

$$
K_{r+1}(n,k)\le M^{tail}_{r+1}(n,k)
$$

が読みやすい theorem 名で使えるようになった。

さらに tail split と組み合わせて、

$$
K_{r+1}(n,k)\le R^{tail}*{r+1}(n,k)+K^{tail}*{r+1}(n,k)
$$

が直接 theorem 化された。

これが、

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

じゃ。

## 3. レビュー

## 3.1. tail 側を補った判断は正しい

No.102 の source split だけでも、親 cell の分解は言えた。
しかし Collatz の一歩遷移は source から tail へ移る。

だから本当に欲しいのは、

```text
source 側で continuation mass を見る
tail 側でその受け皿 retention mass を分解する
```

という二段構えじゃ。

今回、tail 側に

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
```

が入ったことで、この二段構えが成立した。

## 3.2. `forcing` 名が効いている

今回の alias 名はかなり良い。

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
```

これは単なる不等式の別名ではなく、数学的な読みを固定している。

つまり、

$$
K_{r+1}\le M^{tail}_{r+1}
$$

を、

```text
source continuation mass が tail retention mass を強制する
```

と読める。

ここで「強制する」はよい語彙じゃ。
大きな continuation mass があるなら、次の窓の retention 受け皿にも、それを収めるだけの質量が必要になる。

## 3.3. `le_tailRecovery_add_tailContinuation` は次章への橋

今回のおまけ theorem、

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

は、かなり使いやすい。

これは二本の theorem を合成したもの。

```text
source continuation <= tail retention
tail retention = tail recovery + tail continuation
```

したがって、

```text
source continuation <= tail recovery + tail continuation
```

が得られる。

これ自体は contraction を言わない。
しかし「continuation mass の行き先予算」が明示された。

この theorem があると、次に

```text
tail recovery が十分大きいか
tail continuation が残り続けるか
```

という分岐議論に入れる。

## 4. 数学的解説

これまでの構図をまとめると、source 側では、

$$
M_r=R_r+K_r
$$

がある。

これは、深さ \(r\) の retention cell が、深さ \(r+1\) で recovery sibling と continuation sibling に分かれるという意味である。

今回 tail 側でも、

$$
M^{tail}_r=R^{tail}_r+K^{tail}_r
$$

が得られた。

そして既存の channel-flow により、source continuation は tail retention に入る。

$$
K_{r+1}\le M^{tail}_{r+1}
$$

tail retention を分解すると、

$$
M^{tail}*{r+1}=R^{tail}*{r+1}+K^{tail}_{r+1}
$$

なので、

$$
K_{r+1}\le R^{tail}*{r+1}+K^{tail}*{r+1}
$$

が出る。

この式の意味はこうじゃ。

```text
低剥離を続ける source continuation mass は、
次窓では tail retention cylinder に収まり、
その中で tail recovery と tail continuation に再分配される。
```

つまり、Collatz の low-peeling path を「毎 step で retention cylinder に再投入される質量」として追えるようになった。

## 5. 今回閉じたもの

今回で閉じたのは、

```text
source split
tail split
source-to-tail forcing
forcing + tail split の合成
```

じゃ。

流れとしては、

```text
No.100:
  finite channel-flow

No.101:
  finite ratio / retention mass names

No.102:
  source retention split

No.103:
  tail retention split + forcing package
```

となった。

これはかなり綺麗な積み上げじゃ。

## 6. まだ閉じていないもの

ここでまだ言えていないのは、**縮小** じゃ。

たとえば、次のようなことはまだ theorem ではない。

$$
2K_r\le M_r
$$

あるいは、

$$
K_{r+1}<K_r
$$

あるいは、

$$
K_r
$$

が深さとともに必ず減る、という主張。

今回できたのは、行き先予算の構造化じゃ。

```text
continuation mass は tail retention に流れる
tail retention は recovery と continuation に分かれる
```

ここから「必ずどこかで recovery が一定量出る」や「continuation が全部残ることはできない」を言うには、追加の仮定か、別の構造が必要になる。

## 7. 次の指示

次は、いきなり強い contraction を狙うより、**反復可能な forcing chain** を薄く整えるのがよい。

今あるのは一歩分。

$$
K_{r+1}\le R^{tail}*{r+1}+K^{tail}*{r+1}
$$

次に欲しいのは、この読みを「次 depth / 次 window でも使える」形にすること。

ただし、source と tail は window index がずれているだけなので、まずは定理名と補題の整理が先でよい。

## 7.1. まず recovery-or-continuation budget を named theorem 化

今回すでに、

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

がある。

次は同様に recovery 側も package してよい。

```lean
theorem orbitWindowRecoveryMass_le_tailRecovery
```

は既に alias としてあるので、もし必要なら、

```lean
theorem orbitWindowRecoveryMass_le_tailRecovery_add_tailContinuation
```

も置ける。

ただし、これはやや弱いので、優先度は低い。

## 7.2. `AtMostHalf` と split の接続

No.101 で `AtMostHalf` を導入した。
No.102/103 で split が入った。
次はこれを接続する theorem が自然じゃ。

たとえば、

```lean
theorem atMostHalf_continuation_of_recovery_le_continuation
```

のような形。

数学的には、

$$
M=R+K
$$

かつ、

$$
K\le R
$$

なら、

$$
2K\le M
$$

である。

つまり、

```text
continuation <= recovery
  -> continuation is at most half of retention
```

Lean 候補はこう。

```lean
theorem atMostHalf_continuation_of_continuation_le_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2 n k r ≤
        orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r)
```

証明は、

$$
M_r=R_r+K_r
$$

を使って `omega` で落ちるはずじゃ。

これは強い事実を証明しているわけではない。
しかし、「何を示せば半分以下と言えるか」を theorem 化する。
これは次章の方針補題として非常に良い。

## 8. 一歩先ゆく推論

今後の大きな目標は、低剥離 continuation が長く続くことに何らかの「予算制約」をかけることじゃ。

今の構図は、

$$
K_{r+1}\le R^{tail}*{r+1}+K^{tail}*{r+1}
$$

である。

もし毎階層で continuation が recovery より大きいなら、

$$
R_r<K_r
$$

となり、mass はかなり continuation 側に偏る。

逆に、どこかで

$$
K_r\le R_r
$$

が出れば、

$$
2K_r\le M_r
$$

なので、continuation は親 retention の半分以下になる。

したがって、次の探索目標は、

```text
どの条件なら continuation <= recovery が出るか
```

じゃ。

これは純粋な 2-adic 分布だけでは必ずしも出ないかもしれない。
そこに、次の層として **height drift** または **odd factor carrier** が関わる可能性がある。

しかし、いきなり odd factor に行く前に、まずは条件付き補題として、

```text
continuation <= recovery を仮定すると AtMostHalf が出る
```

を作るのがよい。

これにより、「あと何を証明すればよいか」が明確になる。

## 9. 賢狼が試して欲しい実験補題

## 実験 A: split から half を出す source 版

```lean
theorem atMostHalf_continuation_of_continuation_le_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2 n k r ≤
        orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split]
  omega
```

## 実験 B: split から half を出す tail 版

```lean
theorem atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2Tail n k r ≤
        orbitWindowRecoverySiblingMassPow2Tail n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega
```

## 実験 C: recovery が少なくとも半分なら continuation は半分以下

これは B の裏側。

```lean
theorem atMostHalf_continuation_of_retention_le_two_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowRetentionMassPow2 n k r ≤
        2 * orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split] at h ⊢
  omega
```

## 実験 D: tail retention budget package

今回の theorem を少し別名で、次章向けに置く。

```lean
theorem orbitWindowContinuationMass_tailBudget
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k
```

これは alias だけだが、名前を `tailBudget` にすると後続が読みやすい。

## 実験 E: tail child bounds as ratio witness

```lean
theorem tailContinuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail n k r
```

source 版も同様。

```lean
theorem continuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2_le_retentionMass n k r
```

これは弱いが、ratio witness と mass bound を接続する最初の橋になる。

## 10. 次コミットの推奨順

```text
1. continuation <= recovery -> AtMostHalf continuation retention

2. tailContinuation <= tailRecovery -> AtMostHalf tailContinuation tailRetention

3. retention <= 2 * recovery -> AtMostHalf continuation retention

4. continuation/tailContinuation の AtMostRatioNat 1 1 bridge

5. tailBudget alias

6. docs:
   finite half criterion / contraction candidate を追記
```

ここまで行くと、

```text
split がある
比較条件がある
半分以下が出る
```

という ratio 層の最小 calculus ができる。

## 11. 総括

checkpoint `103` は、No.102 の source split に対して、tail 側の split と forcing を補い、finite mass-flow grammar をかなり完成させた。

いま見えている中心式は、

$$
K_{r+1}\le M^{tail}*{r+1}=R^{tail}*{r+1}+K^{tail}_{r+1}
$$

じゃ。

これはまだ contraction ではない。
しかし、低剥離 continuation mass の行き先が、tail retention cylinder の二つの child budget に分解されるところまで Lean で読める。

次は、

$$
K_r\le R_r
$$

のような比較条件から、

$$
2K_r\le M_r
$$

を出す `AtMostHalf` 補題を整えるのがよい。

うむ。
ここまで来ると、Collatz.PetalBridge は「座標観測」から「有限質量予算の力学」へ入ってきた。これはかなり良い進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8dcdb4e9..f9d74cc4 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1770,6 +1770,69 @@ theorem orbitWindowContinuationSiblingMassPow2_le_retentionMass
   rw [orbitWindowRetentionMass_split]
   omega
 
+/--
+Depth refinement for generic shifted-tail residue counts.
+
+This is the tail-window counterpart of
+`orbitWindowResidueCountPow2_refine_succ`.
+-/
+theorem orbitWindowResidueCountPow2Tail_refine_succ
+    (n : OddNat) (k depth residue : ℕ)
+    (hres : residue < 2 ^ depth) :
+    orbitWindowResidueCountPow2Tail n k depth residue =
+      orbitWindowResidueCountPow2Tail n k (depth + 1) residue +
+        orbitWindowResidueCountPow2Tail n k (depth + 1)
+          (residue + 2 ^ depth) := by
+  induction k with
+  | zero =>
+      simp [orbitWindowResidueCountPow2Tail]
+  | succ k ih =>
+      rw [orbitWindowResidueCountPow2Tail_succ]
+      rw [orbitWindowResidueCountPow2Tail_succ]
+      rw [orbitWindowResidueCountPow2Tail_succ]
+      rw [ih]
+      have hindicator :=
+        pow2ResidueIndicator_refine_succ
+          (oddOrbitLabel n (k + 1)) depth residue hres
+      omega
+
+/--
+Tail retention mass splits into the tail recovery and tail continuation sibling
+masses at the next depth.
+-/
+theorem orbitWindowRetentionMassPow2Tail_split
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRetentionMassPow2Tail n k r =
+      orbitWindowRecoverySiblingMassPow2Tail n k r +
+        orbitWindowContinuationSiblingMassPow2Tail n k r := by
+  unfold orbitWindowRetentionMassPow2Tail
+  unfold orbitWindowRecoverySiblingMassPow2Tail
+  unfold orbitWindowContinuationSiblingMassPow2Tail
+  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
+  have hsplit :=
+    orbitWindowResidueCountPow2Tail_refine_succ n k r (2 ^ r - 1) hres
+  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
+    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
+    rw [pow_succ]
+    omega
+  simpa [hright] using hsplit
+
+/-- Tail recovery sibling mass is bounded by tail retention mass. -/
+theorem orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k r ≤
+      orbitWindowRetentionMassPow2Tail n k r := by
+  rw [orbitWindowRetentionMassPow2Tail_split]
+  omega
+
+/-- Tail continuation sibling mass is bounded by tail retention mass. -/
+theorem orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowContinuationSiblingMassPow2Tail n k r ≤
+      orbitWindowRetentionMassPow2Tail n k r := by
+  rw [orbitWindowRetentionMassPow2Tail_split]
+  omega
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -2716,6 +2779,18 @@ theorem orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
   unfold orbitWindowRecoverySiblingMassPow2 orbitWindowRecoverySiblingMassPow2Tail
   exact orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper r hr n k
 
+/--
+Forcing-name alias for the recovery channel-flow theorem.
+
+The source recovery mass at parent depth `r + 1` forces at least that much mass
+in the shifted-tail recovery sibling at parent depth `r`.
+-/
+theorem orbitWindowRecoveryMass_forces_tailRecovery
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRecoverySiblingMassPow2Tail n k r :=
+  orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass r hr n k
+
 /--
 Count-level recursive Petal transition for the continuation sibling.
 
@@ -2779,6 +2854,41 @@ theorem orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
   unfold orbitWindowContinuationSiblingMassPow2 orbitWindowRetentionMassPow2Tail
   exact orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper r hr n k
 
+/--
+Forcing-name alias for the continuation channel-flow theorem.
+
+The source continuation mass at parent depth `r + 1` must fit inside shifted-tail
+retention at the same depth.
+-/
+theorem orbitWindowContinuationMass_forces_tailRetention
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
+  orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass r hr n k
+
+/--
+Continuation mass is bounded by the two child masses of the shifted-tail
+retention cylinder.
+
+This packages the two-step reading:
+
+`source continuation <= tail retention`
+and
+`tail retention = tail recovery + tail continuation`.
+-/
+theorem orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
+        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) := by
+  calc
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1)
+        ≤ orbitWindowRetentionMassPow2Tail n k (r + 1) :=
+          orbitWindowContinuationMass_forces_tailRetention r hr n k
+    _ = orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
+          orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) := by
+        rw [orbitWindowRetentionMassPow2Tail_split]
+
 /--
 Tail continuation sibling mass is definitionally the same as tail retention at
 the next depth.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index d3b92801..8de83dfb 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -137,6 +137,7 @@ docs/Collatz-Package-Structure.md
 docs/Collatz-FiniteChannelFlow-100.md
 docs/Collatz-FiniteRatioRetention-101.md
 docs/Collatz-DepthRefinement-102.md
+docs/Collatz-TailDepthRefinement-103.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -245,3 +246,24 @@ retention mass at depth r
 This is still finite `Nat` counting.  It does not use probability, limits, or
 real-valued density.  It gives the next local tool for saying that a long
 low-peeling path must keep occupying a nested retention cylinder.
+
+Checkpoint 103 closes the shifted-tail counterpart:
+
+```lean
+orbitWindowResidueCountPow2Tail_refine_succ
+orbitWindowRetentionMassPow2Tail_split
+orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
+orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowRecoveryMass_forces_tailRecovery
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+The source and shifted-tail windows now both have the same recursive Petal
+split.  This makes later mass-flow statements readable as:
+
+```text
+source continuation mass
+  <= shifted-tail retention mass
+  = shifted-tail recovery mass + shifted-tail continuation mass
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 47c6bb71..ceaa90bb 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -267,6 +267,33 @@ Use this theorem when an argument needs to show that recovery and continuation
 are not independent extra mass.  They are the two subcells of the previous
 retention cylinder.
 
+Checkpoint 103 adds the shifted-tail counterpart:
+
+```lean
+orbitWindowResidueCountPow2Tail_refine_succ
+orbitWindowRetentionMassPow2Tail_split
+```
+
+So the same reading is available in the receiving window:
+
+```text
+tail retention mass at depth r
+  = tail recovery sibling mass at depth r+1
+    + tail continuation sibling mass at depth r+1
+```
+
+The useful forcing aliases are:
+
+```lean
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowRecoveryMass_forces_tailRecovery
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+Use these names when the argument is conceptually about mass flow from the
+source window into the shifted-tail window.  Use the split theorems when the
+argument is about decomposing a retention cylinder into its two child cells.
+
 This is the theorem to reach for before writing a custom induction over `k`.
 
 ## Recursive Petal Residues
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 2b9a3743..10ec37e6 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -201,6 +201,10 @@ orbitWindowResidueCountPow2_refine_succ
 orbitWindowRetentionMass_split
 orbitWindowRecoverySiblingMassPow2_le_retentionMass
 orbitWindowContinuationSiblingMassPow2_le_retentionMass
+orbitWindowResidueCountPow2Tail_refine_succ
+orbitWindowRetentionMassPow2Tail_split
+orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
+orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -278,7 +282,10 @@ orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
 orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
 orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
 orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
+orbitWindowRecoveryMass_forces_tailRecovery
 orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
 orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md
new file mode 100644
index 00000000..5a232b9e
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md
@@ -0,0 +1,123 @@
+# Collatz Tail Depth Refinement 103
+
+Checkpoint 103 closes the shifted-tail side of the recursive Petal split.
+
+Checkpoint 102 proved the source-window split:
+
+```lean
+orbitWindowResidueCountPow2_refine_succ
+orbitWindowRetentionMass_split
+```
+
+Checkpoint 103 adds the matching shifted-tail split:
+
+```lean
+orbitWindowResidueCountPow2Tail_refine_succ
+orbitWindowRetentionMassPow2Tail_split
+```
+
+## Tail Count Split
+
+The general theorem is:
+
+```lean
+orbitWindowResidueCountPow2Tail_refine_succ
+```
+
+It says that shifted-tail occupation in a valid parent residue cell at depth
+`depth` is the sum of occupation in its two child cells at depth `depth + 1`.
+
+In formula form:
+
+```text
+tailCount(depth, residue)
+  =
+tailCount(depth+1, residue)
+  + tailCount(depth+1, residue + 2^depth)
+```
+
+The proof uses the same pointwise indicator theorem as the source case:
+
+```lean
+pow2ResidueIndicator_refine_succ
+```
+
+The only difference is that the point being counted is
+`oddOrbitLabel n (i + 1)`.
+
+## Tail Retention Split
+
+The named tail retention theorem is:
+
+```lean
+orbitWindowRetentionMassPow2Tail_split
+```
+
+It reads:
+
+```text
+tail retention mass at depth r
+  =
+tail recovery sibling mass at depth r+1
+  + tail continuation sibling mass at depth r+1
+```
+
+This gives source/tail symmetry:
+
+```text
+M_r        = R_r        + K_r
+M_tail_r   = R_tail_r   + K_tail_r
+```
+
+## Child Bounds
+
+The child masses are bounded by their parent tail retention mass:
+
+```lean
+orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
+orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
+```
+
+These are direct consequences of the tail split.
+
+## Forcing Aliases
+
+Two aliases were added to make later mass-flow arguments read naturally:
+
+```lean
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowRecoveryMass_forces_tailRecovery
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+They restate existing recursive channel-flow theorems with forcing-oriented
+names.
+
+The important chain is now:
+
+```text
+source continuation mass
+  <= tail retention mass
+  = tail recovery mass + tail continuation mass
+```
+
+This is the first clean finite mass-flow grammar for following a low-peeling
+Collatz segment through nested Petal cylinders.
+
+## Packaged Continuation Budget
+
+The two-line chain is also packaged directly as:
+
+```lean
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+This theorem combines:
+
+```lean
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowRetentionMassPow2Tail_split
+```
+
+It does not prove contraction by itself, but it exposes the exact destination
+budget of continuation mass.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-103.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-103.md
new file mode 100644
index 00000000..7f3050e1
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-103.md
@@ -0,0 +1,145 @@
+# Report Petal 103
+
+## Summary
+
+Checkpoint 103 completed the shifted-tail counterpart of the depth refinement
+introduced in checkpoint 102.
+
+The source window and shifted-tail window now both support the same recursive
+Petal split:
+
+```text
+retention = recovery + continuation
+```
+
+## Implemented Lean Surface
+
+Tail count refinement:
+
+```lean
+orbitWindowResidueCountPow2Tail_refine_succ
+```
+
+Tail retention split:
+
+```lean
+orbitWindowRetentionMassPow2Tail_split
+```
+
+Tail child bounds:
+
+```lean
+orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
+orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
+```
+
+Forcing aliases:
+
+```lean
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowRecoveryMass_forces_tailRecovery
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+## Mathematical Reading
+
+Checkpoint 102 gave:
+
+```text
+M_r = R_r + K_r
+```
+
+for source-window retention mass.
+
+Checkpoint 103 gives:
+
+```text
+M_tail_r = R_tail_r + K_tail_r
+```
+
+for shifted-tail retention mass.
+
+Together with the existing channel-flow theorem, the continuation channel now
+has a clean finite mass-flow reading:
+
+```text
+source continuation mass
+  <= shifted-tail retention mass
+  = shifted-tail recovery mass + shifted-tail continuation mass
+```
+
+This does not prove contraction.  It fixes the destination budget of the
+continuation mass inside the next observation window.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-TailDepthRefinement-103.md
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
+## Extra Result
+
+The initially proposed next-step theorem was small enough to implement in this
+checkpoint:
+
+```lean
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+```
+
+It packages:
+
+```text
+source continuation <= tail retention
+tail retention = tail recovery + tail continuation
+```
+
+into:
+
+```text
+source continuation <= tail recovery + tail continuation
+```
+
+## Next Inference
+
+The next checkpoint can now focus on a genuine contraction or obstruction
+condition rather than the bookkeeping chain.
+
+Candidate shapes:
+
+```lean
+AtMostHalf
+  (orbitWindowContinuationSiblingMassPow2 n k (r + 1))
+  (orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
+    orbitWindowContinuationSiblingMassPow2Tail n k (r + 1))
+```
+
+or a contradiction-style theorem showing that a proposed low-peeling cylinder
+cannot be closed under too many consecutive continuation steps without
+exceeding the finite window budget.
````
`````
