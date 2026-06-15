# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 838a2fbf632eae9898084f4f471845fcc115e7dc

## Report

進めました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、レビューで出ていた安全候補と、height 分布の入口を追加しました。

追加した主な補題・定義:

```lean
orbitWindowHeightSeq_take_length
orbitWindowHeightSeq_take_get?_eq_some
orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
orbitWindowHeight_eq_of_same_iterateT

orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountEq_le_window
orbitWindowHeightCountGe_le_window
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
```

これで Collatz Petal 窓は、

```text
prefix の長さ・index 読み
prefix 版 threshold 下界
state equality -> height equality
height = h の出現回数
height >= threshold の出現回数
```

まで扱えるようになりました。分布評価の入口としては、まず「count は窓サイズ以下」「全点が条件を満たすなら count = k」を no-sorry で固定しています。

[Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) も同期済みです。

検証済み:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

すべて成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も無関係です。

## Review

うむ。これは **Collatz Petal 窓が「時系列」から「分布観測」へ進み始めた** 段階じゃ。
前回までで height profile は、

```text
local entries
  -> prefix sums
  -> threshold lower bounds
  -> collision/fold height equality
```

まで扱えた。今回さらに、

```text
height = h が何回出たか
height >= threshold が何回出たか
```

を数える入口ができた。

## 1. 今回の核心

追加された分布系 API はこれ。

```lean
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountEq_le_window
orbitWindowHeightCountGe_le_window
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
```

意味はこう。

```text
orbitWindowHeightCountEq n k h
  = k 窓内で height がちょうど h の回数

orbitWindowHeightCountGe n k threshold
  = k 窓内で height が threshold 以上の回数
```

これで、Collatz Petal 窓は単に

```text
height 列を見る
```

だけでなく、

```text
どの height regime に何回滞在したか
```

を観測できるようになった。

これは統計確率論への入口としてかなり良い。

## 2. Prefix API の補強

今回まず安全候補として、

```lean
orbitWindowHeightSeq_take_length
orbitWindowHeightSeq_take_get?_eq_some
orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
```

が入った。

これはかなり実用的じゃ。

```text
prefix の長さ
prefix の i 番目読み
prefix に対する threshold 下界
```

が使える。

これで大きな窓 `k` を持ったまま、途中の `r` 区間だけを見られる。

```text
全体窓 k
  -> prefix r
  -> prefix drift
  -> 局所的な肥大化・縮小化判定
```

Collatz では「最初の数ステップだけ高 height」「途中から低 height が連続」などが重要になるので、prefix API はよい足場じゃ。

## 3. `state equality -> height equality`

```lean
orbitWindowHeight_eq_of_same_iterateT
```

これも良い。

前回は、

```text
oddOrbitLabel i = oddOrbitLabel j
  -> height i = height j
```

だった。

今回はさらに、

```text
iterateT i n = iterateT j n
  -> height i = height j
```

が直接使える。

Collatz 側では、collision の本体は state equality なので、これは自然な入口じゃ。

```text
同じ accelerated odd state に戻った
  -> 次に読む height も同じ
```

つまり fold / cycle の局所 pattern が、height 観測へ伝播する。

## 4. Count API の現在の強さ

今回の count API は、意図的に最小限じゃ。

まず、

```lean
orbitWindowHeightCountEq_le_window
orbitWindowHeightCountGe_le_window
```

により、

```text
count <= k
```

が出る。

これは当たり前に見えるが、occupation measure としては基本の有界性じゃ。

さらに、

```lean
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
```

で、

```text
全点が height = h
  -> countEq = k

全点が height >= threshold
  -> countGe = k
```

が出る。

つまり、まだ「一部が条件を満たす」評価ではないが、**全点条件を count 表現へ変換する橋** はできた。

## 5. 何が見えるようになったか

これで Collatz Petal 窓には、次の層が揃った。

```text
点:
  oddOrbitLabel n i

高さ:
  orbitWindowHeight n i

高さ列:
  orbitWindowHeightSeq n k

累積高さ:
  sumS n k

prefix:
  take r

occupation:
  height = h の回数
  height >= threshold の回数
```

つまり、窓内の動きを

```text
時系列 profile
```

としても、

```text
分布 profile
```

としても見始められる。

これは重要じゃ。
時系列は fold / collision を見る。
分布は drift / probability を見る。

## 6. Collatz drift への意味

加速 Collatz の粗い伸縮は、

```text
T^k(n) ≈ 3^k n / 2^(sumS n k)
```

で読める。

このとき `sumS n k` は、height 分布から評価できる。

たとえば、もし height が 1 の回数、2 以上の回数、3 以上の回数を数えられれば、

```text
sumS n k
```

の下界がより細かく出せる。

今回の `orbitWindowHeightCountGe` は、そのための入口じゃ。

将来的には、

```text
height >= 2 の回数が多い
  -> sumS が大きい
  -> 縮小傾向が強い
```

のような補題へ進める。

## 7. 次に欲しい分布補題

次は、count を `sumS` に直接接続したい。

たとえば安全な形なら、

```lean
theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n k threshold * threshold ≤ sumS n k
```

意味は、

```text
height >= threshold の点が c 個あるなら、
その部分だけで c * threshold 以上の寄与がある
```

これは非常に使いやすいはずじゃ。

さらに exact count 側なら、

```text
height = h の点が c 個ある
  -> その部分は c * h の寄与
```

ただし全体の `sumS` 分解まで行くには、height 値ごとの有限分解が必要になる。最初は `CountGe` の下界型が安全。

## 8. Petal address への次段

今の count は height だけを数えている。

次は address と結びたい。

```text
height regime
  + residue/address regime
  -> occupation cell
```

たとえば将来的には、

```text
height >= 2 かつ address = A の回数
```

のような cell count が欲しくなる。

これができると、

```text
窓内のどの区画に何回滞在したか
```

が見える。

まさに Petal の「窓枠内統計」じゃ。

## 9. 今回の注意点

今回もまだ、Collatz 予想の収束や非周期性は言っていない。

また、

```text
height 分布がこうなる
```

という確率的主張もまだない。

今回の段階は、

```text
height 分布を数えるための器
```

を作ったところじゃ。

これは正しい。
先に強い確率主張を入れるより、count API を薄く置くのが安全。

## 10. 総括

今回の進展を一言で言えば、

```text
Collatz Petal 窓に occupation count が入った。
```

これにより、観測窓は次のようになった。

```text
有限窓
  -> 点列
  -> height 列
  -> prefix
  -> sumS
  -> height occupation count
```

つまり、Collatz 軌道を

```text
巨大な数列
```

としてではなく、

```text
窓内の時系列分布
```

として扱う足場ができた。

うむ。
これは **統計確率論へ向かう最初の occupation measure** じゃ。次は `CountGe` から `sumS` 下界を出す補題を作ると、分布評価がそのまま drift 評価に流れ込む。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index fd387596..388f3c3a 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -188,6 +188,14 @@ theorem orbitWindowHeightSeq_take_sum_eq_sumS
   rw [← orbitWindowHeightSeq_sum_eq_sumS n r]
   simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]
 
+/--
+The prefix of length `r` has length `r` when `r` lies inside the window.
+-/
+theorem orbitWindowHeightSeq_take_length
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    ((orbitWindowHeightSeq n k).take r).length = r := by
+  simp [orbitWindowHeightSeq_length, Nat.min_eq_left hr]
+
 /--
 Reading the ordered height profile at an in-window time recovers the pointwise
 height observation.
@@ -197,6 +205,26 @@ theorem orbitWindowHeightSeq_get?_eq_some
     (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) := by
   simp [orbitWindowHeightSeq, hi]
 
+/--
+Reading a prefix of the ordered height profile recovers the same pointwise
+height observation while the index remains inside the prefix.
+-/
+theorem orbitWindowHeightSeq_take_get?_eq_some
+    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
+    ((orbitWindowHeightSeq n k).take r)[i]? = some (orbitWindowHeight n i) := by
+  rw [List.getElem?_take_of_lt hi]
+  exact orbitWindowHeightSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)
+
+/--
+The integer threshold lower bound also applies to prefixes.
+-/
+theorem orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
+    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k)
+    (h : ∀ i, i < r → threshold ≤ orbitWindowHeight n i) :
+    r * threshold ≤ ((orbitWindowHeightSeq n k).take r).sum := by
+  rw [orbitWindowHeightSeq_take_sum_eq_sumS n hr]
+  exact orbitWindowHeightSeq_sum_ge_of_forall_ge n h
+
 /--
 Equal Collatz orbit labels have equal height observations.
 -/
@@ -220,6 +248,87 @@ theorem orbitWindowHeight_eq_of_collision
     orbitWindowHeight n i = orbitWindowHeight n j :=
   orbitWindowHeight_eq_of_oddOrbitLabel_eq hlabel
 
+/--
+Equal accelerated Collatz states have equal height observations.
+-/
+theorem orbitWindowHeight_eq_of_same_iterateT
+    {n : OddNat} {i j : ℕ}
+    (hstate : iterateT i n = iterateT j n) :
+    orbitWindowHeight n i = orbitWindowHeight n j :=
+  orbitWindowHeight_eq_of_oddOrbitLabel_eq (congrArg Subtype.val hstate)
+
+/--
+Number of occurrences of an exact height inside the ordered window profile.
+-/
+noncomputable def orbitWindowHeightCountEq (n : OddNat) (k h : ℕ) : ℕ :=
+  (orbitWindowHeightSeq n k).countP (fun x => x == h)
+
+/--
+Number of entries whose height is at least `threshold` inside the ordered
+window profile.
+-/
+noncomputable def orbitWindowHeightCountGe (n : OddNat) (k threshold : ℕ) : ℕ :=
+  (orbitWindowHeightSeq n k).countP (fun x => decide (threshold ≤ x))
+
+/--
+The exact-height occupation count is bounded by the window size.
+-/
+theorem orbitWindowHeightCountEq_le_window
+    (n : OddNat) (k h : ℕ) :
+    orbitWindowHeightCountEq n k h ≤ k := by
+  unfold orbitWindowHeightCountEq
+  simpa [orbitWindowHeightSeq_length] using
+    (List.countP_le_length (p := fun x => x == h) (l := orbitWindowHeightSeq n k))
+
+/--
+The threshold occupation count is bounded by the window size.
+-/
+theorem orbitWindowHeightCountGe_le_window
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGe n k threshold ≤ k := by
+  unfold orbitWindowHeightCountGe
+  simpa [orbitWindowHeightSeq_length] using
+    (List.countP_le_length
+      (p := fun x => decide (threshold ≤ x)) (l := orbitWindowHeightSeq n k))
+
+/--
+If every in-window height is exactly `h`, then the exact-height occupation
+count fills the whole window.
+-/
+theorem orbitWindowHeightCountEq_eq_window_of_forall_eq
+    (n : OddNat) {k h : ℕ}
+    (hall : ∀ i, i < k → orbitWindowHeight n i = h) :
+    orbitWindowHeightCountEq n k h = k := by
+  unfold orbitWindowHeightCountEq orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      have hprefix : ∀ i, i < k → orbitWindowHeight n i = h := by
+        intro i hi
+        exact hall i (Nat.lt_trans hi (Nat.lt_succ_self k))
+      have hlast : orbitWindowHeight n k = h := hall k (Nat.lt_succ_self k)
+      simp [List.range_succ, ih hprefix, hlast]
+
+/--
+If every in-window height is at least `threshold`, then the threshold
+occupation count fills the whole window.
+-/
+theorem orbitWindowHeightCountGe_eq_window_of_forall_ge
+    (n : OddNat) {k threshold : ℕ}
+    (hall : ∀ i, i < k → threshold ≤ orbitWindowHeight n i) :
+    orbitWindowHeightCountGe n k threshold = k := by
+  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      have hprefix : ∀ i, i < k → threshold ≤ orbitWindowHeight n i := by
+        intro i hi
+        exact hall i (Nat.lt_trans hi (Nat.lt_succ_self k))
+      have hlast : threshold ≤ orbitWindowHeight n k := hall k (Nat.lt_succ_self k)
+      simp [List.range_succ, ih hprefix, hlast]
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d28d3b20..e072cbc2 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -103,9 +103,19 @@ orbitWindowHeightSeq_length
 orbitWindowHeightSeq_sum_eq_sumS
 orbitWindowHeightSeq_sum_ge_of_forall_ge
 orbitWindowHeightSeq_take_sum_eq_sumS
+orbitWindowHeightSeq_take_length
 orbitWindowHeightSeq_get?_eq_some
+orbitWindowHeightSeq_take_get?_eq_some
+orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
 orbitWindowHeight_eq_of_oddOrbitLabel_eq
 orbitWindowHeight_eq_of_collision
+orbitWindowHeight_eq_of_same_iterateT
+orbitWindowHeightCountEq
+orbitWindowHeightCountGe
+orbitWindowHeightCountEq_le_window
+orbitWindowHeightCountGe_le_window
+orbitWindowHeightCountEq_eq_window_of_forall_eq
+orbitWindowHeightCountGe_eq_window_of_forall_ge
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -227,6 +237,31 @@ local entries
   -> collision/fold height equality
 ```
 
+The bridge now also has the first occupation-count vocabulary:
+
+```text
+orbitWindowHeightCountEq n k h
+  = number of entries with height exactly h
+
+orbitWindowHeightCountGe n k threshold
+  = number of entries with height at least threshold
+```
+
+The current count API is intentionally minimal:
+
+```text
+exact-height count <= k
+threshold count <= k
+all heights equal h
+  -> exact-height count = k
+all heights >= threshold
+  -> threshold count = k
+```
+
+This is the first distribution layer.  It does not yet decompose `sumS` by
+height classes, but it gives future drift estimates a stable place to count
+how often each local height regime appears.
+
 The bridge theorem
 
 ```lean
@@ -248,6 +283,7 @@ orbit collision implies a specific fold/cycle condition
 ordered height profile controls accumulated Collatz drift
 height-threshold hypotheses give integer lower bounds for `sumS`
 label collisions preserve the next height observation
+height occupation counts measure exact and lower-bound regimes
 ```
 
 ## Next Candidate Work
@@ -257,9 +293,10 @@ The next safe steps are:
 ```text
 1. Connect the ordered height profile to a Petal address/residue reading.
 2. Add a window occupation/address transition layer.
-3. Use prefix sums and threshold bounds as the Collatz-side drift input.
-4. Test whether an external label transform can turn orbit labels into carrier labels.
-5. Only after that, test whether Collatz labels can feed ABC support/rad.
+3. Refine occupation counts into distribution estimates for `sumS`.
+4. Use prefix sums and threshold bounds as the Collatz-side drift input.
+5. Test whether an external label transform can turn orbit labels into carrier labels.
+6. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
 
 The main caution is that Collatz state labels are not prime labels.  Any bridge
````
`````
