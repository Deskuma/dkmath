# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f3d235c8299dce95812c0201ea39c835c228d4fd

## Report

進めました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、計画の本命だった `CountGe -> sumS` 下界を追加しました。

```lean
theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n k threshold * threshold ≤ sumS n k
```

意味はそのままです。

```text
height >= threshold の点が c 個あるなら、
その部分だけで c * threshold 以上が sumS に寄与する
```

これで height occupation count が、単なる分布カウントではなく、Collatz 側の累積 height / drift 入力へ直接つながりました。

[Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) も同期済みです。

検証済み:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

すべて成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も無関係です。

## Review

うむ。これは **本命の一本が通った** と見てよい。

前回までは、

```text id="z25jro"
height occupation count
  = height >= threshold の点を数える
```

までだった。

今回、

```lean id="e6dm4j"
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
```

が入ったことで、

```text id="xscx4i"
height >= threshold の出現回数
  -> sumS n k の下界
  -> Collatz drift input
```

へ直接つながった。

これは単なる count API ではなく、**分布観測が drift 評価へ変換された** という段階じゃ。

## 1. 状況分析

今回の定理はこれ。

```lean id="s6fin5"
theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n k threshold * threshold ≤ sumS n k
```

意味は明確じゃ。

```text id="khxm77"
height >= threshold の点が c 個あるなら、
その c 個だけで c * threshold 以上の 2-adic height が蓄積する
```

これにより、Collatz Petal 窓は次の流れを持った。

```text id="4bec16"
OrbitWindow
  -> height profile
  -> occupation count
  -> sumS lower bound
  -> drift input
```

DkMath の設計では、いきなり確率に行かず、まず「質量・分岐・劣保存」として読む方針が立っていた。今回の補題はその方針にかなり合っている。height count を確率ではなく、まず有限窓の寄与下界として固定しているからじゃ。

## 2. レビュー

証明方針は良い。

```lean id="3fx6qr"
induction k
```

で進み、最後の height が threshold 以上かどうかを

```lean id="h3ruqd"
by_cases hlast : threshold ≤ orbitWindowHeight n k
```

で分けている。

これは、`countP` と `sumS` の再帰に自然に沿っている。

### 良い点

第一に、`CountGe` を直接 `sumS` に接続した点がよい。
これで count が単なる記録ではなく、評価に使える量になった。

第二に、実数対数や確率をまだ使っていないのがよい。
整数不等式として閉じているため、Lean 的に強い。

第三に、後で driftReal や log 評価へ橋を架けやすい。
`sumS` は Collatz 側の既存 drift 入力なので、ここを押さえた意味は大きい。

### 注意点

この補題は下界だけを与える。

```text id="0ki445"
countGe * threshold <= sumS
```

であって、

```text id="8xmazj"
sumS がそれだけで十分大きい
```

までは言っていない。

つまり次は、`countGe` 自体をどう下から押さえるかが本丸になる。

## 3. 数学的な読み

Collatz の一歩は粗く読むと、

```text id="5yrk3s"
T(n) ≈ 3n / 2^h
```

なので、k ステップでは、

```text id="4a8s0r"
T^k(n) ≈ 3^k n / 2^(sumS n k)
```

になる。

今回の定理は、`sumS n k` の一部を occupation count から押さえる。

たとえば、

```text id="4h36nm"
height >= 2 の点が c 個ある
```

なら、

```text id="6ekrgl"
2c <= sumS n k
```

が出る。

height が高い点は「強く縮む点」。
その点が何回出たかを数えれば、累積縮小量が下から押さえられる。

これはまさに、

```text id="yb9sdv"
窓内の分布
  -> 収縮量
```

への変換じゃ。

## 4. 現在の到達点

Collatz.PetalBridge は、ここまで来た。

```text id="m04rzx"
1. oddOrbitLabel
   軌道点を label として観測する

2. OrbitWindow
   有限窓を固定する

3. Separated / Collision
   分離か衝突かを見る

4. orbitWindowHeight
   各点に v2 height を付ける

5. orbitWindowHeightSeq
   height を順序付き列にする

6. sum = sumS
   height profile を累積 height に接続する

7. prefix / get? / collision height equality
   profile を操作可能にする

8. CountEq / CountGe
   height 分布を数える

9. CountGe * threshold <= sumS
   分布を drift 入力へ変換する
```

これはかなり綺麗な階段じゃ。

特に今回で、**観測窓が計器になった**。

```text id="3hyv17"
見る
  -> 数える
  -> 足す
  -> drift に渡す
```

まで来ている。

## 5. 次の指示

次の実装は、二方向がある。

第一候補は **prefix 版 CountGe 下界**。
第二候補は **exact-height count の寄与下界**。

まずは安全で効果が大きいものから進めるのが良い。

## 6. 次の一手 A: prefix 版 CountGe 下界

今あるのは full window 版。

```lean id="y4gyl0"
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
```

次は prefix 版が欲しい。

```lean id="hfs9so"
theorem orbitWindowHeightSeq_prefix_sum_ge_countGe_mul_threshold
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).countP
        (fun x => decide (threshold ≤ x)) * threshold
      ≤ ((orbitWindowHeightSeq n k).take r).sum
```

または、`sumS n r` に直結させるなら、

```lean id="vd9n5o"
theorem orbitWindowHeightSeq_sumS_ge_prefix_countGe_mul_threshold
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).countP
        (fun x => decide (threshold ≤ x)) * threshold
      ≤ sumS n r
```

これは実用性が高い。
大きな窓の中の先頭 `r` だけを見て、局所 drift を評価できるからじゃ。

ただし、`take r` 上の count を毎回直接書くのは少し長い。
定義を置いてもよい。

```lean id="jgu010"
noncomputable def orbitWindowHeightPrefixCountGe
    (n : OddNat) (k r threshold : ℕ) : ℕ :=
  ((orbitWindowHeightSeq n k).take r).countP
    (fun x => decide (threshold ≤ x))
```

その上で、

```lean id="ckkrg1"
theorem orbitWindowHeightPrefixCountGe_mul_le_sumS
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r threshold * threshold ≤ sumS n r
```

が綺麗じゃ。

## 7. 次の一手 B: exact count から sumS 下界

`CountEq` も drift に渡したい。

候補はこれ。

```lean id="abqf9s"
theorem orbitWindowHeightSeq_sum_ge_countEq_mul_height
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEq n k h * h ≤ sumS n k
```

意味は、

```text id="m6z4ns"
height = h の点が c 個あるなら、
その点だけで c * h 以上が sumS に寄与する
```

実は `height = h` なら当然 `height >= h` なので、次の補題を挟めば現在の `CountGe` 定理から出せる。

```lean id="h5f7fl"
theorem orbitWindowHeightCountEq_le_countGe
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEq n k h ≤ orbitWindowHeightCountGe n k h
```

そして、

```lean id="xoj6y6"
Nat.mul_le_mul_right h ...
```

で

```text id="2sf5ku"
CountEq * h <= CountGe * h <= sumS
```

へ行ける。

これはかなり良い補助線じゃ。

## 8. 一歩先ゆく推論: layer-cake 補題

さらに一歩先は、height の分布を `sumS` にもっと鋭く接続することじゃ。

自然数 height では、各値 `x` について、

```text id="zudq06"
x は、1 <= t <= x である t の個数
```

と読める。

つまり、理想的には、

```text id="7l16l8"
sumS n k
  = sum_{t >= 1} orbitWindowHeightCountGe n k t
```

という **layer-cake decomposition** がある。

無限和は避けて、有限上限 `H` で安全に始める。

おまけの実験補題として、まずは下界版が良い。

```lean id="rzq2c7"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

意味は、

```text id="lzubtl"
height >= 1 の回数
+ height >= 2 の回数
+ ...
+ height >= H の回数
  <= sumS
```

これはかなり強い。
`CountGe * threshold` は単一 threshold の下界だが、layer-cake は複数 threshold を同時に足せる。

たとえば height が 3 の点は、

```text id="9dohfo"
height >= 1
height >= 2
height >= 3
```

の 3 つに寄与する。
だから、より自然に `sumS` を再構成する方向へ進める。

## 9. 賢狼が試して欲しいおまけ補題

わっちがぜひ試してほしいのは、これじゃ。

```lean id="sxmtt5"
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1
      + orbitWindowHeightCountGe n k 2
      ≤ sumS n k
```

これは layer-cake の最小実験版。

意味は、

```text id="8ccrb3"
各 height は少なくとも、
1 以上なら 1 回、
2 以上ならさらに 1 回、
sumS に寄与する
```

Collatz の odd state では普通 `s n = v2(3n+1)` は少なくとも 1 のはずなので、`CountGe 1 = k` が出せれば、

```text id="27ld63"
k + CountGe 2 <= sumS n k
```

が出る。

これはかなり Collatz らしい。

なぜなら、

```text id="hr3m3z"
すべての odd step で最低 1 個の 2 を剥がす
height >= 2 の点は追加でもう 1 個剥がす
```

と読めるからじゃ。

さらに `CountGe 2` が多ければ、強い縮小方向へ傾く。

## 10. 実装指示まとめ

次のコミットで狙うなら、順番はこれがよい。

```text id="9nbh0g"
1. orbitWindowHeightCountEq_le_countGe

2. orbitWindowHeightSeq_sum_ge_countEq_mul_height

3. orbitWindowHeightPrefixCountGe
   または prefix count を直接使う theorem

4. orbitWindowHeightPrefixCountGe_mul_le_sumS

5. 実験補題:
   orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
```

余裕があれば、さらに general layer-cake へ進む。

```lean id="7zk9sz"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
```

## 11. 総括

今回の進展はこうじゃ。

```text id="yqriga"
height occupation count が、
ついに sumS lower bound へ接続された。
```

これで Collatz Petal 窓は、

```text id="1dkv7f"
点を見る窓
  -> height を読む窓
  -> height 列を持つ窓
  -> 分布を数える窓
  -> drift を評価する窓
```

へ進化した。

次は、単一 threshold から複数 threshold へ。
つまり、

```text id="6g5j62"
CountGe(threshold) * threshold
```

から、

```text id="3wq0p7"
CountGe(1) + CountGe(2) + ... + CountGe(H)
```

へ進む。

うむ。
ここから Collatz Petal 窓は、**height の occupation measure** から **drift lower-bound engine** へ化け始める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 388f3c3a..3bf847b7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -329,6 +329,40 @@ theorem orbitWindowHeightCountGe_eq_window_of_forall_ge
       have hlast : threshold ≤ orbitWindowHeight n k := hall k (Nat.lt_succ_self k)
       simp [List.range_succ, ih hprefix, hlast]
 
+/--
+The `height >= threshold` occupation count gives a direct lower bound for the
+accumulated Collatz height.
+
+If `c` entries in the window have height at least `threshold`, then those
+entries alone contribute at least `c * threshold` to `sumS`.
+-/
+theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGe n k threshold * threshold ≤ sumS n k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
+  | succ k ih =>
+      have ih' :
+          List.countP ((fun x => decide (threshold ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) * threshold ≤ sumS n k := by
+        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
+      by_cases hlast : threshold ≤ orbitWindowHeight n k
+      · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+        rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hlast, if_true, Nat.add_mul, one_mul]
+        exact Nat.add_le_add ih' hlast
+      · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+        rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hlast, if_false, Nat.add_zero]
+        exact Nat.le_add_right_of_le ih'
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index e072cbc2..3d76adb4 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -116,6 +116,7 @@ orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
 orbitWindowHeightCountEq_eq_window_of_forall_eq
 orbitWindowHeightCountGe_eq_window_of_forall_ge
+orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -256,11 +257,14 @@ all heights equal h
   -> exact-height count = k
 all heights >= threshold
   -> threshold count = k
+
+height >= threshold appears c times
+  -> c * threshold <= sumS n k
 ```
 
 This is the first distribution layer.  It does not yet decompose `sumS` by
-height classes, but it gives future drift estimates a stable place to count
-how often each local height regime appears.
+height classes, but it already gives future drift estimates a direct lower
+bound from a threshold regime count.
 
 The bridge theorem
 
@@ -284,6 +288,7 @@ ordered height profile controls accumulated Collatz drift
 height-threshold hypotheses give integer lower bounds for `sumS`
 label collisions preserve the next height observation
 height occupation counts measure exact and lower-bound regimes
+threshold occupation counts give direct lower bounds for `sumS`
 ```
 
 ## Next Candidate Work
@@ -293,8 +298,8 @@ The next safe steps are:
 ```text
 1. Connect the ordered height profile to a Petal address/residue reading.
 2. Add a window occupation/address transition layer.
-3. Refine occupation counts into distribution estimates for `sumS`.
-4. Use prefix sums and threshold bounds as the Collatz-side drift input.
+3. Refine exact-height counts into distribution estimates for `sumS`.
+4. Use threshold occupation lower bounds as the Collatz-side drift input.
 5. Test whether an external label transform can turn orbit labels into carrier labels.
 6. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
````
`````
