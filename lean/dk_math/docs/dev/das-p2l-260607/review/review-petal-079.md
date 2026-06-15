# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 1478c18397065532256ce87dc2424a2b30d2e882

## Report

進めました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、`orbitWindowHeightSeq` を実際に使うための小補題群を追加しました。

```lean
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_take_sum_eq_sumS
orbitWindowHeightSeq_get?_eq_some
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
```

これで、Collatz Petal 窓は次を扱えます。

```text
各 height が threshold 以上
  -> k * threshold <= sumS n k

prefix の合計
  -> sumS n r

リスト index 読み
  -> orbitWindowHeight n i

label collision
  -> height も一致
```

[Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) も同期しました。

検証済み:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

すべて成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も無関係です。

## Review

うむ。これは **Collatz Petal 窓が、ただの観測列から「使える時系列 API」へ進んだ** という状況じゃ。
前回は、

```text id="kzx00e"
orbitWindowHeightSeq n k
  = 最初の k ステップの height 列

(orbitWindowHeightSeq n k).sum = sumS n k
```

までだった。今回の更新で、その height 列に対して **下界・prefix・index 読み・collision 連動** ができるようになった。

## 1. 今回の核心

追加された補題はこの 5 本。

```lean id="hial3h"
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_take_sum_eq_sumS
orbitWindowHeightSeq_get?_eq_some
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
```

意味をまとめると、こうじゃ。

```text id="eq8m2i"
各 height が threshold 以上
  -> k * threshold <= sumS n k

先頭 r 個の合計
  -> sumS n r

リストの i 番目
  -> orbitWindowHeight n i

同じ orbit label
  -> 同じ height

collision
  -> collision 点の height も一致
```

つまり、Petal 観測窓の height 列が、単なる表示用リストではなく、**計算・推論に使える profile** になった。

## 2. `sum_ge_of_forall_ge` の意味

```lean id="a0svtf"
orbitWindowHeightSeq_sum_ge_of_forall_ge
```

これは整数版の平均 height 下界じゃ。

```text id="v1qstb"
∀ i < k, threshold <= orbitWindowHeight n i
  -> k * threshold <= sumS n k
```

かなり素直だが重要。

Collatz の加速写像では、ざっくり

```text id="8krivv"
T^k(n) ≈ 3^k n / 2^(sumS n k)
```

なので、`sumS n k` は縮小側の累積量。
今回の補題は、

```text id="pbzczw"
各ステップで最低 threshold だけ 2 を剥がすなら、
k ステップ全体では最低 k * threshold だけ剥がす
```

を Lean で言えるようにした。

ただし、`threshold = 2` のような一様下界は Collatz 全体では強すぎる。今後は「高さ 1 が何回、2 以上が何回」のような分布型の補題が欲しくなる。

## 3. `take_sum_eq_sumS` の意味

```lean id="ufzbvp"
orbitWindowHeightSeq_take_sum_eq_sumS
```

これは prefix 観測の橋じゃ。

```text id="z876e4"
r <= k
  -> ((orbitWindowHeightSeq n k).take r).sum = sumS n r
```

これで、大きな窓 `k` を取っていても、その先頭 `r` だけを切り出して Collatz 側の `sumS n r` に戻せる。

これは今後かなり使うはず。

```text id="vrjxp7"
全体窓
  -> prefix
  -> partial drift
  -> 局所的な伸縮判定
```

Collatz では「ある区間だけ強く縮む」「途中まで膨らんでから縮む」のような局所情報が大事なので、prefix 補題は良い。

## 4. `get?` 補題の意味

```lean id="h3os1y"
orbitWindowHeightSeq_get?_eq_some
```

これは list profile と時刻 index の往復。

```text id="0g8sat"
i < k
  -> (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i)
```

これで、

```text id="5thb2b"
リスト上の i 番目の height
```

と、

```text id="lhxd6d"
軌道上の時刻 i の height
```

がつながる。

これは小さいが、後で統計・検索・条件分岐を書くときに効く。
たとえば「heightSeq の中に 1 がある」「i 番目だけ高い」などの補題に進みやすい。

## 5. collision と height の接続

```lean id="yh8wea"
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
```

これは非常に Collatz らしい。

意味は、

```text id="f0mvre"
同じ odd state に戻ったなら、
次に読む v2 height も同じ
```

じゃ。

つまり collision は、点だけでなく **次の局所挙動** も一致させる。

```text id="lhzo0g"
oddOrbitLabel i = oddOrbitLabel j
  -> orbitWindowHeight i = orbitWindowHeight j
```

これは fold / cycle を見る上でかなり重要。

周期候補では、状態が戻ればその後の height pattern も繰り返す。
今回の補題はその最初の一歩を固定している。

## 6. 現在の構造

ここまでで、Collatz.PetalBridge はこういう段階になった。

```text id="h2rn5g"
OrbitWindow:
  有限観測窓

oddOrbitLabel:
  窓内の点

Separated / Collision:
  点列の分離・衝突

orbitWindowHeight:
  各点の 2-adic height

orbitWindowHeightSeq:
  height の順序付き profile

sum = sumS:
  profile と累積 height の接続

prefix / get? / lower bound:
  profile を実際に使う API

collision -> same height:
  fold/cycle 診断の入口
```

かなりきれいな観測装置になってきた。

## 7. Petal 的な意味

Petal 語彙では、今回の更新はこう読める。

```text id="wn6jxx"
窓内の一点:
  oddOrbitLabel n i

その点の高さ:
  orbitWindowHeight n i

窓内の軌跡:
  orbitWindowHeightSeq n k

軌跡の累積縮小量:
  sumS n k

衝突:
  同じ点に戻り、同じ高さを持つ
```

つまり、Collatz 軌道の肥大化・縮小化が、

```text id="jxruc4"
時系列 height profile
```

として見えるようになった。

これは「巨大な値を直接見る」のではなく、

```text id="qdg4ks"
窓内の address-like height の動き
```

を見るということじゃ。

## 8. 次に欲しいもの

次は分布補題が欲しくなる。

一様に `height >= threshold` は強いので、より現実的には、

```text id="h32pku"
height = 1 が何回あるか
height >= 2 が何回あるか
height >= 3 が何回あるか
```

を数える方向がよい。

たとえば、

```lean id="q8vj7o"
def orbitWindowHeightCount (n : OddNat) (k h : ℕ) : ℕ :=
  ((orbitWindowHeightSeq n k).filter fun x => x = h).length
```

あるいは Finset 側なら、

```text id="vzyrpu"
#{ i < k | orbitWindowHeight n i = h }
```

この count ができると、

```text id="i6pf1b"
sumS n k
  = 1 * count(height=1)
  + 2 * count(height=2)
  + ...
```

のような分布評価へ進める。

Collatz の drift には、単純な全点下界より、こちらの方が効くはずじゃ。

## 9. 次の安全な theorem 候補

直近で自然なのはこのあたり。

```lean id="7ojxnd"
orbitWindowHeight_eq_of_same_iterateT
```

```text id="8z2mtg"
iterateT i n = iterateT j n
  -> orbitWindowHeight n i = orbitWindowHeight n j
```

今は label equality から height equality なので、state equality 版もあると便利。

次に、

```lean id="9ojpr4"
orbitWindowHeightSeq_take_length
orbitWindowHeightSeq_take_get?
orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
```

さらに drift 入口として、

```lean id="96ov5d"
k * threshold <= sumS n k
  -> drift lower/upper bound
```

へ進める。

## 10. 総括

今回の進展はこうじゃ。

```text id="slh2sc"
Collatz Petal 窓の height profile が、
実際に推論できる時系列データになった。
```

前回は、

```text id="tj5lmt"
profile の合計は sumS
```

まで。

今回は、

```text id="e47wkm"
profile の各点
prefix
下界
collision との関係
```

まで入った。

これで Petal 窓は、

```text id="abk1ha"
局所 height を読む
累積 height を読む
prefix drift を読む
衝突時の height 一致を読む
```

計器になった。

うむ。
これはもう、Collatz の **単位核剥離量の時系列観測装置** と呼んでよい段階じゃ。次は height の分布・occupation measure に進むと、統計確率論の窓がさらに開く。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 97258d2c..fd387596 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -154,6 +154,72 @@ theorem orbitWindowHeightSeq_sum_eq_sumS (n : OddNat) (k : ℕ) :
       simp [orbitWindowHeightSeq, List.range_succ, sumS,
         orbitWindowHeight_eq_s_iterateT, ih']
 
+/--
+If every height in the window is at least `threshold`, then the accumulated
+Collatz height is at least `k * threshold`.
+
+This is the integer threshold form of an average-height lower bound.  It avoids
+real logarithms and keeps the bridge on the combinatorial side.
+-/
+theorem orbitWindowHeightSeq_sum_ge_of_forall_ge
+    (n : OddNat) {k threshold : ℕ}
+    (h : ∀ i, i < k → threshold ≤ orbitWindowHeight n i) :
+    k * threshold ≤ sumS n k := by
+  induction k with
+  | zero =>
+      simp [sumS]
+  | succ k ih =>
+      have hprefix : ∀ i, i < k → threshold ≤ orbitWindowHeight n i := by
+        intro i hi
+        exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
+      have hlast : threshold ≤ orbitWindowHeight n k := h k (Nat.lt_succ_self k)
+      have ih' : k * threshold ≤ sumS n k := ih hprefix
+      rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+      rw [Nat.succ_mul]
+      exact Nat.add_le_add ih' hlast
+
+/--
+The prefix of the ordered height profile has sum `sumS n r`, as long as the
+prefix length `r` lies inside the ambient window `k`.
+-/
+theorem orbitWindowHeightSeq_take_sum_eq_sumS
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    ((orbitWindowHeightSeq n k).take r).sum = sumS n r := by
+  rw [← orbitWindowHeightSeq_sum_eq_sumS n r]
+  simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]
+
+/--
+Reading the ordered height profile at an in-window time recovers the pointwise
+height observation.
+-/
+theorem orbitWindowHeightSeq_get?_eq_some
+    (n : OddNat) {i k : ℕ} (hi : i < k) :
+    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) := by
+  simp [orbitWindowHeightSeq, hi]
+
+/--
+Equal Collatz orbit labels have equal height observations.
+-/
+theorem orbitWindowHeight_eq_of_oddOrbitLabel_eq
+    {n : OddNat} {i j : ℕ}
+    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
+    orbitWindowHeight n i = orbitWindowHeight n j := by
+  simp [orbitWindowHeight, hlabel]
+
+/--
+A label collision forces equality of the height observations at the colliding
+times.
+
+If the orbit has returned to the same odd state, then the next `v2` height read
+from that state is also the same.
+-/
+theorem orbitWindowHeight_eq_of_collision
+    {n : OddNat} {k i j : ℕ}
+    (_hi : i < k) (_hj : j < k)
+    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
+    orbitWindowHeight n i = orbitWindowHeight n j :=
+  orbitWindowHeight_eq_of_oddOrbitLabel_eq hlabel
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 6a23086d..d28d3b20 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -101,6 +101,11 @@ rawHeightLabel_eq_s
 orbitWindowHeight_eq_s_iterateT
 orbitWindowHeightSeq_length
 orbitWindowHeightSeq_sum_eq_sumS
+orbitWindowHeightSeq_sum_ge_of_forall_ge
+orbitWindowHeightSeq_take_sum_eq_sumS
+orbitWindowHeightSeq_get?_eq_some
+orbitWindowHeight_eq_of_oddOrbitLabel_eq
+orbitWindowHeight_eq_of_collision
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -197,6 +202,31 @@ accumulated drift input:
 The profile form is useful for address/window diagnostics, while `sumS` is the
 existing Collatz side used by drift and growth estimates.
 
+The next small API layer records how to use the profile:
+
+```text
+all heights >= threshold
+  -> k * threshold <= sumS n k
+
+take r from a k-window, with r <= k
+  -> prefix sum = sumS n r
+
+read index i in a k-window, with i < k
+  -> the list entry is orbitWindowHeight n i
+
+same orbit label at i and j
+  -> same height at i and j
+```
+
+This gives the window a usable sequence interface:
+
+```text
+local entries
+  -> prefix sums
+  -> threshold lower bounds
+  -> collision/fold height equality
+```
+
 The bridge theorem
 
 ```lean
@@ -216,6 +246,8 @@ orbit labels are mapped to prime labels
 orbit collision implies a specific fold/cycle condition
 2-adic height controls Petal address movement
 ordered height profile controls accumulated Collatz drift
+height-threshold hypotheses give integer lower bounds for `sumS`
+label collisions preserve the next height observation
 ```
 
 ## Next Candidate Work
@@ -225,7 +257,7 @@ The next safe steps are:
 ```text
 1. Connect the ordered height profile to a Petal address/residue reading.
 2. Add a window occupation/address transition layer.
-3. Use `sumS`/height-profile bounds as the Collatz-side drift input.
+3. Use prefix sums and threshold bounds as the Collatz-side drift input.
 4. Test whether an external label transform can turn orbit labels into carrier labels.
 5. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
````
`````
