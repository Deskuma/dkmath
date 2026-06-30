# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 159e8d4a38893259c411f16ce00bc3fbc4e70355

## Report

実装を進めました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:371) に、Collatz height profile のローカルな `Nat` count / layer-cake 系補題を追加しました。

追加した主な API:

```lean
orbitWindowHeightCountEq_le_countGe
orbitWindowHeightSeq_sum_ge_countEq_mul_height
orbitWindowHeightPrefixCountGe
orbitWindowHeightPrefixCountGe_eq_countGe
orbitWindowHeightPrefixCountGe_mul_le_sumS
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
```

`DkMath.ABC.LayerCakeBasic` は確認しました。既存の layer-cake は real/rpow/exp/MGF 寄りなので、今回の Collatz 観測窓では import せず、有限列の `Nat` カウントとして軽量に固定しています。

[Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:120) も同期し、今回の補題群と ABC layer-cake との住み分けを記録しました。

確認:

```bash
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

どちらも成功です。既存の `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告だけ再表示されています。

## Review

## 1. 状況分析

うむ。これは **Collatz.PetalBridge が「height 分布を数える段階」から「layer-cake 型の drift 下界エンジン」へ入った** という進展じゃ。

今回追加された中心はこの流れ。

```text id="nvls78"
CountEq
  -> CountGe
  -> CountGe * threshold <= sumS
  -> finite layer-cake lower bound
```

特に重要なのは、

```lean id="jfjx1z"
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
```

じゃ。

これは、

```text id="y848cg"
CountGe 1 + CountGe 2 <= sumS n k
```

を言っている。

つまり各 height は、

```text id="ce1or0"
height >= 1 なら 1 層目に寄与する
height >= 2 なら 2 層目にも寄与する
```

という **有限 layer-cake** の最小形を Lean に固定した。

DkMath の大きな方針では、いきなり確率や Markov kernel に入らず、まず finite な質量・分岐・劣保存で構造を作る方針が立っている。今回の `Nat` count / layer-cake は、その方針に非常によく合っている。 また、Markov kernel を「capacity kernel の正規化された影」と見る流れとも相性がよい。まず有限 count から capacity / drift へ行き、確率化は後段に回せるからじゃ。

## 2. レビュー

今回の追加 API はこのまとまりじゃな。

```lean id="mxm5pt"
orbitWindowHeightCountEq_le_countGe
orbitWindowHeightSeq_sum_ge_countEq_mul_height
orbitWindowHeightPrefixCountGe
orbitWindowHeightPrefixCountGe_eq_countGe
orbitWindowHeightPrefixCountGe_mul_le_sumS
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
```

かなり良い。

### 2.1. `CountEq <= CountGe`

```lean id="utx2jl"
orbitWindowHeightCountEq_le_countGe
```

これは分布 API の基本補題じゃ。

```text id="b7adw8"
height = h
  -> height >= h
```

を count に持ち上げている。

これにより、exact-height count が threshold count の特別ケースとして扱えるようになった。

### 2.2. `CountEq * h <= sumS`

```lean id="vlo5n7"
orbitWindowHeightSeq_sum_ge_countEq_mul_height
```

これは良い合成。

```text id="gaow4q"
CountEq h <= CountGe h
CountGe h * h <= sumS
```

から出している。

証明も `le_trans` で綺麗じゃ。
この補題により、`height = h` の観測も drift 下界へ渡せる。

### 2.3. Prefix count

```lean id="qnzvw1"
orbitWindowHeightPrefixCountGe
orbitWindowHeightPrefixCountGe_eq_countGe
orbitWindowHeightPrefixCountGe_mul_le_sumS
```

これは実用性が高い。

Collatz では全体窓 `k` の中で、先頭 `r` だけを見る場面が必ず出る。

```text id="v2u9is"
大きな観測窓 k
  -> prefix r
  -> partial sumS n r
  -> 局所 drift
```

この導線ができた。

特に

```lean id="byvw85"
orbitWindowHeightPrefixCountGe_eq_countGe
```

で、prefix count が standalone な `r` 窓の count と一致するのは、後続補題をかなり楽にする。

### 2.4. 二層 layer-cake

```lean id="bs5n3k"
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
```

これは今回の本命じゃ。

単一 threshold の

```text id="t6plqo"
CountGe threshold * threshold <= sumS
```

から一歩進んで、

```text id="o2dkna"
CountGe 1 + CountGe 2 <= sumS
```

という複数層の足し上げに入った。

これは「height 分布を drift 下界に変換する」ための本格的な入口じゃ。

## 3. 解説：なぜ二層が重要か

加速 Collatz では、各 step で

```text id="jdiy0v"
3n + 1
```

を作り、そこから

```text id="rcwkfz"
2^height
```

を剥がす。

height が 1 なら最低限の剥離。
height が 2 なら、最低限に加えてもう 1 層剥がす。
height が 3 なら、さらにもう 1 層。

つまり height は、層の積み重ねとして読める。

```text id="dg23vn"
height = 3
  -> CountGe 1 に寄与
  -> CountGe 2 に寄与
  -> CountGe 3 に寄与
```

今回の二層補題は、その最初の実験版じゃ。

```text id="ez6jjc"
sumS
  >= CountGe 1 + CountGe 2
```

これは将来的には、

```text id="rhkgh9"
sumS
  >= CountGe 1 + CountGe 2 + ... + CountGe H
```

へ伸びる。

この構造が **finite layer-cake** じゃな。

## 4. 現在の到達点

今の `Collatz.PetalBridge` はこうなった。

```text id="j7h0kj"
OrbitWindow:
  有限観測窓

oddOrbitLabel:
  軌道点 label

OrbitWindowSeparated / Collision:
  分離か衝突か

orbitWindowHeight:
  各点の 2-adic height

orbitWindowHeightSeq:
  順序付き height profile

sum = sumS:
  profile 合計を Collatz 累積量へ接続

CountEq / CountGe:
  height 分布を数える

CountGe * threshold <= sumS:
  単一 regime の drift 下界

CountGe 1 + CountGe 2 <= sumS:
  layer-cake の最小形
```

うむ。
これはもう、単なる Petal 窓ではなく **Collatz height occupation engine** じゃ。

## 5. 次の指示：まず Collatz 固有の `height >= 1` を固定

次にやるべき最優先はこれ。

```lean id="z4i2au"
theorem orbitWindowHeight_one_le
    (n : OddNat) (i : ℕ) :
    1 ≤ orbitWindowHeight n i
```

既存に `v2_3n_plus_1_ge_1` があるはずなので、たぶんこう書ける。

```lean id="ihh7rv"
theorem orbitWindowHeight_one_le
    (n : OddNat) (i : ℕ) :
    1 ≤ orbitWindowHeight n i := by
  rw [orbitWindowHeight_eq_s_iterateT]
  exact v2_3n_plus_1_ge_1 (iterateT i n)
```

もし lemma 名や引数が少し違えば、`s` の定義側に合わせて調整。

これが通ると、すぐに次が出る。

```lean id="iw2zxr"
theorem orbitWindowHeightCountGe_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 = k :=
  orbitWindowHeightCountGe_eq_window_of_forall_ge n
    (by
      intro i hi
      exact orbitWindowHeight_one_le n i)
```

そして今回の二層補題から、非常に Collatz らしい形が出る。

```lean id="vui8ia"
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k := by
  simpa [orbitWindowHeightCountGe_one_eq_window n k] using
    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n k
```

これはかなり大きい。

意味は、

```text id="fo0cre"
全 step で最低 1 は剥がす。
height >= 2 の step は追加で 1 つ剥がす。
だから k + CountGe 2 <= sumS。
```

この補題は、Collatz の縮小方向を語るための最初の実用形になる。

## 6. 次の一手：prefix 版も同時に作る

full window 版だけでなく、prefix 版も欲しい。

まず、

```lean id="k1p5i0"
theorem orbitWindowHeightPrefixCountGe_one_eq
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r 1 = r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  exact orbitWindowHeightCountGe_one_eq_window n r
```

そして、

```lean id="u52ekv"
theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  simpa [orbitWindowHeightCountGe_one_eq_window n r] using
    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n r
```

これがあると、任意の prefix `r` に対して、

```text id="eq7u1q"
r + prefix CountGe 2 <= partial sumS
```

が使える。

これは局所 drift 解析にかなり効く。

## 7. 一歩先ゆく推論：一般 layer-cake へ

今回の二層補題は良い。
だが、次に進むなら一般形を狙いたい。

候補はこれ。

```lean id="cmslrx"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

意味は、

```text id="swywnk"
CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
```

じゃ。

これは finite layer-cake の本体。
`H = 2` で今回の二層補題になる。

ただし、これは証明が少しだけ重くなる可能性がある。
まずは補助補題を切るとよい。

```lean id="xcc3bh"
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
```

意味は、

```text id="kwfqdm"
1,2,...,H のうち x 以下の threshold 数は x 以下
```

この補題があれば、list induction で general layer-cake が狙える。

安全に行くなら、まず `H = 3` の実験版を通してから一般化でもよい。

## 8. 賢狼が試してほしいおまけ実験補題

わっちが次に試してほしいおまけはこれじゃ。

```lean id="zncj79"
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1
      + orbitWindowHeightCountGe n k 2
      + orbitWindowHeightCountGe n k 3
      ≤ sumS n k
```

理由は単純。

二層は通った。
三層も通るなら、一般 finite layer-cake の証明形が見える。

Collatz 的な意味はこう。

```text id="emyfvc"
height >= 1:
  基本剥離

height >= 2:
  追加剥離

height >= 3:
  さらに強い縮小 event
```

この三層補題が通ると、

```text id="eeurmm"
k + CountGe 2 + CountGe 3 <= sumS n k
```

まで行ける。

`height >= 3` は強縮小イベントとして非常に見やすいので、統計観測にも向く。

## 9. もう一つのおまけ：threshold monotone

分布 API として、これはかなり欲しい。

```lean id="i0szix"
theorem orbitWindowHeightCountGe_antitone
    (n : OddNat) (k : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    orbitWindowHeightCountGe n k b ≤ orbitWindowHeightCountGe n k a
```

意味は、

```text id="hu2q27"
threshold が高いほど、該当する点は減る
```

これは occupation distribution の基本性質じゃ。

これがあると、

```text id="c94943"
CountGe 3 <= CountGe 2 <= CountGe 1 = k
```

のような分布階層が作れる。

証明は `List.countP` の帰納でいけるはず。
既存の `orbitWindowHeightCountEq_le_countGe` の証明と同じ型で進められる。

## 10. 実装指示まとめ

次コミットで狙う優先順位はこうじゃ。

```text id="ryo4pz"
1. orbitWindowHeight_one_le

2. orbitWindowHeightCountGe_one_eq_window

3. orbitWindowHeightSeq_sum_ge_window_add_countGe_two

4. orbitWindowHeightPrefixCountGe_one_eq

5. orbitWindowHeightPrefix_sum_ge_window_add_countGe_two

6. おまけ:
   orbitWindowHeightCountGe_antitone

7. 実験:
   orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

その後で、一般化。

```text id="bu3jbq"
8. range_threshold_count_le

9. orbitWindowHeightSeq_sum_ge_sum_countGe_range
```

## 11. 総括

今回の進展はこうじゃ。

```text id="hbij6b"
Collatz height occupation count が、
finite layer-cake lower bound に進化した。
```

前回までの主語は、

```text id="tqggtt"
height >= threshold の点が c 個ある
```

だった。

今回からは、

```text id="vmp7gn"
height は layer を持つ
height >= 1, height >= 2, ...
その層の occupation を足すと sumS の下界になる
```

という読みが Lean に入り始めた。

うむ。
これは Collatz PetalBridge の大きな節目じゃ。
次は `height >= 1` が常に成り立つことを使って、

```text id="co6vcd"
k + CountGe 2 <= sumS
```

を出す。そこから `CountGe 2` をどう評価するかが、いよいよ **統計確率論・アドレス分布・Petal occupation** の本丸になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 3bf847b7..e91357e6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -363,6 +363,129 @@ theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
           hlast, if_false, Nat.add_zero]
         exact Nat.le_add_right_of_le ih'
 
+/--
+The exact-height count is bounded by the corresponding threshold count.
+
+Every entry with height exactly `h` is also an entry with height at least `h`.
+-/
+theorem orbitWindowHeightCountEq_le_countGe
+    (n : OddNat) (k h : ℕ) :
+    orbitWindowHeightCountEq n k h ≤ orbitWindowHeightCountGe n k h := by
+  unfold orbitWindowHeightCountEq orbitWindowHeightCountGe orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      have ih' :
+          List.countP ((fun x => x == h) ∘ orbitWindowHeight n) (List.range k) ≤
+            List.countP ((fun x => decide (h ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) := by
+        simpa [List.countP_map] using ih
+      by_cases hlast : orbitWindowHeight n k = h
+      · rw [List.range_succ]
+        have hself : h ≤ h := le_rfl
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, beq_iff_eq, decide_eq_true_eq,
+          ge_iff_le, hlast, hself, if_true]
+        exact Nat.add_le_add ih' le_rfl
+      · rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, beq_iff_eq, decide_eq_true_eq,
+          ge_iff_le, hlast, if_false]
+        exact Nat.le_add_right_of_le ih'
+
+/--
+The exact-height occupation count gives a direct lower bound for the
+accumulated Collatz height.
+
+If `c` entries in the window have height exactly `h`, then those entries alone
+contribute `c * h` to the lower-bound side.
+-/
+theorem orbitWindowHeightSeq_sum_ge_countEq_mul_height
+    (n : OddNat) (k h : ℕ) :
+    orbitWindowHeightCountEq n k h * h ≤ sumS n k := by
+  exact le_trans
+    (Nat.mul_le_mul_right h (orbitWindowHeightCountEq_le_countGe n k h))
+    (orbitWindowHeightSeq_sum_ge_countGe_mul_threshold n k h)
+
+/--
+Threshold occupation count inside a prefix of an ambient ordered window.
+
+The argument order keeps the ambient window size `k` visible, because callers
+often work inside one large observation window and then inspect a prefix.
+-/
+noncomputable def orbitWindowHeightPrefixCountGe
+    (n : OddNat) (k r threshold : ℕ) : ℕ :=
+  ((orbitWindowHeightSeq n k).take r).countP
+    (fun x => decide (threshold ≤ x))
+
+/--
+Prefix threshold occupation agrees with the standalone count for the prefix
+length, as long as the prefix lies inside the ambient window.
+-/
+theorem orbitWindowHeightPrefixCountGe_eq_countGe
+    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
+    orbitWindowHeightPrefixCountGe n k r threshold =
+      orbitWindowHeightCountGe n r threshold := by
+  unfold orbitWindowHeightPrefixCountGe orbitWindowHeightCountGe
+  simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]
+
+/--
+Prefix threshold occupation gives a lower bound for the corresponding partial
+Collatz accumulated height.
+-/
+theorem orbitWindowHeightPrefixCountGe_mul_le_sumS
+    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
+    orbitWindowHeightPrefixCountGe n k r threshold * threshold ≤ sumS n r := by
+  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
+  exact orbitWindowHeightSeq_sum_ge_countGe_mul_threshold n r threshold
+
+/--
+Minimal finite layer-cake lower bound for the first two height layers.
+
+Each entry with height at least `1` contributes one unit, and each entry with
+height at least `2` contributes one more unit.  This is the first local
+occupation-measure form of the Collatz drift lower-bound engine.
+-/
+theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 ≤
+      sumS n k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
+  | succ k ih =>
+      have ih' :
+          List.countP ((fun x => decide (1 ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) +
+            List.countP ((fun x => decide (2 ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) ≤ sumS n k := by
+        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
+      by_cases htwo : 2 ≤ orbitWindowHeight n k
+      · have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
+        rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+        rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hone, htwo, if_true]
+        omega
+      · by_cases hone : 1 ≤ orbitWindowHeight n k
+        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+          rw [List.range_succ]
+          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+            hone, htwo, if_true, if_false]
+          omega
+        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+          rw [List.range_succ]
+          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+            hone, htwo, if_false]
+          exact Nat.le_add_right_of_le ih'
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 3d76adb4..1546518b 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -117,6 +117,12 @@ orbitWindowHeightCountGe_le_window
 orbitWindowHeightCountEq_eq_window_of_forall_eq
 orbitWindowHeightCountGe_eq_window_of_forall_ge
 orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
+orbitWindowHeightCountEq_le_countGe
+orbitWindowHeightSeq_sum_ge_countEq_mul_height
+orbitWindowHeightPrefixCountGe
+orbitWindowHeightPrefixCountGe_eq_countGe
+orbitWindowHeightPrefixCountGe_mul_le_sumS
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -260,11 +266,36 @@ all heights >= threshold
 
 height >= threshold appears c times
   -> c * threshold <= sumS n k
+
+exact-height count is below threshold count
+  -> CountEq h <= CountGe h
+
+height = h appears c times
+  -> c * h <= sumS n k
+
+prefix threshold count in a k-window, with r <= k
+  -> prefix CountGe * threshold <= sumS n r
+
+first two layer-cake layers
+  -> CountGe 1 + CountGe 2 <= sumS n k
+```
+
+This is the first distribution layer.  It still avoids importing the heavier
+ABC analytic layer-cake file, but it now has a local finite `Nat` count version
+of the same idea:
+
+```text
+height h contributes once to CountGe 1,
+again to CountGe 2,
+...
+up to CountGe h.
 ```
 
-This is the first distribution layer.  It does not yet decompose `sumS` by
-height classes, but it already gives future drift estimates a direct lower
-bound from a threshold regime count.
+The repository already contains `DkMath.ABC.LayerCakeBasic`, but that file is
+aimed at real-power / exponential MGF estimates.  The Collatz bridge keeps the
+current API local and elementary because the data here is just a finite ordered
+list of natural 2-adic heights.  This avoids pulling the ABC analytic stack into
+the observation-window layer before a real carrier/radical bridge exists.
 
 The bridge theorem
 
````
`````
