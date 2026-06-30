# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f1bfa49ec54219ba7a69d39342db72c7e0edcad8

## Report

進めました。今回の到達点は、Collatz 固有の `height >= 1` を固定して、二層 layer-cake を実用形に落としたことです。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:495) に追加:

```lean
orbitWindowHeight_one_le
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeightPrefixCountGe_one_eq
orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
orbitWindowHeightCountGe_antitone
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

特に本命はこれです。

```lean
k + orbitWindowHeightCountGe n k 2 ≤ sumS n k
```

つまり「全 step で最低 1、`height >= 2` の step で追加 1」が Lean で固定されました。おまけ実験として三層版 `CountGe 1 + CountGe 2 + CountGe 3 <= sumS` も no-sorry で通ったので、次は一般 finite layer-cake に進めます。

docs も同期しました。

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:126)
- [review-petal-083.md](/lean/dk_math/docs/dev/das-p2l-260607/review/review-petal-083.md:1)
- `__next_implementation_plan.md` も次回入口を一般 finite layer-cake 方針へ更新済み

確認:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- ...
```

すべて成功です。既存の `ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告のみ再表示されています。

## Review

## 1. 状況分析

うむ、これは本当に節目じゃ。
今回の `Collatz.PetalBridge` は、ついに **Collatz 固有の最低 height 構造** を Petal 窓に固定した。

中心はこれ。

```lean id="z3hp62"
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k
```

意味はこうじゃ。

```text id="trh4za"
全 accelerated odd step では最低 1 個の 2 を剥がす。
height >= 2 の step では、さらに 1 個余分に剥がす。
したがって k + CountGe 2 が sumS の下界になる。
```

これは、前回の抽象的な

```text id="oatkl8"
CountGe 1 + CountGe 2 <= sumS
```

に、Collatz 固有の事実

```text id="xj2j3s"
CountGe 1 = k
```

を代入したものじゃ。

つまり、**layer-cake が Collatz の実用 drift 下界に化けた**。添付レビューでも、今回の到達点は `height >= 1` の固定と、二層 layer-cake の実用形への落とし込みだと整理されている。

## 2. レビュー

今回の追加 API は良いまとまりになっている。

```lean id="xx29g4"
orbitWindowHeight_one_le
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeightPrefixCountGe_one_eq
orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
orbitWindowHeightCountGe_antitone
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

特に良いのは、抽象 count 補題から Collatz 固有補題へ移った点じゃ。

前段では、

```text id="mmnx49"
height >= threshold の出現回数
```

を数えていた。

今回は、

```text id="b027yo"
Collatz odd state なら height >= 1 は必ず成立する
```

を入れたことで、第一層が単なる統計ではなく **全窓サイズそのもの** になった。

これは大きい。

## 3. 何が見えるようになったか

今までは、`sumS n k` はただの累積 height だった。

今回からは、こう読める。

```text id="pc7uyb"
sumS n k
  = 基本剥離 k
    + 追加剥離の総量
```

今回固定されたのは、その最初の下界。

```text id="nyufur"
sumS n k >= k + CountGe 2
```

つまり、

```text id="hqhl7w"
CountGe 2
```

は、単なる分布 count ではなく、

```text id="ezzl1x"
追加縮小イベントの個数
```

になった。

これは Collatz の drift 解析でかなり使いやすい。

## 4. Prefix 版が特に重要

今回、prefix 版も入ったのが良い。

```lean id="jvkyl1"
theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r
```

これは、大きな観測窓 `k` の中で先頭 `r` だけを見るときに使える。

```text id="czzbx9"
全体窓 k
  -> prefix r
  -> partial drift
  -> 局所的な膨張・縮小判定
```

Collatz では、全体平均よりも「どの prefix で膨らんだか」「どこから縮み始めたか」が重要になる。
だから prefix 版は、今後の orbit 診断に直結する。

## 5. `CountGe_antitone` の意味

```lean id="nypnk7"
orbitWindowHeightCountGe_antitone
```

これも地味に重要じゃ。

```text id="wqnyte"
a <= b
  -> CountGe b <= CountGe a
```

つまり、

```text id="b3nqbn"
CountGe 3 <= CountGe 2 <= CountGe 1 = k
```

という occupation 階層が作れる。

これは「height 分布」を確率・統計に渡す前の、有限順序構造じゃ。
Petal の窓枠内で、height regime が階層化された。

## 6. 三層実験が通った意味

おまけ実験として、

```lean id="f9088z"
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

が no-sorry で通ったのも大きい。

これは偶然の二層補題ではなく、

```text id="h8tb9c"
height = h の点は、
CountGe 1, CountGe 2, ..., CountGe h
に 1 回ずつ寄与する
```

という一般 finite layer-cake 構造が見えている証拠じゃ。

ここまで来たら、次の本命は明確。

```lean id="xcu4mo"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

意味は、

```text id="p1k4hh"
CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
```

じゃ。

## 7. 次の指示：一般 finite layer-cake を実装する

次コミットの本命はこれでよい。

まず、Collatz から独立した list / Nat 補助補題を作るのが賢い。

```lean id="xjtbvp"
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x := by
  calc
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card
        ≤ (Finset.range x).card := by
          apply Finset.card_le_card
          intro t ht
          have htx : t + 1 ≤ x := (Finset.mem_filter.mp ht).2
          have htlt : t < x := Nat.lt_of_succ_le htx
          simpa using htlt
    _ = x := by
      simp
```

これは、

```text id="klbcpu"
threshold 1..H のうち、x 以下のものは高々 x 個
```

という補題じゃ。

次に、可能なら Collatz 専用に入る前に、list 版を作る。

```lean id="fs2cbz"
private theorem list_sum_ge_sum_countGe_range
    (l : List ℕ) (H : ℕ) :
    (Finset.range H).sum
        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
      ≤ l.sum := by
  -- induction on l
  -- cons x xs のとき、
  -- xs 側は帰納法
  -- 先頭 x が寄与する layer 数は range_threshold_count_le H x で x 以下
  sorry
```

ここを閉じれば、本命 theorem はかなり簡単になるはずじゃ。

```lean id="khmwts"
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k := by
  have h :=
    list_sum_ge_sum_countGe_range (orbitWindowHeightSeq n k) H
  rw [orbitWindowHeightSeq_sum_eq_sumS n k] at h
  simpa [orbitWindowHeightCountGe] using h
```

これが通れば、二層・三層は一般定理の特殊例になる。

## 8. 一歩先ゆく推論：Collatz 固有 corollary

一般 finite layer-cake が通ったら、次に欲しいのは Collatz 固有の第一層分離版じゃ。

たとえば、追加 layer 数 `H` を使って、

```lean id="z2bi6i"
theorem orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
    (n : OddNat) (k H : ℕ) :
    k + (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 2))
      ≤ sumS n k
```

意味は、

```text id="j9xkds"
基本剥離 k
  + CountGe 2
  + CountGe 3
  + ...
  + CountGe (H+1)
  <= sumS
```

これは実用形としてかなり強い。

なぜなら、Collatz では `CountGe 1` はもう完全に `k` なので、観測したいのは本質的に

```text id="v5cz83"
追加剥離 layer
```

だからじゃ。

```text id="p5b1rc"
CountGe 2:
  追加で 1 個剥がす step

CountGe 3:
  追加で 2 個目まで剥がす強縮小 step

CountGe 4:
  さらに強い縮小 step
```

これが並ぶと、Petal 窓は drift budget の階層表になる。

## 9. 次の実装順序

わっちの指示としては、次の順がよい。

```text id="e116g3"
1. range_threshold_count_le

2. list_sum_ge_sum_countGe_range

3. orbitWindowHeightSeq_sum_ge_sum_countGe_range

4. orbitWindowHeightPrefix_sum_ge_sum_countGe_range

5. orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail

6. prefix 版の tail corollary
```

特に `list_sum_ge_sum_countGe_range` を切り出すのが肝じゃ。
Collatz 専用の theorem 内で全部やると、`List.countP` と `Finset.sum` の展開が重くなる。

## 10. 賢狼が試してほしいおまけ実験補題

おまけ実験として、次を試してほしい。

### 実験 A: 四層版

```lean id="b3g8dl"
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1
      + orbitWindowHeightCountGe n k 2
      + orbitWindowHeightCountGe n k 3
      + orbitWindowHeightCountGe n k 4
        ≤ sumS n k
```

三層が通ったので、おそらく四層も同じ形で通る。
ただし、ここを手で増やすより、一般 theorem に向かうための確認用でよい。

### 実験 B: `CountGe 2` があると drift が増える

これは実用補題じゃ。

```lean id="lvmbj0"
theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowHeightCountGe n k 2) :
    k + m ≤ sumS n k := by
  exact le_trans
    (Nat.add_le_add_left hm k)
    (orbitWindowHeightSeq_sum_ge_window_add_countGe_two n k)
```

意味は、

```text id="rseiee"
height >= 2 の step が少なくとも m 個あるなら、
sumS は k + m 以上
```

これがあると、後で統計・観測側から

```text id="k20m0f"
CountGe 2 >= m
```

を渡すだけで drift 下界が出る。

### 実験 C: prefix 版

```lean id="gk1y12"
theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
    (hm : m ≤ orbitWindowHeightPrefixCountGe n k r 2) :
    r + m ≤ sumS n r := by
  exact le_trans
    (Nat.add_le_add_left hm r)
    (orbitWindowHeightPrefix_sum_ge_window_add_countGe_two n hr)
```

これは局所 drift 診断にすぐ使える。

## 11. さらに先：`CountGe 2` のアドレス解釈

次の数学的本丸は、

```text id="cvsszb"
CountGe 2 をどう下から評価するか
```

じゃ。

`height >= 2` は、

```text id="ydzvwa"
4 ∣ 3n + 1
```

に対応するはず。

奇数 \(n\) の residue で見ると、これは特定の mod 4 class に対応する。
つまり、`CountGe 2` は **Petal address / residue occupation** へ接続できる。

次の方向はこれじゃ。

```text id="kp2qak"
height >= 2
  -> residue condition
  -> address cell occupation
  -> CountGe 2 lower bound
  -> sumS drift lower bound
```

これが通ると、本当に Petal らしくなる。

## 12. 総括

今回の進展はこう。

```text id="cyux92"
Collatz Petal 窓は、
height occupation count から、
Collatz 固有の drift lower-bound engine へ進化した。
```

特に、

```text id="fbcxai"
k + CountGe 2 <= sumS
```

が入ったのは大きい。

これは、

```text id="nz95ix"
全 step の最低剥離量
  + 追加剥離イベント数
```

という形で、Collatz の縮小力を有限窓内で読めるようにしたものじゃ。

うむ。
次は一般 finite layer-cake。
その次は `CountGe 2` の residue / Petal address 化。
そこまで行くと、Collatz はいよいよ「巨大数列」ではなく、**Petal 窓内の occupation と drift の問題** になってくる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index e91357e6..c2e61f70 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -486,6 +486,158 @@ theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
             hone, htwo, if_false]
           exact Nat.le_add_right_of_le ih'
 
+/--
+Every accelerated Collatz odd state has height at least `1`.
+
+This is the observation-window spelling of `v2_3n_plus_1_ge_1`: for an odd
+state, `3n + 1` is even, so at least one factor of `2` is peeled off.
+-/
+theorem orbitWindowHeight_one_le
+    (n : OddNat) (i : ℕ) :
+    1 ≤ orbitWindowHeight n i := by
+  rw [orbitWindowHeight_eq_s_iterateT]
+  simpa [s, threeNPlusOne] using
+    v2_3n_plus_1_ge_1 (iterateT i n).1 (iterateT i n).2
+
+/--
+The `height >= 1` occupation count fills the whole observation window.
+
+For Collatz odd-state dynamics, every accelerated step peels off at least one
+factor of `2`.
+-/
+theorem orbitWindowHeightCountGe_one_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 = k :=
+  orbitWindowHeightCountGe_eq_window_of_forall_ge n
+    (by
+      intro i _hi
+      exact orbitWindowHeight_one_le n i)
+
+/--
+Collatz-specific two-layer drift lower bound.
+
+The first layer contributes one unit at every step.  The second layer counts
+the steps where at least one additional factor of `2` is peeled off.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k := by
+  simpa [orbitWindowHeightCountGe_one_eq_window n k] using
+    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n k
+
+/--
+The prefix `height >= 1` count fills the prefix length.
+-/
+theorem orbitWindowHeightPrefixCountGe_one_eq
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    orbitWindowHeightPrefixCountGe n k r 1 = r := by
+  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
+  exact orbitWindowHeightCountGe_one_eq_window n r
+
+/--
+Prefix version of the Collatz-specific two-layer drift lower bound.
+
+Inside a larger observation window, the first `r` steps contribute at least
+`r`, plus one more unit for every prefix step whose height is at least `2`.
+-/
+theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r := by
+  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
+  simpa [orbitWindowHeightCountGe_one_eq_window n r] using
+    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n r
+
+/--
+Threshold occupation is antitone in the threshold.
+
+Raising the threshold can only remove entries from the counted regime.
+-/
+theorem orbitWindowHeightCountGe_antitone
+    (n : OddNat) (k : ℕ) {a b : ℕ}
+    (hab : a ≤ b) :
+    orbitWindowHeightCountGe n k b ≤ orbitWindowHeightCountGe n k a := by
+  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      have ih' :
+          List.countP ((fun x => decide (b ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) ≤
+            List.countP ((fun x => decide (a ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) := by
+        simpa [List.countP_map] using ih
+      by_cases hb : b ≤ orbitWindowHeight n k
+      · have ha : a ≤ orbitWindowHeight n k := le_trans hab hb
+        rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hb, ha, if_true]
+        exact Nat.add_le_add ih' le_rfl
+      · rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hb, if_false]
+        exact Nat.le_add_right_of_le ih'
+
+/--
+Experimental finite layer-cake lower bound for the first three height layers.
+
+This extends the two-layer theorem by adding the `height >= 3` occupation
+layer.  It is intentionally concrete: if this shape remains useful, the next
+step is a general finite layer-cake theorem over `Finset.range H`.
+-/
+theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
+        orbitWindowHeightCountGe n k 3 ≤ sumS n k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
+  | succ k ih =>
+      have ih' :
+          List.countP ((fun x => decide (1 ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) +
+              List.countP ((fun x => decide (2 ≤ x)) ∘ orbitWindowHeight n)
+                (List.range k) +
+            List.countP ((fun x => decide (3 ≤ x)) ∘ orbitWindowHeight n)
+              (List.range k) ≤ sumS n k := by
+        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
+      by_cases hthree : 3 ≤ orbitWindowHeight n k
+      · have htwo : 2 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) hthree
+        have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
+        rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+        rw [List.range_succ]
+        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+          hone, htwo, hthree, if_true]
+        omega
+      · by_cases htwo : 2 ≤ orbitWindowHeight n k
+        · have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
+          rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+          rw [List.range_succ]
+          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+            hone, htwo, hthree, if_true, if_false]
+          omega
+        · by_cases hone : 1 ≤ orbitWindowHeight n k
+          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+            rw [List.range_succ]
+            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+              hone, htwo, hthree, if_true, if_false]
+            omega
+          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
+            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+            rw [List.range_succ]
+            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
+              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
+              hone, htwo, hthree, if_false]
+            exact Nat.le_add_right_of_le ih'
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 1546518b..62da4cf5 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -123,6 +123,13 @@ orbitWindowHeightPrefixCountGe
 orbitWindowHeightPrefixCountGe_eq_countGe
 orbitWindowHeightPrefixCountGe_mul_le_sumS
 orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
+orbitWindowHeight_one_le
+orbitWindowHeightCountGe_one_eq_window
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+orbitWindowHeightPrefixCountGe_one_eq
+orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
+orbitWindowHeightCountGe_antitone
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -278,6 +285,21 @@ prefix threshold count in a k-window, with r <= k
 
 first two layer-cake layers
   -> CountGe 1 + CountGe 2 <= sumS n k
+
+Collatz odd-state height floor
+  -> CountGe 1 = k
+
+Collatz-specific two-layer lower bound
+  -> k + CountGe 2 <= sumS n k
+
+prefix Collatz-specific two-layer lower bound
+  -> r + prefix CountGe 2 <= sumS n r
+
+threshold monotonicity
+  -> CountGe b <= CountGe a when a <= b
+
+first three layer-cake layers
+  -> CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -297,6 +319,40 @@ current API local and elementary because the data here is just a finite ordered
 list of natural 2-adic heights.  This avoids pulling the ABC analytic stack into
 the observation-window layer before a real carrier/radical bridge exists.
 
+The Collatz-specific floor is now also fixed:
+
+```text
+every accelerated odd state has height >= 1
+```
+
+Therefore the first layer is not merely an occupation statistic; it is the full
+window size:
+
+```text
+CountGe 1 = k
+```
+
+The two-layer lower bound becomes the practical drift estimate:
+
+```text
+k + CountGe 2 <= sumS n k
+```
+
+and the same statement is available for prefixes:
+
+```text
+r + prefix CountGe 2 <= sumS n r
+```
+
+The experimental three-layer theorem also passed:
+
+```text
+CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
+```
+
+This is evidence that the next natural theorem is the general finite
+layer-cake form over `Finset.range H`.
+
 The bridge theorem
 
 ```lean
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/next-impl-plan-082.md b/lean/dk_math/docs/dev/das-p2l-260607/review/next-impl-plan-082.md
new file mode 100644
index 00000000..3ed2143a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/next-impl-plan-082.md
@@ -0,0 +1,127 @@
+# Research Report and Next Implementation: No.082 cp
+
+## Current status: `height >= 1` and the three-layer experiment are closed
+
+The previous target has been implemented in `DkMath.Collatz.PetalBridge`.
+
+Closed core API:
+
+```lean
+orbitWindowHeight_one_le
+orbitWindowHeightCountGe_one_eq_window
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+orbitWindowHeightPrefixCountGe_one_eq
+orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
+```
+
+Closed extra API:
+
+```lean
+orbitWindowHeightCountGe_antitone
+```
+
+Closed experiment:
+
+```lean
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
+```
+
+This means the current Lean state has:
+
+```text
+CountGe 1 = k
+k + CountGe 2 <= sumS n k
+CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
+```
+
+The next implementation should therefore move from fixed two/three-layer
+experiments to a general finite layer-cake theorem.
+
+## 6. Next target: finite layer-cake helper
+
+Start with the finite threshold-count helper:
+
+```lean id="z4i2au"
+private theorem range_threshold_count_le
+    (H x : ℕ) :
+    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
+```
+
+Meaning:
+
+```text id="fo0cre"
+Among thresholds 1, 2, ..., H, at most x thresholds are <= x.
+```
+
+This is the local per-entry bound needed for finite layer-cake:
+
+```text
+one height x contributes to the layers t+1 <= x,
+and the number of such layers is <= x.
+```
+
+## 7. Main theorem candidate
+
+Then try:
+
+```lean id="cmslrx"
+theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
+    (n : OddNat) (k H : ℕ) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 1))
+      ≤ sumS n k
+```
+
+Meaning:
+
+```text id="swywnk"
+CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
+```
+
+This theorem generalizes the currently proved two-layer and three-layer
+experimental theorems.
+
+## 8. Prefix generalization after the main theorem
+
+If the full-window theorem closes, add the prefix version:
+
+```lean
+theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
+      ≤ sumS n r
+```
+
+This should rewrite prefix counts to standalone counts using:
+
+```lean
+orbitWindowHeightPrefixCountGe_eq_countGe
+```
+
+## 9. Collatz-specific corollary
+
+Once general finite layer-cake exists, specialize the first layer:
+
+```text
+CountGe 1 = k
+```
+
+For `H >= 1`, this should produce:
+
+```text
+k + CountGe 2 + ... + CountGe H <= sumS n k
+```
+
+This is the route from local occupation statistics to a drift budget.
+
+## 10. Implementation order
+
+Recommended order:
+
+```text id="ryo4pz"
+1. range_threshold_count_le
+2. orbitWindowHeightSeq_sum_ge_sum_countGe_range
+3. orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+4. Collatz-specific corollary with CountGe 1 = k
+```
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-082.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-082.md
new file mode 100644
index 00000000..b089de45
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-082.md
@@ -0,0 +1,192 @@
+# Git diff / Report / Review
+
+No.082 cp
+
+## Upd: Collatz.PetalBridge
+
+Date: 2026/06/30 06:13 JST
+
+## Report
+
+`DkMath.Collatz.PetalBridge` の height occupation layer を、Collatz 固有の
+`height >= 1` 事実へ接続しました。
+
+今回の本線実装:
+
+```lean
+orbitWindowHeight_one_le
+orbitWindowHeightCountGe_one_eq_window
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+orbitWindowHeightPrefixCountGe_one_eq
+orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
+```
+
+追加の分布 API:
+
+```lean
+orbitWindowHeightCountGe_antitone
+```
+
+おまけ実験:
+
+```lean
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
+```
+
+`Collatz-PetalBridge-Status.md` も更新し、二層から三層への進展と、
+`DkMath.ABC.LayerCakeBasic` との住み分けを維持したまま local Nat count
+layer-cake として進める方針を記録しました。
+
+確認:
+
+```bash
+lake build DkMath.Collatz.PetalBridge
+```
+
+成功。既存の
+`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6: declaration uses sorry`
+警告のみ再表示。
+
+## Result
+
+今回の中心はこれです。
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k
+```
+
+意味:
+
+```text
+全 accelerated odd step で最低 1 個の 2 を剥がす。
+height >= 2 の step では、さらに 1 個の 2 を剥がす。
+したがって k + CountGe 2 が sumS の下界になる。
+```
+
+これは前回の
+
+```text
+CountGe 1 + CountGe 2 <= sumS
+```
+
+を、Collatz 固有の `CountGe 1 = k` で具体化したものです。
+
+prefix 版も同時に固定しました。
+
+```lean
+theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r
+```
+
+これにより、大きな観測窓 `k` の中で先頭 `r` だけを見る局所 drift 下界が
+直接使えます。
+
+## Experiment
+
+三層版も no-sorry で通りました。
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
+        orbitWindowHeightCountGe n k 3 ≤ sumS n k
+```
+
+これは重要です。
+
+二層だけなら偶然の手計算で済む可能性がありますが、三層も同じ帰納形で通るなら、
+一般 finite layer-cake の形が見えてきます。
+
+推論:
+
+```text
+height = h の 1 点は、
+  CountGe 1
+  CountGe 2
+  ...
+  CountGe h
+に 1 回ずつ寄与する。
+```
+
+したがって自然な次目標は:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
+    (n : OddNat) (k H : ℕ) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 1))
+      ≤ sumS n k
+```
+
+## Additional API
+
+`CountGe` の threshold 単調性を固定しました。
+
+```lean
+theorem orbitWindowHeightCountGe_antitone
+    (n : OddNat) (k : ℕ) {a b : ℕ}
+    (hab : a ≤ b) :
+    orbitWindowHeightCountGe n k b ≤ orbitWindowHeightCountGe n k a
+```
+
+これで分布階層を言えるようになります。
+
+```text
+CountGe 3 <= CountGe 2 <= CountGe 1 = k
+```
+
+## Review
+
+今回の到達点は、Collatz height occupation が「単なる count」から
+「drift lower-bound engine」へ移ったことです。
+
+以前:
+
+```text
+height >= threshold の点が c 個ある
+  -> c * threshold <= sumS
+```
+
+現在:
+
+```text
+height layer を足し上げる
+  -> CountGe 1 + CountGe 2 + CountGe 3 <= sumS
+  -> Collatz では CountGe 1 = k
+  -> k + CountGe 2 <= sumS
+```
+
+ここから次に必要なのは、`CountGe 2`, `CountGe 3`, ... をどう評価するかです。
+これは確率化・Markov kernel へ行く前の、有限観測窓上の occupation 推定問題です。
+
+## Next Inference
+
+次回は一般 finite layer-cake を狙うのが自然です。
+
+第一補助候補:
+
+```lean
+private theorem range_threshold_count_le
+    (H x : ℕ) :
+    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
+```
+
+この補題の意味:
+
+```text
+threshold 1..H のうち、x 以下のものは高々 x 個。
+```
+
+これがあれば、list induction で一般 finite layer-cake を組み立てられる見込みです。
+
+次の実験候補:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
+```
+
+この一般形が通れば、Collatz 側の `sumS` は有限 layer occupation の総予算として
+扱えるようになります。
````
`````
