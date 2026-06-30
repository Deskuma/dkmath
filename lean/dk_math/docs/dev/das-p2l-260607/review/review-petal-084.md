# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 1788fdb63ab85b23138150b68cab97d117bf544c

## Report

実装しました。checkpoint `083` は、一般 finite layer-cake まで到達しています。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:650) に追加した主な定理:

```lean
range_threshold_count_le
list_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightPrefix_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
```

おまけ実験として四層版も追加しました。

```lean
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
```

これは手書き帰納ではなく、一般 theorem `orbitWindowHeightSeq_sum_ge_sum_countGe_range` の `H = 4` 特殊化として通しています。つまり、固定深度の layer 補題は一般 finite layer-cake の例になりました。

ドキュメントも同期しました。

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:126)
- [report-petal-083.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-083.md:1)

検証:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-083.md
```

すべて成功です。既存の `ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告のみ再表示されています。

次の推論先は `CountGe 2` の下界です。`height >= 2` は `4 ∣ 3n + 1` に対応するはずなので、次は residue / Petal address occupation へ接続するのが自然です。

## Review

## 1. 状況分析

これは大きい。
checkpoint `083` で、**一般 finite layer-cake が閉じた**。

前回までは、

```text id="mxp35p"
CountGe 1 + CountGe 2 <= sumS
CountGe 1 + CountGe 2 + CountGe 3 <= sumS
```

という固定深度の実験だった。

今回、

```lean id="lbce85"
orbitWindowHeightSeq_sum_ge_sum_countGe_range
```

が入ったことで、任意の有限深度 `H` に対して、

```text id="qr93ex"
CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
```

が Lean で固定された。

添付レポートでも、今回の中心定理は `orbitWindowHeightSeq_sum_ge_sum_countGe_range` であり、二層・三層観測が一般 finite layer-cake theorem にアップグレードされたと整理されている。

これは、Collatz.PetalBridge の height 観測が **完全に drift-budget engine になった** ということじゃ。

## 2. 今回の中核

追加された主な API はこれ。

```lean id="gjlecp"
range_threshold_count_le
list_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightPrefix_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
```

特に美しいのは、証明を Collatz 専用にせず、まず list / Nat 補題として切り出した点じゃ。

```lean id="qdfvsz"
private theorem list_sum_ge_sum_countGe_range
    (l : List ℕ) (H : ℕ) :
    (Finset.range H).sum
        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
      ≤ l.sum
```

これは Collatz とは無関係の有限 layer-cake 補題。

つまり、数学的には次を言っている。

```text id="2m5cdv"
自然数列 l に対して、
各 threshold 層の occupation count を有限個足しても、
元の値の総和を超えない。
```

その上で `l = orbitWindowHeightSeq n k` と置き、

```lean id="wcaztk"
(orbitWindowHeightSeq n k).sum = sumS n k
```

を使って Collatz に戻している。

この分離はとても良い。
PetalBridge の中に「一般有限測度エンジン」ができた。

## 3. 数学的な意味

いま証明されたのは、自然数 height 列 \(h_0,\dots,h_{k-1}\) に対して、

$$
\sum_{t=1}^{H}#{i<k\mid h_i\ge t}\le \sum_{i=0}^{k-1}h_i
$$

という有限 layer-cake 下界じゃ。

Collatz では、

$$
h_i=v_2(3T^i(n)+1)
$$

なので、右辺は `sumS n k`。

したがって、

$$
\sum_{t=1}^{H}#{i<k\mid h_i\ge t}\le sumS(n,k)
$$

となる。

これは、`sumS` を単なる合計ではなく、

```text id="3wxj5a"
height layer occupation の総予算
```

として見られることを意味する。

## 4. Collatz 固有の tail 形

さらに今回の良い点は、Collatz 固有の第一層を分離したことじゃ。

Collatz odd state では常に

```text id="h7r9b0"
height >= 1
```

なので、

```text id="o0kl7e"
CountGe 1 = k
```

となる。

これを一般 layer-cake に入れて、

```lean id="z078lp"
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

が得られた。

意味は、

```text id="k38wln"
k + CountGe 2 + CountGe 3 + ... + CountGe (H+1) <= sumS
```

じゃ。

これはかなり実用的な形。

なぜなら、`k` は最低限の剥離量で、`CountGe 2` 以降が追加剥離イベントだからじゃ。

```text id="5t95np"
base peeling:
  k

extra peeling:
  CountGe 2 + CountGe 3 + ...
```

つまり `sumS` が、

```text id="imn2ug"
基本縮小量
  + 追加縮小量
```

に分解され始めた。

## 5. Prefix 版の意味

prefix 版も入っている。

```lean id="vu1x38"
orbitWindowHeightPrefix_sum_ge_sum_countGe_range
orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
```

これは、長い観測窓 `k` の中で、先頭 `r` だけを見て同じ layer-cake が使えるということじゃ。

```text id="778orc"
prefix r
  -> local layer occupation
  -> local sumS n r
  -> local drift budget
```

これは後で軌道の途中区間や初期膨張区間を調べるときに重要になる。

## 6. 実用 bridge が入った意味

今回さらに、

```lean id="t2sj25"
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
```

が入った。

これは、

```text id="0hwc1i"
m <= CountGe 2
  -> k + m <= sumS
```

を言う。

これは今後の bridge として非常に重要じゃ。

なぜなら、次に Petal address / residue 側でやるべきことは、

```text id="rkou67"
CountGe 2 が少なくとも m 個ある
```

を示すことだからじゃ。

それができた瞬間、

```text id="vcrh1k"
k + m <= sumS
```

が自動で出る。

つまり、今後の residue/address occupation theorem は、`sumS` を直接触らなくてよい。

```text id="9u2r4c"
address 側:
  m <= CountGe 2 を示す

PetalBridge 側:
  k + m <= sumS へ変換する
```

この分担ができた。

## 7. レビュー

今回の実装は構成がとても良い。

### 良い点 1: Collatz-independent helper

`list_sum_ge_sum_countGe_range` を private helper として切ったことで、一般 layer-cake の核心が軌道定義から分離された。

これは正しい。

### 良い点 2: Fixed-depth theorem を一般 theorem の例にした

四層版は、

```lean id="msb97o"
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
```

として残しているが、手書き帰納ではなく一般 theorem の `H = 4` から出している。

これは良い「実験 witness」じゃ。
読みやすい補題名は残しつつ、証明負債を増やしていない。

### 良い点 3: 次の責務が明確になった

レポートにもある通り、次は layer-cake ではなく、

```text id="dmrc4j"
CountGe 2 lower bound
```

じゃ。

つまり本丸が明確になった。

## 8. 次の指示：`height >= 2` を residue 条件へ落とす

次はこれ。

```text id="l63p2w"
height >= 2
  <-> 4 ∣ 3n + 1
```

を固定する。

まず raw label で。

```lean id="tw9qy7"
theorem rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
    (n : ℕ) :
    2 ≤ rawHeightLabel n ↔ 4 ∣ 3 * n + 1
```

ただし、既存の `v2` API によって statement は調整が必要。

もし `v2 m` が `padicValNat 2 m` 相当なら、一般補題として、

```lean id="b6b7j0"
theorem two_le_v2_iff_four_dvd
    {m : ℕ} (hm : m ≠ 0) :
    2 ≤ v2 m ↔ 4 ∣ m
```

が先かもしれない。

その後、Collatz height へ持ち上げる。

```lean id="eulx4g"
theorem orbitWindowHeight_two_le_iff_four_dvd
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n i ↔
      4 ∣ 3 * oddOrbitLabel n i + 1
```

そして residue へ。

奇数 \(m\) について、

```text id="x7q1w8"
4 ∣ 3m + 1
```

は、

```text id="oxzspr"
m ≡ 1 mod 4
```

に対応するはずじゃ。

確認すると、

```text id="5fmyw8"
m ≡ 1 mod 4
  -> 3m + 1 ≡ 3 + 1 ≡ 0 mod 4
```

一方、

```text id="kwpqnd"
m ≡ 3 mod 4
  -> 3m + 1 ≡ 9 + 1 ≡ 2 mod 4
```

なので、奇数では確かに `m % 4 = 1` が height >= 2 の条件になる。

候補 theorem:

```lean id="vswrxc"
theorem odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
    {m : ℕ} (hmOdd : Odd m) :
    4 ∣ 3 * m + 1 ↔ m % 4 = 1
```

そして軌道版。

```lean id="6mdnnu"
theorem orbitWindowHeight_two_le_iff_mod_four_eq_one
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 4 = 1
```

これが次の本命じゃ。

## 9. 一歩先ゆく推論：CountGe 2 を residue occupation へ

`height >= 2` と `mod 4 = 1` がつながったら、次は count の同一視。

定義候補。

```lean id="dckacl"
noncomputable def orbitWindowResidueCountMod4EqOne
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 1))
```

または、既存の height seq に合わせるなら、index count でもよい。

主 theorem。

```lean id="9xul0u"
theorem orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 2 =
      orbitWindowResidueCountMod4EqOne n k
```

これが通ると、

```text id="pywv5l"
residue occupation
  -> CountGe 2
  -> k + m <= sumS
```

の橋ができる。

さらに、もし residue 側で

```lean id="e92jab"
m ≤ orbitWindowResidueCountMod4EqOne n k
```

を示せば、既存の

```lean id="r7rx25"
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
```

で

```text id="aanmkd"
k + m <= sumS n k
```

へ渡せる。

## 10. さらに先：transition residue map

その次は、mod 4 だけでなく、加速写像の residue transition を見る。

height が 1 の場合と 2 以上の場合で、次の奇数状態への写像が変わる。

```text id="b91lbr"
m ≡ 3 mod 4:
  height = 1

m ≡ 1 mod 4:
  height >= 2
```

さらに height >= 3 は mod 8 条件。

一般に、

```text id="06vxu8"
height >= r
  <-> 2^r ∣ 3m + 1
  <-> m ≡ a_r mod 2^r
```

ここで \(a_r\) は \(3^{-1}(-1)\) modulo \(2^r\)。

この一般 residue coordinate が Petal address の本体になりそうじゃ。

候補としては、

```lean id="0pqz2s"
def collatzHeightResidue (r : ℕ) : ZMod (2^r) := ...
```

だが、これは少し重い。
まずは mod 4、次に mod 8 がよい。

## 11. 賢狼が試してほしいおまけ実験補題

### おまけ A: `height >= 3` と mod 8

奇数 \(m\) について、

```text id="j2a6bg"
v2(3m + 1) >= 3
```

は

```text id="skkr45"
8 ∣ 3m + 1
```

で、これは `m % 8 = 5` になるはず。

確認：

```text id="z8r5id"
m = 5
3m + 1 = 16
```

候補 theorem:

```lean id="idf3pq"
theorem orbitWindowHeight_three_le_iff_mod_eight_eq_five
    (n : OddNat) (i : ℕ) :
    3 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 8 = 5
```

これはかなり良い実験。
`height >= 2` の mod 4 版が通ったら、同じ方針で mod 8 も試せる。

### おまけ B: `height >= 4` と mod 16

同様に、

```text id="v19fkj"
16 ∣ 3m + 1
```

を解くと、

```text id="s4d58u"
m ≡ 5 mod 16
```

か確認したい。

実際、

```text id="nwa9wb"
m = 5
3m + 1 = 16
```

なので `m % 16 = 5` で height >= 4。

候補 theorem:

```lean id="yi2a8d"
theorem orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
    (n : OddNat) (i : ℕ) :
    4 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 16 = 5
```

ただし一般に residue は r ごとに変わるので、ここは必ず手計算で確認してから入れる。

### おまけ C: residue count bridge for mod 4

```lean id="dmjr78"
theorem orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowResidueCountMod4EqOne n k) :
    k + m ≤ sumS n k
```

これは、residue occupation が drift に直結する最初の theorem になる。

## 12. 実装順序まとめ

次コミットの推奨順。

```text id="olbhx6"
1. v2 側の補題を確認
   two_le_v2_iff_four_dvd が既存か探す

2. rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne

3. orbitWindowHeight_two_le_iff_four_dvd

4. odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one

5. orbitWindowHeight_two_le_iff_mod_four_eq_one

6. orbitWindowResidueCountMod4EqOne

7. orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one

8. residue count lower bound -> sumS bridge
```

おまけで、

```text id="0ptjj1"
9. height >= 3 <-> mod 8 = 5
10. height >= 4 <-> mod 16 = 5
```

を試す。

## 13. 総括

今回の checkpoint `083` で、

```text id="eix034"
finite layer-cake
```

は閉じた。

したがって次の本丸は、

```text id="z1v3g6"
occupation count をどう評価するか
```

に移った。

最初の対象は `CountGe 2`。

そして `CountGe 2` は、

```text id="arxmt4"
height >= 2
  -> 4 | 3n + 1
  -> n % 4 = 1
```

として residue / address occupation に落ちる。

うむ。
ここから Petal は、単なる height 窓ではなく、**residue address 窓**になる。
Collatz の drift は、いよいよ「どの剰余区画に何回滞在するか」という問題へ変換される。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index c2e61f70..2b118650 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -638,6 +638,169 @@ theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_thre
               hone, htwo, hthree, if_false]
             exact Nat.le_add_right_of_le ih'
 
+/--
+Only `x` of the positive thresholds can be visible below a natural height `x`.
+
+This is the local counting fact behind the finite layer-cake theorem: among
+the thresholds `1, 2, ..., H`, at most `x` thresholds are `<= x`.
+-/
+private theorem range_threshold_count_le
+    (H x : ℕ) :
+    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x := by
+  calc
+    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card
+        ≤ (Finset.range x).card := by
+          apply Finset.card_le_card
+          intro t ht
+          have htx : t + 1 ≤ x := (Finset.mem_filter.mp ht).2
+          have htlt : t < x := Nat.lt_of_succ_le htx
+          simpa using htlt
+    _ = x := by
+      simp
+
+/--
+Finite layer-cake lower bound for a list of natural heights.
+
+The sum of threshold occupations over thresholds `1, ..., H` is bounded by the
+ordinary sum of the list.  This is Collatz-independent and keeps the finite
+counting engine separate from the orbit-window vocabulary.
+-/
+private theorem list_sum_ge_sum_countGe_range
+    (l : List ℕ) (H : ℕ) :
+    (Finset.range H).sum
+        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
+      ≤ l.sum := by
+  induction l with
+  | nil =>
+      simp
+  | cons x xs ih =>
+      have hhead :
+          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0) ≤ x := by
+        calc
+          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0)
+              = ((Finset.range H).filter (fun t => t + 1 ≤ x)).card := by
+                simp
+          _ ≤ x := range_threshold_count_le H x
+      calc
+        (Finset.range H).sum
+            (fun t => (x :: xs).countP (fun y => decide (t + 1 ≤ y)))
+            =
+          (Finset.range H).sum (fun t => (if t + 1 ≤ x then 1 else 0) +
+              xs.countP (fun y => decide (t + 1 ≤ y))) := by
+              apply Finset.sum_congr rfl
+              intro t _ht
+              by_cases ht : t < x
+              · have ht' : t + 1 ≤ x := Nat.succ_le_iff.mpr ht
+                simp [ht, ht', Nat.add_comm]
+              · have ht' : ¬ t + 1 ≤ x := by
+                  intro h
+                  exact ht (Nat.lt_of_succ_le h)
+                simp [ht, ht']
+        _ =
+          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0) +
+            (Finset.range H).sum
+              (fun t => xs.countP (fun y => decide (t + 1 ≤ y))) := by
+              rw [Finset.sum_add_distrib]
+        _ ≤ x + xs.sum := Nat.add_le_add hhead ih
+        _ = (x :: xs).sum := by
+          simp
+
+/--
+General finite layer-cake lower bound for the ordered Collatz height profile.
+
+The first `H` threshold occupation layers are jointly bounded by the accumulated
+Collatz height `sumS`.
+-/
+theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
+    (n : OddNat) (k H : ℕ) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 1))
+      ≤ sumS n k := by
+  have h := list_sum_ge_sum_countGe_range (orbitWindowHeightSeq n k) H
+  rw [orbitWindowHeightSeq_sum_eq_sumS n k] at h
+  simpa [orbitWindowHeightCountGe] using h
+
+/--
+Four-layer finite layer-cake lower bound, now derived from the general theorem.
+
+This is kept as an explicit experiment witness: the fixed-depth layer lemmas no
+longer need independent induction proofs once the general finite layer-cake
+theorem is available.
+-/
+theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
+        orbitWindowHeightCountGe n k 3 + orbitWindowHeightCountGe n k 4 ≤
+      sumS n k := by
+  have h := orbitWindowHeightSeq_sum_ge_sum_countGe_range n k 4
+  norm_num [Finset.sum_range_succ, Nat.add_assoc] at h
+  simpa [Nat.add_assoc] using h
+
+/--
+Prefix version of the finite layer-cake lower bound.
+
+Inside an ambient `k`-window, the first `r` observations have the same finite
+layer-cake budget as the standalone `r`-window.
+-/
+theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
+      ≤ sumS n r := by
+  have h := orbitWindowHeightSeq_sum_ge_sum_countGe_range n r H
+  simpa [orbitWindowHeightPrefixCountGe_eq_countGe n hr] using h
+
+/--
+Collatz-specific finite layer-cake tail bound.
+
+The first layer is always the full window size `k`; the remaining finite
+layers measure additional peeling events.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+    (n : OddNat) (k H : ℕ) :
+    k + (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 2))
+      ≤ sumS n k := by
+  simpa [Finset.sum_range_succ', orbitWindowHeightCountGe_one_eq_window n k,
+    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
+    orbitWindowHeightSeq_sum_ge_sum_countGe_range n k (H + 1)
+
+/--
+Prefix version of the Collatz-specific finite layer-cake tail bound.
+-/
+theorem orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
+    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
+    r + (Finset.range H).sum
+        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 2))
+      ≤ sumS n r := by
+  simpa [Finset.sum_range_succ', orbitWindowHeightPrefixCountGe_one_eq n hr,
+    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
+    orbitWindowHeightPrefix_sum_ge_sum_countGe_range n (r := r) (k := k) (H := H + 1) hr
+
+/--
+If at least `m` observations have height `>= 2`, then the accumulated height is
+at least `k + m`.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+    (n : OddNat) (k m : ℕ)
+    (hm : m ≤ orbitWindowHeightCountGe n k 2) :
+    k + m ≤ sumS n k := by
+  exact le_trans
+    (Nat.add_le_add_left hm k)
+    (orbitWindowHeightSeq_sum_ge_window_add_countGe_two n k)
+
+/--
+Prefix version: a lower bound on the prefix `height >= 2` occupation gives a
+local drift lower bound.
+-/
+theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
+    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
+    (hm : m ≤ orbitWindowHeightPrefixCountGe n k r 2) :
+    r + m ≤ sumS n r := by
+  exact le_trans
+    (Nat.add_le_add_left hm r)
+    (orbitWindowHeightPrefix_sum_ge_window_add_countGe_two n hr)
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 62da4cf5..58d33289 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -130,6 +130,13 @@ orbitWindowHeightPrefixCountGe_one_eq
 orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
 orbitWindowHeightCountGe_antitone
 orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
+orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
+orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -300,6 +307,18 @@ threshold monotonicity
 
 first three layer-cake layers
   -> CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
+
+finite layer-cake
+  -> Sum_{t < H} CountGe (t + 1) <= sumS n k
+
+first four layer-cake layers
+  -> CountGe 1 + CountGe 2 + CountGe 3 + CountGe 4 <= sumS n k
+
+finite tail layer-cake
+  -> k + Sum_{t < H} CountGe (t + 2) <= sumS n k
+
+external CountGe 2 lower bound
+  -> m <= CountGe 2 -> k + m <= sumS n k
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -350,8 +369,34 @@ The experimental three-layer theorem also passed:
 CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
 ```
 
-This is evidence that the next natural theorem is the general finite
-layer-cake form over `Finset.range H`.
+This evidence has now been upgraded to the general finite layer-cake theorem:
+
+```text
+Sum_{t < H} CountGe (t + 1) <= sumS n k
+```
+
+The explicit four-layer theorem is retained as a readable experiment witness,
+but it is now derived from the general theorem rather than proved by another
+hand-written induction.
+
+Since `CountGe 1 = k`, the practical Collatz-facing form is the tail budget:
+
+```text
+k + Sum_{t < H} CountGe (t + 2) <= sumS n k
+```
+
+This separates the always-present base peeling from the additional peeling
+events.  The same structure is also available for prefixes.
+
+Finally, downstream observation layers can now feed the drift estimate by
+proving only a lower bound on the second layer:
+
+```text
+m <= CountGe 2 -> k + m <= sumS n k
+```
+
+This is the intended bridge from a future residue/address occupation theorem
+to a Collatz drift lower bound.
 
 The bridge theorem
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-083.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-083.md
new file mode 100644
index 00000000..9d6080e8
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-083.md
@@ -0,0 +1,290 @@
+# Report: Petal 083
+
+Date: 2026/06/30 15:16 JST
+
+## Scope
+
+Checkpoint `083` implemented the general finite layer-cake stage for
+`DkMath.Collatz.PetalBridge`.
+
+The input instruction was:
+
+```text
+general finite layer-cake
+  -> list / Nat helper
+  -> Collatz height profile theorem
+  -> prefix theorem
+  -> Collatz-specific tail theorem
+  -> small experiments and next inference
+```
+
+The temporary `__next_implementation-083.md` file was used only as input.  It
+was not edited, following the docs filename rule for temporary `__*` files.
+
+## Implemented API
+
+New private helpers:
+
+```lean
+range_threshold_count_le
+list_sum_ge_sum_countGe_range
+```
+
+New public finite layer-cake theorems:
+
+```lean
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+```
+
+New Collatz-specific tail forms:
+
+```lean
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
+```
+
+New practical observation-to-drift bridges:
+
+```lean
+orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
+```
+
+New explicit experiment witness:
+
+```lean
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
+```
+
+## Main Result
+
+The central theorem is:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
+    (n : OddNat) (k H : ℕ) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 1))
+      ≤ sumS n k
+```
+
+Meaning:
+
+```text
+CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
+```
+
+This upgrades the previous two-layer and three-layer observations into a
+general finite layer-cake theorem.
+
+## Proof Shape
+
+The proof was split before touching Collatz-specific vocabulary.
+
+First, a local threshold-count helper:
+
+```lean
+private theorem range_threshold_count_le
+    (H x : ℕ) :
+    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
+```
+
+Meaning:
+
+```text
+Among thresholds 1, ..., H, at most x thresholds are <= x.
+```
+
+Then, a Collatz-independent list theorem:
+
+```lean
+private theorem list_sum_ge_sum_countGe_range
+    (l : List ℕ) (H : ℕ) :
+    (Finset.range H).sum
+        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
+      ≤ l.sum
+```
+
+The list proof is the finite layer-cake engine.  Each head element `x`
+contributes to the visible layers `t + 1 <= x`, and
+`range_threshold_count_le` bounds that contribution by `x`.
+
+The Collatz theorem then follows by applying the list theorem to
+`orbitWindowHeightSeq n k` and rewriting its sum as `sumS n k`.
+
+## Collatz Tail Form
+
+Because Collatz odd-state dynamics already proved:
+
+```text
+CountGe 1 = k
+```
+
+the more useful form separates the base layer:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+    (n : OddNat) (k H : ℕ) :
+    k + (Finset.range H).sum
+        (fun t => orbitWindowHeightCountGe n k (t + 2))
+      ≤ sumS n k
+```
+
+Meaning:
+
+```text
+base peeling k
+  + CountGe 2
+  + CountGe 3
+  + ...
+  + CountGe (H + 1)
+  <= sumS
+```
+
+This is the currently most useful drift-budget theorem.
+
+## Prefix Form
+
+The prefix version was also implemented:
+
+```lean
+theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
+    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
+    (Finset.range H).sum
+        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
+      ≤ sumS n r
+```
+
+and the Collatz-specific prefix tail:
+
+```lean
+theorem orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
+    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
+    r + (Finset.range H).sum
+        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 2))
+      ≤ sumS n r
+```
+
+This keeps local-window diagnostics available without leaving the finite
+observation-window setting.
+
+## Experiment
+
+The four-layer theorem was added as an explicit witness:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
+        orbitWindowHeightCountGe n k 3 + orbitWindowHeightCountGe n k 4 ≤
+      sumS n k
+```
+
+This theorem is not proved by a new hand-written induction.  It is derived from
+the general finite layer-cake theorem at `H = 4`.
+
+Result:
+
+```text
+The fixed-depth layer theorems are now examples of the general theorem.
+```
+
+## Practical Bridge
+
+Two small corollaries turn future occupation estimates directly into drift
+lower bounds:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+    (n : OddNat) (k m : ℕ)
+    (hm : m ≤ orbitWindowHeightCountGe n k 2) :
+    k + m ≤ sumS n k
+```
+
+```lean
+theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
+    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
+    (hm : m ≤ orbitWindowHeightPrefixCountGe n k r 2) :
+    r + m ≤ sumS n r
+```
+
+Meaning:
+
+```text
+If a future residue/address theorem proves CountGe 2 >= m,
+then the drift lower bound k + m <= sumS follows immediately.
+```
+
+This is the bridge from Petal address occupation to Collatz drift.
+
+## Documentation
+
+Updated:
+
+```text
+DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status document now records:
+
+```text
+finite layer-cake
+finite tail layer-cake
+four-layer experiment witness
+external CountGe 2 lower-bound bridge
+```
+
+## Verification
+
+The targeted build passed:
+
+```bash
+lake build DkMath.Collatz.PetalBridge
+```
+
+Existing unrelated warning still appears:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses sorry
+```
+
+## Next Inference
+
+The next mathematical target is no longer layer-cake itself.  It is now:
+
+```text
+CountGe 2 lower bound
+```
+
+For Collatz:
+
+```text
+height >= 2
+  means v2(3n + 1) >= 2
+  means 4 divides 3n + 1
+```
+
+For odd `n`, this should correspond to a residue class modulo `4`.
+
+Thus the next implementation direction should be:
+
+```text
+height >= 2
+  -> residue condition modulo 4
+  -> address / residue occupation count
+  -> CountGe 2 lower bound
+  -> k + m <= sumS
+```
+
+Concrete next candidates:
+
+```lean
+theorem rawHeightLabel_two_le_iff_mod_four
+theorem orbitWindowHeight_two_le_iff_mod_four
+theorem orbitWindowHeightCountGe_two_eq_residueCount
+```
+
+The exact theorem names and statement shape should be adjusted after checking
+the existing `V2`, `Shift`, and modular arithmetic API.
````
`````
