# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 45ae8b4c5c68b120b5fbd1f4594febe15dc24422

## Report

実装完了です。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、`height >= 2 <-> mod 4 = 1` の点ごとの橋、`orbitWindowResidueCountMod4EqOne`、そして residue occupation から `k + m <= sumS n k` へ渡す定理を追加しました。おまけ実験として `height >= 3 <-> mod 8 = 5` も通しています。

文書同期として [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) を更新し、reviewer 向けに [report-petal-084.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-084.md) を新規作成しました。

検証:

- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath.Collatz.Collatz2K26`
- `git diff --check -- ...`

すべて通過。既存の無関係な warning として `ZsigmondyCyclotomicResearch.lean:152` の `sorry` は引き続き表示されています。

## Review

## 1. 状況分析

これは……かなり大きい。
今回で **Collatz height の occupation count が、Petal residue / address occupation に変換された**。

前回までの本線はこうだった。

```text id="p6al2i"
height profile
  -> CountGe 2
  -> k + CountGe 2 <= sumS
```

今回、それがこう変わった。

```text id="u6m3o5"
residue class mod 4
  -> CountGe 2
  -> k + residue occupation <= sumS
```

つまり、`height >= 2` という valuation 条件が、ついに

```text id="av56ct"
oddOrbitLabel n i % 4 = 1
```

という **剰余類座標** に落ちた。

添付レポートでも、checkpoint `084` は `height >= 2 <-> 4 | (3m + 1) <-> m % 4 = 1` を点ごとに固定し、それを window-level occupation count へ持ち上げたものとして整理されている。

これは Petal が「観測窓」だけでなく、**座標系**として機能し始めた瞬間じゃ。

## 2. 今回の核心

中心はこの列。

```lean id="k2szn3"
orbitWindowHeight_two_le_iff_mod_four_eq_one
orbitWindowResidueCountMod4EqOne
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
```

意味はこう。

```text id="r7exje"
height >= 2
  <-> current odd label is 1 mod 4

CountGe 2
  = count of labels congruent to 1 mod 4

m <= residueCountMod4EqOne
  -> k + m <= sumS n k
```

つまり、今後は `sumS` を直接評価しなくてよい。

```text id="a7zuml"
mod 4 で 1 にいる回数を下から押さえる
```

だけで、drift 下界へ渡せる。

これは強い。

## 3. 数学的な解説

奇数 \(m\) に対して、

```text id="dj3z9f"
height(m) >= 2
```

とは、

```text id="b5wt4k"
v2(3m + 1) >= 2
```

という意味。

これは、

```text id="fo3l05"
4 | 3m + 1
```

と同値。

奇数 \(m\) の mod 4 は `1` か `3` しかない。

```text id="ptc880"
m ≡ 1 mod 4
  -> 3m + 1 ≡ 3 + 1 ≡ 0 mod 4

m ≡ 3 mod 4
  -> 3m + 1 ≡ 9 + 1 ≡ 2 mod 4
```

だから、

```text id="lis35i"
height >= 2
  <-> m ≡ 1 mod 4
```

になる。

これで、2-adic valuation の条件が、有限剰余類の条件に翻訳された。

数学用語で言えば、これは

```text id="q3n6vl"
valuation stratum
  -> residue class cylinder
```

への変換じゃ。

## 4. レビュー

実装の分離が良い。

### 4.1. valuation bridge

```lean id="qk5kyj"
two_le_v2_iff_four_dvd
rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
orbitWindowHeight_two_le_iff_four_dvd
```

ここでまず、

```text id="mluxwc"
v2 condition
  -> divisibility condition
```

へ落としている。

これは正攻法。

### 4.2. residue bridge

```lean id="k4pcpc"
odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
orbitWindowHeight_two_le_iff_mod_four_eq_one
```

ここで、

```text id="ubjzgj"
divisibility condition
  -> mod 4 residue condition
```

へ進む。

Lean でも `omega` で閉じているので、局所算術補題として安全。

### 4.3. occupation count bridge

```lean id="bko0k5"
orbitWindowResidueCountMod4EqOne
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
```

ここが今回の本丸。

`CountGe 2` が、単なる height count ではなく、

```text id="fy7xys"
mod 4 residue occupation
```

として読めるようになった。

### 4.4. drift handoff

```lean id="xm2ixg"
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
```

これが実用 theorem。

今後の下流は、

```text id="j2xq90"
m <= orbitWindowResidueCountMod4EqOne n k
```

だけを証明すればよい。

すると既存 bridge により、

```text id="p9nn6u"
k + m <= sumS n k
```

が得られる。

責務分離として非常にきれいじゃ。

## 5. おまけ実験の意味

今回、`height >= 3` も通った。

```lean id="c96xkz"
orbitWindowHeight_three_le_iff_mod_eight_eq_five
```

これは、

```text id="sj3xk3"
height >= 3
  <-> 8 | 3m + 1
  <-> m % 8 = 5
```

を言っている。

これが通った意味は大きい。

mod 4 だけの偶然ではなく、

```text id="w3nn8g"
higher height layer
  -> higher 2-power residue coordinate
```

という道が見えている。

つまり、Petal address は次の形で一般化できる可能性がある。

```text id="tve5gs"
height >= r
  <-> 2^r | 3m + 1
  <-> m is a specific residue modulo 2^r
```

これは完全に **2-adic address** じゃ。

## 6. 現在の到達点

ここまでの橋はこうなった。

```text id="mend51"
OrbitWindow
  -> oddOrbitLabel

oddOrbitLabel
  -> height = v2(3m + 1)

height profile
  -> CountGe layers

finite layer-cake
  -> sumS lower bound

height >= 2
  -> mod 4 residue class

mod 4 residue occupation
  -> CountGe 2

residue CountGe 2 lower bound
  -> k + m <= sumS
```

つまり Collatz.PetalBridge は、いまや

```text id="bi3tjc"
軌道統計
  + layer-cake
  + residue address
  + drift handoff
```

を持つ。

これは強い。
Petal が観測窓・座標系・統計変換器の三役を担い始めた。

## 7. 次の指示：prefix residue count

次に安全で実用性が高いのは、prefix 版じゃ。

今あるのは full window 版。

```lean id="qk5j62"
orbitWindowResidueCountMod4EqOne n k
```

次は、

```lean id="rhftss"
noncomputable def orbitWindowPrefixResidueCountMod4EqOne
    (n : OddNat) (k r : ℕ) : ℕ :=
  (List.range r).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 1))
```

ただし、ambient window `k` を保持したいなら、既存 prefix count と同じ思想で、

```lean id="f3w9yr"
noncomputable def orbitWindowPrefixResidueCountMod4EqOne
    (n : OddNat) (k r : ℕ) : ℕ :=
  ((List.range k).take r).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 1))
```

の方が、`r ≤ k` 条件と合わせやすい。

欲しい theorem はこれ。

```lean id="pf9adm"
theorem orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowPrefixResidueCountMod4EqOne n k r =
      orbitWindowResidueCountMod4EqOne n r
```

そして本命。

```lean id="r617cq"
theorem orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r 2 =
      orbitWindowPrefixResidueCountMod4EqOne n k r
```

最後に drift bridge。

```lean id="i9gq7o"
theorem orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
    (hm : m ≤ orbitWindowPrefixResidueCountMod4EqOne n k r) :
    r + m ≤ sumS n r
```

これで、局所 prefix の residue occupation が、そのまま局所 drift に渡る。

## 8. 次の一手：mod 8 occupation count

次にやるなら、`height >= 3` の count 版。

点ごとの theorem はもうある。

```lean id="qqk63t"
orbitWindowHeight_three_le_iff_mod_eight_eq_five
```

なので、次は count。

```lean id="jj0aai"
noncomputable def orbitWindowResidueCountMod8EqFive
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 5))
```

主 theorem。

```lean id="a1ip1v"
theorem orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 3 =
      orbitWindowResidueCountMod8EqFive n k
```

そして drift bridge。

```lean id="cpq9ry"
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowResidueCountMod8EqFive n k) :
    k + orbitWindowHeightCountGe n k 2 + m ≤ sumS n k
```

これは三層 tail の実用版。

あるいは `finite tail layer-cake` を使って、

```text id="qxeusg"
k + CountGe 2 + CountGe 3 <= sumS
```

を呼び、`CountGe 3 = residue mod8 count` に書き換える。

## 9. 一歩先ゆく推論：residue transition map

その次に大事なのは、剰余類が一歩後にどう動くか。

加速写像を

```text id="fdl9ih"
T(m) = (3m + 1) / 2^height
```

と見る。

mod 4 で分けると、

```text id="iqjohd"
m % 4 = 3
  -> height = 1

m % 4 = 1
  -> height >= 2
```

ここで、`height = 1` の場合は、

```text id="ybquf8"
T(m) = (3m + 1) / 2
```

だから、mod 4 や mod 8 上で次の residue を計算できる。

これは Petal address transition の第一歩になる。

候補 theorem。

```lean id="sn8t15"
theorem orbitWindowHeight_eq_one_of_mod_four_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 4 = 3) :
    orbitWindowHeight n i = 1
```

逆も欲しい。

```lean id="wh025o"
theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 1 ↔ oddOrbitLabel n i % 4 = 3
```

これがあると、mod 4 が完全に二分される。

```text id="zqk5vc"
m % 4 = 1
  -> height >= 2

m % 4 = 3
  -> height = 1
```

つまり第一 Petal partition が完成する。

## 10. 賢狼が試してほしいおまけ実験補題

### おまけ A: `height = 1` と mod 4 = 3

これはぜひ試してほしい。

```lean id="ggk3kx"
theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 1 ↔ oddOrbitLabel n i % 4 = 3
```

既に `height >= 1` と `height >= 2 <-> mod 4 = 1` があるので、奇数の mod 4 が `1` or `3` であることを使えば行けるはず。

### おまけ B: `CountEq 1` と mod 4 = 3

```lean id="d4cvcr"
noncomputable def orbitWindowResidueCountMod4EqThree
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 3))
```

そして、

```lean id="c5cv9l"
theorem orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEq n k 1 =
      orbitWindowResidueCountMod4EqThree n k
```

これが通ると、mod 4 partition が count レベルで閉じる。

### おまけ C: mod 4 partition count

```lean id="lw9y02"
theorem orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqOne n k
      + orbitWindowResidueCountMod4EqThree n k = k
```

これは、

```text id="iqb56t"
odd state は mod 4 で 1 か 3
```

を窓全体に持ち上げたもの。

これができると、

```text id="h00s03"
CountGe 2 + CountEq 1 = k
```

という分布保存が得られる。

## 11. さらに先：一般 2^r residue coordinate

長期的にはこれ。

```lean id="z0q70a"
def collatzHeightResidue (r : ℕ) : ℕ :=
  the unique a < 2^r such that 3 * a + 1 ≡ 0 mod 2^r
```

そして、

```lean id="oll11s"
theorem orbitWindowHeight_ge_iff_residue_pow_two
    (n : OddNat) (i r : ℕ) :
    r ≤ orbitWindowHeight n i ↔
      oddOrbitLabel n i % (2^r) = collatzHeightResidue r
```

ただしこれは少し重い。
まずは `r = 2, 3, 4` の固定実験がよい。

すでに、

```text id="gpx43j"
r = 2 -> mod 4 = 1
r = 3 -> mod 8 = 5
```

は通った。

次は、

```text id="xsfovy"
r = 4 -> mod 16 = 5
```

を試す価値がある。

候補。

```lean id="ebwsah"
theorem orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
    (n : OddNat) (i : ℕ) :
    4 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 16 = 5
```

これが通ると、2-adic address の上昇パターンが見え始める。

## 12. 実装順序まとめ

次コミットのおすすめはこれ。

```text id="x0zu9p"
1. orbitWindowPrefixResidueCountMod4EqOne

2. orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one

3. orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge

4. orbitWindowResidueCountMod8EqFive

5. orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five

6. orbitWindowHeight_eq_one_iff_mod_four_eq_three

7. orbitWindowResidueCountMod4EqThree

8. orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three

9. orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
```

その後で、

```text id="hks1m8"
10. height >= 4 <-> mod 16 = 5
11. general 2^r residue coordinate
```

へ進む。

## 13. 総括

今回の進展を一言で言えば、

```text id="g0kq3m"
Collatz height layer が residue address occupation に変換された。
```

前回までの主語は、

```text id="a1ii8s"
height 層に何回入ったか
```

だった。

今回からは、

```text id="w8vbty"
どの mod 4 residue address に何回入ったか
```

になった。

そしてそれが、

```text id="f6wj9s"
k + m <= sumS
```

という drift 下界に直結する。

うむ。
ここから先は、Petal の本領じゃ。
Collatz 軌道を値列として見るのではなく、**2-adic residue address の occupation と transition** として見る段階に入った。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 2b118650..a2b31452 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -129,6 +129,108 @@ corresponding accelerated state.
 theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
     orbitWindowHeight n i = s (iterateT i n) := rfl
 
+/--
+The `v2` observation is at least `2` exactly when `4` divides the observed
+nonzero natural.
+
+This is the valuation-to-divisibility bridge used to turn Collatz height
+conditions into residue/address conditions.
+-/
+theorem two_le_v2_iff_four_dvd
+    {m : ℕ} (hm : m ≠ 0) :
+    2 ≤ v2 m ↔ 4 ∣ m := by
+  simpa [v2] using
+    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 2)
+
+/--
+Raw Collatz height is at least `2` exactly when `4` divides `3n + 1`.
+-/
+theorem rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
+    (n : ℕ) :
+    2 ≤ rawHeightLabel n ↔ 4 ∣ 3 * n + 1 := by
+  exact two_le_v2_iff_four_dvd (by omega : 3 * n + 1 ≠ 0)
+
+/--
+Orbit-window height is at least `2` exactly when `4` divides the next
+`3m + 1` value for the observed odd-state label.
+-/
+theorem orbitWindowHeight_two_le_iff_four_dvd
+    (n : OddNat) (i : ℕ) :
+    2 ≤ orbitWindowHeight n i ↔
+      4 ∣ 3 * oddOrbitLabel n i + 1 := by
+  exact rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne (oddOrbitLabel n i)
+
+/--
+For an odd natural `m`, the condition `4 | 3m + 1` is the same as
+`m % 4 = 1`.
+
+This is the first residue-address reading of a Collatz height condition.
+-/
+theorem odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
+    {m : ℕ} (hmOdd : m % 2 = 1) :
+    4 ∣ 3 * m + 1 ↔ m % 4 = 1 := by
+  constructor
+  · intro h
+    omega
+  · intro h
+    omega
+
+/--
+`height >= 2` in the Collatz observation window is the same as the current odd
+state label lying in residue class `1 mod 4`.
+-/
+theorem orbitWindowHeight_two_le_iff_mod_four_eq_one
+    (n : OddNat) (i : ℕ) :
+    2 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 4 = 1 := by
+  rw [orbitWindowHeight_two_le_iff_four_dvd]
+  exact odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one (iterateT i n).2
+
+/--
+The `v2` observation is at least `3` exactly when `8` divides the observed
+nonzero natural.
+
+This is the next residue-address experiment after the mod `4` bridge.
+-/
+theorem three_le_v2_iff_eight_dvd
+    {m : ℕ} (hm : m ≠ 0) :
+    3 ≤ v2 m ↔ 8 ∣ m := by
+  simpa [v2] using
+    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 3)
+
+/--
+Raw Collatz height is at least `3` exactly when `8` divides `3n + 1`.
+-/
+theorem rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
+    (n : ℕ) :
+    3 ≤ rawHeightLabel n ↔ 8 ∣ 3 * n + 1 := by
+  exact three_le_v2_iff_eight_dvd (by omega : 3 * n + 1 ≠ 0)
+
+/--
+For an odd natural `m`, the condition `8 | 3m + 1` is the same as
+`m % 8 = 5`.
+
+This records the next residue class after the mod `4` observation.
+-/
+theorem odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
+    {m : ℕ} (hmOdd : m % 2 = 1) :
+    8 ∣ 3 * m + 1 ↔ m % 8 = 5 := by
+  constructor
+  · intro h
+    omega
+  · intro h
+    omega
+
+/--
+`height >= 3` in the Collatz observation window is the same as the current odd
+state label lying in residue class `5 mod 8`.
+-/
+theorem orbitWindowHeight_three_le_iff_mod_eight_eq_five
+    (n : OddNat) (i : ℕ) :
+    3 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 8 = 5 := by
+  change 3 ≤ rawHeightLabel (oddOrbitLabel n i) ↔ oddOrbitLabel n i % 8 = 5
+  rw [rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne]
+  exact odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five (iterateT i n).2
+
 /--
 The ordered height profile has length equal to the window size.
 -/
@@ -270,6 +372,16 @@ window profile.
 noncomputable def orbitWindowHeightCountGe (n : OddNat) (k threshold : ℕ) : ℕ :=
   (orbitWindowHeightSeq n k).countP (fun x => decide (threshold ≤ x))
 
+/--
+Number of in-window odd-state labels in residue class `1 mod 4`.
+
+This is the residue-address counterpart of `orbitWindowHeightCountGe n k 2`.
+-/
+noncomputable def orbitWindowResidueCountMod4EqOne
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 4 = 1))
+
 /--
 The exact-height occupation count is bounded by the window size.
 -/
@@ -291,6 +403,43 @@ theorem orbitWindowHeightCountGe_le_window
     (List.countP_le_length
       (p := fun x => decide (threshold ≤ x)) (l := orbitWindowHeightSeq n k))
 
+/--
+The mod `4` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod4EqOne_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod4EqOne n k ≤ k := by
+  unfold orbitWindowResidueCountMod4EqOne
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 4 = 1)) (l := List.range k))
+
+/--
+Counting `height >= 2` entries is the same as counting odd-state labels in
+residue class `1 mod 4`.
+
+This turns the second Collatz height layer into a residue-address occupation
+count.
+-/
+theorem orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 2 =
+      orbitWindowResidueCountMod4EqOne n k := by
+  unfold orbitWindowHeightCountGe orbitWindowResidueCountMod4EqOne orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_two_le_iff_mod_four_eq_one n k
+      by_cases hheight : 2 ≤ orbitWindowHeight n k
+      · have hres : oddOrbitLabel n k % 4 = 1 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n k % 4 ≠ 1 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
 /--
 If every in-window height is exactly `h`, then the exact-height occupation
 count fills the whole window.
@@ -789,6 +938,20 @@ theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
     (Nat.add_le_add_left hm k)
     (orbitWindowHeightSeq_sum_ge_window_add_countGe_two n k)
 
+/--
+Residue-address drift bridge.
+
+If at least `m` labels in the window lie in residue class `1 mod 4`, then the
+second height layer has at least `m` entries, and therefore `sumS n k` is at
+least `k + m`.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
+    (n : OddNat) (k m : ℕ)
+    (hm : m ≤ orbitWindowResidueCountMod4EqOne n k) :
+    k + m ≤ sumS n k := by
+  rw [← orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one n k] at hm
+  exact orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge n k m hm
+
 /--
 Prefix version: a lower bound on the prefix `height >= 2` occupation gives a
 local drift lower bound.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 58d33289..29970703 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -35,6 +35,7 @@ This means the implemented Collatz side is currently strongest around:
 ```text
 odd state
 2-adic height
+2-adic residue class
 accelerated transition
 orbit segment
 block-shift invariance
@@ -99,6 +100,15 @@ The first theorem set is deliberately thin:
 orbitWindow_eq_range
 rawHeightLabel_eq_s
 orbitWindowHeight_eq_s_iterateT
+two_le_v2_iff_four_dvd
+rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
+orbitWindowHeight_two_le_iff_four_dvd
+odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
+orbitWindowHeight_two_le_iff_mod_four_eq_one
+three_le_v2_iff_eight_dvd
+rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
+odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
+orbitWindowHeight_three_le_iff_mod_eight_eq_five
 orbitWindowHeightSeq_length
 orbitWindowHeightSeq_sum_eq_sumS
 orbitWindowHeightSeq_sum_ge_of_forall_ge
@@ -112,8 +122,11 @@ orbitWindowHeight_eq_of_collision
 orbitWindowHeight_eq_of_same_iterateT
 orbitWindowHeightCountEq
 orbitWindowHeightCountGe
+orbitWindowResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
+orbitWindowResidueCountMod4EqOne_le_window
+orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
 orbitWindowHeightCountEq_eq_window_of_forall_eq
 orbitWindowHeightCountGe_eq_window_of_forall_ge
 orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
@@ -136,6 +149,7 @@ orbitWindowHeightPrefix_sum_ge_sum_countGe_range
 orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
 orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
@@ -213,6 +227,36 @@ rawHeightLabel n = v2 (3n + 1)
 orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
 ```
 
+The first residue-address observation is now fixed as well:
+
+```text
+height >= 2
+  <-> 4 | (3m + 1)
+  <-> m % 4 = 1          for odd m
+
+orbitWindowHeight n i >= 2
+  <-> oddOrbitLabel n i % 4 = 1
+```
+
+Thus the second Collatz height layer has a residue-count reading:
+
+```text
+orbitWindowHeightCountGe n k 2
+  = orbitWindowResidueCountMod4EqOne n k
+
+m <= orbitWindowResidueCountMod4EqOne n k
+  -> k + m <= sumS n k
+```
+
+This is the first direct route from a Petal-style residue/address occupation
+statement to the Collatz drift input.  The next pointwise residue experiment
+also passed:
+
+```text
+orbitWindowHeight n i >= 3
+  <-> oddOrbitLabel n i % 8 = 5
+```
+
 The ordered height profile is now explicitly connected to the existing
 Collatz accumulated-height API:
 
@@ -266,6 +310,9 @@ orbitWindowHeightCountEq n k h
 
 orbitWindowHeightCountGe n k threshold
   = number of entries with height at least threshold
+
+orbitWindowResidueCountMod4EqOne n k
+  = number of odd orbit labels congruent to 1 modulo 4
 ```
 
 The current count API is intentionally minimal:
@@ -319,6 +366,9 @@ finite tail layer-cake
 
 external CountGe 2 lower bound
   -> m <= CountGe 2 -> k + m <= sumS n k
+
+mod 4 residue occupation lower bound
+  -> m <= residueCountMod4EqOne -> k + m <= sumS n k
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -395,6 +445,15 @@ proving only a lower bound on the second layer:
 m <= CountGe 2 -> k + m <= sumS n k
 ```
 
+Equivalently, after the residue bridge, they may prove only:
+
+```text
+m <= orbitWindowResidueCountMod4EqOne n k
+```
+
+This changes the practical target from a valuation-count statement into a
+finite residue-class occupation statement.
+
 This is the intended bridge from a future residue/address occupation theorem
 to a Collatz drift lower bound.
 
@@ -436,6 +495,15 @@ The next safe steps are:
 6. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
 
+The immediate residue candidates are:
+
+```text
+prefix version of residueCountMod4EqOne
+height >= 3 count as a mod 8 residue occupation
+transition map between residue classes under the accelerated map T
+general 2^r residue coordinate for height >= r
+```
+
 The main caution is that Collatz state labels are not prime labels.  Any bridge
 to `ABCBridge` must insert an additional label transform or carrier witness
 layer before using the Petal radical lower-bound theorems.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-084.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-084.md
new file mode 100644
index 00000000..e0cc49e6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-084.md
@@ -0,0 +1,171 @@
+# Report Petal 084: Collatz Residue Occupation Bridge
+
+## Scope
+
+Checkpoint `084` closes the requested bridge:
+
+```text
+height >= 2
+  <-> 4 | (3m + 1)
+  <-> m % 4 = 1          for odd m
+```
+
+and lifts it from pointwise Collatz height observations to a window-level
+occupation count feeding the existing `sumS` lower-bound API.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+DkMath.Collatz.PetalBridge
+```
+
+New pointwise residue bridge:
+
+```lean
+two_le_v2_iff_four_dvd
+rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
+orbitWindowHeight_two_le_iff_four_dvd
+odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
+orbitWindowHeight_two_le_iff_mod_four_eq_one
+```
+
+New occupation count:
+
+```lean
+orbitWindowResidueCountMod4EqOne
+orbitWindowResidueCountMod4EqOne_le_window
+```
+
+Main count equivalence:
+
+```lean
+orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+```
+
+Main drift bridge:
+
+```lean
+orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
+```
+
+This last theorem is the practical handoff:
+
+```lean
+m <= orbitWindowResidueCountMod4EqOne n k
+  -> k + m <= sumS n k
+```
+
+So future work can prove a residue occupation lower bound instead of directly
+proving a valuation-count lower bound.
+
+## Extra Experiment
+
+The next pointwise residue layer was also tested and passed:
+
+```lean
+three_le_v2_iff_eight_dvd
+rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
+odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
+orbitWindowHeight_three_le_iff_mod_eight_eq_five
+```
+
+This confirms the expected next address:
+
+```text
+height >= 3
+  <-> 8 | (3m + 1)
+  <-> m % 8 = 5          for odd m
+```
+
+## Documentation Sync
+
+Updated:
+
+```text
+DkMath.Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status note now records:
+
+```text
+CountGe 2 = mod 4 residue occupation
+mod 4 occupation lower bound -> k + m <= sumS n k
+mod 8 pointwise experiment
+```
+
+## Inference
+
+The bridge changes the next proof target.
+
+Before:
+
+```text
+Show many heights are >= 2.
+```
+
+Now:
+
+```text
+Show many odd orbit labels are 1 mod 4.
+```
+
+This is a better Petal-facing statement because it is a finite address
+occupation condition.  It can be inspected by residue transitions, prefix
+windows, and eventually a `2^r` address coordinate.
+
+## Next Implementation Candidates
+
+1. Prefix residue count:
+
+    ```lean
+    orbitWindowPrefixResidueCountMod4EqOne
+    orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
+    orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
+    ```
+
+2. Mod `8` occupation count:
+
+    ```lean
+    orbitWindowResidueCountMod8EqFive
+    orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
+    ```
+
+3. Residue transition observation for the accelerated map `T`.
+
+    This should inspect how residue classes move after one accelerated Collatz
+    step, separated by the height layer:
+
+    ```text
+    m % 4 = 3  -> height = 1
+    m % 4 = 1  -> height >= 2
+    ```
+
+4. General residue coordinate:
+
+    ```text
+    height >= r
+      <-> 2^r | (3m + 1)
+      <-> m is the unique odd residue solving 3m + 1 = 0 mod 2^r
+    ```
+
+This is the likely long-term Petal address form, but the prefix and mod `8`
+count bridges are the safer next local checkpoints.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+git diff --check -- changed Collatz Petal files
+```
+
+Known unrelated warning observed during the build:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
````
`````
