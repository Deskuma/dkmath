# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 98e89af869d920e854d3c904368c1d230c10af7c

## Report

checkpoint 086 完了です。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、mod 8 の height partition を追加しました。主な追加は `height = 2 <-> mod 8 = 1`、`height = 1 <-> mod 8 = 3 or 7`、`CountEq 2 = residue mod 8 = 1`、そして mod 8 の四セル partition count です。

transition map も入りました。`mod 8 = 3` の height-one channel は `T` 後に `mod 4 = 1`、`mod 8 = 7` は `T` 後に `mod 4 = 3` へ進むことを `orbitNext_mod_four_eq_one_of_mod_eight_eq_three` / `orbitNext_mod_four_eq_three_of_mod_eight_eq_seven` として固定しました。

おまけ実験として `height >= 4 <-> mod 16 = 5` も通りました。これで `mod 4`, `mod 8`, `mod 16` の固定座標実験が揃い、次の一般 `2^r` residue coordinate へ進む根拠が増えています。

文書同期:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-086.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-086.md)

検証:

- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath.Collatz.Collatz2K26`
- `git diff --check -- ...`

すべて通過。既存の無関係な `ZsigmondyCyclotomicResearch.lean:152` の `sorry` warning は引き続き表示されています。

## Review

## 1. 状況分析

これは checkpoint `086` で、**Petal が「座標系」から「遷移系」へ入り始めた** 局面じゃ。

前回までは、

```text id="q8i4j1"
height layer
  -> residue address
  -> occupation count
  -> drift lower bound
```

だった。

今回、そこに初めて

```text id="bh76ea"
current residue address
  -> next residue address
```

が入った。

つまり、Petal はもう「どの区画に何回いたか」を数えるだけでなく、**その区画から次にどこへ動くか** を記述し始めている。添付レポートでも、checkpoint `086` は static residue occupation から transition graph へ移る段階として整理されている。

## 2. 今回の中心成果

今回の柱は三つ。

```text id="bzeqkr"
1. mod 8 height partition

2. exact height-one channel の transition map

3. height >= 4 <-> mod 16 = 5 の固定実験
```

特に重要なのは transition map。

```lean id="it43t8"
orbitNext_mod_four_eq_one_of_mod_eight_eq_three
orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
```

意味は、

```text id="jh8seb"
current label % 8 = 3
  -> height = 1
  -> next T-state % 4 = 1

current label % 8 = 7
  -> height = 1
  -> next T-state % 4 = 3
```

これは Petal residue graph の最初の有向辺じゃ。

## 3. mod 8 partition の意味

今回、mod 8 の奇数剰余類が閉じた。

```text id="q1vu4q"
1 mod 8:
  height = 2

3 mod 8:
  height = 1

5 mod 8:
  height >= 3

7 mod 8:
  height = 1
```

Lean では次が入っている。

```lean id="x0v53r"
orbitWindowHeight_eq_two_iff_mod_eight_eq_one
orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
orbitWindowResidueCountMod8_partition_eq_window
```

これは大きい。

mod 4 では、

```text id="gm8qxk"
1 mod 4:
  height >= 2

3 mod 4:
  height = 1
```

までだった。

mod 8 では、それがさらに細分化されて、

```text id="ulr1uy"
1 mod 4 = {1 mod 8, 5 mod 8}
3 mod 4 = {3 mod 8, 7 mod 8}
```

となり、`height = 2` と `height >= 3`、さらに height-one の二つの遷移 channel が分離された。

## 4. transition map の意味

今回の transition は、height-one channel に限定している。

height = 1 なら、加速写像は見える形になる。

```text id="p64xyq"
T(m) = (3m + 1) / 2
```

そこで mod 8 の二つの height-one channel を見ると、

```text id="knsafo"
m % 8 = 3
  -> T(m) % 4 = 1

m % 8 = 7
  -> T(m) % 4 = 3
```

が出る。

これは本当に Petal 的じゃ。

```text id="i9v7d2"
3 mod 8 cell:
  次に強剥離側 1 mod 4 へ送る

7 mod 8 cell:
  次も height-one 側 3 mod 4 へ残る
```

つまり、同じ exact height 1 でも、次の挙動が違う。

ここが重要じゃ。
height だけでは見えなかった遷移の差が、residue address で見える。

## 5. レビュー

今回の実装は、かなり良い方向に進んでいる。

### 良い点 1: mod 8 partition を count level まで固定した

`orbitWindowResidueCountMod8_partition_eq_window` により、mod 8 の四セルが窓全体を埋めることが証明された。

これは symbolic dynamics の partition そのものじゃ。

```text id="j7xby9"
window size k
  = Count(1 mod 8)
  + Count(3 mod 8)
  + Count(5 mod 8)
  + Count(7 mod 8)
```

これがあると、後で「どのセルが不足しているか」「どのセルが過剰か」を有限組合せで扱える。

### 良い点 2: exact height と residue が対応した

`height = 2 <-> mod 8 = 1` が入ったことで、`CountEq 2` も residue count になった。

これで、

```text id="qu3p2o"
exact height statistics
```

も residue 側へ移せる。

### 良い点 3: transition theorem が入った

`orbitNext_mod_four...` は、Petal address graph の第一歩じゃ。

ただし今の statement はまだ、

```lean id="s5vxnu"
(T (iterateT i n)).1 % 4 = ...
```

という形。

次はこれを、

```lean id="e2yrab"
oddOrbitLabel n (i + 1) % 4 = ...
```

にするのが実用面で重要じゃ。

添付レポートでも、次は `iterateT_succ_eq_T_iterateT` を足して next-label formulation にするのが自然だと整理されている。

## 6. 現在の到達点

いまの `Collatz.PetalBridge` は、こうなった。

```text id="gjd6yo"
finite orbit window
  -> height profile

height profile
  -> layer occupation

layer occupation
  -> sumS lower bound

height layer
  -> residue class

residue class
  -> occupation count

residue cell
  -> next residue cell
```

つまり、

```text id="jrunni"
観測
  -> 統計
  -> 座標
  -> 遷移
```

まで来た。

これは、Collatz 軌道を値列としてではなく、**有限 symbolic dynamics** として読み始めた、ということじゃ。

## 7. 次の指示：next-label transition を作る

次の最優先は、transition theorem を `oddOrbitLabel` の次ラベルに直すこと。

まず必要なのはこれ。

```lean id="f72doz"
theorem iterateT_succ_eq_T_iterateT
    (n : OddNat) (i : ℕ) :
    iterateT (i + 1) n = T (iterateT i n)
```

もし `iterateT` が `Nat.iterate T i n` 系なら、`rfl` や既存 simp で落ちる可能性がある。

続いて label 版。

```lean id="iob6yy"
theorem oddOrbitLabel_succ_eq_T_iterateT
    (n : OddNat) (i : ℕ) :
    oddOrbitLabel n (i + 1) = (T (iterateT i n)).1 := by
  unfold oddOrbitLabel
  rw [iterateT_succ_eq_T_iterateT]
```

これが通れば、本命。

```lean id="du8e2z"
theorem oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    oddOrbitLabel n (i + 1) % 4 = 1 := by
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  exact orbitNext_mod_four_eq_one_of_mod_eight_eq_three n i hmod
```

```lean id="ztv3ec"
theorem oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    oddOrbitLabel n (i + 1) % 4 = 3 := by
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  exact orbitNext_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
```

この形になると、Petal transition graph がそのまま軌道ラベル列に乗る。

## 8. 一歩先ゆく推論：transition count へ

next-label theorem が通ったら、次は count-level transition。

たとえば、

```text id="cu5kvi"
i < k
oddOrbitLabel n i % 8 = 3
```

なら、

```text id="mxm66a"
oddOrbitLabel n (i + 1) % 4 = 1
```

だから、prefix を一つずらせば、

```text id="qbbvcf"
mod 8 = 3 の出現回数
```

は、次の窓の

```text id="aywzru"
mod 4 = 1 の出現回数
```

の下界になりそうじゃ。

ただし index が `i+1` になるので、窓は `1..k` 側にずれる。

そのため、次に欲しい定義は **shifted prefix count** じゃ。

候補。

```lean id="mxbzop"
noncomputable def orbitWindowResidueCountMod4EqOneFrom
    (n : OddNat) (start k : ℕ) : ℕ :=
  (List.range k).countP
    (fun j => decide (oddOrbitLabel n (start + j) % 4 = 1))
```

まずは `start = 1` だけでもよい。

```lean id="d6einm"
noncomputable def orbitWindowResidueCountMod4EqOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1))
```

そして transition count。

```lean id="au29lh"
theorem residueCountMod8EqThree_le_nextResidueCountMod4EqOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k
      ≤ orbitWindowResidueCountMod4EqOneTail n k
```

これはかなり本質的。

```text id="hih9vk"
3 mod 8 channel は、次の時刻で 1 mod 4 を供給する
```

という count-level transition じゃ。

同様に、

```lean id="sfxd1c"
theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k
      ≤ orbitWindowResidueCountMod4EqThreeTail n k
```

も欲しい。

## 9. さらに先：反復的な occupation transfer

ここから見える大きな絵は、

```text id="mju6t6"
mod 8 = 3
  -> next mod 4 = 1
  -> next step has height >= 2
  -> contributes extra peeling
```

つまり、ある時刻で height-one だったとしても、次時刻で追加剥離側に送られる channel がある。

これは Collatz の drift を考える上でとても大事じゃ。

なぜなら、

```text id="pal6r3"
height = 1 が多い
```

だけでは弱いが、その中に

```text id="jk5b3y"
3 mod 8 channel が多い
```

なら、次に `height >= 2` を生む。

これは「遅延した縮小力」じゃ。

Petal 語彙で言えば、

```text id="eeot0c"
Beam が一拍遅れて戻る
```

ような構造じゃな。

## 10. 賢狼が試して欲しいおまけ実験補題

### 実験 A: tail window count

まずこれ。

```lean id="lzh4xb"
noncomputable def orbitWindowResidueCountMod4EqOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1))
```

そして、

```lean id="dl8j7c"
theorem orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k
      ≤ orbitWindowResidueCountMod4EqOneTail n k
```

期待としては、むしろ等号に近いが、まずは `≤` が安全。

ただし、各 `i` が `i+1` に単射で移ることは明らかなので、点ごとの implication から count inequality で行けるはず。

### 実験 B: next height lower bound

`mod 8 = 3` は次時刻で `mod 4 = 1` なので、次時刻の height は `>= 2`。

```lean id="e8irb3"
theorem orbitWindowNextHeight_two_le_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    2 ≤ orbitWindowHeight n (i + 1) := by
  apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n (i + 1)).mpr
  exact oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n i hmod
```

これは非常に良い補題じゃ。

意味は、

```text id="pdt0dn"
3 mod 8 にいると、次の step は追加剥離側になる
```

### 実験 C: 2-step drift

これを使うと、二歩窓でこういう補題が欲しくなる。

```lean id="xpy8ix"
theorem sumS_two_steps_ge_three_of_mod_eight_eq_three
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 8 = 3) :
    3 ≤ sumS n 2
```

理由：

```text id="v7uoxh"
current step:
  mod 8 = 3 -> height = 1

next step:
  mod 4 = 1 -> height >= 2

two steps:
  sumS >= 1 + 2 = 3
```

これは「遅延縮小」の最小実験補題じゃ。

## 11. 次の実装順序

おすすめ順はこれ。

```text id="zjkmfy"
1. iterateT_succ_eq_T_iterateT

2. oddOrbitLabel_succ_eq_T_iterateT

3. oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three

4. oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven

5. orbitWindowNextHeight_two_le_of_mod_eight_eq_three

6. orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
   または
   orbitWindowNextHeight_one_le / not two_le から exact 1

7. tail residue count definitions

8. count-level transition inequalities

9. two-step drift experiment:
   sumS_two_steps_ge_three_of_mod_eight_eq_three
```

## 12. 長期方向：一般 residue coordinate

mod 16 実験も通った。

```text id="tkhftr"
height >= 4 <-> mod 16 = 5
```

これで固定座標は、

```text id="swbf2e"
height >= 2 <-> mod 4  = 1
height >= 3 <-> mod 8  = 5
height >= 4 <-> mod 16 = 5
```

まで来た。

次の一般化は、

```text id="z1gp7l"
height >= r
  <-> 2^r | 3m + 1
  <-> m ≡ a_r mod 2^r
```

じゃ。

ただし、これは急がなくてよい。
まず transition count を一段作る方が実りが大きい。

## 13. 総括

今回の checkpoint `086` で、

```text id="bbubtg"
mod 8 partition
```

が閉じ、

```text id="hpluj2"
3 mod 8 -> next 1 mod 4
7 mod 8 -> next 3 mod 4
```

という最初の transition edge が Lean に入った。

これは、Collatz PetalBridge が

```text id="b31s6f"
static occupation
```

から

```text id="ipz8w7"
residue transition dynamics
```

へ進んだことを意味する。

うむ。
ここからは、Petal は単なる観測窓ではなく、**有限有向グラフ上の軌道解析**になる。
次は next-label theorem と count-level transition。そこが通れば、`height = 1` の中にも「次に縮小へ向かう channel」と「まだ低剥離に残る channel」があることを、Lean 上で統計化できる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 7ddacac6..70e1a039 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -193,6 +193,14 @@ theorem odd_mod_four_eq_one_or_three
     m % 4 = 1 ∨ m % 4 = 3 := by
   omega
 
+/--
+An odd natural number is in one of the four odd residue classes modulo `8`.
+-/
+theorem odd_mod_eight_eq_one_or_three_or_five_or_seven
+    {m : ℕ} (hmOdd : m % 2 = 1) :
+    m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
+  omega
+
 /--
 The `v2` observation is at least `3` exactly when `8` divides the observed
 nonzero natural.
@@ -205,6 +213,16 @@ theorem three_le_v2_iff_eight_dvd
   simpa [v2] using
     (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 3)
 
+/--
+The `v2` observation is at least `4` exactly when `16` divides the observed
+nonzero natural.
+-/
+theorem four_le_v2_iff_sixteen_dvd
+    {m : ℕ} (hm : m ≠ 0) :
+    4 ≤ v2 m ↔ 16 ∣ m := by
+  simpa [v2] using
+    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 4)
+
 /--
 Raw Collatz height is at least `3` exactly when `8` divides `3n + 1`.
 -/
@@ -213,6 +231,14 @@ theorem rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
     3 ≤ rawHeightLabel n ↔ 8 ∣ 3 * n + 1 := by
   exact three_le_v2_iff_eight_dvd (by omega : 3 * n + 1 ≠ 0)
 
+/--
+Raw Collatz height is at least `4` exactly when `16` divides `3n + 1`.
+-/
+theorem rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
+    (n : ℕ) :
+    4 ≤ rawHeightLabel n ↔ 16 ∣ 3 * n + 1 := by
+  exact four_le_v2_iff_sixteen_dvd (by omega : 3 * n + 1 ≠ 0)
+
 /--
 For an odd natural `m`, the condition `8 | 3m + 1` is the same as
 `m % 8 = 5`.
@@ -228,6 +254,19 @@ theorem odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
   · intro h
     omega
 
+/--
+For an odd natural `m`, the condition `16 | 3m + 1` is the same as
+`m % 16 = 5`.
+-/
+theorem odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
+    {m : ℕ} (hmOdd : m % 2 = 1) :
+    16 ∣ 3 * m + 1 ↔ m % 16 = 5 := by
+  constructor
+  · intro h
+    omega
+  · intro h
+    omega
+
 /--
 `height >= 3` in the Collatz observation window is the same as the current odd
 state label lying in residue class `5 mod 8`.
@@ -239,6 +278,50 @@ theorem orbitWindowHeight_three_le_iff_mod_eight_eq_five
   rw [rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne]
   exact odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five (iterateT i n).2
 
+/--
+`height >= 4` in the Collatz observation window is the same as the current odd
+state label lying in residue class `5 mod 16`.
+
+This fixed-coordinate experiment supports the later general `2^r` residue
+coordinate route.
+-/
+theorem orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
+    (n : OddNat) (i : ℕ) :
+    4 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 16 = 5 := by
+  change 4 ≤ rawHeightLabel (oddOrbitLabel n i) ↔ oddOrbitLabel n i % 16 = 5
+  rw [rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne]
+  exact odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five (iterateT i n).2
+
+/--
+If `m = 3 mod 8`, then the height-one Collatz branch sends
+`(3m + 1) / 2` to residue class `1 mod 4`.
+-/
+theorem next_mod_four_of_mod_eight_eq_three
+    {m : ℕ} (hm : m % 8 = 3) :
+    ((3 * m + 1) / 2) % 4 = 1 := by
+  omega
+
+/--
+If `m = 7 mod 8`, then the height-one Collatz branch sends
+`(3m + 1) / 2` to residue class `3 mod 4`.
+-/
+theorem next_mod_four_of_mod_eight_eq_seven
+    {m : ℕ} (hm : m % 8 = 7) :
+    ((3 * m + 1) / 2) % 4 = 3 := by
+  omega
+
+/--
+On the exact height-one channel, the accelerated Collatz map is the visible
+one-step expression `(3m + 1) / 2`.
+-/
+theorem T_val_eq_three_mul_add_one_div_two_of_s_eq_one
+    (n : OddNat) (h : s n = 1) :
+    (T n).1 = (3 * n.1 + 1) / 2 := by
+  have hv : v2 (3 * n.1 + 1) = 1 := by
+    simpa [s, threeNPlusOne] using h
+  unfold T
+  simp [threeNPlusOne, hv, pow2]
+
 /--
 The ordered height profile has length equal to the window size.
 -/
@@ -400,6 +483,26 @@ noncomputable def orbitWindowResidueCountMod4EqThree
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n i % 4 = 3))
 
+/--
+Number of in-window odd-state labels in residue class `1 mod 8`.
+
+This is the residue-address counterpart of exact height `2`.
+-/
+noncomputable def orbitWindowResidueCountMod8EqOne
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 8 = 1))
+
+/--
+Number of in-window odd-state labels in residue class `3 mod 8`.
+
+This is one of the two exact height-one transition channels.
+-/
+noncomputable def orbitWindowResidueCountMod8EqThree
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 8 = 3))
+
 /--
 Number of in-window odd-state labels in residue class `5 mod 8`.
 
@@ -410,6 +513,16 @@ noncomputable def orbitWindowResidueCountMod8EqFive
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n i % 8 = 5))
 
+/--
+Number of in-window odd-state labels in residue class `7 mod 8`.
+
+This is one of the two exact height-one transition channels.
+-/
+noncomputable def orbitWindowResidueCountMod8EqSeven
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 8 = 7))
+
 /--
 Residue count inside a prefix of an ambient observation window.
 
@@ -464,6 +577,28 @@ theorem orbitWindowResidueCountMod4EqThree_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n i % 4 = 3)) (l := List.range k))
 
+/--
+The mod `8 = 1` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod8EqOne_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqOne n k ≤ k := by
+  unfold orbitWindowResidueCountMod8EqOne
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 8 = 1)) (l := List.range k))
+
+/--
+The mod `8 = 3` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod8EqThree_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k ≤ k := by
+  unfold orbitWindowResidueCountMod8EqThree
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 8 = 3)) (l := List.range k))
+
 /--
 The mod `8` residue count is bounded by the window size.
 -/
@@ -475,6 +610,17 @@ theorem orbitWindowResidueCountMod8EqFive_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n i % 8 = 5)) (l := List.range k))
 
+/--
+The mod `8 = 7` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod8EqSeven_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k ≤ k := by
+  unfold orbitWindowResidueCountMod8EqSeven
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 8 = 7)) (l := List.range k))
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -770,6 +916,50 @@ theorem orbitWindowHeight_one_le
   simpa [s, threeNPlusOne] using
     v2_3n_plus_1_ge_1 (iterateT i n).1 (iterateT i n).2
 
+/--
+The second exact Collatz height layer is residue class `1 mod 8`.
+
+This refines `height >= 2` by excluding the `height >= 3` residue class.
+-/
+theorem orbitWindowHeight_eq_two_iff_mod_eight_eq_one
+    (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i = 2 ↔ oddOrbitLabel n i % 8 = 1 := by
+  constructor
+  · intro hheight
+    have htwo : 2 ≤ orbitWindowHeight n i := by omega
+    have hnotThree : ¬ 3 ≤ orbitWindowHeight n i := by omega
+    have hmod4 : oddOrbitLabel n i % 4 = 1 :=
+      (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mp htwo
+    have hnotFive : oddOrbitLabel n i % 8 ≠ 5 := by
+      intro hfive
+      exact hnotThree ((orbitWindowHeight_three_le_iff_mod_eight_eq_five n i).mpr hfive)
+    cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT i n).2 with
+    | inl hOne =>
+        change oddOrbitLabel n i % 8 = 1 at hOne
+        exact hOne
+    | inr hrest =>
+        cases hrest with
+        | inl hThree =>
+            change oddOrbitLabel n i % 8 = 3 at hThree
+            omega
+        | inr hrest =>
+            cases hrest with
+            | inl hFive =>
+                change oddOrbitLabel n i % 8 = 5 at hFive
+                exact (hnotFive hFive).elim
+            | inr hSeven =>
+                change oddOrbitLabel n i % 8 = 7 at hSeven
+                omega
+  · intro hmod
+    have htwo : 2 ≤ orbitWindowHeight n i := by
+      apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mpr
+      omega
+    have hnotThree : ¬ 3 ≤ orbitWindowHeight n i := by
+      intro hthree
+      have hfive := (orbitWindowHeight_three_le_iff_mod_eight_eq_five n i).mp hthree
+      omega
+    omega
+
 /--
 The first Collatz height layer is exact height `1` precisely on residue class
 `3 mod 4`.
@@ -801,6 +991,77 @@ theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
       omega
     omega
 
+/--
+Exact height `1` is the union of the two mod `8` channels `3` and `7`.
+-/
+theorem orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
+    (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i = 1 ↔
+      oddOrbitLabel n i % 8 = 3 ∨ oddOrbitLabel n i % 8 = 7 := by
+  constructor
+  · intro hheight
+    have hmod4 := (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).mp hheight
+    cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT i n).2 with
+    | inl hOne =>
+        change oddOrbitLabel n i % 8 = 1 at hOne
+        omega
+    | inr hrest =>
+        cases hrest with
+        | inl hThree =>
+            change oddOrbitLabel n i % 8 = 3 at hThree
+            exact Or.inl hThree
+        | inr hrest =>
+            cases hrest with
+            | inl hFive =>
+                change oddOrbitLabel n i % 8 = 5 at hFive
+                omega
+            | inr hSeven =>
+                change oddOrbitLabel n i % 8 = 7 at hSeven
+                exact Or.inr hSeven
+  · intro hmod
+    apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).mpr
+    cases hmod with
+    | inl hThree =>
+        omega
+    | inr hSeven =>
+        omega
+
+/--
+Orbit-level transition from the `3 mod 8` height-one channel.
+
+The current odd-state label is in residue class `3 mod 8`, so the accelerated
+next state `T` lands in residue class `1 mod 4`.
+-/
+theorem orbitNext_mod_four_eq_one_of_mod_eight_eq_three
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 3) :
+    (T (iterateT i n)).1 % 4 = 1 := by
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inl hmod)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_four_of_mod_eight_eq_three hmod
+
+/--
+Orbit-level transition from the `7 mod 8` height-one channel.
+
+The current odd-state label is in residue class `7 mod 8`, so the accelerated
+next state `T` lands in residue class `3 mod 4`.
+-/
+theorem orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 7) :
+    (T (iterateT i n)).1 % 4 = 3 := by
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_four_of_mod_eight_eq_seven hmod
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
@@ -824,6 +1085,29 @@ theorem orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
           exact hheight (hiff.mpr h)
         simp [ih, hheight, hres]
 
+/--
+Counting exact height `2` entries is the same as counting odd-state labels in
+residue class `1 mod 8`.
+-/
+theorem orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountEq n k 2 =
+      orbitWindowResidueCountMod8EqOne n k := by
+  unfold orbitWindowHeightCountEq orbitWindowResidueCountMod8EqOne orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_eq_two_iff_mod_eight_eq_one n k
+      by_cases hheight : orbitWindowHeight n k = 2
+      · have hres : oddOrbitLabel n k % 8 = 1 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n k % 8 ≠ 1 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
 /--
 The two odd residue classes modulo `4` fill the whole observation window.
 -/
@@ -847,6 +1131,44 @@ theorem orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
           simp [hThree]
           omega
 
+/--
+The four odd residue classes modulo `8` fill the whole observation window.
+-/
+theorem orbitWindowResidueCountMod8_partition_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqOne n k +
+      orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqFive n k +
+      orbitWindowResidueCountMod8EqSeven n k = k := by
+  unfold orbitWindowResidueCountMod8EqOne orbitWindowResidueCountMod8EqThree
+    orbitWindowResidueCountMod8EqFive orbitWindowResidueCountMod8EqSeven
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT k n).2 with
+      | inl hOne =>
+          change oddOrbitLabel n k % 8 = 1 at hOne
+          simp [hOne]
+          omega
+      | inr hrest =>
+          cases hrest with
+          | inl hThree =>
+              change oddOrbitLabel n k % 8 = 3 at hThree
+              simp [hThree]
+              omega
+          | inr hrest =>
+              cases hrest with
+              | inl hFive =>
+                  change oddOrbitLabel n k % 8 = 5 at hFive
+                  simp [hFive]
+                  omega
+              | inr hSeven =>
+                  change oddOrbitLabel n k % 8 = 7 at hSeven
+                  simp [hSeven]
+                  omega
+
 /--
 The `height >= 1` occupation count fills the whole observation window.
 
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 60d5252f..97563db7 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -106,10 +106,18 @@ orbitWindowHeight_two_le_iff_four_dvd
 odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
 orbitWindowHeight_two_le_iff_mod_four_eq_one
 odd_mod_four_eq_one_or_three
+odd_mod_eight_eq_one_or_three_or_five_or_seven
 three_le_v2_iff_eight_dvd
+four_le_v2_iff_sixteen_dvd
 rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
+rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
 odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
+odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
 orbitWindowHeight_three_le_iff_mod_eight_eq_five
+orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
+next_mod_four_of_mod_eight_eq_three
+next_mod_four_of_mod_eight_eq_seven
+T_val_eq_three_mul_add_one_div_two_of_s_eq_one
 orbitWindowHeightSeq_length
 orbitWindowHeightSeq_sum_eq_sumS
 orbitWindowHeightSeq_sum_ge_of_forall_ge
@@ -125,13 +133,19 @@ orbitWindowHeightCountEq
 orbitWindowHeightCountGe
 orbitWindowResidueCountMod4EqOne
 orbitWindowResidueCountMod4EqThree
+orbitWindowResidueCountMod8EqOne
+orbitWindowResidueCountMod8EqThree
 orbitWindowResidueCountMod8EqFive
+orbitWindowResidueCountMod8EqSeven
 orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
 orbitWindowResidueCountMod4EqOne_le_window
 orbitWindowResidueCountMod4EqThree_le_window
+orbitWindowResidueCountMod8EqOne_le_window
+orbitWindowResidueCountMod8EqThree_le_window
 orbitWindowResidueCountMod8EqFive_le_window
+orbitWindowResidueCountMod8EqSeven_le_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -148,9 +162,15 @@ orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
 orbitWindowHeight_one_le
 orbitWindowHeightCountGe_one_eq_window
 orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+orbitWindowHeight_eq_two_iff_mod_eight_eq_one
 orbitWindowHeight_eq_one_iff_mod_four_eq_three
+orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
+orbitNext_mod_four_eq_one_of_mod_eight_eq_three
+orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
+orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
+orbitWindowResidueCountMod8_partition_eq_window
 orbitWindowHeightPrefixCountGe_one_eq
 orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
 orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
@@ -332,9 +352,18 @@ orbitWindowResidueCountMod4EqOne n k
 orbitWindowResidueCountMod4EqThree n k
   = number of odd orbit labels congruent to 3 modulo 4
 
+orbitWindowResidueCountMod8EqOne n k
+  = number of odd orbit labels congruent to 1 modulo 8
+
+orbitWindowResidueCountMod8EqThree n k
+  = number of odd orbit labels congruent to 3 modulo 8
+
 orbitWindowResidueCountMod8EqFive n k
   = number of odd orbit labels congruent to 5 modulo 8
 
+orbitWindowResidueCountMod8EqSeven n k
+  = number of odd orbit labels congruent to 7 modulo 8
+
 orbitWindowPrefixResidueCountMod4EqOne n k r
   = number of prefix labels congruent to 1 modulo 4 inside an ambient k-window
 ```
@@ -509,6 +538,32 @@ m <= residueCountMod8EqFive
   -> k + CountGe 2 + m <= sumS n k
 ```
 
+The exact mod `8` height partition is now also visible:
+
+```text
+height = 2 <-> oddOrbitLabel % 8 = 1
+height = 1 <-> oddOrbitLabel % 8 = 3 or 7
+CountEq 2 = residue mod 8 = 1
+residueCountMod8EqOne + residueCountMod8EqThree
+  + residueCountMod8EqFive + residueCountMod8EqSeven = k
+```
+
+The first transition map is now fixed for the exact height-one channels:
+
+```text
+oddOrbitLabel % 8 = 3
+  -> (T current).val % 4 = 1
+
+oddOrbitLabel % 8 = 7
+  -> (T current).val % 4 = 3
+```
+
+The next higher-coordinate experiment also passed:
+
+```text
+height >= 4 <-> oddOrbitLabel % 16 = 5
+```
+
 This is the intended bridge from a future residue/address occupation theorem
 to a Collatz drift lower bound.
 
@@ -553,10 +608,10 @@ The next safe steps are:
 The immediate residue candidates are:
 
 ```text
-transition map between residue classes under the accelerated map T
 general 2^r residue coordinate for height >= r
 prefix mod 8 residue occupation
-fixed experiment for height >= 4 as a mod 16 residue occupation
+next-label formulation of the T transition using iterateT (i + 1)
+count-level transition statistics for mod 8 height-one channels
 ```
 
 The main caution is that Collatz state labels are not prime labels.  Any bridge
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-086.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-086.md
new file mode 100644
index 00000000..563eaf7a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-086.md
@@ -0,0 +1,211 @@
+# Report Petal 086: Mod 8 Height Partition and First Transition Map
+
+## Scope
+
+Checkpoint `086` moves from static residue occupation toward a transition
+graph.  The main target was the exact height-one channel:
+
+```text
+odd label % 8 = 3  -> next T-state % 4 = 1
+odd label % 8 = 7  -> next T-state % 4 = 3
+```
+
+The checkpoint also closes the mod `8` height partition at pointwise and count
+level.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+DkMath.Collatz.PetalBridge
+```
+
+Mod `8` partition facts:
+
+```lean
+odd_mod_eight_eq_one_or_three_or_five_or_seven
+orbitWindowHeight_eq_two_iff_mod_eight_eq_one
+orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
+```
+
+New mod `8` residue counts:
+
+```lean
+orbitWindowResidueCountMod8EqOne
+orbitWindowResidueCountMod8EqThree
+orbitWindowResidueCountMod8EqSeven
+```
+
+with window bounds:
+
+```lean
+orbitWindowResidueCountMod8EqOne_le_window
+orbitWindowResidueCountMod8EqThree_le_window
+orbitWindowResidueCountMod8EqSeven_le_window
+```
+
+Exact-height count bridge:
+
+```lean
+orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
+```
+
+Mod `8` partition count:
+
+```lean
+orbitWindowResidueCountMod8_partition_eq_window
+```
+
+## Transition Map
+
+Raw height-one branch arithmetic:
+
+```lean
+next_mod_four_of_mod_eight_eq_three
+next_mod_four_of_mod_eight_eq_seven
+```
+
+Accelerated-map value on the height-one channel:
+
+```lean
+T_val_eq_three_mul_add_one_div_two_of_s_eq_one
+```
+
+Orbit-level transition:
+
+```lean
+orbitNext_mod_four_eq_one_of_mod_eight_eq_three
+orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
+```
+
+Meaning:
+
+```text
+current odd label % 8 = 3
+  -> exact height 1
+  -> T(current).val % 4 = 1
+
+current odd label % 8 = 7
+  -> exact height 1
+  -> T(current).val % 4 = 3
+```
+
+This is the first directed edge information for the Petal residue graph.
+
+## Extra Experiment
+
+The fixed higher-coordinate experiment also passed:
+
+```lean
+four_le_v2_iff_sixteen_dvd
+rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
+odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
+orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
+```
+
+So the visible coordinate sequence now includes:
+
+```text
+height >= 2 <-> mod 4  = 1
+height >= 3 <-> mod 8  = 5
+height >= 4 <-> mod 16 = 5
+```
+
+This supports the later general `2^r` residue-coordinate route.
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
+mod 8 pointwise height partition
+mod 8 count partition
+first height-one transition edges
+mod 16 fixed-coordinate experiment
+```
+
+## Inference
+
+The residue graph now has its first directed edges:
+
+```text
+3 mod 8 -> 1 mod 4
+7 mod 8 -> 3 mod 4
+```
+
+This shows why the static occupation counts are not the endpoint.  The next
+usable layer is transition statistics: how often the orbit enters the exact
+height-one subchannels, and how those subchannels feed the next mod `4`
+occupation layer.
+
+The current theorem statements use `T (iterateT i n)` as the next state.  A
+more ergonomic next step is a next-label formulation using `iterateT (i + 1)`.
+That likely needs a small iterate identity:
+
+```lean
+iterateT_succ_eq_T_iterateT
+```
+
+## Next Implementation Candidates
+
+1. Add the iterate identity:
+
+    ```lean
+    theorem iterateT_succ_eq_T_iterateT
+        (n : OddNat) (i : ℕ) :
+        iterateT (i + 1) n = T (iterateT i n)
+    ```
+
+    Then expose label-facing transition theorems:
+
+    ```lean
+    oddOrbitLabel n i % 8 = 3
+      -> oddOrbitLabel n (i + 1) % 4 = 1
+
+    oddOrbitLabel n i % 8 = 7
+      -> oddOrbitLabel n (i + 1) % 4 = 3
+    ```
+
+2. Prefix mod `8` occupation:
+
+    ```lean
+    orbitWindowPrefixResidueCountMod8EqOne
+    orbitWindowPrefixResidueCountMod8EqThree
+    orbitWindowPrefixResidueCountMod8EqFive
+    orbitWindowPrefixResidueCountMod8EqSeven
+    ```
+
+3. Count-level transition statistics for exact height-one subchannels.
+
+4. Start a general fixed-coordinate helper for:
+
+    ```text
+    height >= r <-> odd residue solving 3m + 1 = 0 mod 2^r
+    ```
+
+but only after one more fixed experiment or after repeated duplication makes
+the abstraction pay for itself.
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
