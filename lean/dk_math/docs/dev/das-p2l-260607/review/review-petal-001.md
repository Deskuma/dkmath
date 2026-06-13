# Git diff / Report / Review

## Add: review

gch: ca0c1f042c6e4d5254af9161b11fd11cb8a382fd

## Report

Petal の基礎語彙を Lean 側に固定しました。今回は `GNBridge` へ進まず、設計ノートに沿って「数え上げ・住所・境界」の最小核を追加しています。

追加:

- [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean)
  - `baseUnitCore`
  - `inheritanceSlot`
  - `lapBase`
  - `relPetalTotal`
  - `relPolygonKernel`
  - `SameRelPetalOrbit`
  - `R_5(0)=5`, `R_5(1)=30`, `R_5(2)=180`
  - `5,30,180` が同じ Petal orbit 上にある補題

- [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean)
  - `relPetalBlockSize`
  - `PetalAddress`
  - `outerPetalAddress`
  - `channel 0 = inheritance/core channel`
  - `channel 1..n = Petal channels`
  - `outerPetalAddress 5 1 25 = { lap := 1, channel := 4, offset := 5 }`
  - `outerPetalAddress 5 2 25 = { lap := 2, channel := 0, offset := 25 }`
  - offset と channel の基本境界補題

更新:

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean) に `Counting` / `Address` を追加 import

検証:

```text
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

うむ、これは良い。
今回の `d029916...` は、前回の議論をかなり素直に Lean へ落とせておる。

## 1. 何が前進したか

今回の本質はこれじゃ。

```text
Petal.GNBridge へ進む前に、
Petal の「数え上げ」と「住所」を固定した
```

つまり、Petal が単なる `S0/GN` の橋ではなく、

```text
基底単位核
継承口
周回基数
周回総数
住所
同一 orbit
```

を持つ構造として立ち始めた。

これは大事じゃ。
「相対多角数」という言葉が曖昧なまま補題を増やすと、あとで理論名と算出式が混ざる。今回それを避けて、まず **計算可能な核** を置いた。

## 2. `Counting.lean` の意味

追加された定義は、まさに議論通りじゃ。

```lean
def baseUnitCore (n : Nat) : Nat := n
def inheritanceSlot (_n : Nat) : Nat := 1
def lapBase (n : Nat) : Nat :=
  baseUnitCore n + inheritanceSlot n
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap
def relPolygonKernel (n : Nat) : Nat :=
  baseUnitCore n * lapBase n
```

ここで一番良いのは、`lapBase n = n + 1` を **計算結果** として theorem にしつつ、API 上は `lapBase` を主語にした点じゃ。

```lean
theorem lapBase_eq_succ (n : Nat) :
    lapBase n = n + 1
```

これにより、

$$
n+1
$$

をただの数値に潰さず、

$$
\text{基底単位核 }n+\text{継承口 }1
$$

として扱える。

これは設計上かなり良い。
後で `inheritanceSlot` を一般化して、

$$
n+s
$$

や、動的継承口、重み付き継承口へ拡張する余地も残っておる。

## 3. (5,30,180) の固定

この三つが Lean theorem として入った。

```lean
theorem relPetalTotal_five_zero :
    relPetalTotal 5 0 = 5

theorem relPetalTotal_five_one :
    relPetalTotal 5 1 = 30

theorem relPetalTotal_five_two :
    relPetalTotal 5 2 = 180
```

数学的には、

$$
R_5(0)=5
$$

$$
R_5(1)=5(5+1)=30
$$

$$
R_5(2)=5(5+1)^2=180
$$

が固定された。

さらに、

```lean
def SameRelPetalOrbit (n a b : Nat) : Prop :=
  ∃ i j, a = relPetalTotal n i ∧ b = relPetalTotal n j
```

により、

```lean
sameRelPetalOrbit_five_5_30
sameRelPetalOrbit_five_30_180
sameRelPetalOrbit_five_5_180
```

も入った。

これは前に話していた

```text
5, 30, 180 は絶対値としては違うが、
同じ基底単位核 5 の周回軌道上では同一視できる
```

を Lean 上の predicate として固定した、ということじゃ。

## 4. `Address.lean` の意味

こちらはさらに重要じゃ。

```lean
structure PetalAddress where
  lap : Nat
  channel : Nat
  offset : Nat
```

そして規約が明記された。

```text
channel 0 = inheritance/core channel
channel 1..n = Petal channels
offset は 1-based
```

この規約を Lean ファイルのコメントに入れたのは偉い。
ここをコメントで済ませず theorem へ育てられるようにしたのがよい。

外側 address は、

```lean
def outerPetalAddress (n lap m : Nat) : PetalAddress :=
  let b := relPetalBlockSize n lap
  { lap := lap
    channel := (m - 1) / b
    offset := (m - 1) % b + 1 }
```

つまり、(m) は 1-based 位置として読み、

$$
channel=\left\lfloor\frac{m-1}{B}\right\rfloor
$$

$$
offset=(m-1)\bmod B+1
$$

じゃ。

これは前回の設計そのものじゃな。

## 5. 例の検証は正しく固定された

今回、議論していた二つの例が Lean theorem になった。

```lean
outerPetalAddress 5 1 25
  = { lap := 1, channel := 4, offset := 5 }
```

```lean
outerPetalAddress 5 2 25
  = { lap := 2, channel := 0, offset := 25 }
```

これはかなり大きい。

特に二つ目、

```text
channel 0 = inheritance/core channel
offset 25
```

が入ったことで、お主の読みである

```text
25 は 2 周目から見ると継承口側にあり、
内側の単位核方向へ降りる
```

が形式化された。

この `channel 0` 規約は、今後の nested address へつながる。

## 6. 境界補題も良い

今回、単なる具体例だけでなく、一般補題も入っておる。

```lean
outerPetalAddress_offset_pos
outerPetalAddress_offset_le_blockSize
outerPetalAddress_channel_lt_lapBase
```

特に、

```lean
theorem outerPetalAddress_channel_lt_lapBase
```

は重要じゃ。

これは条件

```lean
0 < lap
1 ≤ m
m ≤ relPetalTotal n lap
```

のもとで、

```lean
channel < lapBase n
```

を示す。

つまり address の channel は、ちゃんと

$$
0,\ldots,lapBase(n)-1
$$

に収まる。

`lapBase n = n+1` なので、

$$
0,\ldots,n
$$

じゃ。
これにより、

```text
0 = inheritance/core
1..n = Petal
```

の有限 channel 空間が Lean 上で保証された。

## 7. 今回まだ入っていないもの

ここはやわらかく確認じゃ。

今回入ったのは **固定単位核の Counting / Address** じゃ。
まだ次は入っていない。

```text
dynamicOrbitTotal
dynamicPetalTotal
factorial orbit
primorial orbit
NestedPetalAddress
channel 0 を再帰的に降りる関数
```

つまり、前回話した

```text
固定単位核から動的単位核へ
階乗・プリモリアルへ
```

は次フェーズじゃな。

今回の差分は、その前段として十分よい。

## 8. 次に自然な補題

次に入れるなら、わっちはこの順を推す。

### A. channel 0 判定補題

```lean
theorem outerPetalAddress_channel_eq_zero_iff_lt_blockSize
```

意味は、

$$
channel=0
$$

なら、値が外側 block の最初にあるということ。

1-based なら概ね、

$$
m \le B
$$

と同値にできるはずじゃ。

これは `R(5,2,25)` の「単位核内」読みを一般化する。

### B. channel positive は Petal channel

```lean
def IsInheritanceChannel (A : PetalAddress) : Prop :=
  A.channel = 0

def IsPetalChannel (A : PetalAddress) : Prop :=
  0 < A.channel
```

あるいは `channel ≤ n` の補題と合わせて、

```lean
1 ≤ channel ∧ channel ≤ n
```

を Petal channel とする。

### C. nested address

外側から再帰的に address を取る。

```text
nestedAddress n lap m
```

例えば、

```text
nestedAddress 5 2 25
  = [
      { lap := 2, channel := 0, offset := 25 },
      { lap := 1, channel := 4, offset := 5 }
    ]
```

ただし Lean では最初から List にすると証明が重くなるので、まずは theorem 例だけでも良い。

## 9. 動的単位核への橋

`Counting.lean` の次の拡張はこれじゃ。

```lean
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b

def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * Finset.prod (Finset.range k) (fun i => a i + 1)
```

そして固定核との接続。

```lean
theorem dynamicPetalTotal_const :
    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k
```

ここが通れば、

```text
固定単位核 Petal は、動的単位核 Petal の特殊ケース
```

が Lean で固定される。

さらに、

```lean
theorem dynamicOrbitTotal_succ_eq_factorial :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

へ進める。

プリモリアルはその後じゃな。

## 10. 総括

今回の実装は、かなり良い。

```text
Petal.Counting:
  基底単位核・継承口・周回基数・周回総数を固定

Petal.Address:
  channel 0 = inheritance/core
  channel 1..n = Petal
  offset 1-based
  25 の具体例を Lean で検証

SameRelPetalOrbit:
  5, 30, 180 を同じ周回 orbit として同一視
```

これで「相対多角数」という曖昧な理論名の下に、まず

```text
何を数えるのか
どこに位置するのか
同じ orbit とは何か
```

が固定された。

賢狼の判定としては、

```text
Petal 基礎語彙 Phase 1 完了
次は channel 0 / nested address / dynamic orbit
```

じゃな。

これは良いぞ、D.。
花びらの数え方が決まった。数え方が決まれば、次に風が吹いたとき、どの花びらが揺れたかをちゃんと追える。こういう地味な土台ほど、あとで証明の牙になるのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 506aa272..f3c3655e 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -5,6 +5,8 @@ Authors: D. and Wise Wolf.
 -/

 import DkMath.Petal.Basic
+import DkMath.Petal.Counting
+import DkMath.Petal.Address
 import DkMath.Petal.Forms
 import DkMath.Petal.RelPolygon
 import DkMath.Petal.CoreUnit
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
new file mode 100644
index 00000000..0150881c
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -0,0 +1,119 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.Counting
+
+#print "file: DkMath.Petal.Address"
+
+/-!
+# Petal Addressing
+
+This file fixes the first outer address convention for relative Petal systems.
+
+The address is one-step and outermost.  The channel is internally zero-based:
+
+* channel `0` is the inheritance/core channel;
+* channels `1..n` are Petal channels.
+
+The value `m` is read as a one-based position inside the current lap total.
+-/
+
+namespace DkMath
+namespace Petal
+
+/-- One-step outer block size at the given lap. -/
+def relPetalBlockSize (n lap : Nat) : Nat :=
+  relPetalTotal n (lap - 1)
+
+/--
+Outer Petal address.
+
+`channel = 0` is the inheritance/core channel.  Positive channels are Petal
+channels.  `offset` is one-based inside the selected outer block.
+-/
+structure PetalAddress where
+  lap : Nat
+  channel : Nat
+  offset : Nat
+deriving Repr, DecidableEq
+
+/--
+Outer one-step address of a one-based value `m`.
+
+The correctness lemmas are intended for `0 < n`, `0 < lap`, and
+`1 <= m <= relPetalTotal n lap`.
+-/
+def outerPetalAddress (n lap m : Nat) : PetalAddress :=
+  let b := relPetalBlockSize n lap
+  { lap := lap
+    channel := (m - 1) / b
+    offset := (m - 1) % b + 1 }
+
+/-- The block size at lap zero is the base unit core. -/
+theorem relPetalBlockSize_zero (n : Nat) :
+    relPetalBlockSize n 0 = n := by
+  simp [relPetalBlockSize, relPetalTotal_zero]
+
+/-- A positive-lap block size is the previous lap total. -/
+theorem relPetalBlockSize_succ (n lap : Nat) :
+    relPetalBlockSize n (lap + 1) = relPetalTotal n lap := by
+  simp [relPetalBlockSize]
+
+/-- The pentagonal one-lap address of `25`. -/
+theorem outerPetalAddress_five_one_twentyfive :
+    outerPetalAddress 5 1 25 = { lap := 1, channel := 4, offset := 5 } := by
+  decide
+
+/--
+The pentagonal two-lap address of `25`.
+
+This lands in channel `0`, the inheritance/core channel, with offset `25`.
+-/
+theorem outerPetalAddress_five_two_twentyfive :
+    outerPetalAddress 5 2 25 = { lap := 2, channel := 0, offset := 25 } := by
+  decide
+
+/-- The address lap field is definitionally the observed lap. -/
+theorem outerPetalAddress_lap (n lap m : Nat) :
+    (outerPetalAddress n lap m).lap = lap := by
+  rfl
+
+/-- The offset of an outer address is always positive. -/
+theorem outerPetalAddress_offset_pos
+    {n lap m : Nat} :
+    0 < (outerPetalAddress n lap m).offset := by
+  simp [outerPetalAddress]
+
+/-- The offset of a valid address is bounded by the outer block size. -/
+theorem outerPetalAddress_offset_le_blockSize
+    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
+    (outerPetalAddress n lap m).offset ≤ relPetalBlockSize n lap := by
+  rw [outerPetalAddress]
+  exact Nat.succ_le_of_lt (Nat.mod_lt _ hb)
+
+/--
+The channel is bounded by the lap base when the observed value stays inside the
+current lap total.
+-/
+theorem outerPetalAddress_channel_lt_lapBase
+    {n lap m : Nat}
+    (hlap : 0 < lap)
+    (hm : 1 ≤ m)
+    (hbound : m ≤ relPetalTotal n lap) :
+    (outerPetalAddress n lap m).channel < lapBase n := by
+  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlap) with ⟨k, rfl⟩
+  have hm_pos : 0 < m := hm
+  have htotal :
+      relPetalTotal n (k + 1) = relPetalTotal n k * lapBase n :=
+    relPetalTotal_succ n k
+  have hsub_lt : m - 1 < relPetalTotal n k * lapBase n := by
+    have hlt : m - 1 < m := Nat.sub_lt hm_pos Nat.zero_lt_one
+    exact lt_of_lt_of_le hlt (by simpa [htotal] using hbound)
+  rw [outerPetalAddress, relPetalBlockSize_succ]
+  exact Nat.div_lt_of_lt_mul hsub_lt
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
new file mode 100644
index 00000000..e1f6b27e
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -0,0 +1,107 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.Basic
+
+#print "file: DkMath.Petal.Counting"
+
+/-!
+# Petal Counting
+
+This file fixes the first counting vocabulary for relative Petal systems.
+
+The arithmetic is ordinary natural-number arithmetic.  The important point is
+the naming: `n + 1` is exposed as a lap base made from a base unit core and one
+inheritance slot.
+-/
+
+namespace DkMath
+namespace Petal
+
+/-- Base unit core: the number of Petal directions. -/
+def baseUnitCore (n : Nat) : Nat := n
+
+/-- The single channel that carries the core to the next lap. -/
+def inheritanceSlot (_n : Nat) : Nat := 1
+
+/-- Lap base: Petal directions plus the inheritance slot. -/
+def lapBase (n : Nat) : Nat :=
+  baseUnitCore n + inheritanceSlot n
+
+/-- Total count after `lap` relative-Petal expansions. -/
+def relPetalTotal (n lap : Nat) : Nat :=
+  baseUnitCore n * lapBase n ^ lap
+
+/-- The one-lap relative polygon kernel. -/
+def relPolygonKernel (n : Nat) : Nat :=
+  baseUnitCore n * lapBase n
+
+/-- The lap base computes to `n + 1`, but keeps the Petal meaning in the API. -/
+theorem lapBase_eq_succ (n : Nat) :
+    lapBase n = n + 1 := by
+  rfl
+
+/-- Zero laps return the base unit core. -/
+theorem relPetalTotal_zero (n : Nat) :
+    relPetalTotal n 0 = n := by
+  simp [relPetalTotal, baseUnitCore]
+
+/-- One more lap multiplies the current total by the lap base. -/
+theorem relPetalTotal_succ (n lap : Nat) :
+    relPetalTotal n (lap + 1) = relPetalTotal n lap * lapBase n := by
+  simp [relPetalTotal, pow_succ, Nat.mul_assoc]
+
+/-- The one-lap total is the relative polygon kernel. -/
+theorem relPetalTotal_one (n : Nat) :
+    relPetalTotal n 1 = relPolygonKernel n := by
+  simp [relPetalTotal, relPolygonKernel]
+
+/-- The relative polygon kernel is the first Petal-orbit total. -/
+theorem relPolygonKernel_eq_relPetalTotal_one (n : Nat) :
+    relPolygonKernel n = relPetalTotal n 1 := by
+  exact (relPetalTotal_one n).symm
+
+/-- The fixed `n = 5` zero-lap example. -/
+theorem relPetalTotal_five_zero :
+    relPetalTotal 5 0 = 5 := by
+  decide
+
+/-- The fixed `n = 5` one-lap example. -/
+theorem relPetalTotal_five_one :
+    relPetalTotal 5 1 = 30 := by
+  decide
+
+/-- The fixed `n = 5` two-lap example. -/
+theorem relPetalTotal_five_two :
+    relPetalTotal 5 2 = 180 := by
+  decide
+
+/--
+Relative unit-core orbit equivalence.
+
+Two values are in the same fixed-core Petal orbit if both are lap totals for the
+same base unit core.
+-/
+def SameRelPetalOrbit (n a b : Nat) : Prop :=
+  ∃ i j, a = relPetalTotal n i ∧ b = relPetalTotal n j
+
+/-- The base unit and first one-lap total of the pentagonal Petal orbit agree as orbit members. -/
+theorem sameRelPetalOrbit_five_5_30 :
+    SameRelPetalOrbit 5 5 30 := by
+  refine ⟨0, 1, ?_, ?_⟩ <;> decide
+
+/-- The first and second lap totals of the pentagonal Petal orbit agree as orbit members. -/
+theorem sameRelPetalOrbit_five_30_180 :
+    SameRelPetalOrbit 5 30 180 := by
+  refine ⟨1, 2, ?_, ?_⟩ <;> decide
+
+/-- The base unit and second lap total of the pentagonal Petal orbit agree as orbit members. -/
+theorem sameRelPetalOrbit_five_5_180 :
+    SameRelPetalOrbit 5 5 180 := by
+  refine ⟨0, 2, ?_, ?_⟩ <;> decide
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/History.md b/lean/dk_math/docs/dev/das-p2l-260607/History.md
index dbdb86ec..1cc4ccc5 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/History.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/History.md
@@ -1248,3 +1248,43 @@ git diff --check
 ```

 すべて成功しています。
+
+### 2026/06/10  6:41
+
+Petal の基礎語彙を Lean 側に固定しました。今回は `GNBridge` へ進まず、設計ノートに沿って「数え上げ・住所・境界」の最小核を追加しています。
+
+追加:
+
+- [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean)
+  - `baseUnitCore`
+  - `inheritanceSlot`
+  - `lapBase`
+  - `relPetalTotal`
+  - `relPolygonKernel`
+  - `SameRelPetalOrbit`
+  - `R_5(0)=5`, `R_5(1)=30`, `R_5(2)=180`
+  - `5,30,180` が同じ Petal orbit 上にある補題
+
+- [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean)
+  - `relPetalBlockSize`
+  - `PetalAddress`
+  - `outerPetalAddress`
+  - `channel 0 = inheritance/core channel`
+  - `channel 1..n = Petal channels`
+  - `outerPetalAddress 5 1 25 = { lap := 1, channel := 4, offset := 5 }`
+  - `outerPetalAddress 5 2 25 = { lap := 2, channel := 0, offset := 25 }`
+  - offset と channel の基本境界補題
+
+更新:
+
+- [Petal.lean](/lean/dk_math/DkMath/Petal.lean) に `Counting` / `Address` を追加 import
+
+検証:
+
+```text
+lake build DkMath.Petal
+lake build DkMath
+git diff --check
+```
+
+すべて成功です。
````
`````
