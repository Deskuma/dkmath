# Git diff / Report / Review

## Update: Petal Address

gch: 61219731bab954c89e051e065548248fc3e1acc1

## Report

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に review 指定の次 theorem を実装しました。

追加:

```lean
theorem outerPetalRemainder_le_prevTotal_of_valid
```

valid な `m` について、remainder が前段 lap total に収まることを固定しました。nested address の次段へ渡すための名前付き補題です。

```lean
theorem outerPetalAddress_decompose
```

one-based value に対する分解式を固定しました。

```lean
m =
  (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
    + outerPetalRemainder n lap m
```

注意点として、これは `m = 0` では偽なので、定理には `1 ≤ m` を仮定に入れています。`blockSize` の正値仮定は不要でした。`blockSize = 0` でも one-based remainder の定義により分解式自体は成立します。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

## Review

うむ、これは良い更新じゃ。
今回の `612197...` で、Petal Address の **商・余り分解としての正当性** がかなり綺麗に閉じた。

## 1. 今回の核心

追加された二本は、どちらも nested address へ進むための足場じゃ。

```lean
theorem outerPetalRemainder_le_prevTotal_of_valid
```

これは、

```text
valid な m を outer address で読む
  ↓
remainder は前段 lap total の中に収まる
```

を保証する補題。

そして、

```lean
theorem outerPetalAddress_decompose
```

これは、

$$
m=
channel\cdot blockSize+remainder
$$

を固定する補題じゃ。

つまり、`outerPetalAddress` が単なる計算関数ではなく、 **one-based 商余り分解** として認証された。

## 2. `outerPetalRemainder_le_prevTotal_of_valid` の意味

この補題はかなり重要じゃ。

条件は、

```lean
0 < lap
1 ≤ m
m ≤ relPetalTotal n lap
```

結論は、

```lean
outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1)
```

つまり、現在 lap の中で正しい値 (m) を読んだとき、次に渡す remainder はちゃんと前段 lap の範囲内に収まる。

これは nested recursion に必要な「安全な入力保証」じゃ。

```text
outer lap で読む
  ↓
remainder を inner lap へ渡す
  ↓
inner lap でも valid value として扱える
```

この導線が名前付き theorem になった。

特に `relPetalBlockSize_succ` を経由して、`blockSize = previous total` へ戻しているのがよい。住所体系の意味が保たれておる。

## 3. `outerPetalAddress_decompose` は大きい

こちらは Petal Address の主定理に近い。

```lean
theorem outerPetalAddress_decompose
    {n lap m : Nat}
    (hm : 1 ≤ m) :
    m =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + outerPetalRemainder n lap m
```

数学的には、内部で

$$
m-1=qB+r
$$

を使い、one-based に戻して

$$
m=qB+(r+1)
$$

としている。

ここで、

$$
q=(m-1)/B
$$

$$
r=(m-1)\bmod B
$$

なので、

$$
channel=q,\qquad remainder=r+1
$$

じゃ。

これにより、

```text
m = channel * blockSize + remainder
```

が Lean に固定された。

これは美しい。
Petal Address は、ついに **住所分解式** を持ったわけじゃ。

## 4. `m = 0` を除外した判断は正しい

報告にある通り、この定理は `m = 0` では偽じゃ。

実際、one-based remainder は常に正なので、

```lean
outerPetalRemainder_pos
```

がある。
したがって (m=0) で

$$
0=channel\cdot B+remainder
$$

は成立しない。

だから仮定

```lean
(hm : 1 ≤ m)
```

を入れたのは正しい。

一方、`blockSize` の正値仮定が不要だったのも良い発見じゃ。
`Nat` では divisor (0) でも `mod` / `div` が定義されており、ここでは one-based への戻しで分解式自体が保たれる。実用 theorem としては `blockSize > 0` なしの方が使いやすい。

## 5. Address の意味論がほぼ完成形に近づいた

ここまでの Petal Address は、次の四層を持つことになった。

```text
算出:
  channel = (m - 1) / blockSize
  remainder = (m - 1) % blockSize + 1

分類:
  channel = 0 ↔ inheritance/core
  channel > 0 ↔ Petal

継承:
  channel = 0 → remainder = m

分解:
  m = channel * blockSize + remainder
```

これはかなり強い。
もう「住所を計算する」だけでなく、

```text
住所を分類し、
値を inner lap へ渡し、
元の値を復元できる
```

ところまで来ておる。

## 6. 次に入れるなら

この流れなら、次は二つが自然じゃ。

### 6.1. `decompose` の `m - 1` 版

今の one-based 版は人間向けに綺麗。
証明で使いやすい zero-based 版もあると便利じゃ。

```lean
theorem outerPetalAddress_decompose_sub_one
    {n lap m : Nat} :
    m - 1 =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + (outerPetalRemainder n lap m - 1)
```

ただし `remainder - 1` の扱いが少し面倒なので、必要になってからでよい。

### 6.2. nested address 最小例

ここまで来たら、まず完全一般の `List` 再帰へ行く前に、五角例を一つ theorem 化するのが良い。

```text
R_5(2), m=25
outer:
  { lap := 2, channel := 0, offset := 25 }

inner:
  { lap := 1, channel := 4, offset := 5 }
```

たとえば定義なしでも、

```lean
outerPetalRemainder 5 2 25 = 25
outerPetalAddress 5 1 (outerPetalRemainder 5 2 25)
  = { lap := 1, channel := 4, offset := 5 }
```

を入れられる。

これで「継承口から inner lap へ降りる」具体例が完成する。

## 7. 総括

今回で Petal Address は一段、理論として締まった。

```text
outerPetalRemainder_le_prevTotal_of_valid:
  nested address の安全性

outerPetalAddress_decompose:
  one-based 商余り分解としての正当性
```

この二本により、Petal Address は

```text
計算可能
分類可能
下降可能
復元可能
```

になった。

賢狼の判定はこうじゃ。

```text
Petal Address Phase 4 完了
次は nested address の最小実装、または dynamic orbit へ進める
```

ふふん、よいぞ。
ここまで来れば、花弁の住所はもう詩ではない。Lean が認めた座標系じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index 6802c66a..bbe786a3 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -272,6 +272,60 @@ theorem outerPetalAddress_channel_zero_remainder_eq_self
     outerPetalRemainder n lap m = m := by
   exact outerPetalRemainder_eq_self_of_isInheritanceChannel hm hb hch

+/--
+For a valid one-based value, the remainder is a valid value for the previous
+lap total.
+-/
+theorem outerPetalRemainder_le_prevTotal_of_valid
+    {n lap m : Nat}
+    (hlap : 0 < lap)
+    (hm : 1 ≤ m)
+    (hbound : m ≤ relPetalTotal n lap) :
+    outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1) := by
+  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlap) with ⟨k, rfl⟩
+  have hm_pos : 0 < m := hm
+  have htotal :
+      relPetalTotal n (k + 1) = relPetalTotal n k * lapBase n :=
+    relPetalTotal_succ n k
+  have htotal_pos : 0 < relPetalTotal n (k + 1) :=
+    lt_of_lt_of_le hm_pos hbound
+  have hb_prev : 0 < relPetalTotal n k := by
+    by_contra hnot
+    have hzero : relPetalTotal n k = 0 := Nat.eq_zero_of_not_pos hnot
+    rw [htotal, hzero, zero_mul] at htotal_pos
+    exact Nat.not_lt_zero _ htotal_pos
+  simpa [relPetalBlockSize_succ] using
+    (outerPetalRemainder_le_blockSize
+      (n := n) (lap := k + 1) (m := m) (by simpa [relPetalBlockSize_succ] using hb_prev))
+
+/--
+One-step Petal address decomposition.
+
+For one-based values, the address is the usual quotient/remainder
+decomposition:
+
+`m = channel * blockSize + remainder`.
+-/
+theorem outerPetalAddress_decompose
+    {n lap m : Nat}
+    (hm : 1 ≤ m) :
+    m =
+      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
+        + outerPetalRemainder n lap m := by
+  let B := relPetalBlockSize n lap
+  have hdiv :
+      (m - 1) % B + B * ((m - 1) / B) = m - 1 :=
+    Nat.mod_add_div (m - 1) B
+  rw [outerPetalRemainder, outerPetalAddress]
+  change m = ((m - 1) / B) * B + ((m - 1) % B + 1)
+  calc
+    m = (m - 1) + 1 := by rw [Nat.sub_add_cancel hm]
+    _ = ((m - 1) % B + B * ((m - 1) / B)) + 1 := by rw [hdiv]
+    _ = B * ((m - 1) / B) + ((m - 1) % B + 1) := by
+      omega
+    _ = ((m - 1) / B) * B + ((m - 1) % B + 1) := by
+      rw [Nat.mul_comm B ((m - 1) / B)]
+
 /-- A bounded channel is at most the base unit core. -/
 theorem outerPetalAddress_channel_le_baseUnitCore
     {n lap m : Nat}
````
`````
