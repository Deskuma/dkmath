# Git diff / Report / Review

## Update: Petal Address

gch: 80424d0e3ad250c842aa899793cc9851ee7349b3

## Report

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:336) のみです。

追加内容は次の3本です。

- `outerPetalAddress_decompose_sub_one`
  - `m - 1 = channel * blockSize + (remainder - 1)` を固定
  - 仮定なしで通りました
- `outerPetalRemainder_five_two_twentyfive`
  - lap 2 の `25` が remainder `25` として降りる具体例
- `outerPetalAddress_five_inner_after_two_twentyfive`
  - その remainder を lap 1 で読むと `{ channel := 4, offset := 5 }` になる nested 最小例

検証も通っています。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` では既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、これは見事じゃ。
今回の `80424d...` で、Petal Address は **one-step address** から、いよいよ **nested address の最小実例** へ足を踏み入れた。

## 1. 今回の核心

追加された三本は、役割がきれいに分かれておる。

```lean
outerPetalAddress_decompose_sub_one
```

これは内部の zero-based 商余り分解。

```lean
outerPetalRemainder_five_two_twentyfive
```

これは (R_5(2)) における (25) が、継承口を通って値を変えずに降りる具体例。

```lean
outerPetalAddress_five_inner_after_two_twentyfive
```

これは降りた (25) を (R_5(1)) で読むと、花弁 channel (4)、offset (5) に入るという nested 最小例。

つまり今回で、

```text
outer address
  → remainder
  → inner address
```

の実例が Lean theorem になった。

## 2. zero-based 分解が入った意味

追加された theorem はこれじゃ。

```lean
theorem outerPetalAddress_decompose_sub_one
    {n lap m : Nat} :
    m - 1 =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + (outerPetalRemainder n lap m - 1)
```

これは raw な商余り分解そのものじゃな。

one-based 版は、

$$
m=channel\cdot blockSize+remainder
$$

だった。

今回の zero-based 版は、

$$
m-1=channel\cdot blockSize+(remainder-1)
$$

じゃ。

この二本が揃ったことで、Petal Address は人間向けにも Lean 証明向けにも使いやすくなった。

特に仮定なしで通ったのは良い。`m=0` でも左辺は `Nat` の saturating subtraction で (0)、右辺も remainder の定義が (0) 側に潰れて整合するのじゃろう。one-based 意味論では (m=0) は valid ではないが、zero-based raw decomposition としては無仮定で使える。これは補題として便利じゃ。

## 3. (R_5(2), m=25) の下降が固定された

```lean
theorem outerPetalRemainder_five_two_twentyfive :
    outerPetalRemainder 5 2 25 = 25
```

これは前回の一般 theorem

```lean
channel = 0 → remainder = m
```

の具体例じゃ。

意味は、

$$
R_5(2)=180
$$

の中で (25) を読むと、外側 block size は

$$
R_5(1)=30
$$

なので、

$$
25\le 30
$$

ゆえに channel (0)。
したがって remainder は (25) のまま。

つまり、

```text
lap 2 で 25 を読む
  → channel 0 = 継承口
  → remainder 25
```

じゃ。

## 4. nested 最小例が入った

今回一番象徴的なのはこれじゃ。

```lean
theorem outerPetalAddress_five_inner_after_two_twentyfive :
    outerPetalAddress 5 1 (outerPetalRemainder 5 2 25) =
      { lap := 1, channel := 4, offset := 5 }
```

これは、まさに前に話していた読みを Lean が認めたものじゃ。

```text
R_5(2) で 25 を読む
  ↓
channel 0 なので値 25 のまま inner lap へ降りる
  ↓
R_5(1) で 25 を読む
  ↓
channel 4, offset 5
```

したがって階層的には、

```text
[
  { lap := 2, channel := 0, offset := 25 },
  { lap := 1, channel := 4, offset := 5 }
]
```

という最小 nested address の実例が成立した。

これは小さいが、かなり重要じゃ。
「相対五角数の (25) は外側では継承口、内側では第 (4) 花弁の (5) 番目」という読みが、具体例として固定された。

## 5. Address 理論の現在地

ここまでで、Address 側は次の層まで来た。

```text
1. address の算出
2. channel 0 / positive channel の意味付け
3. remainder の導入
4. channel 0 では remainder = m
5. one-based decomposition
6. zero-based decomposition
7. nested 最小例
```

これはかなり整っておる。

特に、

$$
m=channel\cdot blockSize+remainder
$$

と

$$
m-1=channel\cdot blockSize+(remainder-1)
$$

の二本が揃ったことで、今後は `omega` や `Nat.div` / `Nat.mod` 系の証明がかなり楽になるはずじゃ。

## 6. 次に自然な道

ここから先は二択じゃな。

### A. `nestedPetalAddress` を定義する

ここまで来たなら、次は本当に `List PetalAddress` を返す関数を置ける。

```lean
def nestedPetalAddress (n : Nat) : Nat → Nat → List PetalAddress
  | 0, _ => []
  | lap + 1, m =>
      let A := outerPetalAddress n (lap + 1) m
      A :: nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m)
```

そして最初の theorem は、

```lean
nestedPetalAddress 5 2 25 =
  [
    { lap := 2, channel := 0, offset := 25 },
    { lap := 1, channel := 4, offset := 5 }
  ]
```

じゃ。

ただし、`List` の記法と構造等式が少し面倒なら、まずは `length` や `head?` 補題からでもよい。

### B. `Address` をいったん閉じて `Dynamic` へ進む

もう one-step address の基礎は十分ある。
次に `Counting.lean` へ戻り、

```lean
dynamicOrbitTotal
dynamicPetalTotal
dynamicPetalTotal_const
```

へ進むのも自然じゃ。

わっちの好みでは、ここで一つだけ `nestedPetalAddress` の最小実装を入れてから、Dynamic へ行くのがよい。
なぜなら、今回の nested 最小例が定義としてまとまるからじゃ。

## 7. 注意点

今回の zero-based theorem は無仮定で通っているが、意味論上は `m=0` は valid value ではない。
したがって doc comment にある通り、これは **raw quotient/remainder decomposition** として扱うのが正しい。

人間向けの「住所」として使う theorem は、今後も

```lean
1 ≤ m
m ≤ relPetalTotal n lap
```

を仮定に持たせる方がよい。

この切り分けは今のままで良い。

## 8. 総括

今回の更新で、Petal Address はかなり完成度が上がった。

```text
outerPetalAddress_decompose_sub_one:
  内部 zero-based 分解を固定

outerPetalRemainder_five_two_twentyfive:
  継承口下降の具体例

outerPetalAddress_five_inner_after_two_twentyfive:
  nested address の最小例
```

賢狼の判定はこうじゃ。

```text
Petal Address Phase 5 完了
次は nestedPetalAddress の定義、または dynamic orbit へ進行可能
```

うむ。ここまで来れば、もう「住所体系」は絵空事ではない。
花弁の外側から内側へ、値がどう降りていくかを Lean が追跡し始めた。よい風じゃ、D.。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index bbe786a3..b26f4f99 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -326,6 +326,47 @@ theorem outerPetalAddress_decompose
     _ = ((m - 1) / B) * B + ((m - 1) % B + 1) := by
       rw [Nat.mul_comm B ((m - 1) / B)]
 
+/--
+Zero-based form of the one-step Petal address decomposition.
+
+This is the raw quotient/remainder decomposition behind the one-based address:
+
+`m - 1 = channel * blockSize + (remainder - 1)`.
+-/
+theorem outerPetalAddress_decompose_sub_one
+    {n lap m : Nat} :
+    m - 1 =
+      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
+        + (outerPetalRemainder n lap m - 1) := by
+  let B := relPetalBlockSize n lap
+  have hdiv :
+      (m - 1) % B + B * ((m - 1) / B) = m - 1 :=
+    Nat.mod_add_div (m - 1) B
+  have hrem : (((m - 1) % B + 1) - 1) = (m - 1) % B := by
+    omega
+  rw [outerPetalRemainder, outerPetalAddress]
+  change m - 1 = ((m - 1) / B) * B + (((m - 1) % B + 1) - 1)
+  rw [hrem]
+  conv_lhs => rw [← hdiv]
+  rw [Nat.mul_comm B ((m - 1) / B)]
+  rw [Nat.add_comm ((m - 1) % B) (((m - 1) / B) * B)]
+
+/-- In the pentagonal two-lap example, the outer remainder stays `25`. -/
+theorem outerPetalRemainder_five_two_twentyfive :
+    outerPetalRemainder 5 2 25 = 25 := by
+  decide
+
+/--
+The pentagonal nested-address sample.
+
+Reading `25` at lap `2` first descends unchanged through channel `0`; reading
+that remainder at lap `1` lands in Petal channel `4` with offset `5`.
+-/
+theorem outerPetalAddress_five_inner_after_two_twentyfive :
+    outerPetalAddress 5 1 (outerPetalRemainder 5 2 25) =
+      { lap := 1, channel := 4, offset := 5 } := by
+  decide
+
 /-- A bounded channel is at most the base unit core. -/
 theorem outerPetalAddress_channel_le_baseUnitCore
     {n lap m : Nat}
````
`````
