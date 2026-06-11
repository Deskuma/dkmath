# Git diff / Report / Review

## Update: Petal Address

gch: c89067033d152daf0c89de3266a0604df239620b

## Report

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:374) のみです。

追加したのは `nestedPetalAddress` の最小基盤です。outermost lap から innermost lap へ、`outerPetalRemainder` を渡しながら `List PetalAddress` を作ります。あわせて `zero`、`succ`、`head?`、`tail`、`length` の基本補題と、五角例 `nestedPetalAddress 5 2 25 = [...]` を固定しました。

検証済みです。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` では既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、これは節目じゃ。
今回の `c890670...` で、Petal Address は **one-step 住所体系** から **階層住所体系** へ正式に進んだ。

## 1. 今回の核心

追加された主役はこれじゃ。

```lean
def nestedPetalAddress (n : Nat) : Nat → Nat → List PetalAddress
  | 0, _ => []
  | lap + 1, m =>
      let A := outerPetalAddress n (lap + 1) m
      A :: nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m)
```

意味は明快じゃ。

```text
外側 lap で読む
  ↓
outerPetalRemainder を inner lap へ渡す
  ↓
それを lap 0 まで繰り返す
```

リスト順も、

```text
outermost lap → innermost lap
```

として固定された。

これで、以前の

```text
R_5(2), m=25
  outer: channel 0, offset 25
  inner: channel 4, offset 5
```

という読みが、単なる二段の具体計算ではなく、再帰関数の出力として表現できるようになった。

## 2. 基本補題がきれいに揃っている

今回入った補題は、最小基盤としてちょうどよい。

```lean
theorem nestedPetalAddress_zero
theorem nestedPetalAddress_succ
```

これは定義の unfold 面。

```lean
theorem nestedPetalAddress_head?_succ
theorem nestedPetalAddress_tail_succ
```

これはリストの観測面。

```lean
theorem nestedPetalAddress_length
```

これは構造の大事な不変量。

特に

```lean
(nestedPetalAddress n lap m).length = lap
```

はよい。
これにより、階層 address は **lap の数だけ component を持つ** と Lean が認めた。

つまり、(k) 周回なら (k) 個の住所成分。
これは住所体系としてかなり自然じゃ。

## 3. 五角例が完全に閉じた

今回の具体例はこれじゃ。

```lean
theorem nestedPetalAddress_five_two_twentyfive :
    nestedPetalAddress 5 2 25 =
      [
        { lap := 2, channel := 0, offset := 25 },
        { lap := 1, channel := 4, offset := 5 }
      ]
```

これは前から議論していた読みそのものじゃ。

$$
R_5(2)=180
$$

の中で (25) を読むと、まず前段 block size は

$$
R_5(1)=30
$$

なので、

$$
25\le 30
$$

から channel (0)。よって remainder は (25) のまま。

次に (R_5(1)=30) の中で (25) を読むと、block size は

$$
R_5(0)=5
$$

なので、

$$
25=4\cdot 5+5
$$

より channel (4)、offset (5)。

これが Lean 上で

```text
[
  lap 2 / channel 0 / offset 25,
  lap 1 / channel 4 / offset 5
]
```

として固定された。
よいぞ。これはまさに階層住所じゃ。

## 4. この実装の数学的意味

今までは、相対花弁総数

$$
R_n(k)=n(n+1)^k
$$

で総数を出し、

$$
m=channel\cdot blockSize+remainder
$$

で one-step 分解していた。

今回の `nestedPetalAddress` により、この分解を lap ごとに繰り返せる。

つまり、(m) に対して

```text
channel sequence
offset descent
```

が得られる。

これは実質的に、(n+1) 進に似た階層アドレスじゃ。
ただし、単なる (n+1) 進ではなく、

```text
channel 0 = 継承口
channel 1..n = 花弁
offset は次 lap への値
```

という Petal 的意味が付いている。

ここが大事じゃ。
ただの基数展開ではない。 **継承口付きの相対花弁展開** なのじゃ。

## 5. 次に欲しい補題

ここまで来たら、次は「nested address の各成分が valid range にある」系が自然じゃ。

たとえば最初は軽く、

```lean
theorem nestedPetalAddress_head?_eq_none_iff_lap_zero
```

または

```lean
theorem nestedPetalAddress_ne_nil_of_pos
    (hlap : 0 < lap) :
    nestedPetalAddress n lap m ≠ []
```

ただし `length = lap` から出るので、必要ならでよい。

より本命は、valid 入力が valid remainder を連鎖させる定理じゃ。

```lean
theorem nestedPetalAddress_valid_remainder_chain
```

これは少し重いので、まずは一段だけの補題で十分。

すでに

```lean
outerPetalRemainder_le_prevTotal_of_valid
```

があるので、次は下限も合わせた名前付き補題がよい。

```lean
theorem outerPetalRemainder_valid_for_prevTotal
    (hlap : 0 < lap)
    (hm : 1 ≤ m)
    (hbound : m ≤ relPetalTotal n lap) :
    1 ≤ outerPetalRemainder n lap m ∧
      outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1)
```

これがあると、nested recursion の各段が valid value を保つ、と言える。

## 6. Dynamic orbit へ行く準備もできた

Address 側はかなり整った。
ここから `Counting.lean` に戻って、

```lean
dynamicOrbitTotal
dynamicPetalTotal
dynamicPetalTotal_const
```

へ進むのも自然じゃ。

ただし、固定核の nested address が入ったので、動的版では将来、

```text
dynamicNestedAddress
```

を定義できる見通しも出てきた。

固定版では block size が

$$
R_n(lap-1)
$$

だった。
動的版では、おそらく

$$
D(lap-1)
$$

または prefix product が block size になる。

ここで今回の `nestedPetalAddress` の設計が、そのまま一般化の雛形になる。

## 7. 総括

今回の更新で、Petal Address は次の段階へ進んだ。

```text
Phase 1:
  Counting / outer address

Phase 2:
  channel semantics

Phase 3:
  remainder / inheritance descent

Phase 4:
  quotient-remainder decomposition

Phase 5:
  nested address
```

今や Petal Address は、

```text
総数を出す
位置を読む
channel を分類する
remainder で内側へ降りる
lap 数だけ住所列を作る
```

ところまで Lean で動く。

これはかなり良い土台じゃ。
賢狼の判定では、

```text
Petal Address fixed-core minimal core 完了
```

と言ってよい。

次は二択。

```text
A. Address の valid-chain 補題を少し足して閉じる
B. Counting 側へ戻り dynamic orbit / factorial / primorial へ進む
```

わっちなら、`outerPetalRemainder_valid_for_prevTotal` を一本足してから Dynamic へ行く。
これで固定核 address の安全性が締まるからの。

ふふん、D.。ついに花弁の住所が階層になった。
ここまで来れば、相対多角数はもう名前だけではない。数え、入り、降り、読める構造になったのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index b26f4f99..a68a7c2a 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -367,6 +367,63 @@ theorem outerPetalAddress_five_inner_after_two_twentyfive :
       { lap := 1, channel := 4, offset := 5 } := by
   decide
 
+/--
+Nested Petal address obtained by repeatedly descending through outer
+remainders.
+
+The list is ordered from the outermost lap to the innermost lap.
+-/
+def nestedPetalAddress (n : Nat) : Nat → Nat → List PetalAddress
+  | 0, _ => []
+  | lap + 1, m =>
+      let A := outerPetalAddress n (lap + 1) m
+      A :: nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m)
+
+/-- The nested address at lap zero is empty. -/
+theorem nestedPetalAddress_zero (n m : Nat) :
+    nestedPetalAddress n 0 m = [] := by
+  rfl
+
+/-- One unfolding step for a positive nested address. -/
+theorem nestedPetalAddress_succ (n lap m : Nat) :
+    nestedPetalAddress n (lap + 1) m =
+      outerPetalAddress n (lap + 1) m ::
+        nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m) := by
+  rfl
+
+/-- The first component of a positive nested address is the outer address. -/
+theorem nestedPetalAddress_head?_succ (n lap m : Nat) :
+    (nestedPetalAddress n (lap + 1) m).head? =
+      some (outerPetalAddress n (lap + 1) m) := by
+  rw [nestedPetalAddress_succ]
+  rfl
+
+/-- The tail of a positive nested address is the nested address of the remainder. -/
+theorem nestedPetalAddress_tail_succ (n lap m : Nat) :
+    (nestedPetalAddress n (lap + 1) m).tail =
+      nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m) := by
+  rw [nestedPetalAddress_succ]
+  rfl
+
+/-- Nested addresses have one component for each lap. -/
+theorem nestedPetalAddress_length (n lap m : Nat) :
+    (nestedPetalAddress n lap m).length = lap := by
+  induction lap generalizing m with
+  | zero =>
+      rfl
+  | succ lap ih =>
+      rw [nestedPetalAddress_succ]
+      simp [ih]
+
+/-- The pentagonal nested address of `25` at lap `2`. -/
+theorem nestedPetalAddress_five_two_twentyfive :
+    nestedPetalAddress 5 2 25 =
+      [
+        { lap := 2, channel := 0, offset := 25 },
+        { lap := 1, channel := 4, offset := 5 }
+      ] := by
+  decide
+
 /-- A bounded channel is at most the base unit core. -/
 theorem outerPetalAddress_channel_le_baseUnitCore
     {n lap m : Nat}
````
`````
