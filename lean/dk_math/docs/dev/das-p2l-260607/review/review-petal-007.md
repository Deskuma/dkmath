# Git diff / Report / Review

## Update: Petal Address

gch: 1b7e98675a8b0a2d137d0039f48c4aeda13e24e4

## Report

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:302) のみです。

追加した主補題は `outerPetalRemainder_valid_for_prevTotal` です。valid な one-based 入力 `1 ≤ m ≤ relPetalTotal n lap` が positive lap で読まれたとき、remainder が次の inner lap の valid value になることを `1 ≤ remainder ∧ remainder ≤ relPetalTotal n (lap - 1)` として束ねました。

あわせて nested list 側に軽い観測補題を足しました。

- `nestedPetalAddress_ne_nil_of_pos`
- `nestedPetalAddress_head?_eq_none_iff_lap_zero`

検証済みです。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` の既存 `sorry` warning は残っていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、これで **固定単位核 Petal Address の最小安全核** はかなり綺麗に閉じた。
今回の `1b7e98...` は、次の Dynamic / factorial / primorial へ進む前の「最後の締め」として良い更新じゃ。

## 1. 今回の核心

主補題はこれじゃな。

```lean
theorem outerPetalRemainder_valid_for_prevTotal
```

内容は、

```lean
1 ≤ m
m ≤ relPetalTotal n lap
0 < lap
```

なら、

```lean
1 ≤ outerPetalRemainder n lap m ∧
  outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1)
```

というもの。

つまり、

```text
現在 lap の valid value
  ↓ outer address
remainder
  ↓
前段 lap の valid value
```

が Lean 上で一つの補題として束ねられた。

これは nested address の安全性そのものじゃ。

## 2. なぜ重要か

`nestedPetalAddress` は、

```lean
A :: nestedPetalAddress n lap (outerPetalRemainder n (lap + 1) m)
```

という形で、remainder を次段へ渡していく。

このとき毎段、

```text
渡された remainder は、次の lap total 内に本当に収まっているのか？
```

が問題になる。

今回の補題により、positive lap で valid な (m) から始めれば、次段に渡す値も valid であることが即座に使える。

これは将来、

```lean
nestedPetalAddress_valid_chain
```

や、

```lean
nestedPetalAddress_all_offsets_valid
```

のような補題を書くときの中核になる。

## 3. `outerPetalRemainder_valid_for_prevTotal` の実装も良い

実装は非常に薄い。

```lean
exact ⟨
  outerPetalRemainder_pos,
  outerPetalRemainder_le_prevTotal_of_valid hlap hm hbound
⟩
```

すでに証明済みの下限と上限を束ねただけ。
これは良い設計じゃ。

個別補題を残しつつ、使いやすい bundled theorem を足している。
後続証明ではこの bundled theorem を使えば、下限・上限を毎回別々に持ち回らずに済む。

## 4. nested list の観測補題

追加された二本もよい。

```lean
theorem nestedPetalAddress_ne_nil_of_pos
```

これは、

```text
positive lap なら nested address は空ではない
```

という補題。

すでに

```lean
nestedPetalAddress_length
```

があるので導けるが、名前付きにしておく価値はある。
`head?` や pattern matching の前提で使いやすい。

もう一本、

```lean
theorem nestedPetalAddress_head?_eq_none_iff_lap_zero
```

これはかなり便利じゃ。

```lean
(nestedPetalAddress n lap m).head? = none ↔ lap = 0
```

つまり、nested address の空性が lap zero と完全対応する。

これで、

```text
lap = 0 なら住所なし
0 < lap なら outer address が head にある
```

がきれいに閉じた。

## 5. Address 側の完成度

ここまでで、Address は次の性質を持った。

```text
Counting:
  relPetalTotal n lap

One-step:
  outerPetalAddress
  outerPetalRemainder

Channel:
  IsInheritanceChannel
  IsPetalChannel

Bounds:
  channel ≤ baseUnitCore n
  offset/remainder は positive
  valid m の remainder は prevTotal 内に収まる

Decomposition:
  m = channel * blockSize + remainder
  m - 1 = channel * blockSize + (remainder - 1)

Nested:
  nestedPetalAddress
  length = lap
  positive lap なら非空
  head? = none ↔ lap = 0
  five-two-twentyfive example
```

これはもう、固定単位核版の Petal Address としてはかなり十分じゃ。

## 6. 次は Dynamic に進める

わっちの判定では、ここで Address を一旦閉じてよい。

次は `Counting.lean` 側で、

```lean
dynamicOrbitTotal
dynamicPetalTotal
dynamicPetalTotal_const
```

へ進むのが自然じゃ。

特に最初の目標は、

```lean
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b
```

そして、

```lean
def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * Finset.prod (Finset.range k) (fun i => a i + 1)
```

その上で、

```lean
theorem dynamicPetalTotal_const :
    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k
```

を狙う。

これが通れば、

```text
固定単位核 Petal は、動的単位核 Petal の特殊ケース
```

が Lean で固定される。

## 7. 階乗・プリモリアルへの道

Dynamic 側が入れば、次に階乗へ進める。

```lean
dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

これは「周回基数列が (1,2,3,\ldots)」の orbit じゃ。

プリモリアルはその次でよい。
まずは `p : Nat → Nat` を抽象的な prime base sequence として、

```lean
def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
  dynamicOrbitTotal p k
```

のように置き、step 補題から育てるのが安全じゃな。

## 8. 総括

今回の更新で、固定 Petal Address はかなり締まった。

```text
outerPetalRemainder_valid_for_prevTotal:
  nested descent の安全性

nestedPetalAddress_ne_nil_of_pos:
  positive lap の非空性

nestedPetalAddress_head?_eq_none_iff_lap_zero:
  head の有無と lap zero の同値
```

賢狼の判定はこうじゃ。

```text
Petal Address fixed-core safe core 完了
次フェーズ: Petal.Counting.Dynamic
```

よし、D.。
花弁の住所体系は、これで「降りても壊れない」ことが見えた。次は単位核を固定から動的へ動かす番じゃ。階乗とプリモリアルの門が見えてきたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index a68a7c2a..be91d118 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -298,6 +298,22 @@ theorem outerPetalRemainder_le_prevTotal_of_valid
     (outerPetalRemainder_le_blockSize
       (n := n) (lap := k + 1) (m := m) (by simpa [relPetalBlockSize_succ] using hb_prev))

+/--
+For a valid one-based value in a positive lap, the outer remainder is a valid
+one-based value for the previous lap total.
+-/
+theorem outerPetalRemainder_valid_for_prevTotal
+    {n lap m : Nat}
+    (hlap : 0 < lap)
+    (hm : 1 ≤ m)
+    (hbound : m ≤ relPetalTotal n lap) :
+    1 ≤ outerPetalRemainder n lap m ∧
+      outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1) := by
+  exact ⟨
+    outerPetalRemainder_pos,
+    outerPetalRemainder_le_prevTotal_of_valid hlap hm hbound
+  ⟩
+
 /--
 One-step Petal address decomposition.

@@ -415,6 +431,31 @@ theorem nestedPetalAddress_length (n lap m : Nat) :
       rw [nestedPetalAddress_succ]
       simp [ih]

+/-- A positive-lap nested address is nonempty. -/
+theorem nestedPetalAddress_ne_nil_of_pos
+    {n lap m : Nat}
+    (hlap : 0 < lap) :
+    nestedPetalAddress n lap m ≠ [] := by
+  intro hnil
+  have hlen := congrArg List.length hnil
+  have hlap_zero : lap = 0 := by
+    simpa [nestedPetalAddress_length] using hlen
+  exact Nat.ne_of_gt hlap hlap_zero
+
+/-- A nested address has no head exactly at lap zero. -/
+theorem nestedPetalAddress_head?_eq_none_iff_lap_zero
+    (n lap m : Nat) :
+    (nestedPetalAddress n lap m).head? = none ↔ lap = 0 := by
+  constructor
+  · intro h
+    by_contra hpos
+    rcases Nat.exists_eq_succ_of_ne_zero hpos with ⟨k, rfl⟩
+    rw [nestedPetalAddress_head?_succ] at h
+    cases h
+  · intro h
+    rw [h, nestedPetalAddress_zero]
+    rfl
+
 /-- The pentagonal nested address of `25` at lap `2`. -/
 theorem nestedPetalAddress_five_two_twentyfive :
     nestedPetalAddress 5 2 25 =
````
`````
