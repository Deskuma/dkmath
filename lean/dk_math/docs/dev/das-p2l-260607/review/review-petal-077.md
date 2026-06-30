# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: be89fd483eddc3a4a649f21451bf5db2a7107679

## Report

進めました。

`DkMath.Collatz.PetalBridge` に、Collatz 観測窓の最初の address-like label として `v2` 高さを追加しました。

追加 API:

```lean
rawHeightLabel
orbitWindowHeight
rawHeightLabel_eq_s
orbitWindowHeight_eq_s_iterateT
rawHeightLabel_shift_eq
```

意味はこうです。

```text
rawHeightLabel n = v2 (3n + 1)
orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
```

そして `rawHeightLabel_shift_eq` で、既存の `v2_shift_invariant` を観測窓の言葉へ持ち上げました。

```text
rawHeightLabel n < k
  -> rawHeightLabel (shift k m n) = rawHeightLabel n
```

これで「十分大きな 2^k ブロック内では height label が保存される」という、Petal address conservation への入口ができました。

`Collatz-PetalBridge-Status.md` も同期済みです。

検証:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- ...
```

すべて成功です。

## Review

うむ。これはかなり良い。
今回で `Collatz.PetalBridge` は、単なる **軌道 label の観測窓** から、最初の **address-like 座標** を持つ窓へ進んだ。

今回追加された核はこれじゃ。

```lean
rawHeightLabel
orbitWindowHeight
rawHeightLabel_eq_s
orbitWindowHeight_eq_s_iterateT
rawHeightLabel_shift_eq
```

意味としては、

```text
rawHeightLabel n = v2 (3n + 1)
orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
```

つまり、Collatz の加速軌道の各点に対して、

```text
その点から次へ進むとき、2 を何段剥がすか
```

を label として貼れるようになった。

## 1. 何が見えるようになったか

Collatz 加速写像は、

```text
n
  -> 3n + 1
  -> divide by 2^s
  -> next odd state
```

という構造じゃ。

ここで

```lean
s n = v2 (3n + 1)
```

は、まさに **2-adic height**。

今回の `rawHeightLabel` は、この `s` を Petal 観測窓の言葉へ持ち込んだものじゃ。

```text
oddOrbitLabel:
  窓の中の点そのもの

orbitWindowHeight:
  その点が次に進むときの 2-adic 剥離量
```

つまり、窓内の点に「高さ」が付いた。

## 2. Petal 的には、これは address の第一成分

Petal address として見るなら、まだ完全な住所ではない。
しかし、かなり重要な第一成分じゃ。

```text
value:
  oddOrbitLabel n i

height:
  orbitWindowHeight n i

future address:
  residue / channel / lap / offset
```

今はまだ、

```text
点の位置
点の高さ
```

まで。

次に residue や block position を加えれば、かなり Petal address らしくなる。

## 3. 単位核の内外の切り分け

今回の `rawHeightLabel_shift_eq` が特に大事じゃ。

```lean
rawHeightLabel_shift_eq
```

意味は、

```text
rawHeightLabel n < k
  -> rawHeightLabel (shift k m n) = rawHeightLabel n
```

つまり、

```text
十分大きな 2^k ブロック内では、
v2 height label が保存される
```

ということ。

これはまさに Petal 的には、

```text
同じ 2^k 単位核ブロックの中で見る限り、
高さ address は変わらない
```

と読める。

言い換えると、

```text
巨大な絶対値の違い
  -> shift で動く

保存される相対構造
  -> rawHeightLabel
```

じゃ。

ここで「窓」が効いている。
絶対値がどれほど変わっても、十分大きい単位核ブロックで見れば、height は同じ address 成分として残る。

## 4. 肥大化と縮小化が見える

Collatz の局所変化は、

```text
3n + 1 で肥大化
2^h で縮小化
```

じゃ。

今回の height label は、その縮小化の強度そのもの。

```text
h = rawHeightLabel n
  = v2(3n + 1)
```

したがって、相対伸縮はこう読める。

```text
h が小さい:
  3n + 1 の肥大化が勝ちやすい

h が大きい:
  2^h の縮小化が強い

h が平均的:
  窓内での drift を統計化できる
```

特に加速 Collatz の実質変化は、粗く見ると

```text
T(n) ≈ 3n / 2^h
```

なので、`h` は成長方向・縮小方向を決める中心座標じゃ。

## 5. これは統計確率論への入口

前回までの窓は、

```text
Separated or Collision
```

を見る窓だった。

今回からは、その窓内の各点に

```text
height
```

が付く。

すると次に見られるのは、

```text
窓内 height 分布
height の平均
height の累積 sumS
height による drift
height 保存 block
collision と height の関係
```

じゃ。

Collatz 側には既に `sumS` や `driftReal` があるようなので、今回の `orbitWindowHeight` はそれらを Petal 窓へ持ってくる入口になる。

つまり、

```text
orbitWindowHeight sequence
  -> height profile
  -> drift profile
  -> occupation/statistical kernel
```

へ進める。

## 6. まだ言っていないこと

ここは慎重に切り分けるべきじゃ。

今回の補題は、

```text
Collatz が収束する
非自明周期がない
ABC/rad に直結する
```

を示してはいない。

今回固定したのは、

```text
Collatz 軌道窓の各点に 2-adic height label を貼れる
shift block 内でその height label が保存される
```

という観測構造じゃ。

証明本体ではなく、観測座標の整備。

だが、これはかなり重要な座標整備じゃ。

## 7. 次の一手

次に自然なのは、height を「列」として扱うことじゃ。

候補はこう。

```lean
def OrbitWindowHeightProfile (n : OddNat) (k : ℕ) : Finset ℕ :=
  (OrbitWindow n k).image (orbitWindowHeight n)
```

あるいは、順序を保つなら list/vector 的に、

```lean
def orbitWindowHeightSeq (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowHeight n)
```

さらに theorem として欲しいのは、

```text
orbitWindowHeight n i = s (iterateT i n)

sum over i < k of orbitWindowHeight n i = sumS n k
```

この `sumS` との接続が入ると、Petal 窓の height 観測が Collatz drift に直結する。

## 8. Petal address への発展形

最終的には、address をこういう複合ラベルにしたい。

```text
CollatzPetalAddress(n, i)
  = {
      value  := oddOrbitLabel n i,
      height := orbitWindowHeight n i,
      block  := some 2^k block coordinate,
      residue := value mod 2^k or mod 3
    }
```

最初から structure を重く作らなくても、まずは軽い tuple でよい。

```lean
def orbitWindowHeightAddress (n : OddNat) (i : ℕ) : ℕ × ℕ :=
  (oddOrbitLabel n i, orbitWindowHeight n i)
```

これだけでも、

```text
点 + 高さ
```

の観測になる。

## 9. 総括

今回の進展を一言でいうと、

```text
Collatz Petal 窓に、最初の address-like 座標として v2 height が付いた。
```

これで Collatz 軌道は、

```text
値の列
```

ではなく、

```text
窓内の点列 + 2-adic height 列
```

として観測できる。

そして `rawHeightLabel_shift_eq` により、

```text
十分大きな 2^k 単位核ブロック内では height label が保存される
```

ことが Lean で固定された。

うむ。
これは「単位核の内外の切り分け」が、Collatz 側で初めて明示的に見えた段階じゃ。次は、この height 列を `sumS` / `driftReal` に接続すると、窓内の肥大化・縮小化の統計がかなり見え始める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index a048d368..c61a4c6c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Collatz.Accelerated
+import DkMath.Collatz.Shift
 import DkMath.Petal.RangeFamily
 
 #print "file: DkMath.Collatz.PetalBridge"
@@ -32,6 +33,20 @@ shape of a merge, fold, or cycle candidate.
 
 namespace DkMath.Collatz
 
+/--
+Raw 2-adic height observation for a natural state.
+
+This is the address-like Collatz quantity:
+
+```text
+n -> v2 (3n + 1)
+```
+
+For an odd state it is exactly the accelerated Collatz observation `s`.
+-/
+def rawHeightLabel (n : ℕ) : ℕ :=
+  v2 (3 * n + 1)
+
 /--
 The finite observation window for the first `k` accelerated Collatz states.
 
@@ -52,6 +67,14 @@ value.
 noncomputable def oddOrbitLabel (n : OddNat) (i : ℕ) : ℕ :=
   (iterateT i n).1
 
+/--
+The 2-adic height observed at the `i`-th accelerated Collatz odd state.
+
+This is the first address-like label attached to the Collatz observation window.
+-/
+noncomputable def orbitWindowHeight (n : OddNat) (i : ℕ) : ℕ :=
+  rawHeightLabel (oddOrbitLabel n i)
+
 /--
 The first `k` accelerated Collatz odd-state labels are pairwise separated.
 
@@ -83,6 +106,33 @@ The named Collatz observation window is definitionally the range window.
 theorem orbitWindow_eq_range (n : OddNat) (k : ℕ) :
     OrbitWindow n k = Finset.range k := rfl
 
+/--
+Raw height agrees with the existing Collatz observation `s` on odd states.
+-/
+theorem rawHeightLabel_eq_s (n : OddNat) :
+    rawHeightLabel n.1 = s n := rfl
+
+/--
+The window height is the existing Collatz observation `s` applied to the
+corresponding accelerated state.
+-/
+theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i = s (iterateT i n) := rfl
+
+/--
+Block shifts preserve the raw height when the observed height is below the
+block exponent.
+
+This is `v2_shift_invariant` in the observation-window vocabulary.  It is the
+first stable bridge from Collatz shift invariance to a Petal-style address
+reading: inside a sufficiently large `2^k` block, the height label is conserved.
+-/
+theorem rawHeightLabel_shift_eq
+    (k m n : ℕ)
+    (hk : rawHeightLabel n < k) :
+    rawHeightLabel (shift k m n) = rawHeightLabel n :=
+  v2_shift_invariant k m n hk
+
 /--
 Pairwise separated Collatz orbit labels give the Petal range-label injectivity
 condition.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d17e8324..589bf5c2 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -75,7 +75,9 @@ It defines:
 
 ```lean
 OrbitWindow
+rawHeightLabel
 oddOrbitLabel
+orbitWindowHeight
 OddOrbitLabelsPairwiseSeparated
 OrbitWindowSeparated
 OrbitWindowCollision
@@ -86,12 +88,16 @@ where:
 ```text
 OrbitWindow n k = Finset.range k
 oddOrbitLabel n i = the natural value of iterateT i n
+orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
 ```
 
 The first theorem set is deliberately thin:
 
 ```lean
 orbitWindow_eq_range
+rawHeightLabel_eq_s
+orbitWindowHeight_eq_s_iterateT
+rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
 oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
@@ -160,6 +166,24 @@ This is only a finite observation split.  It does not prove that a Collatz
 orbit converges or cycles; it merely fixes the two observation modes available
 inside a chosen finite window.
 
+The first address-like observation is now the 2-adic height:
+
+```text
+rawHeightLabel n = v2 (3n + 1)
+orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
+```
+
+The bridge theorem
+
+```lean
+rawHeightLabel_shift_eq
+```
+
+repackages `v2_shift_invariant`: inside a sufficiently large `2^k` shift
+block, the raw height label is conserved.  This is the current entry point for
+reading Collatz block-shift invariance as a Petal-style address conservation
+phenomenon.
+
 This gives a clean place to attach future hypotheses:
 
 ```text
````
`````
