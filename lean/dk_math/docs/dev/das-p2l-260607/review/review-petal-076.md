# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: bd5dd6b649b8bb8f61d54dcb4078443b134ed64c

## Report

観測窓の環境を作りました。

`DkMath.Collatz.PetalBridge` に、有限軌道片を明示する API を追加しました。

```lean
OrbitWindow
OrbitWindowSeparated
OrbitWindowCollision
orbitWindow_eq_range
exists_same_iterateT_of_orbitWindowCollision
not_orbitWindowCollision_of_separated
orbitWindowSeparated_contradiction_of_collision
orbitWindowSeparated_or_collision
```

これで Collatz の加速軌道について、有限窓 `Finset.range k` の中で

```text
Separated:
  最初の k 点が全部異なる

Collision:
  異なる i,j < k で同じ oddOrbitLabel に戻る
```

という観測分岐を Lean 上で固定できました。`Collision` が出ると `iterateT i n = iterateT j n` まで読めるので、Petal 側では独立 counting の破綻、Collatz 側では merge / fold / cycle candidate として扱えます。

`Collatz-PetalBridge-Status.md` も更新し、現在の窓口と次の作業を同期しました。

検証:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- ...
```

いずれも成功です。

## Review

うむ。これは **Collatz.PetalBridge が「観測窓」から「有限窓の二分岐 API」へ進んだ** という状況じゃ。
前回は `oddOrbitLabel` を通じて Collatz 軌道を Petal RangeFamily の label として読めるようにした。今回は、その観測対象を明示的に

```text
OrbitWindow n k = Finset.range k
```

として名前付けし、窓内で起こることを

```text
Separated
Collision
```

の二択として Lean 上に固定した。

## 1. 今回の核心

追加された主役はこの 3 つ。

```lean
OrbitWindow
OrbitWindowSeparated
OrbitWindowCollision
```

意味はこう。

```text
OrbitWindow n k:
  加速 Collatz 軌道の最初の k ステップを見る有限窓

OrbitWindowSeparated n k:
  その k 点がすべて異なる

OrbitWindowCollision n k:
  異なる i,j < k で同じ oddOrbitLabel に戻る
```

つまり、Collatz 軌道を無限列としていきなり扱わず、まず有限窓に切って、

```text
この窓の中では全部別の点か？
それとも衝突しているか？
```

を観測する API ができた。

これはかなり正しい初手じゃ。

## 2. 観測窓としての意味

Collatz の軌道は値そのものを見ると暴れる。

```text
大きくなる
小さくなる
また大きくなる
```

しかし今回の `OrbitWindow` では、観測範囲を

```text
0, 1, ..., k-1
```

に固定する。

そのうえで、各時刻の値を

```lean
oddOrbitLabel n i = (iterateT i n).1
```

として読む。

つまり、巨大な軌道そのものではなく、

```text
有限窓内の点列
```

として見るわけじゃ。

これで、統計・幾何・衝突解析に持ち込みやすくなる。

## 3. 分離と衝突の二分岐ができた

今回の重要 theorem はこれ。

```lean
orbitWindowSeparated_or_collision
```

これは、

```text
OrbitWindowSeparated n k ∨ OrbitWindowCollision n k
```

を出す。

もちろん、これは Collatz 予想の主張ではない。
有限集合上の観測モードを二分しているだけじゃ。

しかし、この「だけ」が重要。

Collatz では、無限の収束をいきなり言うより、まず有限窓ごとに

```text
まだ全部違う
または
どこかで同じ点に戻った
```

を切り分けるのが自然だからじゃ。

## 4. Collision が出たときの意味

今回の補題で、Collision からここまで読める。

```lean
exists_same_iterateT_of_orbitWindowCollision
```

意味は、

```text
OrbitWindowCollision n k
  -> ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ iterateT i n = iterateT j n
```

つまり、label が同じというだけでなく、`OddNat` の accelerated state 自体が同じになる。

これは Collatz 側ではかなり強い観測じゃ。

```text
同じ accelerated odd state に戻った
  -> merge / fold / cycle candidate
```

Petal 側では独立 counting の破綻。
Collatz 側では軌道構造の発見。

この二重読みが今回も維持されている。

## 5. Separated 側の意味

Separated 側は、

```lean
not_orbitWindowCollision_of_separated
```

で、

```text
Separated なら Collision はない
```

を固定している。

さらに、

```lean
orbitWindowSeparated_contradiction_of_collision
```

で、

```text
Separated と Collision を同時に仮定したら False
```

が出る。

これはトロミノ論法的には、かなり良い形じゃ。

```text
Core:
  有限観測窓

Beam:
  各時刻の oddOrbitLabel

True route:
  全部違うので分離軌道片として扱える

False route:
  分離と仮定したのに衝突が見つかる

Gap:
  その衝突が fold / merge / cycle 情報になる
```

## 6. なぜこれは Petal 的に重要か

前回までの `PetalBridge` は、Collatz 軌道 label を Petal RangeFamily に接続しただけだった。

今回からは、

```text
窓
分離
衝突
二分岐
```

が Collatz 側の名前で定義された。

つまり、Petal の外部補題を直接使うだけでなく、Collatz 側に **Petal 的観測語彙** が定着し始めた。

これは大事じゃ。

```text
Petal.RangeFamily の言葉を借りる段階
  -> Collatz.PetalBridge の固有語彙として定着する段階
```

へ進んだ。

## 7. まだ到達していないこと

ここは前回と同じく注意。

今回もまだ、

```text
2^k <= rad(GN)
```

には行っていない。

理由は、`oddOrbitLabel n i` はまだ

```text
prime label
primitive carrier
GN divisor
Zsigmondy witness
```

ではないからじゃ。

今回の成果は、

```text
Collatz 軌道の有限窓を Petal 的に観測できる
```

という段階。

ABC support/rad へ渡すには、さらに

```text
orbit label -> carrier label
orbit label -> prime label
orbit transition -> Petal address transition
```

のような変換層が要る。

## 8. 次の一手が明確になった

docs の更新でも、次の作業が整理されている。

```text
1. v2_shift_invariant を Petal address / residue 読みに接続する
2. window occupation / address transition layer を追加する
3. external label transform で orbit labels を carrier labels にできるか試す
4. その後で ABC support/rad への接続を検討する
```

この順番は良い。

特に次は、値そのものではなく、

```text
v2 height
address
residue
window occupation
transition
```

へ進むべきじゃ。

つまり、次に作るべきはたぶんこれ。

```lean
def orbitWindowAddress ...
def OrbitWindowAddressTransition ...
def OrbitWindowOccupation ...
```

あるいは、まずは軽く、

```lean
def orbitWindowHeight (n : OddNat) (i : ℕ) : ℕ := s (iterateT i n)
```

のように、各窓内点の `v2` 高さを観測する API がよい。

## 9. Collatz × Petal の現在地

現状はこうじゃ。

```text
Collatz.Accelerated:
  iterateT, s, sumS, driftReal

Collatz.PetalBridge:
  oddOrbitLabel
  OrbitWindow
  Separated / Collision split

Petal.RangeFamily:
  pairwise separation
  collision obstruction

Future:
  address transition
  occupation measure
  v2-height geometry
  probability/statistics
```

つまり今回で、Collatz 軌道を

```text
無限列
```

としてではなく、

```text
有限窓内の点配置
```

として観測する土台ができた。

## 10. 総括

今回の進展を一言で言うと、

```text
Collatz の加速軌道に対して、
有限観測窓 OrbitWindow を定義し、
その窓が Separated か Collision かを Lean 上で二分できるようにした。
```

これは証明の山頂ではなく、観測装置の整備じゃ。

だが Collatz では、この観測装置がかなり重要になる。

```text
Separated:
  まだ窓内で重複していない軌道片

Collision:
  同じ accelerated odd state への帰還
  merge / fold / cycle candidate
```

うむ。
これはまさに **Collatz を Petal 窓の中で見るための初期座標系** ができた段階じゃ。次は、その窓の中の点に `v2` 高さや Petal address を付ける段じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 4a931b65..a048d368 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -32,6 +32,16 @@ shape of a merge, fold, or cycle candidate.
 
 namespace DkMath.Collatz
 
+/--
+The finite observation window for the first `k` accelerated Collatz states.
+
+This is intentionally just `Finset.range k`; the point is to give the Collatz
+side a named window that can later carry address, height, or statistical
+observations.
+-/
+def OrbitWindow (_n : OddNat) (k : ℕ) : Finset ℕ :=
+  Finset.range k
+
 /--
 The natural-number label of the `i`-th accelerated Collatz odd state.
 
@@ -51,6 +61,28 @@ different in-range times have different observed odd states.
 def OddOrbitLabelsPairwiseSeparated (n : OddNat) (k : ℕ) : Prop :=
   ∀ i, i < k → ∀ j, j < k → i ≠ j → oddOrbitLabel n i ≠ oddOrbitLabel n j
 
+/--
+Window-level spelling of pairwise separation for accelerated Collatz labels.
+-/
+def OrbitWindowSeparated (n : OddNat) (k : ℕ) : Prop :=
+  OddOrbitLabelsPairwiseSeparated n k
+
+/--
+Window-level collision: two distinct in-window times have the same accelerated
+odd-state label.
+
+For Petal/ABC this blocks independent range counting.  For Collatz dynamics it
+is the observable merge/fold/cycle signal.
+-/
+def OrbitWindowCollision (n : OddNat) (k : ℕ) : Prop :=
+  ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ oddOrbitLabel n i = oddOrbitLabel n j
+
+/--
+The named Collatz observation window is definitionally the range window.
+-/
+theorem orbitWindow_eq_range (n : OddNat) (k : ℕ) :
+    OrbitWindow n k = Finset.range k := rfl
+
 /--
 Pairwise separated Collatz orbit labels give the Petal range-label injectivity
 condition.
@@ -106,4 +138,55 @@ theorem same_iterateT_of_oddOrbitLabel_collision
     iterateT i n = iterateT j n :=
   iterateT_eq_of_oddOrbitLabel_eq hlabel
 
+/--
+A window collision identifies the two accelerated Collatz states at the
+colliding times.
+-/
+theorem exists_same_iterateT_of_orbitWindowCollision
+    {n : OddNat} {k : ℕ}
+    (hcollision : OrbitWindowCollision n k) :
+    ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ iterateT i n = iterateT j n := by
+  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
+  exact ⟨i, j, hi, hj, hne, iterateT_eq_of_oddOrbitLabel_eq hlabel⟩
+
+/--
+Separated windows have no collision.
+-/
+theorem not_orbitWindowCollision_of_separated
+    {n : OddNat} {k : ℕ}
+    (hsep : OrbitWindowSeparated n k) :
+    ¬ OrbitWindowCollision n k := by
+  intro hcollision
+  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
+  exact (hsep i hi j hj hne) hlabel
+
+/--
+A collision closes the separated-window route as `False`.
+-/
+theorem orbitWindowSeparated_contradiction_of_collision
+    {n : OddNat} {k : ℕ}
+    (hsep : OrbitWindowSeparated n k)
+    (hcollision : OrbitWindowCollision n k) :
+    False :=
+  not_orbitWindowCollision_of_separated hsep hcollision
+
+/--
+Finite observation split: an accelerated Collatz window is either pairwise
+separated, or it contains a collision.
+
+This is not a convergence statement.  It only names the two basic observation
+modes for a finite window.
+-/
+theorem orbitWindowSeparated_or_collision
+    (n : OddNat) (k : ℕ) :
+    OrbitWindowSeparated n k ∨ OrbitWindowCollision n k := by
+  classical
+  by_cases hsep : OrbitWindowSeparated n k
+  · exact Or.inl hsep
+  · right
+    unfold OrbitWindowSeparated OddOrbitLabelsPairwiseSeparated at hsep
+    push Not at hsep
+    rcases hsep with ⟨i, hi, j, hj, hne, hlabel⟩
+    exact ⟨i, j, hi, hj, hne, hlabel⟩
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index ea2f2dea..d17e8324 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -74,23 +74,32 @@ DkMath.Collatz.PetalBridge
 It defines:
 
 ```lean
+OrbitWindow
 oddOrbitLabel
 OddOrbitLabelsPairwiseSeparated
+OrbitWindowSeparated
+OrbitWindowCollision
 ```
 
 where:
 
 ```text
+OrbitWindow n k = Finset.range k
 oddOrbitLabel n i = the natural value of iterateT i n
 ```
 
 The first theorem set is deliberately thin:
 
 ```lean
+orbitWindow_eq_range
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
 oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
 same_iterateT_of_oddOrbitLabel_collision
+exists_same_iterateT_of_orbitWindowCollision
+not_orbitWindowCollision_of_separated
+orbitWindowSeparated_contradiction_of_collision
+orbitWindowSeparated_or_collision
 ```
 
 ## Interpretation
@@ -139,6 +148,18 @@ Collatz orbit segment
   -> either separated segment or collision obstruction
 ```
 
+The current window-level split is:
+
+```text
+OrbitWindowSeparated n k
+or
+OrbitWindowCollision n k
+```
+
+This is only a finite observation split.  It does not prove that a Collatz
+orbit converges or cycles; it merely fixes the two observation modes available
+inside a chosen finite window.
+
 This gives a clean place to attach future hypotheses:
 
 ```text
@@ -153,9 +174,9 @@ orbit collision implies a specific fold/cycle condition
 The next safe steps are:
 
 ```text
-1. Define a Collatz orbit segment as a finite range family.
-2. Add a collision-vs-separated predicate split.
-3. Connect v2_shift_invariant to a Petal address/residue reading.
+1. Connect v2_shift_invariant to a Petal address/residue reading.
+2. Add a window occupation/address transition layer.
+3. Test whether an external label transform can turn orbit labels into carrier labels.
 4. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
 
````
`````
