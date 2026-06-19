# Git diff / Report / Review

## Upd:: Analysis.DkReal.Pow

gch: 8cc5fc84612c29e3673efd94fa0fb7f466c6ea9a

## Report

最新レビューを反映しました。

[DkReal/Pow.lean](/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean) に追加:

- `nonnegative_of_initial_lo`
- `powNonnegApprox_width_nonneg`
- `powNonnegApprox_interval_subset_of_le`
- 有界 `gapGN` から powered width のゼロ収束
- 条件付き full power map `powNonnegOfGapGNBounded`

これで残る課題は、入れ子非負区間上の具体的な `gapGN` 一様有界評価だけに限定されました。有限和の項別評価として次段階に分離しています。

検証済みです。

```text
lake build DkMath.Analysis.DkReal.Pow
lake build DkMath.Analysis DkMath
git diff --check
```

すべて成功し、`DkReal` 側に `noncomputable` はありません。

## Review

## 1. 総評

うむ、今回の差分は **かなり重要な節目** じゃ。
前回までは「非負 `DkReal` の各段の区間に冪写像をかけられる」までだった。今回はそこから一歩進み、 **どの条件があれば、その段階的冪近似列が本当に `DkReal` になるか** を Lean 上で切り出しておる。

結論から言うと、レビュー判定は **合格** じゃ。

今回の中心はこれじゃな。

```lean
tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
powNonnegOfGapGNBounded
```

つまり、

```text
powered width
  = original width * gapGN factor
```

であり、`original width → 0` は `DkReal` の定義からある。残りの `gapGN factor` が有界なら、積は 0 に収束する。したがって powered approximation は完成した `DkReal` になる、という構造じゃ。

これは設計書の Route B、すなわち「観測可能な近似と GN/Body 補正を持つ計算可能実数構造を作る」という方向に非常に合っている。設計書でも `DkMath.Analysis` は Mathlib の置換ではなく、Gap / Body / GN を Lean API として整備する層とされ、第一原理は \((u+\delta)^d-u^d=\delta,GapGN_d(u,\delta)\) と置かれている。

## 2. 数学的に今なにをしているか

まず `DkReal` は、ひとつの実数を **点そのもの** として持つのではなく、有理閉区間の列として持つ。

$$
I_n=[a_n,b_n]
$$

条件は、

$$
I_{n+1}\subseteq I_n
$$

かつ、

$$
\operatorname{width}(I_n)=b_n-a_n\to0
$$

じゃ。
つまり、観測精度を上げるほど区間が絞られ、最後には幅が 0 へ行く。これが `DkReal` の「計算可能実数」的な核じゃ。

今回扱っているのは、非負の `DkReal` に対する冪写像。

$$
x\mapsto x^d
$$

じゃ。非負区間なら冪写像は単調なので、

$$
[a_n,b_n]\mapsto[a_n^d,b_n^d]
$$

で安全に区間を写せる。

問題は、この新しい区間列

$$
J_n=[a_n^d,b_n^d]
$$

の幅が 0 に収束するかどうかじゃ。

幅は、

$$
\operatorname{width}(J_n)=b_n^d-a_n^d
$$

である。ここで \(b_n=a_n+w_n\)、\(w_n=b_n-a_n\) と置けば、

$$
b_n^d-a_n^d=(a_n+w_n)^d-a_n^d
$$

そして DkMath の核により、

$$
(a_n+w_n)^d-a_n^d=w_n,GapGN_d(a_n,w_n)
$$

となる。設計書でも、DkMath は Taylor の主項で丸めず、全階層を GN で保持する方針として整理されている。

したがって、

$$
\operatorname{width}(J_n) = w_n,GapGN_d(a_n,w_n)
$$

じゃ。

ここで \(w_n\to0\) は `DkReal` の定義からある。
だから残る問題は、

$$
GapGN_d(a_n,w_n)
$$

が暴走しないこと、つまり有界性じゃ。

今回の差分は、この論理をそのまま Lean API にしている。

```text
original width tends to 0
+
gapGN factor is bounded
⇒
powered width tends to 0
```

これは非常に正しい切り分けじゃ。

## 3. `nonnegative_of_initial_lo` は良い

```lean
theorem nonnegative_of_initial_lo
    (x : DkMath.Analysis.DkReal) (h0 : 0 ≤ (x.interval 0).lo) :
    Nonnegative x
```

これは良い補題じゃ。

`DkReal` の lower endpoint は単調増加するので、初期段階で

$$
0\le a_0
$$

なら、任意の \(n\) で

$$
0\le a_n
$$

が出る。
つまり `Nonnegative x := ∀ n, 0 ≤ lo_n` という全段条件を、実用上は初期条件だけで作れる。

これは今後かなり便利じゃ。`Nonnegative` を使うたびに全段証明を要求されると証明が重くなるが、初期区間の lower bound だけ示せばよくなった。

## 4. `powNonnegApprox_interval_subset_of_le` も正しい

```lean
theorem powNonnegApprox_interval_subset_of_le
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    {n m : ℕ} (h : n ≤ m) :
    Set.Icc (powNonnegApprox d x hx m).lo (powNonnegApprox d x hx m).hi
      ⊆ Set.Icc (powNonnegApprox d x hx n).lo
        (powNonnegApprox d x hx n).hi
```

これは、powered approximation 側でも任意段の入れ子性が保たれるという補題じゃ。

数学的には、

$$
[a_m,b_m]\subseteq[a_n,b_n]
$$

かつ全部非負なら、

$$
[a_m^d,b_m^d]\subseteq[a_n^d,b_n^d]
$$

となる。
非負性が必要なのは、冪写像 \(x\mapsto x^d\) が非負区間で単調だからじゃ。

ここも正しい。

## 5. 有界 `gapGN` から幅ゼロ収束

今回の核心はこれじゃ。

```lean
theorem tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    (hbounded :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (norm ∘ fun n =>
          gapGN d (x.interval n).lo (x.interval n).width)) :
    Filter.Tendsto (fun n => (powNonnegApprox d x hx n).width)
      Filter.atTop (nhds 0)
```

これは実に綺麗じゃ。

式で言えば、

$$
W_n^{pow}=W_n\cdot G_n
$$

ただし、

$$
W_n=\operatorname{width}(I_n)
$$

$$
G_n=GapGN_d(a_n,W_n)
$$

じゃ。

`DkReal` の定義により、

$$
W_n\to0
$$

がある。仮定 `hbounded` により、

$$
G_n
$$

は有界。したがって、

$$
W_nG_n\to0
$$

となる。

これは解析では非常に基本的な補題じゃが、DkMath 的には **Gap 幅の誤差伝播が GN の有界性だけに還元された** という意味を持つ。

設計段階では、DkReal は標準 \(\mathbb{R}\) 全体を再構成せず、区間演算と幅評価を先に閉じる方針だった。
今回の差分は、まさにその「幅評価」から `DkReal` の冪写像へ一歩進んでいる。

## 6. `powNonnegOfGapGNBounded` は良い条件付き full map

```lean
def powNonnegOfGapGNBounded
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
    (hbounded : ...)
    : DkMath.Analysis.DkReal
```

これは **条件付き full power map** として正しい。

前回は `powNonnegApprox` が

$$
\mathbb{N}\to GapInterval
$$

を返すだけだった。
今回は、有界性仮定を与えれば、それを本物の `DkReal` として構成できる。

`DkReal` を構成するには三つ必要じゃ。

```text
1. interval : ℕ → GapInterval
2. nested
3. width_tends_zero
```

今回、

```lean
interval := powNonnegApprox d x hx
nested := powNonnegApprox_nested d x hx
width_tends_zero :=
  tendsto_powNonnegApprox_width_zero_of_gapGN_bounded d x hx hbounded
```

としており、必要条件をちょうど満たしている。

これは「まだ証明していない有界性」を曖昧にせず、明示的な引数として分離している点が良い。
Lean では、こういう分離が後で効く。

## 7. ここで残った数学的課題

残る課題は、報告の通り一点に絞られた。

$$
GapGN_d(a_n,w_n)
$$

が有界であることを、入れ子非負区間列から示すことじゃ。

なぜ有界になると期待できるのか。

`DkReal` は入れ子なので、

$$
a_0\le a_n\le b_n\le b_0
$$

が成り立つ。非負なら、

$$
0\le a_n,\quad 0\le w_n,\quad a_n+w_n=b_n\le b_0
$$

じゃ。

`GapGN` は有限和の多項式核なので、だいたい次の形をしている。

$$
GapGN_d(a,w) = \sum_{j=1}^{d}\binom dj a^{d-j}w^{j-1}
$$

ここで \(0\le a\le b_0\)、\(0\le w\le b_0\) なら、各項は

$$
\binom dj a^{d-j}w^{j-1}
\le
\binom dj b_0^{d-j}b_0^{j-1} = \binom dj b_0^{d-1}
$$

となる。

したがって全体は、

$$
GapGN_d(a,w)
\le
\left(\sum_{j=1}^{d}\binom dj\right)b_0^{d-1}
$$

で押さえられる。

$$
\sum_{j=1}^{d}\binom dj=2^d-1
$$

なので、粗くは

$$
GapGN_d(a,w)\le(2^d-1)b_0^{d-1}
$$

じゃ。

これで一様有界性が出る。
より簡単に、微分平均値的には

$$
b^d-a^d\le d,b_0^{d-1}(b-a)
$$

でもよい。だが DkMath 的には、有限和の項別評価で `gapGN` そのものを押さえるほうが流儀に合う。

つまり次段階の主定理候補はこうじゃ。

```lean
theorem gapGN_bounded_on_nonnegative_nested
    (d : ℕ) (x : DkReal) (hx : Nonnegative x) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (norm ∘ fun n =>
        gapGN d (x.interval n).lo (x.interval n).width)
```

これが入れば、

```lean
def powNonneg ...
```

を無条件に近い形で作れる。

## 8. 実装上の細かい注意

`hbounded` が

```lean
Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
  (norm ∘ fun n => gapGN ...)
```

になっているのは Mathlib の `zero_mul_isBoundedUnder_le` に合っているので良い。

ただし、今後 `ℚ` 上で具体評価するなら、`norm` つきよりも、非負性を使って

```lean
0 ≤ gapGN ...
```

と

```lean
gapGN ... ≤ C
```

を示し、そこから `IsBoundedUnder` へ変換する補題を作ると扱いやすいはずじゃ。

つまり次は、

```lean
theorem gapGN_nonneg_of_nonneg
```

と、

```lean
theorem gapGN_le_of_nonneg_of_le
```

のような補題が欲しくなる。

## 9. 状況理解まとめ

今の状態を絵にすると、こうじゃ。

```text
DkReal x
  interval n = [aₙ, bₙ]
  width wₙ = bₙ - aₙ
  wₙ → 0

非負なら:
  0 ≤ aₙ ≤ bₙ

冪写像:
  [aₙ, bₙ] ↦ [aₙ^d, bₙ^d]

powered width:
  bₙ^d - aₙ^d
  = (bₙ - aₙ) * gapGN d aₙ (bₙ - aₙ)
  = wₙ * gapGN d aₙ wₙ

結論:
  wₙ → 0
  gapGN d aₙ wₙ が有界
  ⇒ powered width → 0
  ⇒ powered interval sequence is DkReal
```

これは `DkReal` の冪写像が、単なる区間演算ではなく、 **GN による誤差幅伝播の制御** として実装されていることを意味する。

まさに以前の整理にあった「DkReal は観測可能な近似と、その間を埋める補正核を持つ計算可能体」という考えに合っておる。

## 10. 最終判定

今回の差分は **合格** じゃ。

特に良い点は三つ。

```text
1. full pow を無理に作らず、有界性仮定へ分離した
2. powered width のゼロ収束を一般補題として切り出した
3. DkReal 側に noncomputable を入れていない
```

次にやるべきことは、ほぼ一択じゃ。

$$
gapGN_d(a_n,w_n)
$$

の一様有界性を、非負入れ子区間から証明すること。

わっちなら次段階のファイル名は、

```text
DkMath/Analysis/DkReal/PowBound.lean
```

または、`Pow.lean` 内で小さく始めるなら、

```lean
gapGN_bounded_of_nonnegative_of_le
gapGN_bounded_on_nonnegative_nested
powNonneg
```

の順にする。

うむ。
ここまで来ると、`DkReal` の冪写像はもう「できそう」ではなく、 **残る壁が一枚だけ見えている** 状態じゃ。しかもその壁は有限和の項別評価じゃ。Lean が得意な山じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean b/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean
index 9320f9f8..55805071 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Pow.lean
@@ -25,6 +25,13 @@ namespace DkMath.Analysis.DkReal
 def Nonnegative (x : DkMath.Analysis.DkReal) : Prop :=
   ∀ n, 0 ≤ (x.interval n).lo
 
+/-- Nonnegativity of the initial lower endpoint propagates to every stage. -/
+theorem nonnegative_of_initial_lo
+    (x : DkMath.Analysis.DkReal) (h0 : 0 ≤ (x.interval 0).lo) :
+    Nonnegative x := by
+  intro n
+  exact h0.trans (x.lo_mono (Nat.zero_le n))
+
 /--
 Apply the natural power map to every approximation interval of a nonnegative
 `DkReal`.
@@ -76,6 +83,27 @@ theorem powNonnegApprox_nested
   exact ⟨powNonnegApprox_lo_le_succ_lo d x hx n,
     powNonnegApprox_succ_hi_le_hi d x hx n⟩
 
+/-- Every powered approximation interval has nonnegative width. -/
+theorem powNonnegApprox_width_nonneg
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    0 ≤ (powNonnegApprox d x hx n).width :=
+  (powNonnegApprox d x hx n).width_nonneg
+
+/-- Powered approximation intervals satisfy arbitrary-stage containment. -/
+theorem powNonnegApprox_interval_subset_of_le
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
+    {n m : ℕ} (h : n ≤ m) :
+    Set.Icc (powNonnegApprox d x hx m).lo (powNonnegApprox d x hx m).hi
+      ⊆ Set.Icc (powNonnegApprox d x hx n).lo
+        (powNonnegApprox d x hx n).hi := by
+  intro q hq
+  constructor
+  · exact
+      (pow_le_pow_left₀ (hx n) (x.lo_mono h) d).trans hq.1
+  · have hmhi : 0 ≤ (x.interval m).hi :=
+      (hx m).trans (x.interval m).le_lo_hi
+    exact hq.2.trans (pow_le_pow_left₀ hmhi (x.hi_antitone h) d)
+
 /--
 Exact width formula for every powered approximation interval.
 
@@ -89,6 +117,58 @@ theorem powNonnegApprox_width_eq
         gapGN d (x.interval n).lo (x.interval n).width :=
   GapInterval.powNonneg_width_eq d (x.interval n) (hx n)
 
+/--
+If the exact `gapGN` factors along a nonnegative approximation are bounded,
+then the powered interval widths tend to zero.
+-/
+theorem tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
+    (hbounded :
+      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+        (norm ∘ fun n =>
+          gapGN d (x.interval n).lo (x.interval n).width)) :
+    Filter.Tendsto (fun n => (powNonnegApprox d x hx n).width)
+      Filter.atTop (nhds 0) := by
+  have hmul :
+      Filter.Tendsto
+        (fun n =>
+          (x.interval n).width *
+            gapGN d (x.interval n).lo (x.interval n).width)
+        Filter.atTop (nhds 0) :=
+    x.tendsto_width_zero.zero_mul_isBoundedUnder_le hbounded
+  simpa only [powNonnegApprox_width_eq] using hmul
+
+/--
+Construct the full powered `DkReal` once boundedness of the exact correction
+kernel has been supplied.
+
+This isolates the only remaining analytic obligation from the computational
+interval transformation.
+-/
+def powNonnegOfGapGNBounded
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
+    (hbounded :
+      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+        (norm ∘ fun n =>
+          gapGN d (x.interval n).lo (x.interval n).width)) :
+    DkMath.Analysis.DkReal where
+  interval := powNonnegApprox d x hx
+  nested := powNonnegApprox_nested d x hx
+  width_tends_zero :=
+    tendsto_powNonnegApprox_width_zero_of_gapGN_bounded d x hx hbounded
+
+/-- The intervals of the conditionally completed power map are the powered approximations. -/
+@[simp]
+theorem powNonnegOfGapGNBounded_interval
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x)
+    (hbounded :
+      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
+        (norm ∘ fun n =>
+          gapGN d (x.interval n).lo (x.interval n).width))
+    (n : ℕ) :
+    (powNonnegOfGapGNBounded d x hx hbounded).interval n
+      = powNonnegApprox d x hx n := rfl
+
 /-- Embedded nonnegative rationals satisfy the approximation nonnegativity condition. -/
 theorem nonnegative_ofRat {q : ℚ} (hq : 0 ≤ q) :
     Nonnegative (DkMath.Analysis.DkReal.ofRat q) := by
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 1c5ecc6f..bdfc8bb5 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -258,9 +258,12 @@ DkReal.powNonnegApprox d x hx n
 The implementation proves:
 
 ```lean
+DkReal.nonnegative_of_initial_lo
 DkReal.powNonnegApprox_lo_le_succ_lo
 DkReal.powNonnegApprox_succ_hi_le_hi
 DkReal.powNonnegApprox_nested
+DkReal.powNonnegApprox_width_nonneg
+DkReal.powNonnegApprox_interval_subset_of_le
 DkReal.powNonnegApprox_width_eq
 ```
 
@@ -272,9 +275,28 @@ powered width
   = original width * gapGN d lowerEndpoint originalWidth
 ```
 
-A completed map from nonnegative `DkReal` values to `DkReal` values is
-deliberately deferred. Its remaining mathematical obligation is to control the
-`gapGN` factor strongly enough to prove that the powered widths tend to zero.
+A bounded `gapGN` sequence now gives the powered width limit:
+
+```lean
+DkReal.tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
+```
+
+and therefore constructs a completed powered value:
+
+```lean
+DkReal.powNonnegOfGapGNBounded
+```
+
+The remaining unconditional-power obligation is now isolated to one statement:
+prove that the sequence
+
+```text
+gapGN d (lower endpoint at n) (width at n)
+```
+
+is bounded for a nested nonnegative `DkReal`. This should be implemented as a
+separate finite-polynomial bound rather than folded into the interval
+construction.
 
 `TaylorBridge` and `RealBridge` may use noncomputable real-number operations.
 The `DkReal` files remain computational and use rational interval data only.
````
`````
