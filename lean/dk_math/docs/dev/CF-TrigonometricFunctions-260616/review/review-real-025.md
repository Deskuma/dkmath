# Git diff / Report / Review

## Upd: Analysis.DkReal.Equiv, PowBound

gch: 74d1b3964f621ee21989fc421177057c04bec4d1

## Report

`powNonneg` の congruence を実装しました。

追加した主要定理:

- `nonnegative_powNonneg`
- `equiv_of_interval_eq`
- `powNonneg_succ_interval`
- `equiv_powNonneg`

証明は新たな Lipschitz 評価を導入せず、

```text
x^(d+1) = x^d * x
```

と既存の `equiv_mulNonneg` を指数帰納法で適用しています。`gapGN` は冪の幅収束、乗法反復は表現同値の保存、という役割分担です。

検証済み:

- `lake build DkMath.Analysis.DkReal.PowBound DkMath.Analysis.DkReal.Equiv DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

次の設計候補は、Setoid の quotient または非負値専用 wrapper による半環 API です。

## Review

## 1. 総評

うむ、今回も **合格** じゃ。
これはかなり良い閉じ方をしておる。`powNonneg` の congruence を、直接 `gapGN` の絶対値評価で証明せず、既に確立した `equiv_mulNonneg` へ還元している。証明再利用として、とても Lean 向きじゃ。

今回の追加は主にこれじゃな。

```lean id="x91nqu"
nonnegative_powNonneg
equiv_of_interval_eq
powNonneg_succ_interval
equiv_powNonneg
```

報告では、`x^(d+1) = x^d * x` を使い、`equiv_mulNonneg` を指数帰納法で適用したとある。これは、`gapGN` を「冪写像を DkReal として構成する幅収束の核」に残し、congruence 側は「乗法の反復」で処理するという役割分担になっておる。これは良い設計じゃ。

## 2. 今回の数学的意味

今回閉じたのは、次の主張じゃ。

$$
x\sim x'\quad\Rightarrow\quad x^d\sim {x'}^d
$$

ただし、非負 `DkReal` 領域での自然数冪じゃ。

これで、`Equiv` に対して安定な演算は次の三つになった。

```text id="crirxz"
add
mulNonneg
powNonneg
```

つまり、表現を取り替えても、加法・非負乗法・自然数冪の結果は同じ表現値を与える。
これは quotient / wrapper へ進むための大きな条件じゃ。

## 3. `nonnegative_powNonneg` は必要な補題

```lean id="hogpyr"
theorem nonnegative_powNonneg
    (d : ℕ) {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
    Nonnegative (powNonneg d x hx)
```

これは今回の帰納法に必要な補題じゃな。
`powNonneg d x hx` を次の段階で `mulNonneg` の左因子にするには、それ自体が非負である必要がある。

数学的には、非負数の自然数冪は非負、というだけじゃ。
しかし Lean API としては、これがないと `powNonneg_succ_interval` と `equiv_mulNonneg` をきれいに繋げられない。

よい追加じゃ。

## 4. `equiv_of_interval_eq` は便利

```lean id="asnh6c"
theorem equiv_of_interval_eq
    {x y : DkMath.Analysis.DkReal}
    (hxy : ∀ n, x.interval n = y.interval n) :
    Equiv x y
```

これは今後かなり使う補題じゃ。
`DkReal` の生の構造体等号ではなく、全段の interval が一致すれば `Equiv` で同じ、という道を作っている。

今回の `powNonneg_succ_interval` のように、stagewise に一致する補題を `Equiv` へ持ち上げるときに使える。
この形は安全じゃ。`DkReal` の証明フィールドの違いを無視して、観測区間列の一致だけで表現同値へ行ける。

## 5. `powNonneg_succ_interval` の方針は良い

```lean id="nv4t0h"
theorem powNonneg_succ_interval
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonneg (d + 1) x hx).interval n
      =
    (mulNonneg (powNonneg d x hx) x
        (nonnegative_powNonneg d hx) hx).interval n
```

これは非常に良い補題じゃ。

各段で見れば、

$$
a^{d+1}=a^d a
$$

であり、上端でも同じ。

この補題があることで、`powNonneg` congruence を「冪専用の解析評価」ではなく、「乗法 congruence の反復」として処理できる。
Lean 的には、これはかなり強い分解じゃ。

## 6. `equiv_powNonneg` の証明構造

今回の主定理はこれじゃ。

```lean id="j218ro"
theorem equiv_powNonneg
    (d : ℕ) {x x' : DkMath.Analysis.DkReal}
    (hx : Nonnegative x) (hx' : Nonnegative x')
    (hxx' : Equiv x x') :
    Equiv (powNonneg d x hx) (powNonneg d x' hx')
```

証明は指数帰納法。

0 乗では、両方とも singleton \(1\) の区間列になるので `equiv_of_interval_eq` で閉じる。

後続ステップでは、

$$
x^{d+1}=x^d x
$$

を使い、

```lean id="m90gth"
equiv_mulNonneg
```

へ渡している。

これは正しい。
しかも、`gapGN` の符号付き差分評価や Lipschitz 評価を新たに作っていない。これは重要じゃ。

## 7. `gapGN` の役割分担が美しい

今回の文書更新で述べている通り、`gapGN` は冪写像を構成する段階では不可欠じゃ。
非負冪の幅収束では、powered width を `wₙ * gapGN d aₙ wₙ` と分解し、`gapGN` の有界性で `DkReal` として閉じた。これは既存 milestone にも明記されている。

しかし、いったん `powNonneg` が構成され、`mulNonneg` が `Equiv` と両立することが証明されたなら、冪の congruence は乗法反復で済む。

つまり役割はこう分かれた。

```text id="k1offj"
gapGN:
  powNonneg が DkReal として成立するための幅収束を担当

mulNonneg congruence:
  powNonneg が Equiv を保つことを指数帰納法で担当
```

この分離はとても良い。
同じ数学を二重に証明せず、既存構造を組み上げている。

## 8. import 構成も問題なさそう

`Equiv.lean` が `PowBound` と `Arithmetic` を import する形になった。
依存関係としては、

```text id="zpvdvk"
PowBound:
  powNonneg と nonnegative_powNonneg

Arithmetic:
  add / mulNonneg / equiv_mulNonneg の対象演算

Equiv:
  Setoid と congruence 群
```

という配置になる。

`Arithmetic` が `PowBound` に依存していないなら、循環は起きない。今回の差分を見る限り、`Equiv` が両方を集約する形で自然じゃ。

## 9. 現在の到達点

ここまでで、`DkReal` の非負領域はかなり強い状態になった。

```text id="zht9zn"
Equiv:
  Setoid

add:
  Equiv-compatible

mulNonneg:
  Equiv-compatible

powNonneg:
  Equiv-compatible
```

数学的には、

$$
DkReal_{\ge0}/\sim
$$

上で、加法・乗法・自然数冪が well-defined になった、というところまで来ている。

もちろん、まだ quotient 自体を作っていないので、正式な `Semiring` instance ではない。
しかし、その前提条件のかなり大きな部分は揃った。

## 10. 次の設計候補

報告の通り、次は二択じゃ。

```text id="w6j1ni"
1. Setoid quotient を作る
2. 非負値専用 wrapper を作る
```

わっちの推奨は、まず **wrapper** じゃ。

いきなり quotient に進むと、Lean の `Quotient.lift` と proof irrelevance 周りで API が重くなる可能性がある。
一方で、非負値専用 wrapper は次のように扱える。

```lean id="5ya51v"
structure DkNNReal where
  val : DkMath.Analysis.DkReal
  nonneg : Nonnegative val
```

そして `DkNNReal` 側で `Equiv` を定義するか、`DkReal.Equiv val val` を持ち上げる。
その後で quotient するなら、

```lean id="hlcwjb"
Quotient DkNNReal.equivSetoid
```

のように進める。

これなら、`mulNonneg` のたびに `hx` と `hy` を持ち回る負担が減る。
非負半環 API を作るなら、こちらの方が見通しが良い。

## 11. 小さな注意点

`powNonneg_succ_interval` は `simp [pow_succ]` で閉じている。これは現時点では良い。
ただ、将来 `simp` が重くなった場合は、端点ごとの補題に分ける選択肢もある。

```lean id="cxxqpn"
powNonneg_succ_lo
powNonneg_succ_hi
```

今は不要じゃが、後で `simp` が深く展開しすぎるようなら検討でよい。

もう一点、`equiv_powNonneg` は指数帰納法で非常に綺麗に閉じているので、将来 quotient 上で自然数冪を定義するとき、この定理をそのまま `Quotient.lift` の well-defined proof として使えるはずじゃ。

## 12. 最終判定

今回の差分は **合格** じゃ。

```text id="yc9kfg"
良い点:
  powNonneg congruence を指数帰納法で閉じた
  新規 Lipschitz 評価を避けた
  既存 equiv_mulNonneg を再利用した
  gapGN の役割を幅収束側に限定した
  DkReal 層に noncomputable を入れていない
  quotient / wrapper の前提がさらに揃った

残る課題:
  DkNNReal wrapper または quotient 設計
  quotient 上の add / mul / pow API
  非負半環法則の quotient 版
  BridgeReal との意味論接続
```

うむ。
これで `DkReal` の非負領域は、かなりはっきりと **表現同値つきの計算可能半環候補** になった。
次に wrapper か quotient を切れば、今まで積んできた `add`、`mulNonneg`、`powNonneg` が、いよいよ数学的な演算として表へ出てくるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
index ff96b6d0..38f4c842 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Equiv.lean
@@ -4,6 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
+import DkMath.Analysis.DkReal.PowBound
 import DkMath.Analysis.DkReal.Arithmetic
 
 #print "file: DkMath.Analysis.DkReal.Equiv"
@@ -80,6 +81,14 @@ theorem equiv_of_eq
   subst y
   exact equiv_refl x
 
+/-- Pointwise equality of approximation intervals implies representation equivalence. -/
+theorem equiv_of_interval_eq
+    {x y : DkMath.Analysis.DkReal}
+    (hxy : ∀ n, x.interval n = y.interval n) :
+    Equiv x y := by
+  simp only [Equiv, hxy, GapInterval.separation_self]
+  exact tendsto_const_nhds
+
 /-!
 ## Compatibility with addition
 
@@ -243,4 +252,61 @@ theorem equiv_mulNonneg_right
     Equiv (mulNonneg x y hx hy) (mulNonneg x y' hx hy') :=
   equiv_mulNonneg hx hx hy hy' (equiv_refl x) hyy'
 
+/-!
+## Compatibility with natural powers
+
+Natural power congruence is obtained from multiplicative congruence by
+induction on the exponent. This avoids introducing a signed increment into
+`gapGN`: successor powers are stagewise the product of the preceding power and
+the original approximation.
+-/
+
+/--
+The successor power agrees stagewise with multiplying the preceding power by
+the original nonnegative approximation.
+-/
+theorem powNonneg_succ_interval
+    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonneg (d + 1) x hx).interval n
+      =
+    (mulNonneg (powNonneg d x hx) x
+        (nonnegative_powNonneg d hx) hx).interval n := by
+  apply GapInterval.ext <;>
+    simp [powNonneg, powNonnegApprox, mulNonneg, mulNonnegApprox, pow_succ]
+
+/-- Natural powers preserve representation equivalence on the nonnegative domain. -/
+theorem equiv_powNonneg
+    (d : ℕ) {x x' : DkMath.Analysis.DkReal}
+    (hx : Nonnegative x) (hx' : Nonnegative x')
+    (hxx' : Equiv x x') :
+    Equiv (powNonneg d x hx) (powNonneg d x' hx') := by
+  induction d with
+  | zero =>
+      apply equiv_of_interval_eq
+      intro n
+      rw [powNonneg_zero_interval, powNonneg_zero_interval]
+  | succ d ih =>
+      have hmul :
+          Equiv
+            (mulNonneg (powNonneg d x hx) x
+              (nonnegative_powNonneg d hx) hx)
+            (mulNonneg (powNonneg d x' hx') x'
+              (nonnegative_powNonneg d hx') hx') :=
+        equiv_mulNonneg
+          (nonnegative_powNonneg d hx) (nonnegative_powNonneg d hx')
+          hx hx' ih hxx'
+      have hleft :
+          Equiv
+            (powNonneg (d + 1) x hx)
+            (mulNonneg (powNonneg d x hx) x
+              (nonnegative_powNonneg d hx) hx) :=
+        equiv_of_interval_eq (powNonneg_succ_interval d x hx)
+      have hright :
+          Equiv
+            (mulNonneg (powNonneg d x' hx') x'
+              (nonnegative_powNonneg d hx') hx')
+            (powNonneg (d + 1) x' hx') :=
+        equiv_symm (equiv_of_interval_eq (powNonneg_succ_interval d x' hx'))
+      exact equiv_trans (equiv_trans hleft hmul) hright
+
 end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
index f0cdcc96..1c668042 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
@@ -161,4 +161,11 @@ theorem powNonneg_one_interval
     (powNonneg 1 x hx).interval n = x.interval n := by
   apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]
 
+/-- Natural powers of a nonnegative `DkReal` remain nonnegative. -/
+theorem nonnegative_powNonneg
+    (d : ℕ) {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
+    Nonnegative (powNonneg d x hx) := by
+  intro n
+  exact pow_nonneg (hx n) d
+
 end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 55fb97e2..1d37acb2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -59,7 +59,7 @@ DkMath.Analysis.DkReal.Arithmetic
 
 DkMath.Analysis.DkReal.Equiv
   vanishing interval separation, representation setoid, endpoint convergence,
-  and additive/nonnegative multiplicative congruence
+  and additive, nonnegative multiplicative, and natural-power congruence
 
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index b3c14dd6..1ac6af4d 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -209,9 +209,35 @@ Finally, interval separation is bounded by the absolute difference between
 the product lower endpoints. This gives `equiv_mulNonneg` and its one-sided
 variants without evaluating either representation as a Mathlib real number.
 
-The next arithmetic congruence target is `powNonneg`. It should follow from
-the same endpoint-convergence principle together with a uniform bound for the
-finite `gapGN` correction factor.
+Natural powers now also preserve representation equivalence through
+`equiv_powNonneg`. The proof does not require a new absolute-value estimate for
+`gapGN`. Instead it uses the algebraic recursion
+
+```text
+x^(d+1) = x^d * x
+```
+
+at every approximation stage and applies `equiv_mulNonneg` inductively. This
+keeps the congruence proof inside the already established nonnegative
+multiplicative structure, while `gapGN` remains responsible for the separate
+width-convergence proof that constructs `powNonneg`.
+
+The general interval lemma
+
+```lean
+separation_le_abs_lo_sub_lo
+```
+
+is the final bridge in both multiplication and power arguments: proving
+convergence of lower-endpoint differences is sufficient to prove vanishing
+interval separation. This implication depends on each `GapInterval` being a
+valid ordered closed interval; it is not a generic fact about arbitrary pairs
+of endpoint sequences.
+
+At this point addition, nonnegative multiplication, and natural powers all
+respect the representation setoid. The next design question is whether to
+introduce a quotient or a dedicated wrapper for the nonnegative computable
+semiring API.
 
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
````
`````
