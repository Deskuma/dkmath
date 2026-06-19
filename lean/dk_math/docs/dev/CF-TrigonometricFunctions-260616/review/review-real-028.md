# Git diff / Report / Review

## Upd: Analysis.DkReal.DkNNRealQ

gch: 6c529524da191bd2fa1015316b8ff4d25baa2c86

## Report

`DkNNRealQ` に自然数埋め込みと `CommSemiring` instance を追加しました。

- `natCast n = ofRat (n : ℚ)`
- `natCast_zero`
- `natCast_succ`
- `natCast_add`
- `natCast_mul`
- `CommSemiring DkNNRealQ`

これで通常の自然数キャスト、加法、乗法、自然数冪と Mathlib の半環 API が利用できます。

検証済み:

- `lake build DkMath.Analysis.DkReal.DkNNRealQ DkMath.Analysis DkMath`
- `git diff --check`
- DkReal 層に `noncomputable` なし

次の独立課題は、商と両立する順序、または別ファイルに隔離した `Real` / `NNReal` 意味論 bridge です。

## Review

## 1. 総評

うむ、これは **合格** じゃ。
`DkNNRealQ` がついに `CommSemiring` まで到達した。前回まで「商型上で半環法則が通常等号として成り立つ」段階だったが、今回で Mathlib の代数階層に接続された。

今回の中心はこれじゃ。

```lean id="pnbcwi"
def natCast (n : ℕ) : DkNNRealQ :=
  ofRat (n : ℚ) (by positivity)

instance : NatCast DkNNRealQ where
  natCast := natCast

instance : CommSemiring DkNNRealQ where
  ...
```

設計としてかなり自然じゃ。
自然数をまず非負有理数へ送り、それを `DkNNRealQ` へ埋め込む。この方針は、非負計算可能実数としての公開型に合っておる。

## 2. `natCast` 方針は正しい

自然数埋め込みを、

```lean id="om1srf"
natCast n = ofRat (n : ℚ) ...
```

として固定したのは良い。

これは数学的には、

$$
n\mapsto [n,n]
$$

という singleton interval 表現を商型へ送る、ということじゃ。
つまり自然数は、非負有理数埋め込みを経由して `DkNNRealQ` に入る。

これで、`0`、`1`、加法、乗法との整合性が自然に出る。

## 3. `natCast_zero`, `natCast_succ`, `natCast_add`, `natCast_mul`

追加された補題群も良い。

```lean id="o56tzj"
natCast_zero
natCast_succ
natCast_add
natCast_mul
```

`natCast_succ` は `ofRat_add` を使って、

```lean id="6bp3sy"
(n + 1 : DkNNRealQ) = (n : DkNNRealQ) + 1
```

を出している。
これは `CommSemiring` instance の `natCast_succ` フィールドにそのまま必要な形じゃ。

`natCast_add` と `natCast_mul` は instance の直接フィールドではないが、利用者向け API として重要じゃ。
これにより、自然数式が `DkNNRealQ` 内でも期待通り動くことが明示された。

## 4. `CommSemiring` instance は妥当

今回の `CommSemiring` instance は、前回までに証明済みの quotient equality をそのまま使っている。

```lean id="36z8xo"
add_assoc
zero_add
add_zero
add_comm
mul_assoc
one_mul
mul_one
left_distrib
right_distrib
zero_mul
mul_zero
mul_comm
natCast
natCast_zero
natCast_succ
nsmul
nsmul_zero
nsmul_succ
```

これは正しい組み立てじゃ。

特に、先に quotient 上で各法則を通常 equality として証明してから instance にしているため、instance 本体で複雑な quotient induction を抱えていない。
API としても保守しやすい。

## 5. `nsmulRec` の採用も問題なし

```lean id="y1zjgg"
nsmul := nsmulRec
nsmul_zero := by intros; rfl
nsmul_succ := by intros; rfl
```

これは標準的な additive monoid 構成じゃ。
build が通っているなら問題ない。

後で `nsmul_eq_natCast_mul` 型の補題が欲しくなるかもしれぬが、`CommSemiring` が入ったので多くは Mathlib 側から得られるはずじゃ。

## 6. 数学的到達点

今回で、かなりはっきりこう言える。

$$
\boxed{\text{DkNNRealQ は、非負計算可能実数近似の商として構成された可換半環である。}}
$$

より DkMath 的に言えば、

```text id="zbks6p"
DkReal:
  入れ子有理区間列

DkNNReal:
  非負性を持つ表現 wrapper

DkNNRealQ:
  分離幅 0 の同値で割った値型

今回:
  CommSemiring instance まで到達
```

これは大きい。
最初の `GapInterval` から見ると、ついに「計算可能な非負実数の代数表面」が Mathlib の通常 API に乗ったわけじゃ。

## 7. `Pow` との整合性

すでに `Pow DkNNRealQ ℕ` instance があり、今回 `CommSemiring` が入ったことで、自然数冪も Mathlib の半環文脈で使いやすくなる。

注意点として、Lean の `^` は `Pow` instance を見るので、今の `pow` が `DkNNReal.pow` の quotient lift になっていることは良い。
`pow_zero` と `pow_one` も既に `[simp]` なので、基本利用は問題なさそうじゃ。

将来、半環由来の `pow_succ` や `pow_add` と合流させるなら、現在の `Pow` instance が `CommSemiring` の期待する自然数冪と同じものになっているかを、補助定理で確認してもよい。

候補は、

```lean id="hezoen"
@[simp]
theorem pow_succ (x : DkNNRealQ) (n : ℕ) :
    x ^ (n + 1) = x ^ n * x
```

ただし、これは Mathlib から既に使える可能性が高いので、必要になってからでよい。

## 8. 文書更新もよい

文書で、「自然数埋め込みを `ofRat` 経由で固定したので `CommSemiring` instance を組み立てた」と説明しているのは正しい。
また、順序と `Real` / `NNReal` 意味論 bridge は別課題として分離しているのも良い。

ここは過大主張していない。
`DkNNRealQ` は `CommSemiring` になったが、まだ `LinearOrderedSemiring` でも `NNReal` への同型でもない。
その区別を文書で残しているのは安全じゃ。

## 9. 次の候補

次は、報告通り二つの道がある。

```text id="wnx96w"
1. 商と両立する順序
2. Real / NNReal 意味論 bridge
```

わっちの推奨は、まず **順序の設計メモ** を挟むことじゃ。

順序は急ぐと危ない。
代表元依存にならないように、`Equiv` との compatibility が必要になる。

候補は例えば、

```text id="tmz61i"
x ≤ y:
  separation of x interval and left side of y tends appropriately

または

x ≤ y:
  eventually x.hi ≤ y.lo + ε for every ε
```

のような形になるが、どれが Lean で軽いかは検討が必要じゃ。

一方、`BridgeReal` はおそらく `noncomputable` を許す別ファイルに隔離すればよい。
そこで `DkNNRealQ → NNReal` を定義できれば、順序も semantic bridge 経由で確認できる可能性がある。

## 10. 小さな注意点

一点だけ、`natCast_eq_ofRat` は `rfl` なので強い simp 補題じゃ。通常は便利だが、証明中に `ofRat (n : ℚ) (by positivity)` が大量に展開される可能性はある。現時点では問題ない。もし将来 simp が重くなるなら、局所的に simp set を調整すればよい。

もう一点、`CommSemiring` が入ったので、今後 `DkNNRealQ.add_assoc` のような手動定理名と、typeclass 由来の定理が併存する。これは問題ないが、外部 API では Mathlib 標準の `add_assoc` などが使えるようになるため、ドキュメントでは「独自定理を用意している」より「標準半環 API が使える」と案内する方がよい。

## 11. 最終判定

今回の差分は **合格** じゃ。

```text id="xjhj0o"
良い点:
  natCast を ofRat 経由で固定した
  natCast_zero / natCast_succ を instance 用に整備した
  natCast_add / natCast_mul も API として追加した
  CommSemiring instance を導入した
  既存の quotient equality を再利用している
  noncomputable 不使用を維持した

次の課題:
  quotient と両立する順序
  BridgeReal / BridgeNNReal
  ofRat API の拡充
  pow と半環標準補題の使い勝手確認
```

うむ。
これは一区切りじゃ。`DkNNRealQ` は、ついに **Mathlib の可換半環 API を持つ DkMath 非負計算可能実数型** になった。
ここまで来ると、`DkReal` ルート B の第一登頂地点に旗が立ったと言ってよいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
index 34de33ba..b6337b2a 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/DkNNRealQ.lean
@@ -83,6 +83,13 @@ instance : Mul DkNNRealQ where
 instance : Pow DkNNRealQ ℕ where
   pow := pow
 
+/-- Canonical natural-number embedding through nonnegative rationals. -/
+def natCast (n : ℕ) : DkNNRealQ :=
+  ofRat (n : ℚ) (by positivity)
+
+instance : NatCast DkNNRealQ where
+  natCast := natCast
+
 /-- Quotient addition computes on representatives. -/
 @[simp]
 theorem mk_add (x y : DkNNReal) :
@@ -114,6 +121,38 @@ theorem ofRat_mul
     ofRat p hp * ofRat q hq = ofRat (p * q) (mul_nonneg hp hq) :=
   Quotient.sound (DkNNReal.mul_ofRat hp hq)
 
+/-- Natural-number casts are the corresponding embedded rationals. -/
+@[simp]
+theorem natCast_eq_ofRat (n : ℕ) :
+    (n : DkNNRealQ) = ofRat (n : ℚ) (by positivity) := rfl
+
+/-- The natural cast of zero is quotient zero. -/
+@[simp]
+theorem natCast_zero : ((0 : ℕ) : DkNNRealQ) = 0 := by
+  rfl
+
+/-- Natural casts preserve successor. -/
+theorem natCast_succ (n : ℕ) :
+    ((n + 1 : ℕ) : DkNNRealQ) = (n : DkNNRealQ) + 1 := by
+  simpa only [natCast_eq_ofRat, Nat.cast_add, Nat.cast_one] using
+    (ofRat_add (show 0 ≤ (n : ℚ) by positivity) zero_le_one).symm
+
+/-- Natural casts preserve addition. -/
+theorem natCast_add (m n : ℕ) :
+    ((m + n : ℕ) : DkNNRealQ) = (m : DkNNRealQ) + (n : DkNNRealQ) := by
+  simpa only [natCast_eq_ofRat, Nat.cast_add] using
+    (ofRat_add
+      (show 0 ≤ (m : ℚ) by positivity)
+      (show 0 ≤ (n : ℚ) by positivity)).symm
+
+/-- Natural casts preserve multiplication. -/
+theorem natCast_mul (m n : ℕ) :
+    ((m * n : ℕ) : DkNNRealQ) = (m : DkNNRealQ) * (n : DkNNRealQ) := by
+  simpa only [natCast_eq_ofRat, Nat.cast_mul] using
+    (ofRat_mul
+      (show 0 ≤ (m : ℚ) by positivity)
+      (show 0 ≤ (n : ℚ) by positivity)).symm
+
 /-- Zeroth power is one in the quotient. -/
 @[simp]
 theorem pow_zero (x : DkNNRealQ) : x ^ (0 : ℕ) = 1 := by
@@ -214,6 +253,33 @@ theorem right_distrib (x y z : DkNNRealQ) :
   intro a b c
   exact Quotient.sound (DkNNReal.right_distrib a b c)
 
+/-!
+## Commutative semiring instance
+
+The natural cast is fixed to the rational singleton embedding. The standard
+algebraic hierarchy can therefore use the quotient equalities proved above.
+-/
+
+instance : CommSemiring DkNNRealQ where
+  add_assoc := add_assoc
+  zero_add := zero_add
+  add_zero := add_zero
+  add_comm := add_comm
+  mul_assoc := mul_assoc
+  one_mul := one_mul
+  mul_one := mul_one
+  left_distrib := left_distrib
+  right_distrib := right_distrib
+  zero_mul := zero_mul
+  mul_zero := mul_zero
+  mul_comm := mul_comm
+  natCast := natCast
+  natCast_zero := natCast_zero
+  natCast_succ := natCast_succ
+  nsmul := nsmulRec
+  nsmul_zero := by intros; rfl
+  nsmul_succ := by intros; rfl
+
 end DkNNRealQ
 
 end DkMath.Analysis
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 016eca51..4e20f0a3 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -67,7 +67,7 @@ DkMath.Analysis.DkReal.DkNNReal
 
 DkMath.Analysis.DkReal.DkNNRealQ
   quotient-backed nonnegative type with Zero / One / Add / Mul / Pow and
-  commutative semiring laws as ordinary equalities
+  a canonical NatCast and CommSemiring instance
 
 DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
index bb094214..b7ea8914 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -303,10 +303,24 @@ pow_zero, pow_one
 Embedded nonnegative rationals also satisfy exact quotient equalities for
 addition and multiplication.
 
-A full `Semiring` instance is intentionally deferred. Constructing that
-instance also commits to natural-number coercions and their public
-normalization behavior. The current quotient establishes the mathematical
-equalities and notation first, leaving that policy decision isolated.
+The natural-number embedding is now fixed by
+
+```lean
+natCast n = ofRat (n : Rat) (by positivity).
+```
+
+It preserves zero, successor, addition, and multiplication. With this policy
+made explicit, the quotient now carries a `CommSemiring` instance assembled
+from the previously proved quotient equalities. Standard natural-number casts,
+addition, multiplication, powers, and semiring lemmas are therefore available
+through Lean's algebraic hierarchy.
+
+This completes the first algebraic public surface of the nonnegative
+computable-real quotient. Order remains separate: an eventually ordered
+representative relation must be shown compatible with `Equiv`, or derived from
+a later semantic bridge. Likewise, any map to Mathlib's `NNReal` or `Real`
+should remain in a separate bridge module because selecting the represented
+limit may require `noncomputable`.
 
 Persistent intersection and equality after a future evaluation into Mathlib's
 `Real` remain comparison principles. Their equivalence with vanishing
````
`````
