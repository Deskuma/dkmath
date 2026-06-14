# Git diff / Report / Review

## Add: Petal.BezoutBridge

gch: a07382619c5207d9d0100fc4d73172f3c1a3831b

## Report

`DkMath.Petal.BezoutBridge` を追加しました。

主な追加内容は [BezoutBridge.lean](/lean/dk_math/DkMath/Petal/BezoutBridge.lean:1) です。既存の根本定理を再証明せず、Petal 側から読める名前として次を置いています。

- `cosmicBody_eq_boundary_mul_GN`
- `primitivePrimeFactor_dvd_GN_of_cosmicBoundary`
- `primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary`
- `prime_not_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp`
- `padicValNat_boundary_GN_gcd_eq_zero_of_coprime_of_not_dvd_exp`
- `not_primePow_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp`
- `anchoredGNCarrier_of_primitivePrimeFactor`
- `anchoredGNCarrier_of_bodyPrimitivePrimeFactor`

また [Petal.lean](/lean/dk_math/DkMath/Petal.lean:16) に公開 import を追加しました。

検証済みです。

```text
lake build DkMath.Petal.BezoutBridge
lake build DkMath.Petal
git diff --check -- lean/dk_math/DkMath/Petal.lean lean/dk_math/DkMath/Petal/BezoutBridge.lean
```

すべて成功。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回の追加由来ではない既存警告です。

## Review

うむ。これは **merge 可** じゃ。
今回の `Petal.BezoutBridge` は、主張を膨らませず、既存の `PrimitiveBeam` / `UniqueFactorizationGN` / `Anchor` を Petal 側の語彙で読み直す **薄い橋** としてよくできておる。

DkMath の既存方針では、\((x+u)^d-u^d=x\,GN_d(x,u)\) を整数宇宙の核として、可除性・p進付値・primitive factor・Zsigmondy へ渡す設計になっているので、今回の橋はその線に素直に乗っている。fileciteturn1file7 また、GN は差冪構造の境界因子を外した Beam / Tail 側として整理されており、可除性・p進付値・原始素因子解析の基本対象とされている。fileciteturn1file12

## 1. レビュー結論

**Blocking issue は見当たらぬ。**

特に良い点はここじゃ。

- `cosmicBody_eq_boundary_mul_GN` で Petal 側の言葉として
  \[
  (x+u)^d-u^d=x\,GN_d(x,u)
  \]
  を明示した。
- primitive witness が boundary を避けて `GN` 側へ移る、という読みを `primitivePrimeFactor_dvd_GN_of_cosmicBoundary` / `primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary` として置いた。
- `gcd(boundary, GN)` に現れる素因子は \(d\) 側の例外に限られる、という Bezout 風分離を Petal 名で読めるようにした。
- 最後に `AnchoredGNCarrier` へ包んだので、Petal の anchor / carrier 語彙と primitive witness が接続された。

これはかなり重要じゃ。
「原始素因子がある」だけではなく、 **その原始素因子が Petal/GN 面のどこに観測されるか** を theorem 名で指せるようになった。

## 2. 設計評価

`BezoutBridge.lean` という名前は少し強く見えるが、ファイルコメントで

> new Bezout theorem ではなく Petal-facing interpretation

と明確に断っているので安全じゃ。ここはよい判断。今後、理想論的 Bezout や Bézout domain 側へ拡張しても、今回のファイルは「gcd/境界分離の読み替え層」として残せる。

import 方向も自然じゃ。

```lean
import DkMath.Petal.Anchor
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.UniqueFactorizationGN
```

Petal 側の anchor を終点にしつつ、数論本体は `NumberTheory` から借りる形なので、循環依存を作りにくい。`Petal.lean` でも `Anchor` の後に `BezoutBridge` を置いており、公開順も物語として通っている。

## 3. Lean 実装上の細かい所感

`cosmicBody_eq_boundary_mul_GN` は良い薄い wrapper じゃ。
`hx : 0 < x` から `u < x + u` を作り、既存の `pow_sub_pow_factor_cosmic_N` に渡す流れはきれい。

ただし、数学的には \(x=0\) でも

\[
(x+u)^d-u^d=0=x\,GN_d(x,u)
\]

は成り立つはずじゃから、将来ほしければ全域版を別 lemma として足せる。

```lean
theorem cosmicBody_eq_boundary_mul_GN_total
    {d x u : ℕ} (hd : 0 < d) :
    (x + u) ^ d - u ^ d = x * GN d x u := ...
```

ただ、既存下層 theorem が `b < a` を要求するなら、今の `hx : 0 < x` 版は十分に堅い。急いで一般化しなくてよい。

## 4. 追加すると美しい補題候補

今回の bridge は「primitive witness が `GN` に乗る」ところまで来た。
次に Petal 側で欲しくなるのは、既存 theorem のさらに薄い別名じゃな。

たとえば `PrimitiveBeam` 側にある valuation 等式を Petal 名で再公開すると、BezoutBridge の物語がより閉じる。

```lean
theorem padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    padicValNat q (a ^ d - b ^ d) =
      padicValNat q (GN d (a - b) b) := ...
```

また、boundary を割らないことも Petal 名で置くと読みやすい。

```lean
theorem primitivePrimeFactor_not_dvd_boundary
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd1 : 1 < d) :
    ¬ q ∣ a - b := ...
```

これは今回の `primitivePrimeFactor_dvd_GN_of_cosmicBoundary` の前段として、ドキュメント上でも使いやすい。

## 5. 今回の数学的意味

今回の到達点は、こう畳める。

\[
\text{primitive witness}
\quad\Rightarrow\quad
q\mid a^d-b^d
\]

かつ primitive 性により

\[
q\nmid a-b
\]

したがって

\[
a^d-b^d=(a-b)\,GN_d(a-b,b)
\]

から

\[
q\mid GN_d(a-b,b)
\]

へ移る。

つまり、原始素因子は **可視境界ではなく、残余 kernel / GN 面に現れる** 。
これを Petal 側では、anchor carrier として

\[
\text{AnchoredGNCarrier}
\]

へ包めるようになった。

これはまさに

```text
body difference
  -> boundary * GN
  -> primitive witness avoids boundary
  -> witness is observed on GN
  -> anchored GN carrier
```

という橋じゃな。

## 6. 次の一手

わっちなら次は docs に短い節を足す。

`Petal-Overview.md` か `FLGNB-PetalRoadmap.md` に、

```text
Petal.BezoutBridge:
  primitive witness が boundary ではなく GN kernel 側に観測されることを、
  Petal-facing theorem 名で読む橋。
  これは ideal-theoretic Bezout 本体ではなく、gcd/valuation 分離の薄い surface。
```

と置く。

実装としては、今回の差分はこのまま進めてよい。
よい橋じゃ、D.。これは Petal から Zsigmondy へ向かう道の「足場板」が一枚増えた感じじゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 27cb90db..51959ffe 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -16,6 +16,7 @@ import DkMath.Petal.PadicBridge
 import DkMath.Petal.PrimitiveBridge
 import DkMath.Petal.ReducedSupport
 import DkMath.Petal.Anchor
+import DkMath.Petal.BezoutBridge
 import DkMath.Petal.BoundaryD3
 import DkMath.Petal.EisensteinBridge
 import DkMath.Petal.ZsigmondyD3Bridge
@@ -38,7 +39,7 @@ The import order is arranged as the public story of the package:
 basic forms / relative polygon vocabulary
   -> counting and address layers
   -> GN/GCD/p-adic/primitive bridges
-  -> reduced support and anchored carriers
+  -> reduced support, anchored carriers, and Bezout/GN location reading
   -> BoundaryD3 cubic branch split
   -> shifted Eisenstein norm bridge
   -> Zsigmondy d = 3 primitive-divisor bridge
diff --git a/lean/dk_math/DkMath/Petal/BezoutBridge.lean b/lean/dk_math/DkMath/Petal/BezoutBridge.lean
new file mode 100644
index 00000000..a034c037
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/BezoutBridge.lean
@@ -0,0 +1,165 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.Anchor
+import DkMath.NumberTheory.PrimitiveBeam
+import DkMath.NumberTheory.UniqueFactorizationGN
+
+#print "file: DkMath.Petal.BezoutBridge"
+
+/-!
+# Petal Bezout Bridge
+
+This file gives Petal-facing names for the Bezout/gcd reading of the Cosmic
+`GN` factorization.
+
+The mathematical core is already present in the lower layers:
+
+* `PrimitiveBeam` moves primitive prime factors from
+  `a^d - b^d = (a - b) * GN d (a - b) b` to the `GN` side.
+* `UniqueFactorizationGN` controls the gcd between the visible boundary and the
+  residual `GN` kernel.
+
+This bridge does not introduce a new Bezout theorem.  Instead it records the
+interpretation needed by the Petal/Zsigmondy route:
+
+```text
+body difference = boundary * residual kernel
+primitive witness avoids boundary
+therefore the witness is observed on GN
+```
+
+The ideal-theoretic Bezout layer should remain a later, more general bridge.
+This file is deliberately a thin Petal-facing surface.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+open DkMath.NumberTheory.PrimitiveBeam
+
+/--
+Cosmic factor split in Petal boundary/kernel language.
+
+This is the `body = boundary * GN` reading of
+`(x + u)^d - u^d`.
+-/
+theorem cosmicBody_eq_boundary_mul_GN
+    {d x u : ℕ} (hd : 0 < d) (hx : 0 < x) :
+    (x + u) ^ d - u ^ d = x * GN d x u := by
+  have hu_lt : u < x + u := by
+    simpa [Nat.add_comm] using Nat.lt_add_of_pos_right (n := u) hx
+  simpa [Nat.add_sub_cancel] using
+    DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
+      (a := x + u) (b := u) (d := d) hd hu_lt
+
+/--
+Primitive witnesses on the body difference are observed on the residual `GN`
+kernel.
+
+This is the Petal-facing Bezout/gcd reading: the primitive witness avoids the
+visible boundary, so divisibility of `boundary * GN` forces the witness onto
+`GN`.
+-/
+theorem primitivePrimeFactor_dvd_GN_of_cosmicBoundary
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    q ∣ GN d (a - b) b :=
+  primitive_prime_dvd_GN
+    (q := q) (a := a) (b := b) (d := d) hq hd hd1 hab_lt
+
+/--
+Body-coordinate version of `primitivePrimeFactor_dvd_GN_of_cosmicBoundary`.
+
+If the body is written as `(x + u)^d - u^d`, then the primitive witness lies on
+`GN d x u`.
+-/
+theorem primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary
+    {q x u d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
+    (hd : 0 < d) (hd1 : 1 < d) :
+    q ∣ GN d x u :=
+  primitive_prime_dvd_GN_body
+    (q := q) (x := x) (u := u) (d := d) hq hd hd1
+
+/--
+Non-exceptional primes cannot sit in the gcd between the visible boundary and
+the residual `GN` kernel.
+
+This is the Bezout-style separation used by the Petal route: under coprimality
+of `x` and `u`, any prime common to `x` and `GN d x u` must be exceptional for
+the exponent `d`.
+-/
+theorem prime_not_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp
+    {d x u q : ℕ}
+    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
+    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
+    ¬ q ∣ Nat.gcd x (GN d x u) :=
+  DkMath.NumberTheory.prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
+    (d := d) (x := x) (u := u) (q := q)
+    hd1 hx hcop hqP hq_ndvd_d
+
+/--
+Valuation form of the boundary/GN Bezout separation.
+
+For non-exceptional primes, the `q`-adic height of `gcd(boundary, GN)` is zero.
+-/
+theorem padicValNat_boundary_GN_gcd_eq_zero_of_coprime_of_not_dvd_exp
+    {d x u q : ℕ}
+    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
+    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
+    padicValNat q (Nat.gcd x (GN d x u)) = 0 :=
+  DkMath.NumberTheory.padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
+    (d := d) (x := x) (u := u) (q := q)
+    hd1 hx hcop hqP hq_ndvd_d
+
+/--
+Prime-power form of the boundary/GN Bezout separation.
+
+If `q` is non-exceptional for `d`, no positive power of `q` can divide the
+common boundary/GN gcd.
+-/
+theorem not_primePow_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp
+    {d x u q k : ℕ}
+    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
+    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) (hk : 0 < k) :
+    ¬ q ^ k ∣ Nat.gcd x (GN d x u) :=
+  DkMath.NumberTheory.not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
+    (d := d) (x := x) (u := u) (q := q) (k := k)
+    hd1 hx hcop hqP hq_ndvd_d hk
+
+/--
+Primitive witnesses can be packaged as anchored GN carriers.
+
+This is the Anchor-facing endpoint of the Bezout reading: after the primitive
+prime has moved from the body difference to `GN`, the prime itself is a positive
+anchor carrier on the GN surface.
+-/
+theorem anchoredGNCarrier_of_primitivePrimeFactor
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    AnchoredGNCarrier q d (a - b) b q := by
+  refine ⟨?_, ?_⟩
+  · exact hasPositiveAnchorPrime_self_of_prime hq.1
+  · exact primitivePrimeFactor_dvd_GN_of_cosmicBoundary hq hd hd1 hab_lt
+
+/--
+Body-coordinate anchored GN carrier constructor.
+-/
+theorem anchoredGNCarrier_of_bodyPrimitivePrimeFactor
+    {q x u d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
+    (hd : 0 < d) (hd1 : 1 < d) :
+    AnchoredGNCarrier q d x u q := by
+  refine ⟨?_, ?_⟩
+  · exact hasPositiveAnchorPrime_self_of_prime hq.1
+  · exact primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary hq hd hd1
+
+end Petal
+end DkMath
````
`````
