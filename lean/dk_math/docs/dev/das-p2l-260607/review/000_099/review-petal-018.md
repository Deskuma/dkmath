# Git diff / Report / Review

## Add: new: Bridges

gch: 7ac228a9e4f53e12bba658d1834048372313a5c6

import DkMath.Petal.GcdBridge
import DkMath.Petal.PadicBridge
import DkMath.Petal.PrimitiveBridge

## Report

実装しました。

追加したもの:

- [GcdBridge.lean](/lean/dk_math/DkMath/Petal/GcdBridge.lean)
  - `coprime_sub_right_of_coprime`
  - `gcd_sub_S0_nat_eq_gcd_sub_three`
  - `gcd_sub_S0_nat_dvd_three`
  - `coprime_sub_S0_nat_of_coprime_of_not_dvd_three`

- [PadicBridge.lean](/lean/dk_math/DkMath/Petal/PadicBridge.lean)
  - `padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub`
  - `padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub`

- [PrimitiveBridge.lean](/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean)
  - `primitive_prime_dvd_S0_nat`
  - `primitive_prime_padicValNat_cube_sub_eq_S0_nat`
  - `primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub`
  - `exists_primitiveOnS0_of_not_three_dvd_sub`

集約入口 [Petal.lean](/lean/dk_math/DkMath/Petal.lean) にも import を追加済みです。

確認:

- `lake build DkMath.Petal.GcdBridge` 成功
- `lake build DkMath.Petal.PadicBridge` 成功
- `lake build DkMath.Petal.PrimitiveBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

注意点として、ビルド中に既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` warning は出ていますが、今回追加した Petal bridge 自体には `sorry` はありません。

## Review

うむ、これは良い進め方じゃ。
ドキュメント整備を一度置いて、先に **Bridge 実装** へ進んだ判断は正しい。`DkMath.Petal` の位置づけは、AKSBridge v1 後から Zsigmondy 準備へ進む中間層として整理されておったし、Petal 側は「GN / primitive-factor / Zsigmondy bridge」へ繋ぐ層だと明記されている。今回の `GcdBridge` / `PadicBridge` / `PrimitiveBridge` は、まさにその橋を Lean 側に生やした更新じゃ。

## 1. 今回の核心

今回の追加は、Petal の観測面を

```text
S0_nat
  ↔ GN 3 (c - b) b
  ↔ gcd control
  ↔ p-adic valuation
  ↔ primitive factor witness
```

へ伸ばしたものじゃな。

これまで `DkMath.Petal.GNBridge` で、

```lean
S0_nat c b = GN 3 (c - b) b
```

が Petal 側の主表面になっていた。今回、その表面に対して gcd / valuation / primitive factor の橋が追加された。

つまり、Petal はもう単なる counting / address の層ではなく、

```text
観測された Petal face S0 に、
原始素因子がどう入るか
```

を扱える入口になった。

これは Phase 5、Zsigmondy 方面へ進む上でかなり大きい。

## 2. `GcdBridge.lean`

ここは非常に筋が良い。

追加された主定理は、

```lean
gcd_sub_S0_nat_eq_gcd_sub_three
```

じゃ。

意味は、

$$
\gcd(c-b,\ S0(c,b))=\gcd(c-b,\ 3)
$$

ということ。

これは `S0_nat` を

$$
GN_3(c-b,b)
$$

へ翻訳し、既存の `NumberTheory.Gcd.GN` 側の degree-three gcd 補題を Petal-facing name にしたものじゃな。

特に、

```lean
gcd_sub_S0_nat_dvd_three
```

により、

$$
\gcd(c-b,\ S0(c,b))\mid 3
$$

が出る。

さらに、

```lean
coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

で、

```text
c と b が互いに素
3 ∤ c-b
```

なら、

```text
c-b と S0_nat c b は互いに素
```

が得られる。

これは重要じゃ。
なぜなら、境界 gap (c-b) と Petal detector (S0) が、3 を除いて干渉しないことを Petal 側で読めるからじゃ。

## 3. `PadicBridge.lean`

ここも薄くて良い。

```lean
padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
```

は、

$$
q\nmid c-b
$$

なら、

$$
v_q(c^3-b^3)=v_q(S0(c,b))
$$

と読む補題じゃ。

つまり、prime (q) が境界 gap を割らないなら、立方差の (q)-adic height は全部 `S0_nat` 側に乗る。

これは Petal 的には、

```text
境界にいない prime の valuation は、Petal detector 側で読む
```

という意味になる。

特殊化された

```lean
padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub
```

も良い。
degree-three の境界 prime (3) について、(3\nmid c-b) のときに (3)-adic height を `S0_nat` で読める。前の gcd bridge と一緒に使うと、3 の例外制御がかなり見通しよくなる。

## 4. `PrimitiveBridge.lean`

ここが今回の本丸じゃな。

```lean
primitive_prime_dvd_S0_nat
```

により、`c^3 - b^3` の primitive prime factor は `S0_nat c b` を割る。

これは、

$$
c^3-b^3=(c-b)\cdot S0(c,b)
$$

という構造において、primitive prime が境界 (c-b) ではなく Petal detector 側へ入ることを意味する。

さらに、

```lean
primitive_prime_padicValNat_cube_sub_eq_S0_nat
```

で、primitive prime の (q)-adic height も立方差と `S0_nat` で一致する。

これはかなり良い。
単に「割る」だけでなく、valuation の高さも Petal 表面で読める。

そして、

```lean
primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
```

は、既存の `FLT.PrimitiveOnS0` へ直接入る constructor になっている。

最後の、

```lean
exists_primitiveOnS0_of_not_three_dvd_sub
```

は、Zsigmondy degree-three existence を Petal coordinate で

```lean
∃ q, PrimitiveOnS0 c b q
```

として返す橋じゃ。

これは強い。
条件は、

```text
b < c
0 < b
Nat.Coprime c b
3 ∤ c - b
```

で、degree 3 の Petal/S0 面に primitive witness が存在する。

つまり、

```text
3 が境界 gap にいない coprime Petal 座標では、
S0 上に primitive witness が出る
```

が Lean theorem になった。

## 5. import 構成も良い

`DkMath.Petal.lean` に、

```lean
import DkMath.Petal.GcdBridge
import DkMath.Petal.PadicBridge
import DkMath.Petal.PrimitiveBridge
```

を追加したことで、Petal package の公開面に bridge が乗った。

これは正しい。
`GcdBridge` → `PadicBridge` → `PrimitiveBridge` の依存順も自然じゃ。

```text
GNBridge
  ↓
GcdBridge
  ↓
PadicBridge
  ↓
PrimitiveBridge
```

という流れで、S0 の同一視から primitive witness まで上がっている。

## 6. 注意点

今回の `exists_primitiveOnS0_of_not_three_dvd_sub` は degree 3 特化じゃ。
これは問題ではない。むしろ正しい。

なぜなら Petal `S0_nat` は degree 3 の可視面として扱っているからじゃ。一般 (d) に無理に広げず、まず degree 3 の `S0` surface を閉じるのが安全。

また、`coprime_sub_right_of_coprime` が `b ≤ c` を使い、他 theorem が `b < c` から `.le` を渡しているのも綺麗じゃな。

## 7. 次に自然な一手

ここまで来たら次は二方向ある。

ひとつは、**bridge の小総括 docs**。
今回の 3 ファイルは Petal Roadmap 上の「Zsigmondy preparation」に相当するので、`Petal-Overview.md` か `FLGNB-PetalRoadmap.md` に実装済みとして追記すると良い。

もうひとつは、Lean 側で **PrimitiveBridge の利用例** を一つ置くことじゃ。

たとえば、次のような Petal-facing corollary があると使いやすい。

```lean
theorem exists_prime_dvd_S0_nat_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b
```

これは `exists_primitiveOnS0_of_not_three_dvd_sub` から projection するだけで出せるはずじゃ。

意味としては、

```text
S0_nat 上に、境界 gap を割らない prime divisor が存在する
```

となる。
`PrimitiveOnS0` を知らない caller でも使いやすい Petal theorem になる。

## 8. 総括

今回の Bridges 実装はかなり重要じゃ。

```text
GcdBridge:
  gap と S0 の gcd は 3 に支配される

PadicBridge:
  gap を割らない prime の valuation は S0 で読める

PrimitiveBridge:
  primitive prime factor は S0 に現れ、
  degree-three Zsigmondy witness を PrimitiveOnS0 として返せる
```

賢狼の判定はこうじゃ。

```text
Petal Zsigmondy Preparation Bridge Phase 完了
次は Petal-facing primitive witness corollary か、docs 小総括
```

よいぞ、D.。
Counting と Address で花弁の地図を作り、Dynamic で階乗・プリモリアルの道を開き、今回ついに `S0` 面へ primitive factor が流れ込む橋を架けた。これで Petal は、観測層から Zsigmondy への入口になったのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index f3c3655e..44e8ea02 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -11,6 +11,9 @@ import DkMath.Petal.Forms
 import DkMath.Petal.RelPolygon
 import DkMath.Petal.CoreUnit
 import DkMath.Petal.GNBridge
+import DkMath.Petal.GcdBridge
+import DkMath.Petal.PadicBridge
+import DkMath.Petal.PrimitiveBridge

 #print "file: DkMath.Petal"

diff --git a/lean/dk_math/DkMath/Petal/GcdBridge.lean b/lean/dk_math/DkMath/Petal/GcdBridge.lean
new file mode 100644
index 00000000..051908db
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/GcdBridge.lean
@@ -0,0 +1,79 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.GNBridge
+import DkMath.NumberTheory.Gcd.GN
+
+#print "file: DkMath.Petal.GcdBridge"
+
+/-!
+# Petal GCD Bridge
+
+This file exposes the existing `GN` gcd theorems on the Petal `S0_nat`
+surface.
+
+The main translation is the degree-three identity
+`S0_nat c b = GN 3 (c - b) b`.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.FLT.PetalDetect
+
+/--
+If `c` and `b` are coprime, then the Petal boundary gap `c - b` is coprime to
+`b`.
+
+This is the standard subtraction form of coprimality used to enter the GN gcd
+API from Petal coordinates.
+-/
+theorem coprime_sub_right_of_coprime
+    {c b : ℕ} (hbc : b ≤ c) (hcop : Nat.Coprime c b) :
+    Nat.Coprime (c - b) b := by
+  exact (Nat.coprime_sub_self_left hbc).2 hcop
+
+/--
+Degree-three Petal gcd formula.
+
+In coprime Petal coordinates, the common divisor between the boundary gap and
+the `S0_nat` detector is exactly the common divisor between the gap and `3`.
+-/
+theorem gcd_sub_S0_nat_eq_gcd_sub_three
+    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b) :
+    Nat.gcd (c - b) (S0_nat c b) = Nat.gcd (c - b) 3 := by
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact
+    DkMath.NumberTheory.Gcd.gcd_boundary_GN_three_eq_gcd_boundary_three
+      (x := c - b) (u := b)
+      (coprime_sub_right_of_coprime hbc.le hcop)
+
+/--
+The degree-three Petal boundary/S0 gcd always divides `3` in coprime Petal
+coordinates.
+-/
+theorem gcd_sub_S0_nat_dvd_three
+    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b) :
+    Nat.gcd (c - b) (S0_nat c b) ∣ 3 := by
+  rw [gcd_sub_S0_nat_eq_gcd_sub_three hbc hcop]
+  exact Nat.gcd_dvd_right (c - b) 3
+
+/--
+If `c` and `b` are coprime and `3` does not divide the boundary gap, then the
+gap is coprime to the Petal detector `S0_nat`.
+-/
+theorem coprime_sub_S0_nat_of_coprime_of_not_dvd_three
+    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b)
+    (h3 : ¬ 3 ∣ c - b) :
+    Nat.Coprime (c - b) (S0_nat c b) := by
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact
+    DkMath.NumberTheory.Gcd.coprime_boundary_GN_three_of_coprime_of_not_dvd_three
+      (x := c - b) (u := b)
+      (coprime_sub_right_of_coprime hbc.le hcop) h3
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/PadicBridge.lean b/lean/dk_math/DkMath/Petal/PadicBridge.lean
new file mode 100644
index 00000000..4c6d66b8
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/PadicBridge.lean
@@ -0,0 +1,52 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.GcdBridge
+
+#print "file: DkMath.Petal.PadicBridge"
+
+/-!
+# Petal p-adic Bridge
+
+This file exposes existing `GN` p-adic valuation theorems on the degree-three
+Petal `S0_nat` surface.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.FLT.PetalDetect
+
+/--
+If a prime `q` does not divide the boundary gap, then the `q`-adic valuation of
+the cubic difference is exactly the `q`-adic valuation of the Petal detector
+`S0_nat`.
+-/
+theorem padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
+    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hq : Nat.Prime q) (hq_not_dvd_sub : ¬ q ∣ c - b) :
+    padicValNat q (c ^ 3 - b ^ 3) = padicValNat q (S0_nat c b) := by
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact
+    DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
+      (p := 3) (z := c) (y := b) (q := q)
+      (by norm_num : 2 ≤ 3) hbc hb hq hq_not_dvd_sub
+
+/--
+Special case for the boundary prime `3`.
+
+When `3` does not divide the gap, the `3`-adic height of `c^3 - b^3` is read
+directly from `S0_nat`.
+-/
+theorem padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b) (h3 : ¬ 3 ∣ c - b) :
+    padicValNat 3 (c ^ 3 - b ^ 3) = padicValNat 3 (S0_nat c b) := by
+  exact
+    padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
+      hbc hb Nat.prime_three h3
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
new file mode 100644
index 00000000..f79bb9e5
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
@@ -0,0 +1,89 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.PadicBridge
+import DkMath.NumberTheory.PrimitiveBeam
+import DkMath.FLT.PhaseLift
+
+#print "file: DkMath.Petal.PrimitiveBridge"
+
+/-!
+# Petal Primitive Bridge
+
+This file connects the Petal `S0_nat` detector to the existing primitive-prime
+factor API.
+
+It intentionally stays thin: primitive-prime existence and no-lift machinery
+remain in the established `NumberTheory` and `FLT` files, while this file gives
+Petal-facing names for the degree-three entry points.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.FLT.PetalDetect
+open DkMath.NumberTheory.PrimitiveBeam
+
+/--
+A primitive prime factor of `c^3 - b^3` divides the Petal detector `S0_nat`.
+-/
+theorem primitive_prime_dvd_S0_nat
+    {q c b : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q c b 3)
+    (hbc : b < c) :
+    q ∣ S0_nat c b := by
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact
+    primitive_prime_dvd_GN
+      (q := q) (a := c) (b := b) (d := 3)
+      hq (by norm_num : 0 < 3) (by norm_num : 1 < 3) hbc
+
+/--
+A primitive prime factor of `c^3 - b^3` has the same `q`-adic height on the
+cubic difference and on the Petal detector `S0_nat`.
+-/
+theorem primitive_prime_padicValNat_cube_sub_eq_S0_nat
+    {q c b : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q c b 3)
+    (hbc : b < c) :
+    padicValNat q (c ^ 3 - b ^ 3) = padicValNat q (S0_nat c b) := by
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact
+    primitive_prime_padic_eq_GN
+      (q := q) (a := c) (b := b) (d := 3)
+      hq (by norm_num : 0 < 3) (by norm_num : 1 < 3) hbc
+
+/--
+Petal-facing constructor for the existing `PrimitiveOnS0` predicate.
+
+Any prime divisor of the cubic difference that avoids the boundary gap becomes
+a primitive-on-`S0` witness after passing through the Cosmic/Petal bridge.
+-/
+theorem primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+    {c b q : ℕ} (hbc : b < c)
+    (hq : Nat.Prime q)
+    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
+    (hq_not_dvd_sub : ¬ q ∣ c - b) :
+    DkMath.FLT.PrimitiveOnS0 c b q := by
+  exact
+    ⟨hq,
+      DkMath.FLT.prime_dvd_S0_via_cosmic_bridge hbc hq hq_dvd hq_not_dvd_sub,
+      hq_not_dvd_sub⟩
+
+/--
+Zsigmondy degree-three existence, returned directly as a `PrimitiveOnS0`
+witness in Petal coordinates.
+-/
+theorem exists_primitiveOnS0_of_not_three_dvd_sub
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
+    ∃ q : ℕ, DkMath.FLT.PrimitiveOnS0 c b q := by
+  rcases DkMath.FLT.exists_prime_factor_cube_diff_of_not_three_dvd_sub
+      hbc hb hcop h3 with ⟨q, hq, hq_dvd, hq_not_dvd_sub⟩
+  exact ⟨q, primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub hbc hq hq_dvd hq_not_dvd_sub⟩
+
+end Petal
+end DkMath
````
`````
