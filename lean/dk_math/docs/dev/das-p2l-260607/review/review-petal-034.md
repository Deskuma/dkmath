# Git diff / Report / Review

## Upd: Petal PrimitiveD3ValuationBridge

gch: 55bb1c9c7beedda9ed7fee320fa5b62f9497c113

primitive_prime_padic_bound_diff_of_noLift_GN

## Report

交渉を進めました。今回は Petal 専用だった NoLift valuation の核心を、より自然な管轄である `DkMath.NumberTheory.PrimitiveBeam` へ汎用補題として昇格しました。

追加した汎用 theorem:

```lean
primitive_prime_padic_bound_diff_of_noLift_GN
```

意味はこれです。

```text
PrimitivePrimeFactorOfDiffPow q a b d
+ ¬ q^2 ∣ GN d (a - b) b
-> padicValNat q (a^d - b^d) <= 1
```

そのうえで、Petal 側の

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
```

はこの汎用補題へ委譲する形に整理しました。これで構造がかなり綺麗です。

```text
PrimitiveBeam:
  一般の primitive witness + local NoLift -> valuation bound

Petal D3:
  Zsigmondy/Petal shared q を PrimitiveBeam に渡す thin wrapper
```

docs も更新済みです。

検証:

```sh
lake build DkMath.NumberTheory.PrimitiveBeam
lake build DkMath.Petal.PrimitiveD3ValuationBridge
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の research `sorry` 警告だけ継続です。

## Review

うむ、これは **採用でよい**。
今回の昇格はかなり重要じゃ。

これで `PrimitiveD3ValuationBridge` に閉じ込めていた NoLift valuation の核心が、正しい管轄である `DkMath.NumberTheory.PrimitiveBeam` へ移った。

```text
PrimitiveBeam:
  primitive witness + local NoLift GN
  -> padicValNat <= 1

Petal D3:
  Zsigmondy/Petal shared q を PrimitiveBeam witness に変換して渡すだけ
```

この分離はとても綺麗。

## レビュー結論

```text
55bb1c9...
  -> 採用可

primitive_prime_padic_bound_diff_of_noLift_GN
  -> 汎用 theorem として妥当

PrimitiveD3ValuationBridge
  -> thin wrapper 化できて良い

旧 research sorry
  -> さらに置換先が明確になった
```

## 良い点

今回の中核はこれじゃな。

```lean
lemma primitive_prime_padic_bound_diff_of_noLift_GN
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    padicValNat q (a ^ d - b ^ d) ≤ 1
```

これは `d = 3` に依存していない。
だから Petal 専用ではなく、`PrimitiveBeam` に置くのが自然。

証明の流れも正しい。

```text
primitive q
  -> primitive_prime_padic_eq_GN で valuation を GN 側へ移す

padicValNat diff >= 2
  -> padicValNat GN >= 2

padicValNat_dvd_iff_le
  -> q^2 ∣ GN

NoLift と矛盾
```

これで、

```text
¬ q^2 ∣ GN d (a - b) b
```

が本当に valuation bound の最小側条件として API 化された。

## `hGN_ne` の証明も良い

ここは少し重いが、汎用補題として必要な形になっている。

```lean
have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
  simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
```

`GN = 0` だと仮定すると、差冪も 0 になる。
しかし `b < a` かつ `0 < d` なので、

```lean
Nat.pow_lt_pow_left hab_lt hd_ne
```

から `b^d < a^d`、したがって差冪は非ゼロ。
ここで矛盾を取っている。

`PrimitiveBeam` 側で一般 d にしたため、`GN_ne_zero_nat_of_two_le` ではなく factorization から非ゼロを出しているのも妥当じゃ。

## Petal 側が薄くなったのが大きい

修正後の Petal theorem はかなり良い。

```lean
theorem primitiveD3_padicValNat_le_one_of_noLift_GN
    {c b q : ℕ} (hbc : b < c)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
  exact
    primitive_prime_padic_bound_diff_of_noLift_GN
      ...
```

以前の Petal 側は、valuation equality、GN 非ゼロ、`padicValNat_dvd_iff_le` まで自前で持っていた。
今回それを `PrimitiveBeam` に寄せたので、Petal 側は本当に、

```text
Zsigmondy primitive divisor
  -> PrimitiveBeam primitive witness
  -> general no-lift valuation theorem
```

を繋ぐだけになった。

これは良いリファクタリングじゃ。

## 特に良い副作用

`hb : 0 < b` が `primitiveD3_padicValNat_le_one_of_noLift_GN` から消えたのも良い。

以前は GN 非ゼロ証明のために `hb` が必要だった。
しかし汎用 `PrimitiveBeam` 補題では、`b < a` と `0 < d` から差冪非ゼロを確保しているため、Petal wrapper では `hbc : b < c` だけで足りる。

これは theorem の仮定が引き締まっていて良い。

## 位置づけ

今回で階層はこうなった。

```text
DkMath.Zsigmondy
  PrimitivePrimeDivisor

DkMath.Petal.ZsigmondyD3Bridge
  Zsigmondy witness
  -> AnchoredS0Carrier
  -> PrimitivePrimeFactorOfDiffPow

DkMath.NumberTheory.PrimitiveBeam
  PrimitivePrimeFactorOfDiffPow
  + NoLift GN
  -> padicValNat <= 1

DkMath.Petal.PrimitiveD3ValuationBridge
  BoundaryD3 / Zsigmondy / Petal 文脈から
  PrimitiveBeam 汎用 theorem を呼ぶ
```

非常に良い責務分離じゃ。

## 注意点

大きな問題はない。
ただし docs では今後、

```text
Squarefree route is a sufficient-condition wrapper.
NoLift route is the generic local route.
```

を明確にしておくと良い。

もう現在の本命は squarefree ではなく、

```lean
primitive_prime_padic_bound_diff_of_noLift_GN
```

じゃな。

`squarefree` は「全素数に対する NoLift を一括で保証する強い条件」として読むのが自然。

## 判定

```text
PrimitiveBeam への昇格
  -> 正しい

Petal 側の thin wrapper 化
  -> 正しい

NoLift を valuation 層の本命にする整理
  -> 正しい

Zsigmondy / Petal / PrimitiveBeam / Valuation の三層接続
  -> かなり安定化
```

うむ。
これで旧 `squarefree_implies_padic_val_le_one_research` の置換先は、さらに明確になった。

```text
旧:
  primitive-ish q -> padicValNat <= 1
  偽

新:
  PrimitivePrimeFactorOfDiffPow q a b d
  + ¬ q^2 ∣ GN d (a-b) b
  -> padicValNat q (a^d - b^d) <= 1
  真
```

これは大きな前進じゃ。
ここまで来ると、次は FLT / ABC 側の旧参照をこの `PrimitiveBeam` 汎用 theorem、または Petal D3 wrapper へ逃がせるかの調査に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
index 3e59b4a8..ecec0c90 100644
--- a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
+++ b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
@@ -101,6 +101,45 @@ lemma primitive_prime_padic_eq_GN
   have hzero : padicValNat q (a - b) = 0 := padicValNat.eq_zero_of_not_dvd hq_ndiv
   simpa [hzero] using hpadic

+/--
+Honest local no-lift route for the primitive-prime valuation bound:
+if the selected primitive prime `q` does not lift to `q^2` on the `GN` side,
+then its valuation in `a^d - b^d` is at most one.
+
+This is weaker than the squarefree-GN route because it only controls the chosen
+primitive witness.
+-/
+lemma primitive_prime_padic_bound_diff_of_noLift_GN
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
+    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
+  have hpadic_eq_GN :
+      padicValNat q (a ^ d - b ^ d) =
+        padicValNat q (GN d (a - b) b) :=
+    primitive_prime_padic_eq_GN hq hd hd1 hab_lt
+  have hGN_ne : GN d (a - b) b ≠ 0 := by
+    intro hGN0
+    have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
+      have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
+      exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab_lt hd_ne)
+    have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
+      simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
+    rw [hfactor, hGN0, mul_zero] at hdiff_ne
+    exact hdiff_ne rfl
+  by_contra h_not_le
+  have htwo_le_diff : 2 ≤ padicValNat q (a ^ d - b ^ d) := by
+    omega
+  have htwo_le_GN : 2 ≤ padicValNat q (GN d (a - b) b) := by
+    simpa [hpadic_eq_GN] using htwo_le_diff
+  have hq2_dvd_GN : q ^ 2 ∣ GN d (a - b) b := by
+    exact
+      (@padicValNat_dvd_iff_le q (Fact.mk hq.1)
+        (GN d (a - b) b) 2 hGN_ne).2 htwo_le_GN
+  exact hNoLift hq2_dvd_GN
+
 /--
 Honest repair route for the primitive-prime valuation bound:
 once `Squarefree (GN d (a - b) b)` is available, the old research placeholder is unnecessary.
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 68d47056..d6709d58 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1360,6 +1360,13 @@ exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
 exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
 ```

+The generic no-lift valuation helper has also been promoted to
+`DkMath.NumberTheory.PrimitiveBeam`:
+
+```lean
+primitive_prime_padic_bound_diff_of_noLift_GN
+```
+
 Meaning:

 ```text
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
index f3a25643..bc884b57 100644
--- a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
+++ b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
@@ -36,35 +36,18 @@ This is weaker than squarefree `GN3`: it only asks that the selected witness
 `q` does not lift to `q^2` on the `GN3` side.
 -/
 theorem primitiveD3_padicValNat_le_one_of_noLift_GN
-    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
+    {c b q : ℕ} (hbc : b < c)
     (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
     (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
     padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
-  let hprimitive : PrimitivePrimeFactorOfDiffPow q c b 3 :=
-    primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim
-  have hEq :
-      padicValNat q (c ^ 3 - b ^ 3) =
-        padicValNat q (GN 3 (c - b) b) := by
-    exact
-      primitive_prime_padic_eq_GN
-        (q := q) (a := c) (b := b) (d := 3)
-        hprimitive (by norm_num) (by norm_num) hbc
-  have hGN_ne : GN 3 (c - b) b ≠ 0 := by
-    exact
-      GN_ne_zero_nat_of_two_le
-        (d := 3) (x := c - b) (u := b)
-        (by norm_num) (Nat.sub_pos_of_lt hbc) hb
-  by_contra h_not_le
-  have htwo_le_diff : 2 ≤ padicValNat q (c ^ 3 - b ^ 3) := by
-    omega
-  have htwo_le_GN : 2 ≤ padicValNat q (GN 3 (c - b) b) := by
-    simpa [hEq] using htwo_le_diff
-  have hq2_dvd_GN : q ^ 2 ∣ GN 3 (c - b) b := by
-    exact
-      (@padicValNat_dvd_iff_le q
-        (Fact.mk (DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim))
-        (GN 3 (c - b) b) 2 hGN_ne).2 htwo_le_GN
-  exact hNoLift hq2_dvd_GN
+  exact
+    primitive_prime_padic_bound_diff_of_noLift_GN
+      (q := q) (a := c) (b := b) (d := 3)
+      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
+      (by norm_num)
+      (by norm_num)
+      hbc
+      hNoLift

 /--
 Squarefree `GN3` turns the shared `d = 3` primitive witness into the honest
@@ -114,7 +97,7 @@ theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
   exact
     ⟨q, hprim, hprimitive, hcarrier,
       primitiveD3_padicValNat_le_one_of_noLift_GN
-        hbc hb hprim (hNoLift hprim)⟩
+        hbc hprim (hNoLift hprim)⟩

 /--
 Existence form: on the reduced cubic branch, if the `GN3` side is squarefree,
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index b0e4ef28..e87f5a3c 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -375,6 +375,13 @@ The local no-lift input is weaker than full squarefreeness:
 not q^2 divides GN 3 (c - b) b
 ```

+The underlying local no-lift valuation helper is now available in
+`DkMath.NumberTheory.PrimitiveBeam` as:
+
+```lean
+primitive_prime_padic_bound_diff_of_noLift_GN
+```
+
 ### `DkMath.Petal.Counting`

 Defines the fixed and dynamic counting layer.
````
`````
