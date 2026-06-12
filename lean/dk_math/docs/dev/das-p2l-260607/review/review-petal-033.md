# Git diff / Report / Review

## Upd: Petal PrimitiveD3ValuationBridge

gch: 532dc9222f4e48657dcf95c4285faf96257b7c76

## Report

交渉を一段進めました。`PrimitiveD3ValuationBridge` に squarefree より弱い局所 NoLift 版を追加しています。

追加 theorem:

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
```

これで valuation 層は二段構えになりました。

```text
local NoLift:
  ¬ q^2 ∣ GN 3 (c - b) b
  -> padicValNat q (c^3 - b^3) <= 1

squarefree:
  Squarefree (GN 3 (c - b) b)
  -> padicValNat q (c^3 - b^3) <= 1
```

Squarefree は十分条件、NoLift は選ばれた `q` に対する最小側の局所条件、という整理です。docs も `Petal-Overview.md`、`FLGNB-PetalRoadmap.md`、本線 Roadmap に反映しました。

検証:

```sh
lake build DkMath.Petal.PrimitiveD3ValuationBridge
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の research `sorry` 警告だけ継続です。

## Review

うむ、これは **さらに良い**。
`PrimitiveD3ValuationBridge` が、squarefree だけでなく **局所 NoLift** まで降りた。これはかなり重要じゃ。

## レビュー結論

```text id="w7exm9"
532dc922...
  -> 採用可

NoLift 版
  -> 良い。squarefree より本質的に弱い

squarefree 版
  -> 十分条件 wrapper として維持

valuation <= 1
  -> 依然として条件付きなので安全
```

## 何が良くなったか

前回までは、

```text id="h1ezwe"
Squarefree (GN 3 (c - b) b)
  -> padicValNat q (c^3 - b^3) <= 1
```

だった。

今回追加されたのは、

```text id="0eeesp"
¬ q^2 ∣ GN 3 (c - b) b
  -> padicValNat q (c^3 - b^3) <= 1
```

じゃな。

これは意味が大きい。
`Squarefree GN3` は GN 側全体に対する大域条件。
一方 `NoLift` は選ばれた witness `q` だけの局所条件。

つまり、

```text id="dfr2cd"
Squarefree GN3:
  すべての素因子が一回だけ

NoLift q GN3:
  今使っている q だけ二乗で持ち上がらない
```

なので、下流で必要なのは多くの場合 NoLift 版の方じゃ。

## `primitiveD3_padicValNat_le_one_of_noLift_GN`

この theorem は良い。

```lean id="rqxio1"
theorem primitiveD3_padicValNat_le_one_of_noLift_GN
    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1
```

証明の流れも筋が良い。

```text id="1yedos"
PrimitivePrimeDivisor
  -> PrimitivePrimeFactorOfDiffPow
  -> padicValNat diff = padicValNat GN
  -> if padicValNat diff >= 2, then q^2 | GN
  -> contradict NoLift
```

特に、

```lean id="crglbg"
primitive_prime_padic_eq_GN
```

を使って差冪側と GN 側の valuation を一致させているのが正しい。
ここで `hred` や `hcop` を不要にしている点もよい。`hprim` がすでに primitive condition を持っているので、局所 theorem はかなり軽い。

## existence form の仮定について

```lean id="dhj8vi"
(hNoLift :
  ∀ {q : ℕ}, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q →
    ¬ q ^ 2 ∣ GN 3 (c - b) b)
```

これは、存在形としては妥当じゃ。

なぜなら、存在定理で取られる `q` は事前に分からないので、選ばれる primitive witness すべてに対して NoLift を仮定している。

ただし、将来的には次のような「指定 witness 版」も欲しくなる可能性はある。

```lean id="699fet"
theorem primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
    {c b q : ℕ}
    (hbc : b < c) (hb : 0 < b)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hcarrier : AnchoredS0Carrier q c b q)
    (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    ...
```

でも今の `primitiveD3_padicValNat_le_one_of_noLift_GN` がすでに指定 witness 版として使えるので、追加は不要かもしれぬ。

## squarefree 版との関係

今は squarefree 版が既存 honest theorem へ直接行っている。

```lean id="c0bz22"
primitive_prime_padic_bound_diff_of_squarefree_GN
```

一方 NoLift 版は手証明。
この構成で問題ない。

ただ、docs 上では、

```text id="qzq4v5"
squarefree is a sufficient condition for no-lift
```

と書いてあるので、将来的にもし `Squarefree -> ¬ q^2 ∣ GN` の補題が使いやすければ、squarefree 版を NoLift 版経由にしてもよい。
今は不要。

## 重要な意味

これで、昔の偽 placeholder の正しい置換先はかなり明確になった。

旧偽命題:

```text id="tgc466"
primitive-ish q
  -> padicValNat <= 1
```

正しい新命題:

```text id="8xauug"
primitive q
+ q^2 ∤ GN side
  -> padicValNat <= 1
```

または十分条件として、

```text id="7cmjpn"
primitive q
+ Squarefree GN side
  -> padicValNat <= 1
```

これが Lean API になった。

## 判定

```text id="0yui23"
PrimitiveD3ValuationBridge
  -> かなり良い完成度

NoLift route
  -> 本命

Squarefree route
  -> 十分条件 wrapper

Zsigmondy / Petal / PrimitiveBeam / Valuation
  -> 同じ q で接続済み
```

## 次の一手

ここでまた closure checkpoint を更新してもよい。
あるいは、次は `ZsigmondyCyclotomicResearch.lean` の legacy placeholder を docs 上で deprecated 扱いに寄せ、参照元をこの honest route へ逃がす段階じゃな。

技術的には、次の探索が自然。

```text id="yl1lzg"
FLT / ABC で squarefree_implies_padic_val_le_one_research を参照している箇所が、
NoLift 版または Squarefree 版へ置換できるか
```

うむ。
これで「Zsigmondy は存在、Petal は場所、NoLift は重複度」という三分割が、かなり実装で固まったぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index b22fb99c..68d47056 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1354,12 +1354,23 @@ squarefree/no-lift valuation layer.
 Implemented:
 
 ```lean
+primitiveD3_padicValNat_le_one_of_noLift_GN
 primitiveD3_padicValNat_le_one_of_squarefree_GN
+exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
 exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
 ```
 
 Meaning:
 
+```text
+BoundaryD3Reduced hypotheses
+  -> Zsigmondy/Petal/PrimitiveBeam shared witness q
+  -> not q^2 divides GN 3 (c - b) b
+  -> padicValNat q (c^3 - b^3) <= 1
+```
+
+The squarefree variant is the stronger sufficient-condition wrapper:
+
 ```text
 BoundaryD3Reduced hypotheses
   -> Zsigmondy/Petal/PrimitiveBeam shared witness q
@@ -1367,8 +1378,9 @@ BoundaryD3Reduced hypotheses
   -> padicValNat q (c^3 - b^3) <= 1
 ```
 
-This is still not an unconditional valuation theorem.  The squarefree `GN3`
-hypothesis is explicit and belongs to the multiplicity/no-lift layer.
+This is still not an unconditional valuation theorem.  The local no-lift or
+squarefree `GN3` hypothesis is explicit and belongs to the multiplicity/no-lift
+layer.
 
 Expected validation:
 
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index 084a5be9..c2e17708 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -563,7 +563,8 @@ Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有
 さらに同じ witness を `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` としても
 共有し、後続の squarefree/no-lift 評価値層へ渡せる形にした。
 その次の条件付き bridge として `DkMath.Petal.PrimitiveD3ValuationBridge` も
-実装済みであり、`Squarefree (GN 3 (c - b) b)` を明示仮定にした場合のみ
+実装済みであり、局所 no-lift `¬ q^2 ∣ GN 3 (c - b) b`、またはその十分条件
+である `Squarefree (GN 3 (c - b) b)` を明示仮定にした場合のみ
 `padicValNat q (c^3 - b^3) <= 1` へ進む。
 `padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
 持つ別層の仕事として扱う。
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
index 02dfedc3..f3a25643 100644
--- a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
+++ b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
@@ -17,6 +17,9 @@ to the honest squarefree/no-lift valuation layer.
 It does not prove squarefreeness.  It only says that once the caller supplies
 `Squarefree (GN 3 (c - b) b)`, the same primitive divisor `q` already shared by
 Zsigmondy, Petal, and PrimitiveBeam has `padicValNat <= 1` in `c^3 - b^3`.
+
+The file also exposes the strictly weaker local no-lift version:
+`¬ q^2 ∣ GN 3 (c - b) b` is enough for the same bound for that particular `q`.
 -/
 
 namespace DkMath
@@ -25,6 +28,44 @@ namespace Petal
 open DkMath.CosmicFormulaBinom
 open DkMath.NumberTheory.PrimitiveBeam
 
+/--
+Local no-lift on `GN3` turns the shared `d = 3` primitive witness into the
+valuation bound on the difference body.
+
+This is weaker than squarefree `GN3`: it only asks that the selected witness
+`q` does not lift to `q^2` on the `GN3` side.
+-/
+theorem primitiveD3_padicValNat_le_one_of_noLift_GN
+    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
+    (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
+    padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
+  let hprimitive : PrimitivePrimeFactorOfDiffPow q c b 3 :=
+    primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim
+  have hEq :
+      padicValNat q (c ^ 3 - b ^ 3) =
+        padicValNat q (GN 3 (c - b) b) := by
+    exact
+      primitive_prime_padic_eq_GN
+        (q := q) (a := c) (b := b) (d := 3)
+        hprimitive (by norm_num) (by norm_num) hbc
+  have hGN_ne : GN 3 (c - b) b ≠ 0 := by
+    exact
+      GN_ne_zero_nat_of_two_le
+        (d := 3) (x := c - b) (u := b)
+        (by norm_num) (Nat.sub_pos_of_lt hbc) hb
+  by_contra h_not_le
+  have htwo_le_diff : 2 ≤ padicValNat q (c ^ 3 - b ^ 3) := by
+    omega
+  have htwo_le_GN : 2 ≤ padicValNat q (GN 3 (c - b) b) := by
+    simpa [hEq] using htwo_le_diff
+  have hq2_dvd_GN : q ^ 2 ∣ GN 3 (c - b) b := by
+    exact
+      (@padicValNat_dvd_iff_le q
+        (Fact.mk (DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim))
+        (GN 3 (c - b) b) 2 hGN_ne).2 htwo_le_GN
+  exact hNoLift hq2_dvd_GN
+
 /--
 Squarefree `GN3` turns the shared `d = 3` primitive witness into the honest
 valuation bound on the difference body.
@@ -51,6 +92,30 @@ theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
       (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
       hG_sq
 
+/--
+Existence form for the local no-lift route: on the reduced cubic branch, if the
+selected shared witness has no `q^2` lift on `GN3`, then it has valuation at
+most one in the difference body.
+-/
+theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
+    (hNoLift :
+      ∀ {q : ℕ}, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q →
+        ¬ q ^ 2 ∣ GN 3 (c - b) b) :
+    ∃ q : ℕ,
+      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
+        PrimitivePrimeFactorOfDiffPow q c b 3 ∧
+          AnchoredS0Carrier q c b q ∧
+            padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
+  rcases exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
+      hbc hb hcop hred with
+    ⟨q, hprim, hprimitive, hcarrier⟩
+  exact
+    ⟨q, hprim, hprimitive, hcarrier,
+      primitiveD3_padicValNat_le_one_of_noLift_GN
+        hbc hb hprim (hNoLift hprim)⟩
+
 /--
 Existence form: on the reduced cubic branch, if the `GN3` side is squarefree,
 there is a single witness `q` that is simultaneously Zsigmondy-primitive,
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 1b8dea02..b0e4ef28 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -355,18 +355,26 @@ Connects the shared `d = 3` witness to the honest squarefree valuation theorem.
 Important names:
 
 ```lean
+primitiveD3_padicValNat_le_one_of_noLift_GN
 primitiveD3_padicValNat_le_one_of_squarefree_GN
+exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
 exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
 ```
 
 This file is deliberately conditional.  It does not prove that `GN 3 (c - b) b`
-is squarefree.  It only says that, once squarefreeness is supplied, the same
-`q` shared by Zsigmondy, Petal, and PrimitiveBeam satisfies:
+is squarefree.  It only says that, once local no-lift or squarefreeness is
+supplied, the same `q` shared by Zsigmondy, Petal, and PrimitiveBeam satisfies:
 
 ```text
 padicValNat q (c^3 - b^3) <= 1
 ```
 
+The local no-lift input is weaker than full squarefreeness:
+
+```text
+not q^2 divides GN 3 (c - b) b
+```
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
````
`````
