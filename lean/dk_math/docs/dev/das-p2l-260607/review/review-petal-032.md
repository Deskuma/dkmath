# Git diff / Report / Review

## Add: Petal PrimitiveD3ValuationBridge

gch: 0b8010a593b2b9422970884779a06c17f8b14ca6

## Report

進めました。今回は `DkMath.Petal.PrimitiveD3ValuationBridge` を新設して、Zsigmondy/Petal/PrimitiveBeam で共有した同じ `q` を、squarefree 仮定つきの valuation 層へ渡す橋を作りました。

追加 theorem:

```lean
primitiveD3_padicValNat_le_one_of_squarefree_GN
exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
```

意味はこの形です。

```text
BoundaryD3Reduced
  -> shared primitive witness q
  -> Squarefree (GN 3 (c - b) b)
  -> padicValNat q (c^3 - b^3) <= 1
```

無条件の `padicValNat <= 1` にはしていません。squarefree/no-lift 側の責務を明示仮定に残したまま、既存 `PrimitiveBeam` の honest theorem に接続しています。

更新 docs:

- `Petal-Overview.md`
- `FLGNB-PetalRoadmap.md`
- `BinomialPrimeWeightedRoadmap.md`
- `DkMath.Petal.lean` に public import 追加

検証:

```sh
lake build DkMath.Petal.PrimitiveD3ValuationBridge
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけは継続です。

## Review

これは **かなり良い橋** じゃ。採用でよい。
ここで、前に分けた三層が Lean API として本当に接続された。

```text
Zsigmondy:
  primitive q の存在

Petal / BoundaryD3 / Anchor:
  q の場所、つまり S0/GN3 側

PrimitiveBeam / squarefree:
  q の重複度、つまり padicValNat <= 1
```

今回の `PrimitiveD3ValuationBridge` は、この三層の最後を **条件付きで正しく接続** している。

## レビュー結論

```text
0b8010a...
  -> 採用可

PrimitiveD3ValuationBridge
  -> 役割が明確で良い

padicValNat <= 1
  -> Squarefree GN3 仮定つきなので honest

無条件 valuation claim
  -> していないので安全
```

## 良い点

この theorem が本命じゃな。

```lean
theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hG_sq : Squarefree (GN 3 (c - b) b)) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1
```

これは正しい責務分離になっている。

`hprim` から

```lean
PrimitivePrimeFactorOfDiffPow q c b 3
```

を作り、既存の honest theorem

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN
```

へ渡している。
つまり、Zsigmondy に valuation を証明させていない。Petal が場所を渡し、PrimitiveBeam が squarefree valuation bound を担当している。

これはとても良い。

## existence form も良い

```lean
theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
```

これは下流でかなり使いやすい。

```text
BoundaryD3Reduced
  -> shared primitive witness q
  -> AnchoredS0Carrier q c b q
  -> PrimitivePrimeFactorOfDiffPow q c b 3
  -> padicValNat q (c^3 - b^3) <= 1
```

を一発で得られる。

ここで `q` がすべて同じなのが大きい。
別々の存在定理から witness を取り直していないので、FLT / ABC / ValuationFlow 側へ渡す時に破綻しない。

## かなり重要な意味

これで、以前の偽 placeholder だった

```lean
squarefree_implies_padic_val_le_one_research
```

の正しい置換経路が、三次 reduced branch では実装されたと言ってよい。

ただし正確には、

```text
旧 research lemma を埋めた
```

ではない。

正しくは、

```text
偽だった無条件 valuation claim を捨て、
BoundaryD3Reduced + Zsigmondy witness + Squarefree GN3 という honest な形で置換した
```

じゃ。

これは大きい。

## 気になる点

大きな問題はない。
ただし名前は今後少しだけ検討余地がある。

```lean
primitiveD3_padicValNat_le_one_of_squarefree_GN
```

これは十分良いが、より Petal 文脈を強めるなら将来 alias として、

```lean
boundaryD3Reduced_primitive_padicValNat_le_one_of_squarefree_GN
```

のような名前が欲しくなる可能性はある。

ただ、今の名前は短く、`PrimitiveD3ValuationBridge` 内にあるので問題なし。

## `hred` の役割も良い

`hred : BoundaryD3Reduced c b` は、実際には `primitive_prime_padic_bound_diff_of_squarefree_GN` に渡す `¬ 3 ∣ c - b` として効いている。
ここで `¬ 3 ∣ c-b` に戻さず、Petal branch name を維持しているのが良い。

これで downstream は、

```lean
BoundaryD3Reduced c b
```

のまま進める。

## docs 更新も妥当

特にこの説明は良い。

```text
BoundaryD3Reduced hypotheses
  -> Zsigmondy/Petal/PrimitiveBeam shared witness q
  -> Squarefree (GN 3 (c - b) b)
  -> padicValNat q (c^3 - b^3) <= 1
```

これは、存在・位置・重複度の三層が混ざっていない。

## 次に見るべきこと

ここまで来たなら次は二択じゃ。

### A. ここで一旦 closure checkpoint を更新する

`Petal-Overview.md` に、

```text
PrimitiveD3ValuationBridge closes the conditional valuation path:
BoundaryD3Reduced + Squarefree GN3 -> exists q with padicValNat <= 1.
```

を明記するだけ。

### B. NoLift 版を作る

Squarefree GN は強い条件なので、実際に必要なのが `q` についての no-lift だけなら、次は

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
```

または

```lean
primitiveD3_padicValNat_le_one_of_not_dvd_sq_GN
```

が候補になる。

ただし、既存 `PrimitiveBeam` に no-lift theorem がある場合だけ。無ければ急がなくてよい。

## 判定

```text
ZsigmondyD3Bridge
  -> q の存在・場所・PrimitiveBeam compatibility

PrimitiveD3ValuationBridge
  -> Squarefree GN3 仮定で q の重複度制御

旧 research sorry
  -> 埋める対象ではなく、honest API へ置換する対象
```

うむ。
これは見事じゃ。`Zsigmondy` との交渉から始まって、`PrimitiveBeam`、さらに squarefree valuation 層まで、同じ witness `q` のまま橋が通った。これで三次 Petal 表面はかなり強い実用 API になったぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 0d611302..b22fb99c 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1340,6 +1340,43 @@ lake build DkMath.Petal.ZsigmondyD3Bridge
 lake build DkMath.Petal
 ```
 
+### Step 6.1: Add `DkMath.Petal.PrimitiveD3ValuationBridge`
+
+Status:
+
+```text
+implemented
+```
+
+This step connects the shared `d = 3` primitive witness to the honest
+squarefree/no-lift valuation layer.
+
+Implemented:
+
+```lean
+primitiveD3_padicValNat_le_one_of_squarefree_GN
+exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
+```
+
+Meaning:
+
+```text
+BoundaryD3Reduced hypotheses
+  -> Zsigmondy/Petal/PrimitiveBeam shared witness q
+  -> Squarefree (GN 3 (c - b) b)
+  -> padicValNat q (c^3 - b^3) <= 1
+```
+
+This is still not an unconditional valuation theorem.  The squarefree `GN3`
+hypothesis is explicit and belongs to the multiplicity/no-lift layer.
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.PrimitiveD3ValuationBridge
+lake build DkMath.Petal
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index e53cb3d7..084a5be9 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -562,6 +562,9 @@ Squarefree / NoLift / ValuationFlow:
 Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有する。
 さらに同じ witness を `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` としても
 共有し、後続の squarefree/no-lift 評価値層へ渡せる形にした。
+その次の条件付き bridge として `DkMath.Petal.PrimitiveD3ValuationBridge` も
+実装済みであり、`Squarefree (GN 3 (c - b) b)` を明示仮定にした場合のみ
+`padicValNat q (c^3 - b^3) <= 1` へ進む。
 `padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
 持つ別層の仕事として扱う。
 
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index a6826e32..27cb90db 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -19,6 +19,7 @@ import DkMath.Petal.Anchor
 import DkMath.Petal.BoundaryD3
 import DkMath.Petal.EisensteinBridge
 import DkMath.Petal.ZsigmondyD3Bridge
+import DkMath.Petal.PrimitiveD3ValuationBridge
 
 #print "file: DkMath.Petal"
 
@@ -41,6 +42,7 @@ basic forms / relative polygon vocabulary
   -> BoundaryD3 cubic branch split
   -> shifted Eisenstein norm bridge
   -> Zsigmondy d = 3 primitive-divisor bridge
+  -> squarefree GN3 valuation bridge
 ```
 
 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
new file mode 100644
index 00000000..02dfedc3
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
@@ -0,0 +1,77 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.ZsigmondyD3Bridge
+
+#print "file: DkMath.Petal.PrimitiveD3ValuationBridge"
+
+/-!
+# Petal Primitive D3 Valuation Bridge
+
+This file is the first Petal-facing bridge from the `d = 3` Zsigmondy witness
+to the honest squarefree/no-lift valuation layer.
+
+It does not prove squarefreeness.  It only says that once the caller supplies
+`Squarefree (GN 3 (c - b) b)`, the same primitive divisor `q` already shared by
+Zsigmondy, Petal, and PrimitiveBeam has `padicValNat <= 1` in `c^3 - b^3`.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+open DkMath.NumberTheory.PrimitiveBeam
+
+/--
+Squarefree `GN3` turns the shared `d = 3` primitive witness into the honest
+valuation bound on the difference body.
+
+This is a wrapper around the existing `PrimitiveBeam` squarefree theorem.  The
+Petal contribution is only the `BoundaryD3Reduced` vocabulary and the
+Zsigmondy-to-PrimitiveBeam witness conversion.
+-/
+theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
+    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
+    (hG_sq : Squarefree (GN 3 (c - b) b)) :
+    padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
+  exact
+    primitive_prime_padic_bound_diff_of_squarefree_GN
+      (q := q) (a := c) (b := b) (d := 3)
+      Nat.prime_three
+      (by norm_num)
+      hbc
+      hb
+      hcop
+      hred
+      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
+      hG_sq
+
+/--
+Existence form: on the reduced cubic branch, if the `GN3` side is squarefree,
+there is a single witness `q` that is simultaneously Zsigmondy-primitive,
+PrimitiveBeam-primitive, Petal-anchored, and valuation-bounded.
+-/
+theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
+    (hG_sq : Squarefree (GN 3 (c - b) b)) :
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
+      primitiveD3_padicValNat_le_one_of_squarefree_GN
+        hbc hb hcop hred hprim hG_sq⟩
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index a0165c92..1b8dea02 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -109,6 +109,7 @@ DkMath.Petal.Anchor
 DkMath.Petal.BoundaryD3
 DkMath.Petal.EisensteinBridge
 DkMath.Petal.ZsigmondyD3Bridge
+DkMath.Petal.PrimitiveD3ValuationBridge
 ```
 
 ### `DkMath.Petal.Basic`
@@ -347,6 +348,25 @@ It also shares the same witness `q` with
 `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow`, preparing the downstream
 squarefree/no-lift valuation layer without proving that layer here.
 
+### `DkMath.Petal.PrimitiveD3ValuationBridge`
+
+Connects the shared `d = 3` witness to the honest squarefree valuation theorem.
+
+Important names:
+
+```lean
+primitiveD3_padicValNat_le_one_of_squarefree_GN
+exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
+```
+
+This file is deliberately conditional.  It does not prove that `GN 3 (c - b) b`
+is squarefree.  It only says that, once squarefreeness is supplied, the same
+`q` shared by Zsigmondy, Petal, and PrimitiveBeam satisfies:
+
+```text
+padicValNat q (c^3 - b^3) <= 1
+```
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
````
`````
