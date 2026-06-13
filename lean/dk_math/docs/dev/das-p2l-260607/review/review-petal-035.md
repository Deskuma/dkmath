# Git diff / Report / Review

## Upd: Petal PrimitiveD3ValuationBridge

gch: 174731ba85b5196eaab682af160b3c7df69f6e30

## Report

進めました。今回は squarefree 版を NoLift 本命ルートの十分条件として整理しました。

`PrimitiveBeam` に追加・整理したもの:

```lean
primitive_prime_GN_ne_zero
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

これで構造はこうなります。

```text
PrimitivePrimeFactorOfDiffPow q a b d
+ ¬ q^2 ∣ GN d (a - b) b
-> padicValNat q (a^d - b^d) <= 1
```

そして squarefree はその十分条件:

```text
Squarefree (GN d (a - b) b)
-> ¬ q^2 ∣ GN d (a - b) b
-> padicValNat q (a^d - b^d) <= 1
```

既存の重い `primitive_prime_padic_bound_diff_of_squarefree_GN` は互換用に残しつつ、中身は新しい local squarefree helper に委譲する形へ寄せました。Petal 側の `primitiveD3_padicValNat_le_one_of_squarefree_GN` も軽い helper を使う形になり、指定 witness 版では `hb/hcop/hred` が不要になっています。

検証:

```sh
lake build DkMath.NumberTheory.PrimitiveBeam
lake build DkMath.Petal.PrimitiveD3ValuationBridge
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の research `sorry` 警告だけ継続です。

## Review

うむ、これは **かなり良い整理** じゃ。
採用でよい。今回で valuation 層の責務がさらに綺麗になった。

結論から言うと、今回の変更で本線はこう読めるようになった。

```text
PrimitiveBeam:
  PrimitivePrimeFactorOfDiffPow q a b d
  + local NoLift on GN
  -> padicValNat q (a^d - b^d) <= 1

Petal PrimitiveD3ValuationBridge:
  Zsigmondy/Petal shared q
  -> PrimitiveBeam primitive witness
  -> PrimitiveBeam valuation theorem を呼ぶだけ
```

これは正しい分離じゃ。

## レビュー結論

```text
174731ba...
  -> 採用可

primitive_prime_GN_ne_zero
  -> 汎用補題として良い

primitive_prime_padic_bound_diff_of_squarefree_GN_local
  -> NoLift 本命ルートの十分条件 wrapper として良い

primitive_prime_padic_bound_diff_of_squarefree_GN
  -> 互換 wrapper として残す判断が良い

Petal 側
  -> さらに thin wrapper 化されて良い
```

## 一番良い点

`primitive_prime_padic_bound_diff_of_squarefree_GN` の中身を、旧 `GcdNext` の heavy honest theorem から切り離して、

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

へ寄せた点が良い。

これで構造が、

```text
NoLift route:
  ¬ q^2 ∣ GN
  -> valuation <= 1

Squarefree route:
  Squarefree GN
  -> ¬ q^2 ∣ GN
  -> valuation <= 1
```

として読める。

つまり、squarefree が主役ではなく、**NoLift が主役**。
squarefree は「選ばれた q に対する NoLift を保証する十分条件」になった。

これは非常に良い整理じゃ。

## `primitive_prime_GN_ne_zero`

これも良い切り出し。

```lean
lemma primitive_prime_GN_ne_zero
    {q a b d : ℕ}
    (_hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hab_lt : b < a) :
    GN d (a - b) b ≠ 0
```

実際には `_hq` は使っていないように見えるが、命名と配置上は「primitive witness 文脈で使う GN 非ゼロ補題」として許容できる。

もし将来さらに純化するなら、

```lean
lemma GN_ne_zero_of_pos_exp_of_lt
    {a b d : ℕ} (hd : 0 < d) (hab_lt : b < a) :
    GN d (a - b) b ≠ 0
```

のように `PrimitiveBeam` 非依存の一般補題へ昇格してもよい。
ただ、今は `PrimitiveBeam` 内での補助補題なので問題なし。

## `primitive_prime_padic_bound_diff_of_squarefree_GN_local`

この theorem はかなり良い。

```lean
lemma primitive_prime_padic_bound_diff_of_squarefree_GN_local
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    padicValNat q (a ^ d - b ^ d) ≤ 1
```

旧 wrapper にあった、

```lean
Nat.Prime d
3 ≤ d
0 < b
Nat.Coprime a b
¬ d ∣ a - b
```

が消えているのが大きい。

これらは「Zsigmondy から primitive witness を作るための仮定」であって、
すでに

```lean
PrimitivePrimeFactorOfDiffPow q a b d
```

を持っているなら valuation bound 自体には不要。

この仮定削減は正しい。

## Petal 側も良い

Petal 側の squarefree wrapper が、

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

へ直接委譲するようになり、

```lean
hb
hcop
hred
```

が指定 witness 版から消えたのは良い。

```lean
theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
    {c b q : ℕ} (hbc : b < c)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hG_sq : Squarefree (GN 3 (c - b) b)) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1
```

この形はかなり自然じゃ。

`hred` は存在定理で Zsigmondy witness を取る時には必要。
しかし、すでに `hprim` がある指定 witness 版では不要。
この区別が Lean API に反映された。

## 互換 wrapper を残した判断も良い

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN
```

は旧 caller 向けに残しておくのが良い。

ただし内部は、

```lean
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

へ委譲。

これはかなり良い deprecation 準備になっている。

```text
旧 caller:
  重い signature のまま呼べる

新 caller:
  local squarefree helper を直接呼ぶ

内部構造:
  NoLift route が本命
```

## 気になる点は小さい

一点だけ、`primitive_prime_GN_ne_zero` の `_hq` は使われていないので、lint 方針によっては気になるかもしれぬ。
ただし Lean 的には `_hq` なので意図的未使用として扱える。API の文脈性を重視するならこのままでよい。

より純粋にするなら将来、

```lean
lemma GN_ne_zero_of_pow_sub_factor
```

みたいな一般補題へ切り出せる。
今すぐ必要ではない。

## 全体構造

今回で、旧 research placeholder の正しい置換系譜はこう固まった。

```text
偽:
  primitive-ish q
  -> padicValNat q (a^d - b^d) <= 1

正:
  PrimitivePrimeFactorOfDiffPow q a b d
  + ¬ q^2 ∣ GN d (a-b) b
  -> padicValNat q (a^d - b^d) <= 1

十分条件:
  PrimitivePrimeFactorOfDiffPow q a b d
  + Squarefree (GN d (a-b) b)
  -> padicValNat q (a^d - b^d) <= 1
```

Petal d=3 では、

```text
BoundaryD3Reduced
  -> Zsigmondy primitive q
  -> PrimitivePrimeFactorOfDiffPow q c b 3
  -> AnchoredS0Carrier q c b q
  -> NoLift/Squarefree GN3 があれば valuation <= 1
```

ここまで Lean API で通った。

## 次の一手

次は、かなり自然にこれじゃな。

```text
FLT / ABC 側で旧 research placeholder を参照している箇所を調べ、
NoLift route か squarefree local route へ置換する。
```

見るべきは、

```lean
squarefree_implies_padic_val_le_one_research
padicValNat_primitive_prime_factor_le_one_research
```

の参照元。

置換先はだいたい二系統。

```lean
primitive_prime_padic_bound_diff_of_noLift_GN
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

Petal d=3 文脈なら、

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
primitiveD3_padicValNat_le_one_of_squarefree_GN
```

じゃな。

うむ。
これは良い進捗。NoLift が valuation 層の本命として確定し、squarefree は十分条件 wrapper に退いた。かなり理想的な形になってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
index ecec0c90..66a60564 100644
--- a/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
+++ b/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
@@ -101,6 +101,24 @@ lemma primitive_prime_padic_eq_GN
   have hzero : padicValNat q (a - b) = 0 := padicValNat.eq_zero_of_not_dvd hq_ndiv
   simpa [hzero] using hpadic
 
+/--
+For a positive exponent and a strict body boundary `b < a`, the `GN` factor
+attached to a primitive prime witness is nonzero.
+-/
+lemma primitive_prime_GN_ne_zero
+    {q a b d : ℕ}
+    (_hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hab_lt : b < a) :
+    GN d (a - b) b ≠ 0 := by
+  intro hGN0
+  have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
+    have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
+    exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab_lt hd_ne)
+  have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
+    simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
+  rw [hfactor, hGN0, mul_zero] at hdiff_ne
+  exact hdiff_ne rfl
+
 /--
 Honest local no-lift route for the primitive-prime valuation bound:
 if the selected primitive prime `q` does not lift to `q^2` on the `GN` side,
@@ -120,15 +138,8 @@ lemma primitive_prime_padic_bound_diff_of_noLift_GN
       padicValNat q (a ^ d - b ^ d) =
         padicValNat q (GN d (a - b) b) :=
     primitive_prime_padic_eq_GN hq hd hd1 hab_lt
-  have hGN_ne : GN d (a - b) b ≠ 0 := by
-    intro hGN0
-    have hdiff_ne : a ^ d - b ^ d ≠ 0 := by
-      have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
-      exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hab_lt hd_ne)
-    have hfactor : a ^ d - b ^ d = (a - b) * GN d (a - b) b := by
-      simpa using pow_sub_pow_factor_cosmic_N (a := a) (b := b) (d := d) hd hab_lt
-    rw [hfactor, hGN0, mul_zero] at hdiff_ne
-    exact hdiff_ne rfl
+  have hGN_ne : GN d (a - b) b ≠ 0 :=
+    primitive_prime_GN_ne_zero hq hd hab_lt
   by_contra h_not_le
   have htwo_le_diff : 2 ≤ padicValNat q (a ^ d - b ^ d) := by
     omega
@@ -140,6 +151,34 @@ lemma primitive_prime_padic_bound_diff_of_noLift_GN
         (GN d (a - b) b) 2 hGN_ne).2 htwo_le_GN
   exact hNoLift hq2_dvd_GN
 
+/--
+Local squarefree route for the primitive-prime valuation bound.
+
+This is a sufficient-condition wrapper around
+`primitive_prime_padic_bound_diff_of_noLift_GN`: squarefree `GN` forbids the
+selected primitive witness from lifting to `q^2`.
+-/
+lemma primitive_prime_padic_bound_diff_of_squarefree_GN_local
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hG_sq : Squarefree (GN d (a - b) b)) :
+    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
+  have hGN_ne : GN d (a - b) b ≠ 0 :=
+    primitive_prime_GN_ne_zero hq hd hab_lt
+  have hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b := by
+    intro hq2_dvd
+    have hVal : padicValNat q (GN d (a - b) b) ≤ 1 :=
+      DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree
+        hq.1 hGN_ne hG_sq
+    have h2_le : 2 ≤ padicValNat q (GN d (a - b) b) := by
+      exact
+        (@padicValNat_dvd_iff_le q (Fact.mk hq.1)
+          (GN d (a - b) b) 2 hGN_ne).1 hq2_dvd
+    exact (not_le_of_gt h2_le) hVal
+  exact primitive_prime_padic_bound_diff_of_noLift_GN hq hd hd1 hab_lt hNoLift
+
 /--
 Honest repair route for the primitive-prime valuation bound:
 once `Squarefree (GN d (a - b) b)` is available, the old research placeholder is unnecessary.
@@ -147,29 +186,14 @@ once `Squarefree (GN d (a - b) b)` is available, the old research placeholder is
 lemma primitive_prime_padic_bound_diff_of_squarefree_GN
     {q a b d : ℕ}
     (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
-    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
-    (hpnd : ¬ d ∣ a - b)
+    (hab_lt : b < a) (_hb : 0 < b) (_hab : Nat.Coprime a b)
+    (_hpnd : ¬ d ∣ a - b)
     (hq : PrimitivePrimeFactorOfDiffPow q a b d)
     (hG_sq : Squarefree (GN d (a - b) b)) :
     padicValNat q (a ^ d - b ^ d) ≤ 1 := by
-  have hq_prime : Nat.Prime q := hq.1
-  have hq_div_pow : q ∣ a ^ d - b ^ d := hq.2.1
+  have hd_pos : 0 < d := hd_prime.pos
   have hd1 : 1 < d := by omega
-  have hq_ndiv_diff : ¬ q ∣ a - b :=
-    primitive_prime_not_dvd_boundary hq hd1
-  exact
-    DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_honest
-      (a := a) (b := b) (d := d) (q := q)
-      hd_prime
-      hd_ge
-      hab_lt
-      hb
-      hab
-      hpnd
-      hq_prime
-      hq_div_pow
-      hq_ndiv_diff
-      hG_sq
+  exact primitive_prime_padic_bound_diff_of_squarefree_GN_local hq hd_pos hd1 hab_lt hG_sq
 
 /-- Specialized `Body = x * GN d x u` form of `primitive_prime_dvd_GN`. -/
 lemma primitive_prime_dvd_GN_body
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index d6709d58..b9fb7b57 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1364,9 +1364,15 @@ The generic no-lift valuation helper has also been promoted to
 `DkMath.NumberTheory.PrimitiveBeam`:
 
 ```lean
+primitive_prime_GN_ne_zero
 primitive_prime_padic_bound_diff_of_noLift_GN
+primitive_prime_padic_bound_diff_of_squarefree_GN_local
 ```
 
+The local squarefree helper is a sufficient-condition wrapper over the no-lift
+helper.  The older heavier squarefree wrapper remains available for callers
+that still use the previous primitive-prime repair signature.
+
 Meaning:
 
 ```text
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
index bc884b57..acfed62c 100644
--- a/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
+++ b/lean/dk_math/DkMath/Petal/PrimitiveD3ValuationBridge.lean
@@ -58,21 +58,17 @@ Petal contribution is only the `BoundaryD3Reduced` vocabulary and the
 Zsigmondy-to-PrimitiveBeam witness conversion.
 -/
 theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
-    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
-    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
+    {c b q : ℕ} (hbc : b < c)
     (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
     (hG_sq : Squarefree (GN 3 (c - b) b)) :
     padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
   exact
-    primitive_prime_padic_bound_diff_of_squarefree_GN
+    primitive_prime_padic_bound_diff_of_squarefree_GN_local
       (q := q) (a := c) (b := b) (d := 3)
-      Nat.prime_three
+      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
+      (by norm_num)
       (by norm_num)
       hbc
-      hb
-      hcop
-      hred
-      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
       hG_sq
 
 /--
@@ -119,7 +115,7 @@ theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree
   exact
     ⟨q, hprim, hprimitive, hcarrier,
       primitiveD3_padicValNat_le_one_of_squarefree_GN
-        hbc hb hcop hred hprim hG_sq⟩
+        hbc hprim hG_sq⟩
 
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index e87f5a3c..0023c1fb 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -379,9 +379,15 @@ The underlying local no-lift valuation helper is now available in
 `DkMath.NumberTheory.PrimitiveBeam` as:
 
 ```lean
+primitive_prime_GN_ne_zero
 primitive_prime_padic_bound_diff_of_noLift_GN
+primitive_prime_padic_bound_diff_of_squarefree_GN_local
 ```
 
+The older heavier squarefree wrapper is kept for compatibility, but the local
+route is now the canonical reading: squarefree `GN` supplies no-lift for the
+selected witness.
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
````
`````
