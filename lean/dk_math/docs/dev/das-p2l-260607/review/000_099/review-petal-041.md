# Git diff / Report / Review

## Upd: FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch

gch: 9e84d2fb48beaafdd72f2c2e36d2f16c0a7a8308

## Report

FLT 側へ進めました。今回は `CosmicPetalBridgeGNNoWieferichResearch` の honest route を `PrimitiveBeam` 本命ルートへ寄せています。

追加・変更した要点：

- [CosmicPetalBridgeGNNoWieferichResearch.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean)
  - `primitivePrimeFactorOfDiffPow_of_FLT_branch` を追加
  - FLT Branch-B の入力から `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p` へ変換
  - `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge` を手書き valuation 証明から `PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN` への委譲に変更
  - `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge` を NoLift wrapper 経由へ変更

これで FLT 側も ABC 側と同じ階層になりました。

```text
NoLift:
  main local multiplicity route

Squarefree:
  sufficient condition that produces NoLift

Research placeholder:
  still isolated in old research core
```

Roadmap には Step 6.3 として記録しました。

検証：

```sh
lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
git diff --check
```

どちらも通っています。既存の `ZsigmondyCyclotomicResearch`, `GcdNextResearch`, `TriominoCosmicBranchA` の `sorry` 警告は継続です。

## Review

おお、これは **FLT 側も本命 NoLift route へ接続成功** じゃ。
採用でよい。

今回の差分で、ABC 側と FLT 側の構造が揃った。

```text id="470vvx"
PrimitiveBeam:
  primitive witness + local NoLift GN
  -> padicValNat <= 1

ABC:
  PrimitiveBeam theorem を diffMass / local load として読む

FLT:
  Branch-B primitive-prime 入力を PrimitiveBeam witness に変換し、
  PrimitiveBeam theorem へ委譲する
```

## レビュー結論

```text id="lj3stc"
9e84d2fb...
  -> 採用可

FLT NoWieferich honest route
  -> PrimitiveBeam 本命 route へ薄型化成功

Squarefree route
  -> NoLift の十分条件 wrapper 化成功

Research placeholder
  -> まだ隔離場に残るが、honest route からは外れた
```

## 一番大きい進展

追加されたこれが本体じゃな。

```lean id="zjwl1i"
theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_dvd_diff : q ∣ (z ^ p - y ^ p))
    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p
```

これは FLT Branch-B の入力を、`PrimitiveBeam` の共通語彙へ翻訳する橋。
これができたので、FLT 側も独自に p-adic valuation 証明を持つ必要がなくなった。

流れはこうじゃ。

```text id="e4m0c7"
PrimeGe5CounterexamplePack p x y z
q ∣ z^p - y^p
q ∤ z-y
  -> PrimitivePrimeFactorOfDiffPow q z y p
  -> PrimitiveBeam noLift valuation theorem
  -> padicValNat q (z^p - y^p) <= 1
```

## `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge`

ここが非常に良い薄型化になっている。

旧版では FLT 側で、

```text id="nfjv0d"
GN 非ゼロ
padicValNat GN <= 1
padicValNat diff = padicValNat GN
```

を手で処理していた。

今回からは、

```lean id="0l2jyz"
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
```

へ委譲。

これは正しい。

FLT 側の責務は、

```text id="68zfxd"
FLT branch から primitive witness を作る
NoLift bridge から ¬ q^2 ∣ GN を受け取る
```

まで。
valuation 本体は `PrimitiveBeam` の仕事。かなり綺麗じゃ。

## squarefree route も正しい

```lean id="y4c5fe"
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
    (hSq : TriominoSquarefreeGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  exact
    triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
      (triominoNoLiftGNBridge_of_squarefree_GN hSq)
```

これは理想的。

```text id="umxs0r"
Squarefree GN
  -> NoLift GN
  -> valuation <= 1
```

という階層が FLT 側にも反映された。

これで ABC と FLT が同じ思想になった。

```text id="dssg13"
NoLift:
  main local multiplicity route

Squarefree:
  sufficient condition

Research placeholder:
  quarantine / old research core
```

## `_hpB` が未使用なのは問題ない

`primitivePrimeFactorOfDiffPow_of_FLT_branch` では、

```lean id="g3ii5r"
(_hpB : ¬ p ∣ (z - y))
```

が未使用になっている。

これは自然じゃ。
primitive witness への変換自体には、主に

```lean id="8hckyo"
hq_not_dvd_gap : ¬ q ∣ z - y
```

が効く。
`hpB` は FLT Branch-B 文脈を保つための引数で、後続の NoLift bridge や squarefree bridge では必要になることがある。なので wrapper の署名に残してよい。

## まだ残る厚み

ここはまだ Research file 内なので、

```lean id="txd6lr"
import DkMath.NumberTheory.ZsigmondyCyclotomicResearch
```

は残っている。

ただし今回の honest route は、少なくとも valuation core については `PrimitiveBeam` に寄った。
つまり、今はこういう状態。

```text id="u34se0"
Research file:
  旧 placeholder route と honest route が同居

honest route:
  PrimitiveBeam 経由で no-sorry theorem を利用

old research core:
  まだ隔離されて残る
```

これは移行段階として妥当。

将来さらに綺麗にするなら、honest route だけを

```text id="k0unsn"
CosmicPetalBridgeGNNoWieferichPrimitiveBeam
```

または

```text id="iu3fi8"
CosmicPetalBridgeGNNoWieferichValuation
```

のような非 `Research` ファイルへ抽出するのが自然じゃな。

## 次に見るべきところ

この commit の次は、FLT 側で caller survey じゃ。

見る対象はこの辺り。

```text id="i8kfp7"
triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
triominoNoWieferichBridge_of_not_sq_GN
triominoNoWieferichBridge_of_squarefree_GN
```

特に、旧 research placeholder route が downstream でまだ使われているか確認したい。

```text id="lu9e0q"
old research valuation core:
  still used by default provider?
  only kept as legacy target?
  quarantined?
```

これが分かれば、FLT 側も ABC と同じように closure 判定できる。

## `#print axioms` 推奨

次に確認するならこのあたりじゃ。

```lean id="r7i4yh"
#print axioms DkMath.FLT.primitivePrimeFactorOfDiffPow_of_FLT_branch
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

ここに `sorryAx` が無ければ、FLT honest route はかなり安定。

[DkMathTest: CosmicPetalBridgeGNNoWieferichResearch](/lean/dk_math/DkMathTest/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean) - all OK: 2026/06/14  5:00

## 判定

今回で、

```text id="2du2q5"
ABC:
  NoLift -> diffMass/local load

FLT:
  NoLift -> primitive branch padicValNat <= 1
```

が揃った。

これは大きい。
旧 `padicValNat_primitive_prime_factor_le_one_research` を救うのではなく、**PrimitiveBeam NoLift route へ置換する**方針が、ABC と FLT の両方で実装上も通った。

次は FLT 側の closure survey、特に default/provider/quarantine の整理じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
index 1f32036a..7786ee2e 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/

 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
+import DkMath.NumberTheory.PrimitiveBeam
 import DkMath.NumberTheory.ZsigmondyCyclotomicResearch

 #print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch"
@@ -74,17 +75,37 @@ theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le
   exact hVal hpack hpB hqP hq_dvd_diff hq_not_dvd_gap

 /--
-squarefree bridge が供給されれば、primitive-prime branch の valuation target は
-既存 honest route だけで直ちに従う。
+Translate the FLT Branch-B primitive-prime inputs into the shared
+`PrimitiveBeam` primitive-factor predicate.
+
+This is the main handshake between the FLT NoWieferich branch and the newer
+`PrimitiveBeam` valuation route.
 -/
-theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
-    (hSq : TriominoSquarefreeGNBridge) :
-    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
-  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
+theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
+    {p x y z q : ℕ}
+    (hpack : PrimeGe5CounterexamplePack p x y z)
+    (_hpB : ¬ p ∣ (z - y))
+    (hqP : Nat.Prime q)
+    (hq_dvd_diff : q ∣ (z ^ p - y ^ p))
+    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
+    DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p := by
+  refine ⟨hqP, hq_dvd_diff, ?_⟩
+  have hzy_coprime : Nat.Coprime z y := by
+    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
+  intro k hk_pos hk_lt
   exact
-    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core
-      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-      (hSq hpack hpB hqP hq_dvd_diff hq_not_dvd_gap)
+    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
+      (a := z) (b := y) (d := p) (q := q)
+      hpack.hp
+      hpack.hp.one_lt
+      hqP
+      hzy_coprime
+      hpack.hyz_lt
+      hpack.y_pos
+      hq_dvd_diff
+      hq_not_dvd_gap
+      hk_pos
+      hk_lt

 /--
 `padicValNat q (GN p (z - y) y) ≤ 1` が供給できれば、
@@ -136,24 +157,34 @@ theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
     (hNoLift : TriominoNoLiftGNBridge) :
     TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
   intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  have hGN_ne : GN p (z - y) y ≠ 0 :=
-    triominoWieferichShrink_GN_ne_zero_core
+  have hPrim :
+      DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p :=
+    primitivePrimeFactorOfDiffPow_of_FLT_branch
       hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
   have hGN_not_sq : ¬ q ^ 2 ∣ GN p (z - y) y :=
     hNoLift hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  have hGN_le : padicValNat q (GN p (z - y) y) ≤ 1 := by
-    by_contra h_not_le
-    have h_two_le : 2 ≤ padicValNat q (GN p (z - y) y) := by
-      omega
-    have hq2_dvd_GN : q ^ 2 ∣ GN p (z - y) y :=
-      (@padicValNat_dvd_iff_le q (Fact.mk hqP) (GN p (z - y) y) 2 hGN_ne).2 h_two_le
-    exact hGN_not_sq hq2_dvd_GN
-  have hEq :
-      padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) :=
-    triominoWieferichShrink_padicValNat_diff_eq_GN_core
-      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  rw [hEq]
-  exact hGN_le
+  exact
+    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
+      hPrim
+      hpack.hp.pos
+      hpack.hp.one_lt
+      hpack.hyz_lt
+      hGN_not_sq
+
+/--
+squarefree bridge が供給されれば、primitive-prime branch の valuation target は
+NoLift bridge 経由で従う。
+
+This keeps the FLT-side hierarchy aligned with the ABC-side hierarchy:
+local NoLift is the main route, and full `GN` squarefreeness is a sufficient
+condition.
+-/
+theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
+    (hSq : TriominoSquarefreeGNBridge) :
+    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
+  exact
+    triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
+      (triominoNoLiftGNBridge_of_squarefree_GN hSq)

 /--
 phase-15 の研究核:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 5718302a..5939018c 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1530,6 +1530,80 @@ lake build DkMath.ABC.ValuationFlowBridge
 lake build DkMath.ABC.ValuationFlowBridgeExamples
 ```

+### Step 6.3: Thin FLT NoWieferich Research Bridge
+
+Status:
+
+```text
+implemented
+```
+
+`DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch` now has a
+direct handshake from the FLT Branch-B primitive-prime inputs to the shared
+`PrimitiveBeam` predicate:
+
+```lean
+primitivePrimeFactorOfDiffPow_of_FLT_branch
+```
+
+This theorem translates:
+
+```text
+PrimeGe5CounterexamplePack p x y z
+q prime
+q divides z^p - y^p
+q does not divide z - y
+```
+
+into:
+
+```lean
+DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p
+```
+
+The NoLift target wrapper:
+
+```lean
+triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
+```
+
+now delegates its valuation core to:
+
+```lean
+DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
+```
+
+The squarefree target wrapper:
+
+```lean
+triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
+```
+
+is now routed through the NoLift wrapper via:
+
+```lean
+triominoNoLiftGNBridge_of_squarefree_GN
+```
+
+This aligns the FLT-side hierarchy with the ABC-side hierarchy:
+
+```text
+NoLift:
+  main local multiplicity route
+
+Squarefree:
+  sufficient condition that produces NoLift
+
+Research placeholder:
+  still isolated in the old research core, not used by the honest NoLift target
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
+```
+
 ### Step 7: Refactor imports gradually

 Status:
````
`````
