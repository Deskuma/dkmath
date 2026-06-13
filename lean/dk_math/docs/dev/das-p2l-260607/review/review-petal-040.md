# Git diff / Report / Review

## Upd: docs: ABC

gch: 1c4de475f322676e29150e92a7f0f5210be7c1c7

## Report

ABC closure 側を進めました。今回はコード追加ではなく、接続状況の整理と閉じ判定です。

更新した内容：

- [Petal-Zsigmondy-Preflight.md](/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md) の “Honest Replacement Targets” を現状へ更新
  - 本命: `NoLift`
  - 十分条件: local squarefree
  - 旧 API: compatibility wrapper

- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md) に caller survey と ABC-side closure status を追記
  - 旧 ABC wrapper の直接 caller は compatibility regression sample
  - 旧 ValuationFlow wrapper の直接 caller は ABC compatibility wrapper
  - したがって、今すぐ必須の置換作業はなし

検証：

```sh
lake build DkMath.ABC.ValuationFlowBridgeExamples
git diff --check
```

どちらも通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告は継続です。

これで ABC 側は、`NoLift API / local squarefree API / compatibility API / examples / docs closure` が揃った状態です。

## Review

うむ。**次は FLT 側でよい**。
ABC 側はこの docs-only closure で一区切りとして妥当じゃ。

今回の ABC closure 判定は、かなり良い。

```text
ABC 側:
  NoLift API
  local squarefree API
  compatibility API
  squarefree example
  non-squarefree local NoLift example
  docs closure
```

ここまで揃っていて、caller survey でも旧 ABC wrapper の直接 caller が compatibility regression sample に限定されているなら、**今すぐ ABC 側で必須の置換作業はない** と見てよい。

## レビュー結論

```text
1c4de475...
  -> 採用可

ABC closure:
  -> 妥当

次:
  -> FLT 側へ進むのが自然
```

## なぜ次は FLT 側か

理由ははっきりしている。
ABC 側では、旧 heavy squarefree route はもう互換 wrapper に退いた。

一方 FLT 側には、まだ次のような構造が残っている。

```lean
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
```

この中に、まだ research placeholder 経由の valuation root がある。

```lean
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_research
```

ただし、FLT 側にはすでに honest route もかなりある。

```lean
TriominoNoLiftGNBridge
TriominoSquarefreeGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
triominoNoWieferichBridge_of_not_sq_GN
triominoNoWieferichBridge_of_squarefree_GN
```

つまり FLT 側は、ゼロから作る段階ではなく、

```text
既にある honest route を
PrimitiveBeam NoLift 本命ルートへ寄せて薄くする段階
```

じゃな。

## FLT 側で見るべき場所

まず見るべきはここ。

```path
lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
```

ここには現在、二種類の道が同居している。

### 1. 旧 research route

```lean
triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_primitivePrime_core
```

これはまだ

```lean
padicValNat_primitive_prime_factor_le_one_research
```

へ依存している。
これは偽 placeholder 系なので、本線化する対象ではない。

### 2. honest route

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

こちらが本命。
ただし現状では、`of_noLiftGNBridge` がまだ FLT 側で手書き証明を持っている。

今ならこれを、

```lean
PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
```

へ委譲する形にできる可能性が高い。

## FLT 側の次の一手

いきなり FLT descent 本体に行くより、まずは **NoWieferichResearch の薄型化** がよい。

狙いはこれ。

```text
FLT primitive branch assumptions
  -> PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p
  -> PrimitiveBeam noLift theorem
  -> TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
```

現在の FLT target は、だいたいこういう仮定を持っている。

```lean
PrimeGe5CounterexamplePack p x y z
¬ p ∣ z - y
Nat.Prime q
q ∣ z ^ p - y ^ p
¬ q ∣ z - y
```

一方 `PrimitiveBeam` が欲しいのは、

```lean
PrimitivePrimeFactorOfDiffPow q z y p
```

なので、最初に作ると良さそうなのはこの変換補題じゃ。

```lean
theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ z - y)
    (hqP : Nat.Prime q)
    (hq_dvd_diff : q ∣ z ^ p - y ^ p)
    (hq_not_dvd_gap : ¬ q ∣ z - y) :
    PrimitivePrimeFactorOfDiffPow q z y p
```

証明には既存のこの系統が使えるはず。

```lean
prime_exp_not_dvd_diff_imp_primitive
```

すでに `PrimitiveBeam.exists_primitive_prime_factor_as_prop` でも使われているので、かなり通る見込みがある。

必要になる `Nat.Coprime z y` は、FLT pack から既にこう取れている。

```lean
have hzy_coprime : Nat.Coprime z y := by
  exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
```

## その次に薄くできる theorem

変換補題ができたら、次はこれを薄くする。

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
```

現在は `padicValNat` と `q^2 ∣ GN` の議論を FLT 側で手書きしている。
これを次のようにできる。

```lean
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
    (hNoLift : TriominoNoLiftGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  have hPrim : PrimitivePrimeFactorOfDiffPow q z y p :=
    primitivePrimeFactorOfDiffPow_of_FLT_branch
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  exact
    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
      hPrim
      hpack.hp.pos
      hpack.hp.one_lt
      hpack.hyz_lt
      (hNoLift hpack hpB hqP hq_dvd_diff hq_not_dvd_gap)
```

細部の名前は調整が必要じゃが、方向はこれ。

すると FLT 側も ABC 側と同じ構造になる。

```text
PrimitiveBeam:
  primitive witness + NoLift GN
  -> padicValNat <= 1

FLT:
  PrimeGe5CounterexamplePack branch
  -> PrimitiveBeam witness
  -> PrimitiveBeam theorem を呼ぶ
```

## squarefree 版も同じく薄くできる

その次に、

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

も、現在の squarefree core ではなく、

```lean
PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

か、または

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
```

経由へ寄せられる。

ただしこれは急がなくてよい。
本命は NoLift 版。

```text
NoLift:
  本命

Squarefree:
  NoLift の十分条件 wrapper
```

という整理を FLT 側にも反映するのが目的じゃ。

## FLT 側で注意する点

ここは重要。

`CosmicPetalBridgeGNNoWieferichResearch.lean` には、名前に `Research` が入っている。
ここはまだ研究核・隔離場なので、いきなり全部を本線へ移す必要はない。

まずやるべきは、

```text
Research placeholder 依存の root を消す
```

ではなく、

```text
Research ファイル内にある honest route を PrimitiveBeam 本命 API へ寄せる
```

こと。

つまり第一段階は refactor / thin wrapper 化でよい。

## 次の作業単位のおすすめ

### Step FLT-1: primitive witness 変換補題

候補名:

```lean
primitivePrimeFactorOfDiffPow_of_triomino_branch
```

または FLT namespace なら、

```lean
triominoPrimitivePrimeFactorOfDiffPow_of_branch
```

意味:

```text
PrimeGe5CounterexamplePack branch
+ q ∣ z^p - y^p
+ q ∤ z-y
  -> PrimitivePrimeFactorOfDiffPow q z y p
```

### Step FLT-2: NoLift valuation target を PrimitiveBeam へ委譲

対象:

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
```

目的:

```text
手書き padic 証明を削除し、
PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN に委譲
```

### Step FLT-3: squarefree wrapper を NoLift / local squarefree へ寄せる

対象:

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

目的:

```text
squarefree は compatibility / sufficient-condition wrapper として読む
```

### Step FLT-4: default injection の整理調査

見る場所:

```lean
CosmicPetalBridgeGNNoWieferichDefault.lean
CosmicPetalBridgeGNDescentBQuarantine.lean
TriominoSquarefreeGNBridgeProvider.lean
TriominoSquarefreeGNBridgeProviderImpl.lean
```

ここで、

```text
default がまだ research core を注入している箇所
provider 経由で honest route を使える箇所
quarantine に隔離されている箇所
```

を分類する。

## 今回 docs commit の評価

ABC closure docs としては良い。
特にこの分類は正しい。

```text
current direct Lean callers of the old ABC wrapper:
  DkMath.ABC.ValuationFlowBridgeExamples

current direct Lean callers of the old ValuationFlow wrapper:
  DkMath.ABC.ValuationFlowBridge
```

これはつまり、

```text
ABC では旧 wrapper が意図的に残っているだけ
```

ということ。
よって ABC は closure 判定でよい。

## 結論

はい、**次は FLT 側** じゃ。

ただし狙うのは FLT 大本丸ではなく、まずここ。

```text
FLT / PrimeProvider / NoWieferich valuation route の薄型化
```

具体的には、

```text
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
```

を、

```text
PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
```

へ接続すること。

これが通れば、FLT 側も ABC 側と同じ思想になる。

```text
NoLift が本命。
Squarefree は十分条件。
旧 research valuation は quarantine / compatibility。
```

ここまで行けば、`ZsigmondyCyclotomicResearch.lean` の偽 placeholder にぶら下がる範囲がさらに縮む。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 4f2aa4f8..5718302a 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1486,6 +1486,42 @@ PrimitiveBeam no-lift valuation
 This keeps `NoLift` as the main multiplicity hypothesis while preserving the
 older squarefree API for downstream callers.
 
+Caller survey:
+
+```text
+current direct Lean callers of the old ABC wrapper:
+  DkMath.ABC.ValuationFlowBridgeExamples
+
+current direct Lean callers of the old ValuationFlow wrapper:
+  DkMath.ABC.ValuationFlowBridge
+
+classification:
+  example caller:
+    intentionally kept as a compatibility regression sample
+
+  ABC wrapper caller:
+    intentionally kept as the public compatibility surface
+
+  new development:
+    should use noLift_beam_bounds_local_load when local NoLift is available
+    should use squarefree_beam_bounds_local_load_local when only full GN
+    squarefreeness is available
+```
+
+ABC-side closure status:
+
+```text
+implemented:
+  NoLift API
+  local squarefree API
+  compatibility API
+  squarefree example
+  non-squarefree local NoLift example
+
+remaining:
+  no mandatory ABC-side replacement work before returning to Petal/Zsigmondy
+```
+
 Expected validation:
 
 ```sh
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
index de8ea9f3..a50f7c8c 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
@@ -183,35 +183,55 @@ or replaced at the callers by honest squarefree/no-lift APIs.
 
 ## Honest Replacement Targets
 
-The honest squarefree theorem already exists:
+The current honest replacement route is local no-lift first:
 
 ```lean
-DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
+DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
+DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_noLift_beam
+DkMath.ABC.noLift_beam_bounds_local_load
 ```
 
-This theorem requires:
+This route requires only the selected primitive channel to avoid lifting on the
+`GN` side:
 
 ```lean
-Squarefree (GN d (a - b) b)
+¬ q ^ 2 ∣ GN d (a - b) b
 ```
 
-The valuation-flow wrapper also exists:
+Full beam squarefreeness is now treated as a sufficient condition, not as the
+main hypothesis:
 
 ```lean
-DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
+DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN_local
+DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
+DkMath.ABC.squarefree_beam_bounds_local_load_local
 ```
 
-This is the ABC-facing mass-control form.
-
-The underlying primitive-beam route also exists:
+The compatibility wrappers remain available for old callers that still carry
+the heavier squarefree-beam signature:
 
 ```lean
-DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN
-DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_eq_GN
 DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN
+DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
+DkMath.ABC.squarefree_beam_bounds_local_load
+```
+
+The separation is intentional:
+
+```text
+NoLift at q:
+  local multiplicity control for the selected primitive channel
+
+Squarefree GN:
+  global sufficient condition for all channels
+
+Compatibility wrappers:
+  migration surface for older callers
 ```
 
-These are the real replacement targets for valuation `<= 1`.
+`DkMath.ABC.ValuationFlowBridgeExamples` records both a squarefree sample and a
+non-squarefree local NoLift sample, so this hierarchy is now regression-checked
+on concrete data.
 
 ## Current Research Dependencies
 
````
`````
