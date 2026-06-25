# Git diff / Report / Review

## Upd: Petal.ErdosBridge, NumberTheory.PrimitiveSet.ValuationBudget

gch: c2f47bf27d49a1d39b1b83081720b26d3c23f92c

## Report

進めました。今回は review051 の次の本命に向けて、`Set.InjOn` より一段 Petal/address 側が扱いやすい `NatPairwiseDistinctOn` 入口を追加しました。

変更点:

- [ValuationBudget.lean](/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean)
  - `natPairwiseDistinctOn_injOn`
  - `natBaseMultiplicityBudgetOn_of_pairwiseDistinct_of_dvd`

- [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean)
  - `petalPrimeChannelFamily_multiplicityBudget_GN_of_pairwiseDistinct`
  - `petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct`
  - `petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one`

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean)
  - `DkMath.Petal.ErdosBridge` を公開 import に追加
  - パッケージ説明にも Erdos log-capacity bridge を追記

これで次の target はかなり明確です。

```text
Petal address / noncollision
  -> NatPairwiseDistinctOn I qOf
  -> GN multiplicity budget
  -> log SubProbability
```

検証:

- `lake build DkMath.NumberTheory.PrimitiveSet.ValuationBudget` 成功
- `lake build DkMath.Petal.ErdosBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

今回追加分も `sorry` なしです。既存の `ZsigmondyCyclotomicResearch.lean` の warning は再表示されますが、今回の変更とは別件です。

## Review

うむ。これは **実験段階から公開 API 段階へ移行した** と見てよい。
今回の差分は、単に theorem を足しただけではなく、`DkMath.Petal` から `ErdosBridge` が見えるようになった。つまり、Petal の公式導線に **Erdős log-capacity bridge** が入った、ということじゃ。

## 1. 状況の核心

今回の到達点はこう。

```text id="tkef8n"
PetalPrimeChannel family
  + NatPairwiseDistinctOn I qOf
  -> GN multiplicity budget
  -> log SubProbability
```

以前は、

```text id="14s6om"
Set.InjOn qOf ↑I
```

が必要だった。
これは Lean 的には自然だが、Petal / address 側から見ると少し抽象的すぎる。

今回、

```lean id="q40dbq"
natPairwiseDistinctOn_injOn
natBaseMultiplicityBudgetOn_of_pairwiseDistinct_of_dvd
```

が入ったことで、Petal 側が狙うべき条件が

```text id="l8ex84"
prime label が pairwise distinct
```

になった。これはかなりよい。

`Set.InjOn` は関数論的な言い方。
`NatPairwiseDistinctOn` は観測ラベルの非衝突という言い方。
Petal address / noncollision から出したいのは明らかに後者じゃ。

## 2. 今回の一番大きい意味

次の本命ルートが、かなり具体化した。

```text id="4eww9h"
Petal address / noncollision
  -> NatPairwiseDistinctOn I qOf
  -> GN multiplicity budget
  -> log SubProbability
```

以前は、

```text id="9v9c1c"
address noncollision -> injectivity
```

という少し遠い表現だった。

今回からは、

```text id="8zfxv5"
address noncollision -> pairwise distinct prime labels
```

でよい。

これは研究上かなり自然じゃ。
Petal address は「同じ面・同じ枝・同じ carrier に衝突していない」ことを表したい。そこから `qOf i ≠ qOf j` を出せれば、Erdős 側の budget に接続できる。

## 3. `petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one` の位置づけ

この theorem も地味に重要じゃ。

```lean id="mf3cci"
theorem petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
```

これは、

```text id="juxvox"
各 selected channel が NoLift なら、
各 selected label で padicValNat q GN = 1
```

を family で読めるようにしたもの。

ただし docs に必ず書くべき注意がある。

```text id="iamh56"
この theorem は distinctness を主張しない。
同じ q を複数 index が選んでいれば、同じ one-slot valuation を何度も読んでいるだけ。
```

差分コメントにもそれが明記されておる。これは非常に良い。
NoLift は「局所的には 1 slot」を保証するが、family 全体で「重複なし」を保証するわけではない。

したがって、family budget には依然として

```text id="241vel"
NatPairwiseDistinctOn I qOf
```

が必要になる。

この分離は重要じゃ。

## 4. 公開 import の意味

`DkMath.Petal.lean` に

```lean id="fqb17x"
import DkMath.Petal.ErdosBridge
```

が入った。

これはもう、`ErdosBridge` が「実験中の隠しファイル」ではなく、Petal package の一部として扱われるということじゃ。

そのため、ここからは theorem の説明責任が上がる。

特に docs では、

```text id="dy5ljc"
Petal.ErdosBridge は Erdős #1196 本体を証明するファイルではない。
Petal carrier / GN carrier を Erdos log-capacity machinery へ渡す公開 bridge である。
```

と明記するべきじゃ。

## 5. 現在の正しい説明文

今の状況はこう書くのがよい。

```text id="yhqcqz"
DkMath.Petal.ErdosBridge provides the public bridge from Petal GN carriers to
the finite Erdos #1196 log-capacity route.

It does not prove the analytic Erdos #1196 tail estimate.  Instead, it proves
that Petal prime-channel families can be consumed by the existing
PrimitiveSet log-capacity machinery once the required duplicate-free /
multiplicity-budget conditions are supplied.

The current address-facing target is:

  Petal address noncollision
    -> NatPairwiseDistinctOn I qOf
    -> GN multiplicity budget
    -> log SubProbability.
```

これが正確じゃな。

## 6. docs 整備の優先順位

次は docs を 3 箇所直すのがよい。

### 6.1. `Petal-Overview.md`

ここには公開 API としての説明を足す。

```text id="az4x7q"
DkMath.Petal.ErdosBridge

Purpose:
  Reads Petal GN carriers as Erdos finite log-capacity channels.

Main route:
  PetalPrimeChannel family
    + NatPairwiseDistinctOn labels
    -> NatBaseMultiplicityBudgetOn against GN
    -> realLogRatioWeightProvider.SubProbability

Current research target:
  Petal address / noncollision
    -> NatPairwiseDistinctOn.
```

### 6.2. `Petal-ErdosBridge-ExperimentPlan.md`

これは status を更新する。

```text id="36m0er"
Status:
  planning
```

から、

```text id="4uqrr1"
Status:
  first public bridge implemented
```

へ。

そして「通ったもの」「まだ通っていないもの」を分ける。

通ったもの:

```text id="wzpvg3"
PetalPrimeChannel -> NatPrimeValuedOn
PetalNoLiftPrimeChannel -> padicValNat q GN = 1
PetalPrimeChannel + GN ≠ 0 -> singleton budget
PairwiseDistinct PetalPrimeChannel family -> GN multiplicity budget
PairwiseDistinct PetalPrimeChannel family -> log SubProbability
```

まだ未主張:

```text id="vl8m34"
Petal address noncollision -> NatPairwiseDistinctOn
Zsigmondy -> NoLift
GN carrier -> squarefree
full Erdős #1196 analytic tail estimate
```

この仕分けが大事。

### 6.3. `FLGNB-PetalRoadmap.md`

ここには Step 6.5 を `planned` から `implemented-first-bridge` に進める。

```text id="3d0d9s"
Step 6.5: Petal / Erdos Bridge

Status:
  first public bridge implemented
```

そして次の target を書く。

```text id="t216ld"
Next target:
  Petal address / carrier noncollision should supply NatPairwiseDistinctOn.
```

## 7. 今回の theorem 群の意味整理

今回の追加で、ルートはこうなった。

```text id="2rbhs9"
NatPairwiseDistinctOn
  -> Set.InjOn
  -> NatBaseMultiplicityBudgetOn
```

これが PrimitiveSet 側。

Petal 側では、

```text id="3vyv6y"
PetalPrimeChannel family
  + NatPairwiseDistinctOn
  -> GN multiplicity budget
  -> log SubProbability
```

さらに NoLift 側では、

```text id="sfxn5m"
PetalNoLiftPrimeChannel family
  -> each selected q has padicValNat q GN = 1
```

つまり、今の公開 API は二本柱じゃ。

```text id="ckwqb8"
1. duplicate-free carrier family gives global GN log-capacity budget
2. no-lift carrier family gives local exact one-slot valuation
```

この二本は混ぜてはいけないが、将来合流する。

合流形はおそらくこう。

```text id="cokyxl"
NoLift family
  + NatPairwiseDistinctOn
  -> every selected carrier uses exactly one distinct GN exponent slot
  -> GN log SubProbability
```

この theorem も次に狙ってよい。

## 8. 次に立てるとよい公開向け補題

docs 整備と並行して、公開 API を少し補強するならこれ。

```lean id="ka3jxx"
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
```

形は、

```text id="u3vrfy"
PetalNoLiftPrimeChannel family
  + NatPairwiseDistinctOn
  + 1 < GN
  -> log SubProbability
```

中身は `PetalNoLiftPrimeChannel` から `PetalPrimeChannel` を取り出して、既存の pairwiseDistinct theorem に渡すだけ。

意味はわかりやすい。

```text id="sx7vnj"
distinct no-lift carriers on GN form a finite Erdos log-capacity sub-probability family
```

これは公開 docs に書きやすい。

## 9. 現在の成熟度

わっちの評価はこうじゃ。

```text id="q9k1ub"
ErdosBridge maturity:
  experimental core: complete
  public import: done
  first public docs: needed
  address/noncollision layer: next research target
```

つまり、コードはもう「実験第一段」ではなく **Petal 公開面に載った bridge** になった。
これから必要なのは、利用者が theorem 名を見て迷わないように、

```text id="ohhccn"
どこまで証明済みか
何は仮定なのか
次に何を証明すべきか
```

を docs に固定することじゃ。

## 10. 総括

今回で状況はこう変わった。

以前:

```text id="aj1i8k"
Petal carrier は Erdos route に入れそう
```

現在:

```text id="qmc5w6"
Petal carrier は Erdos route に公開 API として入った
```

以前:

```text id="i1jwsc"
multiplicity budget は外部仮定
```

現在:

```text id="ulyhpa"
pairwise distinct Petal prime labels なら GN multiplicity budget を作れる
```

以前:

```text id="pp4xhq"
NoLift は局所条件
```

現在:

```text id="ia3d9b"
NoLift は padicValNat q GN = 1 として family でも読める
```

これは明確な進展じゃ。
次は docs にこの地図を刻む段階。
そしてその次の本丸は、

```text id="9ydwnk"
Petal address noncollision
  -> NatPairwiseDistinctOn
```

じゃな。

ここが通れば、Petal は Erdős #1196 有限 log-capacity route に対して、単なる入口ではなく **予算生成機構** になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean b/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
index 88e6fb13..a118a57f 100644
--- a/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
+++ b/lean/dk_math/DkMath/NumberTheory/PrimitiveSet/ValuationBudget.lean
@@ -67,6 +67,23 @@ theorem natBaseMultiplicityBudgetOn_iff
       ∀ p, Nat.Prime p → NatBaseMultiplicityOn I pOf p ≤ n.factorization p :=
   Iff.rfl

+/--
+Pairwise distinct selected bases are injective on the selected finite index.
+
+This is the conversion layer between the older duplicate-free vocabulary
+`NatPairwiseDistinctOn` and the newer multiplicity-budget theorem that expects
+`Set.InjOn`.
+-/
+theorem natPairwiseDistinctOn_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (pOf : ι → ℕ)
+    (hdistinct : NatPairwiseDistinctOn I pOf) :
+    Set.InjOn pOf ↑I := by
+  intro i hi j hj hij_eq
+  by_contra hij
+  exact (hdistinct i hi j hj hij) hij_eq
+
 /--
 Injective selected bases give a multiplicity budget when every selected base
 divides `n`.
@@ -114,6 +131,26 @@ theorem natBaseMultiplicityBudgetOn_of_injOn_of_dvd
       exact hex ⟨i, hiI, hip⟩
     simp [hfilter_empty]

+/--
+Pairwise distinct selected bases give a multiplicity budget when every selected
+base divides `n`.
+
+This is the duplicate-free form of
+`natBaseMultiplicityBudgetOn_of_injOn_of_dvd`.
+-/
+theorem natBaseMultiplicityBudgetOn_of_pairwiseDistinct_of_dvd
+    {ι : Type _}
+    (I : Finset ι)
+    (pOf : ι → ℕ)
+    (n : ℕ)
+    (hn0 : n ≠ 0)
+    (hdistinct : NatPairwiseDistinctOn I pOf)
+    (hdvd : ∀ i, i ∈ I → pOf i ∣ n) :
+    NatBaseMultiplicityBudgetOn I pOf n :=
+  natBaseMultiplicityBudgetOn_of_injOn_of_dvd I pOf n hn0
+    (natPairwiseDistinctOn_injOn I pOf hdistinct)
+    hdvd
+
 /--
 For prime-valued selected bases, the exponent of a prime `p` in the selected
 product is exactly the number of selected occurrences of `p`.
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 51959ffe..46d5ccf6 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -21,6 +21,7 @@ import DkMath.Petal.BoundaryD3
 import DkMath.Petal.EisensteinBridge
 import DkMath.Petal.ZsigmondyD3Bridge
 import DkMath.Petal.PrimitiveD3ValuationBridge
+import DkMath.Petal.ErdosBridge

 #print "file: DkMath.Petal"

@@ -44,6 +45,7 @@ basic forms / relative polygon vocabulary
   -> shifted Eisenstein norm bridge
   -> Zsigmondy d = 3 primitive-divisor bridge
   -> squarefree GN3 valuation bridge
+  -> Erdos log-capacity bridge from GN carrier channels
 ```

 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 4b57339e..52e9d27e 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -261,6 +261,59 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_injOn
       I d x u qOf (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hGN))
       hinj hcarrier)

+/--
+Pairwise distinct Petal prime-channel labels on the same GN surface supply an
+Erdos multiplicity budget against that GN surface.
+
+This is the duplicate-free vocabulary version of
+`petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn`.  It is the form that
+an address/noncollision layer should be able to target first.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_pairwiseDistinct
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hdistinct :
+      DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
+    I d x u qOf hGN0
+    (DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn
+      I qOf hdistinct)
+    hcarrier
+
+/--
+Pairwise distinct Petal prime-channel labels on the same GN surface give an
+Erdos sub-probability provider.
+
+This is the current address-facing theorem: once Petal geometry can prove
+pairwise distinct prime labels, the log-capacity bridge is available.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (hdistinct :
+      DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_injOn
+    I d x u qOf hGN
+    (DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn
+      I qOf hdistinct)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.

@@ -320,6 +373,24 @@ theorem petalNoLiftPrimeChannel_padicValNat_GN_eq_one
     exact h.2 ((padicValNat_dvd_iff_le hGN0).mpr htwo)
   omega

+/--
+A no-lift Petal channel family has exact one-slot valuation at every selected
+label.
+
+This theorem does not assert distinctness of the labels.  If two indices choose
+the same prime label, they read the same one-slot valuation.
+-/
+theorem petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    ∀ i, i ∈ I → padicValNat (qOf i) (GN d x u) = 1 := by
+  intro i hi
+  exact petalNoLiftPrimeChannel_padicValNat_GN_eq_one (hcarrier i hi)
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
````
`````
