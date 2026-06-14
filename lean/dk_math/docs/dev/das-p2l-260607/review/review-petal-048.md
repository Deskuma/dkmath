# Git diff / Report / Review

## Add: Petal.ErdosBridge

gch: 3a9587454fa8d83979acd716ab04ba9f69730818

## Report

`DkMath.Petal.ErdosBridge` を新設しました。

追加ファイル: [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:1)

今回固定したのは、Petal carrier を Erdos 側の prime-valued channel として読む最初の橋です。

```lean
def PetalPrimeChannel
def PetalNoLiftPrimeChannel

theorem petalPrimeChannel_prime
theorem petalNoLiftPrimeChannel_prime
theorem petalNoLiftPrimeChannel_channel
theorem petalNoLiftPrimeChannel_noLift
theorem petalPrimeChannel_log_nonneg
theorem petalPrimeChannel_natPrimeValuedOn
theorem petalPrimeChannel_realLogNonnegOn
theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
```

主定理の意味はこれです。

```text
Petal carrier family
  + multiplicity budget against n
  -> Erdos log-ratio provider is SubProbability
```

つまり、Petal は「素性 carrier」を供給し、Erdos 側の `NatBaseMultiplicityBudgetOn` があれば、全体の log cost は `1` 以下に抑えられる、という形です。まだ Petal geometry だけで multiplicity budget を出すとは主張していません。

検証済みです。

```text
lake build DkMath.Petal.ErdosBridge
git diff --check -- lean/dk_math/DkMath/Petal/ErdosBridge.lean
```

`DkMath.Petal` への公開 import はまだ入れていません。実験 API として単体で安定させる判断です。

## Review

うむ。これは **実験第一橋として approve** じゃ。
実装内容が、計画書の「薄く始める」「multiplicity budget は仮定として受け取る」「新しい無条件定理は主張しない」という方針にきれいに一致しておる。計画書でも、最初の実験は Petal/Zsigmondy/GN の局所 witness location と Erdős #1196 側の global log-capacity control を接続する段階で、まだ新しい無条件 Zsigmondy / FLT 定理を主張する段階ではないと明記されている。

## 1. レビュー結論

**Blocking issue なし。merge 可。**

今回の主定理

```lean
petalCarrierFamily_logSubProbability_of_multiplicityBudget
```

は、ちょうど欲しかった形じゃ。

```text
Petal carrier family
  + multiplicity budget against n
  -> Erdos log-ratio provider is SubProbability
```

これは過大主張していない。
Petal は

```text
q は prime carrier である
```

を供給し、Erdős 側の `NatBaseMultiplicityBudgetOn` が与えられたときだけ log-cost が `SubProbability` になる、という分業になっておる。計画書でも Step 5 は multiplicity budget を Petal 幾何から証明せず仮定として置き、Petal は prime-valued carrier を供給し、Erdős が予算を供給する形にする、とされている。

## 2. 良い点

`PetalPrimeChannel` を

```lean
def PetalPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q
```

としたのは正しい。これは「carrier 自身が anchor prime である」という最小読みで、prime-power channel へ拡張する前の薄い入口として適切じゃ。計画書でも、この定義は full Erdos transition kernel に踏み込まず実験前の薄い predicate として推奨されている。

`PetalNoLiftPrimeChannel` もよい。
ただし、現段階では主定理で使っていないのが正しい。これは将来の multiplicity / local-load 制御用の予備 API であり、今は「置いてあるだけ」で十分じゃ。

## 3. 主定理の意味

今回の theorem は、DkMath 的にはこういう意味になる。

$$
\text{Petal carrier}
\Rightarrow
\text{prime-valued channel}
$$

かつ、別途

$$
\text{multiplicity budget against } n
$$

があれば、

$$
\sum_i \frac{\log(q_i)}{\log n}\le 1
$$

を Erdos 側の既存 machinery で得る。

これはまさに、計画書の Claim C「有限 Petal carrier family は multiplicity budget があれば sub-probability budget を持つ」の実装版じゃ。

## 4. 注意点

このファイルは、まだ次を主張していない。

```text
Petal address antichain -> multiplicity budget
Zsigmondy -> NoLift
GN carrier -> squarefree
Zsigmondy -> padicValNat <= 1
```

ここを守れておるのが偉い。計画書でも、これらは未証明の研究方向であり、現在の theorem ではないと明記されている。さらに (5^3-3^3=98=2\cdot 7^2) の例が、primitive carrier でも local height が (2) になり得る guardrail として置かれている。

## 5. 小さな改善候補

今すぐ必須ではないが、次の alias があると読みやすいかもしれぬ。

```lean
theorem petalPrimeChannel_subProbabilityProvider_of_multiplicityBudget
```

または、現在の主定理名が少し長いので、将来公開 API にするなら短い別名を足すとよい。

```lean
theorem PetalPrimeChannel.logSubProbability
```

ただし、今は実験ファイルなので現名のままでよい。説明的で安全じゃ。

## 6. 次の一手

次は二択じゃ。

まず堅い道は、`Zsigmondy` からこの橋へ入る薄い theorem を足すこと。

```lean
theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
```

意味は、

```text
Zsigmondy primitive q
  -> AnchoredGNCarrier q d (a - b) b q
  -> PetalPrimeChannel d (a - b) b q
```

じゃ。

もう一つは、まだ研究色が強い道。

```text
Petal address noncollision
  -> NatBaseMultiplicityBudgetOn
```

これは計画書でも Step 6 の本命研究課題として置かれている。親 (n) を body difference にするか、GN にするか、source state にするか、abstract capacity carrier にするかを決める必要があるため、まだ焦らぬ方がよい。

## 7. 判定

**Approve.**

これは小さいが、かなり重要な橋じゃ。

```text
Petal:
  GN 上の素性 carrier を供給する

Erdos:
  multiplicity budget があれば log-cost を 1 以下に抑える
```

この分業が theorem として固定された。
よしよし、わっちの鼻は正しかったの。ここは「通る匂い」どころか、きれいに通った実験第一歩じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
new file mode 100644
index 00000000..b6d4d958
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -0,0 +1,148 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.BezoutBridge
+import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
+
+#print "file: DkMath.Petal.ErdosBridge"
+
+/-!
+# Petal Erdos Bridge
+
+This file starts the experimental bridge from Petal/GN carriers to the finite
+Erdos #1196 log-capacity machinery.
+
+The first step is intentionally small:
+
+```text
+Petal carrier
+  -> prime-valued Erdos channel
+  -> multiplicity-budgeted log sub-probability
+```
+
+No multiplicity budget is proved here.  The caller still supplies the existing
+`PrimitiveSet.NatBaseMultiplicityBudgetOn` hypothesis.  This keeps the bridge
+honest: Petal supplies carrier location, while the Erdos side supplies the
+global capacity bound once a multiplicity budget is available.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+
+/--
+A Petal GN carrier read as a prime Erdos channel.
+
+This is the prime-channel specialization of `AnchoredGNCarrier`: the carrier is
+the anchor prime itself.
+-/
+def PetalPrimeChannel (d x u q : ℕ) : Prop :=
+  AnchoredGNCarrier q d x u q
+
+/--
+A Petal prime channel with local no-lift on the observed GN surface.
+
+This records the local multiplicity condition for the selected channel only.
+It is deliberately weaker than asking the whole `GN` value to be squarefree.
+-/
+def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
+  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
+
+/-- A Petal prime channel carries a prime label. -/
+theorem petalPrimeChannel_prime
+    {d x u q : ℕ}
+    (h : PetalPrimeChannel d x u q) :
+    Nat.Prime q :=
+  anchoredGNCarrier_anchor_prime h
+
+/-- A Petal no-lift prime channel carries a prime label. -/
+theorem petalNoLiftPrimeChannel_prime
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    Nat.Prime q :=
+  petalPrimeChannel_prime h.1
+
+/-- Extract the underlying Petal prime channel from a no-lift channel. -/
+theorem petalNoLiftPrimeChannel_channel
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    PetalPrimeChannel d x u q :=
+  h.1
+
+/-- Extract the local no-lift condition from a Petal no-lift prime channel. -/
+theorem petalNoLiftPrimeChannel_noLift
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    ¬ q ^ 2 ∣ GN d x u :=
+  h.2
+
+/--
+The logarithmic cost of a Petal prime channel is nonnegative.
+-/
+theorem petalPrimeChannel_log_nonneg
+    {d x u q : ℕ}
+    (h : PetalPrimeChannel d x u q) :
+    0 ≤ Real.log (q : ℝ) :=
+  DkMath.NumberTheory.PrimitiveSet.real_log_nat_nonneg_of_one_le
+    (le_of_lt (petalPrimeChannel_prime h).one_lt)
+
+/--
+A finite family of Petal prime channels is prime-valued in the Erdos
+`PrimitiveSet` sense.
+-/
+theorem petalPrimeChannel_natPrimeValuedOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u qOf : ι → ℕ)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I qOf := by
+  intro i hi
+  exact petalPrimeChannel_prime (hcarrier i hi)
+
+/--
+A finite family of Petal prime channels supplies the real/log nonnegativity
+input for the Erdos log-capacity route.
+-/
+theorem petalPrimeChannel_realLogNonnegOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u qOf : ι → ℕ)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.RealLogNonnegOn I qOf :=
+  DkMath.NumberTheory.PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I qOf
+    (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
+
+/--
+First Petal-to-Erdos capacity bridge.
+
+If a finite Petal carrier family has a base-prime multiplicity budget against
+`n`, then the corresponding log-ratio provider is sub-probability.
+
+The multiplicity budget is an explicit hypothesis.  This theorem does not claim
+that Petal geometry or Zsigmondy alone supplies it.
+-/
+theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u qOf : ι → ℕ)
+    (n : ℕ)
+    (hn : 1 < n)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i))
+    (hbudget : DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I qOf n) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf n
+      (petalPrimeChannel_realLogNonnegOn I d x u qOf hcarrier)
+      hn).SubProbability :=
+  DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
+    I qOf n hn
+    (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
+    hbudget
+
+end Petal
+end DkMath
````
`````
