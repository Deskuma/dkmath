# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 249ba3dbfb00cb06d4125e0818f485f9649ab896

## Report

実装しました。対象は [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) です。

追加した主な補題:

- `primitivePrimeFactor_log_nonneg`
- `zsigmondyPrimitivePrimeDivisor_log_nonneg`
- `zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn`
- `zsigmondyFamily_logSubProbability_of_multiplicityBudget`
- `petalNoLiftPrimeChannel_GN_ne_zero`
- `petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN`
- `petalNoLiftPrimeChannel_singleton_logSubProbability_GN`

特に今回は、レビュー049の C 案まで通りました。`PetalNoLiftPrimeChannel` から singleton の multiplicity budget を作り、`GN d x u` 自身を分母にした Erdos log sub-probability まで no-sorry で固定できています。これはかなり良い足場です。

検証:

- `lake build DkMath.Petal.ErdosBridge` 成功
- `git diff --check -- lean/dk_math/DkMath/Petal/ErdosBridge.lean` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は再表示されていますが、今回追加分には `sorry` はありません。

## Review

うむ。これは **かなり良い進展** じゃ。
そして、今回でひとつ重要なことが見えた。

**弱腰ではいかん。だが、無謀ではなく “実験補題を多く立てて、Lean に裁かせる” のが正しい。**

今回通った補題群は、単なる alias 増加ではない。
特にこの 2 本が大きい。

```lean
petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
petalNoLiftPrimeChannel_singleton_logSubProbability_GN
```

これにより、

```text
PetalNoLiftPrimeChannel
  -> singleton multiplicity budget on GN
  -> Erdos log SubProbability on GN
```

が no-sorry で通った。これは **Petal 局所 carrier が、Erdős 側の容量機械に直接入れる** ことを示した最初の実体じゃ。

## 1. レビュー判定

**Approve。これは実験橋としてかなり良い。**

今回の流れはこうじゃ。

```text
PrimitiveBeam / Zsigmondy witness
  -> PetalPrimeChannel
  -> log nonnegativity
  -> family NatPrimeValuedOn
  -> multiplicity budget があれば SubProbability

PetalNoLiftPrimeChannel
  -> GN ≠ 0
  -> singleton multiplicity budget on GN
  -> singleton log SubProbability on GN
```

ここまで来ると、`Petal.ErdosBridge` は単なる翻訳ファイルではなく、 **局所 Petal carrier を有限 Erdos capacity channel に変換する実験場** になった。

## 2. 重要な発見: NoLift は singleton budget には強すぎるかもしれぬ

今回の proof を見ると、`petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN` で NoLift が本当に使われている場所は、主に

```lean
GN d x u ≠ 0
```

を出すところじゃ。

singleton multiplicity budget 自体は、本質的には

$$
q\mid GN_d(x,u),\qquad GN_d(x,u)\neq0
$$

から

$$
1\le v_q(GN_d(x,u))
$$

を得ているだけ。

つまり、より一般に次が通る可能性が高い。

```lean
theorem petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q)
    (hGN0 : GN d x u ≠ 0) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
```

そして `hGN0` を `PetalNoLiftPrimeChannel` から供給するのが、現在の補題の特殊形になる。

これは良い一般化じゃ。
NoLift は本来

$$
q^2\nmid GN
$$

という **上側の multiplicity 制御** であり、singleton budget のための **下側の 1 slot 存在** には強すぎる。ここを分離できる。

## 3. さらに攻められる補題

次に狙うなら、わっちはこの順を推す。

### 3.1. `PetalPrimeChannel` + `GN ≠ 0` から `1 < GN`

```lean
theorem petalPrimeChannel_GN_one_lt_of_ne_zero
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q)
    (hGN0 : GN d x u ≠ 0) :
    1 < GN d x u
```

理由は、

$$
q\mid GN,\quad q\ \text{prime},\quad GN\neq0
$$

なら

$$
q\le GN
$$

かつ

$$
1<q
$$

なので

$$
1<GN
$$

じゃ。

これが通ると、現在 `petalNoLiftPrimeChannel_singleton_logSubProbability_GN` が要求している

```lean
(hGN : 1 < GN d x u)
```

を NoLift から自動供給できる。

### 3.2. `PetalNoLiftPrimeChannel` から `1 < GN`

```lean
theorem petalNoLiftPrimeChannel_GN_one_lt
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    1 < GN d x u :=
  petalPrimeChannel_GN_one_lt_of_ne_zero h.1
    (petalNoLiftPrimeChannel_GN_ne_zero h)
```

これはほぼ通るはずじゃ。

### 3.3. `NoLift` 版 singleton log theorem から `hGN` を消す

現在は

```lean
(hGN : 1 < GN d x u)
```

が必要だが、NoLift から出せるなら、次を作れる。

```lean
theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
      ...
      (petalNoLiftPrimeChannel_GN_one_lt h)).SubProbability
```

これは美しい。
「NoLift Petal channel は、自分が載っている GN を親容量として、そのまま singleton Erdos channel になる」という定理になる。

## 4. もっと攻めるなら: NoLift で valuation = 1

NoLift は本当は

$$
q\mid GN,\qquad q^2\nmid GN
$$

だから、自然には

$$
v_q(GN)=1
$$

を言いたい。

候補はこれじゃ。

```lean
theorem petalNoLiftPrimeChannel_padicValNat_GN_eq_one
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    padicValNat q (GN d x u) = 1
```

これは既存の `padicValNat` 補題次第じゃが、試す価値が高い。
もし通れば、NoLift の意味がかなり明確になる。

```text
NoLiftPrimeChannel
  = selected q has exactly one local exponent slot on GN
```

これが得られると、FLT / ABC 側がかなり食べやすくなる。

## 5. Zsigmondy + NoLift も次に通せる

今は Zsigmondy family から budget 仮定つき SubProbability が通った。

次は局所版として、

```lean
theorem zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN
```

を狙える。

形はこう。

```lean
theorem zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    ...
```

内部では

```lean
zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
```

と `hNoLift` で `PetalNoLiftPrimeChannel` を作る。

これはかなり通る匂いがする。

## 6. 次の研究補題: distinct carriers から multiplicity budget

singleton の次は、多点 family じゃ。

一番安全なのは、

```text
qOf が I 上で injective
各 qOf i が n を割る
n ≠ 0
```

なら multiplicity budget という形。

Lean 候補:

```lean
theorem natBaseMultiplicityBudgetOn_of_injOn_of_prime_dvd
    {ι : Type _}
    (I : Finset ι)
    (qOf : ι → ℕ)
    (n : ℕ)
    (hn0 : n ≠ 0)
    (hprime : DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I qOf)
    (hinj : Set.InjOn qOf ↑I)
    (hdvd : ∀ i, i ∈ I → qOf i ∣ n) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I qOf n
```

これはかなり汎用価値が高い。

Petal 側では、

```text
distinct Petal carrier primes
  + all divide same GN/body
  -> multiplicity budget
```

へ接続できる。

これが通れば、次に

```text
Petal address noncollision
  -> prime injectivity
  -> multiplicity budget
```

の道が見える。

## 7. まだ無理筋なもの

ここは引き続き守るべきじゃ。

```text
Zsigmondy alone -> NoLift
```

これは反例あり。

```text
PetalPrimeChannel alone -> squarefree GN
```

これも無理。

```text
Petal address antichain -> multiplicity budget
```

これはまだ定義不足。ただし、今後の本命じゃ。

## 8. 今回で得た洞察

今回の成功から見える新しい地図はこれじゃ。

```text
PetalPrimeChannel
  -> q ∣ GN
  -> GN ≠ 0 があれば singleton budget
  -> log SubProbability

PetalNoLiftPrimeChannel
  -> GN ≠ 0
  -> singleton budget
  -> log SubProbability
  -> possibly padicValNat GN = 1

ZsigmondyPrimitivePrimeDivisor
  -> PetalPrimeChannel
  -> family NatPrimeValuedOn
  -> budget があれば log SubProbability
```

これはかなり進んだ。
Petal はもう「GN 上の位置情報」だけでなく、 **Erdős log-capacity に入る局所チャネル生成器** になり始めている。

## 9. 判定

**Approve。進展度は確かに一段上がった。**

次は攻めの候補をまとめると、

```text
A. NoLift を外した一般 singleton budget
B. PetalPrimeChannel + GN≠0 -> 1<GN
C. NoLift -> padicValNat GN = 1
D. Zsigmondy + NoLift -> singleton SubProbability
E. distinct Petal carrier family -> multiplicity budget
```

この 5 本じゃ。

お主の言う通り、ここからは「もしかしたら？」を Lean に投げてよい。
長い論理鎖は、賢狼の鼻でも先までは嗅ぎ切れぬ。だからこそ Lean の出番じゃ。
通った鎖は道。切れた鎖は境界線。どちらも宝じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 3922a1db..d34f70f5 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -110,6 +110,30 @@ theorem petalPrimeChannel_log_nonneg
   DkMath.NumberTheory.PrimitiveSet.real_log_nat_nonneg_of_one_le
     (le_of_lt (petalPrimeChannel_prime h).one_lt)
 
+/--
+PrimitiveBeam witnesses have nonnegative Erdos log cost after entering the
+Petal prime channel.
+-/
+theorem primitivePrimeFactor_log_nonneg
+    {q a b d : ℕ}
+    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    0 ≤ Real.log (q : ℝ) :=
+  petalPrimeChannel_log_nonneg
+    (primitivePrimeFactor_petalPrimeChannel hq hd hd1 hab_lt)
+
+/--
+Zsigmondy primitive divisors have nonnegative Erdos log cost after entering the
+Petal prime channel.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_log_nonneg
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    0 ≤ Real.log (q : ℝ) :=
+  petalPrimeChannel_log_nonneg
+    (zsigmondyPrimitivePrimeDivisor_petalPrimeChannel hprim hd hd1 hab_lt)
+
 /--
 A finite family of Petal prime channels is prime-valued in the Erdos
 `PrimitiveSet` sense.
@@ -124,6 +148,29 @@ theorem petalPrimeChannel_natPrimeValuedOn
   intro i hi
   exact petalPrimeChannel_prime (hcarrier i hi)
 
+/--
+A finite family of Zsigmondy primitive divisors is prime-valued in the Erdos
+`PrimitiveSet` sense.
+
+This is the family-level handoff from Zsigmondy witnesses to the Erdos channel
+language.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
+    {ι : Type _}
+    (I : Finset ι)
+    (q a b d : ι → ℕ)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
+    (hd : ∀ i, i ∈ I → 0 < d i)
+    (hd1 : ∀ i, i ∈ I → 1 < d i)
+    (hab_lt : ∀ i, i ∈ I → b i < a i) :
+    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I q := by
+  apply petalPrimeChannel_natPrimeValuedOn I d (fun i => a i - b i) b q
+  intro i hi
+  exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+    (hprim i hi) (hd i hi) (hd1 i hi) (hab_lt i hi)
+
 /--
 A finite family of Petal prime channels supplies the real/log nonnegativity
 input for the Erdos log-capacity route.
@@ -164,5 +211,105 @@ theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
     (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
     hbudget
 
+/--
+Local no-lift makes the observed GN surface nonzero.
+
+If `GN d x u` were zero, then every number, in particular `q ^ 2`, would divide
+it.  This contradicts the no-lift condition.
+-/
+theorem petalNoLiftPrimeChannel_GN_ne_zero
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    GN d x u ≠ 0 := by
+  intro hzero
+  exact h.2 (by rw [hzero]; exact dvd_zero _)
+
+/--
+A single no-lift Petal prime channel fits into the Erdos multiplicity budget of
+its own GN surface.
+
+This is the first local capacity witness: the singleton selected channel uses
+one exponent slot at `q`, and `q ∣ GN d x u` supplies that slot in the
+factorization of `GN d x u`.
+-/
+theorem petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u) := by
+  classical
+  intro p hp
+  unfold DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityOn
+  by_cases hpq : q = p
+  · subst hpq
+    simp only [Finset.filter_true, Finset.card_singleton]
+    have hGN0 : GN d x u ≠ 0 := petalNoLiftPrimeChannel_GN_ne_zero h
+    have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h.1
+    have hq_pow_dvd : q ^ 1 ∣ GN d x u := by simpa using hq_dvd
+    exact (hp.pow_dvd_iff_le_factorization hGN0).mp hq_pow_dvd
+  · simp [hpq]
+
+/--
+Singleton no-lift Petal channels give a direct Erdos log sub-probability
+against the observed GN surface.
+
+This is intentionally a one-channel theorem.  Multi-channel budgets still need
+separate collision/multiplicity control.
+-/
+theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN
+    {d x u q : ℕ}
+    (h : PetalNoLiftPrimeChannel d x u q)
+    (hGN : 1 < GN d x u) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
+      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
+        (fun _ : Unit => u) (fun _ : Unit => q)
+        (by
+          intro i _hi
+          cases i
+          exact h.1))
+      hGN).SubProbability :=
+  petalCarrierFamily_logSubProbability_of_multiplicityBudget
+    ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
+    (fun _ : Unit => u) (fun _ : Unit => q) (GN d x u) hGN
+    (by
+      intro i _hi
+      cases i
+      exact h.1)
+    (petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN h)
+
+/--
+Zsigmondy-family form of the first Petal-to-Erdos capacity bridge.
+
+Once a finite Zsigmondy witness family has a base-prime multiplicity budget
+against `n`, its log-ratio provider is sub-probability.  The theorem still
+keeps the multiplicity budget explicit; Zsigmondy supplies prime channels, not
+global capacity by itself.
+-/
+theorem zsigmondyFamily_logSubProbability_of_multiplicityBudget
+    {ι : Type _}
+    (I : Finset ι)
+    (q a b d : ι → ℕ)
+    (n : ℕ)
+    (hn : 1 < n)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
+    (hd : ∀ i, i ∈ I → 0 < d i)
+    (hd1 : ∀ i, i ∈ I → 1 < d i)
+    (hab_lt : ∀ i, i ∈ I → b i < a i)
+    (hbudget : DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I q n) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I q n
+      (DkMath.NumberTheory.PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I q
+        (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
+          I q a b d hprim hd hd1 hab_lt))
+      hn).SubProbability :=
+  DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
+    I q n hn
+    (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
+      I q a b d hprim hd hd1 hab_lt)
+    hbudget
+
 end Petal
 end DkMath
````
`````
