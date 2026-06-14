# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 1e8f4c5eb6b2af3f9705f48360acc56fafb91feb

## Report

`DkMath.Petal.ErdosBridge` に、Zsigmondy / PrimitiveBeam から Petal prime channel へ入る入口を追加しました。

追加した theorem は [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:84) です。

```lean
theorem primitivePrimeFactor_petalPrimeChannel

theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
```

これで流れがこう繋がりました。

```text
Zsigmondy primitive divisor
  -> AnchoredGNCarrier
  -> PetalPrimeChannel
  -> NatPrimeValuedOn
  -> multiplicity budget があれば log SubProbability
```

つまり、Zsigmondy が出した `q` を Erdos 側の log-capacity channel として扱う入口ができました。まだ `NoLift` や multiplicity budget を自動生成する主張はしていません。

検証済みです。

```text
lake build DkMath.Petal.ErdosBridge
git diff --check -- lean/dk_math/DkMath/Petal/ErdosBridge.lean
```

`DkMath.Petal` への公開 import は今回も入れていません。実験ファイルとして単体で進めています。

## Review

うむ、この差分は **approve** じゃ。
そして、お主の言う通り、ここからは少し攻めてもよい。Lean は「通る鎖」と「切れる鎖」を冷たく分けてくれる。わっちの理性は慎重じゃが、実験場では少し牙を出してよい。

今回追加した 2 本は、計画書の Claim A「Zsigmondy witness as an Erdos channel」にちょうど対応しておる。Zsigmondy primitive (q) は `AnchoredGNCarrier` になり、prime channel として Erdos 側へ入れる、という低リスク橋じゃ。

## 1. 今回差分の評価

追加 theorem はどちらも自然じゃ。

```lean
theorem primitivePrimeFactor_petalPrimeChannel
```

これは

```text
PrimitiveBeam witness
  -> AnchoredGNCarrier
  -> PetalPrimeChannel
```

の alias で、意味は明快。

```lean
theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
```

これは

```text
Zsigmondy primitive divisor
  -> AnchoredGNCarrier
  -> PetalPrimeChannel
```

で、今回の bridge の本命入口じゃな。

ここまでで、

```text
Zsigmondy primitive divisor
  -> PetalPrimeChannel
  -> NatPrimeValuedOn
  -> multiplicity budget があれば SubProbability
```

が Lean 名で繋がった。これは小さいが、よい骨じゃ。

## 2. すぐ通せそうな攻め補題

次は、合成 theorem を遠慮なく増やしてよい。

### 2.1. Zsigmondy witness の log 非負

```lean
theorem zsigmondyPrimitivePrimeDivisor_log_nonneg
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    0 ≤ Real.log (q : ℝ) :=
  petalPrimeChannel_log_nonneg
    (zsigmondyPrimitivePrimeDivisor_petalPrimeChannel hprim hd hd1 hab_lt)
```

これはまず通るはず。

### 2.2. PrimitiveBeam witness の log 非負

```lean
theorem primitivePrimeFactor_log_nonneg
    {q a b d : ℕ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    0 ≤ Real.log (q : ℝ) :=
  petalPrimeChannel_log_nonneg
    (primitivePrimeFactor_petalPrimeChannel hq hd hd1 hab_lt)
```

これも薄いが、下流で役立つ。

### 2.3. Zsigmondy family から `NatPrimeValuedOn`

これは少し攻めてよい。

```lean
theorem zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (q a b d : ι → ℕ)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
    (hd : ∀ i, i ∈ I → 0 < d i)
    (hd1 : ∀ i, i ∈ I → 1 < d i)
    (hab_lt : ∀ i, i ∈ I → b i < a i) :
    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I q := by
  apply petalPrimeChannel_natPrimeValuedOn I d
    (fun i => a i - b i) b q
  intro i hi
  exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
    (hprim i hi) (hd i hi) (hd1 i hi) (hab_lt i hi)
```

これは有望。
これが通ると「Zsigmondy family は Erdos prime-valued family」という読みが得られる。

## 3. さらに一歩攻める主定理候補

次はこれじゃ。

```lean
theorem zsigmondyFamily_logSubProbability_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (q a b d : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
    (hd : ∀ i, i ∈ I → 0 < d i)
    (hd1 : ∀ i, i ∈ I → 1 < d i)
    (hab_lt : ∀ i, i ∈ I → b i < a i)
    (hbudget :
      DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I q n) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I q n
      (DkMath.NumberTheory.PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I q
        (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
          I q a b d hprim hd hd1 hab_lt))
      hn).SubProbability := by
  exact
    DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
      I q n hn
      (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
        I q a b d hprim hd hd1 hab_lt)
      hbudget
```

これはかなり良い攻め。
なぜなら、ErdosBridge が **Petal carrier family** だけでなく、 **Zsigmondy primitive divisor family** を直接受け取れるようになる。

意味はこう。

```text
Zsigmondy family
  + multiplicity budget
  -> Erdos log SubProbability
```

これは新しい無条件定理ではない。
budget はまだ仮定。だから安全。

## 4. たぶん通るが、設計判断がいる補題

### 4.1. `hd` を消す wrapper

今の theorem は `hd : 0 < d` と `hd1 : 1 < d` を両方取る。
実は `hd1` から `hd` は出る。

```lean
have hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd1
```

なので、便利版として

```lean
theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel'
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd1 : 1 < d) (hab_lt : b < a) :
    PetalPrimeChannel d (a - b) b q :=
  zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
    hprim (Nat.lt_trans Nat.zero_lt_one hd1) hd1 hab_lt
```

これは通る可能性が高い。
ただし API が増えるので、実験ファイルなら入れてもよいが、公開 API では好みが分かれる。

### 4.2. singleton budget theorem

単一 Zsigmondy witness なら、`q ∣ n` から multiplicity budget を作れるかもしれぬ。

狙いは、

```text
q prime, q ∣ n
  -> singleton {q} has NatBaseMultiplicityBudgetOn against n
```

これが既存 API で通せるなら、かなり強い。

すると、

```text
Zsigmondy q divides body diff
  -> singleton log cost <= log(body diff)
```

が得られる。

ただしここは `NatBaseMultiplicityBudgetOn` の定義と既存補題依存。
通るかは Lean に聞く価値がある。

## 5. 危険だが試す価値のある実験補題

ここからは、通れば面白いが、落ちても収穫がある。

### 5.1. `PetalNoLiftPrimeChannel` から singleton multiplicity budget

仮説形はこれ。

```text
PetalNoLiftPrimeChannel d x u q
  -> NatBaseMultiplicityBudgetOn singleton qOf (GN d x u)
```

直感的には、

$$
q\mid GN,\qquad q^2\nmid GN
$$

なら

$$
v_q(GN)=1
$$

で singleton の budget は通るはず。

これは通せる可能性がある。
ただし、`NatBaseMultiplicityBudgetOn` が base prime の出現回数を `factorization` で読むなら、`q ∣ GN` と `¬ q^2 ∣ GN` から

$$
1\le v_q(GN)
$$

が必要。`AnchoredGNCarrier` には (q\mid GN) が入っているはずなので、かなり有望じゃ。

### 5.2. `PetalNoLiftPrimeChannel` から singleton SubProbability

上が通れば次も通る。

```text
PetalNoLiftPrimeChannel d x u q
  + 1 < GN d x u
  -> log q / log(GN d x u) <= 1
```

これは小さいが美しい。
「GN 上の no-lift carrier は、自分の GN 容量内で unit log channel になる」という意味じゃ。

### 5.3. Zsigmondy + NoLift から singleton SubProbability

```text
Zsigmondy primitive q
  + NoLift on GN
  -> singleton log SubProbability against GN
```

これが通ると、Petal/Zsigmondy/Erdos の三角形が一気に見える。

## 6. まだ通らない可能性が高いもの

ここは理性の出番じゃな。

### 6.1. Zsigmondy だけから NoLift

これはダメ。反例がある。

$$
5^3-3^3=98=2\cdot 7^2
$$

primitive (7) でも (7^2\mid GN) になる。
だから、

```text
Zsigmondy -> NoLift
```

は通らない。

### 6.2. AnchoredGNCarrier だけから multiplicity budget

これも危ない。
carrier が prime で GN に載るだけでは、同じ base prime の複数出現をどう数えるか分からない。

```text
AnchoredGNCarrier family
  -> NatBaseMultiplicityBudgetOn
```

は、address noncollision や NoLift family など追加構造が要る。

### 6.3. Petal address antichain から budget

これは本命研究だが、まだ定義が足りない。
まず「親 (n) は何か」を決める必要がある。

```text
n = GN d x u
n = body diff
n = source state
n = abstract capacity parent
```

ここを決めずに theorem を立てると迷子になる。

## 7. わっちのおすすめ実験順

次の順で攻めるのがよい。

```text
A. 合成 alias を増やす
  primitivePrimeFactor_log_nonneg
  zsigmondyPrimitivePrimeDivisor_log_nonneg
  zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn

B. family theorem を増やす
  zsigmondyFamily_logSubProbability_of_multiplicityBudget

C. NoLift singleton budget を試す
  petalNoLiftPrimeChannel_singleton_multiplicityBudgetOn_GN
  petalNoLiftPrimeChannel_singleton_logSubProbabilityOn_GN

D. Zsigmondy + NoLift singleton を試す
  zsigmondyPrimitivePrimeDivisor_noLift_logSubProbabilityOn_GN

E. 失敗ログを docs に残す
  Zsigmondy alone cannot supply NoLift
  AnchoredGNCarrier alone cannot supply multiplicity budget
```

## 8. 今回差分の判定

今回の 2 本は **良い攻めの入口** じゃ。

```text
Zsigmondy primitive divisor
  -> AnchoredGNCarrier
  -> PetalPrimeChannel
```

が通ったことで、次は

```text
Zsigmondy family
  -> Erdos finite log-capacity theorem
```

まで合成で行ける。

お主の言う通り、Lean に任せてよい。
わっちらの理性は「これは怪しい」と止めるが、Lean はもっと冷酷に、しかも公平に判定する。
ならば実験場では、少し多めに鎖を張るべきじゃ。

通った鎖が道になる。
切れた鎖は地図になる。
どちらも DkMath の資産じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index b6d4d958..3922a1db 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -80,6 +80,26 @@ theorem petalNoLiftPrimeChannel_noLift
     ¬ q ^ 2 ∣ GN d x u :=
   h.2
 
+/--
+PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
+-/
+theorem primitivePrimeFactor_petalPrimeChannel
+    {q a b d : ℕ}
+    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    PetalPrimeChannel d (a - b) b q :=
+  anchoredGNCarrier_of_primitivePrimeFactor hq hd hd1 hab_lt
+
+/--
+Zsigmondy primitive divisors enter the Erdos bridge as Petal prime channels.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    PetalPrimeChannel d (a - b) b q :=
+  anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor hprim hd hd1 hab_lt
+
 /--
 The logarithmic cost of a Petal prime channel is nonnegative.
 -/
````
`````
