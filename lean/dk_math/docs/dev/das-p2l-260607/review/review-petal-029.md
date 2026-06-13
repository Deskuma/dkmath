# Git diff / Report / Review

## Upd: docs: Petal Zsigmondy Preflight

gch: 04a5d960930a3cbd767a8f434db366088bc08742

## Report

実態調査を行い、Zsigmondy に進む前の整理文書を追加しました。

追加:

- [Petal-Zsigmondy-Preflight.md](/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md)

確認した結論は明確です。

```text
Zsigmondy:
  primitive q の存在を出す

Petal / GN / BoundaryD3 / Anchor:
  q が boundary ではなく S0/GN3 側にいることを示す

Squarefree / NoLift / ValuationFlow:
  q の重複度、つまり padicValNat <= 1 を担当する
```

つまり、次に作るべき橋は `DkMath.Petal.ZsigmondyD3Bridge` 相当で、まずは三次 reduced Petal witness を

```lean
DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

へ翻訳する薄い層です。

一方で、`squarefree_implies_padic_val_le_one_research` は Zsigmondy 交渉で埋まる穴ではありません。反例 `5^3 - 3^3 = 98 = 2 * 7^2` があり、primitive 側でも valuation が 2 になり得ます。`padicValNat <= 1` は既存の honest theorem:

```lean
padicValNat_primitive_prime_factor_le_one_of_squarefree_G
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

または NoLift 系の担当です。

更新:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md)

検証:

```sh
git diff --check
```

成功です。docs-only なので Lean build は走らせていません。

## Review

うむ、これは **採用でよい preflight** じゃ。
交渉前に必要な切り分けが、かなり正確に書けている。

特に、この三分割が決定的じゃな。

```text id="goymzf"
Zsigmondy:
  primitive q の存在

Petal / GN / BoundaryD3 / Anchor:
  q が boundary ではなく S0/GN3 側にいること

Squarefree / NoLift / ValuationFlow:
  q の重複度、すなわち padicValNat <= 1
```

これで次の実装がかなり安全になる。
`ZsigmondyD3Bridge` に valuation bound を背負わせない、と明文化したのが一番大きい。

## レビュー結論

```text id="pk0xtc"
04a5d960...
  -> 採用可

docs-only preflight
  -> 妥当

次の Lean 実装
  -> DkMath.Petal.ZsigmondyD3Bridge

やってはいけないこと
  -> padicValNat <= 1 を Zsigmondy だけで出す
```

## 良い点

`Existing Zsigmondy Contract` で、既存 API をちゃんと列挙しているのが良い。

```lean id="fe2h5k"
DkMath.Zsigmondy.PrimitivePrimeDivisor.prime
DkMath.Zsigmondy.PrimitivePrimeDivisor.dvd
DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp
DkMath.Zsigmondy.primitivePrimeDivisor_body_three_imp_dvd_GN
```

これで、次の bridge が「新定理を発明する」のではなく、既存契約を Petal reduced cubic surface に合わせるだけだと分かる。

## 次の theorem 設計も妥当

まずはこれ。

```lean id="o8b07b"
theorem exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

これは Zsigmondy 側の existence layer を Petal branch name で呼ぶ wrapper。
十分に薄い。

次にこれ。

```lean id="0b2g4t"
theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
      AnchoredS0Carrier q c b q ∧
      ¬ q ∣ c - b
```

これが本命じゃな。
この theorem が通れば、

```text id="oht4pk"
Zsigmondy witness
  = Petal anchored S0 witness
```

が成立する。

## 実装時の注意

この combined witness は、Petal 側の `exists_anchoredS0Carrier_of_boundaryD3Reduced` から取るより、**Zsigmondy 側の q を Petal に持ち込む** 方が綺麗じゃ。

理由は、別々に存在を取ると witness が違う可能性があるから。

実装ルートはこう。

```text id="nwe85v"
1. exists_primitivePrimeDivisor_prime_exp から q を取る
2. hq.prime を得る
3. hq.dvd で q ∣ c^3 - b^3 を得る
4. hq.not_dvd_lower を m = 1 に使って ¬ q ∣ c - b を得る
5. primitivePrimeDivisor_body_three_imp_dvd_GN などで q ∣ GN 3 (c-b) b を得る
6. S0/GN bridge で q ∣ S0_nat c b
7. hasPositiveAnchorPrime_self_of_prime で AnchoredS0Carrier q c b q
```

もし `primitivePrimeDivisor_body_three_imp_dvd_GN` がそのまま `GN`  divisibility をくれるなら、S0 への移動は `anchoredS0Carrier_of_anchoredGNCarrier` または `S0_nat_eq_GN_three_sub` でよい。

## 気になる点

preflight の「Recommended first target」の説明で、

```text id="5il4p3"
三次 reduced Petal witness を PrimitivePrimeDivisor へ翻訳する
```

という表現は少しだけ逆向きに読める。
実装上は、たぶん **Zsigmondy から witness を取り、Petal witness に翻訳する** 方がよい。

なので docs の語感を厳密にするなら、

```text id="0zsj6f"
translate the reduced cubic Petal hypotheses into Zsigmondy's d = 3 existence theorem
```

あるいは、

```text id="a2i82a"
share the Zsigmondy d = 3 witness with the Petal anchored S0 carrier surface
```

くらいがより正確じゃ。

ただし実害はない。今のままでも意味は通る。

## valuation placeholder への判断も正しい

反例

```text id="e8vs0s"
5^3 - 3^3 = 98 = 2 * 7^2
S0_nat 5 3 = 49 = 7^2
```

を docs に残したのは非常に良い。
これがある限り、誰かがまた

```lean id="vqmdwb"
padicValNat q (...) <= 1
```

を Zsigmondy だけで出そうとしても止められる。

## 判定

```text id="m5uj48"
Petal-Zsigmondy-Preflight.md
  -> 良い

Roadmap 反映
  -> 良い

次の一手
  -> Add DkMath.Petal.ZsigmondyD3Bridge

注意
  -> valuation bound は入れない
```

うむ。交渉前の実態調査としてかなり良い。
これで Zsigmondy に無茶な要求をせず、正しい範囲で橋を掛けられる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 32978520..c37a2ba9 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1270,6 +1270,35 @@ lake build DkMath.Petal
 git diff --check
 ```
 
+### Step 5.9: Zsigmondy preflight investigation
+
+Status:
+
+```text
+investigated
+```
+
+Record:
+
+```text
+DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+```
+
+Conclusion:
+
+```text
+Zsigmondy gives existence.
+Petal gives location.
+Squarefree/NoLift gives multiplicity.
+```
+
+The next Lean-facing bridge should therefore be `DkMath.Petal.ZsigmondyD3Bridge`
+or an equivalent `PrimitiveD3` layer.  It should translate the reduced cubic
+Petal witness into `DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q`.
+
+It should not try to prove `padicValNat q (c^3 - b^3) <= 1` without an explicit
+squarefree or no-lift hypothesis.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index 0901a240..299550ff 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -536,6 +536,31 @@ DkMath.Lib.* promotion of neutral S0 / Eisenstein facts
 BoundaryD3Anchor split and final import-direction cleanup
 ```
 
+Zsigmondy へ進む前の実態調査:
+
+```text
+lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+```
+
+調査結果の要点:
+
+```text
+Zsigmondy:
+  primitive q の存在
+
+Petal / GN / BoundaryD3 / Anchor:
+  q が boundary ではなく S0/GN3 側にいること
+
+Squarefree / NoLift / ValuationFlow:
+  q の重複度、すなわち padicValNat <= 1
+```
+
+したがって次に作る橋は、まず三次 reduced Petal witness を
+`DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q` へ翻訳する薄い
+`ZsigmondyD3Bridge` でよい。
+`padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
+持つ別層の仕事として扱う。
+
 ### Phase 5: Zsigmondy への接続準備
 
 目標:
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 02a3dbe6..9cb68c2a 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -493,6 +493,16 @@ BoundaryD3Reduced
 This closes the current S0/GN3/BoundaryD3/Anchor/Eisenstein surface as a
 usable API for later FLT and Zsigmondy-facing work.
 
+The Zsigmondy-facing preflight investigation is recorded in:
+
+```text
+DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+```
+
+Its main conclusion is that the next bridge should translate the `d = 3`
+Petal witness into Zsigmondy's primitive-divisor language, while keeping
+valuation `<= 1` separate under squarefree/no-lift hypotheses.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
