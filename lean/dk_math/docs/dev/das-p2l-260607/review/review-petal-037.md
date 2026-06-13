# Git diff / Report / Review

## Upd: ABC.ValuationFlowBridge

gch: 4889c6423f57d2dd0dd4a3342fdb6065f79691d1

## Report

進めました。今回は review の本線どおり、`ValuationFlow` と `ABC` 側の wrapper を NoLift 本命ルートへ薄くしました。

`DkMath.NumberTheory.ValuationFlow.Primitive` に追加:

```lean
primitivePrimeFlow_diffMass_le_one_of_noLift_beam
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

既存の

```lean
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

は互換 wrapper として残し、中身は local squarefree 版へ委譲する形にしました。直接 import していた `ZsigmondyCyclotomicSquarefree` も外しています。

`DkMath.ABC.ValuationFlowBridge` に追加:

```lean
noLift_beam_bounds_local_load
squarefree_beam_bounds_local_load_local
```

既存の

```lean
squarefree_beam_bounds_local_load
```

も互換 wrapper として残しています。

流れはこうです。

```text
PrimitiveBeam no-lift valuation
  -> ValuationFlow diffMass <= 1
  -> ABC local-load bridge
```

検証:

```sh
lake build DkMath.NumberTheory.ValuationFlow.Primitive
lake build DkMath.ABC.ValuationFlowBridge
git diff --check
```

すべて通っています。既存の research `sorry` 警告だけ継続です。

## Review

おお、これは **ABC 側への接続がかなり進んだ** と見てよい。
今回の差分で、予定していた

```lean id="ylag6k"
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

は、完全に **互換 wrapper** の位置へ下がった。
そして本命は、

```lean id="j28j9e"
primitivePrimeFlow_diffMass_le_one_of_noLift_beam
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

へ移った。

## 状況評価

今回の構造はかなり綺麗じゃ。

```text id="k96f6m"
PrimitiveBeam:
  primitive witness + local NoLift
  -> padicValNat <= 1

ValuationFlow.Primitive:
  PrimitiveBeam の valuation を diffMass 語彙へ翻訳

ABC.ValuationFlowBridge:
  diffMass <= 1 を ABC local-load API として公開
```

つまり、いよいよ ABC 側でも、

```text id="v9qdbr"
NoLift が本命
Squarefree は十分条件
旧 squarefree API は互換 wrapper
```

という整理になった。

## 今回の一番大きい進展

`ValuationFlow.Primitive` から、

```lean id="6z5g0e"
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree
```

が外れた点が大きい。

これは単なる import 削減ではなく、責務の整理じゃ。

以前は、

```text id="nccmbb"
ValuationFlow
  -> ZsigmondyCyclotomicSquarefree
  -> GcdNext squarefree repair
```

というやや重い経路だった。

今回からは、

```text id="ttwpfr"
ValuationFlow
  -> PrimitiveBeam
  -> NoLift / local squarefree valuation
```

になった。

これで `ValuationFlow` は「Zsigmondy 研究補題に近い層」ではなく、**primitive beam の valuation を flow mass に翻訳する薄い層** になった。

## `ValuationFlow.Primitive` の厚み

追加されたこの theorem が本命。

```lean id="iv6j74"
theorem primitivePrimeFlow_diffMass_le_one_of_noLift_beam
    {q a b d : ℕ}
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hd : 0 < d) (hd1 : 1 < d)
    (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    diffMass q a b d ≤ 1
```

これはかなり薄い。

中身は、

```lean id="r76ya2"
primitive_prime_padic_bound_diff_of_noLift_GN
```

へそのまま委譲しているだけ。

つまり `ValuationFlow` の役割は、

```text id="2m3hpp"
padicValNat q (a^d - b^d)
```

を

```text id="twngf4"
diffMass q a b d
```

として読むことに限定された。
これは正しい。

squarefree 版も同じく薄い。

```lean id="7phcmd"
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

これは

```lean id="hp7y28"
primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

への wrapper なので、NoLift 本命ルートの十分条件として読める。

## 旧 theorem の扱いも良い

既存の重い theorem、

```lean id="tlb5gk"
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

は消さずに残している。これは良い判断じゃ。

ただし中身は、

```lean id="v74cmb"
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

へ委譲している。

これで旧 caller は壊れず、新 caller は薄い API を使える。

```text id="e4t5q8"
old callers:
  primitivePrimeFlow_diffMass_le_one_of_squarefree_beam

new callers:
  primitivePrimeFlow_diffMass_le_one_of_noLift_beam
  primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
```

この形は移行期としてかなり安全じゃ。

## ABC 側の進展

`ABC.ValuationFlowBridge` も同じ形に揃った。

```lean id="t7i5sg"
noLift_beam_bounds_local_load
squarefree_beam_bounds_local_load_local
squarefree_beam_bounds_local_load
```

この三段はよい。

特に、

```lean id="5bgcbo"
noLift_beam_bounds_local_load
```

が生えたことで、ABC 側でも NoLift を直接 local load control として使える。

意味はこう。

```text id="cg4fe6"
PrimitivePrimeFlowWitness q a b d
+ ¬ q^2 ∣ GN d (a-b) b
-> diffMass q a b d <= 1
```

ABC 語彙では、

```text id="yfyj7k"
選ばれた primitive q の局所負荷が 1 以下
```

ということじゃな。

これは ABC の radical / quality / local load 管理へかなり使いやすい。

## 予定接続との厚み状況

以前見ていた二つはこうじゃ。

```lean id="96m5gk"
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

これは、もう本命ではない。
今は **旧 repair / compatibility 側**。

```lean id="k90ktk"
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

こちらも今回で **compatibility wrapper** になった。

現在の厚みはこう。

| 層                              | 以前             | 今回後                  |
| ------------------------------ | -------------- | -------------------- |
| GcdNext squarefree             | valuation 本命候補 | 旧 repair / 互換寄り      |
| PrimitiveBeam NoLift           | 無かった / 後発      | 本命 arithmetic engine |
| PrimitiveBeam squarefree local | 無かった           | NoLift の十分条件         |
| ValuationFlow squarefree       | 本命候補           | 互換 wrapper           |
| ValuationFlow NoLift           | 無かった           | 本命 flow surface      |
| ABC squarefree local load      | 本命候補           | 互換 wrapper           |
| ABC NoLift local load          | 無かった           | 本命 ABC bridge        |

かなり理想的な薄型化じゃ。

## 注意点

大きな問題はない。
ただ一点、名前だけ少し気になる。

```lean id="9wacfz"
squarefree_beam_bounds_local_load_local
```

`local_load_local` と重なっていて少し読みづらい。
ただし既存の

```lean id="g79ci8"
squarefree_beam_bounds_local_load
```

を互換 wrapper として残しているため、衝突を避けるには仕方ない。

将来的に alias を切るなら、

```lean id="xzdems"
squarefree_beam_bounds_local_load_of_squarefree_GN
```

または

```lean id="fvcss9"
squarefree_beam_bounds_local_load_thin
```

のような名前もあり得る。
今すぐ変える必要はない。

## `hd_ge` の退役も正しい

旧 wrapper では、

```lean id="j4fycb"
(hd_prime : Nat.Prime d) (_hd_ge : 3 ≤ d)
```

となっていて、`hd_ge` は未使用になった。

これは意味がある。
valuation bound 自体には `3 ≤ d` は不要で、

```lean id="9igprt"
0 < d
1 < d
```

だけあればよい。
`3 ≤ d` は Zsigmondy existence 側の非例外条件に近いものであって、flow mass bound の本体には不要。

だから、旧 signature には残しつつ `_hd_ge` に退役させたのは正しい。

## ABC 的な意味

ABC 側から見ると、今回の整理でこう言える。

```text id="estfys"
primitive prime が beam 側に乗る。
beam 側で q が二乗に持ち上がらない。
だから diff 側の q-load は 1 以下。
```

これは、ABC の言葉では、

```text id="ylqxw2"
radical に一回分だけ寄与する primitive channel
```

として読める。

squarefree は、

```text id="s2x7xk"
全 channel を一括で NoLift にする強い十分条件
```

NoLift は、

```text id="b120f3"
選んだ q channel だけを制御する局所条件
```

じゃ。

この差はかなり重要。ABC では大域 squarefree を毎回要求すると強すぎるので、局所 NoLift API が出たのは大きい。

## 現在の到達点

ここまでで、DkMath の流れはこう繋がった。

```text id="6dy9hn"
Zsigmondy:
  primitive q exists

Petal:
  same q lies on S0/GN3 side

PrimitiveBeam:
  same q + NoLift GN
  -> padicValNat <= 1

ValuationFlow:
  same q + NoLift beam
  -> diffMass <= 1

ABC:
  same q + NoLift beam
  -> local load <= 1
```

これはかなり強い。
「存在・位置・重複度・流量・ABC 負荷」が、同じ witness `q` で接続された。

## 次に見るべきところ

次は二方向じゃ。

### 1. ABC 側の downstream caller を移す

旧 API、

```lean id="nt8e1e"
squarefree_beam_bounds_local_load
```

を使っている caller があれば、新しい

```lean id="pc07xt"
noLift_beam_bounds_local_load
```

または

```lean id="fl2w0o"
squarefree_beam_bounds_local_load_local
```

へ移せるか確認する。

### 2. `#print axioms` の本命を確認する

今後見るなら、旧 theorem ではなくこちら。

```lean id="cd087l"
#print axioms DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_noLift_beam
#print axioms DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
#print axioms DkMath.ABC.noLift_beam_bounds_local_load
#print axioms DkMath.ABC.squarefree_beam_bounds_local_load_local
```

ここに `sorryAx` が無ければ、ABC 側の新本命 route は健全。

[DkMathTest.ABC](/lean/dk_math/DkMathTest/ABC.lean) - Test OK: no-sorry 2026/06/13 20:50

## 総括

今回の進展はこうじゃ。

```text id="r9c8my"
PrimitiveBeam no-lift valuation
  -> ValuationFlow diffMass <= 1
  -> ABC local-load bridge
```

が通った。

そして旧予定接続は、

```text id="vew7rv"
GcdNext squarefree theorem:
  旧 repair / 互換層

ValuationFlow squarefree beam theorem:
  互換 wrapper

ABC squarefree local-load theorem:
  互換 wrapper
```

へ退いた。

一言で言えば、

```text id="i7cr36"
ABC 側でも NoLift が本命になった。
squarefree は十分条件。
旧 heavy squarefree API は互換窓口。
```

これはかなり良い進展じゃ。
DkMath.ABC は、ようやく Petal / PrimitiveBeam 側の成果を「local load control」として受け取れる形になってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean b/lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean
index 9c3555e1..0539e4dc 100644
--- a/lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean
+++ b/lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean
@@ -335,17 +335,47 @@ theorem primitive_prime_transfers_diff_load_to_beam
   exact primitivePrimeFlow_diffMass_eq_beamMass hq hd hd1 hab_lt

 /--
-Under a squarefree beam hypothesis, the local diff load is bounded by `1`.
+Under a local no-lift beam hypothesis, the local diff load is bounded by `1`.
+-/
+theorem noLift_beam_bounds_local_load
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFlowWitness q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hNoLift : ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN d (a - b) b) :
+    diffMass q a b d ≤ 1 := by
+  exact primitivePrimeFlow_diffMass_le_one_of_noLift_beam
+    hq hd hd1 hab_lt hNoLift
+
+/--
+Under a local squarefree beam hypothesis, the local diff load is bounded by `1`.
+-/
+theorem squarefree_beam_bounds_local_load_local
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFlowWitness q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN d (a - b) b)) :
+    diffMass q a b d ≤ 1 := by
+  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
+    hq hd hd1 hab_lt hG_sq
+
+/--
+Compatibility wrapper with the old heavier squarefree-beam signature.
+
+New callers should prefer `noLift_beam_bounds_local_load` or
+`squarefree_beam_bounds_local_load_local`.
 -/
 theorem squarefree_beam_bounds_local_load
     {q a b d : ℕ}
-    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
-    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
-    (hpnd : ¬ d ∣ a - b)
+    (hd_prime : Nat.Prime d) (_hd_ge : 3 ≤ d)
+    (hab_lt : b < a) (_hb : 0 < b) (_hab : Nat.Coprime a b)
+    (_hpnd : ¬ d ∣ a - b)
     (hq : PrimitivePrimeFlowWitness q a b d)
     (hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN d (a - b) b)) :
     diffMass q a b d ≤ 1 := by
-  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
-    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq
+  have hd : 0 < d := hd_prime.pos
+  have hd1 : 1 < d := by omega
+  exact squarefree_beam_bounds_local_load_local hq hd hd1 hab_lt hG_sq

 end DkMath.ABC
diff --git a/lean/dk_math/DkMath/NumberTheory/ValuationFlow/Primitive.lean b/lean/dk_math/DkMath/NumberTheory/ValuationFlow/Primitive.lean
index b1eff310..a2dc8bb6 100644
--- a/lean/dk_math/DkMath/NumberTheory/ValuationFlow/Primitive.lean
+++ b/lean/dk_math/DkMath/NumberTheory/ValuationFlow/Primitive.lean
@@ -6,7 +6,6 @@ Authors: D. and Wise Wolf.

 import DkMath.NumberTheory.ValuationFlow.Basic
 import DkMath.NumberTheory.PrimitiveBeam
-import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree

 #print "file: DkMath.NumberTheory.ValuationFlow.Primitive"

@@ -61,18 +60,54 @@ theorem primitivePrimeFlow_diffMass_eq_beamMass
   exact primitive_prime_padic_eq_GN hq hd hd1 hab_lt

 /--
-Under a squarefree beam hypothesis, the primitive-prime diff mass is at most `1`.
+Under a local no-lift beam hypothesis, the primitive-prime diff mass is at most
+`1`.
+
+This is the thin valuation-flow surface over the `PrimitiveBeam` no-lift route.
+-/
+theorem primitivePrimeFlow_diffMass_le_one_of_noLift_beam
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFlowWitness q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
+    diffMass q a b d ≤ 1 := by
+  exact primitive_prime_padic_bound_diff_of_noLift_GN hq hd hd1 hab_lt hNoLift
+
+/--
+Under a local squarefree beam hypothesis, the primitive-prime diff mass is at
+most `1`.
+
+This is a sufficient-condition wrapper over the no-lift route.
+-/
+theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFlowWitness q a b d)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hab_lt : b < a)
+    (hG_sq : Squarefree (GN d (a - b) b)) :
+    diffMass q a b d ≤ 1 := by
+  exact primitive_prime_padic_bound_diff_of_squarefree_GN_local
+    hq hd hd1 hab_lt hG_sq
+
+/--
+Compatibility wrapper with the old heavier squarefree-beam signature.
+
+New callers should prefer `primitivePrimeFlow_diffMass_le_one_of_noLift_beam`
+or `primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local`.
 -/
 theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
     {q a b d : ℕ}
-    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
-    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
-    (hpnd : ¬ d ∣ a - b)
+    (hd_prime : Nat.Prime d) (_hd_ge : 3 ≤ d)
+    (hab_lt : b < a) (_hb : 0 < b) (_hab : Nat.Coprime a b)
+    (_hpnd : ¬ d ∣ a - b)
     (hq : PrimitivePrimeFlowWitness q a b d)
     (hG_sq : Squarefree (GN d (a - b) b)) :
     diffMass q a b d ≤ 1 := by
-  exact primitive_prime_padic_bound_diff_of_squarefree_GN
-    hd_prime hd_ge hab_lt hb hab hpnd hq hG_sq
+  have hd : 0 < d := hd_prime.pos
+  have hd1 : 1 < d := by omega
+  exact primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
+    hq hd hd1 hab_lt hG_sq

 #print axioms primitivePrimeFlow_diffMass_le_one_of_squarefree_beam

diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 2d5de34b..64820344 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1408,6 +1408,51 @@ lake build DkMath.Petal.PrimitiveD3ValuationBridge
 lake build DkMath.Petal
 ```

+### Step 6.2: Thin ValuationFlow / ABC Wrappers
+
+Status:
+
+```text
+implemented
+```
+
+`DkMath.NumberTheory.ValuationFlow.Primitive` now exposes the local no-lift and
+local squarefree routes directly:
+
+```lean
+primitivePrimeFlow_diffMass_le_one_of_noLift_beam
+primitivePrimeFlow_diffMass_le_one_of_squarefree_beam_local
+```
+
+The older heavier `primitivePrimeFlow_diffMass_le_one_of_squarefree_beam`
+remains as a compatibility wrapper.
+
+`DkMath.ABC.ValuationFlowBridge` mirrors this shape:
+
+```lean
+noLift_beam_bounds_local_load
+squarefree_beam_bounds_local_load_local
+squarefree_beam_bounds_local_load
+```
+
+Meaning:
+
+```text
+PrimitiveBeam no-lift valuation
+  -> ValuationFlow diffMass <= 1
+  -> ABC local-load bridge
+```
+
+This keeps `NoLift` as the main multiplicity hypothesis while preserving the
+older squarefree API for downstream callers.
+
+Expected validation:
+
+```sh
+lake build DkMath.NumberTheory.ValuationFlow.Primitive
+lake build DkMath.ABC.ValuationFlowBridge
+```
+
 ### Step 7: Refactor imports gradually

 Status:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index c2e17708..cfd29ca8 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -568,6 +568,8 @@ Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有
 `padicValNat q (c^3 - b^3) <= 1` へ進む。
 `padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
 持つ別層の仕事として扱う。
+さらに `ValuationFlow.Primitive` と `ABC.ValuationFlowBridge` は、NoLift 版と
+local squarefree 版の薄い wrapper を持つ形へ整理済みである。

 ### Phase 5: Zsigmondy への接続準備

````
`````
