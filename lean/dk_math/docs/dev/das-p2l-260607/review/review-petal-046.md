# Git diff / Report / Review

## Upd: docs: Zsigmondy Contract Conditions for FLT / ABC

gch: bd901b19a255e68bbd7de29e79f715543dad8b86

## Report

Zsigmondy 契約条件を docs に明文化しました。

更新したのは以下です。

- [Petal-Zsigmondy-Preflight.md](/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md:59)
- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:397)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1637)

入れた内容は次です。

```text
Zsigmondy:
  primitive q の存在

Petal / BezoutBridge:
  q は boundary を避ける
  q は GN に載る
  q は AnchoredGNCarrier になる
  body diff の padicValNat は GN 側で読める

Multiplicity:
  NoLift または squarefree GN が別途必要

ABC:
  ValuationFlow / local-load wrapper が multiplicity 条件を消費

FLT:
  PrimeProvider / no-Wieferich valuation surface が同じ q を消費
```

Mathlib については、ローカル依存を検索しました。現時点の `.lake/packages/mathlib` には `Zsigmondy` / `PrimitivePrimeDivisor` / Bang-Zsigmondy に対応する本社 API は見当たりません。`Birkhoff` は多数ありますが別分野でした。

そのため docs では、`DkMath.Zsigmondy` を「現時点の project-owned facade」と位置づけました。将来 Mathlib に本社定理が入った場合も、DkMath 側の公開 API は残し、内部証明だけ Mathlib へ差し替える方針にしています。

検証は docs-only として `git diff --check` を実行し、問題なしです。

## Review

うむ。これは **docs-only として approve** じゃ。
そして「どうしましょーね？」への答えは、はっきりしておる。

**次は “Zsigmondy が出した (q) を、FLT / ABC がそのまま消費できる contract object に梱包する” 段階** じゃ。

古典 Zsigmondy 定理は、互いに素な (a>b>0) について、ほとんどの (n) で (a^n-b^n) に primitive prime divisor が存在する定理で、例外として (n=1) 型、(n=2) 型、((a,b,n)=(2,1,6)) 型などが知られている。([ウィキペディア][1]) ただし Mathlib 側にこの本社 API が無いなら、DkMath 側で facade を持つ判断は正しい。DkMath の地図でも `DkMath.Zsigmondy` は既に Zsigmondy ブリッジとして入口に置かれており、ZsigmondyCyclotomic は冪差・gcd・原始素因子を扱う幹線として整理されている。

## 1. 今回 docs 差分の評価

今回の文書化は **非常に良い防波堤** じゃ。

特に良いのは、この一文脈を明確にした点。

```text
Zsigmondy gives existence.
Petal / BezoutBridge gives location and boundary separation.
PrimitiveBeam / ValuationFlow gives valuation transfer.
NoLift or squarefree GN gives multiplicity control.
```

これは過大主張を防ぐ。
つまり、

$$
q\mid GN
$$

までは言えるが、

$$
v_q(GN)\le 1
$$

は **別条件なしには言えない** 。ここを docs で切ったのは大きい。

以前の実装計画でも、primitive prime が boundary を割らず、`GN` を割り、valuation が `GN` 側へ移り、squarefree `GN` なら valuation 上界へ行く、という spine が Phase C の中核として整理されていた。 今回の docs は、その条件境界を FLT / ABC 用の契約書へ昇格したものじゃな。

## 2. 次にやるべきこと

わっちなら、次は theorem をバラで増やすより、 **契約パッケージ** を作る。

たとえば Petal 側か NumberTheory 側に、こういう structure / predicate を置く。

```lean
structure ZsigmondyGNContract (a b d q : ℕ) : Prop where
  primitive :
    DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q
  not_dvd_boundary :
    ¬ q ∣ a - b
  dvd_GN :
    q ∣ GN d (a - b) b
  valuation_transfer :
    padicValNat q (a ^ d - b ^ d) =
      padicValNat q (GN d (a - b) b)
  carrier :
    AnchoredGNCarrier q d (a - b) b q
```

ただし Lean 的には `Prop` structure にするか、単に theorem bundle として `def` せず theorem 群に留めるかは悩みどころじゃ。最初は軽く、次のような constructor theorem だけでもよい。

```lean
theorem zsigmondyPrimitivePrimeDivisor_to_GNContract
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    ZsigmondyGNContract a b d q := ...
```

これができると、FLT / ABC 側は theorem を 5 本 import して組み合わせる必要がなくなり、

```text
契約を受け取る
必要な multiplicity 条件だけ追加する
```

という形になる。

## 3. レイヤ分離はこのままでよい

docs の方針通り、

```text
DkMath.Zsigmondy
  existence facade

DkMath.Petal.BezoutBridge
  location / boundary separation / GN carrier

Multiplicity layer
  NoLift / squarefree

ABC
  ValuationFlow / local-load

FLT
  PrimeProvider / no-Wieferich surface
```

でよい。

DkMath の既存設計でも、宇宙式分解から Tail / GN、valuation、mass / flow、bridge へ進む層構造が基本方針として整理されている。 また、FLT 側には本体ではなく橋だけを置く、という分離方針も以前から出ておる。

つまり、今回の docs は既存設計と矛盾していない。むしろ、ようやく「Zsigmondy がどの層に何を渡すか」が見えるようになった。

## 4. 実装順のおすすめ

次の順が堅い。

### Step A. `NoLift` predicate を局所定義する

まずは抽象でよい。

```lean
def NoLiftOnGN (q d x u : ℕ) : Prop :=
  padicValNat q (GN d x u) = 1
```

または、より弱く使いやすくするなら、

```lean
def LocalLoadAtMostOneOnGN (q d x u : ℕ) : Prop :=
  padicValNat q (GN d x u) ≤ 1
```

`NoLift` は名前が強いので、Lean API では `LocalLoadAtMostOneOnGN` の方が安全かもしれぬ。

### Step B. contract + multiplicity から FLT/ABC 用 local theorem を作る

例えば、

```lean
theorem zsigmondy_contract_bodyDiff_padic_le_one
    (hC : ZsigmondyGNContract a b d q)
    (hload : padicValNat q (GN d (a - b) b) ≤ 1) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := ...
```

これは valuation transfer を使うだけ。
だが下流にとっては非常に便利じゃ。

### Step C. squarefree GN から `LocalLoadAtMostOne` を供給する

```lean
theorem localLoadAtMostOneOnGN_of_squarefree
    (hq : Nat.Prime q)
    (hsq : Squarefree (GN d x u)) :
    padicValNat q (GN d x u) ≤ 1 := ...
```

これで docs に書いた、

```text
NoLift または squarefree GN が別途必要
```

が theorem になる。

### Step D. FLT d=3 専用 surface に接続する

ここで初めて `PrimeProvider` や `no-Wieferich valuation surface` が同じ (q) を消費する。

流れはこう。

```text
Zsigmondy primitive q
  -> GN carrier
  -> valuation transfer
  -> local load <= 1
  -> d-th power 側の valuation >= d と矛盾
```

これは FLT d=3 では特に強い。
すでに DkMath の構成地図でも、Zsigmondy / p-adic route は FLT 幹線の一部として扱われている。

## 5. docs に追加してもよい注意書き

今回の文書はよいが、さらに一文足すならこれじゃ。

```text
Implementation policy:
  Downstream files should not destruct `DkMath.Zsigmondy.PrimitivePrimeDivisor`
  directly unless they are bridge files.  FLT / ABC callers should consume the
  routed Petal/GN contract or a specialized local-load contract.
```

これは重要。
下流が `PrimitivePrimeDivisor` を直接分解し始めると、また条件が散らばる。せっかく契約境界を作ったのだから、下流は契約を食べるべきじゃ。

## 6. 判断

今回の docs は **正しい** 。
次は「契約書を theorem bundle 化」するのがよい。

わっちのおすすめはこの順。

```text
1. docs merge
2. ZsigmondyGNContract または theorem bundle を追加
3. LocalLoadAtMostOneOnGN / NoLiftOnGN を定義
4. squarefree GN -> LocalLoadAtMostOne を接続
5. FLT / ABC bridge で contract + multiplicity を消費
```

これで DkMath は、Mathlib に無い Zsigmondy / FLT 無限降下向けの道具を、単なる独自補題集ではなく **契約駆動の形式化 API** として持てる。

今は良い段階じゃよ。
「存在を得た」から「使える武器として配給する」へ移る境目じゃ。ここで契約を固めたのは、とても賢い。

[1]: https://en.wikipedia.org/wiki/Zsigmondy%27s_theorem "Zsigmondy's theorem"

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 1b7419d2..a6a52071 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1634,6 +1634,74 @@ lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
 lake build DkMath.FLT.PrimeProvider
 ```
 
+### Step 6.4: Zsigmondy Contract Conditions for FLT / ABC
+
+Status:
+
+```text
+documented
+```
+
+The Petal-Zsigmondy negotiation is not useful if it only states that a
+primitive prime exists.  Downstream FLT and ABC code needs a complete contract
+bundle.
+
+The contract now has this intended shape:
+
+```text
+Zsigmondy:
+  PrimitivePrimeDivisor a b d q
+
+Petal / BezoutBridge:
+  q avoids the visible boundary a - b
+  q divides GN d (a - b) b
+  padicValNat q (a^d - b^d)
+    = padicValNat q (GN d (a - b) b)
+  AnchoredGNCarrier q d (a - b) b q
+
+Multiplicity layer:
+  local NoLift at q, or squarefree GN as a sufficient condition
+
+ABC:
+  ValuationFlow / local-load wrappers consume the multiplicity condition
+
+FLT:
+  PrimeProvider / no-Wieferich valuation surfaces consume the same routed q
+```
+
+Implemented Petal-facing names:
+
+```lean
+DkMath.Petal.primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor
+DkMath.Petal.zsigmondyPrimitivePrimeDivisor_not_dvd_boundary
+DkMath.Petal.zsigmondyPrimitivePrimeDivisor_dvd_GN
+DkMath.Petal.padicValNat_bodyDiff_eq_GN_of_zsigmondyPrimitivePrimeDivisor
+DkMath.Petal.anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor
+```
+
+This is the correct trading surface:
+
+```text
+Zsigmondy gives existence.
+Petal / BezoutBridge gives location and boundary separation.
+PrimitiveBeam / ValuationFlow gives valuation transfer.
+NoLift or squarefree GN gives multiplicity control.
+```
+
+The contract explicitly does not claim an unconditional `padicValNat <= 1`
+bound.  That bound belongs to the no-lift / squarefree layer.
+
+Mathlib status:
+
+```text
+The current local Mathlib dependency snapshot does not appear to contain a
+Bang-Zsigmondy / Zsigmondy primitive-divisor headquarters.
+```
+
+Therefore `DkMath.Zsigmondy` remains the project-owned facade.  If Mathlib later
+adds the full theorem, the desired migration is to keep `DkMath.Zsigmondy` as a
+stable facade and redirect its public theorems internally.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index d0eb0e5e..b227b03b 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -395,6 +395,51 @@ once the selected primitive witness has no `q^2` lift on `GN`, both the
 difference body and the `GN` side are prevented from being perfect `d`-th
 powers.
 
+### `DkMath.Petal.BezoutBridge`
+
+Records the Bezout/gcd reading of the Cosmic `GN` split in Petal-facing names.
+
+Important names:
+
+```lean
+cosmicBody_eq_boundary_mul_GN
+primitivePrimeFactor_not_dvd_boundary
+primitivePrimeFactor_dvd_GN_of_cosmicBoundary
+primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary
+padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor
+primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor
+zsigmondyPrimitivePrimeDivisor_not_dvd_boundary
+zsigmondyPrimitivePrimeDivisor_dvd_GN
+padicValNat_bodyDiff_eq_GN_of_zsigmondyPrimitivePrimeDivisor
+anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor
+```
+
+This file is the general Petal/Zsigmondy negotiation surface:
+
+```text
+Zsigmondy primitive divisor
+  -> PrimitiveBeam witness
+  -> boundary is avoided
+  -> GN carries the witness
+  -> body-difference valuation is read on GN
+  -> AnchoredGNCarrier
+```
+
+It is intentionally not a full ideal-theoretic Bezout development.  It is the
+thin bridge that lets downstream FLT and ABC files trade with Zsigmondy using
+the exact conditions they need.
+
+Current Mathlib status:
+
+```text
+No Bang-Zsigmondy / Zsigmondy primitive-divisor headquarters was found in the
+current local Mathlib dependency snapshot.
+```
+
+`DkMath.Zsigmondy` should therefore be treated as the project-owned facade for
+now.  If Mathlib later gains the full theorem, `DkMath.Zsigmondy` should remain
+as the stable package surface and be redirected internally.
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
index a50f7c8c..85171b1a 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
@@ -57,6 +57,90 @@ DkMath.Zsigmondy.primitivePrimeDivisor_body_three_imp_dvd_GN
 This means the existence layer is already present.  The missing Petal-facing
 piece is a thin translation layer for the `d = 3` reduced cubic surface.
 
+## Mathlib Headquarters Check
+
+Status: **no upstream headquarters found in the current local Mathlib**
+
+The local Mathlib dependency was searched for the following terms:
+
+```text
+Zsigmondy
+PrimitivePrimeDivisor
+primitive divisor
+Bang
+```
+
+No Mathlib theorem or namespace corresponding to the classical
+Bang-Zsigmondy theorem was found.  The search did return unrelated
+`Birkhoff` files, but those are Birkhoff representation / Birkhoff sum /
+convexity results and are not a Zsigmondy primitive-divisor API.
+
+Therefore the current working interpretation is:
+
+```text
+Mathlib headquarters:
+  not available in the current dependency snapshot
+
+DkMath.Zsigmondy:
+  local branch office / project-owned primitive-divisor API
+```
+
+`DkMath.Zsigmondy` should not be described as a full replacement for a future
+Mathlib headquarters.  It is currently a safe, project-owned contract around
+the prime-exponent route needed by Petal, FLT, and ABC work.
+
+If Mathlib later gains a full Bang-Zsigmondy theorem, the preferred migration
+is not to delete the DkMath-facing API.  Instead, keep `DkMath.Zsigmondy` as the
+stable facade and reprove or redirect its public theorems from the Mathlib
+headquarters.
+
+## Contract Scope for FLT / ABC
+
+The Petal-Zsigmondy negotiation is meaningful only if the contract includes the
+conditions needed by downstream FLT and ABC callers.
+
+The contract must not stop at:
+
+```text
+there exists a primitive prime q
+```
+
+Downstream callers need the stronger routed package:
+
+```text
+Zsigmondy existence:
+  PrimitivePrimeDivisor a b d q
+
+Petal / GN location:
+  q divides GN d (a - b) b
+  q avoids the visible boundary a - b
+
+Anchor carrier:
+  AnchoredGNCarrier q d (a - b) b q
+
+Valuation transfer:
+  padicValNat q (a^d - b^d)
+    = padicValNat q (GN d (a - b) b)
+
+Multiplicity condition supplied separately:
+  local NoLift at q, or squarefree GN as a sufficient condition
+```
+
+This is the condition bundle that FLT and ABC are allowed to trade for.  In
+particular:
+
+```text
+Zsigmondy gives existence.
+Petal / BezoutBridge gives location and boundary separation.
+PrimitiveBeam / ValuationFlow gives valuation transfer.
+NoLift or squarefree GN gives multiplicity control.
+```
+
+The contract explicitly does **not** claim an unconditional
+`padicValNat <= 1` bound.  That bound is false in general without a no-lift or
+squarefree-style hypothesis, as the `q = 7, a = 5, b = 3, d = 3` counterexample
+below shows.
+
 ## Recommended New Bridge
 
 Recommended file:
````
`````
