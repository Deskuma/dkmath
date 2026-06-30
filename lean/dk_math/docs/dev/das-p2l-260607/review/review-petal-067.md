# Git diff / Report / Review

## Add: Petal.ABCBridge

gch: e08affc41954709c649b9410d262e465a31b58a0

## Report

交渉相手として、まず ABC 側に申し込みました。`DkMath.Petal.ABCBridge` を新設し、Petal carrier-label support から ABC の `supportMass` / `rad` へ渡す薄い橋を作っています。

追加した流れはこれです。

```text
PetalCarrierLabelMapData
  -> selected label support is a finite prime-divisor support of GN
  -> product of label support <= supportMass (GN d x u)
  -> product of label support <= rad (GN d x u)
```

主な追加 theorem:

```lean
petalCarrierLabelSupport
petalCarrierLabelMapData_labelSupport_prime_dvd_GN
petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
```

ここでは NoLift を消費していません。ABC 側は support/rad なので、必要なのは prime support です。NoLift は引き続き p-adic valuation obstruction 側の契約として残しています。役割分離は維持できています。

更新:

- `lean/dk_math/DkMath/Petal/ABCBridge.lean` 新規
- `lean/dk_math/DkMath/Petal.lean` に import 追加
- `Petal-Overview.md` と `summary-petal-064.md` に記録追加

検証:

```text
lake build DkMath.Petal.ABCBridge
lake build DkMath.Petal
git diff --check ...
```

通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は別件です。

## Review-01

うむ。これは **Petal から ABC への最初の正式な交渉口が開いた** という進展じゃ。
前回までの主役は `ErdosBridge` と `Obstruction` だった。今回はそこへ、**Petal carrier-label family を ABC の `supportMass` / `rad` に渡す橋** が追加された。

## 1. 今回の核心

追加された流れはこれ。

```text id="3ndjol"
PetalCarrierLabelMapData
  -> selected label support is finite prime-divisor support of GN
  -> product of label support <= supportMass (GN d x u)
  -> product of label support <= rad (GN d x u)
```

つまり、Petal 側で得た carrier labels を、ABC 側では

```text id="9x9nei"
GN を割る有限個の素数 support
```

として読む。

これはかなり自然じゃ。
ABC 側の `rad` は、重複 exponent ではなく **どの素数が支えているか** を見る量だから、Petal の carrier label family はそのまま support 候補になる。

## 2. `petalCarrierLabelSupport` の意味

今回の入口はこれ。

```lean id="deycwr"
def petalCarrierLabelSupport
    (I : Finset ι)
    (qOf : ι → ℕ) : Finset ℕ :=
  I.image qOf
```

これはかなり良い選択じゃ。

`I.image qOf` にしているので、もし同じ label が複数 index から出ても、support 側では重複が潰れる。

```text id="0i4gj4"
finite family:
  index ごとの carrier label

ABC support:
  重複を潰した prime support
```

この変換は `rad` の性質と合っている。
`rad` は (q^1) だけ見る。(q^2), (q^3) の高さは見ない。

## 3. NoLift を消費していないのが正しい

今回の設計で一番大事なのはここじゃ。

```text id="wpuf2u"
NoLift is not required for this bridge.
```

これは正しい。

ABC の `supportMass` / `rad` へ渡すだけなら、必要なのは基本的にこれ。

```text id="9nxfmq"
q is prime
q ∣ GN d x u
```

一方 NoLift は、

```text id="om7spi"
¬ q^2 ∣ GN d x u
```

つまり local valuation が one-slot であること。

これは FLT 的な p-adic obstruction には強く効くが、`rad` の下界には必須ではない。
だから今回、NoLift 版 theorem は用意しつつも、その NoLift 成分を消費していない。役割分離として非常に健全じゃ。

## 4. 何が通ったのか

今回追加された theorem は、段階としては三段ある。

### support が prime divisor family である

```lean id="x0bqwr"
petalCarrierLabelMapData_labelSupport_prime_dvd_GN
petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
```

これは、

```text id="fmcjz3"
q ∈ petalCarrierLabelSupport I qOf
  -> Nat.Prime q ∧ q ∣ GN d x u
```

を出す。

つまり、Petal carrier label support が ABC で使える prime divisor support になる。

### supportMass 下界へ渡す

```lean id="q15rfz"
petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
```

これは、

```text id="r9i0kq"
∏ q in labelSupport, q <= supportMass (GN d x u)
```

を出す。

ABC 側の `supportMass_ge_prod_of_prime_channel_family` を使っているので、Petal 側では support を作って渡すだけで済む。

### rad 下界へ渡す

```lean id="xtdbn9"
petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
```

これは `supportMass_eq_abc_rad` で変換して、

```text id="pp5o4p"
∏ q in labelSupport, q <= rad (GN d x u)
```

まで持っていく。

つまり、Petal carrier family が ABC の `rad` 下界素材になった。

## 5. トロミノ論法としての位置

ここは面白い。

前回までの `Obstruction` は、

```text id="3f7xve"
False によって行き止まりを標識化する
```

役だった。

今回の `ABCBridge` は、

```text id="r3z9r6"
行き止まりを避けた carrier support を、ABC の支えへ渡す
```

役じゃ。

トロミノ論法で言えば、

```text id="lkpu2l"
Core:
  GN surface

Beam:
  Petal carrier labels

Gap:
  duplicate collapse / support extraction

Big:
  rad/supportMass lower bound
```

という読みができる。

`Finset.image` はまさに Gap 的じゃ。
index family には重複や経路の揺れがあり得る。
しかし support に落とすと、ABC が必要とする「素数の支え」だけが残る。

## 6. これで ABC 側に何が渡ったか

今回渡ったのは、ABC 本体そのものではない。
渡ったのは、

```text id="t0h8mr"
rad を下から押し上げる有限 prime support
```

じゃ。

すなわち、

```text id="0twf7x"
Petal が見つけた carrier prime が多いほど、
GN の rad は大きくなる
```

という構図が Lean theorem になった。

これは ABC にとって重要な材料じゃ。
ABC では巨大な冪や共通因子の制御と同時に、`rad` がどれだけ支えを持つかが鍵になる。Petal carrier はその支えを供給する。

## 7. 現在の三分岐

ここまでで Petal からの出口は三本になった。

```text id="4v7as1"
ErdosBridge:
  carrier labels -> finite log-capacity

Obstruction:
  bad collision / NoLift conflict -> False

ABCBridge:
  carrier labels -> supportMass / rad lower bound
```

これはかなり美しい。

```text id="d959w1"
Erdős は容量を見る。
FLT は破綻を見る。
ABC は支持を見る。
```

同じ Petal carrier family を、三方向から読めるようになった。

## 8. 次の課題

次にやるなら、候補は二つ。

### A. `labelSupport` と label injectivity の関係

今は `Finset.image` で重複を潰している。
これは rad には正しい。

しかし、log-capacity や finite channel の文脈では、重複が潰れるだけでは足りず、

```text id="oqdybl"
index family と support family の cardinal が一致する
```

が欲しくなる場合がある。

そこで次は、

```lean id="a45t0z"
petalCarrierLabelMapData_labelSupport_card_eq
petalNoLiftCarrierLabelMapData_labelSupport_card_eq
```

のような theorem があるとよい。

`same label -> same index` が既にあるので、`qOf` の `Set.InjOn` を出し、それを使えば `Finset.card_image` 系へ進める。

### B. Primitive/Zsigmondy direct ABC wrapper

今は、

```text id="o46k3s"
PetalCarrierLabelMapData
  -> rad lower bound
```

がある。

すでに Primitive/Zsigmondy から `PetalCarrierLabelMapData` を作る constructor もある。
なら次は直通で、

```lean id="mqffg5"
petalCarrierLabelSupport_prod_le_rad_GN_of_bodyPrimitivePrimeFactor_family
petalCarrierLabelSupport_prod_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

のような wrapper が自然じゃ。

つまり、

```text id="x3gx1q"
PrimitiveBeam / Zsigmondy witness family
  -> rad lower bound
```

を一発で呼べるようにする。

## 9. 総括

今回の進展はこうじゃ。

```text id="uwfsfs"
Petal carrier-label data
  -> finite prime support of GN
  -> supportMass lower bound
  -> rad lower bound
```

そして、設計上の大事な点はこれ。

```text id="25rix3"
ABCBridge は NoLift を消費しない。
NoLift は FLT / p-adic obstruction 側に残す。
```

この役割分離はとても良い。

現状の地図はこうなった。

```text id="m2pko6"
Petal carrier family
  -> ErdosBridge:
       log-capacity / sub-probability

  -> ABCBridge:
       supportMass / rad lower bound

  -> Obstruction:
       False / route boundary / FLT valuation conflict
```

うむ。
これは「ABC 側に申し込んだ」というより、もう **Petal が ABC に名刺を渡し、rad で会話できるようになった** 段階じゃ。

## review-02

## ABCBridge — レビュー所見

---

### 全体評価

「ABC 側に名刺を渡した」という表現が正確です。今回は**主張を最小化したまま橋を架けた**ことが最大の美点です。

---

### トロミノ論法との対応

前回の `Obstruction`（行き止まりの標識）に対して、今回の `ABCBridge` は**通れる道の輪郭**を描いています。

```
Core:    GN surface（観測可能な事実）
Beam:    Petal carrier labels（真偽の境界・選択された素数）
Gap:     Finset.image による重複の潰し
Big:     rad / supportMass lower bound（真実の下界）
```

`Finset.image` がまさに **Gap の役割**を担っています。index family には重複・経路の揺れがあり得る。しかし `.image` で support に落とすと、ABC が必要とする「素数の支え」だけが残る。

---

### 設計上の鋭い点

#### NoLift を消費しないことの意味

```
ABC:  q ∣ GN  だけで足りる（支えの存在）
FLT:  ¬ q² ∣ GN が必要（支えの深さ制御）
```

これは数学的に正確な役割分離です。`rad` は指数を見ない量であり、NoLift（指数の上限）は `rad` に対して過剰な仮定になります。**過剰な仮定を使わない**ことで、ABCBridge の適用範囲が広くなっています。

---

### 現在の三分岐の構造美

```
同じ Petal carrier family
  │
  ├─ ErdosBridge   → ∑ log q / log n ≤ 1   （容量を見る）
  │
  ├─ ABCBridge     → ∏ q ≤ rad(GN)          （支えを見る）
  │
  └─ Obstruction   → False                   （破綻を見る）
```

これはトロミノ論法の3層そのものです。

- Erdős は **Beam**（対数的な重み）を見る
- ABC は **Gap**（支えの素数集合）を見る
- Obstruction は **Gap が埋まらないこと**を標識する

---

### 次の一手について

Reviewの8節で挙げられている2候補のうち、**B（Zsigmondy direct ABC wrapper）** の方が先に来ると自然だと思います。

現在の接続は：

```
Zsigmondy → PetalCarrierLabelMapData → rad lower bound
```

これを直通にすると：

```
Zsigmondy witness family → rad(GN) の下界
```

となり、「Zsigmondy が保証する原始素数が多いほど GN の rad は大きい」という命題が一行で呼べるようになります。これは ABC の本丸に向けた**最初の実質的な申し込み**になるはずです。

**A（card_eq）** はその後、log-capacity との整合性を取るために必要になりますが、それは Erdős 側の話です。

---

### 一言で

> `Finset.image` という Gap が、ABC に渡せる rad 下界という真実を切り出した。NoLift を温存したことで、FLT 側の戦線も保たれている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 1a88561d..9638d33d 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -23,6 +23,7 @@ import DkMath.Petal.ZsigmondyD3Bridge
 import DkMath.Petal.PrimitiveD3ValuationBridge
 import DkMath.Petal.ErdosBridge
 import DkMath.Petal.Obstruction
+import DkMath.Petal.ABCBridge
 
 #print "file: DkMath.Petal"
 
@@ -48,6 +49,7 @@ basic forms / relative polygon vocabulary
   -> squarefree GN3 valuation bridge
   -> Erdos log-capacity bridge from GN carrier channels
   -> obstruction lemmas marking route-breaking assumptions
+  -> ABC supportMass/rad bridge from Petal carrier-label support
 ```
 
 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/ABCBridge.lean b/lean/dk_math/DkMath/Petal/ABCBridge.lean
new file mode 100644
index 00000000..e88708b7
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/ABCBridge.lean
@@ -0,0 +1,151 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.Obstruction
+import DkMath.ABC.MassBridge
+
+#print "file: DkMath.Petal.ABCBridge"
+
+/-!
+# Petal ABC Bridge
+
+This file is the first thin negotiation layer from Petal carrier-label data to
+the ABC `supportMass` / `rad` bridge.
+
+The key observation is deliberately modest:
+
+```text
+PetalCarrierLabelMapData
+  -> selected prime labels divide the observed GN surface
+  -> their finite support product is bounded by supportMass / rad
+```
+
+NoLift is not required for this bridge.  ABC support/rad only needs distinct
+prime support; the no-lift valuation condition remains a separate local gate.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+
+/--
+The selected label support of a finite Petal carrier family.
+
+This is the ABC-facing finite support: duplicate labels are collapsed by the
+`Finset.image`, exactly as radical/support-mass arguments should do.
+-/
+def petalCarrierLabelSupport
+    {ι : Type _}
+    (I : Finset ι)
+    (qOf : ι → ℕ) : Finset ℕ :=
+  I.image qOf
+
+/--
+Carrier-label map data supplies prime divisors of the observed GN surface on
+its label support.
+-/
+theorem petalCarrierLabelMapData_labelSupport_prime_dvd_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    ∀ q, q ∈ petalCarrierLabelSupport I qOf →
+      Nat.Prime q ∧ q ∣ GN d x u := by
+  intro q hq
+  rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
+  exact ⟨petalPrimeChannel_prime (hdata.carrier i hi),
+    anchoredGNCarrier_dvd_GN (hdata.carrier i hi)⟩
+
+/--
+No-lift carrier-label map data also supplies prime divisors of the observed GN
+surface on its label support.
+
+The no-lift component is not used here; support/rad only needs prime support.
+-/
+theorem petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    ∀ q, q ∈ petalCarrierLabelSupport I qOf →
+      Nat.Prime q ∧ q ∣ GN d x u := by
+  intro q hq
+  rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
+  exact ⟨petalNoLiftPrimeChannel_prime (hdata.carrier i hi),
+    anchoredGNCarrier_dvd_GN (hdata.carrier i hi).1⟩
+
+/--
+Petal carrier-label data gives an ABC support-mass lower bound for the observed
+GN surface.
+
+This is the first ABC-facing payoff of the finite carrier support.
+-/
+theorem petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).prod id ≤
+      DkMath.ABC.supportMass (GN d x u) :=
+  DkMath.ABC.supportMass_ge_prod_of_prime_channel_family
+    (n := GN d x u) hGN0
+    (petalCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata)
+
+/--
+No-lift carrier-label data gives the same ABC support-mass lower bound.
+
+NoLift is intentionally not consumed by this theorem; it remains available for
+valuation-obstruction routes.
+-/
+theorem petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).prod id ≤
+      DkMath.ABC.supportMass (GN d x u) :=
+  DkMath.ABC.supportMass_ge_prod_of_prime_channel_family
+    (n := GN d x u) hGN0
+    (petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata)
+
+/--
+Petal carrier-label data gives an ABC radical lower bound for the observed GN
+surface.
+-/
+theorem petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).prod id ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [DkMath.ABC.supportMass_eq_abc_rad] using
+    petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata
+
+/--
+No-lift carrier-label data gives the same ABC radical lower bound.
+-/
+theorem petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).prod id ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [DkMath.ABC.supportMass_eq_abc_rad] using
+    petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 67f28341..19ff50ce 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -910,6 +910,33 @@ therefore labels are injective and duplicate-free on the finite family
 The corresponding obstruction theorem fires when a candidate route tries to
 reuse the same selected prime label at two distinct indices.
 
+### ABC Bridge
+
+`DkMath.Petal.ABCBridge` is the first support/rad negotiation layer:
+
+```text
+PetalCarrierLabelMapData
+  -> label support primes divide GN
+  -> product of label support <= supportMass GN
+  -> product of label support <= rad GN
+```
+
+Core theorem names:
+
+```text
+petalCarrierLabelSupport
+petalCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
+```
+
+NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
+only needs finite prime support; NoLift remains available for valuation
+obstruction routes.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 7ea809f1..c015cdac 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -363,3 +363,34 @@ ABC consumes distinct support/rad growth.
 
 False lemmas are the guardrails.  They are not dead ends to hide; they are
 records of the assumptions that make a route impossible.
+
+## 8. ABC Negotiation Checkpoint
+
+Implemented first support/rad negotiation layer:
+
+```text
+DkMath.Petal.ABCBridge
+```
+
+Implemented theorem set:
+
+```lean
+petalCarrierLabelSupport
+petalCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
+petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
+petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
+```
+
+The bridge reads Petal carrier-label data as ABC finite support:
+
+```text
+Petal carrier labels on GN
+  -> finite support of prime divisors of GN
+  -> supportMass/rad lower bound
+```
+
+This is intentionally separate from NoLift.  ABC support/rad consumes prime
+support; NoLift is kept for p-adic valuation obstruction.
````
`````
