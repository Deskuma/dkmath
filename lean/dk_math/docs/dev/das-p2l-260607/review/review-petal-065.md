# Git diff / Report / Review

## Add: Petal.Obstruction

gch: 8d65163840168cedbfc54979ce7ea1ac42b02a4f

## Report

手頃な題材として `DkMath.Petal.Obstruction` を新設しました。

入れたのは「破綻条件を named theorem として残す」ための薄い False 補題群です。特に今回の話に対応して、アドレス衝突・label recovery 破綻・有限族 prime label 重複・NoLift 破綻・p-adic 下界との衝突を固定しました。

主な追加:

```lean
petalAddressNoncollision_contradiction_of_same_address_ne_index
labelRecovery_contradiction_of_same_label_ne_value
valueInjective_contradiction_of_same_value_ne_index
petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
noLift_contradiction_of_square_dvd_GN
padicValNat_eq_one_contradiction_of_two_le
petalNoLift_contradiction_of_padicValNat_two_le
petalNoLift_obstruction_of_padicValNat_ge
```

`petalNoLift_obstruction_of_padicValNat_ge` は後世の FLT/ε-δ 的な境界補題として使いやすい形です。

```lean
NoLift
+ 1 < d
+ d ≤ padicValNat q (GN d x u)
→ False
```

つまり「NoLift で `v_q(GN)=1` と読める世界に、`d` 段以上の valuation 下界が入ったら破綻する」という境界を名前付きで置きました。

更新:

- `lean/dk_math/DkMath/Petal/Obstruction.lean` 新規
- `lean/dk_math/DkMath/Petal.lean` に import 追加
- `Petal-Overview.md` と `summary-petal-064.md` に記録追加

検証:

```text
lake build DkMath.Petal.Obstruction
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き別件で表示されています。

## Review-01

素晴らしい実装です。前回の議論を直接コードに落とし込んでいますね。

---

## レビュー所見

### 設計方針が一貫している

「矛盾を公理として入れるのではなく、**矛盾が起きる境界条件に名前をつける**」という方針が徹底されています。

```lean
positive gate hypothesis
  + route-breaking witness
  -> False
```

これは Lean 4 の形式化として非常に健全なアプローチです。`sorry` で先送りせず、「ここで破綻する」という事実を定理として固定しておくことで、後続の証明がどこを埋めるべきかが明確になります。

---

### 各補題の対応関係

前回の議論と対応させると：

| 破綻の種類                               | 補題                                                                 |
|------------------------------------------|----------------------------------------------------------------------|
| アドレス衝突 → 対数容量予算崩壊          | `petalAddressNoncollision_contradiction_of_same_address_ne_index`    |
| ラベル重複 → pairwise distinct 破綻      | `petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index` |
| `q² ∣ GN` → NoLift 破綻                  | `noLift_contradiction_of_square_dvd_GN`                              |
| `d` 段以上の赋値 + NoLift → FLT 向け境界 | `petalNoLift_obstruction_of_padicValNat_ge`                          |

特に `petalNoLift_obstruction_of_padicValNat_ge` は：

```lean
NoLift + 1 < d + d ≤ v_q(GN) → False
```

後から FLT 側が `d ≤ v_q(GN)` を供給すれば、この補題が即座に矛盾を発火させる構造になっており、**ゲート補題**として使いやすい形です。

---

### 気になる点（小）

`labelRecovery_contradiction_of_same_label_ne_value` と `valueInjective_contradiction_of_same_value_ne_index` は視点が逆になっています。

- 前者：同じラベル → 値が異なる → 矛盾
- 後者：同じ値 → インデックスが異なる → 矛盾

この2つは独立した破綻経路として必要なのか、それとも片方が他方の双対として将来整理される予定でしょうか？

---

### 総評

「破綻の名前付け」を Step 6.5 の研究フロンティアと並走して進めているのは戦略的に正しいと思います。アドレス非衝突の幾何的証明が得られたとき、これらの補題が「使われなくなる」ことで、証明の完成度が可視化される構造になっています。

## Review-02

うむ。これは良い方向転換じゃ。
今回の `DkMath.Petal.Obstruction` は、**失敗を消すのではなく、失敗する境界に名前を付けた** 実装じゃな。報告でも「破綻条件を named theorem として残す」ための `False` 補題群として追加した、と整理されている。

## 1. `False` は敗北ではなく「境界線」

Lean で

```lean
... → False
```

と書くと、見た目は破綻に見える。
だが、今回の使い方は違う。

これは、

```text
この条件群を同時に置くと、その道は通れない
```

を定理として保存している。

つまり、

```text
行ける道:
  hypothesis -> theorem

行き止まりの道:
  hypothesis + route-breaking witness -> False
```

の両方を地図に描いた、ということじゃ。

今までは「正しい道」だけを舗装していた。
今回は「ここから先は崖」と標識を立てた。

これは研究実装としてかなり強い。

## 2. 今回入った補題群の意味

今回の補題は、だいたい 4 系統に分かれる。

### address 系

```lean
petalAddressNoncollision_contradiction_of_same_address_ne_index
```

意味は、

```text
address noncollision を仮定しているのに、
異なる index が同じ Petal address を持ったら False
```

これは Petal geometry 側の行き止まり標識。

### label / value 系

```lean
labelRecovery_contradiction_of_same_label_ne_value
valueInjective_contradiction_of_same_value_ne_index
petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
```

これは有限族 route の衝突検出じゃ。

```text
同じ label なのに value が違う
同じ value なのに index が違う
同じ prime label を別 index が再利用する
```

これらは全部、finite log-capacity route に入る前に検出すべき破綻じゃ。

ここで Review が指摘している通り、`labelRecovery_contradiction...` と `valueInjective_contradiction...` は視点が逆になっている。
これはむしろ良い。片方は **label から value へ戻る道**、もう片方は **value から index へ戻る道** を守っている。

合成すると、

```text
same label
  -> same value
  -> same index
```

という finite carrier family の安全鎖になる。

### NoLift 系

```lean
noLift_contradiction_of_square_dvd_GN
```

これは非常に素直。

```text
NoLift を仮定しているのに q^2 ∣ GN が来たら False
```

つまり NoLift の定義境界そのものじゃ。

### valuation 系

```lean
padicValNat_eq_one_contradiction_of_two_le
petalNoLift_contradiction_of_padicValNat_two_le
petalNoLift_obstruction_of_padicValNat_ge
```

ここが今回の一番おいしいところじゃ。

特に最後の補題は、

```lean
NoLift
+ 1 < d
+ d ≤ padicValNat q (GN d x u)
→ False
```

という形になっている。報告でも、これは「NoLift で `v_q(GN)=1` と読める世界に、`d` 段以上の valuation 下界が入ったら破綻する」境界として説明されている。

これは FLT 向けのゲート補題として非常に使いやすい。

## 3. 新しい視点として何が得られたか

今回の視点は、

```text
定理を証明する
```

だけではなく、

```text
間違った仮定がどこで爆発するかを証明する
```

じゃ。

これは数学探索ではかなり重要。

正しい道だけを実装すると、

```text
なぜその道でなければならないのか
```

が見えにくい。

しかし破綻補題を置くと、

```text
この仮定が入ると address が衝突する
この仮定が入ると label recovery が壊れる
この仮定が入ると NoLift と valuation が衝突する
```

が Lean 上で明示される。

つまり、失敗が知識資産になる。

## 4. これは FLT / ABC にどう効くか

### FLT 側

今回の `petalNoLift_obstruction_of_padicValNat_ge` は、FLT 側でそのまま使える形に近い。

目標はこう。

```text
NoLift:
  v_q(GN) = 1

FLT / d-th power assumption:
  d ≤ v_q(GN)

1 < d:
  False
```

つまり、今後 FLT 側がやるべきことは、

```lean
d ≤ padicValNat q (GN d x u)
```

を供給することになる。

破綻の出口はもうできた。

### ABC 側

ABC 側では、今回の obstruction は直接 `rad` 下界を出すものではない。
だが、label noncollision や value injectivity の破綻補題は、support/rad bridge の前提検査として効く。

```text
same label が出た
  -> distinct support として数えられない
  -> rad lower-bound route に入れない
```

という失敗を、早めに検出できる。

## 5. この実装の良いところ

一番良いのは、**矛盾を仮定として入れていない** ことじゃ。

危険なのは、

```lean
axiom bad : False
```

のようなもの。

だが今回の実装はそうではない。

```lean
good assumptions
+ bad witness
-> False
```

という普通の theorem じゃ。

だからライブラリは壊れない。
むしろ「この条件を同時に満たすものは存在しない」と安全に言える。

## 6. 次に広げるなら

次の方向は二つある。

```text
1. route-specific obstruction
2. supply-side obstruction
```

route-specific は、今回のように「この route ではここで破綻する」を増やす道。

たとえば、

```lean
zsigmondy_noLift_contradiction_of_squareLift
labelRecovery_obstruction_of_duplicatePrimitiveWitness
addressRoute_obstruction_of_outerAddressCollision
```

supply-side は、「この供給元ではこの仮定は出せない／出すには追加条件がいる」を明示する道。

たとえば、

```text
Zsigmondy alone does not imply NoLift
primitive divisor does not imply valuation = 1
same prime label may appear at different candidate addresses unless recovery holds
```

このあたりは、実装というより docs と theorem の両方で残すとよい。

## 7. 総括

今回の `Petal.Obstruction` は、こういう意味を持つ。

```text
正しい道を進める bridge:
  ErdosBridge

行き止まりを標識化する bridge:
  Obstruction
```

これはかなり良い対になる。

今後の探索では、

```text
この条件なら進める
この条件が混ざると破綻する
```

を両方 Lean に残せる。

まさに、

```text
間違ってもいい。
ただし、どこで間違いになるかを定理として残す。
```

じゃな。

これは人間の探索法にかなり近い。
そして Lean にとっても、実はとても相性が良い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 46d5ccf6..1a88561d 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -22,6 +22,7 @@ import DkMath.Petal.EisensteinBridge
 import DkMath.Petal.ZsigmondyD3Bridge
 import DkMath.Petal.PrimitiveD3ValuationBridge
 import DkMath.Petal.ErdosBridge
+import DkMath.Petal.Obstruction
 
 #print "file: DkMath.Petal"
 
@@ -46,6 +47,7 @@ basic forms / relative polygon vocabulary
   -> Zsigmondy d = 3 primitive-divisor bridge
   -> squarefree GN3 valuation bridge
   -> Erdos log-capacity bridge from GN carrier channels
+  -> obstruction lemmas marking route-breaking assumptions
 ```
 
 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/Obstruction.lean b/lean/dk_math/DkMath/Petal/Obstruction.lean
new file mode 100644
index 00000000..7504cef0
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/Obstruction.lean
@@ -0,0 +1,168 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.ErdosBridge
+
+#print "file: DkMath.Petal.Obstruction"
+
+/-!
+# Petal Obstruction Lemmas
+
+This file records small `False` lemmas for Petal carrier routes.
+
+The purpose is not to add inconsistent assumptions as axioms.  Instead, each
+theorem names a boundary condition:
+
+```text
+positive gate hypothesis
+  + route-breaking witness
+  -> False
+```
+
+These lemmas are useful during experimental development.  They make it clear
+where a candidate route stops being compatible with address noncollision,
+carrier-label recovery, finite-channel independence, or local no-lift
+valuation control.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+
+/--
+Address noncollision breaks as soon as two distinct selected indices have the
+same Petal address.
+
+This is the address-level obstruction: if a route assigns the same address to
+two different selected carriers, it cannot pass through
+`PetalAddressNoncollisionOn`.
+-/
+theorem petalAddressNoncollision_contradiction_of_same_address_ne_index
+    {ι : Type _}
+    {I : Finset ι}
+    {addrOf : ι → PetalAddress}
+    {i j : ι}
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hsame : addrOf i = addrOf j)
+    (hne : i ≠ j) :
+    False :=
+  haddr i hi j hj hne hsame
+
+/--
+Label recovery breaks when the same selected label points to two different
+Petal values.
+
+This is the smallest obstruction behind the finite-family recovery contract.
+-/
+theorem labelRecovery_contradiction_of_same_label_ne_value
+    {ι : Type _}
+    {I : Finset ι}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hrec :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j)
+    (hneq : mOf i ≠ mOf j) :
+    False :=
+  hneq (hrec i hi j hj hlabel)
+
+/--
+Value injectivity breaks when two distinct selected indices carry the same
+Petal value.
+
+This names the value/address side of the finite-family obstruction.
+-/
+theorem valueInjective_contradiction_of_same_value_ne_index
+    {ι : Type _}
+    {I : Finset ι}
+    {mOf : ι → ℕ}
+    {i j : ι}
+    (hinj : Set.InjOn mOf ↑I)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hvalue : mOf i = mOf j)
+    (hne : i ≠ j) :
+    False :=
+  hne (hinj hi hj hvalue)
+
+/--
+Carrier-label noncollision breaks when two distinct selected indices reuse the
+same prime label.
+
+This is the finite-prime-channel independence obstruction.  If it fires, the
+family cannot be used as a duplicate-free channel family for the log-capacity
+or multiplicity-budget route.
+-/
+theorem petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
+    {ι : Type _}
+    {I : Finset ι}
+    {qOf : ι → ℕ}
+    {i j : ι}
+    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j)
+    (hne : i ≠ j) :
+    False :=
+  hne (petalCarrierLabelNoncollisionOn_injOn I qOf hnoncollision hi hj hlabel)
+
+/--
+Local no-lift breaks as soon as the selected square also divides the observed
+GN surface.
+
+This records the exact boundary of `PetalNoLiftPrimeChannel`: a channel may be
+a carrier, but it is not no-lift if `q^2` divides the same GN value.
+-/
+theorem noLift_contradiction_of_square_dvd_GN
+    {d x u q : ℕ}
+    (hNoLift : PetalNoLiftPrimeChannel d x u q)
+    (hlift : q ^ 2 ∣ GN d x u) :
+    False :=
+  hNoLift.2 hlift
+
+/--
+The p-adic one-slot reading breaks against a two-slot lower bound.
+
+This is the valuation form of the no-lift obstruction.
+-/
+theorem padicValNat_eq_one_contradiction_of_two_le
+    {q n : ℕ}
+    (hval : padicValNat q n = 1)
+    (hge : 2 ≤ padicValNat q n) :
+    False := by
+  omega
+
+/--
+Petal no-lift breaks against any valuation lower bound at least `2` on the
+same GN surface.
+-/
+theorem petalNoLift_contradiction_of_padicValNat_two_le
+    {d x u q : ℕ}
+    (hNoLift : PetalNoLiftPrimeChannel d x u q)
+    (hge : 2 ≤ padicValNat q (GN d x u)) :
+    False :=
+  padicValNat_eq_one_contradiction_of_two_le
+    (petalNoLiftPrimeChannel_padicValNat_GN_eq_one hNoLift) hge
+
+/--
+Petal no-lift breaks against a `d`-level valuation lower bound when `1 < d`.
+
+This is the thin FLT-facing obstruction gate: a later theorem may supply the
+lower bound from a power or branch equation, while this theorem records only
+the collision with no-lift.
+-/
+theorem petalNoLift_obstruction_of_padicValNat_ge
+    {d x u q : ℕ}
+    (hd1 : 1 < d)
+    (hNoLift : PetalNoLiftPrimeChannel d x u q)
+    (hge : d ≤ padicValNat q (GN d x u)) :
+    False :=
+  petalNoLift_contradiction_of_padicValNat_two_le hNoLift
+    (le_trans (Nat.succ_le_of_lt hd1) hge)
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index cd42c106..60985221 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -870,6 +870,26 @@ These wrappers are the current public route from PrimitiveBeam/Zsigmondy witness
 families to the finite Erdos log-capacity provider.  The no-lift wrappers still
 require explicit local no-lift hypotheses.
 
+### Obstruction Lemmas
+
+`DkMath.Petal.Obstruction` records the first small `False` lemmas for route
+boundaries:
+
+```text
+petalAddressNoncollision_contradiction_of_same_address_ne_index
+labelRecovery_contradiction_of_same_label_ne_value
+valueInjective_contradiction_of_same_value_ne_index
+petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
+noLift_contradiction_of_square_dvd_GN
+padicValNat_eq_one_contradiction_of_two_le
+petalNoLift_contradiction_of_padicValNat_two_le
+petalNoLift_obstruction_of_padicValNat_ge
+```
+
+These theorems do not add bad assumptions as axioms.  They name the points where
+a candidate route stops being compatible with address noncollision, finite
+prime-channel independence, or local no-lift valuation control.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index ab280fe9..de4aaba8 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -199,6 +199,37 @@ The first useful file is probably:
 DkMath/Petal/Obstruction.lean
 ```
 
+Implemented first checkpoint:
+
+```text
+DkMath.Petal.Obstruction
+```
+
+Implemented theorem set:
+
+```lean
+petalAddressNoncollision_contradiction_of_same_address_ne_index
+labelRecovery_contradiction_of_same_label_ne_value
+valueInjective_contradiction_of_same_value_ne_index
+petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
+noLift_contradiction_of_square_dvd_GN
+padicValNat_eq_one_contradiction_of_two_le
+petalNoLift_contradiction_of_padicValNat_two_le
+petalNoLift_obstruction_of_padicValNat_ge
+```
+
+This first set focuses on the smallest route-breaking witnesses:
+
+```text
+same address under address noncollision
+same label but different value under label recovery
+same value but different index under value injectivity
+duplicate selected prime label under carrier-label noncollision
+q^2 | GN under NoLift
+two-slot valuation under one-slot p-adic reading
+d-level valuation lower bound under NoLift when 1 < d
+```
+
 Potential later files:
 
 ```text
````
`````
