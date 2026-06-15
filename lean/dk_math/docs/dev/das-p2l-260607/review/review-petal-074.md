# Git diff / Report / Review

## Upd: Petal.RangeFamily

gch: a82ba872b695ca79674e8a2896405b88461643ec

## Report

進めました。

`DkMath.Petal.RangeFamily` に False/obstruction 補題を追加しました。

```lean
rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
```

意味はこれです。

```text
pairwise label separation
same label at two distinct in-range indices
  -> False
```

つまり、`qOf` 候補を試していて `i < k`, `j < k`, `i ≠ j` なのに `qOf i = qOf j` が見つかった場合、その family は RangeFamily の独立 carrier route に乗れない、という破綻条件を Lean で固定しました。

docs も同期済みです。

検証:

```bash
lake build DkMath.Petal.RangeFamily
lake build DkMath.Petal
git diff --check -- ...
```

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回範囲外のままです。

## Review

うむ。これは **Collatz に Petal を突き合わせる準備として、ちょうど良い False 補題が入った** 状況じゃ。

今回の追加は小さい。

```lean
rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
```

しかし意味はかなり大きい。

```text
pairwise label separation
same label at two distinct in-range indices
  -> False
```

つまり、

```text
range k に並べた候補 qOf 0, qOf 1, ..., qOf (k-1)
```

が「全部別 label である」と主張しているのに、異なる index で同じ label が見つかったら、その family は **独立 carrier family としては破綻する**。これはまさに「False を得て、道の行き止まりを知る」補題じゃ。

## 1. RangeFamily の現在地

ここまでの `RangeFamily` は、こういう構造になった。

```text
I = Finset.range k
mOf i = i + 1
qOf i = i 番目の candidate label
```

そして、もし

```text
i < k, j < k, i != j -> qOf i != qOf j
```

が成り立ち、各 `qOf i` が PrimitiveBeam / Zsigmondy witness なら、

```text
2^k <= supportMass(GN)
2^k <= rad(GN)
```

へ行ける。

今回の False 補題はその反対側じゃ。

```text
同じ qOf が出た
  -> pairwise route は閉じる
  -> 独立 k 本 carrier として数えてはいけない
```

つまり、成功ルートと失敗ルートが対になった。

## 2. Collatz と相性がよい理由

Collatz は本質的に、

```text
分岐
圧縮
合流
周期候補
2-adic height
odd core
```

の問題じゃ。

特に加速 Collatz を見ると、

```text
n odd
3n + 1 = 2^a m
m odd
```

という形で、毎回

```text
3n + 1 の 2-adic height a
次の odd core m
```

を取り出す。

これは Petal 的にはかなり自然に読める。

```text
Core:
  現在の odd state n

Beam:
  3n + 1 による伸長

Gap:
  2^a による圧縮・除去

次 state:
  odd core m
```

相対多角数が Collatz 観点を持っていた、という話ともつながる。
「成長した形を、単位核や差分核で剥がして次の形へ移る」という読みだからじゃ。

## 3. `qOf` を Collatz でどう読むか

Collatz に Petal RangeFamily を当てるなら、まず `qOf i` は「i 番目の状態の label」として読むのがよい。

候補は複数ある。

```text
qOf i = i 番目の odd core

qOf i = i 番目の 3n+1 の primitive prime label

qOf i = i 番目の 2-adic height と odd core を混ぜた address

qOf i = residue class / PetalAddress を Nat 符号化したもの
```

一番素直なのは、

```text
qOf i = oddPart( Collatz^i n )
```

または加速版で、

```text
qOf i = acceleratedOddOrbit n i
```

じゃ。

このとき pairwise condition は、

```text
0 <= i < k の範囲では odd core が重複しない
```

という意味になる。

## 4. Collatz では「重複」は失敗ではなく情報

ここが重要じゃ。

ABC / primitive carrier route では、label 重複は独立性の失敗だった。

しかし Collatz では、label 重複はむしろ本命情報になり得る。

```text
同じ状態に戻った
  -> cycle 候補

同じ odd core に合流した
  -> orbit merge

同じ residue/address に戻った
  -> fold / petal 再入
```

つまり Collatz では、今回の False 補題は単なる「ダメ」ではない。

```text
独立 carrier route としては False
だが、Collatz dynamics としては合流・周期・折り返しの検出
```

になる。

これはかなり面白い。

## 5. Petal × Collatz の二つの読み

### A. 独立 carrier 読み

範囲 `k` の中で label が全部違うなら、

```text
k 本の独立 Beam がある
```

と読める。

この場合は、Petal.ABCBridge 的に

```text
2^k <= rad(...)
```

のような support 増大へつながる。

### B. 合流 orbit 読み

途中で同じ label が出たなら、

```text
独立性は壊れる
```

しかし Collatz では、

```text
同じ状態へ戻る
同じ odd core へ合流する
同じ address に入る
```

という力学的情報になる。

ここで `False` は、

```text
この区間を「独立 k 本」と仮定する道は通れない
```

というだけで、Collatz 研究としてはむしろ観測結果じゃ。

## 6. 今回の補題の Collatz 的な読み

今回の補題は、Collatz 向けに読むとこうなる。

```text
範囲 k の orbit labels は全部違う、と仮定する。
しかし i < k, j < k, i != j で同じ label が出た。
なら、その orbit segment は独立 range family ではない。
```

これは、Collatz の探索でよくある二択を Lean に残せる。

```text
case 1:
  重複なし
  -> 独立軌道片として扱う

case 2:
  重複あり
  -> 合流 / cycle / fold として扱う
```

これはまさにトロミノ論法じゃ。

```text
Core:
  orbit segment

Beam:
  各 step の label

False:
  独立性仮定の破綻

Gap:
  重複が示す fold / merge / cycle 情報

Big:
  Collatz orbit の全体構造
```

## 7. 次に作るなら

次に欲しいのは、`Petal.RangeFamily` をそのまま Collatz に依存させるのではなく、別ファイルで橋を作ることじゃ。

候補名は例えば、

```text
DkMath.Collatz.PetalBridge
DkMath.Collatz.RangeFamily
DkMath.Collatz.PetalOrbit
```

最小構成はこう。

```lean
def collatzOddStep (n : ℕ) : ℕ := ...
def collatzOddOrbit (n i : ℕ) : ℕ := ...

def collatzOrbitLabel (n : ℕ) (i : ℕ) : ℕ :=
  collatzOddOrbit n i
```

そして最初に置く補題は、

```text
collatz_rangeLabel_collision_obstruction
```

意味は、

```text
range k の orbit label が pairwise distinct だと仮定しているのに、
i != j で同じ orbit label が出たら False
```

これは今回の

```lean
rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
```

をそのまま使える。

## 8. Collatz への本命接続

本命はおそらくこれじゃ。

```text
Collatz orbit segment
  -> Petal address sequence
  -> either pairwise separated
     or collision occurs

pairwise separated:
  support / capacity / growth 下界へ

collision:
  deterministic map により cycle / merge 解析へ
```

Collatz は「いつか 1 に落ちる」問題なので、完全な独立成長だけではダメじゃ。
むしろ、

```text
成長するなら独立 support が増える
だが圧縮・合流がある
その合流構造を False 補題で検出する
```

というルートが DkMath らしい。

## 9. 総括

今回の更新は、Collatz へ戻るにはかなり良い。

```text
RangeFamily:
  k 本の候補 Beam を並べる

pairwise endpoint:
  全部違えば独立 carrier route

obstruction endpoint:
  同じ label が出たら独立 route は False
```

Collatz ではこの「同じ label が出た」が、失敗ではなく、

```text
orbit merge
cycle candidate
folded petal
```

の観測になる。

つまり、今回の補題は Collatz に対して、

```text
独立して進む軌道片
合流して折り返す軌道片
```

を分けるための最小診断器になる。

うむ。
相対多角数から Collatz へ戻るなら、今がちょうど良い。Petal は、Collatz 軌道を **花弁として展開し、重複を fold として検出する道具** になり得る。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/RangeFamily.lean b/lean/dk_math/DkMath/Petal/RangeFamily.lean
index f7d0e30a..e36a1d0c 100644
--- a/lean/dk_math/DkMath/Petal/RangeFamily.lean
+++ b/lean/dk_math/DkMath/Petal/RangeFamily.lean
@@ -68,6 +68,25 @@ theorem rangeLabel_injOn_of_pairwise_ne
   by_contra hij
   exact hneq i (by simpa using hi) j (by simpa using hj) hij hq
 
+/--
+Range pairwise label separation breaks as soon as two distinct in-range indices
+reuse the same label.
+
+This is the `False` observation form of `rangeLabel_injOn_of_pairwise_ne`.
+It is useful when testing a proposed `qOf`: finding one duplicate label at
+different indices identifies exactly why the range-family route cannot supply
+independent carrier labels.
+-/
+theorem rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
+    {k : ℕ} {qOf : ℕ → ℕ} {i j : ℕ}
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
+    (hi : i < k) (hj : j < k)
+    (hlabel : qOf i = qOf j)
+    (hne : i ≠ j) :
+    False :=
+  (hneq i hi j hj hne) hlabel
+
 /--
 Body-coordinate range-family constructor for `PetalCarrierLabelMapData`.
 
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 9383d2aa..4932fae0 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -997,6 +997,7 @@ Important names:
 ```text
 rangeSuccValue_injOn
 rangeLabel_injOn_of_pairwise_ne
+rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
 petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
 petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
 petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
@@ -1026,6 +1027,13 @@ i < k, j < k, i != j -> qOf i != qOf j
 The helper `rangeLabel_injOn_of_pairwise_ne` converts this to the `Set.InjOn`
 hypothesis required by the core constructors.
 
+The obstruction companion
+`rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index` records the
+negative test: if two distinct in-range indices reuse the same label, the
+pairwise range route closes as `False`.  This is intentionally small; it is a
+diagnostic tool for deciding whether a proposed `qOf` can feed the independent
+carrier family.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 513f262a..7b8cff67 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -499,6 +499,7 @@ Implemented theorem set:
 ```lean
 rangeSuccValue_injOn
 rangeLabel_injOn_of_pairwise_ne
+rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
 petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
 petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
 petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
@@ -537,3 +538,20 @@ i < k, j < k, i != j -> qOf i != qOf j
 
 This is converted into `Set.InjOn qOf ↑(Finset.range k)`, so concrete
 experiments can avoid constructing the subtype-level injectivity proof by hand.
+
+False/obstruction checkpoint:
+
+```lean
+rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
+```
+
+This records the failure mode of the range pairwise route:
+
+```text
+pairwise label separation
+same label at two distinct in-range indices
+  -> False
+```
+
+The theorem does not prove that any proposed family is good.  It proves exactly
+where a candidate `qOf` fails when a duplicate label is found.
````
`````
