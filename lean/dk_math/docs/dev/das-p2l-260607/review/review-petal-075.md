# Git diff / Report / Review

## Add: Collatz.PetalBridge

gch: 21055cb342a6da864539f2c094592c01bd29707b

## Report

Collatz 側の現状を確認し、Petal との窓口を作りました。

追加した窓口:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)

実装内容は薄く安全にしています。`iterateT i n` の自然数値を `oddOrbitLabel n i` として読み、Petal `RangeFamily` の pairwise/collision 補題へ接続しました。

主な追加 API:

```lean
oddOrbitLabel
OddOrbitLabelsPairwiseSeparated
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
```

状況判断としては、現時点では Petal/ABC の `2^k <= supportMass/rad(GN)` には直結しません。Collatz の軌道 label は prime label でも primitive carrier でもないためです。ただし、軌道片が「分離している」か「衝突している」かを Petal RangeFamily の言葉で観測する窓口はできました。Collatz では衝突は失敗ではなく、merge / fold / cycle candidate の情報になります。

統合も済みです。

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
lake build DkMath
```

全て成功。既存の `ZsigmondyCyclotomicResearch` などの `sorry` warning は出ますが、今回追加した Collatz/PetalBridge には `sorry` はありません。

## Review

うむ。**初手としては非常に良い。かなり安全で、しかも後で効く橋** になっている。

今回の `DkMath.Collatz.PetalBridge` は、Collatz 予想そのものを進めたというより、**Collatz 軌道を Petal の RangeFamily 言語で観測できるようにした** という段階じゃ。追加内容は、加速 Collatz 軌道 `iterateT i n` の自然数値を `oddOrbitLabel n i` として読み、軌道片の label 分離と衝突を Petal 側の pairwise / obstruction 補題へ接続するものになっている。

## 1. 今回できたこと

Collatz 側にこういう観測窓ができた。

```text id="pp1u71"
accelerated Collatz orbit segment
  -> oddOrbitLabel n i
  -> range-indexed labels
  -> pairwise separated or collision
```

Lean で追加された主語はこれ。

```lean id="b0u27f"
oddOrbitLabel
OddOrbitLabelsPairwiseSeparated
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
```

特に大事なのは、

```lean id="e1lg9j"
oddOrbitLabel n i = (iterateT i n).1
```

という読みじゃ。

つまり、`OddNat` の証明部分は一旦忘れて、加速 Collatz の i 番目の odd state を自然数 label として Petal に渡す。

## 2. Petal 的には何が見えるか

Petal RangeFamily では、すでに

```text id="ix6m24"
i < k, j < k, i != j -> qOf i != qOf j
```

という pairwise label separation から `Set.InjOn` を作り、逆に同じ label が出たら独立 route が `False` になる構造があった。

今回 Collatz 側では、

```text id="xpa5vi"
qOf i := oddOrbitLabel n i
```

として読む。

すると、

```text id="dw1yaq"
最初の k ステップの odd state が全部違う
```

という Collatz 的条件が、そのまま Petal の range-label separation になる。

一方で、

```text id="ufohdq"
oddOrbitLabel n i = oddOrbitLabel n j
```

が見つかると、

```text id="dzaavi"
iterateT i n = iterateT j n
```

まで出る。

これはかなり重要じゃ。単なる label 衝突ではなく、**加速 Collatz 状態そのものの衝突** になる。

## 3. Collatz では「衝突」は失敗ではない

ここが Petal/ABC と Collatz の読み違いじゃ。

Petal/ABC では、同じ label の再利用は、

```text id="zmby26"
独立 carrier family としては数えられない
```

という obstruction になる。

しかし Collatz では、同じ odd state が再出現することは、

```text id="umyqi9"
merge
fold
cycle candidate
```

の情報になる。

つまり同じ出来事が、二通りに読める。

```text id="m8zf2m"
Petal route:
  independent counting obstruction

Collatz route:
  dynamical collision signal
```

この二重読みが今回の価値じゃ。

## 4. まだできていないこと

ここは重要。

今回の橋は、まだ

```text id="v0qxzz"
2^k <= supportMass(GN)
2^k <= rad(GN)
```

には直結しない。

理由は明確で、Collatz の `oddOrbitLabel n i` はただの odd state label であって、

```text id="w1wae8"
prime label
primitive carrier
Zsigmondy witness
GN divisor
```

ではないからじゃ。

報告にもある通り、Collatz の軌道 label は prime label でも primitive carrier でもないため、Petal/ABC の radical 下界にはまだ直接入れない。今回できたのは、あくまで **軌道片が分離しているか、衝突しているかを Petal RangeFamily の言葉で観測する窓口** じゃ。

これは安全な判断じゃ。ここで無理に ABCBridge へ入れないのが良い。

## 5. Collatz 側の意味

現在 Collatz 側で強いのは、

```text id="so1ssl"
odd state
2-adic height
accelerated transition
orbit segment
block-shift invariance
```

のあたり。

今回の `PetalBridge` は、その中の

```text id="yi78xv"
accelerated transition / orbit segment
```

を Petal 側へ接続した。

今後はここに、

```text id="juzcyv"
2-adic height = Petal address movement
shift invariance = address conservation
collision = fold/cycle diagnostic
```

を重ねられる可能性がある。

相対多角数が Collatz 観点を持っていた、という過去の直感とも合う。Collatz は「増やして、2 の高さで剥がして、odd core に戻す」力学だから、Petal 的には **花弁を伸ばして、単位核で折り返す** ように見える。

## 6. トロミノ論法での位置づけ

今回の橋をトロミノ論法で読むとこうじゃ。

```text id="s7omcq"
Core:
  accelerated Collatz orbit segment

Beam:
  oddOrbitLabel n i として並ぶ各時刻の label

False:
  pairwise separated と仮定したのに同じ label が出る

Gap:
  その衝突が示す merge / fold / cycle 情報

Big:
  Collatz 軌道全体の構造理解
```

つまり、今回の `False` は単なる敗北ではない。

```text id="nhglvv"
独立軌道片として読む道は閉じる。
だが、Collatz dynamics としては合流構造が見えた。
```

という診断になる。

## 7. 次の一手

報告書の候補にもある通り、次の安全な作業はこの順番がよい。

```text id="fr8jta"
1. Collatz orbit segment を range family として明示定義する
2. separated / collision の case split を作る
3. v2_shift_invariant を Petal address / residue 読みに接続する
4. Collatz label を prime label へ変換する層を別途検討する
```

特に次に欲しいのは、たぶんこれ。

```lean id="ztow7p"
def CollatzOrbitSegment (n : OddNat) (k : ℕ) := Finset.range k

def CollatzOrbitSeparatedOrCollision ...
```

あるいは theorem として、

```text id="n1mjza"
最初の k label が pairwise separated
または
異なる i,j < k で collision がある
```

という有限 case split。

これは classical decidability を使えばかなり通しやすいはずじゃ。

## 8. 総括

今回の初手はこうまとめられる。

```text id="kw8c3a"
Collatz accelerated orbit
  -> oddOrbitLabel
  -> Petal RangeFamily の separation/collision 言語へ接続
```

できたことは、

```text id="hitxlq"
Collatz 軌道片を Petal の range label として観測できるようになった
```

できていないことは、

```text id="i1nb2k"
Collatz label を prime carrier として ABC/rad 下界へ渡すこと
```

じゃ。

しかし初手としてはかなり良い。
なぜなら、Collatz で最初に見たいのは「素数 support」ではなく、まず

```text id="vx3ja7"
軌道が分離して進むのか
途中で合流・折り返すのか
```

だからじゃ。

うむ。
これは **Collatz を Petal の花弁軌道として観測するための最初の窓** が開いた段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/Collatz2K26.lean b/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
index 659217d0..3c08ee49 100644
--- a/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
+++ b/lean/dk_math/DkMath/Collatz/Collatz2K26.lean
@@ -8,6 +8,7 @@ import DkMath.Collatz.Basic
 import DkMath.Collatz.V2
 import DkMath.Collatz.Accelerated
 import DkMath.Collatz.Shift
+import DkMath.Collatz.PetalBridge
 
 #print "file: DkMath.Collatz.Collatz2K26"
 
@@ -26,5 +27,6 @@ Structure:
   - V2.lean:          2-adic valuation v₂ and foundational lemmas
   - Accelerated.lean: Accelerated map T, observation s, and sequence sums
   - Shift.lean:       Block shift, petal conservation (v₂ invariance)
+  - PetalBridge.lean: Petal range-family window for orbit label separation/collision
   - This file:        Integration and higher-level properties
 -/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
new file mode 100644
index 00000000..4a931b65
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -0,0 +1,109 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.Accelerated
+import DkMath.Petal.RangeFamily
+
+#print "file: DkMath.Collatz.PetalBridge"
+
+/-!
+# Collatz Petal Bridge
+
+This file is a small observation window between the accelerated Collatz
+dynamics and the Petal range-family API.
+
+The bridge is intentionally thin.  It does not claim any Collatz convergence
+or nontrivial cycle theorem.  It only fixes the common language:
+
+```text
+accelerated Collatz orbit segment
+  -> range-indexed labels
+  -> either pairwise separated, or a collision closes that route as False
+```
+
+For Petal/ABC routes, a repeated label means that a proposed independent
+range-family cannot be counted as `k` independent carriers.  For Collatz
+dynamics, the same collision is not merely a failure: it is the observable
+shape of a merge, fold, or cycle candidate.
+-/
+
+namespace DkMath.Collatz
+
+/--
+The natural-number label of the `i`-th accelerated Collatz odd state.
+
+This is the Collatz-facing candidate for a Petal `qOf i` label.  It deliberately
+forgets the proof that the state is odd and keeps only the observed address
+value.
+-/
+noncomputable def oddOrbitLabel (n : OddNat) (i : ℕ) : ℕ :=
+  (iterateT i n).1
+
+/--
+The first `k` accelerated Collatz odd-state labels are pairwise separated.
+
+This is the Collatz-specific spelling of the RangeFamily pairwise condition:
+different in-range times have different observed odd states.
+-/
+def OddOrbitLabelsPairwiseSeparated (n : OddNat) (k : ℕ) : Prop :=
+  ∀ i, i < k → ∀ j, j < k → i ≠ j → oddOrbitLabel n i ≠ oddOrbitLabel n j
+
+/--
+Pairwise separated Collatz orbit labels give the Petal range-label injectivity
+condition.
+-/
+theorem oddOrbitLabel_injOn_of_pairwiseSeparated
+    (n : OddNat) {k : ℕ}
+    (hsep : OddOrbitLabelsPairwiseSeparated n k) :
+    Set.InjOn (oddOrbitLabel n) ↑(Finset.range k) :=
+  DkMath.Petal.rangeLabel_injOn_of_pairwise_ne hsep
+
+/--
+Equal Collatz odd-state labels identify the accelerated states themselves.
+
+Since `OddNat` is a subtype of natural numbers, equality of the stored natural
+value is equality of the subtype state.
+-/
+theorem iterateT_eq_of_oddOrbitLabel_eq
+    {n : OddNat} {i j : ℕ}
+    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
+    iterateT i n = iterateT j n := by
+  apply Subtype.ext
+  exact hlabel
+
+/--
+False/obstruction window for Collatz orbit labels.
+
+If an orbit segment is assumed pairwise separated but two distinct in-range
+times have the same odd-state label, the independent Petal range route closes
+as `False`.
+-/
+theorem oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
+    {n : OddNat} {k i j : ℕ}
+    (hsep : OddOrbitLabelsPairwiseSeparated n k)
+    (hi : i < k) (hj : j < k)
+    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j)
+    (hne : i ≠ j) :
+    False :=
+  DkMath.Petal.rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
+    hsep hi hj hlabel hne
+
+/--
+Collision observation form.
+
+When two different in-range Collatz times have the same label, they are the
+same accelerated odd state.  This theorem does not call that good or bad:
+Petal/ABC reads it as an independence obstruction, while Collatz reads it as a
+merge/fold/cycle candidate.
+-/
+theorem same_iterateT_of_oddOrbitLabel_collision
+    {n : OddNat} {k i j : ℕ}
+    (_hi : i < k) (_hj : j < k)
+    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
+    iterateT i n = iterateT j n :=
+  iterateT_eq_of_oddOrbitLabel_eq hlabel
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
new file mode 100644
index 00000000..ea2f2dea
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -0,0 +1,164 @@
+# Collatz Petal Bridge Status
+
+This note records the current contact point between the accelerated Collatz
+formalization and the Petal range-family route.
+
+## Current Collatz Surface
+
+Implemented Collatz modules already provide:
+
+```text
+DkMath.Collatz.Basic
+  C
+  OddNat
+  threeNPlusOne
+
+DkMath.Collatz.V2
+  v2
+  v2_3n_plus_1_ge_1
+  v2_shift_invariant support lemmas
+
+DkMath.Collatz.Accelerated
+  s n = v2 (3n + 1)
+  T n = (3n + 1) / 2^(v2 (3n + 1))
+  iterateT
+  sumS
+  driftReal
+
+DkMath.Collatz.Shift
+  shift
+  v2_shift_invariant
+```
+
+This means the implemented Collatz side is currently strongest around:
+
+```text
+odd state
+2-adic height
+accelerated transition
+orbit segment
+block-shift invariance
+```
+
+## Petal Contact Point
+
+`DkMath.Petal.RangeFamily` recently introduced a range-indexed observation
+layer:
+
+```text
+I = Finset.range k
+mOf i = i + 1
+qOf i = selected label at index i
+```
+
+It now has both sides of the test:
+
+```text
+pairwise label separation
+  -> Set.InjOn qOf ↑(Finset.range k)
+
+same label at two distinct in-range indices
+  -> False
+```
+
+This is a natural match for Collatz orbit segments.
+
+## New Window
+
+The bridge file is:
+
+```text
+DkMath.Collatz.PetalBridge
+```
+
+It defines:
+
+```lean
+oddOrbitLabel
+OddOrbitLabelsPairwiseSeparated
+```
+
+where:
+
+```text
+oddOrbitLabel n i = the natural value of iterateT i n
+```
+
+The first theorem set is deliberately thin:
+
+```lean
+oddOrbitLabel_injOn_of_pairwiseSeparated
+iterateT_eq_of_oddOrbitLabel_eq
+oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
+same_iterateT_of_oddOrbitLabel_collision
+```
+
+## Interpretation
+
+For Petal / ABC:
+
+```text
+pairwise separated orbit labels
+  -> independent range-family labels are available
+
+duplicate label
+  -> the independent range-family route closes as False
+```
+
+For Collatz dynamics:
+
+```text
+duplicate label
+  -> same accelerated odd state
+  -> merge / fold / cycle candidate
+```
+
+So the same event has two readings:
+
+```text
+Petal route:
+  obstruction to independent counting
+
+Collatz route:
+  dynamical collision signal
+```
+
+## Does This Change the Current Petal Situation?
+
+Not yet at the level of `supportMass` or `rad` lower bounds.
+
+The new bridge does not prove that Collatz orbit labels are prime labels,
+primitive carriers, or Zsigmondy witnesses.  Therefore it does not immediately
+feed the `2^k <= supportMass/rad(GN)` endpoint.
+
+What it changes is the diagnostic layer:
+
+```text
+Collatz orbit segment
+  -> Petal range-label separation test
+  -> either separated segment or collision obstruction
+```
+
+This gives a clean place to attach future hypotheses:
+
+```text
+orbit labels are usable carrier labels
+orbit labels are mapped to prime labels
+orbit collision implies a specific fold/cycle condition
+2-adic height controls Petal address movement
+```
+
+## Next Candidate Work
+
+The next safe steps are:
+
+```text
+1. Define a Collatz orbit segment as a finite range family.
+2. Add a collision-vs-separated predicate split.
+3. Connect v2_shift_invariant to a Petal address/residue reading.
+4. Only after that, test whether Collatz labels can feed ABC support/rad.
+```
+
+The main caution is that Collatz state labels are not prime labels.  Any bridge
+to `ABCBridge` must insert an additional label transform or carrier witness
+layer before using the Petal radical lower-bound theorems.
diff --git a/lean/dk_math/INDEX.md b/lean/dk_math/INDEX.md
index ef5f6b5b..698f89c1 100644
--- a/lean/dk_math/INDEX.md
+++ b/lean/dk_math/INDEX.md
@@ -71,6 +71,7 @@
 ### 3.3 コラッツ
 
 - `DkMath.Collatz.Collatz2K26`
+- `DkMath.Collatz.PetalBridge`
 
 ### 3.4 宇宙式（Cosmic Formula）
 
@@ -470,7 +471,7 @@ graph TD
 # IV. 独立柱（SilverRatio / Collatz / UnitCycle / DHNT）
 
 - SilverRatio / UniqueRepresentation は **代数的独立柱**。
-- Collatz は **動的離散系の実験塔**。
+- Collatz は **動的離散系の実験塔**。PetalBridge により、加速軌道の label 分離と collision を Petal RangeFamily の窓口で読める。
 - UnitCycle / DHNT は **宇宙式と接続可能な補助構造**。
 
 ---
diff --git a/lean/dk_math/README.md b/lean/dk_math/README.md
index 0f6fcc42..3a4272aa 100644
--- a/lean/dk_math/README.md
+++ b/lean/dk_math/README.md
@@ -121,6 +121,7 @@ presented by D. and Wise Wolf
 - 実装報告: [IMPLEMENTATION_REPORT_20260130.md](./DkMath/Collatz/docs/IMPLEMENTATION_REPORT_20260130.md)
 - 補助補題完成報告: [AUXILIARY_LEMMA_COMPLETION_20260130.md](./DkMath/Collatz/docs/AUXILIARY_LEMMA_COMPLETION_20260130.md)
 - sorry 解消進捗: [SORRY_CLEANUP_PROGRESS_20260130.md](./DkMath/Collatz/docs/SORRY_CLEANUP_PROGRESS_20260130.md)
+- Petal 接続窓口: [Collatz-PetalBridge-Status.md](./DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
 
 ---
 
````
`````
