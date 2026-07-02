# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 5eda8db0ceff58786bbd7aded5e0c58964b8dbfb

## Report

Checkpoint 121 完了です。

`DkMath.Collatz.PetalBridge` に、selected pressure witness から delayed budget へつなぐ薄い橋を追加しました。

```text
SourceContinuationPressureOnRange n k 2 1
  -> positive depth-two continuation mass
  -> delayed budget with tail 7 mod 8 remainder
```

追加した主な theorem は以下です。

```lean
exists_towerEntryDepth_of_pressureDepthCount_pos
exists_towerEntryDepth_of_outrunsMoreThanHalf
depthTwoPressureRange_positive_and_budget
exists_depth_two_budget_of_pressureOnRange_two_one
```

Python 実験も追加しました。実軌道 window 上で pressure witness と L1..L5 remainder を同時に観測します。

- [orbit_pressure_remainder_scan.py](/python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py)
- [orbit_pressure_remainder_scan.csv](/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv)
- [orbit_pressure_remainder_scan.md](/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md)

デフォルト観測では、奇数 `n <= 999` の 500 行中、pressure witness あり 237 行、L5 remainder あり 18 行でした。pressure witness は比較的よく出る一方、deep all-ones remainder はかなり薄い、という次の仮説に使えるデータです。

Docs/report も同期済みです。

- [Collatz-SelectedWitnessBudget-121.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md)
- [report-petal-121.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-121.md)

検証済みです。

```text
python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py --max-n 999 --steps 64 --r-start 2 --depth-len 8
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 121 files>
```

`PetalBridge.lean` は no-sorry。既知の無関係な `ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は残っています。

## Review

## 1. 状況分析

checkpoint `121` は、かなり良い転換点じゃ。

前回までで、

```text
pressure / outruns-heavy
  -> positive pressure-depth count
  -> selected local depth witness
  -> positive source continuation mass
```

までは閉じていた。

今回 `121` では、その selected witness を、初めて **delayed budget surface** に接続した。

```text
SourceContinuationPressureOnRange n k 2 1
  -> positive depth-two continuation mass
  -> delayed budget with tail 7 mod 8 remainder
```

追加された主な theorem は、

```lean
exists_towerEntryDepth_of_pressureDepthCount_pos
exists_towerEntryDepth_of_outrunsMoreThanHalf
depthTwoPressureRange_positive_and_budget
exists_depth_two_budget_of_pressureOnRange_two_one
```

じゃ。報告でも、selected pressure witness から delayed budget へつなぐ薄い橋を追加し、Python 側では pressure witness と L1..L5 remainder を同時観測した、と整理されている。

ここで重要なのは、ついに

```text
witness exists
```

から、

```text
budget opportunity exists
```

へ進んだことじゃ。

## 2. 今回の核心

今回の核心はこの theorem じゃ。

```lean
theorem depthTwoPressureRange_positive_and_budget
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        sumS n ((k + 1) + 1) +
          orbitWindowResidueCountMod8EqSevenTail n k
```

これは、まさに会計式になっている。

```text
正の continuation mass がある
```

だけではなく、

```text
その mass は sumS へ課金される分と、tail 7 mod 8 remainder に残る分として扱える
```

と言っている。

つまり、

```text
selected witness
  -> positive mass
  -> delayed budget
  -> explicit remainder
```

が theorem surface になった。

これはかなり大きい。

## 3. レビュー

## 3.1. alias 名が良い

今回追加された、

```lean
exists_towerEntryDepth_of_pressureDepthCount_pos
exists_towerEntryDepth_of_outrunsMoreThanHalf
```

は、ほぼ既存 theorem の caller-facing alias じゃ。

しかし、これは重要。

以前の名前は、

```lean
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
```

で、正確ではあるが「tower entry」としての意味が見えにくかった。

今回の名前だと、

```text
pressure count が正
  -> tower に入れる depth が存在
```

と読める。

これは後続の証明でかなり効く。
この段階では、数学的内容だけでなく **証明の読みやすさ** が重要になってきている。

## 3.2. one-witness に留めたのが正しい

今回の docs でも明示されているが、この theorem は一個 witness の theorem じゃ。

```text
many pressure witnesses
  -> many independent delayed budgets
```

はまだ言っていない。

ここを踏み越えなかったのが良い。

pressure depth count が大きいからといって、その数だけ独立に budget を足し合わせられるとは限らない。
同じ orbit-window mass を複数 depth で重複して数えている可能性がある。

したがって今回の到達点は、

```text
一個の selected witness は budget opportunity になる
```

まで。

これは安全で、Lean 的にも健全じゃ。

## 3.3. Python 観測が良い方向を示している

今回の Python 実験では、奇数 `n <= 999` の 500 行について、

```text
pressure witness あり:
  237 行

L5 remainder あり:
  18 行

max pressure depth count:
  6

max L5 remainder:
  3
```

という結果が出ている。

この観測はかなり示唆的じゃ。

```text
pressure witness はよく出る。
しかし deep all-ones remainder はかなり薄い。
```

つまり、tower の方向性は良さそうに見える。

ただしこれは証明ではない。
使うべき読みは、

```text
次に狙う theorem を選ぶための探索灯
```

じゃ。

## 4. 数学的解説

今の構造は、こうなっている。

まず pressure 側。

```text
SourceContinuationPressureOnRange n k 2 1
```

は、depth `2` の一点幅 pressure を表す。

そこから、

```text
MoreThanHalf continuation retention at depth 2
```

を得て、

```text
0 < continuation mass at depth 2
```

を得る。

次に delayed budget 側へ行く。

```text
(k + 1) + continuationMass
  <= sumS n (k + 2) + tail 7 mod 8 remainder
```

ここで `tail 7 mod 8 remainder` は、以前から tower で追っていた level 1 remainder じゃ。

つまり、pressure witness は即座にすべて `sumS` へ落ちるのではない。

```text
falling contribution:
  sumS 側

continuing contribution:
  tail 7 mod 8 remainder 側
```

として保存される。

この「残りを明示して逃がさない」ことが、今回の重要点じゃ。

## 5. 今回閉じたもの

今回閉じたものは次の四つ。

```text
1. pressureDepthCount positive から tower-entry depth witness を取る alias

2. outruns-heavy から tower-entry depth witness を取る alias

3. depth-two one-range pressure から positive continuation mass を得る bridge

4. その positive mass を delayed budget with tail 7 mod 8 remainder に接続する bridge
```

さらに Python 側で、

```text
pressure witness
L1..L5 remainder
falling colors
sumS
```

を同時に観測する surface が追加された。

これにより、形式化と実験がかなり噛み合ってきた。

## 6. まだ閉じていないもの

未完の本命はこれじゃ。

```text
many pressure witnesses
  -> many usable budget opportunities
```

ただし、ここには危険がある。

```text
many witnesses
```

と、

```text
many independent budgets
```

は違う。

次に必要なのは、次のどれかじゃ。

```text
1. two pressure witnesses exist, but budget independence は主張しない

2. selected depths が address-separated なら independent budget できる

3. target residue channels が disjoint なら budget を足せる

4. one selected witness を反復的に使うだけで十分な obstruction が出る
```

安全な順番は、まず 1。
次に 2 または 3。
最後に multi-budget theorem じゃ。

## 7. 次の指示

## 7.1. まず two witnesses existence を作る

次は、報告にもある通り、

```lean
exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

が良い。

ただし、これは **二つの witness が存在する** だけに留める。

```lean
theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
    (n : OddNat) (k r len : ℕ)
    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
    ∃ j₁ j₂,
      j₁ < len ∧
      j₂ < len ∧
      j₁ ≠ j₂ ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j₁))
        (orbitWindowRetentionMassPow2 n k (r + j₁)) ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j₂))
        (orbitWindowRetentionMassPow2 n k (r + j₂)) := by
  -- countP >= 2 から distinct witnesses
  sorry
```

これはまだ budget を足さない。
witness extraction だけじゃ。

## 7.2. selected witness package を作る

次に、同じ情報を何度も持ち回らなくて済むように、構造体か predicate を用意するとよい。

軽量なら predicate。

```lean
def IsSourcePressureDepth
    (n : OddNat) (k r : ℕ) (j : ℕ) : Prop :=
  MoreThanHalf
    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
    (orbitWindowRetentionMassPow2 n k (r + j))
```

次に positive mass も付ける。

```lean
theorem positive_mass_of_isSourcePressureDepth
    (n : OddNat) (k r j : ℕ)
    (h : IsSourcePressureDepth n k r j) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  unfold IsSourcePressureDepth at h
  exact sourceContinuationMass_pos_of_localPressure n k (r + j) h
```

これで後続が読みやすくなる。

## 7.3. budget に使える witness を定義する

depth `2` 専用 bridge はある。
将来的には、budget-ready な witness を分けたい。

```lean
def IsDepthTwoBudgetWitness
    (n : OddNat) (k : ℕ) : Prop :=
  SourceContinuationPressureOnRange n k 2 1
```

または、より直接に、

```lean
def HasDepthTwoDelayedBudget
    (n : OddNat) (k : ℕ) : Prop :=
  0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k
```

そして、

```lean
theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    HasDepthTwoDelayedBudget n k := by
  unfold HasDepthTwoDelayedBudget
  exact depthTwoPressureRange_positive_and_budget n k h
```

これは、後で multi-budget を作る時の部品になる。

## 8. 一歩先ゆく推論

次に本当に欲しいのは、次の形じゃ。

```text
pressureDepthCount large
  -> selected witnesses exist
  -> selected witnesses are separated enough
  -> sum of delayed budgets is valid
```

だが、いきなり最後へ行くと危ない。

まずは二つの witness を得る。
次に、それらが同じ target residue channel を使ってしまうかを Python で観測する。

具体的には、二つの selected depth `j₁`, `j₂` に対して、

```text
depth r+j₁ の continuation mass が参照する label 集合
depth r+j₂ の continuation mass が参照する label 集合
```

がどれだけ重なるかを見る。

重なるなら、multi-budget は address-separated 条件が必要。
重ならないパターンが多いなら、disjoint channel theorem を狙える。

つまり次は、

```text
witness count
```

ではなく、

```text
witness overlap
```

を見る段階じゃ。

## 9. さらに次の一手

Python 側の次実験として、selected pressure depths の overlap を直接観測したい。

今の `orbit_pressure_remainder_scan.py` は、

```text
pressure_depth_count
first_pressure_depth
continuation_mass_at_first_pressure
L1..L5 remainder
```

を出している。

次はこれを追加する。

```text
selected_depths
continuation_label_indices_per_depth
pairwise_overlap_count
max_pairwise_overlap
has_disjoint_pair
```

観測したい問いはこれ。

```text
pressure_depth_count >= 2 のとき、
二つの selected depths は disjoint な continuation labels を持つことがあるか？
常に重なるのか？
どの条件なら分離するのか？
```

ここが分かれば、Lean で次に定義すべきものが決まる。

```text
SelectedDepthsAddressSeparated
```

なのか、

```text
DisjointTowerTargets
```

なのか、

```text
PrefixNestedSelectedDepths
```

なのかが見える。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source pressure depth predicate

```lean
def IsSourcePressureDepth
    (n : OddNat) (k r : ℕ) (j : ℕ) : Prop :=
  MoreThanHalf
    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
    (orbitWindowRetentionMassPow2 n k (r + j))
```

## 実験 B: pressure range から predicate

```lean
theorem isSourcePressureDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    IsSourcePressureDepth n k r j := by
  unfold IsSourcePressureDepth
  exact sourcePressureAtDepth_of_pressureOnRange n k r len j h hj
```

## 実験 C: predicate から positive mass

```lean
theorem positive_sourceContinuationMass_of_isSourcePressureDepth
    (n : OddNat) (k r j : ℕ)
    (h : IsSourcePressureDepth n k r j) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  unfold IsSourcePressureDepth at h
  exact sourceContinuationMass_pos_of_localPressure n k (r + j) h
```

## 実験 D: count positive から predicate witness

```lean
theorem exists_isSourcePressureDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧ IsSourcePressureDepth n k r j := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, hpressure⟩
```

## 実験 E: count positive から pressure witness with positive mass

```lean
theorem exists_isSourcePressureDepth_with_positive_mass
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      IsSourcePressureDepth n k r j ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_isSourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, hpressure,
    positive_sourceContinuationMass_of_isSourcePressureDepth n k r j hpressure⟩
```

## 実験 F: depth-two budget predicate

```lean
def HasDepthTwoDelayedBudget
    (n : OddNat) (k : ℕ) : Prop :=
  0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k
```

## 実験 G: pressure range から depth-two budget predicate

```lean
theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    HasDepthTwoDelayedBudget n k := by
  unfold HasDepthTwoDelayedBudget
  exact depthTwoPressureRange_positive_and_budget n k h
```

## 実験 H: two witnesses existence

```lean
theorem exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
    (n : OddNat) (k r len : ℕ)
    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
    ∃ j₁ j₂,
      j₁ < len ∧
      j₂ < len ∧
      j₁ ≠ j₂ ∧
      IsSourcePressureDepth n k r j₁ ∧
      IsSourcePressureDepth n k r j₂ := by
  -- countP >= 2 から distinct witnesses
  -- budget independence は主張しない
  sorry
```

これは次 checkpoint の本命候補じゃ。

## 11. 次コミットの推奨順

```text
1. IsSourcePressureDepth を追加

2. isSourcePressureDepth_of_pressureOnRange を追加

3. positive_sourceContinuationMass_of_isSourcePressureDepth を追加

4. exists_isSourcePressureDepth_of_pressureDepthCount_pos を追加

5. exists_isSourcePressureDepth_with_positive_mass を追加

6. HasDepthTwoDelayedBudget を追加

7. hasDepthTwoDelayedBudget_of_pressureOnRange_two_one を追加

8. exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount を試す

9. Python 側で selected-depth overlap scan を追加

10. docs:
    SelectedWitnessBudget から SelectedPressureDepths / OverlapScan へ接続
```

## 12. 総括

checkpoint `121` は、かなり良い。

これで初めて、

```text
selected pressure witness
  -> positive continuation mass
  -> delayed budget with explicit remainder
```

が直接つながった。

Python 観測でも、

```text
pressure witness は比較的よく出る
deep all-ones remainder はかなり薄い
```

という方向性が見えた。

次は、複数 witness を扱う前に、

```text
selected pressure depth
```

という概念を明示し、その witness がどの mass / budget に入るかを整理する段階じゃ。

そして Python では、selected depths の overlap を見る。
Lean では、まず two witnesses existence を安全に作る。

ここを越えると、いよいよ

```text
pressure-heavy range
  -> non-overlapping selected tower entries
  -> summed delayed budget
```

という本当の有限会計に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index ff463c2d..134338ee 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -6412,6 +6412,32 @@ theorem exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
     sourcePressureDepthCount_pos_of_outrunsMoreThanHalf n k r len h
   exact exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
 
+/--
+Tower-entry naming wrapper for positive pressure-depth count.
+
+The theorem only selects a positive local source continuation mass.  It does
+not assert that different selected depths are independent budget carriers.
+-/
+theorem exists_towerEntryDepth_of_pressureDepthCount_pos
+    (n : OddNat) (k r len : ℕ)
+    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
+    ∃ j, j < len ∧
+      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
+  exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
+
+/--
+Tower-entry naming wrapper for source outruns-heavy pressure.
+
+This is the caller-facing name for moving from a pressure-heavy range to one
+selected local tower-entry opportunity.
+-/
+theorem exists_towerEntryDepth_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    ∃ j, j < len ∧
+      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
+  exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf n k r len h
+
 /--
 Extract local depth-two source pressure from the one-depth range pressure
 profile beginning at depth `2`.
@@ -6453,6 +6479,37 @@ theorem sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
         orbitWindowResidueCountMod8EqSevenTail n k :=
   sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder n k
 
+/--
+Depth-two one-range pressure gives both positive continuation mass and the
+depth-two delayed budget inequality.
+
+This is the first direct "selected witness to delayed budget" bridge.
+-/
+theorem depthTwoPressureRange_positive_and_budget
+    (n : OddNat) (k : ℕ)
+    (h : SourceContinuationPressureOnRange n k 2 1) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
+      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+        sumS n ((k + 1) + 1) +
+          orbitWindowResidueCountMod8EqSevenTail n k := by
+  constructor
+  · exact sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one n k h
+  · exact sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder n k
+      (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
+
+/--
+Alias spelling for the same depth-two bridge, emphasizing existence of a
+budget opportunity rather than the pressure-profile input form.
+-/
+theorem exists_depth_two_budget_of_pressureOnRange_two_one
+    (n : OddNat) (k : ℕ)
+    (h : SourceContinuationPressureOnRange n k 2 1) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
+      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+        sumS n ((k + 1) + 1) +
+          orbitWindowResidueCountMod8EqSevenTail n k :=
+  depthTwoPressureRange_positive_and_budget n k h
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index eb5fe065..0760fbe4 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -155,6 +155,7 @@ docs/Collatz-Level2Remainder-117.md
 docs/Collatz-Level3PressureEntrance-118.md
 docs/Collatz-Level4GenericPressure-119.md
 docs/Collatz-Level5AndModScan-120.md
+docs/Collatz-SelectedWitnessBudget-121.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 80429a61..e7ce0742 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1225,3 +1225,40 @@ python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
 The scan confirms the same recovery/continuation law from `mod 16` through
 `mod 1024`, which suggests that future checkpoints should prefer the generic
 power-of-two residue theorem when readability permits it.
+
+## Selected Witness To Budget
+
+Checkpoint 121 connects the selected witness layer to the first delayed-budget
+surface.
+
+The depth-two one-range bridge is:
+
+```lean
+depthTwoPressureRange_positive_and_budget
+exists_depth_two_budget_of_pressureOnRange_two_one
+```
+
+It packages:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> positive source continuation mass at depth 2
+  -> delayed budget with the tail 7 mod 8 remainder
+```
+
+The caller-facing tower-entry aliases are:
+
+```lean
+exists_towerEntryDepth_of_pressureDepthCount_pos
+exists_towerEntryDepth_of_outrunsMoreThanHalf
+```
+
+The Python observation script:
+
+```text
+python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
+```
+
+records pressure witnesses and L1..L5 delayed remainders on concrete orbit
+windows.  Its results are experimental and should be used to choose the next
+formal theorem, not as proof.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 84353e2a..d63d9df4 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -1500,3 +1500,58 @@ python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
 ```
 
 confirms the same recovery/continuation residue law through `mod 1024`.
+
+## Checkpoint 121: Selected Witness To Delayed Budget
+
+Checkpoint 121 connects the one-witness pressure layer to a concrete delayed
+budget theorem.
+
+New caller-facing tower-entry aliases:
+
+```lean
+exists_towerEntryDepth_of_pressureDepthCount_pos
+exists_towerEntryDepth_of_outrunsMoreThanHalf
+```
+
+New depth-two budget package:
+
+```lean
+depthTwoPressureRange_positive_and_budget
+exists_depth_two_budget_of_pressureOnRange_two_one
+```
+
+Meaning:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> 0 < orbitWindowContinuationSiblingMassPow2 n k 2
+  -> (k + 1) + continuationMass <= sumS n ((k + 1) + 1)
+       + tail 7 mod 8 remainder
+```
+
+This is still a one-witness theorem.  It does not claim that multiple selected
+pressure depths can be counted as independent delayed-budget carriers.
+
+New Python observation script:
+
+```text
+python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
+```
+
+Default scan:
+
+```text
+odd n <= 999, steps = 64, depths 2..9
+```
+
+Observed summary:
+
+```text
+rows: 500
+rows with pressure witness: 237
+rows with L5 remainder: 18
+max pressure depth count: 6
+max L5 remainder: 3
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md
new file mode 100644
index 00000000..e18b4bd8
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md
@@ -0,0 +1,152 @@
+# Collatz Selected Witness Budget 121
+
+Checkpoint 121 closes the first direct bridge from a selected pressure witness
+to a delayed-budget opportunity.
+
+The important restriction is that this is still a one-witness theorem.  It does
+not claim independent accounting for multiple selected depths.
+
+## Lean Bridge
+
+Checkpoint 120 gave:
+
+```lean
+exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+```
+
+Checkpoint 121 adds caller-facing names:
+
+```lean
+exists_towerEntryDepth_of_pressureDepthCount_pos
+exists_towerEntryDepth_of_outrunsMoreThanHalf
+```
+
+Meaning:
+
+```text
+positive pressure-depth count
+  -> selected local tower-entry depth
+  -> positive source continuation mass
+```
+
+## Depth-Two Budget Package
+
+The existing depth-two budget theorem was:
+
+```lean
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+```
+
+Checkpoint 121 packages it with positive mass:
+
+```lean
+depthTwoPressureRange_positive_and_budget
+exists_depth_two_budget_of_pressureOnRange_two_one
+```
+
+The theorem reads:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> 0 < orbitWindowContinuationSiblingMassPow2 n k 2
+  -> (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2
+       <= sumS n ((k + 1) + 1)
+          + orbitWindowResidueCountMod8EqSevenTail n k
+```
+
+This is the first stable form of:
+
+```text
+selected pressure witness
+  -> positive continuation mass
+  -> delayed budget with explicit remainder
+```
+
+## Python Orbit Observation
+
+New script:
+
+```text
+python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
+```
+
+Default command:
+
+```text
+python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+```
+
+The output records:
+
+```text
+n
+steps
+sumS
+pressure_depth_count
+first_pressure_depth
+continuation_mass_at_first_pressure
+retention_mass_at_first_pressure
+L1..L5 remainders
+L1..L5 falling colors
+```
+
+Default observed summary:
+
+```text
+rows: 500
+rows with pressure witness: 237
+rows with L5 remainder: 18
+max pressure depth count: 6
+max L5 remainder: 3
+```
+
+## Reading
+
+The scan shows that pressure witnesses are common in finite windows, while deep
+all-ones remainders are much rarer.
+
+This supports the next formal split:
+
+```text
+pressure witness exists
+  -> one delayed budget opportunity
+
+many pressure witnesses
+  -> requires a separate no-overlap / address-separated condition
+```
+
+The second statement is not yet proved and should not be assumed.
+
+## Next Work
+
+The next useful formal object is likely a selected-depth package:
+
+```text
+selected pressure depths as a finite list or Finset
+```
+
+but it should initially expose only witness facts, not independent budget
+claims.
+
+Safer immediate theorem:
+
+```text
+two pressure witnesses exist if pressureDepthCount >= 2
+```
+
+Riskier theorem:
+
+```text
+two pressure witnesses give two independent delayed budgets
+```
+
+The latter needs an explicit disjointness or separated-address hypothesis.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-121.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-121.md
new file mode 100644
index 00000000..624f5a02
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-121.md
@@ -0,0 +1,229 @@
+# Report Petal 121
+
+## Summary
+
+Checkpoint 121 connects the selected pressure witness layer to the first
+delayed-budget surface.
+
+Implemented:
+
+```text
+pressure count / outruns-heavy
+  -> tower-entry witness alias
+
+depth-two one-range pressure
+  -> positive continuation mass
+  -> delayed budget with tail 7 mod 8 remainder
+```
+
+Also added a Python orbit-window scan for pressure witnesses and L1..L5
+remainders.
+
+## Lean Changes
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+### Tower-Entry Aliases
+
+Added:
+
+```lean
+exists_towerEntryDepth_of_pressureDepthCount_pos
+exists_towerEntryDepth_of_outrunsMoreThanHalf
+```
+
+These are caller-facing wrappers over the checkpoint 120 existence theorems:
+
+```lean
+exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+```
+
+Reading:
+
+```text
+positive pressure-depth count
+  -> selected local tower-entry opportunity
+```
+
+and:
+
+```text
+SourceOutrunsMoreThanHalfOnDepthRange
+  -> selected local tower-entry opportunity
+```
+
+The theorem only provides one selected positive source continuation mass.  It
+does not assert independence between several selected depths.
+
+### Depth-Two Positive Budget Pair
+
+Added:
+
+```lean
+depthTwoPressureRange_positive_and_budget
+exists_depth_two_budget_of_pressureOnRange_two_one
+```
+
+Meaning:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> 0 < orbitWindowContinuationSiblingMassPow2 n k 2
+  -> (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2
+       <= sumS n ((k + 1) + 1)
+          + orbitWindowResidueCountMod8EqSevenTail n k
+```
+
+This is the direct selected-witness-to-budget bridge requested by the review.
+
+## Python Experiment
+
+New script:
+
+```text
+python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
+python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
+```
+
+Command:
+
+```text
+python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+```
+
+The table records:
+
+```text
+n
+steps
+sumS
+pressure_depth_count
+first_pressure_depth
+continuation_mass_at_first_pressure
+retention_mass_at_first_pressure
+L1..L5 delayed remainders
+L1..L5 falling colors
+```
+
+Observed summary:
+
+```text
+rows: 500
+rows with pressure witness: 237
+rows with L5 remainder: 18
+max pressure depth count: 6
+max L5 remainder: 3
+```
+
+Top pressure examples include:
+
+```text
+n=511: pressure count 6, first depth 2, continuation 8, retention 10
+n=681: pressure count 6, first depth 2, continuation 8, retention 10
+n=795: pressure count 5, first depth 2, continuation 14, retention 20
+```
+
+## Interpretation
+
+The data suggests:
+
+```text
+pressure witnesses are common
+deep all-ones remainder is much rarer
+```
+
+This is consistent with the current proof direction:
+
+```text
+one pressure witness
+  -> one delayed budget opportunity
+```
+
+but it does not justify:
+
+```text
+many pressure witnesses
+  -> many independent delayed budgets
+```
+
+That second statement still needs a no-overlap or address-separated condition.
+
+## Documentation Updated
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedWitnessBudget-121.md
+```
+
+## Verification
+
+Passed:
+
+```text
+python3 python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched checkpoint 121 files>
+```
+
+The `rg` no-sorry check returned no matches for `PetalBridge.lean`.
+
+Known unrelated warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Suggested Next Implementation
+
+Next target:
+
+```lean
+theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+This should produce two distinct selected pressure depths only.
+
+It must not claim independent budget accounting yet.
+
+The next conceptual package should be one of:
+
+```text
+SelectedPressureDepths
+SelectedDepthsAddressSeparated
+DisjointTowerTargets
+```
+
+The safe route is:
+
+```text
+count >= 2
+  -> two witnesses
+  -> investigate whether their target residue channels overlap
+```
+
+Only after that should the project attempt a multi-budget sum theorem.
diff --git a/python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py b/python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
new file mode 100644
index 00000000..0728b272
--- /dev/null
+++ b/python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
@@ -0,0 +1,231 @@
+#!/usr/bin/env python3
+"""Scan pressure witnesses and delayed-remainder levels on Collatz windows.
+
+This script mirrors the finite natural counts used by
+`DkMath.Collatz.PetalBridge`:
+
+* source pressure depth count
+* first selected source-pressure depth
+* source continuation mass at that depth
+* shifted-tail remainder levels L1..L5
+
+The output is observational data only.  It is meant to guide which Lean theorem
+should be attempted next.
+"""
+
+from __future__ import annotations
+
+import argparse
+import csv
+from dataclasses import dataclass
+from pathlib import Path
+
+
+@dataclass(frozen=True)
+class OrbitPressureRow:
+    n: int
+    steps: int
+    r_start: int
+    depth_len: int
+    sum_s: int
+    pressure_depth_count: int
+    first_pressure_j: int
+    first_pressure_depth: int
+    continuation_mass_at_first_pressure: int
+    retention_mass_at_first_pressure: int
+    l1_remainder: int
+    l2_remainder: int
+    l3_remainder: int
+    l4_remainder: int
+    l5_remainder: int
+    falling_l1: int
+    falling_l2: int
+    falling_l3: int
+    falling_l4: int
+    falling_l5: int
+
+
+def v2(n: int) -> int:
+    if n <= 0:
+        raise ValueError("v2 expects a positive integer")
+    count = 0
+    while n % 2 == 0:
+        count += 1
+        n //= 2
+    return count
+
+
+def accelerated_step(n: int) -> tuple[int, int]:
+    value = 3 * n + 1
+    height = v2(value)
+    return value >> height, height
+
+
+def orbit_labels_and_heights(n: int, steps: int) -> tuple[list[int], list[int]]:
+    labels: list[int] = []
+    heights: list[int] = []
+    current = n
+    for _ in range(steps + 1):
+        labels.append(current)
+        next_value, height = accelerated_step(current)
+        heights.append(height)
+        current = next_value
+    return labels, heights
+
+
+def count_residue(values: list[int], modulus: int, residue: int) -> int:
+    return sum(1 for value in values if value % modulus == residue)
+
+
+def retention_mass(labels: list[int], steps: int, depth: int) -> int:
+    return count_residue(labels[:steps], 2**depth, 2**depth - 1)
+
+
+def continuation_mass(labels: list[int], steps: int, depth: int) -> int:
+    return count_residue(labels[:steps], 2 ** (depth + 1), 2 ** (depth + 1) - 1)
+
+
+def pressure_depths(labels: list[int], steps: int, r_start: int, depth_len: int) -> list[int]:
+    selected: list[int] = []
+    for j in range(depth_len):
+        depth = r_start + j
+        continuation = continuation_mass(labels, steps, depth)
+        retention = retention_mass(labels, steps, depth)
+        if retention < 2 * continuation:
+            selected.append(j)
+    return selected
+
+
+def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OrbitPressureRow:
+    labels, heights = orbit_labels_and_heights(n, steps)
+    tail = labels[1 : steps + 1]
+    selected = pressure_depths(labels, steps, r_start, depth_len)
+    first_j = selected[0] if selected else -1
+    first_depth = r_start + first_j if selected else -1
+    first_continuation = (
+        continuation_mass(labels, steps, first_depth) if selected else 0
+    )
+    first_retention = retention_mass(labels, steps, first_depth) if selected else 0
+    return OrbitPressureRow(
+        n=n,
+        steps=steps,
+        r_start=r_start,
+        depth_len=depth_len,
+        sum_s=sum(heights[:steps]),
+        pressure_depth_count=len(selected),
+        first_pressure_j=first_j,
+        first_pressure_depth=first_depth,
+        continuation_mass_at_first_pressure=first_continuation,
+        retention_mass_at_first_pressure=first_retention,
+        l1_remainder=count_residue(tail[:steps], 8, 7),
+        l2_remainder=count_residue(tail[:steps], 16, 15),
+        l3_remainder=count_residue(tail[:steps], 32, 31),
+        l4_remainder=count_residue(tail[:steps], 64, 63),
+        l5_remainder=count_residue(tail[:steps], 128, 127),
+        falling_l1=count_residue(tail[:steps], 8, 3),
+        falling_l2=count_residue(tail[:steps], 16, 7),
+        falling_l3=count_residue(tail[:steps], 32, 15),
+        falling_l4=count_residue(tail[:steps], 64, 31),
+        falling_l5=count_residue(tail[:steps], 128, 63),
+    )
+
+
+def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[OrbitPressureRow]:
+    rows: list[OrbitPressureRow] = []
+    for n in range(1, max_n + 1, 2):
+        rows.append(row_for(n, steps, r_start, depth_len))
+    return rows
+
+
+def write_csv(rows: list[OrbitPressureRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    with path.open("w", newline="", encoding="utf-8") as f:
+        writer = csv.DictWriter(f, fieldnames=list(OrbitPressureRow.__dataclass_fields__))
+        writer.writeheader()
+        for row in rows:
+            writer.writerow(row.__dict__)
+
+
+def write_summary(rows: list[OrbitPressureRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    with_pressure = [row for row in rows if row.pressure_depth_count > 0]
+    deep_l5 = [row for row in rows if row.l5_remainder > 0]
+    max_pressure = max((row.pressure_depth_count for row in rows), default=0)
+    max_l5 = max((row.l5_remainder for row in rows), default=0)
+    sample = sorted(
+        with_pressure,
+        key=lambda row: (
+            -row.pressure_depth_count,
+            -row.continuation_mass_at_first_pressure,
+            row.n,
+        ),
+    )[:12]
+    lines = [
+        "# Collatz Orbit Pressure Remainder Scan",
+        "",
+        f"- rows: `{len(rows)}`",
+        f"- rows with pressure witness: `{len(with_pressure)}`",
+        f"- rows with L5 remainder: `{len(deep_l5)}`",
+        f"- max pressure depth count: `{max_pressure}`",
+        f"- max L5 remainder: `{max_l5}`",
+        "",
+        "## Top Pressure Samples",
+        "",
+        "| n | sumS | pressure count | first depth | cont mass | ret mass | L1 | L2 | L3 | L4 | L5 |",
+        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
+    ]
+    for row in sample:
+        lines.append(
+            "| "
+            f"{row.n} | {row.sum_s} | {row.pressure_depth_count} | "
+            f"{row.first_pressure_depth} | "
+            f"{row.continuation_mass_at_first_pressure} | "
+            f"{row.retention_mass_at_first_pressure} | "
+            f"{row.l1_remainder} | {row.l2_remainder} | {row.l3_remainder} | "
+            f"{row.l4_remainder} | {row.l5_remainder} |"
+        )
+    lines.extend(
+        [
+            "",
+            "## Reading",
+            "",
+            "`pressure_depth_count > 0` marks at least one local source continuation",
+            "pressure witness.  The Lean checkpoint 121 bridge turns the depth-two",
+            "one-range version into a positive mass plus delayed-budget pair.",
+            "",
+            "The L1..L5 columns record the shifted-tail all-ones delayed remainders.",
+            "They should be read as possible retained mass, not as independent",
+            "budget entries.",
+            "",
+        ]
+    )
+    path.write_text("\n".join(lines), encoding="utf-8")
+
+
+def parse_args() -> argparse.Namespace:
+    parser = argparse.ArgumentParser()
+    parser.add_argument("--max-n", type=int, default=999)
+    parser.add_argument("--steps", type=int, default=64)
+    parser.add_argument("--r-start", type=int, default=2)
+    parser.add_argument("--depth-len", type=int, default=8)
+    parser.add_argument(
+        "--out-dir",
+        type=Path,
+        default=Path("python/Collatz/PetalBridge/results"),
+    )
+    return parser.parse_args()
+
+
+def main() -> None:
+    args = parse_args()
+    rows = scan(args.max_n, args.steps, args.r_start, args.depth_len)
+    csv_path = args.out_dir / "orbit_pressure_remainder_scan.csv"
+    summary_path = args.out_dir / "orbit_pressure_remainder_scan.md"
+    write_csv(rows, csv_path)
+    write_summary(rows, summary_path)
+    print(f"wrote {csv_path}")
+    print(f"wrote {summary_path}")
+
+
+if __name__ == "__main__":
+    main()
diff --git a/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv b/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
new file mode 100644
index 00000000..6efab90a
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.csv
@@ -0,0 +1,501 @@
+n,steps,r_start,depth_len,sum_s,pressure_depth_count,first_pressure_j,first_pressure_depth,continuation_mass_at_first_pressure,retention_mass_at_first_pressure,l1_remainder,l2_remainder,l3_remainder,l4_remainder,l5_remainder,falling_l1,falling_l2,falling_l3,falling_l4,falling_l5
+1,64,2,8,128,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+3,64,2,8,129,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+5,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+7,64,2,8,129,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+9,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+11,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+13,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+15,64,2,8,130,1,0,2,2,3,1,0,0,0,0,1,1,0,0,0
+17,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+19,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+21,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+23,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+25,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+27,64,2,8,116,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+29,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+31,64,2,8,117,1,0,2,14,23,13,6,2,1,0,9,7,4,1,1
+33,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+35,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+37,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+39,64,2,8,129,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+41,64,2,8,117,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+43,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+45,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+47,64,2,8,118,1,0,2,13,22,12,5,2,1,0,9,7,3,1,1
+49,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+51,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+53,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+55,64,2,8,117,1,0,2,14,24,13,6,2,1,0,10,7,4,1,1
+57,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+59,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+61,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+63,64,2,8,118,2,0,2,15,24,14,7,3,1,0,9,7,4,2,1
+65,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+67,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+69,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+71,64,2,8,119,1,0,2,12,21,11,5,2,1,0,9,6,3,1,1
+73,64,2,8,117,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+75,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+77,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+79,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+81,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+83,64,2,8,118,1,0,2,13,23,13,6,2,1,0,9,7,4,1,1
+85,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+87,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+89,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+91,64,2,8,121,1,0,2,11,19,11,5,2,1,0,7,6,3,1,1
+93,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+95,64,2,8,119,1,0,2,14,23,13,6,2,1,0,9,7,4,1,1
+97,64,2,8,117,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+99,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+101,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+103,64,2,8,122,1,0,2,11,18,10,5,2,1,0,7,5,3,1,1
+105,64,2,8,130,0,-1,-1,0,0,2,1,0,0,0,3,1,1,0,0
+107,64,2,8,120,1,0,2,11,20,11,5,2,1,0,8,6,3,1,1
+109,64,2,8,118,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+111,64,2,8,125,2,0,2,9,14,8,4,2,1,0,5,4,2,1,1
+113,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+115,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+117,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+119,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+121,64,2,8,121,1,0,2,11,19,11,5,2,1,0,8,6,3,1,1
+123,64,2,8,129,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+125,64,2,8,119,1,0,2,13,22,13,6,2,1,0,9,7,4,1,1
+127,64,2,8,129,4,0,2,5,7,4,3,2,1,0,2,1,1,1,1
+129,64,2,8,117,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+131,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+133,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+135,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+137,64,2,8,122,1,0,2,11,18,11,5,2,1,0,7,6,3,1,1
+139,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+141,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+143,64,2,8,120,1,0,2,13,22,12,5,2,1,0,9,7,3,1,1
+145,64,2,8,118,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+147,64,2,8,118,1,0,2,13,24,13,6,2,1,0,10,7,4,1,1
+149,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+151,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+153,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+155,64,2,8,123,1,0,2,10,17,10,5,2,1,0,6,5,3,1,1
+157,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+159,64,2,8,128,2,0,2,7,10,6,3,1,0,0,3,3,2,1,0
+161,64,2,8,121,1,0,2,11,19,11,5,2,1,0,8,6,3,1,1
+163,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+165,64,2,8,119,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+167,64,2,8,126,1,0,2,8,13,7,4,2,1,0,5,3,2,1,1
+169,64,2,8,129,4,0,2,5,7,5,4,3,2,1,2,1,1,1,1
+171,64,2,8,117,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+173,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+175,64,2,8,124,1,0,2,10,16,9,4,2,1,0,6,5,2,1,1
+177,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+179,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+181,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+183,64,2,8,122,1,0,2,11,19,10,5,2,1,0,8,5,3,1,1
+185,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+187,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+189,64,2,8,120,1,0,2,12,21,12,5,2,1,0,9,7,3,1,1
+191,64,2,8,130,3,0,2,4,6,3,2,1,0,0,2,1,1,1,0
+193,64,2,8,118,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+195,64,2,8,118,1,0,2,14,25,14,6,2,1,0,10,8,4,1,1
+197,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+199,64,2,8,118,1,0,2,15,25,14,7,3,1,0,10,7,4,2,1
+201,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+203,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+205,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+207,64,2,8,123,1,0,2,11,18,10,4,2,1,0,7,6,2,1,1
+209,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+211,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+213,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+215,64,2,8,121,1,0,2,12,21,11,5,2,1,0,9,6,3,1,1
+217,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+219,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+221,64,2,8,119,1,0,2,13,23,13,6,2,1,0,10,7,4,1,1
+223,64,2,8,126,2,0,2,10,14,9,5,2,1,0,4,4,3,1,1
+225,64,2,8,129,4,0,2,5,7,5,4,3,2,1,2,1,1,1,1
+227,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+229,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+231,64,2,8,117,1,0,2,16,27,15,7,3,1,0,11,8,4,2,1
+233,64,2,8,124,1,0,2,10,16,10,5,2,1,0,6,5,3,1,1
+235,64,2,8,117,1,0,2,15,26,15,7,3,1,0,10,8,4,2,1
+237,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+239,64,2,8,129,1,0,2,6,9,5,2,1,0,0,3,3,1,1,0
+241,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+243,64,2,8,122,1,0,2,11,19,11,5,2,1,0,7,6,3,1,1
+245,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+247,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+249,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+251,64,2,8,127,2,0,2,7,12,7,4,2,1,0,4,3,2,1,1
+253,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+255,64,2,8,130,5,0,2,6,8,5,4,3,2,1,2,1,1,1,1
+257,64,2,8,118,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+259,64,2,8,118,1,0,2,14,25,14,6,2,1,0,10,8,4,1,1
+261,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+263,64,2,8,125,1,0,2,9,15,8,4,2,1,0,6,4,2,1,1
+265,64,2,8,118,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+267,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+269,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+271,64,2,8,131,0,-1,-1,0,0,2,0,0,0,0,3,2,0,0,0
+273,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+275,64,2,8,123,1,0,2,10,18,10,5,2,1,0,7,5,3,1,1
+277,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+279,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+281,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+283,64,2,8,128,2,0,2,7,11,7,4,2,1,0,3,3,2,1,1
+285,64,2,8,121,1,0,2,11,20,11,5,2,1,0,9,6,3,1,1
+287,64,2,8,131,2,0,2,3,5,2,1,0,0,0,2,1,1,0,0
+289,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+291,64,2,8,119,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+293,64,2,8,119,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+295,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,6,1,0,0,0
+297,64,2,8,126,2,0,2,10,14,10,6,3,1,0,4,4,3,2,1
+299,64,2,8,119,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+301,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+303,64,2,8,131,1,0,2,3,5,2,0,0,0,0,2,2,0,0,0
+305,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+307,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+309,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+311,64,2,8,124,1,0,2,10,17,9,4,2,1,0,7,5,2,1,1
+313,64,2,8,117,1,0,2,15,26,15,7,3,1,0,11,8,4,2,1
+315,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+317,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+319,64,2,8,129,2,0,2,7,10,6,3,1,0,0,3,3,2,1,0
+321,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+323,64,2,8,122,1,0,2,11,20,11,5,2,1,0,8,6,3,1,1
+325,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+327,64,2,8,115,1,0,2,17,29,16,8,3,1,0,12,8,5,2,1
+329,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+331,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+333,64,2,8,120,1,0,2,13,22,13,6,2,1,0,9,7,4,1,1
+335,64,2,8,127,2,0,2,9,13,8,4,2,1,0,4,4,2,1,1
+337,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+339,64,2,8,130,3,0,2,4,7,4,3,2,1,0,2,1,1,1,1
+341,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+343,64,2,8,118,1,0,2,15,25,14,7,3,1,0,10,7,4,2,1
+345,64,2,8,118,1,0,2,14,25,14,6,2,1,0,11,8,4,1,1
+347,64,2,8,118,1,0,2,15,26,15,7,3,1,0,10,8,4,2,1
+349,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+351,64,2,8,125,2,0,2,11,17,10,5,2,1,0,6,5,3,1,1
+353,64,2,8,118,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+355,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+357,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+359,64,2,8,130,1,0,2,5,8,4,2,1,0,0,3,2,1,1,0
+361,64,2,8,131,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+363,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+365,64,2,8,123,1,0,2,11,18,11,5,2,1,0,7,6,3,1,1
+367,64,2,8,131,0,-1,-1,0,0,2,0,0,0,0,4,2,0,0,0
+369,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+371,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+373,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+375,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+377,64,2,8,128,2,0,2,7,11,7,4,2,1,0,4,3,2,1,1
+379,64,2,8,129,0,-1,-1,0,0,3,1,0,0,0,4,2,1,0,0
+381,64,2,8,121,1,0,2,13,22,13,6,2,1,0,9,7,4,1,1
+383,64,2,8,131,4,0,2,5,7,4,3,2,1,0,2,1,1,1,1
+385,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+387,64,2,8,119,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+389,64,2,8,119,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+391,64,2,8,119,1,0,2,15,25,14,7,3,1,0,10,7,4,2,1
+393,64,2,8,129,0,-1,-1,0,0,2,0,0,0,0,6,2,0,0,0
+395,64,2,8,126,1,0,2,8,14,8,4,2,1,0,5,4,2,1,1
+397,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+399,64,2,8,119,1,0,2,16,26,15,7,3,1,0,10,8,4,2,1
+401,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+403,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+405,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+407,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+409,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+411,64,2,8,117,1,0,2,16,28,16,8,3,1,0,11,8,5,2,1
+413,64,2,8,124,1,0,2,10,17,10,5,2,1,0,7,5,3,1,1
+415,64,2,8,117,1,0,2,16,27,15,7,2,1,0,11,8,5,1,1
+417,64,2,8,117,1,0,2,15,26,15,7,3,1,0,11,8,4,2,1
+419,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+421,64,2,8,132,0,-1,-1,0,0,2,1,0,0,0,3,1,1,0,0
+423,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+425,64,2,8,129,2,0,2,7,10,7,4,2,1,0,3,3,2,1,1
+427,64,2,8,130,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+429,64,2,8,122,1,0,2,11,19,11,5,2,1,0,8,6,3,1,1
+431,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+433,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+435,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+437,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+439,64,2,8,130,0,-1,-1,0,0,0,0,0,0,0,6,0,0,0,0
+441,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+443,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+445,64,2,8,127,1,0,2,8,13,8,4,2,1,0,5,4,2,1,1
+447,64,2,8,123,4,0,2,14,19,13,8,5,3,2,5,5,3,2,1
+449,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+451,64,2,8,130,4,0,2,5,8,5,4,3,2,1,2,1,1,1,1
+453,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+455,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+457,64,2,8,118,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+459,64,2,8,118,1,0,2,14,25,14,6,2,1,0,10,8,4,1,1
+461,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+463,64,2,8,118,1,0,2,16,27,15,7,3,1,0,11,8,4,2,1
+465,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+467,64,2,8,125,1,0,2,9,16,9,4,2,1,0,6,5,2,1,1
+469,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+471,64,2,8,118,1,0,2,16,27,15,7,3,1,0,11,8,4,2,1
+473,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+475,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+477,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+479,64,2,8,130,1,0,2,6,9,5,2,0,0,0,3,3,2,0,0
+481,64,2,8,131,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+483,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+485,64,2,8,123,1,0,2,11,19,11,5,2,1,0,8,6,3,1,1
+487,64,2,8,116,1,0,2,17,30,16,7,3,1,0,13,9,4,2,1
+489,64,2,8,131,0,-1,-1,0,0,3,1,0,0,0,4,2,1,0,0
+491,64,2,8,116,1,0,2,16,28,16,8,3,1,0,11,8,5,2,1
+493,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+495,64,2,8,123,1,0,2,10,18,9,3,1,0,0,8,6,2,1,0
+497,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+499,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+501,64,2,8,121,1,0,2,13,22,13,6,2,1,0,9,7,4,1,1
+503,64,2,8,128,1,0,2,8,12,7,4,2,1,0,4,3,2,1,1
+505,64,2,8,129,0,-1,-1,0,0,3,1,0,0,0,5,2,1,0,0
+507,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+509,64,2,8,131,3,0,2,4,6,4,3,2,1,0,2,1,1,1,1
+511,64,2,8,129,6,0,2,8,10,7,5,4,3,2,2,2,1,1,1
+513,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+515,64,2,8,119,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+517,64,2,8,119,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+519,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,6,1,0,0,0
+521,64,2,8,119,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+523,64,2,8,119,1,0,2,13,24,13,6,2,1,0,10,7,4,1,1
+525,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+527,64,2,8,126,1,0,2,10,16,9,4,2,1,0,6,5,2,1,1
+529,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+531,64,2,8,119,1,0,2,14,25,14,7,3,1,0,10,7,4,2,1
+533,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+535,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+537,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+539,64,2,8,131,1,0,2,4,7,4,2,1,0,0,2,2,1,1,0
+541,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+543,64,2,8,117,2,0,2,17,27,16,8,3,1,0,10,8,5,2,1
+545,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+547,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+549,64,2,8,124,1,0,2,11,18,11,5,2,1,0,7,6,3,1,1
+551,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+553,64,2,8,117,1,0,2,16,27,16,8,3,1,0,11,8,5,2,1
+555,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+557,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+559,64,2,8,125,0,-1,-1,0,0,5,1,0,0,0,8,4,1,0,0
+561,64,2,8,132,0,-1,-1,0,0,2,1,0,0,0,3,1,1,0,0
+563,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+565,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+567,64,2,8,129,1,0,2,7,11,6,3,1,0,0,4,3,2,1,0
+569,64,2,8,130,0,-1,-1,0,0,3,1,0,0,0,4,2,1,0,0
+571,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+573,64,2,8,122,1,0,2,12,21,12,5,2,1,0,9,7,3,1,1
+575,64,2,8,132,3,0,2,4,6,3,2,1,0,0,2,1,1,1,0
+577,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+579,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+581,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+583,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+585,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,6,1,0,0,0
+587,64,2,8,120,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+589,64,2,8,120,1,0,2,13,23,13,6,2,1,0,10,7,4,1,1
+591,64,2,8,130,0,-1,-1,0,0,2,0,0,0,0,5,2,0,0,0
+593,64,2,8,127,1,0,2,8,13,8,4,2,1,0,5,4,2,1,1
+595,64,2,8,127,2,0,2,9,14,9,5,2,1,0,4,4,3,1,1
+597,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+599,64,2,8,120,1,0,2,15,25,14,7,3,1,0,10,7,4,2,1
+601,64,2,8,130,4,0,2,5,8,5,4,3,2,1,3,1,1,1,1
+603,64,2,8,128,0,-1,-1,0,0,2,0,0,0,0,5,2,0,0,0
+605,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+607,64,2,8,132,1,0,2,4,6,3,1,0,0,0,2,2,1,0,0
+609,64,2,8,118,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+611,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+613,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+615,64,2,8,128,0,-1,-1,0,0,3,1,0,0,0,7,2,1,0,0
+617,64,2,8,118,1,0,2,16,27,16,8,3,1,0,11,8,5,2,1
+619,64,2,8,118,1,0,2,13,25,13,6,2,1,0,11,7,4,1,1
+621,64,2,8,125,1,0,2,10,16,10,5,2,1,0,6,5,3,1,1
+623,64,2,8,118,1,0,2,15,26,14,6,2,1,0,11,8,4,1,1
+625,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+627,64,2,8,118,1,0,2,15,26,15,7,3,1,0,10,8,4,2,1
+629,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+631,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+633,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+635,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+637,64,2,8,130,1,0,2,6,9,6,3,1,0,0,3,3,2,1,0
+639,64,2,8,118,4,0,2,17,27,16,8,4,2,0,10,8,4,2,2
+641,64,2,8,131,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+643,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+645,64,2,8,123,1,0,2,11,19,11,5,2,1,0,8,6,3,1,1
+647,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+649,64,2,8,116,1,0,2,17,30,17,7,3,1,0,13,10,4,2,1
+651,64,2,8,123,1,0,2,10,19,10,5,2,1,0,8,5,3,1,1
+653,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+655,64,2,8,116,1,0,2,18,30,17,8,3,1,0,12,9,5,2,1
+657,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+659,64,2,8,131,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+661,64,2,8,121,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+663,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+665,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+667,64,2,8,116,1,0,2,18,32,18,8,2,1,0,13,10,6,1,1
+669,64,2,8,128,2,0,2,7,12,7,4,2,1,0,5,3,2,1,1
+671,64,2,8,124,5,0,2,13,18,12,7,4,3,2,5,5,3,1,1
+673,64,2,8,129,0,-1,-1,0,0,3,1,0,0,0,5,2,1,0,0
+675,64,2,8,121,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+677,64,2,8,131,4,0,2,5,7,5,4,3,2,1,2,1,1,1,1
+679,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+681,64,2,8,129,6,0,2,8,10,8,6,5,4,3,2,2,1,1,1
+683,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+685,64,2,8,119,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+687,64,2,8,133,1,0,2,3,5,2,0,0,0,0,2,2,0,0,0
+689,64,2,8,119,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+691,64,2,8,119,1,0,2,14,25,14,6,2,1,0,10,8,4,1,1
+693,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+695,64,2,8,119,1,0,2,15,26,14,7,3,1,0,11,7,4,2,1
+697,64,2,8,119,1,0,2,13,24,13,6,2,1,0,11,7,4,1,1
+699,64,2,8,129,0,-1,-1,0,0,1,0,0,0,0,7,1,0,0,0
+701,64,2,8,126,1,0,2,9,15,9,4,2,1,0,6,5,2,1,1
+703,64,2,8,112,2,0,2,22,37,21,11,5,1,0,15,10,6,4,1
+705,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+707,64,2,8,119,1,0,2,15,26,15,7,3,1,0,10,8,4,2,1
+709,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+711,64,2,8,129,4,0,2,6,9,5,4,3,2,1,3,1,1,1,1
+713,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+715,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+717,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+719,64,2,8,131,1,0,2,5,8,4,1,0,0,0,3,3,1,0,0
+721,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+723,64,2,8,132,0,-1,-1,0,0,2,0,0,0,0,3,2,0,0,0
+725,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+727,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+729,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+731,64,2,8,117,1,0,2,16,29,16,7,3,1,0,12,9,4,2,1
+733,64,2,8,124,1,0,2,10,18,10,5,2,1,0,8,5,3,1,1
+735,64,2,8,132,1,0,2,4,7,3,1,0,0,0,3,2,1,0,0
+737,64,2,8,117,1,0,2,16,27,16,8,3,1,0,11,8,5,2,1
+739,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+741,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+743,64,2,8,124,1,0,2,9,17,8,3,1,0,0,8,5,2,1,0
+745,64,2,8,125,0,-1,-1,0,0,6,2,0,0,0,8,4,2,0,0
+747,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+749,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,4,1,0,0,0
+751,64,2,8,117,1,0,2,18,31,17,7,2,1,0,13,10,5,1,1
+753,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+755,64,2,8,129,2,0,2,7,11,7,4,2,1,0,3,3,2,1,1
+757,64,2,8,122,1,0,2,12,21,12,5,2,1,0,9,7,3,1,1
+759,64,2,8,130,0,-1,-1,0,0,3,1,0,0,0,4,2,1,0,0
+761,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+763,64,2,8,115,1,0,2,16,30,16,6,2,1,0,13,10,4,1,1
+765,64,2,8,132,2,0,2,3,5,3,2,1,0,0,2,1,1,1,0
+767,64,2,8,130,5,0,2,7,9,6,4,3,2,1,2,2,1,1,1
+769,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+771,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+773,64,2,8,120,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+775,64,2,8,115,1,0,2,17,30,16,8,3,1,0,13,8,5,2,1
+777,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+779,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+781,64,2,8,120,1,0,2,14,24,14,6,2,1,0,10,8,4,1,1
+783,64,2,8,120,1,0,2,16,26,15,7,3,1,0,10,8,4,2,1
+785,64,2,8,120,1,0,2,13,23,13,6,2,1,0,10,7,4,1,1
+787,64,2,8,130,0,-1,-1,0,0,1,0,0,0,0,6,1,0,0,0
+789,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+791,64,2,8,127,1,0,2,9,15,8,4,2,1,0,6,4,2,1,1
+793,64,2,8,127,2,0,2,9,14,9,5,2,1,0,5,4,3,1,1
+795,64,2,8,123,5,0,2,14,20,14,10,7,5,3,5,4,3,2,2
+797,64,2,8,120,1,0,2,14,24,14,7,3,1,0,10,7,4,2,1
+799,64,2,8,128,1,0,2,6,11,5,2,0,0,0,5,3,2,0,0
+801,64,2,8,130,4,0,2,5,8,5,4,3,2,1,3,1,1,1,1
+803,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+805,64,2,8,136,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+807,64,2,8,128,5,0,2,8,12,7,5,4,3,2,4,2,1,1,1
+809,64,2,8,132,1,0,2,4,6,4,2,1,0,0,2,2,1,1,0
+811,64,2,8,118,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+813,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+815,64,2,8,118,1,0,2,16,26,15,7,3,1,0,10,8,4,2,1
+817,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+819,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+821,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+823,64,2,8,118,1,0,2,16,28,15,7,3,1,0,12,8,4,2,1
+825,64,2,8,118,1,0,2,13,25,13,6,2,1,0,12,7,4,1,1
+827,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+829,64,2,8,125,1,0,2,10,17,10,4,2,1,0,7,6,2,1,1
+831,64,2,8,118,2,0,2,17,27,16,8,3,1,0,10,8,5,2,1
+833,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+835,64,2,8,118,1,0,2,15,27,15,7,3,1,0,11,8,4,2,1
+837,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,4,0,0,0,0
+839,64,2,8,126,0,-1,-1,0,0,4,1,0,0,0,8,3,1,0,0
+841,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+843,64,2,8,133,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+845,64,2,8,133,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+847,64,2,8,134,1,0,2,3,5,2,0,0,0,0,2,2,0,0,0
+849,64,2,8,130,1,0,2,6,9,6,3,1,0,0,3,3,2,1,0
+851,64,2,8,130,1,0,2,6,10,6,3,1,0,0,3,3,2,1,0
+853,64,2,8,137,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+855,64,2,8,131,0,-1,-1,0,0,3,1,0,0,0,4,2,1,0,0
+857,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+859,64,2,8,116,1,0,2,16,29,16,6,2,1,0,12,10,4,1,1
+861,64,2,8,123,1,0,2,11,20,11,5,2,1,0,9,6,3,1,1
+863,64,2,8,133,2,0,2,3,5,2,1,0,0,0,2,1,1,0,0
+865,64,2,8,116,1,0,2,17,30,17,7,3,1,0,13,10,4,2,1
+867,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+869,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+871,64,2,8,109,3,0,2,23,38,22,13,7,3,0,15,9,6,4,3
+873,64,2,8,116,1,0,2,18,30,18,9,3,1,0,12,9,6,2,1
+875,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+877,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+879,64,2,8,116,1,0,2,17,30,16,7,3,1,0,13,9,4,2,1
+881,64,2,8,121,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+883,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+885,64,2,8,121,1,0,2,13,23,13,6,2,1,0,10,7,4,1,1
+887,64,2,8,131,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+889,64,2,8,116,1,0,2,18,32,18,8,2,1,0,14,10,6,1,1
+891,64,2,8,132,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+893,64,2,8,128,2,0,2,9,13,9,5,2,1,0,4,4,3,1,1
+895,64,2,8,124,5,0,2,14,19,13,9,6,4,2,5,4,3,2,2
+897,64,2,8,129,0,-1,-1,0,0,3,1,0,0,0,5,2,1,0,0
+899,64,2,8,121,1,0,2,14,24,14,7,3,1,0,9,7,4,2,1
+901,64,2,8,131,4,0,2,5,7,5,4,3,2,1,2,1,1,1,1
+903,64,2,8,121,1,0,2,14,24,13,6,2,1,0,10,7,4,1,1
+905,64,2,8,129,0,-1,-1,0,0,2,0,0,0,0,5,2,0,0,0
+907,64,2,8,131,4,0,2,5,8,5,4,3,2,1,2,1,1,1,1
+909,64,2,8,137,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+911,64,2,8,133,1,0,2,3,5,2,0,0,0,0,2,2,0,0,0
+913,64,2,8,119,1,0,2,14,23,14,7,3,1,0,9,7,4,2,1
+915,64,2,8,119,1,0,2,14,25,14,7,3,1,0,10,7,4,2,1
+917,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+919,64,2,8,119,1,0,2,15,26,14,6,2,1,0,11,8,4,1,1
+921,64,2,8,119,1,0,2,14,25,14,6,2,1,0,11,8,4,1,1
+923,64,2,8,129,0,-1,-1,0,0,3,1,0,0,0,6,2,1,0,0
+925,64,2,8,119,1,0,2,15,26,15,7,3,1,0,11,8,4,2,1
+927,64,2,8,121,2,0,2,13,23,12,6,2,0,0,10,6,4,2,0
+929,64,2,8,119,1,0,2,13,24,13,6,2,1,0,11,7,4,1,1
+931,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+933,64,2,8,126,1,0,2,10,16,10,5,2,1,0,6,5,3,1,1
+935,64,2,8,119,1,0,2,14,25,13,6,2,1,0,11,7,4,1,1
+937,64,2,8,112,2,0,2,22,37,22,12,6,2,0,15,10,6,4,2
+939,64,2,8,126,2,0,2,9,15,9,5,2,1,0,5,4,3,1,1
+941,64,2,8,119,1,0,2,15,25,15,7,3,1,0,10,8,4,2,1
+943,64,2,8,134,1,0,2,3,5,2,0,0,0,0,2,2,0,0,0
+945,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+947,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+949,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,3,0,0,0,0
+951,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+953,64,2,8,135,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+955,64,2,8,135,0,-1,-1,0,0,0,0,0,0,0,2,0,0,0,0
+957,64,2,8,131,1,0,2,5,8,5,2,1,0,0,3,3,1,1,0
+959,64,2,8,119,1,0,2,16,26,15,7,3,1,0,10,8,4,2,1
+961,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,3,1,0,0,0
+963,64,2,8,132,0,-1,-1,0,0,3,1,0,0,0,3,2,1,0,0
+965,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0
+967,64,2,8,117,1,0,2,16,28,15,6,2,1,0,12,9,4,1,1
+969,64,2,8,132,0,-1,-1,0,0,2,0,0,0,0,3,2,0,0,0
+971,64,2,8,134,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+973,64,2,8,124,1,0,2,11,18,11,5,2,1,0,7,6,3,1,1
+975,64,2,8,117,1,0,2,17,30,16,7,3,1,0,13,9,4,2,1
+977,64,2,8,124,1,0,2,10,18,10,5,2,1,0,8,5,3,1,1
+979,64,2,8,132,0,-1,-1,0,0,2,0,0,0,0,4,2,0,0,0
+981,64,2,8,136,0,-1,-1,0,0,1,0,0,0,0,1,1,0,0,0
+983,64,2,8,117,1,0,2,17,29,16,8,3,1,0,12,8,5,2,1
+985,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+987,64,2,8,134,0,-1,-1,0,0,1,0,0,0,0,2,1,0,0,0
+989,64,2,8,132,0,-1,-1,0,0,0,0,0,0,0,5,0,0,0,0
+991,64,2,8,124,1,0,2,10,18,9,4,1,0,0,8,5,3,1,0
+993,64,2,8,125,0,-1,-1,0,0,6,2,0,0,0,8,4,2,0,0
+995,64,2,8,136,0,-1,-1,0,0,0,0,0,0,0,1,0,0,0,0
+997,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
+999,64,2,8,132,0,-1,-1,0,0,1,0,0,0,0,5,1,0,0,0
diff --git a/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md b/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
new file mode 100644
index 00000000..448ac127
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/orbit_pressure_remainder_scan.md
@@ -0,0 +1,34 @@
+# Collatz Orbit Pressure Remainder Scan
+
+- rows: `500`
+- rows with pressure witness: `237`
+- rows with L5 remainder: `18`
+- max pressure depth count: `6`
+- max L5 remainder: `3`
+
+## Top Pressure Samples
+
+| n | sumS | pressure count | first depth | cont mass | ret mass | L1 | L2 | L3 | L4 | L5 |
+|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
+| 511 | 129 | 6 | 2 | 8 | 10 | 7 | 5 | 4 | 3 | 2 |
+| 681 | 129 | 6 | 2 | 8 | 10 | 8 | 6 | 5 | 4 | 3 |
+| 795 | 123 | 5 | 2 | 14 | 20 | 14 | 10 | 7 | 5 | 3 |
+| 895 | 124 | 5 | 2 | 14 | 19 | 13 | 9 | 6 | 4 | 2 |
+| 671 | 124 | 5 | 2 | 13 | 18 | 12 | 7 | 4 | 3 | 2 |
+| 807 | 128 | 5 | 2 | 8 | 12 | 7 | 5 | 4 | 3 | 2 |
+| 767 | 130 | 5 | 2 | 7 | 9 | 6 | 4 | 3 | 2 | 1 |
+| 255 | 130 | 5 | 2 | 6 | 8 | 5 | 4 | 3 | 2 | 1 |
+| 639 | 118 | 4 | 2 | 17 | 27 | 16 | 8 | 4 | 2 | 0 |
+| 447 | 123 | 4 | 2 | 14 | 19 | 13 | 8 | 5 | 3 | 2 |
+| 711 | 129 | 4 | 2 | 6 | 9 | 5 | 4 | 3 | 2 | 1 |
+| 127 | 129 | 4 | 2 | 5 | 7 | 4 | 3 | 2 | 1 | 0 |
+
+## Reading
+
+`pressure_depth_count > 0` marks at least one local source continuation
+pressure witness.  The Lean checkpoint 121 bridge turns the depth-two
+one-range version into a positive mass plus delayed-budget pair.
+
+The L1..L5 columns record the shifted-tail all-ones delayed remainders.
+They should be read as possible retained mass, not as independent
+budget entries.
````
`````
