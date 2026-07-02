# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: ddf187fcee5a31d99c5c7db3b9f71f0a58a78bc8

## Report

Checkpoint 122 完了です。

`DkMath.Collatz.PetalBridge` に selected pressure depth の語彙を固定しました。

```lean
IsSourcePressureDepth
isSourcePressureDepth_of_pressureOnRange
positive_sourceContinuationMass_of_isSourcePressureDepth
exists_isSourcePressureDepth_of_pressureDepthCount_pos
exists_isSourcePressureDepth_with_positive_mass
```

本命の two-witness extraction も no-sorry で通りました。

```lean
exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

これは安全に「二つの distinct selected witnesses が存在する」だけを言います。budget independence はまだ主張していません。

追加で depth-two budget も predicate 化しました。

```lean
HasDepthTwoDelayedBudget
hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
```

Python 側では selected depths の overlap scan を追加しました。

- [selected_depth_overlap_scan.py](/python/Collatz/PetalBridge/selected_depth_overlap_scan.py)
- [selected_depth_overlap_scan.csv](/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv)
- [selected_depth_overlap_scan.md](/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md)

デフォルト観測では、500 window 中 `pressureDepthCount >= 2` が 52 行。その 52 行すべてで selected continuation sets が重なり、disjoint pair は 0 でした。次は `DisjointTowerTargets` より先に、nested/overlap control の語彙を立てるのが自然です。

Docs/report も同期済みです。

- [Collatz-SelectedPressureDepths-122.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md)
- [report-petal-122.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-122.md)

検証済みです。

```text
python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py --max-n 999 --steps 64 --r-start 2 --depth-len 8
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 122 files>
```

`PetalBridge.lean` は no-sorry。既知の無関係な `ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は残っています。

## Review

## 1. 状況分析

checkpoint `122` は、かなり大事な「方向修正 checkpoint」じゃ。

前回 `121` で、

```text
selected pressure witness
  -> positive continuation mass
  -> delayed budget with explicit remainder
```

までつながった。今回 `122` では、その selected witness をちゃんと Lean の語彙として固定した。

追加された中心語彙は、

```lean
IsSourcePressureDepth
```

そして、それに関する API として、

```lean
isSourcePressureDepth_of_pressureOnRange
positive_sourceContinuationMass_of_isSourcePressureDepth
exists_isSourcePressureDepth_of_pressureDepthCount_pos
exists_isSourcePressureDepth_with_positive_mass
```

が入った。さらに本命だった two-witness extraction も no-sorry で通り、

```lean
exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
```

が追加された。これは安全に「二つの distinct selected witnesses が存在する」だけを言い、budget independence はまだ主張していない。

そして Python 側の overlap scan が非常に重要じゃ。

```text
500 window 中、pressureDepthCount >= 2 は 52 行
その 52 行すべてで selected continuation sets が重なった
disjoint pair は 0
```

この観測はかなり深い。
「独立な selected depths を足し合わせればよい」という道は危ない。
むしろ、selected depths は **入れ子 / overlap 構造** として扱うべき、と見えてきた。

## 2. 今回の核心

今回の核心は、単に two witnesses が取れたことではない。

本当の核心は、

```text
two selected witnesses exist
  does not imply
two independent delayed budgets exist
```

を Lean と Python の両方で確認する流れができたことじゃ。

Lean 側では two-witness theorem を安全に witness extraction だけに留めた。

Python 側では、その二つ以上の selected depths が実際には disjoint にならず、すべて overlap していた。

つまり今回の結論は、

```text
selected pressure depths は、独立な複数予算ではなく、
同じ低位 all-ones cylinder を異なる解像度で見ている可能性が高い
```

ということじゃ。

ここは大きい。
証明方針を間違えると、同じ mass を二重計上してしまう。

## 3. レビュー

## 3.1. `IsSourcePressureDepth` を入れたのは正しい

今回の `IsSourcePressureDepth` は良い抽象化じゃ。

以前は毎回、

```lean
MoreThanHalf
  (orbitWindowContinuationSiblingMassPow2 n k (r + j))
  (orbitWindowRetentionMassPow2 n k (r + j))
```

を直接書いていた。

これは正確だが長い。
しかも後続の証明では「この `j` は selected depth である」という意味が重要になる。

そこで、

```lean
def IsSourcePressureDepth
    (n : OddNat) (k r : ℕ) (j : ℕ) : Prop :=
  MoreThanHalf
    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
    (orbitWindowRetentionMassPow2 n k (r + j))
```

としたのは、証明の主語を整理する意味で正しい。

これで、今後は

```text
selected depth
selected witness
selected pressure depth
```

という語彙で進められる。

## 3.2. two-witness theorem は良いが、あくまで witness extraction

今回の two-witness theorem は、次のように読むべきじゃ。

```text
2 <= sourceContinuationPressureDepthCount
  -> two distinct selected pressure depths exist
```

これは大きい。
しかし、これはまだ

```text
two independent budgets exist
```

ではない。

ここを明確に分けたのが非常に良い。
もしここで budget を足し始めていたら、Python 観測が示した overlap 構造に反して危ない道へ入っていた。

## 3.3. `HasDepthTwoDelayedBudget` の predicate 化も良い

今回、

```lean
HasDepthTwoDelayedBudget
hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
```

も入っている。

これは checkpoint `121` の budget pair を短い proposition として扱えるようにしたものじゃ。

これも正しい。
今後、budget theorem が増えると、毎回長い inequality を持ち歩くのは苦しくなる。

```text
HasDepthTwoDelayedBudget n k
```

としてまとめておくことで、後続の会計補題が読みやすくなる。

## 3.4. overlap scan はかなり重要

今回の Python scan は、ただの補助ではなく、次の形式化方針を決める材料になっている。

観測結果は、

```text
rows with at least two selected depths: 52
rows with a disjoint selected-depth pair: 0
rows where every selected-depth pair overlaps: 52
max selected depth count: 6
max pairwise overlap: 13
```

じゃ。

これはかなりはっきりしている。

選ばれた depths は、バラバラの carrier ではなく、同じ all-ones cylinder の階層を共有している可能性が高い。

したがって次は、

```text
DisjointTowerTargets
```

より先に、

```text
NestedSelectedPressureDepths
```

または、

```text
SelectedDepthOverlapControlled
```

を作るのが自然じゃ。

## 4. 数学的解説

ここで、なぜ selected continuation sets が重なりやすいのかを数論的に見る。

depth \(d\) の continuation channel は、概念的には

```text
q_i ≡ 2^(d+1) - 1 mod 2^(d+1)
```

という all-ones residue class じゃ。

たとえば、

```text
depth 2:
  q_i ≡ 7 mod 8

depth 3:
  q_i ≡ 15 mod 16

depth 4:
  q_i ≡ 31 mod 32
```

になる。

ここで、

```text
q_i ≡ 31 mod 32
```

なら、当然

```text
q_i ≡ 15 mod 16
```

でもあり、

```text
q_i ≡ 7 mod 8
```

でもある。

つまり深い continuation channel は浅い continuation channel の部分集合になる。

構造としては、

```text
C_4 ⊆ C_3 ⊆ C_2
```

のような入れ子じゃ。

だから selected depths が複数あるとき、それらの continuation index sets は disjoint ではなく、むしろ重なりやすい。

Python が disjoint pair 0 を出したのは、かなり自然な挙動じゃ。

## 5. 深い推論：次は「加算」ではなく「入れ子会計」

ここが一番大事じゃ。

今までの直感では、

```text
selected depth が多い
  -> budget entry が多い
  -> sumS にたくさん課金できる
```

と期待したくなる。

しかし overlap scan を見ると、そうではなさそうじゃ。

正しくは、

```text
selected depth が多い
  -> all-ones cylinder の深い階層まで pressure が続いている
  -> mass が細い cylinder へ入れ子状に残っている
```

と読むべき。

つまり、複数 selected depths は「複数の独立予算」ではなく、

```text
同じ mass が、より深い解像度でも continuation として残っている
```

ことを示している可能性が高い。

これは悪いことではない。
むしろ、tower の方向性と完全に合っている。

```text
level 1 remainder:
  7 mod 8

level 2 remainder:
  15 mod 16

level 3 remainder:
  31 mod 32

level 4 remainder:
  63 mod 64
```

selected depths が連続して出るのは、mass がこの tower を深く進んでいるサインかもしれない。

だから次は、

```text
selected depths を足す
```

ではなく、

```text
selected depths の入れ子を使って、deep remainder を制御する
```

方向がよい。

## 6. 今回閉じたもの

今回閉じたものは次の五つ。

```text
1. selected pressure depth の predicate 化

2. pressure range から selected pressure depth への bridge

3. selected pressure depth から positive continuation mass への bridge

4. pressureDepthCount >= 2 から two distinct selected witnesses の抽出

5. depth-two delayed budget の predicate 化
```

さらに Python 側で、

```text
selected continuation index sets は、少なくとも default sample では全 pair overlap
```

という重要な観測を得た。

## 7. まだ閉じていないもの

未完の本命はこれじゃ。

```text
selected depths の overlap / nesting を Lean 側でどう表すか
```

候補は三つある。

```text
1. continuation channels are nested by depth

2. selected depths with d1 < d2 have continuation set at d2 contained in continuation set at d1

3. selected-depth overlap is not an accident, but all-ones residue の単調性から出る
```

この中で、最初に狙うべきは 1。

つまり、

```text
深い all-ones residue は浅い all-ones residue に含まれる
```

を Lean で固定することじゃ。

これが通れば、Python の overlap 観測に理論的説明がつく。

## 8. 次の指示

## 8.1. まず continuation channel の入れ子 lemma を作る

次に狙うべきは、選択 depth ではなく、もっと基本の residue lemma じゃ。

```lean
theorem allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
    (q d e : ℕ)
    (hde : d ≤ e)
    (h : q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1) :
    q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 := by
  sorry
```

これはおそらく少し難しいが、方向は明確。

読みは、

```text
q が深い all-ones cylinder に入っているなら、
q は浅い all-ones cylinder にも入っている
```

じゃ。

既存に `mod_eq_mod_of_dvd_modulus` 系があるなら、それを使える可能性が高い。

## 8.2. continuation mass の深さ単調性を作る

次に count 版。

```lean
theorem sourceContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2 n k e ≤
      orbitWindowContinuationSiblingMassPow2 n k d := by
  -- deeper continuation residue class is included in shallower one
  sorry
```

名前は `anti_mono_depth` がよい。
depth が深くなるほど、mass は小さくなる方向じゃ。

tail 版も欲しい。

```lean
theorem tailContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2Tail n k e ≤
      orbitWindowContinuationSiblingMassPow2Tail n k d := by
  sorry
```

## 8.3. overlap is automatic を theorem 化する

selected depths `j₁ < j₂` のとき、continuation set は入れ子になる。
まずは count で表すなら、

```lean
theorem selectedContinuationMass_nested_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂) :
    orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
      orbitWindowContinuationSiblingMassPow2 n k (r + j₁) := by
  apply sourceContinuationMass_anti_mono_depth
  omega
```

これが通れば、Python の「disjoint pair 0」に理論的背景ができる。

## 9. 一歩先ゆく推論

入れ子が分かると、次に見えるのはこれじゃ。

```text
many selected depths
  -> independent budgets ではない
  -> deepest selected depth が最も細い continuation core
```

つまり、複数 selected depths をまとめるなら、足し算ではなく、

```text
max selected depth
```

を見る方がよいかもしれない。

たとえば selected depths が、

```text
2;3;4;5;6;7
```

なら、それを六個の独立 budget と読むのではなく、

```text
depth 7 まで all-ones continuation core が残っている
```

と読む。

これは tower と完全に一致する。

したがって、次の概念は、

```lean
def MaxSelectedSourcePressureDepth ...
```

または、

```lean
def DeepestSelectedSourcePressureDepth ...
```

が候補になる。

ただし、いきなり max を作ると Finset 周りが重くなる。
まずは existential で十分。

```text
pressureDepthCount >= m
  -> m 個の selected depths がある
```

より、

```text
there exists a selected depth at least r + m
```

が言えるかを観測したい。

ただしこれは一般には成り立たない可能性がある。
Python で selected depths が多くの場合 `2;3;4;...` と連続しているなら、狙う価値がある。

## 10. さらなる次の一手

次の Python 実験は、overlap から一歩進めて、

```text
selected depths are consecutive?
```

を観測するのがよい。

今回の top samples は、

```text
511: 2;3;4;5;6;7
681: 2;3;4;5;6;7
255: 2;3;4;5;6
```

のように、かなり連続している。

なので次は、

```text
selected_depths_are_prefix
selected_depths_are_consecutive
max_selected_depth
missing_selected_depths
```

を Python に出す。

もし selected depths が多くの場合、

```text
2, 3, 4, ..., D
```

の prefix なら、Lean 側では、

```text
SelectedPressurePrefix
```

を作る価値がある。

これは disjointness よりはるかに自然じゃ。

## 11. 賢狼が試して欲しい実験補題

## 実験 A: all-ones residue nesting

```lean
theorem allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
    (q d e : ℕ)
    (hde : d ≤ e)
    (h : q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1) :
    q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 := by
  -- q ≡ -1 mod 2^(e+1)
  -- 2^(d+1) ∣ 2^(e+1)
  -- therefore q ≡ -1 mod 2^(d+1)
  sorry
```

## 実験 B: source continuation mass is anti-monotone in depth

```lean
theorem sourceContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2 n k e ≤
      orbitWindowContinuationSiblingMassPow2 n k d := by
  -- unfold counts
  -- pointwise implication by allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
  -- countP monotonicity over List.range
  sorry
```

## 実験 C: tail continuation mass is anti-monotone in depth

```lean
theorem tailContinuationMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowContinuationSiblingMassPow2Tail n k e ≤
      orbitWindowContinuationSiblingMassPow2Tail n k d := by
  -- same as source, but shifted-tail label i+1
  sorry
```

## 実験 D: selected depth continuation carriers are nested

```lean
theorem selectedContinuationMass_nested_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂) :
    orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
      orbitWindowContinuationSiblingMassPow2 n k (r + j₁) := by
  exact sourceContinuationMass_anti_mono_depth n k (r + j₁) (r + j₂) (by omega)
```

## 実験 E: selected depths overlap if deeper mass is positive

もし deeper continuation mass が正なら、浅い側にも含まれる。

```lean
theorem selectedContinuationMass_overlap_of_lt_of_deeper_pos
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂)
    (hpos : 0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₂)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₁) := by
  have hle :
      orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
        orbitWindowContinuationSiblingMassPow2 n k (r + j₁) :=
    selectedContinuationMass_nested_of_lt n k r j₁ j₂ hlt
  omega
```

これは overlap そのものではないが、「深い selected carrier が非空なら浅い carrier も非空」を言う。

## 実験 F: nested pressure depths predicate

```lean
def SelectedDepthsNestedByContinuationMass
    (n : OddNat) (k r : ℕ) (j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ →
    orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
      orbitWindowContinuationSiblingMassPow2 n k (r + j₁)
```

そして、

```lean
theorem selectedDepthsNestedByContinuationMass_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ) :
    SelectedDepthsNestedByContinuationMass n k r j₁ j₂ := by
  intro hlt
  exact selectedContinuationMass_nested_of_lt n k r j₁ j₂ hlt
```

## 実験 G: Python 側で consecutive selected depths scan

Python に次の列を追加。

```text
selected_depths
is_consecutive
starts_at_r_start
max_selected_depth
selected_span
missing_depths
```

観測目的は、

```text
selected depths が prefix か？
selected depths が連続区間か？
```

を確認すること。

## 実験 H: selected prefix predicate の仮定形

Lean 側ではまだ証明しなくてよいが、名前だけ考えるなら：

```lean
def SelectedSourcePressureDepthPrefix
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m ≤ len ∧
    ∀ j, j < m → IsSourcePressureDepth n k r j
```

この predicate が使えそうなら、次に、

```lean
theorem selectedPrefix_gives_deepest_selected
    (n : OddNat) (k r len m : ℕ)
    (h : SelectedSourcePressureDepthPrefix n k r len m)
    (hm : 0 < m) :
    IsSourcePressureDepth n k r (m - 1) := by
  -- unfold and use h
  sorry
```

を作れる。

## 12. 次コミットの推奨順

```text
1. allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le を試す

2. sourceContinuationMass_anti_mono_depth を試す

3. tailContinuationMass_anti_mono_depth を試す

4. selectedContinuationMass_nested_of_lt を追加

5. selectedContinuationMass_overlap_of_lt_of_deeper_pos を追加

6. Python overlap scan に consecutive / prefix columns を追加

7. SelectedSourcePressureDepthPrefix を docs で概念整理

8. Lean では SelectedDepthsNestedByContinuationMass の薄い predicate を追加

9. docs:
   SelectedPressureDepths から NestedSelectedPressureDepths へ接続
```

## 13. 総括

checkpoint `122` は、かなり良い。

two witnesses が取れた。
しかし Python は disjoint pair が 0 だと教えてくれた。

これは失敗ではない。
むしろ、正しい構造が見えた。

```text
selected depths は独立ではない。
all-ones continuation cylinder の入れ子である。
```

したがって次は、multi-budget summation ではなく、

```text
nested selected pressure depths
```

を形式化するべきじゃ。

賢狼の結論はこう。

```text
足すな。
入れ子を見よ。
深い selected depth は浅い selected depth の中にいる。
```

ここを Lean で固定できれば、overlap scan の観測が単なる実験ではなく、tower 会計の理論的土台になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 134338ee..4e39d80c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -6348,6 +6348,35 @@ theorem sourceContinuationMass_pos_of_pressureOnRange_at
   sourceContinuationMass_pos_of_localPressure n k (r + j)
     (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)
 
+/--
+A selected source pressure depth inside a depth range.
+
+This predicate packages the local `MoreThanHalf` statement so later accounting
+lemmas can talk about selected depths without repeating the mass expressions.
+-/
+def IsSourcePressureDepth
+    (n : OddNat) (k r : ℕ) (j : ℕ) : Prop :=
+  MoreThanHalf
+    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+    (orbitWindowRetentionMassPow2 n k (r + j))
+
+/-- Range pressure marks every in-range depth as a selected source pressure depth. -/
+theorem isSourcePressureDepth_of_pressureOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : SourceContinuationPressureOnRange n k r len)
+    (hj : j < len) :
+    IsSourcePressureDepth n k r j := by
+  unfold IsSourcePressureDepth
+  exact sourcePressureAtDepth_of_pressureOnRange n k r len j h hj
+
+/-- A selected source pressure depth has positive source continuation mass. -/
+theorem positive_sourceContinuationMass_of_isSourcePressureDepth
+    (n : OddNat) (k r j : ℕ)
+    (h : IsSourcePressureDepth n k r j) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
+  unfold IsSourcePressureDepth at h
+  exact sourceContinuationMass_pos_of_localPressure n k (r + j) h
+
 /--
 Positive source pressure-depth count selects at least one local pressure depth.
 
@@ -6398,6 +6427,119 @@ theorem exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
     ⟨j, hj, hpressure⟩
   exact ⟨j, hj, sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩
 
+/-- Positive pressure-depth count selects a packaged pressure-depth witness. -/
+theorem exists_isSourcePressureDepth_of_pressureDepthCount_pos
+    (n : OddNat) (k r len : ℕ)
+    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
+    ∃ j, j < len ∧ IsSourcePressureDepth n k r j := by
+  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
+    ⟨j, hj, hpressure⟩
+  exact ⟨j, hj, hpressure⟩
+
+/--
+Positive pressure-depth count selects a packaged pressure-depth witness together
+with its positive source continuation mass.
+-/
+theorem exists_isSourcePressureDepth_with_positive_mass
+    (n : OddNat) (k r len : ℕ)
+    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
+    ∃ j, j < len ∧
+      IsSourcePressureDepth n k r j ∧
+      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
+  rcases exists_isSourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
+    ⟨j, hj, hpressure⟩
+  exact ⟨j, hj, hpressure,
+    positive_sourceContinuationMass_of_isSourcePressureDepth n k r j hpressure⟩
+
+/--
+Two selected source pressure depths exist when the pressure-depth count is at
+least two.
+
+This theorem only extracts distinct witnesses.  It intentionally does not say
+that their delayed-budget contributions are independent.
+-/
+theorem exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+    (n : OddNat) (k r len : ℕ)
+    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
+    ∃ j₁ j₂,
+      j₁ < len ∧
+      j₂ < len ∧
+      j₁ ≠ j₂ ∧
+      IsSourcePressureDepth n k r j₁ ∧
+      IsSourcePressureDepth n k r j₂ := by
+  classical
+  unfold sourceContinuationPressureDepthCount at hcount
+  induction len with
+  | zero =>
+      simp at hcount
+  | succ len ih =>
+      rw [List.range_succ] at hcount
+      by_cases hlast : IsSourcePressureDepth n k r len
+      · have hlast' :
+            MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+              (orbitWindowRetentionMassPow2 n k (r + len)) := by
+          simpa [IsSourcePressureDepth] using hlast
+        by_cases hprevpos :
+            0 <
+              (List.range len).countP
+                (fun j =>
+                  decide
+                    (MoreThanHalf
+                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+                      (orbitWindowRetentionMassPow2 n k (r + j))))
+        · rcases exists_isSourcePressureDepth_of_pressureDepthCount_pos
+            n k r len hprevpos with ⟨j, hj, hpressure⟩
+          exact ⟨j, len, by omega, by omega, by omega, hpressure, hlast⟩
+        · have hprevzero :
+              (List.range len).countP
+                (fun j =>
+                  decide
+                    (MoreThanHalf
+                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+                      (orbitWindowRetentionMassPow2 n k (r + j)))) = 0 :=
+            Nat.eq_zero_of_not_pos hprevpos
+          simp [hlast', hprevzero] at hcount
+      · have hlast' :
+            ¬ MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+              (orbitWindowRetentionMassPow2 n k (r + len)) := by
+          intro h
+          exact hlast (by simpa [IsSourcePressureDepth] using h)
+        have hprev :
+            2 ≤
+              (List.range len).countP
+                (fun j =>
+                  decide
+                    (MoreThanHalf
+                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+                      (orbitWindowRetentionMassPow2 n k (r + j)))) := by
+          simpa [hlast'] using hcount
+        rcases ih hprev with ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩
+        exact ⟨j₁, j₂, by omega, by omega, hne, hp₁, hp₂⟩
+
+/--
+Unpack the two-witness theorem into the original `MoreThanHalf` spelling.
+
+This theorem is useful for callers that do not yet use the packaged predicate.
+-/
+theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+    (n : OddNat) (k r len : ℕ)
+    (hcount : 2 ≤ sourceContinuationPressureDepthCount n k r len) :
+    ∃ j₁ j₂,
+      j₁ < len ∧
+      j₂ < len ∧
+      j₁ ≠ j₂ ∧
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k (r + j₁))
+        (orbitWindowRetentionMassPow2 n k (r + j₁)) ∧
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k (r + j₂))
+        (orbitWindowRetentionMassPow2 n k (r + j₂)) := by
+  rcases exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+    n k r len hcount with ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩
+  exact ⟨j₁, j₂, hj₁, hj₂, hne, hp₁, hp₂⟩
+
 /--
 Source cause-side outruns-heavy pressure yields a concrete positive source
 continuation mass at some selected depth.
@@ -6510,6 +6652,27 @@ theorem exists_depth_two_budget_of_pressureOnRange_two_one
           orbitWindowResidueCountMod8EqSevenTail n k :=
   depthTwoPressureRange_positive_and_budget n k h
 
+/--
+Depth-two delayed budget predicate.
+
+This packages the positive mass and delayed-budget inequality as a reusable
+property for later multi-witness accounting experiments.
+-/
+def HasDepthTwoDelayedBudget
+    (n : OddNat) (k : ℕ) : Prop :=
+  0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
+    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+      sumS n ((k + 1) + 1) +
+        orbitWindowResidueCountMod8EqSevenTail n k
+
+/-- Depth-two one-range pressure supplies a packaged delayed budget. -/
+theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
+    (n : OddNat) (k : ℕ)
+    (h : SourceContinuationPressureOnRange n k 2 1) :
+    HasDepthTwoDelayedBudget n k := by
+  unfold HasDepthTwoDelayedBudget
+  exact depthTwoPressureRange_positive_and_budget n k h
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 0760fbe4..222d6fd9 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -156,6 +156,7 @@ docs/Collatz-Level3PressureEntrance-118.md
 docs/Collatz-Level4GenericPressure-119.md
 docs/Collatz-Level5AndModScan-120.md
 docs/Collatz-SelectedWitnessBudget-121.md
+docs/Collatz-SelectedPressureDepths-122.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index e7ce0742..e8eca3dc 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1262,3 +1262,39 @@ python/Collatz/PetalBridge/orbit_pressure_remainder_scan.py
 records pressure witnesses and L1..L5 delayed remainders on concrete orbit
 windows.  Its results are experimental and should be used to choose the next
 formal theorem, not as proof.
+
+## Selected Pressure Depths
+
+Checkpoint 122 packages the local pressure condition:
+
+```lean
+IsSourcePressureDepth
+```
+
+and provides witness extractors:
+
+```lean
+exists_isSourcePressureDepth_of_pressureDepthCount_pos
+exists_isSourcePressureDepth_with_positive_mass
+exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+The two-witness theorem deliberately says only:
+
+```text
+two distinct selected pressure depths exist
+```
+
+It does not add their budget contributions.
+
+The new overlap scan:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+```
+
+observed no disjoint selected-depth pair in the default finite sample.  This
+suggests that selected continuation sets are often nested or overlapping, so a
+future multi-budget theorem probably needs an explicit overlap-control or
+nested-accounting predicate before it can sum budgets.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d63d9df4..c4a1516d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -1555,3 +1555,59 @@ rows with L5 remainder: 18
 max pressure depth count: 6
 max L5 remainder: 3
 ```
+
+## Checkpoint 122: Selected Pressure Depths And Overlap Scan
+
+Checkpoint 122 packages selected local pressure depths:
+
+```lean
+IsSourcePressureDepth
+isSourcePressureDepth_of_pressureOnRange
+positive_sourceContinuationMass_of_isSourcePressureDepth
+```
+
+Positive count and positive mass witness helpers:
+
+```lean
+exists_isSourcePressureDepth_of_pressureDepthCount_pos
+exists_isSourcePressureDepth_with_positive_mass
+```
+
+Two-witness extraction:
+
+```lean
+exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+These theorems extract distinct selected pressure-depth witnesses only.  They
+make no multi-budget independence claim.
+
+Depth-two budget predicate:
+
+```lean
+HasDepthTwoDelayedBudget
+hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
+```
+
+New Python overlap scan:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+```
+
+Default observation:
+
+```text
+rows: 500
+rows with at least two selected depths: 52
+rows with a disjoint selected-depth pair: 0
+rows where every selected-depth pair overlaps: 52
+max selected depth count: 6
+max pairwise overlap: 13
+```
+
+This suggests that the next formal predicate should probably describe
+overlap/nesting control, not assume selected depths are independent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md
new file mode 100644
index 00000000..6c1845b8
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md
@@ -0,0 +1,164 @@
+# Collatz Selected Pressure Depths 122
+
+Checkpoint 122 turns "selected pressure depth" into an explicit Lean concept
+and proves the safe two-witness theorem.
+
+The key point is negative discipline:
+
+```text
+two selected witnesses exist
+  does not mean
+two independent delayed budgets exist
+```
+
+## Selected Pressure Predicate
+
+New predicate:
+
+```lean
+IsSourcePressureDepth
+```
+
+Definition reading:
+
+```text
+j is selected when source continuation at depth r+j occupies
+more than half of source retention at that depth.
+```
+
+Basic bridge:
+
+```lean
+isSourcePressureDepth_of_pressureOnRange
+positive_sourceContinuationMass_of_isSourcePressureDepth
+```
+
+Meaning:
+
+```text
+range pressure + j < len
+  -> IsSourcePressureDepth n k r j
+  -> positive source continuation mass at depth r+j
+```
+
+## Witness Extraction
+
+Positive count now has predicate-facing witnesses:
+
+```lean
+exists_isSourcePressureDepth_of_pressureDepthCount_pos
+exists_isSourcePressureDepth_with_positive_mass
+```
+
+The first theorem packages the selected local pressure condition.
+The second carries the positive mass together with it.
+
+## Two Witnesses
+
+New safe theorem:
+
+```lean
+exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+Caller-facing unpacked spelling:
+
+```lean
+exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+Reading:
+
+```text
+2 <= sourceContinuationPressureDepthCount n k r len
+  -> two distinct selected pressure depths exist
+```
+
+No budget addition is claimed.
+
+## Depth-Two Budget Predicate
+
+Checkpoint 121 had:
+
+```lean
+depthTwoPressureRange_positive_and_budget
+```
+
+Checkpoint 122 packages this as:
+
+```lean
+HasDepthTwoDelayedBudget
+hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
+```
+
+This gives later accounting the short proposition:
+
+```text
+HasDepthTwoDelayedBudget n k
+```
+
+instead of carrying the whole positive-mass and inequality pair by hand.
+
+## Python Overlap Scan
+
+New script:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+```
+
+Default command:
+
+```text
+python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+```
+
+Observed summary:
+
+```text
+rows: 500
+rows with at least two selected depths: 52
+rows with a disjoint selected-depth pair: 0
+rows where every selected-depth pair overlaps: 52
+max selected depth count: 6
+max pairwise overlap: 13
+```
+
+## Interpretation
+
+The finite observation strongly suggests that selected depths often form nested
+or overlapping continuation-index sets.
+
+This means the next multi-budget theorem should not start from:
+
+```text
+selected depths are automatically independent
+```
+
+The safer next vocabulary is:
+
+```text
+SelectedDepthOverlapControlled
+NestedSelectedPressureDepths
+DisjointTowerTargets, only under an explicit disjointness hypothesis
+```
+
+## Next Work
+
+The next checkpoint should choose one of two routes:
+
+```text
+1. prove a thin overlap predicate API
+2. keep one-witness delayed budget and search for an iterative obstruction
+```
+
+The Python scan currently favors route 1: overlap/nesting is visible and should
+be named before any budget summation theorem is attempted.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-122.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-122.md
new file mode 100644
index 00000000..763fe2d5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-122.md
@@ -0,0 +1,214 @@
+# Report Petal 122
+
+## Summary
+
+Checkpoint 122 formalizes selected source pressure depths and proves the safe
+two-witness theorem:
+
+```text
+2 <= sourceContinuationPressureDepthCount
+  -> two distinct selected pressure depths exist
+```
+
+It deliberately does not sum delayed budgets.
+
+The Python side now measures overlap between selected continuation-index sets.
+The default scan found no disjoint selected-depth pair in the finite sample.
+
+## Lean Changes
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+## Selected Pressure Predicate
+
+Added:
+
+```lean
+def IsSourcePressureDepth
+```
+
+Meaning:
+
+```text
+IsSourcePressureDepth n k r j
+```
+
+is the local `MoreThanHalf` source continuation pressure at depth `r + j`.
+
+Basic API:
+
+```lean
+isSourcePressureDepth_of_pressureOnRange
+positive_sourceContinuationMass_of_isSourcePressureDepth
+```
+
+## Witness Extraction
+
+Added:
+
+```lean
+exists_isSourcePressureDepth_of_pressureDepthCount_pos
+exists_isSourcePressureDepth_with_positive_mass
+```
+
+These wrap the checkpoint 120 witness theorem in the new predicate vocabulary.
+
+## Two Witnesses
+
+Added:
+
+```lean
+exists_two_isSourcePressureDepths_of_two_le_pressureDepthCount
+exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+The first theorem returns two distinct packaged selected-depth witnesses.
+The second theorem unpacks them into the original `MoreThanHalf` spelling.
+
+No budget independence is asserted.
+
+## Depth-Two Budget Predicate
+
+Added:
+
+```lean
+def HasDepthTwoDelayedBudget
+theorem hasDepthTwoDelayedBudget_of_pressureOnRange_two_one
+```
+
+This packages the checkpoint 121 depth-two positive budget pair as a reusable
+proposition.
+
+## Python Experiment
+
+New script:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+```
+
+Command:
+
+```text
+python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+```
+
+Observed summary:
+
+```text
+rows: 500
+rows with at least two selected depths: 52
+rows with a disjoint selected-depth pair: 0
+rows where every selected-depth pair overlaps: 52
+max selected depth count: 6
+max pairwise overlap: 13
+```
+
+Top samples:
+
+```text
+n=511 selected depths 2;3;4;5;6;7
+n=681 selected depths 2;3;4;5;6;7
+n=255 selected depths 2;3;4;5;6
+```
+
+## Interpretation
+
+The overlap scan is important.  In this finite observation, selected pressure
+depths did not produce disjoint continuation-index sets.  This suggests that
+selected depths should be treated as nested or overlapping unless a future
+hypothesis proves otherwise.
+
+The next formal object should probably not be:
+
+```text
+many witnesses -> many independent budgets
+```
+
+but rather one of:
+
+```text
+SelectedDepthOverlapControlled
+NestedSelectedPressureDepths
+DisjointTowerTargets under an explicit hypothesis
+```
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-SelectedPressureDepths-122.md
+```
+
+## Verification
+
+Passed:
+
+```text
+python3 python/Collatz/PetalBridge/selected_depth_overlap_scan.py \
+  --max-n 999 --steps 64 --r-start 2 --depth-len 8
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched checkpoint 122 files>
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
+The next checkpoint should not sum budgets yet.
+
+A safe next theorem family is:
+
+```lean
+def SelectedDepthContinuationIndices ...
+def SelectedDepthsOverlap ...
+def SelectedDepthsDisjoint ...
+```
+
+or a Lean-only thin predicate:
+
+```lean
+def SelectedSourcePressureDepthsPairwiseDisjoint
+    (n : OddNat) (k r : ℕ) (js : Finset ℕ) : Prop := ...
+```
+
+Then prove only introductory facts:
+
+```text
+disjointness is symmetric
+disjoint selected depths have no shared index
+two-witness theorem plus disjointness hypothesis gives two non-overlapping
+carrier sets
+```
+
+Only after that should a summed delayed-budget theorem be attempted.
diff --git a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
new file mode 100644
index 00000000..67fa090c
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
@@ -0,0 +1,501 @@
+n,steps,r_start,depth_len,selected_depths,selected_count,max_pairwise_overlap,min_pairwise_overlap,total_pair_count,disjoint_pair_count,has_disjoint_pair,first_pair,first_pair_overlap,first_pair_left_mass,first_pair_right_mass
+1,64,2,8,,0,0,0,0,0,False,,0,0,0
+3,64,2,8,,0,0,0,0,0,False,,0,0,0
+5,64,2,8,,0,0,0,0,0,False,,0,0,0
+7,64,2,8,,0,0,0,0,0,False,,0,0,0
+9,64,2,8,,0,0,0,0,0,False,,0,0,0
+11,64,2,8,,0,0,0,0,0,False,,0,0,0
+13,64,2,8,,0,0,0,0,0,False,,0,0,0
+15,64,2,8,2,1,0,0,0,0,False,,0,0,0
+17,64,2,8,,0,0,0,0,0,False,,0,0,0
+19,64,2,8,,0,0,0,0,0,False,,0,0,0
+21,64,2,8,,0,0,0,0,0,False,,0,0,0
+23,64,2,8,,0,0,0,0,0,False,,0,0,0
+25,64,2,8,,0,0,0,0,0,False,,0,0,0
+27,64,2,8,2,1,0,0,0,0,False,,0,0,0
+29,64,2,8,,0,0,0,0,0,False,,0,0,0
+31,64,2,8,2,1,0,0,0,0,False,,0,0,0
+33,64,2,8,,0,0,0,0,0,False,,0,0,0
+35,64,2,8,,0,0,0,0,0,False,,0,0,0
+37,64,2,8,,0,0,0,0,0,False,,0,0,0
+39,64,2,8,,0,0,0,0,0,False,,0,0,0
+41,64,2,8,2,1,0,0,0,0,False,,0,0,0
+43,64,2,8,,0,0,0,0,0,False,,0,0,0
+45,64,2,8,,0,0,0,0,0,False,,0,0,0
+47,64,2,8,2,1,0,0,0,0,False,,0,0,0
+49,64,2,8,,0,0,0,0,0,False,,0,0,0
+51,64,2,8,,0,0,0,0,0,False,,0,0,0
+53,64,2,8,,0,0,0,0,0,False,,0,0,0
+55,64,2,8,2,1,0,0,0,0,False,,0,0,0
+57,64,2,8,,0,0,0,0,0,False,,0,0,0
+59,64,2,8,,0,0,0,0,0,False,,0,0,0
+61,64,2,8,,0,0,0,0,0,False,,0,0,0
+63,64,2,8,2;3,2,8,8,1,0,False,2:3,8,15,8
+65,64,2,8,,0,0,0,0,0,False,,0,0,0
+67,64,2,8,,0,0,0,0,0,False,,0,0,0
+69,64,2,8,,0,0,0,0,0,False,,0,0,0
+71,64,2,8,2,1,0,0,0,0,False,,0,0,0
+73,64,2,8,2,1,0,0,0,0,False,,0,0,0
+75,64,2,8,,0,0,0,0,0,False,,0,0,0
+77,64,2,8,,0,0,0,0,0,False,,0,0,0
+79,64,2,8,,0,0,0,0,0,False,,0,0,0
+81,64,2,8,,0,0,0,0,0,False,,0,0,0
+83,64,2,8,2,1,0,0,0,0,False,,0,0,0
+85,64,2,8,,0,0,0,0,0,False,,0,0,0
+87,64,2,8,,0,0,0,0,0,False,,0,0,0
+89,64,2,8,,0,0,0,0,0,False,,0,0,0
+91,64,2,8,2,1,0,0,0,0,False,,0,0,0
+93,64,2,8,,0,0,0,0,0,False,,0,0,0
+95,64,2,8,2,1,0,0,0,0,False,,0,0,0
+97,64,2,8,2,1,0,0,0,0,False,,0,0,0
+99,64,2,8,,0,0,0,0,0,False,,0,0,0
+101,64,2,8,,0,0,0,0,0,False,,0,0,0
+103,64,2,8,2,1,0,0,0,0,False,,0,0,0
+105,64,2,8,,0,0,0,0,0,False,,0,0,0
+107,64,2,8,2,1,0,0,0,0,False,,0,0,0
+109,64,2,8,2,1,0,0,0,0,False,,0,0,0
+111,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+113,64,2,8,,0,0,0,0,0,False,,0,0,0
+115,64,2,8,,0,0,0,0,0,False,,0,0,0
+117,64,2,8,,0,0,0,0,0,False,,0,0,0
+119,64,2,8,,0,0,0,0,0,False,,0,0,0
+121,64,2,8,2,1,0,0,0,0,False,,0,0,0
+123,64,2,8,,0,0,0,0,0,False,,0,0,0
+125,64,2,8,2,1,0,0,0,0,False,,0,0,0
+127,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+129,64,2,8,2,1,0,0,0,0,False,,0,0,0
+131,64,2,8,,0,0,0,0,0,False,,0,0,0
+133,64,2,8,,0,0,0,0,0,False,,0,0,0
+135,64,2,8,,0,0,0,0,0,False,,0,0,0
+137,64,2,8,2,1,0,0,0,0,False,,0,0,0
+139,64,2,8,,0,0,0,0,0,False,,0,0,0
+141,64,2,8,,0,0,0,0,0,False,,0,0,0
+143,64,2,8,2,1,0,0,0,0,False,,0,0,0
+145,64,2,8,2,1,0,0,0,0,False,,0,0,0
+147,64,2,8,2,1,0,0,0,0,False,,0,0,0
+149,64,2,8,,0,0,0,0,0,False,,0,0,0
+151,64,2,8,,0,0,0,0,0,False,,0,0,0
+153,64,2,8,,0,0,0,0,0,False,,0,0,0
+155,64,2,8,2,1,0,0,0,0,False,,0,0,0
+157,64,2,8,,0,0,0,0,0,False,,0,0,0
+159,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+161,64,2,8,2,1,0,0,0,0,False,,0,0,0
+163,64,2,8,,0,0,0,0,0,False,,0,0,0
+165,64,2,8,2,1,0,0,0,0,False,,0,0,0
+167,64,2,8,2,1,0,0,0,0,False,,0,0,0
+169,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+171,64,2,8,2,1,0,0,0,0,False,,0,0,0
+173,64,2,8,,0,0,0,0,0,False,,0,0,0
+175,64,2,8,2,1,0,0,0,0,False,,0,0,0
+177,64,2,8,,0,0,0,0,0,False,,0,0,0
+179,64,2,8,,0,0,0,0,0,False,,0,0,0
+181,64,2,8,,0,0,0,0,0,False,,0,0,0
+183,64,2,8,2,1,0,0,0,0,False,,0,0,0
+185,64,2,8,,0,0,0,0,0,False,,0,0,0
+187,64,2,8,,0,0,0,0,0,False,,0,0,0
+189,64,2,8,2,1,0,0,0,0,False,,0,0,0
+191,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
+193,64,2,8,2,1,0,0,0,0,False,,0,0,0
+195,64,2,8,2,1,0,0,0,0,False,,0,0,0
+197,64,2,8,,0,0,0,0,0,False,,0,0,0
+199,64,2,8,2,1,0,0,0,0,False,,0,0,0
+201,64,2,8,,0,0,0,0,0,False,,0,0,0
+203,64,2,8,,0,0,0,0,0,False,,0,0,0
+205,64,2,8,,0,0,0,0,0,False,,0,0,0
+207,64,2,8,2,1,0,0,0,0,False,,0,0,0
+209,64,2,8,,0,0,0,0,0,False,,0,0,0
+211,64,2,8,,0,0,0,0,0,False,,0,0,0
+213,64,2,8,,0,0,0,0,0,False,,0,0,0
+215,64,2,8,2,1,0,0,0,0,False,,0,0,0
+217,64,2,8,,0,0,0,0,0,False,,0,0,0
+219,64,2,8,,0,0,0,0,0,False,,0,0,0
+221,64,2,8,2,1,0,0,0,0,False,,0,0,0
+223,64,2,8,2;3,2,6,6,1,0,False,2:3,6,10,6
+225,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+227,64,2,8,,0,0,0,0,0,False,,0,0,0
+229,64,2,8,,0,0,0,0,0,False,,0,0,0
+231,64,2,8,2,1,0,0,0,0,False,,0,0,0
+233,64,2,8,2,1,0,0,0,0,False,,0,0,0
+235,64,2,8,2,1,0,0,0,0,False,,0,0,0
+237,64,2,8,,0,0,0,0,0,False,,0,0,0
+239,64,2,8,2,1,0,0,0,0,False,,0,0,0
+241,64,2,8,,0,0,0,0,0,False,,0,0,0
+243,64,2,8,2,1,0,0,0,0,False,,0,0,0
+245,64,2,8,,0,0,0,0,0,False,,0,0,0
+247,64,2,8,,0,0,0,0,0,False,,0,0,0
+249,64,2,8,,0,0,0,0,0,False,,0,0,0
+251,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+253,64,2,8,2,1,0,0,0,0,False,,0,0,0
+255,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,6,5
+257,64,2,8,2,1,0,0,0,0,False,,0,0,0
+259,64,2,8,2,1,0,0,0,0,False,,0,0,0
+261,64,2,8,,0,0,0,0,0,False,,0,0,0
+263,64,2,8,2,1,0,0,0,0,False,,0,0,0
+265,64,2,8,2,1,0,0,0,0,False,,0,0,0
+267,64,2,8,,0,0,0,0,0,False,,0,0,0
+269,64,2,8,,0,0,0,0,0,False,,0,0,0
+271,64,2,8,,0,0,0,0,0,False,,0,0,0
+273,64,2,8,,0,0,0,0,0,False,,0,0,0
+275,64,2,8,2,1,0,0,0,0,False,,0,0,0
+277,64,2,8,,0,0,0,0,0,False,,0,0,0
+279,64,2,8,,0,0,0,0,0,False,,0,0,0
+281,64,2,8,,0,0,0,0,0,False,,0,0,0
+283,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+285,64,2,8,2,1,0,0,0,0,False,,0,0,0
+287,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
+289,64,2,8,,0,0,0,0,0,False,,0,0,0
+291,64,2,8,2,1,0,0,0,0,False,,0,0,0
+293,64,2,8,2,1,0,0,0,0,False,,0,0,0
+295,64,2,8,,0,0,0,0,0,False,,0,0,0
+297,64,2,8,2;3,2,6,6,1,0,False,2:3,6,10,6
+299,64,2,8,2,1,0,0,0,0,False,,0,0,0
+301,64,2,8,,0,0,0,0,0,False,,0,0,0
+303,64,2,8,2,1,0,0,0,0,False,,0,0,0
+305,64,2,8,,0,0,0,0,0,False,,0,0,0
+307,64,2,8,,0,0,0,0,0,False,,0,0,0
+309,64,2,8,,0,0,0,0,0,False,,0,0,0
+311,64,2,8,2,1,0,0,0,0,False,,0,0,0
+313,64,2,8,2,1,0,0,0,0,False,,0,0,0
+315,64,2,8,,0,0,0,0,0,False,,0,0,0
+317,64,2,8,,0,0,0,0,0,False,,0,0,0
+319,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+321,64,2,8,,0,0,0,0,0,False,,0,0,0
+323,64,2,8,2,1,0,0,0,0,False,,0,0,0
+325,64,2,8,,0,0,0,0,0,False,,0,0,0
+327,64,2,8,2,1,0,0,0,0,False,,0,0,0
+329,64,2,8,,0,0,0,0,0,False,,0,0,0
+331,64,2,8,,0,0,0,0,0,False,,0,0,0
+333,64,2,8,2,1,0,0,0,0,False,,0,0,0
+335,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+337,64,2,8,2,1,0,0,0,0,False,,0,0,0
+339,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
+341,64,2,8,,0,0,0,0,0,False,,0,0,0
+343,64,2,8,2,1,0,0,0,0,False,,0,0,0
+345,64,2,8,2,1,0,0,0,0,False,,0,0,0
+347,64,2,8,2,1,0,0,0,0,False,,0,0,0
+349,64,2,8,,0,0,0,0,0,False,,0,0,0
+351,64,2,8,2;3,2,6,6,1,0,False,2:3,6,11,6
+353,64,2,8,2,1,0,0,0,0,False,,0,0,0
+355,64,2,8,,0,0,0,0,0,False,,0,0,0
+357,64,2,8,,0,0,0,0,0,False,,0,0,0
+359,64,2,8,2,1,0,0,0,0,False,,0,0,0
+361,64,2,8,,0,0,0,0,0,False,,0,0,0
+363,64,2,8,,0,0,0,0,0,False,,0,0,0
+365,64,2,8,2,1,0,0,0,0,False,,0,0,0
+367,64,2,8,,0,0,0,0,0,False,,0,0,0
+369,64,2,8,,0,0,0,0,0,False,,0,0,0
+371,64,2,8,,0,0,0,0,0,False,,0,0,0
+373,64,2,8,,0,0,0,0,0,False,,0,0,0
+375,64,2,8,,0,0,0,0,0,False,,0,0,0
+377,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+379,64,2,8,,0,0,0,0,0,False,,0,0,0
+381,64,2,8,2,1,0,0,0,0,False,,0,0,0
+383,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+385,64,2,8,,0,0,0,0,0,False,,0,0,0
+387,64,2,8,2,1,0,0,0,0,False,,0,0,0
+389,64,2,8,2,1,0,0,0,0,False,,0,0,0
+391,64,2,8,2,1,0,0,0,0,False,,0,0,0
+393,64,2,8,,0,0,0,0,0,False,,0,0,0
+395,64,2,8,2,1,0,0,0,0,False,,0,0,0
+397,64,2,8,,0,0,0,0,0,False,,0,0,0
+399,64,2,8,2,1,0,0,0,0,False,,0,0,0
+401,64,2,8,,0,0,0,0,0,False,,0,0,0
+403,64,2,8,,0,0,0,0,0,False,,0,0,0
+405,64,2,8,,0,0,0,0,0,False,,0,0,0
+407,64,2,8,,0,0,0,0,0,False,,0,0,0
+409,64,2,8,,0,0,0,0,0,False,,0,0,0
+411,64,2,8,2,1,0,0,0,0,False,,0,0,0
+413,64,2,8,2,1,0,0,0,0,False,,0,0,0
+415,64,2,8,2,1,0,0,0,0,False,,0,0,0
+417,64,2,8,2,1,0,0,0,0,False,,0,0,0
+419,64,2,8,,0,0,0,0,0,False,,0,0,0
+421,64,2,8,,0,0,0,0,0,False,,0,0,0
+423,64,2,8,,0,0,0,0,0,False,,0,0,0
+425,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+427,64,2,8,,0,0,0,0,0,False,,0,0,0
+429,64,2,8,2,1,0,0,0,0,False,,0,0,0
+431,64,2,8,,0,0,0,0,0,False,,0,0,0
+433,64,2,8,,0,0,0,0,0,False,,0,0,0
+435,64,2,8,,0,0,0,0,0,False,,0,0,0
+437,64,2,8,2,1,0,0,0,0,False,,0,0,0
+439,64,2,8,,0,0,0,0,0,False,,0,0,0
+441,64,2,8,,0,0,0,0,0,False,,0,0,0
+443,64,2,8,,0,0,0,0,0,False,,0,0,0
+445,64,2,8,2,1,0,0,0,0,False,,0,0,0
+447,64,2,8,2;3;4;5,4,9,4,6,0,False,2:3,9,14,9
+449,64,2,8,2,1,0,0,0,0,False,,0,0,0
+451,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+453,64,2,8,,0,0,0,0,0,False,,0,0,0
+455,64,2,8,,0,0,0,0,0,False,,0,0,0
+457,64,2,8,2,1,0,0,0,0,False,,0,0,0
+459,64,2,8,2,1,0,0,0,0,False,,0,0,0
+461,64,2,8,,0,0,0,0,0,False,,0,0,0
+463,64,2,8,2,1,0,0,0,0,False,,0,0,0
+465,64,2,8,,0,0,0,0,0,False,,0,0,0
+467,64,2,8,2,1,0,0,0,0,False,,0,0,0
+469,64,2,8,,0,0,0,0,0,False,,0,0,0
+471,64,2,8,2,1,0,0,0,0,False,,0,0,0
+473,64,2,8,,0,0,0,0,0,False,,0,0,0
+475,64,2,8,,0,0,0,0,0,False,,0,0,0
+477,64,2,8,,0,0,0,0,0,False,,0,0,0
+479,64,2,8,2,1,0,0,0,0,False,,0,0,0
+481,64,2,8,,0,0,0,0,0,False,,0,0,0
+483,64,2,8,,0,0,0,0,0,False,,0,0,0
+485,64,2,8,2,1,0,0,0,0,False,,0,0,0
+487,64,2,8,2,1,0,0,0,0,False,,0,0,0
+489,64,2,8,,0,0,0,0,0,False,,0,0,0
+491,64,2,8,2,1,0,0,0,0,False,,0,0,0
+493,64,2,8,,0,0,0,0,0,False,,0,0,0
+495,64,2,8,2,1,0,0,0,0,False,,0,0,0
+497,64,2,8,,0,0,0,0,0,False,,0,0,0
+499,64,2,8,,0,0,0,0,0,False,,0,0,0
+501,64,2,8,2,1,0,0,0,0,False,,0,0,0
+503,64,2,8,2,1,0,0,0,0,False,,0,0,0
+505,64,2,8,,0,0,0,0,0,False,,0,0,0
+507,64,2,8,,0,0,0,0,0,False,,0,0,0
+509,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
+511,64,2,8,2;3;4;5;6;7,6,6,2,15,0,False,2:3,6,8,6
+513,64,2,8,,0,0,0,0,0,False,,0,0,0
+515,64,2,8,2,1,0,0,0,0,False,,0,0,0
+517,64,2,8,2,1,0,0,0,0,False,,0,0,0
+519,64,2,8,,0,0,0,0,0,False,,0,0,0
+521,64,2,8,2,1,0,0,0,0,False,,0,0,0
+523,64,2,8,2,1,0,0,0,0,False,,0,0,0
+525,64,2,8,,0,0,0,0,0,False,,0,0,0
+527,64,2,8,2,1,0,0,0,0,False,,0,0,0
+529,64,2,8,,0,0,0,0,0,False,,0,0,0
+531,64,2,8,2,1,0,0,0,0,False,,0,0,0
+533,64,2,8,,0,0,0,0,0,False,,0,0,0
+535,64,2,8,,0,0,0,0,0,False,,0,0,0
+537,64,2,8,,0,0,0,0,0,False,,0,0,0
+539,64,2,8,2,1,0,0,0,0,False,,0,0,0
+541,64,2,8,,0,0,0,0,0,False,,0,0,0
+543,64,2,8,2;3,2,9,9,1,0,False,2:3,9,17,9
+545,64,2,8,,0,0,0,0,0,False,,0,0,0
+547,64,2,8,,0,0,0,0,0,False,,0,0,0
+549,64,2,8,2,1,0,0,0,0,False,,0,0,0
+551,64,2,8,,0,0,0,0,0,False,,0,0,0
+553,64,2,8,2,1,0,0,0,0,False,,0,0,0
+555,64,2,8,,0,0,0,0,0,False,,0,0,0
+557,64,2,8,,0,0,0,0,0,False,,0,0,0
+559,64,2,8,,0,0,0,0,0,False,,0,0,0
+561,64,2,8,,0,0,0,0,0,False,,0,0,0
+563,64,2,8,,0,0,0,0,0,False,,0,0,0
+565,64,2,8,,0,0,0,0,0,False,,0,0,0
+567,64,2,8,2,1,0,0,0,0,False,,0,0,0
+569,64,2,8,,0,0,0,0,0,False,,0,0,0
+571,64,2,8,,0,0,0,0,0,False,,0,0,0
+573,64,2,8,2,1,0,0,0,0,False,,0,0,0
+575,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
+577,64,2,8,,0,0,0,0,0,False,,0,0,0
+579,64,2,8,,0,0,0,0,0,False,,0,0,0
+581,64,2,8,2,1,0,0,0,0,False,,0,0,0
+583,64,2,8,,0,0,0,0,0,False,,0,0,0
+585,64,2,8,,0,0,0,0,0,False,,0,0,0
+587,64,2,8,2,1,0,0,0,0,False,,0,0,0
+589,64,2,8,2,1,0,0,0,0,False,,0,0,0
+591,64,2,8,,0,0,0,0,0,False,,0,0,0
+593,64,2,8,2,1,0,0,0,0,False,,0,0,0
+595,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+597,64,2,8,,0,0,0,0,0,False,,0,0,0
+599,64,2,8,2,1,0,0,0,0,False,,0,0,0
+601,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+603,64,2,8,,0,0,0,0,0,False,,0,0,0
+605,64,2,8,,0,0,0,0,0,False,,0,0,0
+607,64,2,8,2,1,0,0,0,0,False,,0,0,0
+609,64,2,8,2,1,0,0,0,0,False,,0,0,0
+611,64,2,8,,0,0,0,0,0,False,,0,0,0
+613,64,2,8,,0,0,0,0,0,False,,0,0,0
+615,64,2,8,,0,0,0,0,0,False,,0,0,0
+617,64,2,8,2,1,0,0,0,0,False,,0,0,0
+619,64,2,8,2,1,0,0,0,0,False,,0,0,0
+621,64,2,8,2,1,0,0,0,0,False,,0,0,0
+623,64,2,8,2,1,0,0,0,0,False,,0,0,0
+625,64,2,8,,0,0,0,0,0,False,,0,0,0
+627,64,2,8,2,1,0,0,0,0,False,,0,0,0
+629,64,2,8,,0,0,0,0,0,False,,0,0,0
+631,64,2,8,,0,0,0,0,0,False,,0,0,0
+633,64,2,8,,0,0,0,0,0,False,,0,0,0
+635,64,2,8,,0,0,0,0,0,False,,0,0,0
+637,64,2,8,2,1,0,0,0,0,False,,0,0,0
+639,64,2,8,2;3;4;5,4,9,3,6,0,False,2:3,9,17,9
+641,64,2,8,,0,0,0,0,0,False,,0,0,0
+643,64,2,8,,0,0,0,0,0,False,,0,0,0
+645,64,2,8,2,1,0,0,0,0,False,,0,0,0
+647,64,2,8,,0,0,0,0,0,False,,0,0,0
+649,64,2,8,2,1,0,0,0,0,False,,0,0,0
+651,64,2,8,2,1,0,0,0,0,False,,0,0,0
+653,64,2,8,,0,0,0,0,0,False,,0,0,0
+655,64,2,8,2,1,0,0,0,0,False,,0,0,0
+657,64,2,8,,0,0,0,0,0,False,,0,0,0
+659,64,2,8,,0,0,0,0,0,False,,0,0,0
+661,64,2,8,2,1,0,0,0,0,False,,0,0,0
+663,64,2,8,,0,0,0,0,0,False,,0,0,0
+665,64,2,8,,0,0,0,0,0,False,,0,0,0
+667,64,2,8,2,1,0,0,0,0,False,,0,0,0
+669,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+671,64,2,8,2;3;4;5;6,5,8,2,10,0,False,2:3,8,13,8
+673,64,2,8,,0,0,0,0,0,False,,0,0,0
+675,64,2,8,2,1,0,0,0,0,False,,0,0,0
+677,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+679,64,2,8,,0,0,0,0,0,False,,0,0,0
+681,64,2,8,2;3;4;5;6;7,6,6,2,15,0,False,2:3,6,8,6
+683,64,2,8,,0,0,0,0,0,False,,0,0,0
+685,64,2,8,2,1,0,0,0,0,False,,0,0,0
+687,64,2,8,2,1,0,0,0,0,False,,0,0,0
+689,64,2,8,2,1,0,0,0,0,False,,0,0,0
+691,64,2,8,2,1,0,0,0,0,False,,0,0,0
+693,64,2,8,,0,0,0,0,0,False,,0,0,0
+695,64,2,8,2,1,0,0,0,0,False,,0,0,0
+697,64,2,8,2,1,0,0,0,0,False,,0,0,0
+699,64,2,8,,0,0,0,0,0,False,,0,0,0
+701,64,2,8,2,1,0,0,0,0,False,,0,0,0
+703,64,2,8,2;3,2,12,12,1,0,False,2:3,12,22,12
+705,64,2,8,,0,0,0,0,0,False,,0,0,0
+707,64,2,8,2,1,0,0,0,0,False,,0,0,0
+709,64,2,8,,0,0,0,0,0,False,,0,0,0
+711,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,6,4
+713,64,2,8,,0,0,0,0,0,False,,0,0,0
+715,64,2,8,,0,0,0,0,0,False,,0,0,0
+717,64,2,8,,0,0,0,0,0,False,,0,0,0
+719,64,2,8,2,1,0,0,0,0,False,,0,0,0
+721,64,2,8,,0,0,0,0,0,False,,0,0,0
+723,64,2,8,,0,0,0,0,0,False,,0,0,0
+725,64,2,8,,0,0,0,0,0,False,,0,0,0
+727,64,2,8,,0,0,0,0,0,False,,0,0,0
+729,64,2,8,,0,0,0,0,0,False,,0,0,0
+731,64,2,8,2,1,0,0,0,0,False,,0,0,0
+733,64,2,8,2,1,0,0,0,0,False,,0,0,0
+735,64,2,8,2,1,0,0,0,0,False,,0,0,0
+737,64,2,8,2,1,0,0,0,0,False,,0,0,0
+739,64,2,8,,0,0,0,0,0,False,,0,0,0
+741,64,2,8,,0,0,0,0,0,False,,0,0,0
+743,64,2,8,2,1,0,0,0,0,False,,0,0,0
+745,64,2,8,,0,0,0,0,0,False,,0,0,0
+747,64,2,8,,0,0,0,0,0,False,,0,0,0
+749,64,2,8,,0,0,0,0,0,False,,0,0,0
+751,64,2,8,2,1,0,0,0,0,False,,0,0,0
+753,64,2,8,,0,0,0,0,0,False,,0,0,0
+755,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
+757,64,2,8,2,1,0,0,0,0,False,,0,0,0
+759,64,2,8,,0,0,0,0,0,False,,0,0,0
+761,64,2,8,,0,0,0,0,0,False,,0,0,0
+763,64,2,8,2,1,0,0,0,0,False,,0,0,0
+765,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
+767,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,7,5
+769,64,2,8,,0,0,0,0,0,False,,0,0,0
+771,64,2,8,,0,0,0,0,0,False,,0,0,0
+773,64,2,8,2,1,0,0,0,0,False,,0,0,0
+775,64,2,8,2,1,0,0,0,0,False,,0,0,0
+777,64,2,8,,0,0,0,0,0,False,,0,0,0
+779,64,2,8,,0,0,0,0,0,False,,0,0,0
+781,64,2,8,2,1,0,0,0,0,False,,0,0,0
+783,64,2,8,2,1,0,0,0,0,False,,0,0,0
+785,64,2,8,2,1,0,0,0,0,False,,0,0,0
+787,64,2,8,,0,0,0,0,0,False,,0,0,0
+789,64,2,8,,0,0,0,0,0,False,,0,0,0
+791,64,2,8,2,1,0,0,0,0,False,,0,0,0
+793,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+795,64,2,8,2;3;4;5;6,5,10,3,10,0,False,2:3,10,14,10
+797,64,2,8,2,1,0,0,0,0,False,,0,0,0
+799,64,2,8,2,1,0,0,0,0,False,,0,0,0
+801,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+803,64,2,8,,0,0,0,0,0,False,,0,0,0
+805,64,2,8,,0,0,0,0,0,False,,0,0,0
+807,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,8,5
+809,64,2,8,2,1,0,0,0,0,False,,0,0,0
+811,64,2,8,2,1,0,0,0,0,False,,0,0,0
+813,64,2,8,,0,0,0,0,0,False,,0,0,0
+815,64,2,8,2,1,0,0,0,0,False,,0,0,0
+817,64,2,8,,0,0,0,0,0,False,,0,0,0
+819,64,2,8,,0,0,0,0,0,False,,0,0,0
+821,64,2,8,,0,0,0,0,0,False,,0,0,0
+823,64,2,8,2,1,0,0,0,0,False,,0,0,0
+825,64,2,8,2,1,0,0,0,0,False,,0,0,0
+827,64,2,8,,0,0,0,0,0,False,,0,0,0
+829,64,2,8,2,1,0,0,0,0,False,,0,0,0
+831,64,2,8,2;3,2,9,9,1,0,False,2:3,9,17,9
+833,64,2,8,,0,0,0,0,0,False,,0,0,0
+835,64,2,8,2,1,0,0,0,0,False,,0,0,0
+837,64,2,8,,0,0,0,0,0,False,,0,0,0
+839,64,2,8,,0,0,0,0,0,False,,0,0,0
+841,64,2,8,,0,0,0,0,0,False,,0,0,0
+843,64,2,8,,0,0,0,0,0,False,,0,0,0
+845,64,2,8,,0,0,0,0,0,False,,0,0,0
+847,64,2,8,2,1,0,0,0,0,False,,0,0,0
+849,64,2,8,2,1,0,0,0,0,False,,0,0,0
+851,64,2,8,2,1,0,0,0,0,False,,0,0,0
+853,64,2,8,,0,0,0,0,0,False,,0,0,0
+855,64,2,8,,0,0,0,0,0,False,,0,0,0
+857,64,2,8,,0,0,0,0,0,False,,0,0,0
+859,64,2,8,2,1,0,0,0,0,False,,0,0,0
+861,64,2,8,2,1,0,0,0,0,False,,0,0,0
+863,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
+865,64,2,8,2,1,0,0,0,0,False,,0,0,0
+867,64,2,8,,0,0,0,0,0,False,,0,0,0
+869,64,2,8,,0,0,0,0,0,False,,0,0,0
+871,64,2,8,2;3;4,3,13,7,3,0,False,2:3,13,23,13
+873,64,2,8,2,1,0,0,0,0,False,,0,0,0
+875,64,2,8,,0,0,0,0,0,False,,0,0,0
+877,64,2,8,,0,0,0,0,0,False,,0,0,0
+879,64,2,8,2,1,0,0,0,0,False,,0,0,0
+881,64,2,8,2,1,0,0,0,0,False,,0,0,0
+883,64,2,8,,0,0,0,0,0,False,,0,0,0
+885,64,2,8,2,1,0,0,0,0,False,,0,0,0
+887,64,2,8,,0,0,0,0,0,False,,0,0,0
+889,64,2,8,2,1,0,0,0,0,False,,0,0,0
+891,64,2,8,,0,0,0,0,0,False,,0,0,0
+893,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+895,64,2,8,2;3;4;5;6,5,10,3,10,0,False,2:3,10,14,10
+897,64,2,8,,0,0,0,0,0,False,,0,0,0
+899,64,2,8,2,1,0,0,0,0,False,,0,0,0
+901,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+903,64,2,8,2,1,0,0,0,0,False,,0,0,0
+905,64,2,8,,0,0,0,0,0,False,,0,0,0
+907,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
+909,64,2,8,,0,0,0,0,0,False,,0,0,0
+911,64,2,8,2,1,0,0,0,0,False,,0,0,0
+913,64,2,8,2,1,0,0,0,0,False,,0,0,0
+915,64,2,8,2,1,0,0,0,0,False,,0,0,0
+917,64,2,8,,0,0,0,0,0,False,,0,0,0
+919,64,2,8,2,1,0,0,0,0,False,,0,0,0
+921,64,2,8,2,1,0,0,0,0,False,,0,0,0
+923,64,2,8,,0,0,0,0,0,False,,0,0,0
+925,64,2,8,2,1,0,0,0,0,False,,0,0,0
+927,64,2,8,2;3,2,7,7,1,0,False,2:3,7,13,7
+929,64,2,8,2,1,0,0,0,0,False,,0,0,0
+931,64,2,8,,0,0,0,0,0,False,,0,0,0
+933,64,2,8,2,1,0,0,0,0,False,,0,0,0
+935,64,2,8,2,1,0,0,0,0,False,,0,0,0
+937,64,2,8,2;3,2,12,12,1,0,False,2:3,12,22,12
+939,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
+941,64,2,8,2,1,0,0,0,0,False,,0,0,0
+943,64,2,8,2,1,0,0,0,0,False,,0,0,0
+945,64,2,8,,0,0,0,0,0,False,,0,0,0
+947,64,2,8,,0,0,0,0,0,False,,0,0,0
+949,64,2,8,,0,0,0,0,0,False,,0,0,0
+951,64,2,8,,0,0,0,0,0,False,,0,0,0
+953,64,2,8,,0,0,0,0,0,False,,0,0,0
+955,64,2,8,,0,0,0,0,0,False,,0,0,0
+957,64,2,8,2,1,0,0,0,0,False,,0,0,0
+959,64,2,8,2,1,0,0,0,0,False,,0,0,0
+961,64,2,8,,0,0,0,0,0,False,,0,0,0
+963,64,2,8,,0,0,0,0,0,False,,0,0,0
+965,64,2,8,,0,0,0,0,0,False,,0,0,0
+967,64,2,8,2,1,0,0,0,0,False,,0,0,0
+969,64,2,8,,0,0,0,0,0,False,,0,0,0
+971,64,2,8,,0,0,0,0,0,False,,0,0,0
+973,64,2,8,2,1,0,0,0,0,False,,0,0,0
+975,64,2,8,2,1,0,0,0,0,False,,0,0,0
+977,64,2,8,2,1,0,0,0,0,False,,0,0,0
+979,64,2,8,,0,0,0,0,0,False,,0,0,0
+981,64,2,8,,0,0,0,0,0,False,,0,0,0
+983,64,2,8,2,1,0,0,0,0,False,,0,0,0
+985,64,2,8,,0,0,0,0,0,False,,0,0,0
+987,64,2,8,,0,0,0,0,0,False,,0,0,0
+989,64,2,8,,0,0,0,0,0,False,,0,0,0
+991,64,2,8,2,1,0,0,0,0,False,,0,0,0
+993,64,2,8,,0,0,0,0,0,False,,0,0,0
+995,64,2,8,,0,0,0,0,0,False,,0,0,0
+997,64,2,8,,0,0,0,0,0,False,,0,0,0
+999,64,2,8,,0,0,0,0,0,False,,0,0,0
diff --git a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
new file mode 100644
index 00000000..e303faca
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
@@ -0,0 +1,34 @@
+# Collatz Selected Depth Overlap Scan
+
+- rows: `500`
+- rows with at least two selected depths: `52`
+- rows with a disjoint selected-depth pair: `0`
+- rows where every selected-depth pair overlaps: `52`
+- max selected depth count: `6`
+- max pairwise overlap: `13`
+
+## Top Multi-Witness Samples
+
+| n | selected depths | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |
+|---:|---|---:|---:|---:|---|---:|---|
+| 511 | 2;3;4;5;6;7 | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
+| 681 | 2;3;4;5;6;7 | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
+| 255 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 6:5 |
+| 671 | 2;3;4;5;6 | 10 | 0 | 8 | 2:3 | 8 | 13:8 |
+| 767 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 7:5 |
+| 795 | 2;3;4;5;6 | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
+| 807 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 8:5 |
+| 895 | 2;3;4;5;6 | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
+| 127 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 169 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 225 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 383 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+
+## Reading
+
+A disjoint pair means two selected continuation index sets are disjoint
+in this finite orbit window.  This is only experimental evidence.
+
+If disjoint pairs are common, a future Lean predicate could target
+`DisjointTowerTargets`.  If all selected pairs overlap, the right
+formal condition may need to express nested selected-depth behavior.
diff --git a/python/Collatz/PetalBridge/selected_depth_overlap_scan.py b/python/Collatz/PetalBridge/selected_depth_overlap_scan.py
new file mode 100644
index 00000000..592ee488
--- /dev/null
+++ b/python/Collatz/PetalBridge/selected_depth_overlap_scan.py
@@ -0,0 +1,226 @@
+#!/usr/bin/env python3
+"""Scan overlap between selected source pressure depths.
+
+Checkpoint 122 proves that `pressureDepthCount >= 2` gives two selected
+pressure-depth witnesses, but it does not claim that the corresponding budget
+carriers are independent.
+
+This script observes the missing question on concrete Collatz windows:
+
+    for selected depths d1, d2,
+    how much do their continuation-label index sets overlap?
+
+The output is experimental data for choosing the next Lean predicate, such as
+`SelectedDepthsAddressSeparated` or `DisjointTowerTargets`.
+"""
+
+from __future__ import annotations
+
+import argparse
+import csv
+from dataclasses import dataclass
+from itertools import combinations
+from pathlib import Path
+
+
+@dataclass(frozen=True)
+class OverlapRow:
+    n: int
+    steps: int
+    r_start: int
+    depth_len: int
+    selected_depths: str
+    selected_count: int
+    max_pairwise_overlap: int
+    min_pairwise_overlap: int
+    total_pair_count: int
+    disjoint_pair_count: int
+    has_disjoint_pair: bool
+    first_pair: str
+    first_pair_overlap: int
+    first_pair_left_mass: int
+    first_pair_right_mass: int
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
+def orbit_labels(n: int, steps: int) -> list[int]:
+    labels: list[int] = []
+    current = n
+    for _ in range(steps):
+        labels.append(current)
+        current, _height = accelerated_step(current)
+    return labels
+
+
+def continuation_indices(labels: list[int], depth: int) -> set[int]:
+    modulus = 2 ** (depth + 1)
+    residue = modulus - 1
+    return {i for i, value in enumerate(labels) if value % modulus == residue}
+
+
+def retention_indices(labels: list[int], depth: int) -> set[int]:
+    modulus = 2**depth
+    residue = modulus - 1
+    return {i for i, value in enumerate(labels) if value % modulus == residue}
+
+
+def selected_depths(labels: list[int], r_start: int, depth_len: int) -> list[int]:
+    selected: list[int] = []
+    for j in range(depth_len):
+        depth = r_start + j
+        continuation = continuation_indices(labels, depth)
+        retention = retention_indices(labels, depth)
+        if len(retention) < 2 * len(continuation):
+            selected.append(depth)
+    return selected
+
+
+def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OverlapRow:
+    labels = orbit_labels(n, steps)
+    depths = selected_depths(labels, r_start, depth_len)
+    index_sets = {depth: continuation_indices(labels, depth) for depth in depths}
+    pair_stats: list[tuple[int, int, int]] = []
+    for left, right in combinations(depths, 2):
+        pair_stats.append((left, right, len(index_sets[left] & index_sets[right])))
+    if pair_stats:
+        overlaps = [overlap for _left, _right, overlap in pair_stats]
+        first_left, first_right, first_overlap = pair_stats[0]
+        first_pair = f"{first_left}:{first_right}"
+        first_left_mass = len(index_sets[first_left])
+        first_right_mass = len(index_sets[first_right])
+        max_overlap = max(overlaps)
+        min_overlap = min(overlaps)
+        disjoint_pair_count = sum(1 for overlap in overlaps if overlap == 0)
+    else:
+        first_pair = ""
+        first_overlap = 0
+        first_left_mass = 0
+        first_right_mass = 0
+        max_overlap = 0
+        min_overlap = 0
+        disjoint_pair_count = 0
+    return OverlapRow(
+        n=n,
+        steps=steps,
+        r_start=r_start,
+        depth_len=depth_len,
+        selected_depths=";".join(str(depth) for depth in depths),
+        selected_count=len(depths),
+        max_pairwise_overlap=max_overlap,
+        min_pairwise_overlap=min_overlap,
+        total_pair_count=len(pair_stats),
+        disjoint_pair_count=disjoint_pair_count,
+        has_disjoint_pair=disjoint_pair_count > 0,
+        first_pair=first_pair,
+        first_pair_overlap=first_overlap,
+        first_pair_left_mass=first_left_mass,
+        first_pair_right_mass=first_right_mass,
+    )
+
+
+def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[OverlapRow]:
+    return [row_for(n, steps, r_start, depth_len) for n in range(1, max_n + 1, 2)]
+
+
+def write_csv(rows: list[OverlapRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    with path.open("w", newline="", encoding="utf-8") as f:
+        writer = csv.DictWriter(f, fieldnames=list(OverlapRow.__dataclass_fields__))
+        writer.writeheader()
+        for row in rows:
+            writer.writerow(row.__dict__)
+
+
+def write_summary(rows: list[OverlapRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    multi = [row for row in rows if row.selected_count >= 2]
+    with_disjoint = [row for row in multi if row.has_disjoint_pair]
+    all_overlap = [row for row in multi if not row.has_disjoint_pair]
+    max_selected = max((row.selected_count for row in rows), default=0)
+    max_overlap = max((row.max_pairwise_overlap for row in rows), default=0)
+    samples = sorted(
+        multi,
+        key=lambda row: (-row.selected_count, -row.disjoint_pair_count, row.n),
+    )[:12]
+    lines = [
+        "# Collatz Selected Depth Overlap Scan",
+        "",
+        f"- rows: `{len(rows)}`",
+        f"- rows with at least two selected depths: `{len(multi)}`",
+        f"- rows with a disjoint selected-depth pair: `{len(with_disjoint)}`",
+        f"- rows where every selected-depth pair overlaps: `{len(all_overlap)}`",
+        f"- max selected depth count: `{max_selected}`",
+        f"- max pairwise overlap: `{max_overlap}`",
+        "",
+        "## Top Multi-Witness Samples",
+        "",
+        "| n | selected depths | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |",
+        "|---:|---|---:|---:|---:|---|---:|---|",
+    ]
+    for row in samples:
+        lines.append(
+            "| "
+            f"{row.n} | {row.selected_depths} | {row.total_pair_count} | "
+            f"{row.disjoint_pair_count} | {row.max_pairwise_overlap} | "
+            f"{row.first_pair} | {row.first_pair_overlap} | "
+            f"{row.first_pair_left_mass}:{row.first_pair_right_mass} |"
+        )
+    lines.extend(
+        [
+            "",
+            "## Reading",
+            "",
+            "A disjoint pair means two selected continuation index sets are disjoint",
+            "in this finite orbit window.  This is only experimental evidence.",
+            "",
+            "If disjoint pairs are common, a future Lean predicate could target",
+            "`DisjointTowerTargets`.  If all selected pairs overlap, the right",
+            "formal condition may need to express nested selected-depth behavior.",
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
+    csv_path = args.out_dir / "selected_depth_overlap_scan.csv"
+    summary_path = args.out_dir / "selected_depth_overlap_scan.md"
+    write_csv(rows, csv_path)
+    write_summary(rows, summary_path)
+    print(f"wrote {csv_path}")
+    print(f"wrote {summary_path}")
+
+
+if __name__ == "__main__":
+    main()
````
`````
