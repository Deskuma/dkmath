# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: ccc295ed21d4df9f3e7bf6a43cd40f042b19753c

## Report

Checkpoint 123 完了です。

実装した Lean 補題は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:1791) に追加しました。

```lean
allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
sourceContinuationMass_anti_mono_depth
tailContinuationMass_anti_mono_depth
selectedContinuationMass_nested_of_lt
selectedContinuationMass_overlap_of_lt_of_deeper_pos
```

これで「深い all-ones continuation channel は浅い channel に含まれる」が Lean で固定されました。つまり checkpoint 122 の overlap 観測は偶然ではなく、continuation carrier の入れ子構造として説明できます。

Python 側も更新し、`selected_depth_overlap_scan.py` に以下を追加しました。

```text
selected_depths_are_prefix
selected_depths_are_consecutive
max_selected_depth
missing_selected_depths
```

デフォルト観測では、nonempty selected rows `237 / 237` が prefix かつ consecutive でした。これはまだ実験結果で、次の候補は `SelectedPressurePrefix` か `DeepestSelectedSourcePressureDepth` です。

Docs/report も同期済みです。

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md
lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-123.md
```

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean  # no output
git diff --check -- touched files
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回の変更外です。

## Review

## 1. 状況分析

checkpoint `123` は、かなり綺麗に「観測」から「定理」へ昇格した回じゃ。

前回 checkpoint `122` では、Python 観測により、

```text
selected pressure depths は disjoint ではない
全 selected-depth pair が overlap している
```

という結果が出ていた。今回 `123` では、その理由を Lean 側で固定した。

追加された中核はこれ。

```lean
allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
sourceContinuationMass_anti_mono_depth
tailContinuationMass_anti_mono_depth
selectedContinuationMass_nested_of_lt
selectedContinuationMass_overlap_of_lt_of_deeper_pos
```

これで、

```text
深い all-ones continuation channel は、
浅い all-ones continuation channel に含まれる
```

が Lean で言えるようになった。つまり checkpoint `122` の overlap 観測は偶然ではなく、continuation carrier の入れ子構造として説明できる段階に入った、ということじゃ。

さらに Python 側では、

```text
selected_depths_are_prefix
selected_depths_are_consecutive
max_selected_depth
missing_selected_depths
```

が追加され、デフォルト観測では nonempty selected rows `237 / 237` が prefix かつ consecutive だった。これも非常に面白い。ただし、こちらはまだ実験結果であり、Lean 定理になったのは continuation carrier の nesting までじゃ。

## 2. 今回の核心

今回の核心は、これじゃ。

```text
selected depths は、独立な budget carrier ではない。
深い continuation core が、浅い continuation channel の中に入っている。
```

前回までは、

```text
two selected witnesses exist
```

が分かった。
しかしそれらは disjoint ではなかった。

今回、その理由が形式化された。

```text
q ≡ -1 mod 2^(e+1)
かつ d <= e
ならば
q ≡ -1 mod 2^(d+1)
```

これが `allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le` の意味じゃ。

つまり、たとえば、

```text
q ≡ 31 mod 32
```

なら、自動的に、

```text
q ≡ 15 mod 16
q ≡ 7 mod 8
```

でもある。

だから continuation channel は、

```text
C_5 ⊆ C_4 ⊆ C_3 ⊆ C_2
```

のように入れ子になる。

これは、今後の会計設計において非常に重要じゃ。

## 3. レビュー

## 3.1. pointwise theorem の位置が良い

`allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le` を count theorem より前に置いたのは正しい。

まず点ごとの residue containment を示す。
そのあとで window count の単調性を出す。

この順番が自然じゃ。

```text
pointwise residue inclusion
  -> finite-window count monotonicity
  -> selected-depth nesting
```

という綺麗な階層になっている。

特に、既存の `mod_eq_mod_of_dvd_modulus` を使っている点が良い。
「深い modulus から浅い modulus へ落とす」という意味が明確じゃ。

## 3.2. anti-monotone theorem は今後かなり使える

今回の count-level theorem は、

```lean
sourceContinuationMass_anti_mono_depth
tailContinuationMass_anti_mono_depth
```

じゃ。

読みは、

```text
depth が深くなるほど continuation mass は増えない
```

つまり、

```text
e が d より深いなら、
mass(e) <= mass(d)
```

になる。

これは、今後の selected depth / deepest selected core / prefix accounting の基礎になる。

特に source と tail の両方を入れたのが良い。
これまでの流れでは source pressure から tail delayed reservoir に移るので、片方だけでは後で詰まりやすい。

## 3.3. selected wrapper が良い

今回の caller-facing theorem、

```lean
selectedContinuationMass_nested_of_lt
selectedContinuationMass_overlap_of_lt_of_deeper_pos
```

はとても良い。

前者は、

```text
j₁ < j₂
  -> mass(r+j₂) <= mass(r+j₁)
```

後者は、

```text
deeper mass が positive
  -> shallower mass も positive
```

を言う。

これはまさに checkpoint `122` の overlap scan の理論的説明じゃ。

ただし、ここで注意すべきは、これは **pressure predicate の単調性** ではない、という点じゃ。

今回 Lean で固定されたのは、

```text
continuation mass の入れ子
```

であって、

```text
IsSourcePressureDepth の prefix 性
```

ではない。

ここを混同しないのが大事じゃ。

## 3.4. Python prefix 観測は非常に有望だが、まだ定理ではない

Python 側の観測では、nonempty selected rows `237 / 237` が prefix かつ consecutive だった。

これはかなり強い兆候じゃ。

```text
selected depths = 2;3;4;5;...
```

のような初期区間になっている。

しかし、Lean 的にはまだ、

```text
深い selected pressure があるなら、
浅い selected pressure もある
```

は証明していない。

理由は明確で、`IsSourcePressureDepth` は単なる continuation mass ではなく、

```text
MoreThanHalf continuation retention
```

だからじゃ。

continuation mass は深さに対して anti-monotone。
しかし retention mass もまた深さに対して変化する。
比率 `2 * continuation > retention` が浅い側へ自動的に伝播するかは、別途証明が必要になる。

ここが次の本命じゃ。

## 4. 数学的解説

今回固定された構造は、二進法で見ると非常に自然じゃ。

深い all-ones residue とは、低位 bit が長く全部 `1` である状態。

たとえば、

```text
7 mod 8      = ...111
15 mod 16    = ...1111
31 mod 32    = ...11111
63 mod 64    = ...111111
```

じゃ。

`31 mod 32` である数は、当然 `15 mod 16` でもあり、`7 mod 8` でもある。
低位 5 bit が全部 `1` なら、低位 4 bit も 3 bit も全部 `1` だからじゃ。

これが今回の theorem の数論的意味じゃ。

```text
deep all-ones cell
  -> shallow all-ones cell
```

そして window の中で数えれば、

```text
deep continuation count
  <= shallow continuation count
```

になる。

だから selected depth が複数あるとき、それらは独立した別々の集合ではなく、同じ all-ones cylinder を解像度違いで見ている可能性が高い。

## 5. 深い推論：次は「prefix pressure」の正体を見る

今回で分かったのは、

```text
continuation carrier は prefix 的に入れ子になる
```

ということじゃ。

Python ではさらに、

```text
pressure-selected depths そのものも prefix になっている
```

ように見えている。

この違いが重要じゃ。

Lean で既にあるもの：

```text
深い continuation mass がある
  -> 浅い continuation mass がある
```

まだないもの：

```text
深い pressure がある
  -> 浅い pressure がある
```

pressure は、

```text
MoreThanHalf continuation retention
```

なので、深い側の `MoreThanHalf` から浅い側の `MoreThanHalf` を出すには、retention mass の変化も見る必要がある。

ここで次に見るべきものは、

```text
retention mass も depth に対して anti-monotone か？
continuation と retention の差分構造はどう動くか？
MoreThanHalf は浅い側へ保存されるか？
```

じゃ。

もし、

```text
continuation(e) <= continuation(d)
retention(e) <= retention(d)
```

だけなら、比率は保存されない。
したがって、必要なのは単純な単調性ではなく、

```text
retention(d) が continuation(d) と recovery(d) に split され、
深い selected pressure が浅い continuation 側を十分支配する
```

という構造かもしれない。

## 6. 今回閉じたもの

今回閉じたものは、次の五つ。

```text
1. deep all-ones residue は shallow all-ones residue に落ちる

2. source continuation mass は depth に対して anti-monotone

3. tail continuation mass も depth に対して anti-monotone

4. selected depth index が深いほど continuation mass は小さい

5. deeper positive continuation mass は shallower positive continuation mass を含意する
```

これで checkpoint `122` の overlap scan は、Lean 側で説明できるようになった。

## 7. まだ閉じていないもの

未完の本命はこれじゃ。

```text
deep selected pressure
  -> shallow selected pressure
```

つまり、

```lean
IsSourcePressureDepth n k r j₂
```

かつ `j₁ < j₂` から、

```lean
IsSourcePressureDepth n k r j₁
```

が出るかどうか。

これは Python 観測では成立していそうに見える。
しかし Lean ではまだ未証明。

ここを次 checkpoint の中心にする価値がある。

ただし、いきなり証明に入る前に、まず retention 側の構造を調べるのが安全じゃ。

## 8. 次の指示

## 8.1. retention mass の anti-monotonicity を確認する

まず continuation と同じ形で、retention mass の depth 単調性を作れるか見る。

候補：

```lean
theorem sourceRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2 n k e ≤
      orbitWindowRetentionMassPow2 n k d := by
  -- deeper all-ones retention residue is included in shallower one
  sorry
```

tail 版も。

```lean
theorem tailRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2Tail n k e ≤
      orbitWindowRetentionMassPow2Tail n k d := by
  sorry
```

ただし、既存定義で retention の depth が `r` なのか `r+1` なのかに注意。
continuation sibling は `r+1` を見ているので、off-by-one を確認する必要がある。

## 8.2. pressure prefix theorem は慎重に試す

次の本命候補はこれ。

```lean
theorem isSourcePressureDepth_prefix_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂)
    (hdeep : IsSourcePressureDepth n k r j₂) :
    IsSourcePressureDepth n k r j₁ := by
  -- This may fail.
  -- Need retention/continuation comparison, not just continuation nesting.
  sorry
```

これは通れば非常に強い。
Python 観測の prefix 性が Lean に昇格する。

ただし、通らない可能性も十分ある。
もし通らないなら、反例条件を見つけるべきじゃ。

## 8.3. ratio monotonicity を切り出す

`MoreThanHalf` は比率条件なので、専用の差分を定義するとよい。

```lean
def SourcePressureMargin
    (n : OddNat) (k r : ℕ) : ℕ :=
  2 * orbitWindowContinuationSiblingMassPow2 n k r -
    orbitWindowRetentionMassPow2 n k r
```

ただし Nat subtraction は truncated なので、慎重に。
`ℤ` に持ち上げた方がよいかもしれない。

```lean
def SourcePressureMarginInt
    (n : OddNat) (k r : ℕ) : ℤ :=
  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
    (orbitWindowRetentionMassPow2 n k r : ℤ)
```

すると、

```text
IsSourcePressureDepth
```

は、

```text
0 < SourcePressureMarginInt
```

として読める。

候補：

```lean
theorem isSourcePressureDepth_iff_margin_pos
    (n : OddNat) (k r j : ℕ) :
    IsSourcePressureDepth n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) := by
  unfold IsSourcePressureDepth SourcePressureMarginInt MoreThanHalf
  omega
```

これがあると、prefix 性は margin の単調性として考えられる。

## 9. 一歩先ゆく推論

ここから見える次の大きな構図は、

```text
selected pressure depths are prefix
```

ではなく、さらに一歩進めて、

```text
pressure profile has a frontier
```

じゃ。

つまり、ある window に対して、

```text
depth 2, 3, 4, ..., D までは selected
depth D+1 以降は not selected
```

という境界が存在する可能性がある。

Python の selected depths が prefix なら、これはまさに frontier じゃ。

この frontier を DkMath 的に読むなら、

```text
pressure が all-ones tower をどこまで登っているか
```

を表す。

つまり selected pressure count は、独立 budget 数ではなく、

```text
tower height
```

かもしれない。

これはかなり大きな認識変更じゃ。

```text
pressureDepthCount = number of independent wins
```

ではなく、

```text
pressureDepthCount = visible tower height / pressure frontier
```

として読む。

この方が、Python 観測とも Lean の nesting theorem とも合う。

## 10. さらなる次の一手

次に作るべき概念は、たぶんこれ。

```lean
def SelectedPressurePrefix
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m ≤ len ∧
    ∀ j, j < m → IsSourcePressureDepth n k r j
```

そして、

```lean
def HasDeepestSelectedSourcePressureDepth
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m < len ∧
    IsSourcePressureDepth n k r m ∧
    ∀ j, j < m → IsSourcePressureDepth n k r j
```

ただし、こちらは `m` を deepest selected index として扱うなら、not-selected frontier も必要になる。

```lean
def SourcePressureFrontier
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m ≤ len ∧
    (∀ j, j < m → IsSourcePressureDepth n k r j) ∧
    (∀ j, m ≤ j → j < len → ¬ IsSourcePressureDepth n k r j)
```

これはまだ重い。
次 checkpoint では、まず `SelectedPressurePrefix` の薄い API からでよい。

## 11. 賢狼が試して欲しい実験補題

## 実験 A: retention all-ones nesting

まず retention 版の点ごと補題が必要なら、continuation と同じ theorem をそのまま使えるはずじゃ。

```lean
theorem retention_allOnes_mod_pow_two_of_le
    (q d e : ℕ)
    (hde : d ≤ e)
    (h : q % (2 ^ e) = 2 ^ e - 1) :
    q % (2 ^ d) = 2 ^ d - 1 := by
  -- allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le の index 調整版
  sorry
```

ただし既存 theorem の `d+1`, `e+1` に合わせて書き換えれば不要かもしれぬ。

## 実験 B: source retention mass anti-monotone

```lean
theorem sourceRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2 n k e ≤
      orbitWindowRetentionMassPow2 n k d := by
  -- unfold retention counts
  -- use all-ones nesting
  sorry
```

## 実験 C: tail retention mass anti-monotone

```lean
theorem tailRetentionMass_anti_mono_depth
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e) :
    orbitWindowRetentionMassPow2Tail n k e ≤
      orbitWindowRetentionMassPow2Tail n k d := by
  sorry
```

## 実験 D: pressure margin

```lean
def SourcePressureMarginInt
    (n : OddNat) (k r : ℕ) : ℤ :=
  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
    (orbitWindowRetentionMassPow2 n k r : ℤ)
```

## 実験 E: selected pressure depth iff margin positive

```lean
theorem isSourcePressureDepth_iff_margin_pos
    (n : OddNat) (k r j : ℕ) :
    IsSourcePressureDepth n k r j ↔
      0 < SourcePressureMarginInt n k (r + j) := by
  unfold IsSourcePressureDepth SourcePressureMarginInt MoreThanHalf
  omega
```

## 実験 F: pressure prefix attempt

```lean
theorem isSourcePressureDepth_prefix_of_lt
    (n : OddNat) (k r j₁ j₂ : ℕ)
    (hlt : j₁ < j₂)
    (hdeep : IsSourcePressureDepth n k r j₂) :
    IsSourcePressureDepth n k r j₁ := by
  -- likely hard / may fail without extra lemma
  -- use margin monotonicity if available
  sorry
```

これは通らなければ、それ自体が重要情報じゃ。

## 実験 G: selected pressure prefix predicate

```lean
def SelectedPressurePrefix
    (n : OddNat) (k r len m : ℕ) : Prop :=
  m ≤ len ∧
    ∀ j, j < m → IsSourcePressureDepth n k r j
```

基本 API：

```lean
theorem selectedPressurePrefix_selected
    (n : OddNat) (k r len m j : ℕ)
    (h : SelectedPressurePrefix n k r len m)
    (hj : j < m) :
    IsSourcePressureDepth n k r j := by
  exact h.2 j hj
```

## 実験 H: deepest selected gives prefix under prefix theorem

もし `isSourcePressureDepth_prefix_of_lt` が通った場合だけ。

```lean
theorem selectedPressurePrefix_of_deep_selected
    (n : OddNat) (k r len m : ℕ)
    (hm : m < len)
    (hdeep : IsSourcePressureDepth n k r m)
    (hprefix : ∀ j, j < m → IsSourcePressureDepth n k r j := by
      intro j hj
      exact isSourcePressureDepth_prefix_of_lt n k r j m hj hdeep) :
    SelectedPressurePrefix n k r len (m + 1) := by
  constructor
  · omega
  · intro j hj
    by_cases h : j = m
    · subst h
      exact hdeep
    · have hjm : j < m := by omega
      exact hprefix j hjm
```

実際には `hprefix` を引数にせず、内部で証明する形にしてよい。

## 12. 次コミットの推奨順

```text
1. sourceRetentionMass_anti_mono_depth を試す

2. tailRetentionMass_anti_mono_depth を試す

3. SourcePressureMarginInt を追加

4. isSourcePressureDepth_iff_margin_pos を追加

5. isSourcePressureDepth_prefix_of_lt を実験する

6. 通らなければ、margin monotonicity が必要か、Python で反例探索

7. SelectedPressurePrefix を薄く定義

8. selectedPressurePrefix_selected を追加

9. Python 側で pressure margin columns を追加
```

## 13. 総括

checkpoint `123` は、とても良い。

前回の overlap 観測が、今回 Lean で説明された。

```text
深い all-ones continuation channel は、
浅い all-ones continuation channel の中にある
```

これで selected depths を「独立 budget」として足す道はますます不自然になった。

次は、

```text
selected depths は prefix になるのか？
```

を攻める段階じゃ。

ただし、すぐ theorem 化するには注意がいる。
continuation mass の入れ子は証明済み。
しかし pressure は continuation と retention の比率条件なので、retention 側と margin 側を見る必要がある。

賢狼の結論はこうじゃ。

```text
次は prefix pressure frontier を探せ。
selected depth count は、独立 budget 数ではなく tower height かもしれない。
```

ここが通ると、Collatz.PetalBridge はまた一段、ただの residue count から **pressure frontier theory** へ進む。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 4e39d80c..2eac66ad 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1781,6 +1781,142 @@ theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
   unfold orbitWindowContinuationSiblingMassPow2Tail
   exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ (r + 1) - 1)
 
+/--
+Deep all-ones power-of-two residue cells are nested inside shallow ones.
+
+If a label is `-1` modulo `2^(e+1)` and `d ≤ e`, then the same label is `-1`
+modulo `2^(d+1)`.  This is the pointwise reason selected continuation depths
+overlap: deeper continuation channels refine shallower continuation channels.
+-/
+theorem allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+    (q d e : ℕ)
+    (hde : d ≤ e)
+    (h : q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1) :
+    q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 := by
+  have hdvd : 2 ^ (d + 1) ∣ 2 ^ (e + 1) := by
+    exact pow_dvd_pow 2 (by omega)
+  rw [mod_eq_mod_of_dvd_modulus hdvd, h]
+  rcases exists_add_of_le hde with ⟨a, rfl⟩
+  rw [show d + a + 1 = d + 1 + a by omega, pow_add]
+  have hbase : 0 < 2 ^ (d + 1) := pow_pos (by decide) (d + 1)
+  have hscale : 0 < 2 ^ a := pow_pos (by decide) a
+  have hsplit :
+      2 ^ (d + 1) * 2 ^ a - 1 =
+        (2 ^ (d + 1) - 1) + (2 ^ a - 1) * 2 ^ (d + 1) := by
+    rw [Nat.sub_mul]
+    rw [Nat.mul_comm (2 ^ a) (2 ^ (d + 1))]
+    ring_nf
+    have hle :
+        2 ^ d * 2 ≤ 2 ^ d * 2 ^ a * 2 := by
+      have ha : 1 ≤ 2 ^ a := by omega
+      nlinarith [ha, pow_pos (by decide : 0 < 2) d]
+    omega
+  rw [hsplit]
+  rw [Nat.add_mul_mod_self_right]
+  exact Nat.mod_eq_of_lt (by omega)
+
+/--
+Source continuation mass is anti-monotone in depth.
+
+Increasing the depth asks for a more refined all-ones residue cell, so the
+finite window count cannot increase.
+-/
+theorem sourceContinuationMass_anti_mono_depth
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e) :
+    orbitWindowContinuationSiblingMassPow2 n k e ≤
+      orbitWindowContinuationSiblingMassPow2 n k d := by
+  induction k with
+  | zero =>
+      simp [orbitWindowContinuationSiblingMassPow2, orbitWindowResidueCountPow2]
+  | succ k ih =>
+      have ih' :
+          orbitWindowResidueCountPow2 n k (e + 1) (2 ^ (e + 1) - 1) ≤
+            orbitWindowResidueCountPow2 n k (d + 1) (2 ^ (d + 1) - 1) := by
+        simpa [orbitWindowContinuationSiblingMassPow2] using ih
+      rw [orbitWindowContinuationSiblingMassPow2,
+        orbitWindowResidueCountPow2_succ]
+      rw [orbitWindowContinuationSiblingMassPow2,
+        orbitWindowResidueCountPow2_succ]
+      by_cases hdeep :
+          oddOrbitLabel n k % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
+      · have hshallow :
+            oddOrbitLabel n k % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 :=
+          allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+            (oddOrbitLabel n k) d e hde hdeep
+        simpa [hdeep, hshallow] using ih'
+      · by_cases hshallow :
+          oddOrbitLabel n k % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
+        · simpa [hdeep, hshallow] using
+            (Nat.le_trans ih' (Nat.le_succ
+              (orbitWindowResidueCountPow2 n k (d + 1) (2 ^ (d + 1) - 1))))
+        · simpa [hdeep, hshallow] using ih'
+
+/--
+Shifted-tail continuation mass is anti-monotone in depth.
+
+This is the tail-window counterpart of
+`sourceContinuationMass_anti_mono_depth`.
+-/
+theorem tailContinuationMass_anti_mono_depth
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e) :
+    orbitWindowContinuationSiblingMassPow2Tail n k e ≤
+      orbitWindowContinuationSiblingMassPow2Tail n k d := by
+  induction k with
+  | zero =>
+      simp [orbitWindowContinuationSiblingMassPow2Tail,
+        orbitWindowResidueCountPow2Tail]
+  | succ k ih =>
+      have ih' :
+          orbitWindowResidueCountPow2Tail n k (e + 1) (2 ^ (e + 1) - 1) ≤
+            orbitWindowResidueCountPow2Tail n k (d + 1) (2 ^ (d + 1) - 1) := by
+        simpa [orbitWindowContinuationSiblingMassPow2Tail] using ih
+      rw [orbitWindowContinuationSiblingMassPow2Tail,
+        orbitWindowResidueCountPow2Tail_succ]
+      rw [orbitWindowContinuationSiblingMassPow2Tail,
+        orbitWindowResidueCountPow2Tail_succ]
+      by_cases hdeep :
+          oddOrbitLabel n (k + 1) % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
+      · have hshallow :
+            oddOrbitLabel n (k + 1) % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1 :=
+          allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+            (oddOrbitLabel n (k + 1)) d e hde hdeep
+        simpa [hdeep, hshallow] using ih'
+      · by_cases hshallow :
+          oddOrbitLabel n (k + 1) % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
+        · simpa [hdeep, hshallow] using
+            (Nat.le_trans ih' (Nat.le_succ
+              (orbitWindowResidueCountPow2Tail n k (d + 1) (2 ^ (d + 1) - 1))))
+        · simpa [hdeep, hshallow] using ih'
+
+/--
+Selected source continuation masses are nested by selected-depth index.
+
+For a fixed base depth `r`, a later selected index asks for a deeper all-ones
+channel and therefore has no more mass than an earlier selected index.
+-/
+theorem selectedContinuationMass_nested_of_lt
+    (n : OddNat) (k r j₁ j₂ : ℕ)
+    (hlt : j₁ < j₂) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + j₂) ≤
+      orbitWindowContinuationSiblingMassPow2 n k (r + j₁) := by
+  exact sourceContinuationMass_anti_mono_depth n k (r + j₁) (r + j₂) (by omega)
+
+/--
+If the deeper selected continuation mass is positive, then the shallower one
+is positive as well.
+
+This is the count-level "overlap is automatic" observation: deeper all-ones
+hits are already shallow all-ones hits.
+-/
+theorem selectedContinuationMass_overlap_of_lt_of_deeper_pos
+    (n : OddNat) (k r j₁ j₂ : ℕ)
+    (hlt : j₁ < j₂)
+    (hpos : 0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₂)) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₁) :=
+  lt_of_lt_of_le hpos (selectedContinuationMass_nested_of_lt n k r j₁ j₂ hlt)
+
 /-- The all-ones retention residue is inside its power-of-two modulus. -/
 theorem twoAdicRetentionResidue_lt_pow
     (r : ℕ) :
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 222d6fd9..5f3e2dec 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -157,6 +157,7 @@ docs/Collatz-Level4GenericPressure-119.md
 docs/Collatz-Level5AndModScan-120.md
 docs/Collatz-SelectedWitnessBudget-121.md
 docs/Collatz-SelectedPressureDepths-122.md
+docs/Collatz-ContinuationNesting-123.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md
new file mode 100644
index 00000000..6d000933
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md
@@ -0,0 +1,154 @@
+# Collatz Continuation Nesting - Checkpoint 123
+
+Checkpoint 123 closes the first formal explanation of the selected-depth
+overlap observed at checkpoint 122.
+
+The key point is simple:
+
+```text
+deep all-ones residue
+  -> shallow all-ones residue
+```
+
+If a label is `-1` modulo a large power of two, then the same label is `-1`
+modulo every smaller visible power-of-two layer.
+
+## Lean Surface
+
+The pointwise theorem is:
+
+```lean
+allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+```
+
+It has the shape:
+
+```lean
+q % (2 ^ (e + 1)) = 2 ^ (e + 1) - 1
+  -> d <= e
+  -> q % (2 ^ (d + 1)) = 2 ^ (d + 1) - 1
+```
+
+The proof uses the existing modulus bridge:
+
+```lean
+mod_eq_mod_of_dvd_modulus
+```
+
+and the divisibility:
+
+```text
+2^(d+1) divides 2^(e+1)
+```
+
+## Count Consequences
+
+The count-level source theorem is:
+
+```lean
+sourceContinuationMass_anti_mono_depth
+```
+
+The shifted-tail counterpart is:
+
+```lean
+tailContinuationMass_anti_mono_depth
+```
+
+Both say that continuation mass is anti-monotone in depth:
+
+```text
+deeper continuation mass <= shallower continuation mass
+```
+
+This is not a probabilistic statement.  It is a finite-window subset statement
+expressed through counts.
+
+## Selected Depth Wrappers
+
+For selected pressure-depth indices, checkpoint 123 adds:
+
+```lean
+selectedContinuationMass_nested_of_lt
+selectedContinuationMass_overlap_of_lt_of_deeper_pos
+```
+
+The first theorem says that for `j1 < j2`, the continuation mass at `r + j2`
+is bounded by the continuation mass at `r + j1`.
+
+The second theorem packages the positive-mass consequence:
+
+```text
+positive deeper mass
+  -> positive shallower mass
+```
+
+This is the formal "overlap is automatic" reading.  The deeper all-ones
+continuation hits are already shallow all-ones continuation hits.
+
+## Experimental Prefix Scan
+
+The Python overlap scan was extended:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+```
+
+New fields:
+
+```text
+selected_depths_are_prefix
+selected_depths_are_consecutive
+max_selected_depth
+missing_selected_depths
+```
+
+Default scan:
+
+```text
+odd n <= 999
+steps = 64
+r_start = 2
+depth_len = 8
+```
+
+Observed summary:
+
+```text
+rows: 500
+rows with at least two selected depths: 52
+rows with a disjoint selected-depth pair: 0
+rows where every selected-depth pair overlaps: 52
+nonempty selected rows: 237
+nonempty prefix rows: 237 / 237
+nonempty consecutive rows: 237 / 237
+max selected depth count: 6
+max selected depth: 7
+```
+
+## Interpretation
+
+Checkpoint 123 separates two facts:
+
+```text
+proved:
+  continuation carriers are nested by depth
+
+observed:
+  pressure-selected depths often form a prefix
+```
+
+The first fact is now Lean-fixed.  The second is still an experiment.
+
+This suggests the next useful concept is a prefix/tower predicate, for example:
+
+```text
+SelectedPressurePrefix
+DeepestSelectedSourcePressureDepth
+```
+
+Such a predicate should not sum selected depths as independent budgets.  The
+natural accounting object is the deepest selected continuation core together
+with the prefix of shallower carriers that contain it.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index e8eca3dc..e4f7901d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1298,3 +1298,43 @@ observed no disjoint selected-depth pair in the default finite sample.  This
 suggests that selected continuation sets are often nested or overlapping, so a
 future multi-budget theorem probably needs an explicit overlap-control or
 nested-accounting predicate before it can sum budgets.
+
+## Continuation Nesting
+
+Checkpoint 123 turns the overlap observation into a theorem at the continuation
+carrier level.
+
+The pointwise residue theorem is:
+
+```lean
+allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+```
+
+It says that if a label is `-1` modulo `2^(e+1)` and `d <= e`, then the label
+is also `-1` modulo `2^(d+1)`.
+
+The finite-window mass consequences are:
+
+```lean
+sourceContinuationMass_anti_mono_depth
+tailContinuationMass_anti_mono_depth
+```
+
+Thus, deeper continuation mass cannot exceed shallower continuation mass.
+
+For selected indices, the caller-facing statements are:
+
+```lean
+selectedContinuationMass_nested_of_lt
+selectedContinuationMass_overlap_of_lt_of_deeper_pos
+```
+
+This changes the interpretation of multiple selected pressure depths.  They
+should not be read as independent budget carriers by default.  The safer
+reading is a nested tower: the deepest selected continuation core sits inside
+the earlier selected continuation channels.
+
+The updated Python scan also checks whether selected depths form a prefix.  In
+the default sample, every nonempty selected-depth row is both consecutive and a
+prefix from `r_start`.  This is not yet a theorem; it is a candidate for the
+next predicate, possibly named `SelectedPressurePrefix`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index c4a1516d..2ffe189b 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -1611,3 +1611,46 @@ max pairwise overlap: 13
 
 This suggests that the next formal predicate should probably describe
 overlap/nesting control, not assume selected depths are independent.
+
+## Checkpoint 123: Continuation Nesting
+
+Checkpoint 123 proves that all-ones continuation channels are nested by depth.
+
+Pointwise residue theorem:
+
+```lean
+allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+```
+
+Count-level anti-monotonicity:
+
+```lean
+sourceContinuationMass_anti_mono_depth
+tailContinuationMass_anti_mono_depth
+```
+
+Selected-depth wrappers:
+
+```lean
+selectedContinuationMass_nested_of_lt
+selectedContinuationMass_overlap_of_lt_of_deeper_pos
+```
+
+This formally explains the checkpoint 122 observation that selected-depth
+continuation carriers were not disjoint: a deeper all-ones channel is a subset
+of every shallower all-ones channel.
+
+The overlap scan now also records prefix/consecutive fields.  In the default
+window (`odd n <= 999`, `steps = 64`, `r_start = 2`, `depth_len = 8`):
+
+```text
+rows: 500
+nonempty selected rows: 237
+nonempty prefix rows: 237 / 237
+nonempty consecutive rows: 237 / 237
+max selected depth: 7
+```
+
+The prefix observation remains experimental.  The Lean theorem currently
+proves nesting of continuation carriers, not that pressure-selected depths must
+form a prefix.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-123.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-123.md
new file mode 100644
index 00000000..f8aafca1
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-123.md
@@ -0,0 +1,149 @@
+# Report Petal 123
+
+## Goal
+
+Checkpoint 123 asked for a Lean explanation of the selected-depth overlap seen
+in checkpoint 122.
+
+The target was:
+
+```text
+deep all-ones continuation residue
+  -> shallow all-ones continuation residue
+```
+
+and then the corresponding finite-window count monotonicity.
+
+## Lean Result
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New pointwise theorem:
+
+```lean
+allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+```
+
+New count theorems:
+
+```lean
+sourceContinuationMass_anti_mono_depth
+tailContinuationMass_anti_mono_depth
+```
+
+New selected-depth wrappers:
+
+```lean
+selectedContinuationMass_nested_of_lt
+selectedContinuationMass_overlap_of_lt_of_deeper_pos
+```
+
+Meaning:
+
+```text
+j1 < j2
+  -> mass at r+j2 <= mass at r+j1
+
+positive mass at the deeper selected depth
+  -> positive mass at the shallower selected depth
+```
+
+This closes the formal explanation that selected-depth carriers overlap because
+they are nested all-ones residue cylinders.
+
+## Python Experiment
+
+Updated:
+
+```text
+python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+```
+
+Regenerated:
+
+```text
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+```
+
+New fields:
+
+```text
+selected_depths_are_prefix
+selected_depths_are_consecutive
+max_selected_depth
+missing_selected_depths
+```
+
+Default scan result:
+
+```text
+rows: 500
+rows with at least two selected depths: 52
+rows with a disjoint selected-depth pair: 0
+rows where every selected-depth pair overlaps: 52
+rows whose selected depths are a prefix from r_start: 500
+nonempty prefix rows: 237 / 237
+rows whose selected depths are consecutive: 500
+nonempty consecutive rows: 237 / 237
+max selected depth count: 6
+max selected depth: 7
+max pairwise overlap: 13
+```
+
+The prefix/consecutive observation is experimental.  It should not yet be
+promoted to a theorem without a proof of pressure monotonicity or a precise
+counterexample search.
+
+## Documentation
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-ContinuationNesting-123.md
+```
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+```
+
+## Next Implementation Candidate
+
+The natural next checkpoint is to decide whether the experimental prefix
+behavior can be formalized.
+
+Candidate thin predicates:
+
+```lean
+def SelectedPressurePrefix ...
+def HasDeepestSelectedSourcePressureDepth ...
+```
+
+Safer first theorem:
+
+```text
+if selected depth e is positive and d <= e,
+then the continuation mass at d is positive
+```
+
+This is already nearly available from checkpoint 123.  What remains is to
+connect it back to the pressure predicate itself.  That connection may be true
+only under additional monotonicity assumptions, because pressure compares
+continuation mass against retention mass, not continuation mass alone.
diff --git a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
index 67fa090c..2edeb637 100644
--- a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
+++ b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.csv
@@ -1,501 +1,501 @@
-n,steps,r_start,depth_len,selected_depths,selected_count,max_pairwise_overlap,min_pairwise_overlap,total_pair_count,disjoint_pair_count,has_disjoint_pair,first_pair,first_pair_overlap,first_pair_left_mass,first_pair_right_mass
-1,64,2,8,,0,0,0,0,0,False,,0,0,0
-3,64,2,8,,0,0,0,0,0,False,,0,0,0
-5,64,2,8,,0,0,0,0,0,False,,0,0,0
-7,64,2,8,,0,0,0,0,0,False,,0,0,0
-9,64,2,8,,0,0,0,0,0,False,,0,0,0
-11,64,2,8,,0,0,0,0,0,False,,0,0,0
-13,64,2,8,,0,0,0,0,0,False,,0,0,0
-15,64,2,8,2,1,0,0,0,0,False,,0,0,0
-17,64,2,8,,0,0,0,0,0,False,,0,0,0
-19,64,2,8,,0,0,0,0,0,False,,0,0,0
-21,64,2,8,,0,0,0,0,0,False,,0,0,0
-23,64,2,8,,0,0,0,0,0,False,,0,0,0
-25,64,2,8,,0,0,0,0,0,False,,0,0,0
-27,64,2,8,2,1,0,0,0,0,False,,0,0,0
-29,64,2,8,,0,0,0,0,0,False,,0,0,0
-31,64,2,8,2,1,0,0,0,0,False,,0,0,0
-33,64,2,8,,0,0,0,0,0,False,,0,0,0
-35,64,2,8,,0,0,0,0,0,False,,0,0,0
-37,64,2,8,,0,0,0,0,0,False,,0,0,0
-39,64,2,8,,0,0,0,0,0,False,,0,0,0
-41,64,2,8,2,1,0,0,0,0,False,,0,0,0
-43,64,2,8,,0,0,0,0,0,False,,0,0,0
-45,64,2,8,,0,0,0,0,0,False,,0,0,0
-47,64,2,8,2,1,0,0,0,0,False,,0,0,0
-49,64,2,8,,0,0,0,0,0,False,,0,0,0
-51,64,2,8,,0,0,0,0,0,False,,0,0,0
-53,64,2,8,,0,0,0,0,0,False,,0,0,0
-55,64,2,8,2,1,0,0,0,0,False,,0,0,0
-57,64,2,8,,0,0,0,0,0,False,,0,0,0
-59,64,2,8,,0,0,0,0,0,False,,0,0,0
-61,64,2,8,,0,0,0,0,0,False,,0,0,0
-63,64,2,8,2;3,2,8,8,1,0,False,2:3,8,15,8
-65,64,2,8,,0,0,0,0,0,False,,0,0,0
-67,64,2,8,,0,0,0,0,0,False,,0,0,0
-69,64,2,8,,0,0,0,0,0,False,,0,0,0
-71,64,2,8,2,1,0,0,0,0,False,,0,0,0
-73,64,2,8,2,1,0,0,0,0,False,,0,0,0
-75,64,2,8,,0,0,0,0,0,False,,0,0,0
-77,64,2,8,,0,0,0,0,0,False,,0,0,0
-79,64,2,8,,0,0,0,0,0,False,,0,0,0
-81,64,2,8,,0,0,0,0,0,False,,0,0,0
-83,64,2,8,2,1,0,0,0,0,False,,0,0,0
-85,64,2,8,,0,0,0,0,0,False,,0,0,0
-87,64,2,8,,0,0,0,0,0,False,,0,0,0
-89,64,2,8,,0,0,0,0,0,False,,0,0,0
-91,64,2,8,2,1,0,0,0,0,False,,0,0,0
-93,64,2,8,,0,0,0,0,0,False,,0,0,0
-95,64,2,8,2,1,0,0,0,0,False,,0,0,0
-97,64,2,8,2,1,0,0,0,0,False,,0,0,0
-99,64,2,8,,0,0,0,0,0,False,,0,0,0
-101,64,2,8,,0,0,0,0,0,False,,0,0,0
-103,64,2,8,2,1,0,0,0,0,False,,0,0,0
-105,64,2,8,,0,0,0,0,0,False,,0,0,0
-107,64,2,8,2,1,0,0,0,0,False,,0,0,0
-109,64,2,8,2,1,0,0,0,0,False,,0,0,0
-111,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-113,64,2,8,,0,0,0,0,0,False,,0,0,0
-115,64,2,8,,0,0,0,0,0,False,,0,0,0
-117,64,2,8,,0,0,0,0,0,False,,0,0,0
-119,64,2,8,,0,0,0,0,0,False,,0,0,0
-121,64,2,8,2,1,0,0,0,0,False,,0,0,0
-123,64,2,8,,0,0,0,0,0,False,,0,0,0
-125,64,2,8,2,1,0,0,0,0,False,,0,0,0
-127,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-129,64,2,8,2,1,0,0,0,0,False,,0,0,0
-131,64,2,8,,0,0,0,0,0,False,,0,0,0
-133,64,2,8,,0,0,0,0,0,False,,0,0,0
-135,64,2,8,,0,0,0,0,0,False,,0,0,0
-137,64,2,8,2,1,0,0,0,0,False,,0,0,0
-139,64,2,8,,0,0,0,0,0,False,,0,0,0
-141,64,2,8,,0,0,0,0,0,False,,0,0,0
-143,64,2,8,2,1,0,0,0,0,False,,0,0,0
-145,64,2,8,2,1,0,0,0,0,False,,0,0,0
-147,64,2,8,2,1,0,0,0,0,False,,0,0,0
-149,64,2,8,,0,0,0,0,0,False,,0,0,0
-151,64,2,8,,0,0,0,0,0,False,,0,0,0
-153,64,2,8,,0,0,0,0,0,False,,0,0,0
-155,64,2,8,2,1,0,0,0,0,False,,0,0,0
-157,64,2,8,,0,0,0,0,0,False,,0,0,0
-159,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-161,64,2,8,2,1,0,0,0,0,False,,0,0,0
-163,64,2,8,,0,0,0,0,0,False,,0,0,0
-165,64,2,8,2,1,0,0,0,0,False,,0,0,0
-167,64,2,8,2,1,0,0,0,0,False,,0,0,0
-169,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-171,64,2,8,2,1,0,0,0,0,False,,0,0,0
-173,64,2,8,,0,0,0,0,0,False,,0,0,0
-175,64,2,8,2,1,0,0,0,0,False,,0,0,0
-177,64,2,8,,0,0,0,0,0,False,,0,0,0
-179,64,2,8,,0,0,0,0,0,False,,0,0,0
-181,64,2,8,,0,0,0,0,0,False,,0,0,0
-183,64,2,8,2,1,0,0,0,0,False,,0,0,0
-185,64,2,8,,0,0,0,0,0,False,,0,0,0
-187,64,2,8,,0,0,0,0,0,False,,0,0,0
-189,64,2,8,2,1,0,0,0,0,False,,0,0,0
-191,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
-193,64,2,8,2,1,0,0,0,0,False,,0,0,0
-195,64,2,8,2,1,0,0,0,0,False,,0,0,0
-197,64,2,8,,0,0,0,0,0,False,,0,0,0
-199,64,2,8,2,1,0,0,0,0,False,,0,0,0
-201,64,2,8,,0,0,0,0,0,False,,0,0,0
-203,64,2,8,,0,0,0,0,0,False,,0,0,0
-205,64,2,8,,0,0,0,0,0,False,,0,0,0
-207,64,2,8,2,1,0,0,0,0,False,,0,0,0
-209,64,2,8,,0,0,0,0,0,False,,0,0,0
-211,64,2,8,,0,0,0,0,0,False,,0,0,0
-213,64,2,8,,0,0,0,0,0,False,,0,0,0
-215,64,2,8,2,1,0,0,0,0,False,,0,0,0
-217,64,2,8,,0,0,0,0,0,False,,0,0,0
-219,64,2,8,,0,0,0,0,0,False,,0,0,0
-221,64,2,8,2,1,0,0,0,0,False,,0,0,0
-223,64,2,8,2;3,2,6,6,1,0,False,2:3,6,10,6
-225,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-227,64,2,8,,0,0,0,0,0,False,,0,0,0
-229,64,2,8,,0,0,0,0,0,False,,0,0,0
-231,64,2,8,2,1,0,0,0,0,False,,0,0,0
-233,64,2,8,2,1,0,0,0,0,False,,0,0,0
-235,64,2,8,2,1,0,0,0,0,False,,0,0,0
-237,64,2,8,,0,0,0,0,0,False,,0,0,0
-239,64,2,8,2,1,0,0,0,0,False,,0,0,0
-241,64,2,8,,0,0,0,0,0,False,,0,0,0
-243,64,2,8,2,1,0,0,0,0,False,,0,0,0
-245,64,2,8,,0,0,0,0,0,False,,0,0,0
-247,64,2,8,,0,0,0,0,0,False,,0,0,0
-249,64,2,8,,0,0,0,0,0,False,,0,0,0
-251,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-253,64,2,8,2,1,0,0,0,0,False,,0,0,0
-255,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,6,5
-257,64,2,8,2,1,0,0,0,0,False,,0,0,0
-259,64,2,8,2,1,0,0,0,0,False,,0,0,0
-261,64,2,8,,0,0,0,0,0,False,,0,0,0
-263,64,2,8,2,1,0,0,0,0,False,,0,0,0
-265,64,2,8,2,1,0,0,0,0,False,,0,0,0
-267,64,2,8,,0,0,0,0,0,False,,0,0,0
-269,64,2,8,,0,0,0,0,0,False,,0,0,0
-271,64,2,8,,0,0,0,0,0,False,,0,0,0
-273,64,2,8,,0,0,0,0,0,False,,0,0,0
-275,64,2,8,2,1,0,0,0,0,False,,0,0,0
-277,64,2,8,,0,0,0,0,0,False,,0,0,0
-279,64,2,8,,0,0,0,0,0,False,,0,0,0
-281,64,2,8,,0,0,0,0,0,False,,0,0,0
-283,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-285,64,2,8,2,1,0,0,0,0,False,,0,0,0
-287,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
-289,64,2,8,,0,0,0,0,0,False,,0,0,0
-291,64,2,8,2,1,0,0,0,0,False,,0,0,0
-293,64,2,8,2,1,0,0,0,0,False,,0,0,0
-295,64,2,8,,0,0,0,0,0,False,,0,0,0
-297,64,2,8,2;3,2,6,6,1,0,False,2:3,6,10,6
-299,64,2,8,2,1,0,0,0,0,False,,0,0,0
-301,64,2,8,,0,0,0,0,0,False,,0,0,0
-303,64,2,8,2,1,0,0,0,0,False,,0,0,0
-305,64,2,8,,0,0,0,0,0,False,,0,0,0
-307,64,2,8,,0,0,0,0,0,False,,0,0,0
-309,64,2,8,,0,0,0,0,0,False,,0,0,0
-311,64,2,8,2,1,0,0,0,0,False,,0,0,0
-313,64,2,8,2,1,0,0,0,0,False,,0,0,0
-315,64,2,8,,0,0,0,0,0,False,,0,0,0
-317,64,2,8,,0,0,0,0,0,False,,0,0,0
-319,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-321,64,2,8,,0,0,0,0,0,False,,0,0,0
-323,64,2,8,2,1,0,0,0,0,False,,0,0,0
-325,64,2,8,,0,0,0,0,0,False,,0,0,0
-327,64,2,8,2,1,0,0,0,0,False,,0,0,0
-329,64,2,8,,0,0,0,0,0,False,,0,0,0
-331,64,2,8,,0,0,0,0,0,False,,0,0,0
-333,64,2,8,2,1,0,0,0,0,False,,0,0,0
-335,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-337,64,2,8,2,1,0,0,0,0,False,,0,0,0
-339,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
-341,64,2,8,,0,0,0,0,0,False,,0,0,0
-343,64,2,8,2,1,0,0,0,0,False,,0,0,0
-345,64,2,8,2,1,0,0,0,0,False,,0,0,0
-347,64,2,8,2,1,0,0,0,0,False,,0,0,0
-349,64,2,8,,0,0,0,0,0,False,,0,0,0
-351,64,2,8,2;3,2,6,6,1,0,False,2:3,6,11,6
-353,64,2,8,2,1,0,0,0,0,False,,0,0,0
-355,64,2,8,,0,0,0,0,0,False,,0,0,0
-357,64,2,8,,0,0,0,0,0,False,,0,0,0
-359,64,2,8,2,1,0,0,0,0,False,,0,0,0
-361,64,2,8,,0,0,0,0,0,False,,0,0,0
-363,64,2,8,,0,0,0,0,0,False,,0,0,0
-365,64,2,8,2,1,0,0,0,0,False,,0,0,0
-367,64,2,8,,0,0,0,0,0,False,,0,0,0
-369,64,2,8,,0,0,0,0,0,False,,0,0,0
-371,64,2,8,,0,0,0,0,0,False,,0,0,0
-373,64,2,8,,0,0,0,0,0,False,,0,0,0
-375,64,2,8,,0,0,0,0,0,False,,0,0,0
-377,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-379,64,2,8,,0,0,0,0,0,False,,0,0,0
-381,64,2,8,2,1,0,0,0,0,False,,0,0,0
-383,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-385,64,2,8,,0,0,0,0,0,False,,0,0,0
-387,64,2,8,2,1,0,0,0,0,False,,0,0,0
-389,64,2,8,2,1,0,0,0,0,False,,0,0,0
-391,64,2,8,2,1,0,0,0,0,False,,0,0,0
-393,64,2,8,,0,0,0,0,0,False,,0,0,0
-395,64,2,8,2,1,0,0,0,0,False,,0,0,0
-397,64,2,8,,0,0,0,0,0,False,,0,0,0
-399,64,2,8,2,1,0,0,0,0,False,,0,0,0
-401,64,2,8,,0,0,0,0,0,False,,0,0,0
-403,64,2,8,,0,0,0,0,0,False,,0,0,0
-405,64,2,8,,0,0,0,0,0,False,,0,0,0
-407,64,2,8,,0,0,0,0,0,False,,0,0,0
-409,64,2,8,,0,0,0,0,0,False,,0,0,0
-411,64,2,8,2,1,0,0,0,0,False,,0,0,0
-413,64,2,8,2,1,0,0,0,0,False,,0,0,0
-415,64,2,8,2,1,0,0,0,0,False,,0,0,0
-417,64,2,8,2,1,0,0,0,0,False,,0,0,0
-419,64,2,8,,0,0,0,0,0,False,,0,0,0
-421,64,2,8,,0,0,0,0,0,False,,0,0,0
-423,64,2,8,,0,0,0,0,0,False,,0,0,0
-425,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-427,64,2,8,,0,0,0,0,0,False,,0,0,0
-429,64,2,8,2,1,0,0,0,0,False,,0,0,0
-431,64,2,8,,0,0,0,0,0,False,,0,0,0
-433,64,2,8,,0,0,0,0,0,False,,0,0,0
-435,64,2,8,,0,0,0,0,0,False,,0,0,0
-437,64,2,8,2,1,0,0,0,0,False,,0,0,0
-439,64,2,8,,0,0,0,0,0,False,,0,0,0
-441,64,2,8,,0,0,0,0,0,False,,0,0,0
-443,64,2,8,,0,0,0,0,0,False,,0,0,0
-445,64,2,8,2,1,0,0,0,0,False,,0,0,0
-447,64,2,8,2;3;4;5,4,9,4,6,0,False,2:3,9,14,9
-449,64,2,8,2,1,0,0,0,0,False,,0,0,0
-451,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-453,64,2,8,,0,0,0,0,0,False,,0,0,0
-455,64,2,8,,0,0,0,0,0,False,,0,0,0
-457,64,2,8,2,1,0,0,0,0,False,,0,0,0
-459,64,2,8,2,1,0,0,0,0,False,,0,0,0
-461,64,2,8,,0,0,0,0,0,False,,0,0,0
-463,64,2,8,2,1,0,0,0,0,False,,0,0,0
-465,64,2,8,,0,0,0,0,0,False,,0,0,0
-467,64,2,8,2,1,0,0,0,0,False,,0,0,0
-469,64,2,8,,0,0,0,0,0,False,,0,0,0
-471,64,2,8,2,1,0,0,0,0,False,,0,0,0
-473,64,2,8,,0,0,0,0,0,False,,0,0,0
-475,64,2,8,,0,0,0,0,0,False,,0,0,0
-477,64,2,8,,0,0,0,0,0,False,,0,0,0
-479,64,2,8,2,1,0,0,0,0,False,,0,0,0
-481,64,2,8,,0,0,0,0,0,False,,0,0,0
-483,64,2,8,,0,0,0,0,0,False,,0,0,0
-485,64,2,8,2,1,0,0,0,0,False,,0,0,0
-487,64,2,8,2,1,0,0,0,0,False,,0,0,0
-489,64,2,8,,0,0,0,0,0,False,,0,0,0
-491,64,2,8,2,1,0,0,0,0,False,,0,0,0
-493,64,2,8,,0,0,0,0,0,False,,0,0,0
-495,64,2,8,2,1,0,0,0,0,False,,0,0,0
-497,64,2,8,,0,0,0,0,0,False,,0,0,0
-499,64,2,8,,0,0,0,0,0,False,,0,0,0
-501,64,2,8,2,1,0,0,0,0,False,,0,0,0
-503,64,2,8,2,1,0,0,0,0,False,,0,0,0
-505,64,2,8,,0,0,0,0,0,False,,0,0,0
-507,64,2,8,,0,0,0,0,0,False,,0,0,0
-509,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
-511,64,2,8,2;3;4;5;6;7,6,6,2,15,0,False,2:3,6,8,6
-513,64,2,8,,0,0,0,0,0,False,,0,0,0
-515,64,2,8,2,1,0,0,0,0,False,,0,0,0
-517,64,2,8,2,1,0,0,0,0,False,,0,0,0
-519,64,2,8,,0,0,0,0,0,False,,0,0,0
-521,64,2,8,2,1,0,0,0,0,False,,0,0,0
-523,64,2,8,2,1,0,0,0,0,False,,0,0,0
-525,64,2,8,,0,0,0,0,0,False,,0,0,0
-527,64,2,8,2,1,0,0,0,0,False,,0,0,0
-529,64,2,8,,0,0,0,0,0,False,,0,0,0
-531,64,2,8,2,1,0,0,0,0,False,,0,0,0
-533,64,2,8,,0,0,0,0,0,False,,0,0,0
-535,64,2,8,,0,0,0,0,0,False,,0,0,0
-537,64,2,8,,0,0,0,0,0,False,,0,0,0
-539,64,2,8,2,1,0,0,0,0,False,,0,0,0
-541,64,2,8,,0,0,0,0,0,False,,0,0,0
-543,64,2,8,2;3,2,9,9,1,0,False,2:3,9,17,9
-545,64,2,8,,0,0,0,0,0,False,,0,0,0
-547,64,2,8,,0,0,0,0,0,False,,0,0,0
-549,64,2,8,2,1,0,0,0,0,False,,0,0,0
-551,64,2,8,,0,0,0,0,0,False,,0,0,0
-553,64,2,8,2,1,0,0,0,0,False,,0,0,0
-555,64,2,8,,0,0,0,0,0,False,,0,0,0
-557,64,2,8,,0,0,0,0,0,False,,0,0,0
-559,64,2,8,,0,0,0,0,0,False,,0,0,0
-561,64,2,8,,0,0,0,0,0,False,,0,0,0
-563,64,2,8,,0,0,0,0,0,False,,0,0,0
-565,64,2,8,,0,0,0,0,0,False,,0,0,0
-567,64,2,8,2,1,0,0,0,0,False,,0,0,0
-569,64,2,8,,0,0,0,0,0,False,,0,0,0
-571,64,2,8,,0,0,0,0,0,False,,0,0,0
-573,64,2,8,2,1,0,0,0,0,False,,0,0,0
-575,64,2,8,2;3;4,3,3,2,3,0,False,2:3,3,4,3
-577,64,2,8,,0,0,0,0,0,False,,0,0,0
-579,64,2,8,,0,0,0,0,0,False,,0,0,0
-581,64,2,8,2,1,0,0,0,0,False,,0,0,0
-583,64,2,8,,0,0,0,0,0,False,,0,0,0
-585,64,2,8,,0,0,0,0,0,False,,0,0,0
-587,64,2,8,2,1,0,0,0,0,False,,0,0,0
-589,64,2,8,2,1,0,0,0,0,False,,0,0,0
-591,64,2,8,,0,0,0,0,0,False,,0,0,0
-593,64,2,8,2,1,0,0,0,0,False,,0,0,0
-595,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-597,64,2,8,,0,0,0,0,0,False,,0,0,0
-599,64,2,8,2,1,0,0,0,0,False,,0,0,0
-601,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-603,64,2,8,,0,0,0,0,0,False,,0,0,0
-605,64,2,8,,0,0,0,0,0,False,,0,0,0
-607,64,2,8,2,1,0,0,0,0,False,,0,0,0
-609,64,2,8,2,1,0,0,0,0,False,,0,0,0
-611,64,2,8,,0,0,0,0,0,False,,0,0,0
-613,64,2,8,,0,0,0,0,0,False,,0,0,0
-615,64,2,8,,0,0,0,0,0,False,,0,0,0
-617,64,2,8,2,1,0,0,0,0,False,,0,0,0
-619,64,2,8,2,1,0,0,0,0,False,,0,0,0
-621,64,2,8,2,1,0,0,0,0,False,,0,0,0
-623,64,2,8,2,1,0,0,0,0,False,,0,0,0
-625,64,2,8,,0,0,0,0,0,False,,0,0,0
-627,64,2,8,2,1,0,0,0,0,False,,0,0,0
-629,64,2,8,,0,0,0,0,0,False,,0,0,0
-631,64,2,8,,0,0,0,0,0,False,,0,0,0
-633,64,2,8,,0,0,0,0,0,False,,0,0,0
-635,64,2,8,,0,0,0,0,0,False,,0,0,0
-637,64,2,8,2,1,0,0,0,0,False,,0,0,0
-639,64,2,8,2;3;4;5,4,9,3,6,0,False,2:3,9,17,9
-641,64,2,8,,0,0,0,0,0,False,,0,0,0
-643,64,2,8,,0,0,0,0,0,False,,0,0,0
-645,64,2,8,2,1,0,0,0,0,False,,0,0,0
-647,64,2,8,,0,0,0,0,0,False,,0,0,0
-649,64,2,8,2,1,0,0,0,0,False,,0,0,0
-651,64,2,8,2,1,0,0,0,0,False,,0,0,0
-653,64,2,8,,0,0,0,0,0,False,,0,0,0
-655,64,2,8,2,1,0,0,0,0,False,,0,0,0
-657,64,2,8,,0,0,0,0,0,False,,0,0,0
-659,64,2,8,,0,0,0,0,0,False,,0,0,0
-661,64,2,8,2,1,0,0,0,0,False,,0,0,0
-663,64,2,8,,0,0,0,0,0,False,,0,0,0
-665,64,2,8,,0,0,0,0,0,False,,0,0,0
-667,64,2,8,2,1,0,0,0,0,False,,0,0,0
-669,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-671,64,2,8,2;3;4;5;6,5,8,2,10,0,False,2:3,8,13,8
-673,64,2,8,,0,0,0,0,0,False,,0,0,0
-675,64,2,8,2,1,0,0,0,0,False,,0,0,0
-677,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-679,64,2,8,,0,0,0,0,0,False,,0,0,0
-681,64,2,8,2;3;4;5;6;7,6,6,2,15,0,False,2:3,6,8,6
-683,64,2,8,,0,0,0,0,0,False,,0,0,0
-685,64,2,8,2,1,0,0,0,0,False,,0,0,0
-687,64,2,8,2,1,0,0,0,0,False,,0,0,0
-689,64,2,8,2,1,0,0,0,0,False,,0,0,0
-691,64,2,8,2,1,0,0,0,0,False,,0,0,0
-693,64,2,8,,0,0,0,0,0,False,,0,0,0
-695,64,2,8,2,1,0,0,0,0,False,,0,0,0
-697,64,2,8,2,1,0,0,0,0,False,,0,0,0
-699,64,2,8,,0,0,0,0,0,False,,0,0,0
-701,64,2,8,2,1,0,0,0,0,False,,0,0,0
-703,64,2,8,2;3,2,12,12,1,0,False,2:3,12,22,12
-705,64,2,8,,0,0,0,0,0,False,,0,0,0
-707,64,2,8,2,1,0,0,0,0,False,,0,0,0
-709,64,2,8,,0,0,0,0,0,False,,0,0,0
-711,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,6,4
-713,64,2,8,,0,0,0,0,0,False,,0,0,0
-715,64,2,8,,0,0,0,0,0,False,,0,0,0
-717,64,2,8,,0,0,0,0,0,False,,0,0,0
-719,64,2,8,2,1,0,0,0,0,False,,0,0,0
-721,64,2,8,,0,0,0,0,0,False,,0,0,0
-723,64,2,8,,0,0,0,0,0,False,,0,0,0
-725,64,2,8,,0,0,0,0,0,False,,0,0,0
-727,64,2,8,,0,0,0,0,0,False,,0,0,0
-729,64,2,8,,0,0,0,0,0,False,,0,0,0
-731,64,2,8,2,1,0,0,0,0,False,,0,0,0
-733,64,2,8,2,1,0,0,0,0,False,,0,0,0
-735,64,2,8,2,1,0,0,0,0,False,,0,0,0
-737,64,2,8,2,1,0,0,0,0,False,,0,0,0
-739,64,2,8,,0,0,0,0,0,False,,0,0,0
-741,64,2,8,,0,0,0,0,0,False,,0,0,0
-743,64,2,8,2,1,0,0,0,0,False,,0,0,0
-745,64,2,8,,0,0,0,0,0,False,,0,0,0
-747,64,2,8,,0,0,0,0,0,False,,0,0,0
-749,64,2,8,,0,0,0,0,0,False,,0,0,0
-751,64,2,8,2,1,0,0,0,0,False,,0,0,0
-753,64,2,8,,0,0,0,0,0,False,,0,0,0
-755,64,2,8,2;3,2,4,4,1,0,False,2:3,4,7,4
-757,64,2,8,2,1,0,0,0,0,False,,0,0,0
-759,64,2,8,,0,0,0,0,0,False,,0,0,0
-761,64,2,8,,0,0,0,0,0,False,,0,0,0
-763,64,2,8,2,1,0,0,0,0,False,,0,0,0
-765,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
-767,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,7,5
-769,64,2,8,,0,0,0,0,0,False,,0,0,0
-771,64,2,8,,0,0,0,0,0,False,,0,0,0
-773,64,2,8,2,1,0,0,0,0,False,,0,0,0
-775,64,2,8,2,1,0,0,0,0,False,,0,0,0
-777,64,2,8,,0,0,0,0,0,False,,0,0,0
-779,64,2,8,,0,0,0,0,0,False,,0,0,0
-781,64,2,8,2,1,0,0,0,0,False,,0,0,0
-783,64,2,8,2,1,0,0,0,0,False,,0,0,0
-785,64,2,8,2,1,0,0,0,0,False,,0,0,0
-787,64,2,8,,0,0,0,0,0,False,,0,0,0
-789,64,2,8,,0,0,0,0,0,False,,0,0,0
-791,64,2,8,2,1,0,0,0,0,False,,0,0,0
-793,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-795,64,2,8,2;3;4;5;6,5,10,3,10,0,False,2:3,10,14,10
-797,64,2,8,2,1,0,0,0,0,False,,0,0,0
-799,64,2,8,2,1,0,0,0,0,False,,0,0,0
-801,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-803,64,2,8,,0,0,0,0,0,False,,0,0,0
-805,64,2,8,,0,0,0,0,0,False,,0,0,0
-807,64,2,8,2;3;4;5;6,5,5,2,10,0,False,2:3,5,8,5
-809,64,2,8,2,1,0,0,0,0,False,,0,0,0
-811,64,2,8,2,1,0,0,0,0,False,,0,0,0
-813,64,2,8,,0,0,0,0,0,False,,0,0,0
-815,64,2,8,2,1,0,0,0,0,False,,0,0,0
-817,64,2,8,,0,0,0,0,0,False,,0,0,0
-819,64,2,8,,0,0,0,0,0,False,,0,0,0
-821,64,2,8,,0,0,0,0,0,False,,0,0,0
-823,64,2,8,2,1,0,0,0,0,False,,0,0,0
-825,64,2,8,2,1,0,0,0,0,False,,0,0,0
-827,64,2,8,,0,0,0,0,0,False,,0,0,0
-829,64,2,8,2,1,0,0,0,0,False,,0,0,0
-831,64,2,8,2;3,2,9,9,1,0,False,2:3,9,17,9
-833,64,2,8,,0,0,0,0,0,False,,0,0,0
-835,64,2,8,2,1,0,0,0,0,False,,0,0,0
-837,64,2,8,,0,0,0,0,0,False,,0,0,0
-839,64,2,8,,0,0,0,0,0,False,,0,0,0
-841,64,2,8,,0,0,0,0,0,False,,0,0,0
-843,64,2,8,,0,0,0,0,0,False,,0,0,0
-845,64,2,8,,0,0,0,0,0,False,,0,0,0
-847,64,2,8,2,1,0,0,0,0,False,,0,0,0
-849,64,2,8,2,1,0,0,0,0,False,,0,0,0
-851,64,2,8,2,1,0,0,0,0,False,,0,0,0
-853,64,2,8,,0,0,0,0,0,False,,0,0,0
-855,64,2,8,,0,0,0,0,0,False,,0,0,0
-857,64,2,8,,0,0,0,0,0,False,,0,0,0
-859,64,2,8,2,1,0,0,0,0,False,,0,0,0
-861,64,2,8,2,1,0,0,0,0,False,,0,0,0
-863,64,2,8,2;3,2,2,2,1,0,False,2:3,2,3,2
-865,64,2,8,2,1,0,0,0,0,False,,0,0,0
-867,64,2,8,,0,0,0,0,0,False,,0,0,0
-869,64,2,8,,0,0,0,0,0,False,,0,0,0
-871,64,2,8,2;3;4,3,13,7,3,0,False,2:3,13,23,13
-873,64,2,8,2,1,0,0,0,0,False,,0,0,0
-875,64,2,8,,0,0,0,0,0,False,,0,0,0
-877,64,2,8,,0,0,0,0,0,False,,0,0,0
-879,64,2,8,2,1,0,0,0,0,False,,0,0,0
-881,64,2,8,2,1,0,0,0,0,False,,0,0,0
-883,64,2,8,,0,0,0,0,0,False,,0,0,0
-885,64,2,8,2,1,0,0,0,0,False,,0,0,0
-887,64,2,8,,0,0,0,0,0,False,,0,0,0
-889,64,2,8,2,1,0,0,0,0,False,,0,0,0
-891,64,2,8,,0,0,0,0,0,False,,0,0,0
-893,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-895,64,2,8,2;3;4;5;6,5,10,3,10,0,False,2:3,10,14,10
-897,64,2,8,,0,0,0,0,0,False,,0,0,0
-899,64,2,8,2,1,0,0,0,0,False,,0,0,0
-901,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-903,64,2,8,2,1,0,0,0,0,False,,0,0,0
-905,64,2,8,,0,0,0,0,0,False,,0,0,0
-907,64,2,8,2;3;4;5,4,4,2,6,0,False,2:3,4,5,4
-909,64,2,8,,0,0,0,0,0,False,,0,0,0
-911,64,2,8,2,1,0,0,0,0,False,,0,0,0
-913,64,2,8,2,1,0,0,0,0,False,,0,0,0
-915,64,2,8,2,1,0,0,0,0,False,,0,0,0
-917,64,2,8,,0,0,0,0,0,False,,0,0,0
-919,64,2,8,2,1,0,0,0,0,False,,0,0,0
-921,64,2,8,2,1,0,0,0,0,False,,0,0,0
-923,64,2,8,,0,0,0,0,0,False,,0,0,0
-925,64,2,8,2,1,0,0,0,0,False,,0,0,0
-927,64,2,8,2;3,2,7,7,1,0,False,2:3,7,13,7
-929,64,2,8,2,1,0,0,0,0,False,,0,0,0
-931,64,2,8,,0,0,0,0,0,False,,0,0,0
-933,64,2,8,2,1,0,0,0,0,False,,0,0,0
-935,64,2,8,2,1,0,0,0,0,False,,0,0,0
-937,64,2,8,2;3,2,12,12,1,0,False,2:3,12,22,12
-939,64,2,8,2;3,2,5,5,1,0,False,2:3,5,9,5
-941,64,2,8,2,1,0,0,0,0,False,,0,0,0
-943,64,2,8,2,1,0,0,0,0,False,,0,0,0
-945,64,2,8,,0,0,0,0,0,False,,0,0,0
-947,64,2,8,,0,0,0,0,0,False,,0,0,0
-949,64,2,8,,0,0,0,0,0,False,,0,0,0
-951,64,2,8,,0,0,0,0,0,False,,0,0,0
-953,64,2,8,,0,0,0,0,0,False,,0,0,0
-955,64,2,8,,0,0,0,0,0,False,,0,0,0
-957,64,2,8,2,1,0,0,0,0,False,,0,0,0
-959,64,2,8,2,1,0,0,0,0,False,,0,0,0
-961,64,2,8,,0,0,0,0,0,False,,0,0,0
-963,64,2,8,,0,0,0,0,0,False,,0,0,0
-965,64,2,8,,0,0,0,0,0,False,,0,0,0
-967,64,2,8,2,1,0,0,0,0,False,,0,0,0
-969,64,2,8,,0,0,0,0,0,False,,0,0,0
-971,64,2,8,,0,0,0,0,0,False,,0,0,0
-973,64,2,8,2,1,0,0,0,0,False,,0,0,0
-975,64,2,8,2,1,0,0,0,0,False,,0,0,0
-977,64,2,8,2,1,0,0,0,0,False,,0,0,0
-979,64,2,8,,0,0,0,0,0,False,,0,0,0
-981,64,2,8,,0,0,0,0,0,False,,0,0,0
-983,64,2,8,2,1,0,0,0,0,False,,0,0,0
-985,64,2,8,,0,0,0,0,0,False,,0,0,0
-987,64,2,8,,0,0,0,0,0,False,,0,0,0
-989,64,2,8,,0,0,0,0,0,False,,0,0,0
-991,64,2,8,2,1,0,0,0,0,False,,0,0,0
-993,64,2,8,,0,0,0,0,0,False,,0,0,0
-995,64,2,8,,0,0,0,0,0,False,,0,0,0
-997,64,2,8,,0,0,0,0,0,False,,0,0,0
-999,64,2,8,,0,0,0,0,0,False,,0,0,0
+n,steps,r_start,depth_len,selected_depths,selected_count,selected_depths_are_prefix,selected_depths_are_consecutive,max_selected_depth,missing_selected_depths,max_pairwise_overlap,min_pairwise_overlap,total_pair_count,disjoint_pair_count,has_disjoint_pair,first_pair,first_pair_overlap,first_pair_left_mass,first_pair_right_mass
+1,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+3,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+5,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+7,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+9,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+11,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+13,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+15,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+17,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+19,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+21,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+23,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+25,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+27,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+29,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+31,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+33,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+35,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+37,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+39,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+41,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+43,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+45,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+47,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+49,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+51,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+53,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+55,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+57,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+59,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+61,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+63,64,2,8,2;3,2,True,True,3,,8,8,1,0,False,2:3,8,15,8
+65,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+67,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+69,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+71,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+73,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+75,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+77,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+79,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+81,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+83,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+85,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+87,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+89,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+91,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+93,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+95,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+97,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+99,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+101,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+103,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+105,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+107,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+109,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+111,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+113,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+115,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+117,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+119,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+121,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+123,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+125,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+127,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+129,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+131,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+133,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+135,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+137,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+139,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+141,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+143,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+145,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+147,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+149,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+151,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+153,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+155,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+157,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+159,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+161,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+163,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+165,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+167,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+169,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+171,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+173,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+175,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+177,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+179,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+181,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+183,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+185,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+187,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+189,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+191,64,2,8,2;3;4,3,True,True,4,,3,2,3,0,False,2:3,3,4,3
+193,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+195,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+197,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+199,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+201,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+203,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+205,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+207,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+209,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+211,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+213,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+215,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+217,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+219,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+221,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+223,64,2,8,2;3,2,True,True,3,,6,6,1,0,False,2:3,6,10,6
+225,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+227,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+229,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+231,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+233,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+235,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+237,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+239,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+241,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+243,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+245,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+247,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+249,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+251,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+253,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+255,64,2,8,2;3;4;5;6,5,True,True,6,,5,2,10,0,False,2:3,5,6,5
+257,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+259,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+261,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+263,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+265,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+267,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+269,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+271,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+273,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+275,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+277,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+279,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+281,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+283,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+285,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+287,64,2,8,2;3,2,True,True,3,,2,2,1,0,False,2:3,2,3,2
+289,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+291,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+293,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+295,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+297,64,2,8,2;3,2,True,True,3,,6,6,1,0,False,2:3,6,10,6
+299,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+301,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+303,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+305,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+307,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+309,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+311,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+313,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+315,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+317,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+319,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+321,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+323,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+325,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+327,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+329,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+331,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+333,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+335,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+337,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+339,64,2,8,2;3;4,3,True,True,4,,3,2,3,0,False,2:3,3,4,3
+341,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+343,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+345,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+347,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+349,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+351,64,2,8,2;3,2,True,True,3,,6,6,1,0,False,2:3,6,11,6
+353,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+355,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+357,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+359,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+361,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+363,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+365,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+367,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+369,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+371,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+373,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+375,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+377,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+379,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+381,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+383,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+385,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+387,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+389,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+391,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+393,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+395,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+397,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+399,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+401,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+403,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+405,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+407,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+409,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+411,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+413,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+415,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+417,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+419,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+421,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+423,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+425,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+427,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+429,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+431,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+433,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+435,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+437,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+439,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+441,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+443,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+445,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+447,64,2,8,2;3;4;5,4,True,True,5,,9,4,6,0,False,2:3,9,14,9
+449,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+451,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+453,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+455,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+457,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+459,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+461,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+463,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+465,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+467,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+469,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+471,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+473,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+475,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+477,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+479,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+481,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+483,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+485,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+487,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+489,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+491,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+493,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+495,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+497,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+499,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+501,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+503,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+505,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+507,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+509,64,2,8,2;3;4,3,True,True,4,,3,2,3,0,False,2:3,3,4,3
+511,64,2,8,2;3;4;5;6;7,6,True,True,7,,6,2,15,0,False,2:3,6,8,6
+513,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+515,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+517,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+519,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+521,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+523,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+525,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+527,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+529,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+531,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+533,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+535,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+537,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+539,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+541,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+543,64,2,8,2;3,2,True,True,3,,9,9,1,0,False,2:3,9,17,9
+545,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+547,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+549,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+551,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+553,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+555,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+557,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+559,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+561,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+563,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+565,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+567,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+569,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+571,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+573,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+575,64,2,8,2;3;4,3,True,True,4,,3,2,3,0,False,2:3,3,4,3
+577,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+579,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+581,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+583,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+585,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+587,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+589,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+591,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+593,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+595,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+597,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+599,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+601,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+603,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+605,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+607,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+609,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+611,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+613,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+615,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+617,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+619,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+621,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+623,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+625,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+627,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+629,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+631,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+633,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+635,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+637,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+639,64,2,8,2;3;4;5,4,True,True,5,,9,3,6,0,False,2:3,9,17,9
+641,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+643,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+645,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+647,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+649,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+651,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+653,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+655,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+657,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+659,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+661,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+663,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+665,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+667,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+669,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+671,64,2,8,2;3;4;5;6,5,True,True,6,,8,2,10,0,False,2:3,8,13,8
+673,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+675,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+677,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+679,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+681,64,2,8,2;3;4;5;6;7,6,True,True,7,,6,2,15,0,False,2:3,6,8,6
+683,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+685,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+687,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+689,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+691,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+693,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+695,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+697,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+699,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+701,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+703,64,2,8,2;3,2,True,True,3,,12,12,1,0,False,2:3,12,22,12
+705,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+707,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+709,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+711,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,6,4
+713,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+715,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+717,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+719,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+721,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+723,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+725,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+727,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+729,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+731,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+733,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+735,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+737,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+739,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+741,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+743,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+745,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+747,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+749,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+751,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+753,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+755,64,2,8,2;3,2,True,True,3,,4,4,1,0,False,2:3,4,7,4
+757,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+759,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+761,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+763,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+765,64,2,8,2;3,2,True,True,3,,2,2,1,0,False,2:3,2,3,2
+767,64,2,8,2;3;4;5;6,5,True,True,6,,5,2,10,0,False,2:3,5,7,5
+769,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+771,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+773,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+775,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+777,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+779,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+781,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+783,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+785,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+787,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+789,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+791,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+793,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+795,64,2,8,2;3;4;5;6,5,True,True,6,,10,3,10,0,False,2:3,10,14,10
+797,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+799,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+801,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+803,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+805,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+807,64,2,8,2;3;4;5;6,5,True,True,6,,5,2,10,0,False,2:3,5,8,5
+809,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+811,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+813,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+815,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+817,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+819,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+821,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+823,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+825,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+827,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+829,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+831,64,2,8,2;3,2,True,True,3,,9,9,1,0,False,2:3,9,17,9
+833,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+835,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+837,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+839,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+841,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+843,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+845,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+847,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+849,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+851,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+853,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+855,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+857,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+859,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+861,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+863,64,2,8,2;3,2,True,True,3,,2,2,1,0,False,2:3,2,3,2
+865,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+867,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+869,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+871,64,2,8,2;3;4,3,True,True,4,,13,7,3,0,False,2:3,13,23,13
+873,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+875,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+877,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+879,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+881,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+883,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+885,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+887,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+889,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+891,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+893,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+895,64,2,8,2;3;4;5;6,5,True,True,6,,10,3,10,0,False,2:3,10,14,10
+897,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+899,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+901,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+903,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+905,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+907,64,2,8,2;3;4;5,4,True,True,5,,4,2,6,0,False,2:3,4,5,4
+909,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+911,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+913,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+915,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+917,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+919,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+921,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+923,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+925,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+927,64,2,8,2;3,2,True,True,3,,7,7,1,0,False,2:3,7,13,7
+929,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+931,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+933,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+935,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+937,64,2,8,2;3,2,True,True,3,,12,12,1,0,False,2:3,12,22,12
+939,64,2,8,2;3,2,True,True,3,,5,5,1,0,False,2:3,5,9,5
+941,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+943,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+945,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+947,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+949,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+951,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+953,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+955,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+957,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+959,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+961,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+963,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+965,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+967,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+969,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+971,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+973,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+975,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+977,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+979,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+981,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+983,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+985,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+987,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+989,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+991,64,2,8,2,1,True,True,2,,0,0,0,0,False,,0,0,0
+993,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+995,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+997,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
+999,64,2,8,,0,True,True,0,,0,0,0,0,False,,0,0,0
diff --git a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
index e303faca..19df078a 100644
--- a/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
+++ b/python/Collatz/PetalBridge/results/selected_depth_overlap_scan.md
@@ -4,25 +4,30 @@
 - rows with at least two selected depths: `52`
 - rows with a disjoint selected-depth pair: `0`
 - rows where every selected-depth pair overlaps: `52`
+- rows whose selected depths are a prefix from `r_start`: `500`
+- nonempty prefix rows: `237` / `237`
+- rows whose selected depths are consecutive: `500`
+- nonempty consecutive rows: `237` / `237`
 - max selected depth count: `6`
+- max selected depth: `7`
 - max pairwise overlap: `13`
 
 ## Top Multi-Witness Samples
 
-| n | selected depths | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |
-|---:|---|---:|---:|---:|---|---:|---|
-| 511 | 2;3;4;5;6;7 | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
-| 681 | 2;3;4;5;6;7 | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
-| 255 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 6:5 |
-| 671 | 2;3;4;5;6 | 10 | 0 | 8 | 2:3 | 8 | 13:8 |
-| 767 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 7:5 |
-| 795 | 2;3;4;5;6 | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
-| 807 | 2;3;4;5;6 | 10 | 0 | 5 | 2:3 | 5 | 8:5 |
-| 895 | 2;3;4;5;6 | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
-| 127 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
-| 169 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
-| 225 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
-| 383 | 2;3;4;5 | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| n | selected depths | prefix | consecutive | missing | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |
+|---:|---|---|---|---|---:|---:|---:|---|---:|---|
+| 511 | 2;3;4;5;6;7 | True | True |  | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
+| 681 | 2;3;4;5;6;7 | True | True |  | 15 | 0 | 6 | 2:3 | 6 | 8:6 |
+| 255 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 6:5 |
+| 671 | 2;3;4;5;6 | True | True |  | 10 | 0 | 8 | 2:3 | 8 | 13:8 |
+| 767 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 7:5 |
+| 795 | 2;3;4;5;6 | True | True |  | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
+| 807 | 2;3;4;5;6 | True | True |  | 10 | 0 | 5 | 2:3 | 5 | 8:5 |
+| 895 | 2;3;4;5;6 | True | True |  | 10 | 0 | 10 | 2:3 | 10 | 14:10 |
+| 127 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 169 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 225 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
+| 383 | 2;3;4;5 | True | True |  | 6 | 0 | 4 | 2:3 | 4 | 5:4 |
 
 ## Reading
 
@@ -32,3 +37,7 @@ in this finite orbit window.  This is only experimental evidence.
 If disjoint pairs are common, a future Lean predicate could target
 `DisjointTowerTargets`.  If all selected pairs overlap, the right
 formal condition may need to express nested selected-depth behavior.
+
+The prefix/consecutive fields test the next hypothesis: selected
+depths may form a visible initial tower segment.  A prefix row means
+`r_start, r_start+1, ..., max_selected_depth` are all selected.
diff --git a/python/Collatz/PetalBridge/selected_depth_overlap_scan.py b/python/Collatz/PetalBridge/selected_depth_overlap_scan.py
index 592ee488..c14d843b 100644
--- a/python/Collatz/PetalBridge/selected_depth_overlap_scan.py
+++ b/python/Collatz/PetalBridge/selected_depth_overlap_scan.py
@@ -31,6 +31,10 @@ class OverlapRow:
     depth_len: int
     selected_depths: str
     selected_count: int
+    selected_depths_are_prefix: bool
+    selected_depths_are_consecutive: bool
+    max_selected_depth: int
+    missing_selected_depths: str
     max_pairwise_overlap: int
     min_pairwise_overlap: int
     total_pair_count: int
@@ -90,10 +94,28 @@ def selected_depths(labels: list[int], r_start: int, depth_len: int) -> list[int
     return selected
 
 
+def depths_are_consecutive(depths: list[int]) -> bool:
+    return all(right == left + 1 for left, right in zip(depths, depths[1:]))
+
+
+def depths_are_prefix(depths: list[int], r_start: int) -> bool:
+    if not depths:
+        return True
+    return depths[0] == r_start and depths_are_consecutive(depths)
+
+
+def missing_depths_from_prefix(depths: list[int], r_start: int) -> list[int]:
+    if not depths:
+        return []
+    selected = set(depths)
+    return [depth for depth in range(r_start, max(depths) + 1) if depth not in selected]
+
+
 def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OverlapRow:
     labels = orbit_labels(n, steps)
     depths = selected_depths(labels, r_start, depth_len)
     index_sets = {depth: continuation_indices(labels, depth) for depth in depths}
+    missing = missing_depths_from_prefix(depths, r_start)
     pair_stats: list[tuple[int, int, int]] = []
     for left, right in combinations(depths, 2):
         pair_stats.append((left, right, len(index_sets[left] & index_sets[right])))
@@ -121,6 +143,10 @@ def row_for(n: int, steps: int, r_start: int, depth_len: int) -> OverlapRow:
         depth_len=depth_len,
         selected_depths=";".join(str(depth) for depth in depths),
         selected_count=len(depths),
+        selected_depths_are_prefix=depths_are_prefix(depths, r_start),
+        selected_depths_are_consecutive=depths_are_consecutive(depths),
+        max_selected_depth=max(depths, default=0),
+        missing_selected_depths=";".join(str(depth) for depth in missing),
         max_pairwise_overlap=max_overlap,
         min_pairwise_overlap=min_overlap,
         total_pair_count=len(pair_stats),
@@ -140,7 +166,11 @@ def scan(max_n: int, steps: int, r_start: int, depth_len: int) -> list[OverlapRo
 def write_csv(rows: list[OverlapRow], path: Path) -> None:
     path.parent.mkdir(parents=True, exist_ok=True)
     with path.open("w", newline="", encoding="utf-8") as f:
-        writer = csv.DictWriter(f, fieldnames=list(OverlapRow.__dataclass_fields__))
+        writer = csv.DictWriter(
+            f,
+            fieldnames=list(OverlapRow.__dataclass_fields__),
+            lineterminator="\n",
+        )
         writer.writeheader()
         for row in rows:
             writer.writerow(row.__dict__)
@@ -151,7 +181,13 @@ def write_summary(rows: list[OverlapRow], path: Path) -> None:
     multi = [row for row in rows if row.selected_count >= 2]
     with_disjoint = [row for row in multi if row.has_disjoint_pair]
     all_overlap = [row for row in multi if not row.has_disjoint_pair]
+    prefix_rows = [row for row in rows if row.selected_depths_are_prefix]
+    consecutive_rows = [row for row in rows if row.selected_depths_are_consecutive]
+    nonempty = [row for row in rows if row.selected_count > 0]
+    nonempty_prefix = [row for row in nonempty if row.selected_depths_are_prefix]
+    nonempty_consecutive = [row for row in nonempty if row.selected_depths_are_consecutive]
     max_selected = max((row.selected_count for row in rows), default=0)
+    max_selected_depth = max((row.max_selected_depth for row in rows), default=0)
     max_overlap = max((row.max_pairwise_overlap for row in rows), default=0)
     samples = sorted(
         multi,
@@ -164,20 +200,26 @@ def write_summary(rows: list[OverlapRow], path: Path) -> None:
         f"- rows with at least two selected depths: `{len(multi)}`",
         f"- rows with a disjoint selected-depth pair: `{len(with_disjoint)}`",
         f"- rows where every selected-depth pair overlaps: `{len(all_overlap)}`",
+        f"- rows whose selected depths are a prefix from `r_start`: `{len(prefix_rows)}`",
+        f"- nonempty prefix rows: `{len(nonempty_prefix)}` / `{len(nonempty)}`",
+        f"- rows whose selected depths are consecutive: `{len(consecutive_rows)}`",
+        f"- nonempty consecutive rows: `{len(nonempty_consecutive)}` / `{len(nonempty)}`",
         f"- max selected depth count: `{max_selected}`",
+        f"- max selected depth: `{max_selected_depth}`",
         f"- max pairwise overlap: `{max_overlap}`",
         "",
         "## Top Multi-Witness Samples",
         "",
-        "| n | selected depths | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |",
-        "|---:|---|---:|---:|---:|---|---:|---|",
+        "| n | selected depths | prefix | consecutive | missing | pairs | disjoint pairs | max overlap | first pair | first overlap | masses |",
+        "|---:|---|---|---|---|---:|---:|---:|---|---:|---|",
     ]
     for row in samples:
         lines.append(
             "| "
-            f"{row.n} | {row.selected_depths} | {row.total_pair_count} | "
-            f"{row.disjoint_pair_count} | {row.max_pairwise_overlap} | "
-            f"{row.first_pair} | {row.first_pair_overlap} | "
+            f"{row.n} | {row.selected_depths} | {row.selected_depths_are_prefix} | "
+            f"{row.selected_depths_are_consecutive} | {row.missing_selected_depths} | "
+            f"{row.total_pair_count} | {row.disjoint_pair_count} | "
+            f"{row.max_pairwise_overlap} | {row.first_pair} | {row.first_pair_overlap} | "
             f"{row.first_pair_left_mass}:{row.first_pair_right_mass} |"
         )
     lines.extend(
@@ -192,6 +234,10 @@ def write_summary(rows: list[OverlapRow], path: Path) -> None:
             "`DisjointTowerTargets`.  If all selected pairs overlap, the right",
             "formal condition may need to express nested selected-depth behavior.",
             "",
+            "The prefix/consecutive fields test the next hypothesis: selected",
+            "depths may form a visible initial tower segment.  A prefix row means",
+            "`r_start, r_start+1, ..., max_selected_depth` are all selected.",
+            "",
         ]
     )
     path.write_text("\n".join(lines), encoding="utf-8")
````
`````
