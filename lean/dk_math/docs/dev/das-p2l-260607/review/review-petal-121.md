# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 386059be10dced233b6fa0869938aecad87a02cf

## Report

Checkpoint 120 完了です。

`DkMath.Collatz.PetalBridge` では、level 5 の delayed reservoir を追加しました。主な固定点は次です。

```text
tail 127 mod 128
  = tail 127 mod 256 + tail 255 mod 256

tail 127 mod 128
  -> next tail 63 mod 128 + next tail 127 mod 128
```

あわせて、pressure count 側も進めました。

```text
0 < sourceContinuationPressureDepthCount
  -> selected local pressure depth exists
  -> positive source continuation mass exists
```

Python 数値検証も追加済みです。

- [retention_tower_mod_scan.py](/python/Collatz/PetalBridge/retention_tower_mod_scan.py)
- [retention_tower_mod_scan.csv](/python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv)
- [retention_tower_mod_scan.md](/python/Collatz/PetalBridge/results/retention_tower_mod_scan.md)

`mod 1024` まで確認し、全行で recovery/continuation 法則が一致しました。これにより「次も単に level 6 を手書きで増やす」より、既存 generic residue theorem を使い、selected depths の独立性・非重複 budget へ進む方が良さそうです。

ドキュメントとレビュア向けレポートも同期しました。

- [Collatz-Level5AndModScan-120.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md)
- [report-petal-120.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-120.md)

検証済みです。

```text
python3 python/Collatz/PetalBridge/retention_tower_mod_scan.py --max-modulus 1024
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched checkpoint 120 files>
```

`PetalBridge.lean` は no-sorry。既知の無関係な `ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は残っています。

## Review

## 1. 状況分析

checkpoint `120` は、かなり重要な区切りじゃ。

今回で Lean 側は level `5` まで delayed-reservoir tower を登った。

```text
tail 127 mod 128
  = tail 127 mod 256 + tail 255 mod 256

tail 127 mod 128
  -> next tail 63 mod 128 + next tail 127 mod 128
```

同時に、pressure 側もかなり前進している。

```text
0 < sourceContinuationPressureDepthCount
  -> selected local pressure depth exists
  -> positive source continuation mass exists
```

さらに大きいのは、Python 観測を入れたことじゃ。`retention_tower_mod_scan.py` により `mod 1024` まで scan し、全行で recovery / continuation 法則が一致した、と報告されている。これにより、次もただ level `6` を手書きで増やすより、generic residue theorem と selected-depth accounting へ進む方がよい、という判断がかなり妥当になった。

ここで方針が変わる。

```text
これ以上、ただ登るだけではない。
tower を会計に使う段階へ入る。
```

## 2. 今回の核心

今回の核心は三つ。

```text
1. level 5 tower extension

2. pressureDepthCount positive から selected witness を取れるようになった

3. Python scan により、tower law が mod 1024 まで安定していることを確認した
```

特に重要なのは、二つ目じゃ。

```lean
exists_sourcePressureDepth_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

これにより、

```text
outruns-heavy
  -> pressureDepthCount positive
  -> selected depth j exists
  -> continuation mass at r+j is positive
```

までつながった。

これは大きい。
今までは pressure / outruns が「頻度」だった。
今回から、その頻度が **具体的な depth witness** を持つようになった。

## 3. レビュー

## 3.1. level 5 まで登ったのは良い smoke test

level `5` では、

```lean
orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
```

が追加され、

```lean
tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
```

で static split が入り、

```lean
tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
```

で count recursion edge まで通っている。

ここまで登ったことで、低段だけの偶然ではないことがかなり濃厚になった。

しかも Python scan では `mod 1024` まで同じ law が確認されている。
つまり、今後も level を手書きで伸ばせば通る可能性は高い。

だが、だからこそ次は手書き level 追加を主目標にしない方がよい。

## 3.2. Python scan を入れた判断が非常に良い

これは今回の一番の判断勝ちじゃ。

Lean で level を一段ずつ固定してきたおかげで、構造が信頼できるようになった。
その上で Python scan を入れたので、探索と形式化の役割分担がはっきりした。

```text
Python:
  law の安定性確認
  modulus frontier の観測
  次に一般化すべき式の探索

Lean:
  安定した law の固定
  pressure / witness / budget の安全な接続
```

これで「まだ登るのか？」問題に答えが出た。

```text
もう、ただ登らなくてよい。
必要な frontier だけ named theorem にする。
一般 law は generic theorem 側へ寄せる。
```

## 3.3. pressure count positive から witness を取ったのが本線

今回の pressure 側は非常に大きい。

```lean
exists_sourcePressureDepth_of_pressureDepthCount_pos
```

これは、

```text
positive count
  -> exists selected local pressure depth
```

という、count から witness への橋じゃ。

そして、

```lean
exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
```

で、

```text
selected local pressure depth
  -> positive continuation mass
```

まで進む。

さらに、

```lean
exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
```

で cause-side からも入れる。

これは今後の会計証明にとって必須じゃ。
なぜなら、tower budget は local mass を入力として使うからじゃ。

## 4. 数学的解説

今の構造はこうなっている。

tower 側は、

```text
remainder
  -> falling child
  -> next remainder
```

を繰り返す。

具体的には、

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
```

という all-ones remainder があり、各段で一部が falling child になる。

一方、pressure 側は、

```text
MoreThanHalf continuation retention
```

が起きている depth を検出する。

今回の橋により、

```text
pressure-heavy / outruns-heavy
  -> どこかに positive continuation mass がある
```

が言えるようになった。

つまり、いま見えている戦略はこう。

```text
pressure / outruns がある
  -> local continuation mass が正
  -> delayed-reservoir tower に入る
  -> falling part は sumS へ
  -> continuing part は deep remainder へ
```

これは一発で全 mass を落とす証明ではない。
**落ちた分を sumS に課金し、残った分を deeper remainder として保存する会計証明**じゃ。

## 5. 一歩先ゆく推論

ここからの本命は、もう level `6` ではない。

もちろん level `6` も通るだろう。
だが、Python scan が `mod 1024` まで同じ law を示した以上、単なる level 追加の価値は下がった。

次の本命はこれ。

```text
selected local pressure depths を、
独立または非重複な tower-entry budget として扱えるか？
```

ここが難所じゃ。

なぜなら、

```text
pressureDepthCount が大きい
```

からといって、

```text
その個数分だけ独立した tower budget がある
```

とは言えないからじゃ。

同じ orbit-window mass を別 depth で重複して数えている可能性がある。

したがって次の焦点は、

```text
selected depths are address-separated
```

または、

```text
selected tower-entry target channels are disjoint
```

または、

```text
one selected depth is already enough for a local drift theorem
```

のどれを採用するかになる。

賢狼の見立てでは、最初に狙うべきは **existence から one selected budget**。
そのあとに **two selected depths**。
最後に **count many selected depths** じゃ。

## 6. 今回閉じたもの

今回閉じたものは、次の四つ。

```text
1. level 5 delayed-reservoir tower

2. Python mod scan through mod 1024

3. positive pressureDepthCount から local pressure depth witness

4. outruns-heavy から positive continuation mass witness
```

このうち一番今後に効くのは 3 と 4。
tower を使う入口ができたからじゃ。

## 7. まだ閉じていないもの

未完はこの三つ。

```text
1. selected witness を delayed budget に直接接続する theorem

2. 複数 selected depths の非重複性 / 独立性

3. deep remainder の sparsity / obstruction
```

次は 1 を狙うのがよい。
いきなり 2 を狙うと重い。

まず、

```text
exists positive continuation mass
  -> exists selected delayed budget opportunity
```

を定理として作る。

## 8. 次の指示

## 8.1. selected witness から delayed budget へ接続する

既に depth `2` 専用には、

```lean
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

がある。

しかし、今回得た witness は一般に `r + j` なので、まずは **depth 2 に戻すか**、または **generic depth budget** を作るかを判断する。

短期的には、depth `2` 特化でよい。

```lean
theorem exists_depth_two_budget_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        sumS n ((k + 1) + 1) +
          orbitWindowResidueCountMod8EqSevenTail n k := by
  constructor
  · exact sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one n k h
  · exact sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder n k
      (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
```

これは「local pressure があると、positive mass と budget が同時に使える」形じゃ。

## 8.2. positive count から selected witness を取る theorem を使いやすくする

今回入った theorem を caller-friendly にする alias があるとよい。

```lean
theorem exists_towerEntryDepth_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf n k r len h
```

これはほぼ alias だが、名前として「towerEntryDepth」を使うと次が読みやすい。

## 8.3. two selected pressure depths は慎重に

次に、

```text
2 <= sourceContinuationPressureDepthCount
  -> exists j1 j2, j1 < j2 ...
```

を作りたくなる。

これは有用だが、まだ **独立予算** を主張してはいけない。

まずは witness だけ。

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
  -- countP >= 2 -> two distinct witnesses
  sorry
```

これは次々段階。
まずは one witness を budget に接続するのが先じゃ。

## 9. さらなる次の一手

次の大きなテーマは **selected-depth accounting** じゃ。

候補は三つある。

## 9.1. address-separated selected depths

もし depth が違うだけでは同じ mass を重複するなら、追加条件として、

```text
selected depths are address-separated
```

を置く。

候補定義：

```lean
def SelectedDepthsAddressSeparated
    (n : OddNat) (k r : ℕ) (js : Finset ℕ) : Prop :=
  -- selected depths r+j correspond to disjoint residue channels / addresses
  True
```

まだ `True` 仮置きでよいわけではないが、docs で概念名を固定すると次の探索がしやすい。

## 9.2. disjoint target channels

tower entry の target residue が違えば、budget は重ならない可能性がある。

候補概念：

```text
selected depths have disjoint tail residue targets
```

これが言えれば、

```text
複数 selected depths
  -> 複数 non-overlapping tower budgets
```

へ進める。

## 9.3. one selected depth is enough route

もしかすると複数 selected depths を数える必要はないかもしれない。

```text
outruns-heavy
  -> at least one positive continuation mass
  -> local delayed budget
  -> obstruction if repeated indefinitely
```

という一個 witness の反復でも進める可能性がある。

ここは Python 観測で、positive tower-entry witness が出た軌道がその後どう動くかを見るとよい。

## 10. Python 側の次観測

今回の scan は residue law の確認だった。
次の Python は orbit window 上で、

```text
pressure witness
tower entry
falling contribution
deep remainder
```

を同時に観測したい。

出したい表はこれ。

```text
n
steps
sumS
pressure_depth_count
first_pressure_depth
continuation_mass_at_first_pressure
L1_remainder
L2_remainder
L3_remainder
L4_remainder
L5_remainder
```

観測目的は、

```text
pressure witness があると deep remainder は増えるのか？
それとも falling contribution として回収されるのか？
```

を見ることじゃ。

これは Lean より Python が速い。

## 11. 賢狼が試して欲しい実験補題

## 実験 A: depth 2 pressure range gives positive budget pair

```lean
theorem depthTwoPressureRange_positive_and_budget
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 ∧
      (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        sumS n ((k + 1) + 1) +
          orbitWindowResidueCountMod8EqSevenTail n k := by
  constructor
  · exact sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one n k h
  · exact sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder n k
      (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
```

## 実験 B: tower entry depth alias

```lean
theorem exists_towerEntryDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
```

## 実験 C: outruns-heavy から tower entry depth

```lean
theorem exists_towerEntryDepth_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf n k r len h
```

## 実験 D: one witness theorem を local pressure 付きにする

positive mass だけでなく local pressure も持っておく版。

```lean
theorem exists_sourcePressureDepth_with_positive_mass
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j)) ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj, hpressure,
    sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩
```

これは便利じゃ。
後続で `MoreThanHalf` も `0 < mass` も必要になる可能性が高い。

## 実験 E: two witnesses は existence だけ

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
  -- まだ budget independence は主張しない
  sorry
```

## 実験 F: level 5 static split alias はすでにあるか確認

checkpoint `120` では `tailRemainderLevel4_static_split` は入った。
`tailRemainderLevel5_static_split` はまだ次 level が必要。
level 6 を急がないなら、ここは保留でよい。

## 実験 G: generic residue theorem を使う smoke theorem

次のような「named level を使わない」版を試す。

```lean
theorem tailAllOnesContinuation_step_generic_smoke
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 2) := by
  -- 既存 generic transition があれば、それを直接使う
  sorry
```

これは実際の定義に合わせて調整が必要。
狙いは「level 6 以降は generic theorem を使えるか」を確認すること。

## 12. 次コミットの推奨順

```text
1. depthTwoPressureRange_positive_and_budget を追加

2. exists_towerEntryDepth_of_pressureDepthCount_pos を追加

3. exists_towerEntryDepth_of_outrunsMoreThanHalf を追加

4. exists_sourcePressureDepth_with_positive_mass を追加

5. Python 側で pressure witness + remainder count の orbit scan を追加

6. exists_two_sourcePressureDepths_of_two_le_pressureDepthCount を試す

7. generic residue theorem を使う smoke theorem を試す

8. docs:
   Level5AndModScan から SelectedPressureWitnessAccounting へ接続
```

## 13. 総括

checkpoint `120` は、とても良い。

Lean は level `5` まで登った。
Python は `mod 1024` まで見た。
そして pressure count positive から selected local witness が取れるようになった。

つまり、今後の方向は明確じゃ。

```text
もう単に登るのではない。
pressure witness を選び、
tower budget に入れ、
落ちる分と残る分を会計する。
```

次の主戦場は、

```text
selected-depth accounting
```

じゃ。

一個 witness から始める。
次に二個 witness。
その後、非重複性・separation 条件を探す。

ここが通れば、`pressure-heavy window` が本当に `sumS contribution + deep remainder` に変換され始める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 1979f025..ff463c2d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1064,6 +1064,28 @@ noncomputable def orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 127))
 
+/--
+Number of shifted-tail labels in residue class `127 mod 256`.
+
+This is the delayed-peeling child inside the shifted-tail `127 mod 128`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 127))
+
+/--
+Number of shifted-tail labels in residue class `255 mod 256`.
+
+This is the continuing child inside the shifted-tail `127 mod 128`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 255))
+
 /-- Level `0` tail remainder: the whole shifted-tail exact-height-one reservoir. -/
 noncomputable def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowHeightCountEqTail n k 1
@@ -1100,6 +1122,14 @@ noncomputable def TailRemainderLevel4 (n : OddNat) (k : ℕ) : ℕ :=
 noncomputable def TailFallingLevel4 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowResidueCountMod64EqThirtyOneTail n k
 
+/-- Level `5` tail remainder: the shifted-tail `127 mod 128` continuing color. -/
+noncomputable def TailRemainderLevel5 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k
+
+/-- Level `5` falling color: the shifted-tail `63 mod 128` delayed-peeling color. -/
+noncomputable def TailFallingLevel5 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod128EqSixtyThreeTail n k
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -4258,6 +4288,58 @@ theorem tailRemainderLevel3_static_split
   unfold TailRemainderLevel3 TailFallingLevel4 TailRemainderLevel4
   exact tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree n k
 
+/--
+The shifted-tail `127 mod 128` continuing color splits into its two children
+modulo `256`: the delayed-peeling child `127 mod 256` and the continuing child
+`255 mod 256`.
+-/
+theorem tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k =
+      orbitWindowResidueCountMod256EqOneHundredTwentySevenTail n k +
+        orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail n k := by
+  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+  unfold orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
+  unfold orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      by_cases h127 : oddOrbitLabel n (k + 1) % 256 = 127
+      · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
+          omega
+        simp [ih, hmod128, h127, Nat.add_assoc, Nat.add_comm]
+      · by_cases h255 : oddOrbitLabel n (k + 1) % 256 = 255
+        · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
+            omega
+          simp [ih, hmod128, h255, Nat.add_comm, Nat.add_left_comm]
+        · have hnotMod128 : oddOrbitLabel n (k + 1) % 128 ≠ 127 := by
+            intro hmod128
+            have hchild :
+                oddOrbitLabel n (k + 1) % 256 = 127 ∨
+                  oddOrbitLabel n (k + 1) % 256 = 255 := by
+              omega
+            cases hchild with
+            | inl h =>
+                exact h127 h
+            | inr h =>
+                exact h255 h
+          simp [ih, hnotMod128, h127, h255]
+
+/--
+Level-alias version of the level-`4` static split.
+
+The level-`4` remainder is the sum of the level-`5` falling color and the
+level-`5` remainder.
+-/
+theorem tailRemainderLevel4_static_split
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel4 n k =
+      TailFallingLevel5 n k + TailRemainderLevel5 n k := by
+  unfold TailRemainderLevel4 TailFallingLevel5 TailRemainderLevel5
+  exact tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven n k
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4509,6 +4591,50 @@ theorem oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven hmod
 
+/--
+The `127 mod 256` subchannel moves to `63 mod 128` at the next label.
+
+This is the level-`5` recovery sibling inside the narrowing retention cylinder.
+-/
+theorem oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 256 = 127) :
+    oddOrbitLabel n (i + 1) % 128 = 63 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact
+    next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
+      hmod
+
+/--
+The `255 mod 256` subchannel continues as `127 mod 128` at the next label.
+
+The low-peeling path survives by entering the next thinner all-ones cylinder.
+-/
+theorem oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 256 = 255) :
+    oddOrbitLabel n (i + 1) % 128 = 127 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact
+    next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
+      hmod
+
 /--
 General orbit-label transition for the recovery sibling.
 
@@ -4876,6 +5002,87 @@ theorem tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThre
           · simp [hsource, htargetThirtyOne, htargetSixtyThree]
             omega
 
+/--
+Level-alias version of the level-`4` recursion edge.
+
+The level-`4` remainder re-enters the next level-`4` falling/remainder split.
+-/
+theorem tailRemainderLevel4_step_grammar
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel4 n k ≤
+      TailFallingLevel4 n (k + 1) + TailRemainderLevel4 n (k + 1) := by
+  unfold TailRemainderLevel4 TailFallingLevel4
+  exact tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree n k
+
+/--
+The shifted-tail `127 mod 128` continuing color enters the next shifted-tail
+`63 mod 128 / 127 mod 128` split.
+
+This is the level-`5` recursion edge of the delayed-reservoir tower.
+-/
+theorem tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k ≤
+      orbitWindowResidueCountMod128EqSixtyThreeTail n (k + 1) +
+        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n (k + 1) := by
+  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransitionSixtyThree :
+          oddOrbitLabel n (k + 1) % 256 = 127 →
+            oddOrbitLabel n ((k + 1) + 1) % 128 = 63 :=
+        oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127 n (k + 1)
+      have htransitionOneHundredTwentySeven :
+          oddOrbitLabel n (k + 1) % 256 = 255 →
+            oddOrbitLabel n ((k + 1) + 1) % 128 = 127 :=
+        oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255 n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 128 = 127
+      · have hchild :
+            oddOrbitLabel n (k + 1) % 256 = 127 ∨
+              oddOrbitLabel n (k + 1) % 256 = 255 := by
+          omega
+        cases hchild with
+        | inl h127 =>
+            have htargetSixtyThree :
+                oddOrbitLabel n ((k + 1) + 1) % 128 = 63 :=
+              htransitionSixtyThree h127
+            simp [hsource, htargetSixtyThree]
+            omega
+        | inr h255 =>
+            have htargetOneHundredTwentySeven :
+                oddOrbitLabel n ((k + 1) + 1) % 128 = 127 :=
+              htransitionOneHundredTwentySeven h255
+            simp [hsource, htargetOneHundredTwentySeven]
+            omega
+      · by_cases htargetSixtyThree :
+            oddOrbitLabel n ((k + 1) + 1) % 128 = 63
+        · simp [hsource, htargetSixtyThree]
+          omega
+        · by_cases htargetOneHundredTwentySeven :
+            oddOrbitLabel n ((k + 1) + 1) % 128 = 127
+          · simp [hsource, htargetOneHundredTwentySeven]
+            omega
+          · simp [hsource, htargetSixtyThree, htargetOneHundredTwentySeven]
+            omega
+
+/--
+Level-alias version of the level-`5` recursion edge.
+
+The level-`5` remainder re-enters the next level-`5` falling/remainder split.
+-/
+theorem tailRemainderLevel5_step_grammar
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel5 n k ≤
+      TailFallingLevel5 n (k + 1) + TailRemainderLevel5 n (k + 1) := by
+  unfold TailRemainderLevel5 TailFallingLevel5
+  exact
+    tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
+      n k
+
 /--
 One-step grammar for the shifted-tail exact-height-one reservoir.
 
@@ -6141,6 +6348,70 @@ theorem sourceContinuationMass_pos_of_pressureOnRange_at
   sourceContinuationMass_pos_of_localPressure n k (r + j)
     (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)
 
+/--
+Positive source pressure-depth count selects at least one local pressure depth.
+
+This is intentionally only an existence theorem.  It does not claim that
+multiple selected depths are independent.
+-/
+theorem exists_sourcePressureDepth_of_pressureDepthCount_pos
+    (n : OddNat) (k r len : ℕ)
+    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
+    ∃ j, j < len ∧
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+        (orbitWindowRetentionMassPow2 n k (r + j)) := by
+  classical
+  unfold sourceContinuationPressureDepthCount at hpos
+  induction len with
+  | zero =>
+      simp at hpos
+  | succ len ih =>
+      rw [List.range_succ] at hpos
+      by_cases hlast :
+          MoreThanHalf
+            (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+            (orbitWindowRetentionMassPow2 n k (r + len))
+      · exact ⟨len, by omega, hlast⟩
+      · have hprev :
+            0 <
+              (List.range len).countP
+                (fun j =>
+                  decide
+                    (MoreThanHalf
+                      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+                      (orbitWindowRetentionMassPow2 n k (r + j)))) := by
+          simpa [hlast] using hpos
+        rcases ih hprev with ⟨j, hj, hpressure⟩
+        exact ⟨j, by omega, hpressure⟩
+
+/--
+Positive source pressure-depth count selects a depth with positive source
+continuation mass.
+-/
+theorem exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+    (n : OddNat) (k r len : ℕ)
+    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
+    ∃ j, j < len ∧
+      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
+  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
+    ⟨j, hj, hpressure⟩
+  exact ⟨j, hj, sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩
+
+/--
+Source cause-side outruns-heavy pressure yields a concrete positive source
+continuation mass at some selected depth.
+-/
+theorem exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    ∃ j, j < len ∧
+      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
+  have hpos :
+      0 < sourceContinuationPressureDepthCount n k r len :=
+    sourcePressureDepthCount_pos_of_outrunsMoreThanHalf n k r len h
+  exact exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
+
 /--
 Extract local depth-two source pressure from the one-depth range pressure
 profile beginning at depth `2`.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index a9f71d92..eb5fe065 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -154,6 +154,7 @@ docs/Collatz-DelayedReservoirTower-116.md
 docs/Collatz-Level2Remainder-117.md
 docs/Collatz-Level3PressureEntrance-118.md
 docs/Collatz-Level4GenericPressure-119.md
+docs/Collatz-Level5AndModScan-120.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md
new file mode 100644
index 00000000..6b543785
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md
@@ -0,0 +1,196 @@
+# Collatz Level-5 And Mod Scan 120
+
+Checkpoint 120 has two purposes:
+
+```text
+1. extend the concrete delayed-reservoir tower to level 5
+2. stop climbing blindly by adding a Python observation table through mod 1024
+```
+
+The Lean side remains conservative.  The Python side is an observation tool
+that helps choose the next theorem targets.
+
+## Level-5 Tower Extension
+
+Checkpoint 119 fixed:
+
+```text
+tail 63 mod 64
+  -> next tail 31 mod 64 + next tail 63 mod 64
+```
+
+Checkpoint 120 adds:
+
+```text
+tail 127 mod 128
+  -> next tail 63 mod 128 + next tail 127 mod 128
+```
+
+New shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
+orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
+```
+
+Static split:
+
+```lean
+tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
+```
+
+Reading:
+
+```text
+tail 127 mod 128
+  = tail 127 mod 256
+    + tail 255 mod 256
+```
+
+Pointwise aliases:
+
+```lean
+oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
+oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
+```
+
+Count-level recursion edge:
+
+```lean
+tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
+```
+
+Level aliases:
+
+```lean
+TailRemainderLevel5
+TailFallingLevel5
+tailRemainderLevel4_static_split
+tailRemainderLevel4_step_grammar
+tailRemainderLevel5_step_grammar
+```
+
+## Pressure Count To Witness
+
+Checkpoint 119 could extract pressure at a selected depth:
+
+```text
+SourceContinuationPressureOnRange n k r len
+  and j < len
+  -> local pressure at r+j
+```
+
+Checkpoint 120 adds the count-facing entrance:
+
+```lean
+exists_sourcePressureDepth_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+```
+
+The important reading is:
+
+```text
+positive pressure-depth count
+  -> there exists a selected depth
+  -> source continuation mass is positive there
+```
+
+This is deliberately existential.  It does not claim that several selected
+depths are independent.  The independence/disjointness problem remains a later
+budget theorem.
+
+## Python Observation Window
+
+The new script is:
+
+```text
+python/Collatz/PetalBridge/retention_tower_mod_scan.py
+```
+
+Default output:
+
+```text
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
+```
+
+The scan checks the exact height-one residue law through `mod 1024`.
+
+For depth `d >= 3`:
+
+```text
+parent:       2^d - 1 mod 2^d
+recovery:     2^d - 1 mod 2^(d+1)
+continuation: 2^(d+1) - 1 mod 2^(d+1)
+
+T1(recovery)     = 2^(d-1) - 1 mod 2^d
+T1(continuation) = 2^d - 1 mod 2^d
+```
+
+where:
+
+```text
+T1(x) = (3*x + 1) / 2
+```
+
+Observed levels:
+
+```text
+7 mod 16     -> 3 mod 8
+15 mod 16    -> 7 mod 8
+15 mod 32    -> 7 mod 16
+31 mod 32    -> 15 mod 16
+31 mod 64    -> 15 mod 32
+63 mod 64    -> 31 mod 32
+63 mod 128   -> 31 mod 64
+127 mod 128  -> 63 mod 64
+127 mod 256  -> 63 mod 128
+255 mod 256  -> 127 mod 128
+255 mod 512  -> 127 mod 256
+511 mod 512  -> 255 mod 256
+511 mod 1024 -> 255 mod 512
+1023 mod 1024 -> 511 mod 512
+```
+
+All checked rows matched the expected law.
+
+## Inference
+
+The table confirms that the delayed-reservoir tower is not a special accident
+of low modulus.  The existing generic Lean theorems:
+
+```lean
+next_recovery_residue_of_mod
+next_continuation_residue_of_mod
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
+```
+
+are the right long-term surface.
+
+Concrete aliases are still useful at active frontier levels because they make
+the proof state readable:
+
+```text
+127 mod 256 -> 63 mod 128
+255 mod 256 -> 127 mod 128
+```
+
+but future levels should be promoted only when a downstream theorem needs that
+named level.
+
+## Next Work
+
+The tower can continue mechanically, but the next mathematical gain is not
+another named modulus.  The better target is:
+
+```text
+selected pressure depths
+  + no-overlap / separated address condition
+  -> non-duplicated tower-entry budget
+```
+
+The new existential pressure-count bridge gives the first selected local depth.
+The next step is to determine which separation predicate can safely turn
+several selected depths into several independent budget entries.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 0ce995d9..80429a61 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1193,3 +1193,35 @@ orbitWindowContinuationSiblingMassPow2
 
 Use these names when a theorem is conceptually about low-peeling retention,
 rather than writing the raw residue-count expression every time.
+
+## Level-5 And Mod Scan
+
+Checkpoint 120 extends the delayed-retention tower one more level and adds a
+Python observation window through `mod 1024`.
+
+The new Lean frontier is:
+
+```text
+tail 127 mod 128
+  = tail 127 mod 256 + tail 255 mod 256
+
+tail 127 mod 128
+  -> next tail 63 mod 128 + next tail 127 mod 128
+```
+
+The Python scan lives under:
+
+```text
+python/Collatz/PetalBridge/
+```
+
+and currently writes:
+
+```text
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
+```
+
+The scan confirms the same recovery/continuation law from `mod 16` through
+`mod 1024`, which suggests that future checkpoints should prefer the generic
+power-of-two residue theorem when readability permits it.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 3e41f1b9..84353e2a 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -1441,3 +1441,62 @@ shifted-tail prefix versions of the transition-count inequalities
 The main caution is that Collatz state labels are not prime labels.  Any bridge
 to `ABCBridge` must insert an additional label transform or carrier witness
 layer before using the Petal radical lower-bound theorems.
+
+## Checkpoint 120: Level 5 And Mod-1024 Scan
+
+Checkpoint 120 adds one more concrete delayed-retention level:
+
+```lean
+orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
+orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
+TailRemainderLevel5
+TailFallingLevel5
+```
+
+The new split theorem is:
+
+```lean
+tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
+tailRemainderLevel4_static_split
+```
+
+The new orbit-label transition aliases are:
+
+```lean
+oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
+oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
+```
+
+The new count recursion edge is:
+
+```lean
+tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
+tailRemainderLevel4_step_grammar
+tailRemainderLevel5_step_grammar
+```
+
+The pressure-count existence layer is now available:
+
+```lean
+exists_sourcePressureDepth_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+```
+
+This closes the first safe bridge from:
+
+```text
+positive pressure-depth count
+  -> selected local pressure depth
+  -> positive source continuation mass
+```
+
+The Python observation window:
+
+```text
+python/Collatz/PetalBridge/retention_tower_mod_scan.py
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
+```
+
+confirms the same recovery/continuation residue law through `mod 1024`.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-120.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-120.md
new file mode 100644
index 00000000..daad301b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-120.md
@@ -0,0 +1,309 @@
+# Report Petal 120
+
+## Summary
+
+Checkpoint 120 advanced two tracks:
+
+```text
+Lean:
+  level-5 delayed-reservoir tower
+  pressure-count positive -> selected local tower-entry witness
+
+Python:
+  mod 1024 retention-tower scan
+  CSV and Markdown observation table
+```
+
+The main result is that the concrete tower can still be climbed, but the Python
+table makes it clear that future progress should not depend on naming every
+modulus by hand.  The stronger next direction is selected-depth accounting with
+an explicit no-overlap or separated-address condition.
+
+## Lean Changes
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+### New Level-5 Tail Counts
+
+Added:
+
+```lean
+orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
+orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
+```
+
+These count shifted-tail labels in:
+
+```text
+127 mod 256
+255 mod 256
+```
+
+They refine the previous continuing channel:
+
+```text
+127 mod 128
+```
+
+### New Level Aliases
+
+Added:
+
+```lean
+TailRemainderLevel5
+TailFallingLevel5
+```
+
+Readings:
+
+```text
+TailRemainderLevel5 = shifted-tail 127 mod 128
+TailFallingLevel5   = shifted-tail 63 mod 128
+```
+
+### Static Split
+
+Added:
+
+```lean
+tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
+tailRemainderLevel4_static_split
+```
+
+Meaning:
+
+```text
+tail 127 mod 128
+  = tail 127 mod 256
+    + tail 255 mod 256
+
+level 4 remainder
+  = level 5 falling + level 5 remainder
+```
+
+### Orbit-Level Transition Aliases
+
+Added:
+
+```lean
+oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
+oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
+```
+
+Meaning:
+
+```text
+127 mod 256 -> next 63 mod 128
+255 mod 256 -> next 127 mod 128
+```
+
+These are concrete aliases over the raw arithmetic anchors:
+
+```lean
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
+next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
+```
+
+### Count Recursion Edge
+
+Added:
+
+```lean
+tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
+tailRemainderLevel4_step_grammar
+tailRemainderLevel5_step_grammar
+```
+
+Meaning:
+
+```text
+tail 127 mod 128
+  -> next tail 63 mod 128 + next tail 127 mod 128
+```
+
+This is the level-5 version of the delayed-reservoir recursion.
+
+## Pressure Count Witness
+
+Added:
+
+```lean
+exists_sourcePressureDepth_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
+exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
+```
+
+This closes the safe existence bridge:
+
+```text
+0 < sourceContinuationPressureDepthCount
+  -> exists selected local pressure depth
+  -> exists positive source continuation mass
+```
+
+and:
+
+```text
+SourceOutrunsMoreThanHalfOnDepthRange
+  -> exists positive source continuation mass
+```
+
+This theorem is deliberately existential.  It does not claim that several
+selected depths can be counted independently.
+
+## Python Observation
+
+New script:
+
+```text
+python/Collatz/PetalBridge/retention_tower_mod_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
+```
+
+Command used:
+
+```text
+python3 python/Collatz/PetalBridge/retention_tower_mod_scan.py --max-modulus 1024
+```
+
+Observed law:
+
+```text
+parent:       2^d - 1 mod 2^d
+recovery:     2^d - 1 mod 2^(d+1)
+continuation: 2^(d+1) - 1 mod 2^(d+1)
+
+T1(recovery)     = 2^(d-1) - 1 mod 2^d
+T1(continuation) = 2^d - 1 mod 2^d
+```
+
+where:
+
+```text
+T1(x) = (3*x + 1) / 2
+```
+
+Observed rows through `mod 1024` all matched.
+
+## Data Table
+
+Source:
+
+```text
+python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
+```
+
+Compact view:
+
+```text
+d=3:  7 mod 16      -> 3 mod 8,    15 mod 16     -> 7 mod 8
+d=4:  15 mod 32     -> 7 mod 16,   31 mod 32     -> 15 mod 16
+d=5:  31 mod 64     -> 15 mod 32,  63 mod 64     -> 31 mod 32
+d=6:  63 mod 128    -> 31 mod 64,  127 mod 128   -> 63 mod 64
+d=7:  127 mod 256   -> 63 mod 128, 255 mod 256   -> 127 mod 128
+d=8:  255 mod 512   -> 127 mod 256, 511 mod 512  -> 255 mod 256
+d=9:  511 mod 1024  -> 255 mod 512, 1023 mod 1024 -> 511 mod 512
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-Level5AndModScan-120.md
+```
+
+## Verification
+
+Passed:
+
+```text
+python3 python/Collatz/PetalBridge/retention_tower_mod_scan.py --max-modulus 1024
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched checkpoint 120 files>
+```
+
+The rebuilt `DkMath.Collatz.PetalBridge` produced no local warning after
+shortening the new level-5 theorem name and removing an unused simp argument.
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
+## Inference
+
+The mod scan shows that the delayed-reservoir law is structurally stable at
+least through `mod 1024`, and the Lean file already contains generic theorems
+for the underlying residue motion.
+
+Therefore, the next high-value target is not another concrete level name.  The
+next target is the accounting problem:
+
+```text
+pressureDepthCount positive / large
+  -> selected local depths
+  -> independent or non-overlapping tower-entry budget
+```
+
+Checkpoint 120 supplies the first selected local witness.  A future checkpoint
+should decide which separation predicate controls duplicate use of the same
+orbit-window mass.
+
+## Suggested Next Implementation
+
+Do not immediately add level 6 unless a reviewer specifically wants another
+concrete smoke test.
+
+The better next theorem family is:
+
+```lean
+def SelectedSourcePressureDepths ...
+
+theorem selectedSourcePressureDepth_mem_iff ...
+theorem selectedSourcePressureDepth_count_eq_pressureDepthCount ...
+```
+
+or, if list packaging feels too early, stay thinner:
+
+```lean
+theorem exists_two_sourcePressureDepths_of_two_le_pressureDepthCount
+```
+
+but only if the resulting two depths are still treated as selected witnesses,
+not as independent budget carriers.
+
+The missing condition to investigate is:
+
+```text
+selected depths are address-separated
+or selected tower-entry target channels are disjoint
+or one selected depth is enough for the immediate drift theorem
+```
+
+This is the next contract point between the pressure-count side and the
+delayed-reservoir tower side.
diff --git a/python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv b/python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
new file mode 100644
index 00000000..a285ad15
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/retention_tower_mod_scan.csv
@@ -0,0 +1,8 @@
+depth,parent_modulus,parent_residue,child_modulus,recovery_child,continuation_child,target_modulus,recovery_target,continuation_target,expected_recovery_target,expected_continuation_target,recovery_ok,continuation_ok
+3,8,7,16,7,15,8,3,7,3,7,True,True
+4,16,15,32,15,31,16,7,15,7,15,True,True
+5,32,31,64,31,63,32,15,31,15,31,True,True
+6,64,63,128,63,127,64,31,63,31,63,True,True
+7,128,127,256,127,255,128,63,127,63,127,True,True
+8,256,255,512,255,511,256,127,255,127,255,True,True
+9,512,511,1024,511,1023,512,255,511,255,511,True,True
diff --git a/python/Collatz/PetalBridge/results/retention_tower_mod_scan.md b/python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
new file mode 100644
index 00000000..06c7a573
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/retention_tower_mod_scan.md
@@ -0,0 +1,39 @@
+# Collatz PetalBridge Retention Tower Scan
+
+- max modulus: `1024`
+- scanned levels: `7`
+- all transitions matched expected law: `True`
+
+## Law
+
+For depth `d >= 3`:
+
+```text
+parent:       2^d - 1 mod 2^d
+recovery:     2^d - 1 mod 2^(d+1)
+continuation: 2^(d+1) - 1 mod 2^(d+1)
+
+T1(recovery)     = 2^(d-1) - 1 mod 2^d
+T1(continuation) = 2^d - 1 mod 2^d
+```
+
+where `T1(x) = (3*x + 1) / 2` is the exact height-one visible step.
+
+## Table
+
+| d | parent | recovery child | continuation child | recovery target | continuation target | ok |
+|---:|---:|---:|---:|---:|---:|:---:|
+| 3 | 7 mod 8 | 7 mod 16 | 15 mod 16 | 3 mod 8 | 7 mod 8 | True |
+| 4 | 15 mod 16 | 15 mod 32 | 31 mod 32 | 7 mod 16 | 15 mod 16 | True |
+| 5 | 31 mod 32 | 31 mod 64 | 63 mod 64 | 15 mod 32 | 31 mod 32 | True |
+| 6 | 63 mod 64 | 63 mod 128 | 127 mod 128 | 31 mod 64 | 63 mod 64 | True |
+| 7 | 127 mod 128 | 127 mod 256 | 255 mod 256 | 63 mod 128 | 127 mod 128 | True |
+| 8 | 255 mod 256 | 255 mod 512 | 511 mod 512 | 127 mod 256 | 255 mod 256 | True |
+| 9 | 511 mod 512 | 511 mod 1024 | 1023 mod 1024 | 255 mod 512 | 511 mod 512 | True |
+
+## Lean Inference
+
+The table supports replacing one-off named arithmetic anchors by the
+existing generic residue theorem whenever the call site can tolerate
+the power-of-two parameters.  For readability, the concrete Lean
+aliases remain useful at the active frontier levels.
diff --git a/python/Collatz/PetalBridge/retention_tower_mod_scan.py b/python/Collatz/PetalBridge/retention_tower_mod_scan.py
new file mode 100644
index 00000000..7d66326d
--- /dev/null
+++ b/python/Collatz/PetalBridge/retention_tower_mod_scan.py
@@ -0,0 +1,172 @@
+#!/usr/bin/env python3
+"""Scan the Collatz delayed-retention residue tower up to a power-of-two modulus.
+
+The Lean file `DkMath.Collatz.PetalBridge` proves the first concrete levels of
+the following observation:
+
+    (2^d - 1) mod 2^d
+      splits inside mod 2^(d+1) into
+        (2^d - 1) and (2^(d+1) - 1),
+
+and one exact height-one Collatz step `(3n + 1) / 2` sends those two children to
+the recovery and continuation residues modulo `2^(d-1)`.
+
+This script produces CSV evidence through `mod 1024` by default.  It is an
+observation tool only; the Lean theorems remain the source of truth.
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
+class TowerRow:
+    depth: int
+    parent_modulus: int
+    parent_residue: int
+    child_modulus: int
+    recovery_child: int
+    continuation_child: int
+    target_modulus: int
+    recovery_target: int
+    continuation_target: int
+    expected_recovery_target: int
+    expected_continuation_target: int
+    recovery_ok: bool
+    continuation_ok: bool
+
+
+def one_height_step(residue: int) -> int:
+    """The visible height-one odd Collatz step for residues in `7 mod 8`."""
+    return (3 * residue + 1) // 2
+
+
+def scan(max_modulus: int) -> list[TowerRow]:
+    rows: list[TowerRow] = []
+    depth = 3
+    while 2 ** (depth + 1) <= max_modulus:
+        parent_modulus = 2**depth
+        parent_residue = parent_modulus - 1
+        child_modulus = 2 ** (depth + 1)
+        recovery_child = parent_residue
+        continuation_child = child_modulus - 1
+        target_modulus = parent_modulus
+        recovery_target = one_height_step(recovery_child) % target_modulus
+        continuation_target = one_height_step(continuation_child) % target_modulus
+        expected_recovery_target = 2 ** (depth - 1) - 1
+        expected_continuation_target = parent_residue
+        rows.append(
+            TowerRow(
+                depth=depth,
+                parent_modulus=parent_modulus,
+                parent_residue=parent_residue,
+                child_modulus=child_modulus,
+                recovery_child=recovery_child,
+                continuation_child=continuation_child,
+                target_modulus=target_modulus,
+                recovery_target=recovery_target,
+                continuation_target=continuation_target,
+                expected_recovery_target=expected_recovery_target,
+                expected_continuation_target=expected_continuation_target,
+                recovery_ok=recovery_target == expected_recovery_target,
+                continuation_ok=continuation_target == expected_continuation_target,
+            )
+        )
+        depth += 1
+    return rows
+
+
+def write_csv(rows: list[TowerRow], path: Path) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    with path.open("w", newline="", encoding="utf-8") as f:
+        writer = csv.DictWriter(f, fieldnames=list(TowerRow.__dataclass_fields__))
+        writer.writeheader()
+        for row in rows:
+            writer.writerow(row.__dict__)
+
+
+def write_summary(rows: list[TowerRow], path: Path, max_modulus: int) -> None:
+    path.parent.mkdir(parents=True, exist_ok=True)
+    all_ok = all(row.recovery_ok and row.continuation_ok for row in rows)
+    lines = [
+        "# Collatz PetalBridge Retention Tower Scan",
+        "",
+        f"- max modulus: `{max_modulus}`",
+        f"- scanned levels: `{len(rows)}`",
+        f"- all transitions matched expected law: `{all_ok}`",
+        "",
+        "## Law",
+        "",
+        "For depth `d >= 3`:",
+        "",
+        "```text",
+        "parent:       2^d - 1 mod 2^d",
+        "recovery:     2^d - 1 mod 2^(d+1)",
+        "continuation: 2^(d+1) - 1 mod 2^(d+1)",
+        "",
+        "T1(recovery)     = 2^(d-1) - 1 mod 2^d",
+        "T1(continuation) = 2^d - 1 mod 2^d",
+        "```",
+        "",
+        "where `T1(x) = (3*x + 1) / 2` is the exact height-one visible step.",
+        "",
+        "## Table",
+        "",
+        "| d | parent | recovery child | continuation child | recovery target | continuation target | ok |",
+        "|---:|---:|---:|---:|---:|---:|:---:|",
+    ]
+    for row in rows:
+        ok = row.recovery_ok and row.continuation_ok
+        lines.append(
+            "| "
+            f"{row.depth} | "
+            f"{row.parent_residue} mod {row.parent_modulus} | "
+            f"{row.recovery_child} mod {row.child_modulus} | "
+            f"{row.continuation_child} mod {row.child_modulus} | "
+            f"{row.recovery_target} mod {row.target_modulus} | "
+            f"{row.continuation_target} mod {row.target_modulus} | "
+            f"{ok} |"
+        )
+    lines.extend(
+        [
+            "",
+            "## Lean Inference",
+            "",
+            "The table supports replacing one-off named arithmetic anchors by the",
+            "existing generic residue theorem whenever the call site can tolerate",
+            "the power-of-two parameters.  For readability, the concrete Lean",
+            "aliases remain useful at the active frontier levels.",
+            "",
+        ]
+    )
+    path.write_text("\n".join(lines), encoding="utf-8")
+
+
+def parse_args() -> argparse.Namespace:
+    parser = argparse.ArgumentParser()
+    parser.add_argument("--max-modulus", type=int, default=1024)
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
+    rows = scan(args.max_modulus)
+    csv_path = args.out_dir / "retention_tower_mod_scan.csv"
+    summary_path = args.out_dir / "retention_tower_mod_scan.md"
+    write_csv(rows, csv_path)
+    write_summary(rows, summary_path, args.max_modulus)
+    print(f"wrote {csv_path}")
+    print(f"wrote {summary_path}")
+
+
+if __name__ == "__main__":
+    main()
````
`````
