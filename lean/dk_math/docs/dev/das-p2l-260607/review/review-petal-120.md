# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f796f55f90ca46b6351ac5a63034404b8be4b935

## Report

Checkpoint 119 完了です。

`DkMath.Collatz.PetalBridge` に level 4 の tail reservoir と generic pressure 抽出を追加しました。主な到達点は、`63 mod 64` tail を `63 mod 128 / 127 mod 128` に分割し、次段で

```text
63 mod 64 -> next 31 mod 64 + next 63 mod 64
```

として reservoir tower をもう一段伸ばしたことです。あわせて `SourceContinuationPressureOnRange` から任意位置 `j < len` の local pressure を取り出し、そこから continuation mass の正値性まで落とす小補題も入れました。

ドキュメントも同期済みです。

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
- [Collatz-Level4GenericPressure-119.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md)
- [report-petal-119.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-119.md)

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
git diff --check -- <touched files>
```

`PetalBridge.lean` 自体は no-sorry。既知の無関係な警告として、上流側の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は残っています。

## Review

## 1. 状況分析

checkpoint `119` は、かなり節目じゃ。
今回は **tower 側** と **pressure 側** の両方が一段進んでいる。

tower 側では、level `4` まで到達した。

```text
level 1:
  3 mod 8 falls, 7 mod 8 remains

level 2:
  7 mod 16 falls, 15 mod 16 remains

level 3:
  15 mod 32 falls, 31 mod 32 remains

level 4:
  31 mod 64 falls, 63 mod 64 remains
```

pressure 側では、`SourceContinuationPressureOnRange` から任意の `j < len` を選んで local pressure を取り出し、そこから positive continuation mass まで落とせるようになった。報告でも、level 4 の reservoir tower と generic pressure 抽出を追加したこと、さらに `63 mod 64 -> next 31 mod 64 + next 63 mod 64` が通ったことが要点として整理されている。

これは、かなり重要な転換点じゃ。
今までは「tower を伸ばす」作業だった。
今回からは「pressure-heavy range を tower に流し込む」準備が整い始めた。

## 2. 今回の核心

今回の核心は二つ。

ひとつ目は tower level `4`。

```lean
tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
```

これは、

```text
tail 63 mod 64
  -> next tail 31 mod 64
     +
     next tail 63 mod 64
```

を言う。

ふたつ目は generic pressure extraction。

```lean
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
```

これは、

```text
SourceContinuationPressureOnRange n k r len
  and j < len
  -> local MoreThanHalf at depth r+j
  -> positive continuation mass at depth r+j
```

を言う。

つまり、今まで分かれていた二つの世界、

```text
delayed-reservoir tower

pressure / outruns frequency
```

が接続され始めた。

## 3. レビュー

## 3.1. level 4 拡張は成功

追加された level 4 counts はこれ。

```lean
orbitWindowResidueCountMod128EqSixtyThreeTail
orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
```

そして split theorem。

```lean
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
```

読みは、

```text
tail 63 mod 64
  = tail 63 mod 128
    + tail 127 mod 128
```

ここまで、

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
```

と、continuing color が綺麗に伸びている。

これはかなり強い。
もう偶然の一段ではなく、明らかに tower pattern が見えている。

## 3.2. orbit-label transition を足したのが良い

今回、raw arithmetic anchor だけでなく、orbit-label 版も追加している。

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
```

これは良い判断じゃ。
raw residue theorem は低位算術として正しいが、PetalBridge の主語は `oddOrbitLabel` と `orbitWindow` なので、使いやすい theorem surface に上げておく必要がある。

特に後者は名前を短縮している。
Lean の行長・可読性の都合を考えると妥当じゃ。

## 3.3. generic pressure wrapper は大きい

今回の本当の価値は、tower level 4 そのものより、こちらかもしれぬ。

```lean
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
```

これで、任意の pressure range から selected local depth を取り出せる。

今後の finite accounting では、

```text
pressure-heavy range の中から、使える depth を選ぶ
```

必要がある。

そのときに、毎回 `moreThanHalf_of_sourceContinuationPressure` を直接使うのではなく、

```lean
sourcePressureAtDepth_of_pressureOnRange
```

という意味名で取り出せるのは大きい。

## 3.4. ここからは「もう一段伸ばす」だけでは足りない

level 5 を伸ばすのは自然じゃ。
しかし、今回で重要な警告も見えた。

tower は伸びる。
だが、tower が伸びるだけでは Collatz pressure を処理したことにはならない。

次に必要なのは、

```text
pressure range
  -> selected local pressure depths
  -> local tower-entry masses
  -> sumS contribution + deep remainder
```

という有限会計の組み立てじゃ。

つまり、次の中心は「残りをどう細くするか」だけでなく、「どの pressure mass を tower に入れるか」になる。

## 4. 数学的解説

現在の tower pattern は、かなり明瞭じゃ。

continuing remainder は、

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
```

へ向かう。

これは、

$$
2^m-1 \pmod {2^m}
$$

という all-ones residue class じゃ。

一方で、falling color は一段浅い all-ones residue。

```text
3 mod 8
7 mod 16
15 mod 32
31 mod 64
63 mod 128
```

各段で、continuing remainder を一段細かく見ると、

```text
falling child + next continuing child
```

に分かれる。

したがって、構造はこう。

```text
remainder
  -> falling child
  -> deeper remainder
```

そして falling child は、未来の `sumS` に課金できる。

だから今の DkMath 的読みは、

```text
即時に全部落とすのではない。
落ちる色を会計に入れ、残る色をさらに細くする。
```

これじゃ。

## 5. 深い推論：tower は「証明」ではなく「会計台帳」

ここが重要じゃ。

delayed-reservoir tower は、単独では Collatz 証明ではない。
しかし、局所 mass を無駄にしないための **会計台帳** になっている。

以前の危険な読みは、

```text
continuation mass はすぐ extra peeling になる
```

だった。

Lean はそれを否定した。
正しくは、

```text
continuation mass の一部は delayed peeling として sumS に入る。
残りは continuing remainder として明示的に残る。
```

この「残りを明示する」のが非常に大事じゃ。

証明で一番危険なのは、落ちなかった mass をどこかに消してしまうこと。
今回の tower はそれをしない。

```text
落ちた分:
  sumS へ

落ちなかった分:
  TailRemainderLevel L へ
```

として保存している。

これは、まさに `Big - Gap = Body` 的な保存会計に近い。

## 6. 今回閉じたもの

今回閉じたものは、次の五つ。

```text
1. level 4 residue counts:
   63 mod 128 / 127 mod 128

2. level 4 static split:
   63 mod 64 = 63 mod 128 + 127 mod 128

3. level 4 pointwise orbit-label transition

4. level 4 recursion:
   63 mod 64 -> next 31 mod 64 + next 63 mod 64

5. generic pressure extraction:
   pressure range + selected j -> local pressure -> positive continuation mass
```

これで、tower 側は level 4、pressure 側は任意 selected depth まで到達した。

## 7. まだ閉じていないもの

未完の本命は三つある。

```text
1. level 5:
   127 mod 128 -> 63 mod 128 + 127 mod 128

2. finite selected-depth accounting:
   pressure range から複数の local tower-entry を取り出す

3. deep-remainder sparsity:
   深い all-ones residue class の占有数を制約する
```

この中で一番重要なのは 2 と 3 じゃ。
level 5 は自然だが、そろそろ「tower を伸ばすだけ」の効果は逓減してくる。

次は、pressure range の中にある複数の selected local depths をどう扱うか。
そして、その local mass を重複なく tower budget に流せるか。

ここが難所になる。

## 8. 次の指示

## 8.1. level 5 は一段だけ進める

まず pattern 確認として level 5 は進めてよい。

```lean
noncomputable def orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 127))

noncomputable def orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 255))
```

split theorem。

```lean
theorem tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k =
      orbitWindowResidueCountMod256EqOneHundredTwentySevenTail n k +
        orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail n k := by
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  unfold orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
  unfold orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h127 : oddOrbitLabel n (k + 1) % 256 = 127
      · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
          omega
        have hnot255 : oddOrbitLabel n (k + 1) % 256 ≠ 255 := by
          omega
        simp [ih, hmod128, h127, hnot255, Nat.add_assoc, Nat.add_comm]
      · by_cases h255 : oddOrbitLabel n (k + 1) % 256 = 255
        · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
            omega
          simp [ih, hmod128, h255, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod128 : oddOrbitLabel n (k + 1) % 128 ≠ 127 := by
            intro hmod128
            have hchild :
                oddOrbitLabel n (k + 1) % 256 = 127 ∨
                  oddOrbitLabel n (k + 1) % 256 = 255 := by
              omega
            cases hchild with
            | inl h =>
                exact h127 h
            | inr h =>
                exact h255 h
          simp [ih, hnotMod128, h127, h255]
```

ただし、ここは命名が長くなる。
`Eq127Tail` / `Eq255Tail` の短縮命名を検討してもよい段階じゃ。

## 8.2. pressure range から selected depths を数える

次の本命は、generic extraction を count に戻すことじゃ。

まずは existence でよい。

```lean
theorem exists_sourcePressureDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j)) := by
  -- countP positive -> exists
  sorry
```

これが通ると、

```text
pressure count positive
  -> at least one local tower-entry opportunity
```

が得られる。

さらに composition。

```lean
theorem exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj,
    sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩
```

これはかなり使える。

## 8.3. pressure-heavy から existence へ

既にあるはずの、

```lean
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
```

または pressure-heavy 系から、上の existence へ接続する。

候補：

```lean
theorem exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  have hpos :
      0 < sourceContinuationPressureDepthCount n k r len :=
    sourcePressureDepthCount_pos_of_outrunsMoreThanHalf n k r len h
  exact exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
```

これで cause-side pressure/outRuns から、具体的な tower-entry mass の存在が出る。

## 9. 一歩先の次の一手

存在だけではまだ弱い。
次は「多数の selected depths」を扱いたい。

ただし、ここで注意が必要じゃ。
複数 depth の continuation mass は、同じ orbit window mass を重複して数える可能性がある。

だから、いきなり

```text
pressureDepthCount 個の tower entries がある
```

とは言わない方がよい。

まずは、selected depth list を作るより、より安全に、

```text
positive pressure depth が存在する
```

を得る。

その次に、

```text
互いに独立な selected depths
```

あるいは、

```text
disjoint residue channels
```

を調べる。

ここで既存の `OrbitWindowSeparated` / `OddOrbitLabelsPairwiseSeparated` 系が効く可能性がある。

## 10. deep-remainder sparsity への推論

tower が level 4 まで伸びたので、deep remainder はこうなった。

```text
TailRemainderLevel4:
  63 mod 64
```

次は level 5 なら、

```text
127 mod 128
```

この all-ones cylinder はかなり細い。
もし orbit labels が window 内で十分 separated なら、深い cylinder に大量に滞在することは難しいかもしれない。

狙いたい将来補題はこう。

```lean
theorem tailDeepRemainderLevel4_le_window_div_pow
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel4 n k ≤ k := by
  -- trivial
```

これは弱すぎる。

本当に欲しいのは、何らかの separation 条件付きで、

```text
TailRemainderLevel L が小さい
```

または、

```text
TailRemainderLevel L が全部を占めるなら、強い合同固定が発生する
```

のような定理じゃ。

例えば将来候補：

```lean
def TailAllOnesCylinderDominates
    (L : ℕ) (n : OddNat) (k : ℕ) : Prop :=
  -- TailRemainderLevel L n k is large
  True
```

ただし、これはまだ早い。
今は level 5 と existence bridge までがよい。

## 11. 賢狼が試して欲しい実験補題

## 実験 A: pressure count positive から local pressure existence

```lean
theorem exists_sourcePressureDepth_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j)) := by
  -- unfold sourceContinuationPressureDepthCount
  -- List.countP positive -> exists
  sorry
```

`List.countP` の positive-to-exists 補題が既にあればそれを使う。
なければ専用補題を作る。

## 実験 B: pressure count positive から positive continuation mass existence

```lean
theorem exists_positive_sourceContinuationMass_of_pressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (hpos : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  rcases exists_sourcePressureDepth_of_pressureDepthCount_pos n k r len hpos with
    ⟨j, hj, hpressure⟩
  exact ⟨j, hj,
    sourceContinuationMass_pos_of_localPressure n k (r + j) hpressure⟩
```

## 実験 C: outruns-heavy から positive continuation mass existence

```lean
theorem exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  have hpos :
      0 < sourceContinuationPressureDepthCount n k r len :=
    sourcePressureDepthCount_pos_of_outrunsMoreThanHalf n k r len h
  exact exists_positive_sourceContinuationMass_of_pressureDepthCount_pos n k r len hpos
```

## 実験 D: level 5 residue counts

```lean
noncomputable def orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 127))

noncomputable def orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 255))
```

## 実験 E: TailRemainderLevel5 / TailFallingLevel5

```lean
def TailRemainderLevel5 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k

def TailFallingLevel5 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod128EqSixtyThreeTail n k
```

## 実験 F: level 4 static split alias

```lean
theorem tailRemainderLevel4_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel4 n k =
      TailFallingLevel5 n k + TailRemainderLevel5 n k := by
  unfold TailRemainderLevel4 TailFallingLevel5 TailRemainderLevel5
  exact tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven n k
```

## 実験 G: level 4 step grammar alias

```lean
theorem tailRemainderLevel4_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel4 n k ≤
      TailFallingLevel4 n (k + 1) + TailRemainderLevel4 n (k + 1) := by
  unfold TailRemainderLevel4 TailFallingLevel4
  exact tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree n k
```

## 実験 H: level 5 recursion edge は保留気味

level 5 recursion は進めてもよいが、ここから名前が長くなる。
先に pressure existence bridge を優先した方が収穫が大きい。

必要なら次。

```lean
theorem tailMod128OneHundredTwentySeven_le_nextTailMod128SixtyThree_add_nextTailMod128OneHundredTwentySeven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k ≤
      orbitWindowResidueCountMod128EqSixtyThreeTail n (k + 1) +
        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n (k + 1) := by
  -- pointwise anchors around mod 256 needed
  sorry
```

## 12. 次コミットの推奨順

```text
1. exists_sourcePressureDepth_of_pressureDepthCount_pos を試す

2. exists_positive_sourceContinuationMass_of_pressureDepthCount_pos を追加

3. exists_positive_sourceContinuationMass_of_outrunsMoreThanHalf を追加

4. level 5 counts を追加

5. TailRemainderLevel5 / TailFallingLevel5 を追加

6. tailRemainderLevel4_static_split を追加

7. tailRemainderLevel4_step_grammar を追加

8. level 5 recursion edge は、時間があれば追加

9. docs:
   Level4GenericPressure から PressureExistenceAndLevel5 へ接続
```

## 13. 総括

checkpoint `119` はかなり良い。

tower 側は level 4 へ進み、

```text
63 mod 64
  -> next 31 mod 64 + next 63 mod 64
```

が通った。

pressure 側は、任意 selected depth へ入れるようになった。

```text
pressure range + j < len
  -> local pressure
  -> positive continuation mass
```

ここから先は、tower を伸ばすだけではなく、

```text
pressure-heavy range
  -> local tower-entry opportunities
  -> sumS contribution + deep remainder
```

を作る段階じゃ。

賢狼としては、次は level 5 よりもまず **pressure count positive から local pressure existence** を推す。
それが通れば、pressure-heavy / outruns-heavy が本当に tower entry を生むことになる。
そこから deep remainder sparsity へ向かう道が開く。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 0572f272..1979f025 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1042,6 +1042,28 @@ noncomputable def orbitWindowResidueCountMod64EqSixtyThreeTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 63))
 
+/--
+Number of shifted-tail labels in residue class `63 mod 128`.
+
+This is the delayed-peeling child inside the shifted-tail `63 mod 64`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod128EqSixtyThreeTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 63))
+
+/--
+Number of shifted-tail labels in residue class `127 mod 128`.
+
+This is the continuing child inside the shifted-tail `63 mod 64` continuing
+color.
+-/
+noncomputable def orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 127))
+
 /-- Level `0` tail remainder: the whole shifted-tail exact-height-one reservoir. -/
 noncomputable def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowHeightCountEqTail n k 1
@@ -1070,6 +1092,14 @@ noncomputable def TailRemainderLevel3 (n : OddNat) (k : ℕ) : ℕ :=
 noncomputable def TailFallingLevel3 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowResidueCountMod32EqFifteenTail n k
 
+/-- Level `4` tail remainder: the shifted-tail `63 mod 64` continuing color. -/
+noncomputable def TailRemainderLevel4 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod64EqSixtyThreeTail n k
+
+/-- Level `4` falling color: the shifted-tail `31 mod 64` delayed-peeling color. -/
+noncomputable def TailFallingLevel4 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod64EqThirtyOneTail n k
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -4176,6 +4206,58 @@ theorem tailRemainderLevel2_static_split
   unfold TailRemainderLevel2 TailFallingLevel3 TailRemainderLevel3
   exact tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne n k
 
+/--
+The shifted-tail `63 mod 64` continuing color splits into its two children
+modulo `128`: the delayed-peeling child `63 mod 128` and the continuing child
+`127 mod 128`.
+-/
+theorem tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod64EqSixtyThreeTail n k =
+      orbitWindowResidueCountMod128EqSixtyThreeTail n k +
+        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k := by
+  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
+  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
+  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      by_cases h63 : oddOrbitLabel n (k + 1) % 128 = 63
+      · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
+          omega
+        simp [ih, hmod64, h63, Nat.add_assoc, Nat.add_comm]
+      · by_cases h127 : oddOrbitLabel n (k + 1) % 128 = 127
+        · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
+            omega
+          simp [ih, hmod64, h127, Nat.add_comm, Nat.add_left_comm]
+        · have hnotMod64 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
+            intro hmod64
+            have hchild :
+                oddOrbitLabel n (k + 1) % 128 = 63 ∨
+                  oddOrbitLabel n (k + 1) % 128 = 127 := by
+              omega
+            cases hchild with
+            | inl h =>
+                exact h63 h
+            | inr h =>
+                exact h127 h
+          simp [ih, hnotMod64, h63, h127]
+
+/--
+Level-alias version of the level-`3` static split.
+
+The level-`3` remainder is the sum of the level-`4` falling color and the
+level-`4` remainder.
+-/
+theorem tailRemainderLevel3_static_split
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel3 n k =
+      TailFallingLevel4 n k + TailRemainderLevel4 n k := by
+  unfold TailRemainderLevel3 TailFallingLevel4 TailRemainderLevel4
+  exact tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree n k
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4387,6 +4469,46 @@ theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtyt
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree hmod
 
+/--
+The `63 mod 128` subchannel moves to `31 mod 64` at the next label.
+
+This is the level-`4` recovery sibling inside the narrowing retention cylinder.
+-/
+theorem oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 128 = 63) :
+    oddOrbitLabel n (i + 1) % 64 = 31 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree hmod
+
+/--
+The `127 mod 128` subchannel continues as `63 mod 64` at the next label.
+
+The low-peeling path survives by entering the next thinner all-ones cylinder.
+-/
+theorem oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 128 = 127) :
+    oddOrbitLabel n (i + 1) % 64 = 63 := by
+  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
+    omega
+  have hheight : orbitWindowHeight n i = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
+      (Or.inr hmod8)
+  have hs : s (iterateT i n) = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
+  exact next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven hmod
+
 /--
 General orbit-label transition for the recovery sibling.
 
@@ -4686,6 +4808,74 @@ theorem tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
           · simp [hsource, htargetFifteen, htargetThirtyOne]
             omega
 
+/--
+Level-alias version of the level-`3` recursion edge.
+
+The level-`3` remainder re-enters the next level-`3` falling/remainder split.
+-/
+theorem tailRemainderLevel3_step_grammar
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel3 n k ≤
+      TailFallingLevel3 n (k + 1) + TailRemainderLevel3 n (k + 1) := by
+  unfold TailRemainderLevel3 TailFallingLevel3
+  exact tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne n k
+
+/--
+The shifted-tail `63 mod 64` continuing color enters the next shifted-tail
+`31 mod 64 / 63 mod 64` split.
+
+This is the level-`4` recursion edge of the delayed-reservoir tower.
+-/
+theorem tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod64EqSixtyThreeTail n k ≤
+      orbitWindowResidueCountMod64EqThirtyOneTail n (k + 1) +
+        orbitWindowResidueCountMod64EqSixtyThreeTail n (k + 1) := by
+  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
+  unfold orbitWindowResidueCountMod64EqThirtyOneTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransitionThirtyOne :
+          oddOrbitLabel n (k + 1) % 128 = 63 →
+            oddOrbitLabel n ((k + 1) + 1) % 64 = 31 :=
+        oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+          n (k + 1)
+      have htransitionSixtyThree :
+          oddOrbitLabel n (k + 1) % 128 = 127 →
+            oddOrbitLabel n ((k + 1) + 1) % 64 = 63 :=
+        oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127 n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 64 = 63
+      · have hchild :
+            oddOrbitLabel n (k + 1) % 128 = 63 ∨
+              oddOrbitLabel n (k + 1) % 128 = 127 := by
+          omega
+        cases hchild with
+        | inl h63 =>
+            have htargetThirtyOne :
+                oddOrbitLabel n ((k + 1) + 1) % 64 = 31 :=
+              htransitionThirtyOne h63
+            simp [hsource, htargetThirtyOne]
+            omega
+        | inr h127 =>
+            have htargetSixtyThree :
+                oddOrbitLabel n ((k + 1) + 1) % 64 = 63 :=
+              htransitionSixtyThree h127
+            simp [hsource, htargetSixtyThree]
+            omega
+      · by_cases htargetThirtyOne :
+            oddOrbitLabel n ((k + 1) + 1) % 64 = 31
+        · simp [hsource, htargetThirtyOne]
+          omega
+        · by_cases htargetSixtyThree :
+            oddOrbitLabel n ((k + 1) + 1) % 64 = 63
+          · simp [hsource, htargetSixtyThree]
+            omega
+          · simp [hsource, htargetThirtyOne, htargetSixtyThree]
+            omega
+
 /--
 One-step grammar for the shifted-tail exact-height-one reservoir.
 
@@ -5909,6 +6099,48 @@ theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
   unfold MoreThanHalf at h
   omega
 
+/--
+Meaning-name wrapper for extracting local source pressure from a finite source
+pressure profile.
+
+Use this theorem at call sites instead of the more generic internal extractor
+when the proof is conceptually moving from range pressure to a local depth.
+-/
+theorem sourcePressureAtDepth_of_pressureOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : SourceContinuationPressureOnRange n k r len)
+    (hj : j < len) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+      (orbitWindowRetentionMassPow2 n k (r + j)) :=
+  moreThanHalf_of_sourceContinuationPressure n k r len j h hj
+
+/--
+Local source pressure at any depth forces positive source continuation mass at
+that depth.
+-/
+theorem sourceContinuationMass_pos_of_localPressure
+    (n : OddNat) (k r : ℕ)
+    (h :
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k r)
+        (orbitWindowRetentionMassPow2 n k r)) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k r := by
+  unfold MoreThanHalf at h
+  omega
+
+/--
+Range pressure yields positive source continuation mass at any selected depth
+inside the range.
+-/
+theorem sourceContinuationMass_pos_of_pressureOnRange_at
+    (n : OddNat) (k r len j : ℕ)
+    (h : SourceContinuationPressureOnRange n k r len)
+    (hj : j < len) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
+  sourceContinuationMass_pos_of_localPressure n k (r + j)
+    (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)
+
 /--
 Extract local depth-two source pressure from the one-depth range pressure
 profile beginning at depth `2`.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index c7448325..a9f71d92 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -153,6 +153,7 @@ docs/Collatz-RecoveryDelayedBranch-115.md
 docs/Collatz-DelayedReservoirTower-116.md
 docs/Collatz-Level2Remainder-117.md
 docs/Collatz-Level3PressureEntrance-118.md
+docs/Collatz-Level4GenericPressure-119.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md
new file mode 100644
index 00000000..5ed81b9a
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md
@@ -0,0 +1,164 @@
+# Collatz Level-4 And Generic Pressure 119
+
+Checkpoint 119 advances both sides of the current program:
+
+```text
+tower side:
+  extend the delayed-reservoir tower to level 4
+
+pressure side:
+  generalize range-pressure extraction to any selected depth in the range
+```
+
+## Level-4 Tower Extension
+
+Checkpoint 118 fixed level `3`:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32 + next tail 31 mod 32
+```
+
+Checkpoint 119 adds level `4`:
+
+```text
+tail 63 mod 64
+  -> next tail 31 mod 64 + next tail 63 mod 64
+```
+
+New shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod128EqSixtyThreeTail
+orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+```
+
+Static split:
+
+```lean
+tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+```
+
+Reading:
+
+```text
+tail 63 mod 64
+  = tail 63 mod 128
+    + tail 127 mod 128
+```
+
+Pointwise aliases:
+
+```lean
+oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
+```
+
+The second name is shortened to avoid long-line warnings while the docstring
+keeps the full `127 mod 128 -> 63 mod 64` reading searchable.
+
+Count-level recursion edge:
+
+```lean
+tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+```
+
+## Level Aliases
+
+New aliases:
+
+```lean
+TailRemainderLevel4
+TailFallingLevel4
+```
+
+New alias theorems:
+
+```lean
+tailRemainderLevel3_static_split
+tailRemainderLevel3_step_grammar
+```
+
+Reading:
+
+```text
+level 3 remainder
+  = level 4 falling + level 4 remainder
+
+level 3 remainder
+  -> next level 3 falling + next level 3 remainder
+```
+
+## Generic Pressure Extraction
+
+Checkpoint 118 had a special one-depth extractor:
+
+```lean
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+```
+
+Checkpoint 119 adds general wrappers:
+
+```lean
+sourcePressureAtDepth_of_pressureOnRange
+sourceContinuationMass_pos_of_localPressure
+sourceContinuationMass_pos_of_pressureOnRange_at
+```
+
+The meaning is:
+
+```text
+SourceContinuationPressureOnRange n k r len
+  and j < len
+  -> local MoreThanHalf pressure at depth r+j
+  -> positive continuation mass at depth r+j
+```
+
+This is the first reusable pressure-side surface for selecting local
+tower-entry opportunities from a pressure-heavy range.
+
+## Current Tower
+
+The concrete tower now reaches:
+
+```text
+level 1:
+  3 mod 8 falls
+  7 mod 8 remains
+
+level 2:
+  7 mod 16 falls
+  15 mod 16 remains
+
+level 3:
+  15 mod 32 falls
+  31 mod 32 remains
+
+level 4:
+  31 mod 64 falls
+  63 mod 64 remains
+```
+
+The next expected concrete level is:
+
+```text
+level 5:
+  63 mod 128 falls
+  127 mod 128 remains
+```
+
+## Next Direction
+
+The tower and pressure API are now close enough to start finite accounting
+experiments:
+
+```text
+pressure-heavy range
+  -> many selected local pressure depths
+  -> positive local tower-entry mass
+  -> delayed budget plus deep remainder
+```
+
+The likely next hard question is not how to extend one more residue level, but
+how to count useful selected local pressure depths without double-counting the
+same finite window mass.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index ebbda1e9..0ce995d9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1073,6 +1073,44 @@ sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
 This is the first bridge from the range profile vocabulary to the delayed
 reservoir budget entrance.
 
+## Level-4 And Generic Pressure
+
+Checkpoint 119 extends the concrete tower to level `4`:
+
+```lean
+orbitWindowResidueCountMod128EqSixtyThreeTail
+orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+```
+
+The tower edge is:
+
+```text
+tail 63 mod 64
+  -> next tail 31 mod 64 + next tail 63 mod 64
+```
+
+The alias layer is:
+
+```lean
+TailRemainderLevel4
+TailFallingLevel4
+tailRemainderLevel3_static_split
+tailRemainderLevel3_step_grammar
+```
+
+Checkpoint 119 also generalizes the pressure entrance:
+
+```lean
+sourcePressureAtDepth_of_pressureOnRange
+sourceContinuationMass_pos_of_localPressure
+sourceContinuationMass_pos_of_pressureOnRange_at
+```
+
+Use these names when a proof has a pressure profile over a depth range and
+needs a local tower-entry opportunity at a selected depth `r + j`.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 7fe2834a..3e41f1b9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -351,6 +351,19 @@ tailRemainderLevel2_step_grammar
 tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
 sourcePressureDepthTwo_of_pressureOnRange_two_one
 sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+orbitWindowResidueCountMod128EqSixtyThreeTail
+orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+TailRemainderLevel4
+TailFallingLevel4
+tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+tailRemainderLevel3_static_split
+tailRemainderLevel3_step_grammar
+oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
+tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+sourcePressureAtDepth_of_pressureOnRange
+sourceContinuationMass_pos_of_localPressure
+sourceContinuationMass_pos_of_pressureOnRange_at
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-119.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-119.md
new file mode 100644
index 00000000..b53f0e7a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-119.md
@@ -0,0 +1,319 @@
+# Report Petal 119: Level-4 And Generic Pressure
+
+## Summary
+
+Checkpoint 119 closes two useful extensions.
+
+Tower side:
+
+```text
+tail 63 mod 64
+  -> next tail 31 mod 64 + next tail 63 mod 64
+```
+
+Pressure side:
+
+```text
+SourceContinuationPressureOnRange n k r len
+  and j < len
+  -> local pressure at depth r+j
+  -> positive continuation mass at depth r+j
+```
+
+This moves the project from a one-depth pressure entrance to a reusable
+selected-depth interface.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New level-`4` shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod128EqSixtyThreeTail
+orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+```
+
+New aliases:
+
+```lean
+TailRemainderLevel4
+TailFallingLevel4
+```
+
+Level-`4` static split:
+
+```lean
+tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+```
+
+Level-`3` alias theorems:
+
+```lean
+tailRemainderLevel3_static_split
+tailRemainderLevel3_step_grammar
+```
+
+Pointwise level-`4` aliases:
+
+```lean
+oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
+```
+
+Level-`4` recursion edge:
+
+```lean
+tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+```
+
+Generic pressure wrappers:
+
+```lean
+sourcePressureAtDepth_of_pressureOnRange
+sourceContinuationMass_pos_of_localPressure
+sourceContinuationMass_pos_of_pressureOnRange_at
+```
+
+## Experimental Results
+
+### Experiment A-C: generic pressure extraction
+
+Succeeded.
+
+The new wrapper:
+
+```lean
+sourcePressureAtDepth_of_pressureOnRange
+```
+
+is a meaning-name alias around:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+```
+
+The positivity bridge:
+
+```lean
+sourceContinuationMass_pos_of_localPressure
+```
+
+works for any depth, not just depth `2`.
+
+The composed range theorem:
+
+```lean
+sourceContinuationMass_pos_of_pressureOnRange_at
+```
+
+gives:
+
+```text
+pressure range + selected index j
+  -> positive continuation mass at depth r+j
+```
+
+### Experiment D-E: level-4 residue counts and split
+
+Succeeded.
+
+```lean
+orbitWindowResidueCountMod128EqSixtyThreeTail
+orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
+tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
+```
+
+Reading:
+
+```text
+tail 63 mod 64
+  = tail 63 mod 128
+    + tail 127 mod 128
+```
+
+### Experiment F-H: level-4 aliases and recursion support
+
+Succeeded.
+
+```lean
+TailRemainderLevel4
+TailFallingLevel4
+tailRemainderLevel3_static_split
+tailRemainderLevel3_step_grammar
+```
+
+The level-`3` alias grammar now reads:
+
+```text
+level 3 remainder
+  = level 4 falling + level 4 remainder
+
+level 3 remainder
+  -> next level 3 falling + next level 3 remainder
+```
+
+### Extra: pointwise aliases for level 4
+
+The raw arithmetic anchors already existed:
+
+```lean
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
+next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
+```
+
+Checkpoint 119 added orbit-label versions:
+
+```lean
+oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
+```
+
+The second name is shortened to avoid line-length warnings.
+
+### Extra: level-4 count recursion
+
+Succeeded.
+
+```lean
+tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
+```
+
+Reading:
+
+```text
+tail 63 mod 64
+  -> next tail 31 mod 64
+     or
+     next tail 63 mod 64
+```
+
+## Mathematical Reading
+
+The concrete tower now reaches:
+
+```text
+level 1:
+  3 mod 8 falls
+  7 mod 8 remains
+
+level 2:
+  7 mod 16 falls
+  15 mod 16 remains
+
+level 3:
+  15 mod 32 falls
+  31 mod 32 remains
+
+level 4:
+  31 mod 64 falls
+  63 mod 64 remains
+```
+
+This confirms the recurring pattern:
+
+```text
+falling color:
+  2^(L+1)-1 modulo 2^(L+2)
+
+continuing color:
+  2^(L+2)-1 modulo 2^(L+2)
+```
+
+The pressure interface now supports selected local depths:
+
+```text
+range pressure
+  -> choose j
+  -> local positive continuation mass
+```
+
+This is a needed precondition for finite accounting over pressure-heavy ranges.
+
+## Documentation Updates
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-Level4GenericPressure-119.md
+```
+
+## Verification
+
+Commands run:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched files>
+```
+
+Result:
+
+```text
+Both builds completed successfully.
+No `sorry` was found in `DkMath.Collatz.PetalBridge`.
+`git diff --check` reported no whitespace errors.
+```
+
+Known unrelated warning remains:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Implementation Candidates
+
+### 1. Add level 5 concrete split
+
+Expected next split:
+
+```text
+tail 127 mod 128
+  = tail 127 mod 256
+    + tail 255 mod 256
+```
+
+The raw arithmetic anchors around `mod 256` already appear to exist.
+
+### 2. Start finite selected-depth accounting
+
+The next harder bridge is no longer merely another residue level.  It is:
+
+```text
+SourceContinuationPressureOnRange n k r len
+  -> many usable local pressure depths
+```
+
+The new `sourceContinuationMass_pos_of_pressureOnRange_at` gives one selected
+depth.  A future theorem should package a finite collection of selected depths
+without double-counting window mass.
+
+### 3. Deep-remainder sparsity
+
+The tower suggests that continuing mass is pushed into:
+
+```text
+7 mod 8
+15 mod 16
+31 mod 32
+63 mod 64
+...
+```
+
+The future obstruction target is a sparsity statement for deep all-ones
+residue classes, probably under separation or orbit-window hypotheses.
````
`````
