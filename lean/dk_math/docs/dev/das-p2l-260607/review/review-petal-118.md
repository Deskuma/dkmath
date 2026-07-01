# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 692c6618872260d6e4a8b1049bb49de92c5f3ae3

## Report

117 進めました。`15 mod 16` の level 2 remainder まで concrete に固定できています。

主な追加は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:1024) です。

- `orbitWindowResidueCountMod32EqFifteenTail`
- `orbitWindowResidueCountMod32EqThirtyOneTail`
- `TailRemainderLevel0/1/2`
- `TailFallingLevel1/2`
- `tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne`
- `tailRemainderLevel1_static_split`
- `tailRemainderLevel1_step_grammar`
- `tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen`
- `sourceContinuationMass_depth_two_pos_of_pressure_depth_two`
- `sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder`

これで tower は次の形まで通りました。

```text
level 1:
  tail 7 mod 8
    -> next tail 3 mod 8 + next tail 7 mod 8

level 2:
  tail 15 mod 16
    -> next tail 7 mod 16 + next tail 15 mod 16
```

さらに pressure 側の入口として、depth 2 の `MoreThanHalf` から continuation mass の正性を得る補題も入りました。

文書も同期済みです。

- [Collatz-Level2Remainder-117.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md)
- [report-petal-117.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-117.md)
- README / Guide / Status 更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath.Collatz.Collatz2K26` 成功
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean` 該当なし
- `git diff --check` 問題なし

既存の unrelated warning として、`DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は継続しています。

## Review

## 1. 状況分析

checkpoint `117` は、delayed-reservoir tower が **level 2** まで concrete に固定された回じゃ。

前回 `116` では、

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8
```

まで通った。今回 `117` では、その次の continuing remainder である `15 mod 16` について、

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

まで通っている。つまり、tower が単発の比喩ではなく、少なくとも level 2 まで再帰的に見えることが Lean 上で確認された。

今回の追加名も、構造としてかなり整理されている。

```lean
TailRemainderLevel0
TailRemainderLevel1
TailRemainderLevel2
TailFallingLevel1
TailFallingLevel2
```

これで、低解像度の residue 名を直接扱うだけではなく、

```text
falling color
continuing remainder
```

という会計語彙で読めるようになった。

## 2. 今回の核心

今回の核心は二つある。

第一に、level 2 の static split。

```lean
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
```

これは、

```text
tail 15 mod 16
  = tail 15 mod 32
    + tail 31 mod 32
```

を固定している。

第二に、level 2 の recursion edge。

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

これは、

```text
tail 15 mod 16
  -> next tail 7 mod 16
     or
     next tail 15 mod 16
```

を count level で表している。

この二つにより、tower は次の形になった。

```text
level 0:
  exact-height-one reservoir

level 1:
  3 mod 8 falls
  7 mod 8 remains

level 2:
  7 mod 16 falls
  15 mod 16 remains
```

ここで大事なのは、「残るもの」が同じ形で次の解像度へ送られていることじゃ。

## 3. レビュー

## 3.1. level alias を入れた判断は正しい

今回の `TailRemainderLevel0/1/2` と `TailFallingLevel1/2` は、薄い alias だが非常に良い。

これまでの表記は、

```lean
orbitWindowResidueCountMod8EqSevenTail
orbitWindowResidueCountMod16EqFifteenTail
```

のように、具体 residue 名が主語だった。

これは正確だが、tower の構造を読むには少し重い。

今回 alias が入ったことで、

```text
TailRemainderLevel1
TailRemainderLevel2
TailFallingLevel1
TailFallingLevel2
```

として、「何の役割を持つ色か」が名前から読めるようになった。

これは後で一般化するためにも良い。
いきなり再帰定義に飛ばず、まず level 0/1/2 を手で固めるのは安全じゃ。

## 3.2. level 2 static split は tower の安定性確認

`tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne` は、前回の

```lean
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

と同型じゃ。

この「同じ形で一段深く進めた」ことが大事。

つまり、たまたま `7 mod 8` だけで起きた現象ではなく、

```text
continuing color:
  2^m - 1 mod 2^m
```

を一段細かく見ると、

```text
falling child:
  2^(m-1)-1 mod 2^(m+1)

continuing child:
  2^(m+1)-1 mod 2^(m+1)
```

のような形が見え始めている。

まだ一般化は早いが、低段のデータとしてはかなり強い。

## 3.3. level 2 recursion edge が本当に大きい

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

これは今回の一番大きな theorem じゃ。

単に `15 mod 16` を `15 mod 32` / `31 mod 32` に割っただけではない。
それぞれの child が次 step でどう移るかまで使って、

```text
tail 15 mod 16
  -> next tail 7 mod 16
     +
     next tail 15 mod 16
```

を示した。

ここで使われた既存 pointwise theorem、

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

も重要じゃ。

これは tower 一般化の原型になっている。

## 3.4. pressure entrance は小さいが重要

今回追加された、

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

は、tower 本体とは少し別の意味で重要じゃ。

いま tower は tail residue の会計として育っている。
だが Collatz.PetalBridge の本線は、pressure / outruns の頻度から height / drift へつなぐこと。

その入口として、

```text
MoreThanHalf continuation pressure at depth 2
  -> continuation mass at depth 2 is positive
```

が入った。

これはかなり小さい補題だが、後で range pressure から tower budget へ入る入口になる。

## 4. 数学的解説

今回の tower を低位 bit で見ると、非常に綺麗じゃ。

level 0 は exact height one reservoir。

```text
q ≡ 3 mod 4
```

これを mod 8 で見ると、

```text
q ≡ 3 mod 8
q ≡ 7 mod 8
```

に分かれる。

`3 mod 8` は次に height \(\ge 2\) へ落ちる。
`7 mod 8` は残る。

次に、その `7 mod 8` を mod 16 で見る。

```text
q ≡ 7 mod 16
q ≡ 15 mod 16
```

`7 mod 16` は次に falling 側へ移る。
`15 mod 16` は残る。

次に、`15 mod 16` を mod 32 で見る。

```text
q ≡ 15 mod 32
q ≡ 31 mod 32
```

今回ここまで分解した。
そして `15 mod 32` は次に `7 mod 16` 側、つまり level 2 falling 側へ移る。
`31 mod 32` は次も `15 mod 16` 側へ残る。

したがって、tower はこう読む。

```text
残る色は、全部 1 の低位 bit に寄っていく。

その色を一段細かく見ると、
一部は falling child になり、
残りはさらに深い全部 1 の色として残る。
```

これはかなり Collatz 的じゃ。

## 5. 一歩先ゆく推論

今回の結果から、より大きな構造が見える。

level \(m\) の continuing remainder は、おそらく次の形をしている。

```text
2^(m+2) - 1 mod 2^(m+2)
```

具体的には、

```text
level 1 remainder:
  7 mod 8 = 2^3 - 1

level 2 remainder:
  15 mod 16 = 2^4 - 1

level 3 remainder:
  31 mod 32 = 2^5 - 1
```

そして falling child は、その一段前の「半分 1」側。

```text
level 1 falling:
  3 mod 8

level 2 falling:
  7 mod 16

level 3 falling:
  15 mod 32
```

つまり、各 level で、

```text
TailRemainderLevel m
  = TailFallingLevel (m+1)
    + TailRemainderLevel (m+1)
```

に近い構造がある。

ただし、これはまだ一般定理にしない方がいい。
理由は、index shift と next-window の扱いがまだ手で見えている段階だからじゃ。

まずは level 3 まで concrete に進めるのが正しい。

## 6. 今回閉じたもの

今回閉じたものは、次の四つ。

```text
1. level 2 の residue count:
   15 mod 32 / 31 mod 32

2. level 1 remainder の static split:
   7 mod 8 = 7 mod 16 + 15 mod 16

3. level 2 の static split:
   15 mod 16 = 15 mod 32 + 31 mod 32

4. level 2 recursion:
   15 mod 16 -> next 7 mod 16 + next 15 mod 16
```

さらに pressure 側入口として、

```text
5. pressure at depth 2 -> continuation mass depth 2 positive
```

も入った。

これで tower と pressure vocabulary の接点が初めて作られた。

## 7. まだ閉じていないもの

まだ閉じていない本命は二つ。

```text
1. level 3 remainder:
   31 mod 32 -> 31 mod 64 + 63 mod 64

2. range pressure:
   SourceContinuationPressureOnRange n k 2 1
   -> local MoreThanHalf at depth 2
```

前者は tower の concrete extension。
後者は pressure API から tower budget へ入るための caller bridge。

どちらも重要だが、順番としては次のように分けるとよい。

```text
実装安定性を伸ばす:
  level 3 concrete split / recursion

pressure 本線へ戻る:
  range pressure specialization
```

次 checkpoint では、この二本を両方少し進めるのがよい。

## 8. 次の指示

## 8.1. level 3 concrete split を追加

まず `31 mod 32` を `64` で分ける。

```lean
noncomputable def orbitWindowResidueCountMod64EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 31))

noncomputable def orbitWindowResidueCountMod64EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 63))
```

split theorem。

```lean
theorem tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k =
      orbitWindowResidueCountMod64EqThirtyOneTail n k +
        orbitWindowResidueCountMod64EqSixtyThreeTail n k := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h31 : oddOrbitLabel n (k + 1) % 64 = 31
      · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
          omega
        have hnot63 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
          omega
        simp [ih, hmod32, h31, hnot63, Nat.add_assoc, Nat.add_comm]
      · by_cases h63 : oddOrbitLabel n (k + 1) % 64 = 63
        · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
            omega
          simp [ih, hmod32, h63, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod32 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
            intro hmod32
            have hchild :
                oddOrbitLabel n (k + 1) % 64 = 31 ∨
                  oddOrbitLabel n (k + 1) % 64 = 63 := by
              omega
            cases hchild with
            | inl h =>
                exact h31 h
            | inr h =>
                exact h63 h
          simp [ih, hnotMod32, h31, h63]
```

これは前回と同型なので、通る可能性は高い。

## 8.2. level 3 recursion edge を追加

報告には既存候補として次が挙がっている。

```lean
oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
```

これを使って、

```lean
theorem tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k ≤
      orbitWindowResidueCountMod32EqFifteenTail n (k + 1) +
        orbitWindowResidueCountMod32EqThirtyOneTail n (k + 1) := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransitionFifteen :
          oddOrbitLabel n (k + 1) % 64 = 31 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
          n (k + 1)
      have htransitionThirtyOne :
          oddOrbitLabel n (k + 1) % 64 = 63 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
          n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 32 = 31
      · have hchild :
            oddOrbitLabel n (k + 1) % 64 = 31 ∨
              oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        cases hchild with
        | inl h31 =>
            have htarget15 :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
              htransitionFifteen h31
            simp [hsource, htarget15]
            omega
        | inr h63 =>
            have htarget31 :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
              htransitionThirtyOne h63
            simp [hsource, htarget31]
            omega
      · by_cases htarget15 :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15
        · simp [hsource, htarget15]
          omega
        · by_cases htarget31 :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31
          · simp [hsource, htarget15, htarget31]
            omega
          · simp [hsource, htarget15, htarget31]
            omega
```

これが通れば、tower は level 3 まで伸びる。

## 8.3. level 3 alias を追加

```lean
def TailRemainderLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqThirtyOneTail n k

def TailFallingLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqFifteenTail n k
```

そして alias theorem。

```lean
theorem tailRemainderLevel2_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k =
      TailFallingLevel3 n k + TailRemainderLevel3 n k := by
  unfold TailRemainderLevel2 TailFallingLevel3 TailRemainderLevel3
  exact tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne n k
```

```lean
theorem tailRemainderLevel2_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k ≤
      TailFallingLevel2 n (k + 1) + TailRemainderLevel2 n (k + 1) := by
  unfold TailRemainderLevel2 TailFallingLevel2
  exact tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen n k
```

注意：`step_grammar` の target が `TailFallingLevel2` なのは、次 window で `7 mod 16 / 15 mod 16` に戻るからじゃ。
一方、`static_split` は level 3 falling / level 3 remainder を使う。

## 9. range pressure 側への次の橋

次に重要なのは、

```text
SourceContinuationPressureOnRange n k 2 1
```

から local depth 2 pressure を取り出すこと。

checkpoint `107` 系の定義がたぶん、

```lean
SourceContinuationPressureOnRange n k r len
```

で、各 \(j < len\) について `MoreThanHalf ... (r+j)` を言う形なら、`r=2`, `len=1` から `j=0` を取ればよい。

候補：

```lean
theorem sourcePressureDepthTwo_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k 2)
      (orbitWindowRetentionMassPow2 n k 2) := by
  -- unfold SourceContinuationPressureOnRange at h
  -- specialize h 0
  -- simp at h
  -- exact h
  sorry
```

もし `SourceContinuationPressureOnRange` が count filling theorem 側の predicate なら、展開に合わせて修正。

これが通れば、

```lean
theorem sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 :=
  sourceContinuationMass_depth_two_pos_of_pressure_depth_two n k
    (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
```

が通る。

これで range vocabulary から tower に入れる。

## 10. 一歩先の次の一手

level 3 まで concrete に伸びたら、次は **finite-depth remainder budget** を作りたい。

すでに level 1 remainder 付き budget はある。

```lean
tailExactHeightOneReservoir_budget_with_remainder
```

次は level 2 remainder 付き budget。

読みとしては、

```text
base + exact-height-one reservoir
  <= future sumS
     + TailRemainderLevel2
```

を狙う。

ただし、index は慎重に見る必要がある。

level 1 budget は、

```text
(k + 1) + level0 <= sumS n (k + 2) + level1 remainder at k
```

だった。

level 2 まで落とすなら、おそらく、

```text
(k + 2) + level0 <= sumS n (k + 3) + level2 remainder at k
```

のような形になる。

候補：

```lean
theorem tailExactHeightOneReservoir_budget_with_level2_remainder
    (n : OddNat) (k : ℕ) :
    ((k + 1) + 1) + TailRemainderLevel0 n k ≤
      sumS n (((k + 1) + 1) + 1) +
        TailRemainderLevel2 n k := by
  -- level0 split:
  --   level1 falling goes to sumS after one step
  --   level1 remainder remains
  -- level1 remainder static split:
  --   level2 falling + level2 remainder
  -- level2 falling should contribute one step later
  sorry
```

この補題は少し重い。
でも level 2 tower が通った後の自然な本命じゃ。

## 11. さらに先の推論

もし level \(L\) までこの pattern が続くなら、有限段では次の会計が見える。

```text
base + L layers + initial reservoir
  <= future sumS + level L remainder
```

ここで level \(L\) remainder は、

```text
2^(L+2)-1 mod 2^(L+2)
```

の tail count になる。

この remainder は、かなり細い residue class。
有限 window \(k\) に対して、level を深くすれば、remainder が小さくなる可能性がある。

ここが大本命かもしれない。

```text
remainder を 0 にするのではなく、
有限 window に対して十分細い residue class へ追い込む。
```

これは `Big - Gap = Body` 的にも、Gnomon 一色線的にも自然じゃ。
色を捨てずに追跡し、残る色がどんどん細い単色線へ寄っていく。

## 12. 賢狼が試して欲しい実験補題

## 実験 A: level 3 residue count

```lean
noncomputable def orbitWindowResidueCountMod64EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 31))

noncomputable def orbitWindowResidueCountMod64EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 63))
```

## 実験 B: level 3 static split

```lean
theorem tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k =
      orbitWindowResidueCountMod64EqThirtyOneTail n k +
        orbitWindowResidueCountMod64EqSixtyThreeTail n k := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h31 : oddOrbitLabel n (k + 1) % 64 = 31
      · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
          omega
        have hnot63 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
          omega
        simp [ih, hmod32, h31, hnot63, Nat.add_assoc, Nat.add_comm]
      · by_cases h63 : oddOrbitLabel n (k + 1) % 64 = 63
        · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
            omega
          simp [ih, hmod32, h63, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod32 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
            intro hmod32
            have hchild :
                oddOrbitLabel n (k + 1) % 64 = 31 ∨
                  oddOrbitLabel n (k + 1) % 64 = 63 := by
              omega
            cases hchild with
            | inl h =>
                exact h31 h
            | inr h =>
                exact h63 h
          simp [ih, hnotMod32, h31, h63]
```

## 実験 C: level 3 recursion edge

```lean
theorem tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k ≤
      orbitWindowResidueCountMod32EqFifteenTail n (k + 1) +
        orbitWindowResidueCountMod32EqThirtyOneTail n (k + 1) := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransition15 :
          oddOrbitLabel n (k + 1) % 64 = 31 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
          n (k + 1)
      have htransition31 :
          oddOrbitLabel n (k + 1) % 64 = 63 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
          n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 32 = 31
      · have hchild :
            oddOrbitLabel n (k + 1) % 64 = 31 ∨
              oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        cases hchild with
        | inl h31 =>
            have htarget15 :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
              htransition15 h31
            simp [hsource, htarget15]
            omega
        | inr h63 =>
            have htarget31 :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
              htransition31 h63
            simp [hsource, htarget31]
            omega
      · by_cases htarget15 :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15
        · simp [hsource, htarget15]
          omega
        · by_cases htarget31 :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31
          · simp [hsource, htarget15, htarget31]
            omega
          · simp [hsource, htarget15, htarget31]
            omega
```

## 実験 D: level 3 aliases

```lean
def TailRemainderLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqThirtyOneTail n k

def TailFallingLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqFifteenTail n k
```

## 実験 E: level 2 static split alias

```lean
theorem tailRemainderLevel2_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k =
      TailFallingLevel3 n k + TailRemainderLevel3 n k := by
  unfold TailRemainderLevel2 TailFallingLevel3 TailRemainderLevel3
  exact tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne n k
```

## 実験 F: level 2 step grammar alias

```lean
theorem tailRemainderLevel2_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k ≤
      TailFallingLevel2 n (k + 1) + TailRemainderLevel2 n (k + 1) := by
  unfold TailRemainderLevel2 TailFallingLevel2
  exact tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen n k
```

## 実験 G: range pressure to local depth 2 pressure

```lean
theorem sourcePressureDepthTwo_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k 2)
      (orbitWindowRetentionMassPow2 n k 2) := by
  unfold SourceContinuationPressureOnRange at h
  specialize h 0
  have hz : 0 < 1 := by omega
  specialize h hz
  simpa using h
```

もし `SourceContinuationPressureOnRange` の引数順や定義が違えば、ここだけ調整。

## 実験 H: range pressure to positive continuation mass

```lean
theorem sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 :=
  sourceContinuationMass_depth_two_pos_of_pressure_depth_two n k
    (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
```

## 13. 次コミットの推奨順

```text
1. level 3 residue count:
   mod64 = 31 / 63

2. level 3 static split:
   31 mod 32 = 31 mod 64 + 63 mod 64

3. level 3 recursion edge:
   31 mod 32 -> next 15 mod 32 + next 31 mod 32

4. TailRemainderLevel3 / TailFallingLevel3 aliases

5. tailRemainderLevel2_static_split

6. tailRemainderLevel2_step_grammar

7. SourceContinuationPressureOnRange n k 2 1 から local pressure を抽出

8. local pressure から continuation mass positive へ接続

9. docs:
   Level2Remainder から Level3Remainder / PressureRangeEntrance へ接続
```

## 14. 総括

checkpoint `117` は非常に順調じゃ。

delayed-reservoir tower は、level 2 まで concrete に見えた。

```text
level 1:
  tail 7 mod 8
    -> next tail 3 mod 8 + next tail 7 mod 8

level 2:
  tail 15 mod 16
    -> next tail 7 mod 16 + next tail 15 mod 16
```

これは、Gnomon 一色線で言えば、

```text
落ちる色を取り出す
残る色をさらに細い一色候補へ送る
```

という処理そのものじゃ。

次は level 3。
同時に、pressure range から depth 2 local pressure への入口を作る。

ここが通れば、tower は「綺麗な residue 文法」から、「pressure-heavy な Collatz window を実際に処理する会計装置」へ近づく。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 6e1d3478..8f4731b6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -998,6 +998,48 @@ noncomputable def orbitWindowResidueCountMod16EqFifteenTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 15))
 
+/--
+Number of shifted-tail labels in residue class `15 mod 32`.
+
+This is the delayed-peeling child inside the shifted-tail `15 mod 16`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod32EqFifteenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 15))
+
+/--
+Number of shifted-tail labels in residue class `31 mod 32`.
+
+This is the continuing child inside the shifted-tail `15 mod 16` continuing
+color.
+-/
+noncomputable def orbitWindowResidueCountMod32EqThirtyOneTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 31))
+
+/-- Level `0` tail remainder: the whole shifted-tail exact-height-one reservoir. -/
+noncomputable def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowHeightCountEqTail n k 1
+
+/-- Level `1` tail remainder: the shifted-tail `7 mod 8` continuing color. -/
+noncomputable def TailRemainderLevel1 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod8EqSevenTail n k
+
+/-- Level `2` tail remainder: the shifted-tail `15 mod 16` continuing color. -/
+noncomputable def TailRemainderLevel2 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod16EqFifteenTail n k
+
+/-- Level `1` falling color: the shifted-tail `3 mod 8` delayed-peeling color. -/
+noncomputable def TailFallingLevel1 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod8EqThreeTail n k
+
+/-- Level `2` falling color: the shifted-tail `7 mod 16` delayed-peeling color. -/
+noncomputable def TailFallingLevel2 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod16EqSevenTail n k
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -3997,9 +4039,61 @@ theorem tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
             | inl h =>
                 exact hseven h
             | inr h =>
-                exact hfifteen h
+            exact hfifteen h
           simp [ih, hnotMod8, hseven, hfifteen]
 
+/--
+The shifted-tail `15 mod 16` continuing color splits into its two children
+modulo `32`: the delayed-peeling child `15 mod 32` and the continuing child
+`31 mod 32`.
+-/
+theorem tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod16EqFifteenTail n k =
+      orbitWindowResidueCountMod32EqFifteenTail n k +
+        orbitWindowResidueCountMod32EqThirtyOneTail n k := by
+  unfold orbitWindowResidueCountMod16EqFifteenTail
+  unfold orbitWindowResidueCountMod32EqFifteenTail
+  unfold orbitWindowResidueCountMod32EqThirtyOneTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      by_cases hfifteen : oddOrbitLabel n (k + 1) % 32 = 15
+      · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
+          omega
+        simp [ih, hmod16, hfifteen, Nat.add_assoc, Nat.add_comm]
+      · by_cases h31 : oddOrbitLabel n (k + 1) % 32 = 31
+        · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
+            omega
+          simp [ih, hmod16, h31, Nat.add_comm, Nat.add_left_comm]
+        · have hnotMod16 : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
+            intro hmod16
+            have hchild :
+                oddOrbitLabel n (k + 1) % 32 = 15 ∨
+                  oddOrbitLabel n (k + 1) % 32 = 31 := by
+              omega
+            cases hchild with
+            | inl h =>
+                exact hfifteen h
+            | inr h =>
+                exact h31 h
+          simp [ih, hnotMod16, hfifteen, h31]
+
+/--
+Level-alias version of the level-`1` static split.
+
+The level-`1` remainder is the sum of the level-`2` falling color and the
+level-`2` remainder.
+-/
+theorem tailRemainderLevel1_static_split
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel1 n k =
+      TailFallingLevel2 n k + TailRemainderLevel2 n k := by
+  unfold TailRemainderLevel1 TailFallingLevel2 TailRemainderLevel2
+  exact tailResidueCountMod8EqSeven_split_mod16_seven_fifteen n k
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4369,6 +4463,78 @@ theorem tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
   rw [tailHeightCountEq_one_split_mod8_three_seven] at h
   exact h
 
+/--
+Level-alias version of the level-`1` recursion edge.
+
+The level-`1` remainder enters the next tail reservoir and splits into the
+level-`1` falling color and the level-`1` remainder at the next window.
+-/
+theorem tailRemainderLevel1_step_grammar
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel1 n k ≤
+      TailFallingLevel1 n (k + 1) + TailRemainderLevel1 n (k + 1) := by
+  unfold TailRemainderLevel1 TailFallingLevel1
+  exact tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven n k
+
+/--
+The shifted-tail `15 mod 16` continuing color enters the next shifted-tail
+`7 mod 16 / 15 mod 16` split.
+
+This is the level-`2` recursion edge of the delayed-reservoir tower.
+-/
+theorem tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod16EqFifteenTail n k ≤
+      orbitWindowResidueCountMod16EqSevenTail n (k + 1) +
+        orbitWindowResidueCountMod16EqFifteenTail n (k + 1) := by
+  unfold orbitWindowResidueCountMod16EqFifteenTail
+  unfold orbitWindowResidueCountMod16EqSevenTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransitionSeven :
+          oddOrbitLabel n (k + 1) % 32 = 15 →
+            oddOrbitLabel n ((k + 1) + 1) % 16 = 7 :=
+        oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+          n (k + 1)
+      have htransitionFifteen :
+          oddOrbitLabel n (k + 1) % 32 = 31 →
+            oddOrbitLabel n ((k + 1) + 1) % 16 = 15 :=
+        oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+          n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 16 = 15
+      · have hchild :
+            oddOrbitLabel n (k + 1) % 32 = 15 ∨
+              oddOrbitLabel n (k + 1) % 32 = 31 := by
+          omega
+        cases hchild with
+        | inl hfifteen =>
+            have htargetSeven :
+                oddOrbitLabel n ((k + 1) + 1) % 16 = 7 :=
+              htransitionSeven hfifteen
+            have htargetNotFifteen :
+                oddOrbitLabel n ((k + 1) + 1) % 16 ≠ 15 := by
+              omega
+            simp [hsource, htargetSeven]
+            omega
+        | inr h31 =>
+            have htargetFifteen :
+                oddOrbitLabel n ((k + 1) + 1) % 16 = 15 :=
+              htransitionFifteen h31
+            simp [hsource, htargetFifteen]
+            omega
+      · by_cases htargetSeven : oddOrbitLabel n ((k + 1) + 1) % 16 = 7
+        · simp [hsource, htargetSeven]
+          omega
+        · by_cases htargetFifteen :
+            oddOrbitLabel n ((k + 1) + 1) % 16 = 15
+          · simp [hsource, htargetFifteen]
+            omega
+          · simp [hsource, htargetSeven, htargetFifteen]
+            omega
+
 /--
 One-step grammar for the shifted-tail exact-height-one reservoir.
 
@@ -5575,6 +5741,41 @@ theorem sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
     tailResidueCountMod8EqThree_delayed_drift n k
   omega
 
+/--
+More-than-half pressure at depth `2` forces positive depth-two continuation
+mass.
+
+This is the first thin entrance from the pressure vocabulary into the delayed
+reservoir budget.
+-/
+theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+    (n : OddNat) (k : ℕ)
+    (h :
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k 2)
+        (orbitWindowRetentionMassPow2 n k 2)) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k 2 := by
+  unfold MoreThanHalf at h
+  omega
+
+/--
+Pressure-facing wrapper for the depth-two delayed-reservoir budget.
+
+The pressure hypothesis is not needed by the inequality itself; it records the
+intended caller context, where a pressure-heavy depth supplies positive
+continuation mass and then uses the delayed budget.
+-/
+theorem sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+    (n : OddNat) (k : ℕ)
+    (_h :
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k 2)
+        (orbitWindowRetentionMassPow2 n k 2)) :
+    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+      sumS n ((k + 1) + 1) +
+        orbitWindowResidueCountMod8EqSevenTail n k :=
+  sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder n k
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index c3d9e320..327fc53e 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -151,6 +151,7 @@ docs/Collatz-FrequencyHeightBridge-113.md
 docs/Collatz-TailFacingHeightBridge-114.md
 docs/Collatz-RecoveryDelayedBranch-115.md
 docs/Collatz-DelayedReservoirTower-116.md
+docs/Collatz-Level2Remainder-117.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md
new file mode 100644
index 00000000..fee33c33
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md
@@ -0,0 +1,176 @@
+# Collatz Level-2 Remainder 117
+
+Checkpoint 117 extends the delayed-reservoir tower from level `1` to level `2`.
+
+Checkpoint 116 fixed:
+
+```text
+tail 7 mod 8
+  -> next tail 3 mod 8 + next tail 7 mod 8
+```
+
+Checkpoint 117 adds the next concrete remainder:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16 + next tail 15 mod 16
+```
+
+## Level Names
+
+The first explicit level aliases are:
+
+```lean
+TailRemainderLevel0
+TailRemainderLevel1
+TailRemainderLevel2
+TailFallingLevel1
+TailFallingLevel2
+```
+
+They read:
+
+```text
+TailRemainderLevel0:
+  tail exact height 1
+
+TailFallingLevel1:
+  tail 3 mod 8
+
+TailRemainderLevel1:
+  tail 7 mod 8
+
+TailFallingLevel2:
+  tail 7 mod 16
+
+TailRemainderLevel2:
+  tail 15 mod 16
+```
+
+These are intentionally thin aliases.  They preserve the concrete residue
+definitions while making the tower grammar readable.
+
+## Level-2 Static Split
+
+New shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod32EqFifteenTail
+orbitWindowResidueCountMod32EqThirtyOneTail
+```
+
+The split theorem:
+
+```lean
+tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+```
+
+states:
+
+```text
+tail 15 mod 16
+  = tail 15 mod 32
+    + tail 31 mod 32
+```
+
+## Level-2 Recursion Edge
+
+The count-level recursion edge is:
+
+```lean
+tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+```
+
+It uses the existing pointwise transitions:
+
+```lean
+oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+```
+
+The reading is:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16
+     or
+     next tail 15 mod 16
+```
+
+This is the level-`2` analogue of the checkpoint 116 level-`1` recursion.
+
+## Alias Theorems
+
+The level-`1` alias theorems are:
+
+```lean
+tailRemainderLevel1_static_split
+tailRemainderLevel1_step_grammar
+```
+
+They make the grammar explicit:
+
+```text
+level 1 remainder
+  = level 2 falling + level 2 remainder
+
+level 1 remainder
+  -> next level 1 falling + next level 1 remainder
+```
+
+The second theorem deliberately stays at level `1` on the target side because
+the next tail window re-enters the visible `3 mod 8 / 7 mod 8` reservoir.
+
+## Pressure Entrance
+
+Checkpoint 117 adds the first local pressure entrance:
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+```
+
+The positivity theorem says:
+
+```text
+MoreThanHalf continuation pressure at depth 2
+  -> continuation mass at depth 2 is positive
+```
+
+The pressure-facing budget wrapper keeps the intended caller context visible:
+
+```text
+pressure at depth 2
+  -> use the delayed budget with a tail 7 mod 8 remainder
+```
+
+The pressure hypothesis is not needed by the inequality itself.  It is included
+to make the future API path explicit.
+
+## Current Tower State
+
+The concrete tower now has:
+
+```text
+level 0:
+  exact-height-one reservoir
+
+level 1:
+  3 mod 8 falls
+  7 mod 8 remains
+
+level 2:
+  7 mod 16 falls
+  15 mod 16 remains
+```
+
+The next likely step is:
+
+```text
+level 3:
+  15 mod 32 falls
+  31 mod 32 remains
+```
+
+The recommendation remains: add one concrete level at a time until the naming
+and index pattern stabilizes.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index a171bab9..b384b363 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -941,6 +941,79 @@ the delayed-peeling color pays into sumS;
 the continuing color is not discarded, but carried as the next remainder.
 ```
 
+## Level-2 Remainder
+
+Checkpoint 117 fixes the next concrete tower level.
+
+The level aliases are:
+
+```lean
+TailRemainderLevel0
+TailRemainderLevel1
+TailRemainderLevel2
+TailFallingLevel1
+TailFallingLevel2
+```
+
+They name the first visible pieces of the tower:
+
+```text
+level 0 remainder:
+  tail exact height 1
+
+level 1 falling:
+  tail 3 mod 8
+
+level 1 remainder:
+  tail 7 mod 8
+
+level 2 falling:
+  tail 7 mod 16
+
+level 2 remainder:
+  tail 15 mod 16
+```
+
+The level-`2` static split is:
+
+```lean
+orbitWindowResidueCountMod32EqFifteenTail
+orbitWindowResidueCountMod32EqThirtyOneTail
+tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+```
+
+The level-`2` recursion edge is:
+
+```lean
+tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+```
+
+So the continuing tower now has two concrete levels:
+
+```text
+tail 7 mod 8
+  -> next tail 3 mod 8 + next tail 7 mod 8
+
+tail 15 mod 16
+  -> next tail 7 mod 16 + next tail 15 mod 16
+```
+
+Checkpoint 117 also adds the first pressure-facing entrance:
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+```
+
+This does not yet prove that a pressure-heavy range feeds enough mass into the
+tower.  It records the local depth-`2` caller shape:
+
+```text
+MoreThanHalf continuation pressure at depth 2
+  -> positive continuation mass
+  -> delayed budget with explicit remainder
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 5ba050f0..d9c8f150 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -328,6 +328,19 @@ tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
 tailExactHeightOneReservoir_step_grammar
 tailExactHeightOneReservoir_budget_with_remainder
 sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+orbitWindowResidueCountMod32EqFifteenTail
+orbitWindowResidueCountMod32EqThirtyOneTail
+TailRemainderLevel0
+TailRemainderLevel1
+TailRemainderLevel2
+TailFallingLevel1
+TailFallingLevel2
+tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+tailRemainderLevel1_static_split
+tailRemainderLevel1_step_grammar
+tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-117.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-117.md
new file mode 100644
index 00000000..f3572541
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-117.md
@@ -0,0 +1,320 @@
+# Report Petal 117: Level-2 Remainder
+
+## Summary
+
+Checkpoint 117 extends the delayed-reservoir tower by one concrete level.
+
+Checkpoint 116 established:
+
+```text
+tail 7 mod 8
+  -> next tail 3 mod 8 + next tail 7 mod 8
+```
+
+Checkpoint 117 adds:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16 + next tail 15 mod 16
+```
+
+This makes the tower visible through level `2`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New shifted-tail mod-32 counts:
+
+```lean
+orbitWindowResidueCountMod32EqFifteenTail
+orbitWindowResidueCountMod32EqThirtyOneTail
+```
+
+Level aliases:
+
+```lean
+TailRemainderLevel0
+TailRemainderLevel1
+TailRemainderLevel2
+TailFallingLevel1
+TailFallingLevel2
+```
+
+Level-2 static split:
+
+```lean
+tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+```
+
+Level-alias theorems:
+
+```lean
+tailRemainderLevel1_static_split
+tailRemainderLevel1_step_grammar
+```
+
+Level-2 recursion edge:
+
+```lean
+tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+```
+
+Pressure entrance:
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+```
+
+## Experimental Results
+
+### Experiment A: mod32 split for `15 mod 16`
+
+Succeeded.
+
+```lean
+tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
+```
+
+Reading:
+
+```text
+tail 15 mod 16
+  = tail 15 mod 32
+    + tail 31 mod 32
+```
+
+### Experiment B: pointwise transition aliases
+
+The expected existing theorems were present and reusable:
+
+```lean
+oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+```
+
+No duplicate aliases were needed.
+
+### Experiment C: count-level recursion for `15 mod 16`
+
+Succeeded.
+
+```lean
+tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
+```
+
+Reading:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16
+     or
+     next tail 15 mod 16
+```
+
+### Experiment D-F: level API
+
+Succeeded.
+
+The level aliases make the first tower layers readable:
+
+```text
+level 0 remainder:
+  exact-height-one reservoir
+
+level 1 falling:
+  3 mod 8
+
+level 1 remainder:
+  7 mod 8
+
+level 2 falling:
+  7 mod 16
+
+level 2 remainder:
+  15 mod 16
+```
+
+The alias bridge:
+
+```lean
+tailRemainderLevel1_static_split
+```
+
+records:
+
+```text
+level 1 remainder = level 2 falling + level 2 remainder
+```
+
+The recursion alias:
+
+```lean
+tailRemainderLevel1_step_grammar
+```
+
+records:
+
+```text
+level 1 remainder
+  -> next level 1 falling + next level 1 remainder
+```
+
+### Experiment G: pressure at depth 2 gives positive continuation mass
+
+Succeeded.
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+```
+
+Since:
+
+```lean
+MoreThanHalf count total := total < 2 * count
+```
+
+Lean closes positivity with `omega`.
+
+### Experiment H: pressure-facing delayed budget wrapper
+
+Succeeded.
+
+```lean
+sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+```
+
+The pressure hypothesis is not used by the inequality itself.  It is kept as a
+caller-facing wrapper to document the intended route:
+
+```text
+pressure at depth 2
+  -> positive continuation mass
+  -> delayed budget with explicit remainder
+```
+
+## Mathematical Reading
+
+The tower is now concrete through level `2`:
+
+```text
+level 0:
+  exact-height-one reservoir
+
+level 1:
+  3 mod 8 falls
+  7 mod 8 remains
+
+level 2:
+  7 mod 16 falls
+  15 mod 16 remains
+```
+
+The important pattern is not collapse.  It is accounting:
+
+```text
+falling color:
+  charged to future height / sumS
+
+continuing color:
+  carried as an explicit next-level remainder
+```
+
+This is compatible with the checkpoint 116 budget-with-remainder philosophy.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-Level2Remainder-117.md
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
+### 1. Add level 3 concrete split
+
+Next split:
+
+```text
+tail 31 mod 32
+  = tail 31 mod 64
+    + tail 63 mod 64
+```
+
+Expected count names:
+
+```lean
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+```
+
+### 2. Add level 3 recursion edge
+
+Expected edge:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32 + next tail 31 mod 32
+```
+
+Existing pointwise theorems around:
+
+```lean
+oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+```
+
+should be reusable.
+
+### 3. Connect range pressure to depth-2 pressure
+
+The local pressure entrance is now available.  The next pressure-side bridge is
+probably a small specialization:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> MoreThanHalf continuationMass depth 2 retentionMass depth 2
+```
+
+Once this exists, the caller can enter the delayed-reservoir budget from the
+range-pressure vocabulary rather than a raw local `MoreThanHalf` hypothesis.
````
`````
