# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 8375ebe3e5d9803ab925e8e0e06b0a7da55f5c58

## Report

118 進めました。level 3 の tower 拡張と、range pressure から local depth 2 pressure への入口を両方固定できています。

主な追加は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:1066) です。

- `orbitWindowResidueCountMod64EqThirtyOneTail`
- `orbitWindowResidueCountMod64EqSixtyThreeTail`
- `TailRemainderLevel3`
- `TailFallingLevel3`
- `tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree`
- `tailRemainderLevel2_static_split`
- `tailRemainderLevel2_step_grammar`
- `tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne`
- `sourcePressureDepthTwo_of_pressureOnRange_two_one`
- `sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one`

tower はここまで通りました。

```text
level 1:
  3 mod 8 falls, 7 mod 8 remains

level 2:
  7 mod 16 falls, 15 mod 16 remains

level 3:
  15 mod 32 falls, 31 mod 32 remains
```

pressure 側も、`SourceContinuationPressureOnRange n k 2 1` から local `MoreThanHalf` を取り出し、depth 2 continuation mass の正性へ接続できました。

文書も同期済みです。

- [Collatz-Level3PressureEntrance-118.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md)
- [report-petal-118.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-118.md)
- README / Guide / Status 更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath.Collatz.Collatz2K26` 成功
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean` 該当なし
- `git diff --check` 問題なし

既存の unrelated warning として、`DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は継続しています。

## Review

## 1. 状況分析

checkpoint `118` は、二本の戦線が同時に進んだ良い回じゃ。

第一に、delayed-reservoir tower が **level 3** まで伸びた。

```text
level 1:
  3 mod 8 falls, 7 mod 8 remains

level 2:
  7 mod 16 falls, 15 mod 16 remains

level 3:
  15 mod 32 falls, 31 mod 32 remains
```

第二に、pressure 側から tower 入口へ入るための最初の bridge が入った。

```text
SourceContinuationPressureOnRange n k 2 1
  -> local MoreThanHalf pressure at depth 2
  -> positive continuation mass at depth 2
```

今回の報告でも、level 3 の tower 拡張と、range pressure から local depth 2 pressure への入口を両方固定できた、と整理されている。

これはかなり大きい。
ここまでで、tower は単なる residue 文法ではなく、pressure vocabulary から入れる有限会計装置になり始めた。

## 2. 今回の核心

今回の核心はこの二つ。

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
```

前者は tower の level 3 recursion edge。

```text
tail 31 mod 32
  -> next tail 15 mod 32
     or
     next tail 31 mod 32
```

後者は range pressure から local pressure を取り出す橋。

```text
SourceContinuationPressureOnRange n k 2 1
  -> MoreThanHalf continuation retention at depth 2
```

これで、二つの世界が初めてかなり近づいた。

```text
residue tower:
  falling / remainder の会計

pressure profile:
  MoreThanHalf continuation の検出
```

## 3. レビュー

## 3.1. level 3 の concrete extension は正しい

今回追加された、

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

および、

```lean
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
```

は、level 3 remainder の static split じゃ。

読みは、

```text
tail 31 mod 32
  = tail 31 mod 64
    + tail 63 mod 64
```

これは、これまでの pattern と完全に同型。

```text
7 mod 8
  = 7 mod 16 + 15 mod 16

15 mod 16
  = 15 mod 32 + 31 mod 32

31 mod 32
  = 31 mod 64 + 63 mod 64
```

この同型性が三段連続で通ったのは大きい。
ここまで来ると、低段の偶然ではなく、構造として見てよい段階に近づいている。

## 3.2. level 3 recursion edge が重要

今回の主砲は、

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

じゃ。

これは static split だけでなく、次 step での流れまで示す。

```text
31 mod 64
  -> next 15 mod 32

63 mod 64
  -> next 31 mod 32
```

したがって、

```text
31 mod 32
  -> next 15 mod 32 + next 31 mod 32
```

となる。

つまり、level 3 でも、

```text
remainder
  -> falling child
  -> continuing remainder
```

の構造が維持された。

これは delayed-reservoir tower の安定性確認としてかなり強い。

## 3.3. pressure entrance が実用的になった

今回追加された、

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
```

は、非常に実用的じゃ。

以前は local な仮定として、

```lean
MoreThanHalf
  (orbitWindowContinuationSiblingMassPow2 n k 2)
  (orbitWindowRetentionMassPow2 n k 2)
```

を直接渡す必要があった。

今回からは、

```lean
SourceContinuationPressureOnRange n k 2 1
```

という range-profile 側の言葉から取り出せる。

これは小さいが、本線に戻るうえで重要。

```text
pressure profile
  -> local tower entrance
```

の最初の実装ができた。

## 4. 数学的解説

いま見えている tower は、低位 bit が全部 \(1\) に寄っていく residual channel じゃ。

level 1 remainder は、

$$
7=2^3-1
$$

level 2 remainder は、

$$
15=2^4-1
$$

level 3 remainder は、

$$
31=2^5-1
$$

次の level 4 remainder は、おそらく、

$$
63=2^6-1
$$

になる。

一方、falling color は一段浅い all-ones color になる。

```text
level 1 falling:
  3 mod 8

level 2 falling:
  7 mod 16

level 3 falling:
  15 mod 32

level 4 falling:
  31 mod 64
```

つまり各段で、

```text
continuing remainder:
  2^m - 1 mod 2^m

falling child:
  2^(m-1) - 1 mod 2^m

next continuing child:
  2^m - 1 mod 2^(m+1)
```

のような形が見えている。

ただし、まだ一般定理にするには早い。
index shift と theorem 名が安定するまで、もう一段 level 4 を concrete に通すのが安全じゃ。

## 5. 一歩先ゆく推論

ここで見えてきた本質は、**remainder を消す証明ではなく、remainder を細くする証明**じゃ。

以前の期待は、

```text
pressure
  -> immediate peeling
  -> sumS lower bound
```

だった。

しかし現在の正しい構造は、

```text
pressure
  -> continuation mass
  -> delayed reservoir
  -> falling part is charged to sumS
  -> continuing part becomes thinner remainder
```

じゃ。

つまり残るものを捨てない。
残るものを次の level の residue class へ押し込む。

この residual class はどんどん細くなる。

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

有限 window \(k\) で見たとき、十分深い level まで押し込めば、remainder の占有数が制約される可能性がある。
ここが将来の大きな突破口になりそうじゃ。

## 6. 今回閉じたもの

今回閉じたものは次の五つ。

```text
1. level 3 residue count:
   31 mod 64 / 63 mod 64

2. level 3 static split:
   31 mod 32 = 31 mod 64 + 63 mod 64

3. level 3 recursion:
   31 mod 32 -> next 15 mod 32 + next 31 mod 32

4. level 2 alias:
   TailRemainderLevel2 の split / step grammar

5. range pressure entrance:
   SourceContinuationPressureOnRange n k 2 1
     -> local depth 2 pressure
     -> positive continuation mass
```

特に 5 が重要。
tower が pressure 側と初めて具体的に接続された。

## 7. まだ閉じていないもの

未完の本命は二つ。

```text
1. level 4 tower:
   63 mod 64 -> 31 mod 64 + 63 mod 64 at next window

2. longer pressure range:
   SourceContinuationPressureOnRange n k r len
     -> useful local tower-entry opportunities
```

現在の pressure entrance は `r = 2`, `len = 1` の特殊ケース。
次は、任意の \(j < len\) に対して local pressure を取り出す wrapper が欲しい。

既に内部 theorem として、

```lean
moreThanHalf_of_sourceContinuationPressure
```

が使われているので、これに意味名 alias を足すのがよい。

## 8. 次の指示

## 8.1. level 4 concrete split

次は `63 mod 64` を `128` で分ける。

```lean
noncomputable def orbitWindowResidueCountMod128EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 63))

noncomputable def orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 127))
```

split theorem。

```lean
theorem tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod64EqSixtyThreeTail n k =
      orbitWindowResidueCountMod128EqSixtyThreeTail n k +
        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k := by
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h63 : oddOrbitLabel n (k + 1) % 128 = 63
      · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        have hnot127 : oddOrbitLabel n (k + 1) % 128 ≠ 127 := by
          omega
        simp [ih, hmod64, h63, hnot127, Nat.add_assoc, Nat.add_comm]
      · by_cases h127 : oddOrbitLabel n (k + 1) % 128 = 127
        · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
            omega
          simp [ih, hmod64, h127, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod64 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
            intro hmod64
            have hchild :
                oddOrbitLabel n (k + 1) % 128 = 63 ∨
                  oddOrbitLabel n (k + 1) % 128 = 127 := by
              omega
            cases hchild with
            | inl h =>
                exact h63 h
            | inr h =>
                exact h127 h
          simp [ih, hnotMod64, h63, h127]
```

## 8.2. level 4 recursion edge

報告では、次の既存 theorem が候補として挙がっている。

```lean
oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
oddOrbitLabel_succ_mod_sixtyfour_eq_sixtythree_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
```

これを使って、

```lean
theorem tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod64EqSixtyThreeTail n k ≤
      orbitWindowResidueCountMod64EqThirtyOneTail n (k + 1) +
        orbitWindowResidueCountMod64EqSixtyThreeTail n (k + 1) := by
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  unfold orbitWindowResidueCountMod64EqThirtyOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      -- level 3 recursion edge と同じ構造
      -- 63 mod 128 -> next 31 mod 64
      -- 127 mod 128 -> next 63 mod 64
      sorry
```

ここは theorem 名が長いので、まず既存 theorem の有無を検索した方がよい。

```text
rg "onehundredtwentyeight" DkMath/Collatz/PetalBridge.lean
rg "sixtythree" DkMath/Collatz/PetalBridge.lean
rg "sixtyfour_eq" DkMath/Collatz/PetalBridge.lean
```

## 8.3. level 4 alias

```lean
def TailRemainderLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqSixtyThreeTail n k

def TailFallingLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqThirtyOneTail n k
```

alias theorem。

```lean
theorem tailRemainderLevel3_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k =
      TailFallingLevel4 n k + TailRemainderLevel4 n k := by
  unfold TailRemainderLevel3 TailFallingLevel4 TailRemainderLevel4
  exact tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree n k
```

```lean
theorem tailRemainderLevel3_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k ≤
      TailFallingLevel3 n (k + 1) + TailRemainderLevel3 n (k + 1) := by
  unfold TailRemainderLevel3 TailFallingLevel3
  exact tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne n k
```

注意点は前回と同じ。
`static_split` は次 level の falling / remainder を使う。
`step_grammar` は同じ level の next-window falling / remainder に戻る。

## 9. pressure range 側への次の橋

今回 `r=2`, `len=1` は通った。
次は generic wrapper を作るのがよい。

```lean
theorem sourcePressureAtDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) := by
  exact moreThanHalf_of_sourceContinuationPressure n k r len j h hj
```

これで以後は内部名を直接使わず、

```text
pressureOnRange から local pressure を取り出す
```

という意味名で書ける。

次に、local pressure から continuation mass positive の generic 版。

```lean
theorem sourceContinuationMass_pos_of_localPressure
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold MoreThanHalf at h
  omega
```

そして合成。

```lean
theorem sourceContinuationMass_pos_of_pressureOnRange_at
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  sourceContinuationMass_pos_of_localPressure n k (r + j)
    (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)
```

これは今後かなり使える。

## 10. 一歩先の次の一手

level 4 が通ったら、次は **generic 化の予備段階** に入れる。

いきなり完全一般化ではなく、まず有限 list 的な family を作る。

```lean
def TailRemainderLevel (L : ℕ) (n : OddNat) (k : ℕ) : ℕ :=
  match L with
  | 0 => TailRemainderLevel0 n k
  | 1 => TailRemainderLevel1 n k
  | 2 => TailRemainderLevel2 n k
  | 3 => TailRemainderLevel3 n k
  | 4 => TailRemainderLevel4 n k
  | _ => 0
```

これは一般定理用ではなく、まず API の見通しを作るための仮置き。
`_ => 0` は不自然だが、有限段検証用なら一時的に使える。

もう少し安全にするなら、一般定義はまだ入れず、docs に pattern として書くだけでもよい。

賢狼の推奨は、**level 4 までは concrete に通す**。
その後に、`TailRemainderLevel` の有限 wrapper を検討する。

## 11. さらに先の推論：remainder をどう殺すか

tower の本質は、

```text
mass <= sumS contribution + remainder
```

じゃ。

level が深くなるほど remainder は細い residue class へ入る。

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
```

ここで将来的に欲しいのは、

```text
finite window k に対して、
十分深い all-ones residue class の count は小さい
```

という補題じゃ。

例えば、一般論として、

```text
mod 2^m の特定 residue class の count は高々 window length
```

は自明すぎる。
欲しいのはもう少し強く、

```text
tail labels が pairwise separated なら、
細い residue class に入り続ける個数には制約がある
```

という方向かもしれない。

既に `OddOrbitLabelsPairwiseSeparated` や `OrbitWindowSeparated` 系があるなら、ここに戻る可能性がある。

つまり、tower の先はこうなる。

```text
pressure mass
  -> sumS contribution + deep remainder

deep remainder
  -> separation / residue sparsity で制約

therefore pressure mass must pay into sumS
```

これがかなり本命に見える。

## 12. 賢狼が試して欲しい実験補題

## 実験 A: generic pressure extraction wrapper

```lean
theorem sourcePressureAtDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) := by
  exact moreThanHalf_of_sourceContinuationPressure n k r len j h hj
```

## 実験 B: generic local pressure gives positive continuation mass

```lean
theorem sourceContinuationMass_pos_of_localPressure
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold MoreThanHalf at h
  omega
```

## 実験 C: pressure range gives positive continuation mass at any depth in range

```lean
theorem sourceContinuationMass_pos_of_pressureOnRange_at
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  sourceContinuationMass_pos_of_localPressure n k (r + j)
    (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)
```

## 実験 D: level 4 residue count

```lean
noncomputable def orbitWindowResidueCountMod128EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 63))

noncomputable def orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 127))
```

## 実験 E: level 4 static split

```lean
theorem tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod64EqSixtyThreeTail n k =
      orbitWindowResidueCountMod128EqSixtyThreeTail n k +
        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k := by
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h63 : oddOrbitLabel n (k + 1) % 128 = 63
      · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        have hnot127 : oddOrbitLabel n (k + 1) % 128 ≠ 127 := by
          omega
        simp [ih, hmod64, h63, hnot127, Nat.add_assoc, Nat.add_comm]
      · by_cases h127 : oddOrbitLabel n (k + 1) % 128 = 127
        · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
            omega
          simp [ih, hmod64, h127, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod64 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
            intro hmod64
            have hchild :
                oddOrbitLabel n (k + 1) % 128 = 63 ∨
                  oddOrbitLabel n (k + 1) % 128 = 127 := by
              omega
            cases hchild with
            | inl h =>
                exact h63 h
            | inr h =>
                exact h127 h
          simp [ih, hnotMod64, h63, h127]
```

## 実験 F: level 4 aliases

```lean
def TailRemainderLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqSixtyThreeTail n k

def TailFallingLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqThirtyOneTail n k
```

## 実験 G: level 3 static split alias

```lean
theorem tailRemainderLevel3_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k =
      TailFallingLevel4 n k + TailRemainderLevel4 n k := by
  unfold TailRemainderLevel3 TailFallingLevel4 TailRemainderLevel4
  exact tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree n k
```

## 実験 H: level 3 step grammar alias

```lean
theorem tailRemainderLevel3_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k ≤
      TailFallingLevel3 n (k + 1) + TailRemainderLevel3 n (k + 1) := by
  unfold TailRemainderLevel3 TailFallingLevel3
  exact tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne n k
```

## 13. 次コミットの推奨順

```text
1. generic pressure extraction wrapper を追加

2. generic local pressure -> positive continuation mass を追加

3. pressureOnRange_at -> continuation mass positive を追加

4. level 4 residue counts:
   63 mod 128 / 127 mod 128

5. level 4 static split

6. 既存 pointwise transition theorem を検索

7. level 4 recursion edge を試す

8. TailRemainderLevel4 / TailFallingLevel4 alias

9. level 3 static split / step grammar alias

10. docs:
    Level3PressureEntrance から Level4AndGenericPressureEntrance へ接続
```

## 14. 総括

checkpoint `118` はかなり良い。

tower は level 3 まで伸びた。

```text
7 mod 8
15 mod 16
31 mod 32
```

そして次は、

```text
63 mod 64
```

へ進む。

同時に、pressure range から local tower entrance へ入る橋もできた。

```text
SourceContinuationPressureOnRange n k 2 1
  -> depth 2 local pressure
  -> continuation mass positive
```

ここから先は二つの道を並行するのがよい。

```text
tower 側:
  level 4 まで concrete に伸ばす

pressure 側:
  任意 range の local depth へ取り出す wrapper を整備する
```

この二つが合わさると、いよいよ

```text
pressure-heavy window
  -> many local tower-entry opportunities
  -> sumS contribution + deep remainder
```

という有限会計に入れる。
ここはかなり面白い局面じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8f4731b6..0572f272 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1020,6 +1020,28 @@ noncomputable def orbitWindowResidueCountMod32EqThirtyOneTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 31))
 
+/--
+Number of shifted-tail labels in residue class `31 mod 64`.
+
+This is the delayed-peeling child inside the shifted-tail `31 mod 32`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod64EqThirtyOneTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 31))
+
+/--
+Number of shifted-tail labels in residue class `63 mod 64`.
+
+This is the continuing child inside the shifted-tail `31 mod 32` continuing
+color.
+-/
+noncomputable def orbitWindowResidueCountMod64EqSixtyThreeTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 63))
+
 /-- Level `0` tail remainder: the whole shifted-tail exact-height-one reservoir. -/
 noncomputable def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowHeightCountEqTail n k 1
@@ -1040,6 +1062,14 @@ noncomputable def TailFallingLevel1 (n : OddNat) (k : ℕ) : ℕ :=
 noncomputable def TailFallingLevel2 (n : OddNat) (k : ℕ) : ℕ :=
   orbitWindowResidueCountMod16EqSevenTail n k
 
+/-- Level `3` tail remainder: the shifted-tail `31 mod 32` continuing color. -/
+noncomputable def TailRemainderLevel3 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod32EqThirtyOneTail n k
+
+/-- Level `3` falling color: the shifted-tail `15 mod 32` delayed-peeling color. -/
+noncomputable def TailFallingLevel3 (n : OddNat) (k : ℕ) : ℕ :=
+  orbitWindowResidueCountMod32EqFifteenTail n k
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -4094,6 +4124,58 @@ theorem tailRemainderLevel1_static_split
   unfold TailRemainderLevel1 TailFallingLevel2 TailRemainderLevel2
   exact tailResidueCountMod8EqSeven_split_mod16_seven_fifteen n k
 
+/--
+The shifted-tail `31 mod 32` continuing color splits into its two children
+modulo `64`: the delayed-peeling child `31 mod 64` and the continuing child
+`63 mod 64`.
+-/
+theorem tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod32EqThirtyOneTail n k =
+      orbitWindowResidueCountMod64EqThirtyOneTail n k +
+        orbitWindowResidueCountMod64EqSixtyThreeTail n k := by
+  unfold orbitWindowResidueCountMod32EqThirtyOneTail
+  unfold orbitWindowResidueCountMod64EqThirtyOneTail
+  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      by_cases h31 : oddOrbitLabel n (k + 1) % 64 = 31
+      · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
+          omega
+        simp [ih, hmod32, h31, Nat.add_assoc, Nat.add_comm]
+      · by_cases h63 : oddOrbitLabel n (k + 1) % 64 = 63
+        · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
+            omega
+          simp [ih, hmod32, h63, Nat.add_comm, Nat.add_left_comm]
+        · have hnotMod32 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
+            intro hmod32
+            have hchild :
+                oddOrbitLabel n (k + 1) % 64 = 31 ∨
+                  oddOrbitLabel n (k + 1) % 64 = 63 := by
+              omega
+            cases hchild with
+            | inl h =>
+                exact h31 h
+            | inr h =>
+                exact h63 h
+          simp [ih, hnotMod32, h31, h63]
+
+/--
+Level-alias version of the level-`2` static split.
+
+The level-`2` remainder is the sum of the level-`3` falling color and the
+level-`3` remainder.
+-/
+theorem tailRemainderLevel2_static_split
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel2 n k =
+      TailFallingLevel3 n k + TailRemainderLevel3 n k := by
+  unfold TailRemainderLevel2 TailFallingLevel3 TailRemainderLevel3
+  exact tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne n k
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4535,6 +4617,75 @@ theorem tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
           · simp [hsource, htargetSeven, htargetFifteen]
             omega
 
+/--
+Level-alias version of the level-`2` recursion edge.
+
+The level-`2` remainder re-enters the next level-`2` falling/remainder split.
+-/
+theorem tailRemainderLevel2_step_grammar
+    (n : OddNat) (k : ℕ) :
+    TailRemainderLevel2 n k ≤
+      TailFallingLevel2 n (k + 1) + TailRemainderLevel2 n (k + 1) := by
+  unfold TailRemainderLevel2 TailFallingLevel2
+  exact tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen n k
+
+/--
+The shifted-tail `31 mod 32` continuing color enters the next shifted-tail
+`15 mod 32 / 31 mod 32` split.
+
+This is the level-`3` recursion edge of the delayed-reservoir tower.
+-/
+theorem tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod32EqThirtyOneTail n k ≤
+      orbitWindowResidueCountMod32EqFifteenTail n (k + 1) +
+        orbitWindowResidueCountMod32EqThirtyOneTail n (k + 1) := by
+  unfold orbitWindowResidueCountMod32EqThirtyOneTail
+  unfold orbitWindowResidueCountMod32EqFifteenTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransitionFifteen :
+          oddOrbitLabel n (k + 1) % 64 = 31 →
+            oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
+        oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+          n (k + 1)
+      have htransitionThirtyOne :
+          oddOrbitLabel n (k + 1) % 64 = 63 →
+            oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
+        oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+          n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 32 = 31
+      · have hchild :
+            oddOrbitLabel n (k + 1) % 64 = 31 ∨
+              oddOrbitLabel n (k + 1) % 64 = 63 := by
+          omega
+        cases hchild with
+        | inl h31 =>
+            have htargetFifteen :
+                oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
+              htransitionFifteen h31
+            simp [hsource, htargetFifteen]
+            omega
+        | inr h63 =>
+            have htargetThirtyOne :
+                oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
+              htransitionThirtyOne h63
+            simp [hsource, htargetThirtyOne]
+            omega
+      · by_cases htargetFifteen :
+            oddOrbitLabel n ((k + 1) + 1) % 32 = 15
+        · simp [hsource, htargetFifteen]
+          omega
+        · by_cases htargetThirtyOne :
+            oddOrbitLabel n ((k + 1) + 1) % 32 = 31
+          · simp [hsource, htargetThirtyOne]
+            omega
+          · simp [hsource, htargetFifteen, htargetThirtyOne]
+            omega
+
 /--
 One-step grammar for the shifted-tail exact-height-one reservoir.
 
@@ -5758,6 +5909,29 @@ theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
   unfold MoreThanHalf at h
   omega
 
+/--
+Extract local depth-two source pressure from the one-depth range pressure
+profile beginning at depth `2`.
+-/
+theorem sourcePressureDepthTwo_of_pressureOnRange_two_one
+    (n : OddNat) (k : ℕ)
+    (h : SourceContinuationPressureOnRange n k 2 1) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k 2)
+      (orbitWindowRetentionMassPow2 n k 2) := by
+  simpa using moreThanHalf_of_sourceContinuationPressure n k 2 1 0 h (by omega)
+
+/--
+One-depth range pressure at depth `2` forces positive depth-two continuation
+mass.
+-/
+theorem sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+    (n : OddNat) (k : ℕ)
+    (h : SourceContinuationPressureOnRange n k 2 1) :
+    0 < orbitWindowContinuationSiblingMassPow2 n k 2 :=
+  sourceContinuationMass_depth_two_pos_of_pressure_depth_two n k
+    (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)
+
 /--
 Pressure-facing wrapper for the depth-two delayed-reservoir budget.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 327fc53e..c7448325 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -152,6 +152,7 @@ docs/Collatz-TailFacingHeightBridge-114.md
 docs/Collatz-RecoveryDelayedBranch-115.md
 docs/Collatz-DelayedReservoirTower-116.md
 docs/Collatz-Level2Remainder-117.md
+docs/Collatz-Level3PressureEntrance-118.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md
new file mode 100644
index 00000000..05cc2271
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md
@@ -0,0 +1,149 @@
+# Collatz Level-3 And Pressure Entrance 118
+
+Checkpoint 118 has two roles.
+
+First, it extends the delayed-reservoir tower to level `3`.
+Second, it adds the first bridge from one-depth range pressure into the local
+depth-`2` delayed-reservoir entrance.
+
+## Level-3 Tower Extension
+
+Checkpoint 117 fixed level `2`:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16 + next tail 15 mod 16
+```
+
+Checkpoint 118 adds level `3`:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32 + next tail 31 mod 32
+```
+
+New shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+```
+
+Static split:
+
+```lean
+tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+```
+
+Reading:
+
+```text
+tail 31 mod 32
+  = tail 31 mod 64
+    + tail 63 mod 64
+```
+
+Recursion edge:
+
+```lean
+tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+```
+
+Reading:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32
+     or
+     next tail 31 mod 32
+```
+
+## Level Aliases
+
+New aliases:
+
+```lean
+TailRemainderLevel3
+TailFallingLevel3
+```
+
+New alias theorems:
+
+```lean
+tailRemainderLevel2_static_split
+tailRemainderLevel2_step_grammar
+```
+
+They say:
+
+```text
+level 2 remainder
+  = level 3 falling + level 3 remainder
+
+level 2 remainder
+  -> next level 2 falling + next level 2 remainder
+```
+
+The target of the step theorem remains level `2` because the next shifted-tail
+window re-enters the visible `15 mod 32 / 31 mod 32` split.
+
+## Range Pressure Entrance
+
+Checkpoint 117 added a local pressure entrance:
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+```
+
+Checkpoint 118 adds the one-depth range-pressure extraction:
+
+```lean
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+```
+
+This gives the caller route:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> local MoreThanHalf pressure at depth 2
+  -> positive continuation mass at depth 2
+```
+
+This still does not prove that a long pressure-heavy range feeds enough mass
+into the tower.  It closes the first small interface from the range vocabulary
+to the local tower entrance.
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
+```
+
+The next likely concrete extension is:
+
+```text
+level 4:
+  31 mod 64 falls
+  63 mod 64 remains
+```
+
+The next pressure-side extension is:
+
+```text
+SourceContinuationPressureOnRange n k 2 len
+  -> extract useful local pressure at one or more depths
+  -> enter delayed-reservoir budgets
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index b384b363..ebbda1e9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1014,6 +1014,65 @@ MoreThanHalf continuation pressure at depth 2
   -> delayed budget with explicit remainder
 ```
 
+## Level-3 And Range Pressure Entrance
+
+Checkpoint 118 extends the concrete tower to level `3` and adds the first
+range-pressure entrance.
+
+The level-`3` residue counts are:
+
+```lean
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+```
+
+The static split is:
+
+```lean
+tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+```
+
+with reading:
+
+```text
+tail 31 mod 32
+  = tail 31 mod 64
+    + tail 63 mod 64
+```
+
+The level-`3` recursion edge is:
+
+```lean
+tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+```
+
+so the tower now has:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32 + next tail 31 mod 32
+```
+
+The level aliases are:
+
+```lean
+TailRemainderLevel3
+TailFallingLevel3
+tailRemainderLevel2_static_split
+tailRemainderLevel2_step_grammar
+```
+
+Checkpoint 118 also connects one-depth range pressure to local depth-`2`
+pressure:
+
+```lean
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+```
+
+This is the first bridge from the range profile vocabulary to the delayed
+reservoir budget entrance.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d9c8f150..7fe2834a 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -341,6 +341,16 @@ tailRemainderLevel1_step_grammar
 tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
 sourceContinuationMass_depth_two_pos_of_pressure_depth_two
 sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+TailRemainderLevel3
+TailFallingLevel3
+tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+tailRemainderLevel2_static_split
+tailRemainderLevel2_step_grammar
+tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-118.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-118.md
new file mode 100644
index 00000000..8724aa8d
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-118.md
@@ -0,0 +1,300 @@
+# Report Petal 118: Level-3 And Pressure Entrance
+
+## Summary
+
+Checkpoint 118 advances two fronts.
+
+First, it extends the delayed-reservoir tower to level `3`:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32 + next tail 31 mod 32
+```
+
+Second, it connects one-depth range pressure to local depth-`2` pressure:
+
+```text
+SourceContinuationPressureOnRange n k 2 1
+  -> local MoreThanHalf pressure at depth 2
+  -> positive continuation mass at depth 2
+```
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New level-`3` shifted-tail counts:
+
+```lean
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+```
+
+New aliases:
+
+```lean
+TailRemainderLevel3
+TailFallingLevel3
+```
+
+Level-`3` static split:
+
+```lean
+tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+```
+
+Level-`2` alias theorems:
+
+```lean
+tailRemainderLevel2_static_split
+tailRemainderLevel2_step_grammar
+```
+
+Level-`3` recursion edge:
+
+```lean
+tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+```
+
+Range-pressure extraction:
+
+```lean
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+```
+
+## Experimental Results
+
+### Experiment A: level-3 residue counts
+
+Succeeded.
+
+```lean
+orbitWindowResidueCountMod64EqThirtyOneTail
+orbitWindowResidueCountMod64EqSixtyThreeTail
+```
+
+### Experiment B: level-3 static split
+
+Succeeded.
+
+```lean
+tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
+```
+
+Reading:
+
+```text
+tail 31 mod 32
+  = tail 31 mod 64
+    + tail 63 mod 64
+```
+
+### Experiment C: level-3 recursion edge
+
+Succeeded.
+
+```lean
+tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
+```
+
+It uses the existing pointwise transitions:
+
+```lean
+oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
+oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
+```
+
+Reading:
+
+```text
+tail 31 mod 32
+  -> next tail 15 mod 32
+     or
+     next tail 31 mod 32
+```
+
+### Experiment D-F: level-3 aliases
+
+Succeeded.
+
+```lean
+TailRemainderLevel3
+TailFallingLevel3
+tailRemainderLevel2_static_split
+tailRemainderLevel2_step_grammar
+```
+
+These keep the concrete tower readable:
+
+```text
+level 2 remainder
+  = level 3 falling + level 3 remainder
+
+level 2 remainder
+  -> next level 2 falling + next level 2 remainder
+```
+
+### Experiment G: one-depth range pressure to local pressure
+
+Succeeded.
+
+```lean
+sourcePressureDepthTwo_of_pressureOnRange_two_one
+```
+
+This uses the existing extractor:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+```
+
+with `r = 2`, `len = 1`, and `j = 0`.
+
+### Experiment H: one-depth range pressure to positive continuation mass
+
+Succeeded.
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
+```
+
+This composes the range extraction with:
+
+```lean
+sourceContinuationMass_depth_two_pos_of_pressure_depth_two
+```
+
+## Mathematical Reading
+
+The delayed-reservoir tower now reaches:
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
+```
+
+The pressure side now has its first one-depth connection:
+
+```text
+range pressure over [2, 3)
+  -> local pressure at depth 2
+  -> positive source continuation mass
+```
+
+This is still local.  The next pressure task is to extract useful local
+pressure from longer ranges, or to package a range profile as a finite list of
+local tower-entry opportunities.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-Level3PressureEntrance-118.md
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
+### 1. Add level 4 concrete split
+
+Expected next split:
+
+```text
+tail 63 mod 64
+  = tail 63 mod 128
+    + tail 127 mod 128
+```
+
+Expected existing pointwise transitions are around:
+
+```lean
+oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
+oddOrbitLabel_succ_mod_sixtyfour_eq_sixtythree_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
+```
+
+If these names are absent, add pointwise aliases first.
+
+### 2. Add longer range pressure extractors
+
+The next pressure-facing theorem should extract a local pressure statement from
+a longer range:
+
+```text
+SourceContinuationPressureOnRange n k r len
+  and j < len
+  -> local MoreThanHalf at depth r+j
+```
+
+The generic extractor already exists as:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+```
+
+Useful next wrappers may specialize it to common entry depths such as `2`,
+`3`, or a one-depth range beginning at a chosen depth.
+
+### 3. Start finite tower-entry accounting
+
+A future theorem should connect:
+
+```text
+range pressure count
+```
+
+to:
+
+```text
+number of local delayed-reservoir budget opportunities
+```
+
+This is the point where the tower becomes more than a residue grammar: it
+becomes a finite accounting surface for pressure-heavy windows.
````
`````
