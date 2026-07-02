# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 9e7b7f93241f3e9db164355c75abe441cd67d301

## Report

116 進めました。`7 mod 8` continuing color を次の reservoir へ戻す再帰辺まで Lean で固定できています。

主な追加は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:3967) です。

- `orbitWindowResidueCountMod16EqSevenTail`
- `orbitWindowResidueCountMod16EqFifteenTail`
- `tailResidueCountMod8EqSeven_split_mod16_seven_fifteen`
- `tailMod8Seven_le_nextTailHeightCountEq_one`
- `tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven`
- `tailExactHeightOneReservoir_step_grammar`
- `tailExactHeightOneReservoir_budget_with_remainder`
- `sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder`

今回の要点は、

```text
tail 7 mod 8
  -> next tail exact height 1
  -> next tail 3 mod 8 + next tail 7 mod 8
```

が通ったことです。つまり delayed-reservoir tower の最初の再帰辺ができました。さらに、`sumS` に落ちる分と `7 mod 8` として残る分を分ける remainder budget も通っています。

文書も同期しました。

- [Collatz-DelayedReservoirTower-116.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md)
- [report-petal-116.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-116.md)
- README / Guide / Status も更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath.Collatz.Collatz2K26` 成功
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean` 該当なし
- `git diff --check` 問題なし

既存の unrelated warning として、`DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は継続しています。

## Review

## 1. 状況分析

checkpoint `116` は、かなり大きい。
前回 `115` で見えた

```text
tail exact height 1
  = tail 3 mod 8
    + tail 7 mod 8
```

という reservoir 分解から、今回は **continuing color が次の reservoir へ戻る再帰辺** まで Lean で固定できている。報告でも、`tail 7 mod 8 -> next tail exact height 1 -> next tail 3 mod 8 + next tail 7 mod 8` が通り、delayed-reservoir tower の最初の再帰辺ができた、と明記されている。

今回の到達点は、もはや単なる局所 residue bridge ではなく、**会計モデル** じゃ。

```text
落ちる色:
  sumS に課金される

残る色:
  remainder として次の reservoir へ送られる
```

ここまで来たことで、Collatz.PetalBridge は「即時降下を見る分類器」から、「遅延降下を remainder 付きで追跡する有限会計エンジン」へ変わり始めた。

## 2. 今回の核心

今回の核心はこの二つ。

```lean
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

```lean
tailExactHeightOneReservoir_budget_with_remainder
```

前者は、continuing color の再帰辺。

```text
tail 7 mod 8
  -> next tail 3 mod 8
     +
     next tail 7 mod 8
```

後者は、落ちる分と残る分を同時に扱う budget theorem。

```text
base layer + current exact-height-one reservoir
  <= next accumulated sumS
     + current 7 mod 8 continuing remainder
```

これは非常に重要じゃ。
「全部落ちる」と嘘をつかない。
落ちた分は `sumS` に入り、落ちなかった分は remainder として明示的に残す。

この設計は強い。

## 3. レビュー

## 3.1. mod16 split は正しい一手

今回追加された、

```lean
orbitWindowResidueCountMod16EqSevenTail
orbitWindowResidueCountMod16EqFifteenTail
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

は、tower の次段準備として正しい。

`7 mod 8` は continuing color だった。
それを mod `16` で見ると、

```text
7 mod 8
  = 7 mod 16
    +
    15 mod 16
```

になる。

ここで重要なのは、`7 mod 16` と `15 mod 16` は同じ continuing residue ではないことじゃ。

実際には、

```text
7 mod 16:
  次に 3 mod 8 側へ入る delayed-peeling child

15 mod 16:
  次に 7 mod 8 側へ残る continuing child
```

という役割分担になる。

つまり、解像度を上げると、continuing color の中からまた falling child が抽出される。

## 3.2. `tailMod8Seven_le_nextTailHeightCountEq_one` は tower の再帰辺

```lean
tailMod8Seven_le_nextTailHeightCountEq_one
```

これは、

```text
tail 7 mod 8
  -> next tail exact height 1
```

を count level へ持ち上げている。

これがあるから、次の split

```lean
tailHeightCountEq_one_split_mod8_three_seven
```

を再利用できる。

そして、

```lean
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

が得られる。

この流れは非常に良い。
新しい分解を作るだけでなく、既存の reservoir split を再利用している。

```text
continuing color
  -> next reservoir
  -> same split rule
```

この形が見えた時点で、これは本当に tower になり始めた。

## 3.3. `tailExactHeightOneReservoir_step_grammar` は重要な抽象化

```lean
tailExactHeightOneReservoir_step_grammar
```

これは、現在の exact-height-one reservoir が、次 step では

```text
next height >= 2
```

または

```text
next exact height 1
```

へ送られる、という count-level grammar じゃ。

式としては、

```text
current reservoir
  <= next falling side + next continuing reservoir
```

になっている。

これは今後、remainder tower を一般化する前の中核補題になる。
ただし注意点として、これは injection や個別対応を主張しているわけではない。count inequality として安全に留めている。ここが良い。

## 3.4. budget with remainder が今回最大の収穫

```lean
tailExactHeightOneReservoir_budget_with_remainder
```

と、

```lean
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

は、今回の一番の成果じゃ。

特に後者はかなり使える。

```text
base layer + source continuation depth 2
  <= next sumS
     + tail 7 mod 8 remainder
```

これは、以前の誤った期待

```text
source continuation mass
  -> 全部 extra peeling
```

ではなく、

```text
source continuation mass
  -> 落ちる分は sumS
  -> 残る分は tail 7 mod 8 remainder
```

という正しい会計になっている。

これなら将来、remainder をさらに分解して、少しずつ `sumS` へ移していける。

## 4. 数学的解説

今回の構造は、奇数 (q) の低位 bit で見ると非常に分かりやすい。

まず exact height 1 は、

$$
q\equiv 3\pmod 4
$$

であり、mod (8) では、

$$
q\equiv 3\pmod 8
$$

または、

$$
q\equiv 7\pmod 8
$$

に分かれる。

`3 mod 8` は、次 step で (1 \mod 4) に入り、height (\ge 2) になる。
一方、`7 mod 8` は、次 step でも exact height 1 に残る。

そして今回、`7 mod 8` をさらに mod (16) で分けた。

$$
7\pmod 8
$$

は、

$$
7\pmod {16}
$$

または、

$$
15\pmod {16}
$$

に分かれる。

このうち `7 mod 16` は次 step で `3 mod 8` 側へ移る。
`15 mod 16` は次 step でも `7 mod 8` 側に残る。

つまり pattern はこうじゃ。

```text
3 mod 8:
  falling now

7 mod 8:
  continuing now

7 mod 16:
  falling after one more refinement

15 mod 16:
  continuing after one more refinement
```

もっと一般化すると、continuing color はだんだん

```text
2^m - 1 mod 2^m
```

のような「全部 1 の低位 bit」に寄っていく。

これはまさに、一色線の直感と重なる。

## 5. 一歩先ゆく推論

ここで見えてきたのは、**remainder を消す証明**ではなく、**remainder を追跡する証明**じゃ。

直接、

```text
全部 sumS に落ちる
```

を狙うのではない。

正しくは、

```text
一部は sumS に落ちる
残りはより細い continuing remainder になる
```

を繰り返す。

つまり、次のような階段構造になる。

```text
level 0 remainder:
  exact-height-one reservoir

level 1 remainder:
  tail 7 mod 8

level 2 remainder:
  tail 15 mod 16

level 3 remainder:
  tail 31 mod 32
```

そして各 level で、

```text
remainder
  -> falling child
  -> next remainder
```

が起きる。

これができれば、Collatz の局所会計は次のような形になる。

```text
initial mass
  <= accumulated sumS contribution
     +
     deepest continuing remainder
```

この deepest remainder をどう評価するかが次の課題になる。

有限窓なら、remainder を捨てずに持ち続けるだけでも意味がある。
なぜなら、各 level で少なくとも「落ちる可能性のある色」が抽出されるからじゃ。

## 6. Gnomon / 一色線との接続

今回の tower は、Gnomon 一色線の直感にかなり綺麗に対応する。

Gnomon 層は最初、多色に見える。
それを (2^n) の格子ラインで見ると、色が分かれる。

```text
3 mod 8:
  落ちる色

7 mod 8:
  残る色
```

残る色をさらに細かく見ると、

```text
7 mod 16:
  落ちる色

15 mod 16:
  残る色
```

さらに、

```text
15 mod 32:
  ...
31 mod 32:
  ...
```

と続く。

つまり、一色線へ向かうとは、

```text
残る色をさらに解像度上げして、
落ちる色を抽出し続ける
```

ことじゃ。

これは、以前の「色数が減る」よりもさらに精密な見方になる。

```text
色数が減る
```

というより、

```text
落ちる色を会計に入れ、
残る色だけを次の解像度へ送る
```

という処理じゃ。

## 7. 今回閉じたもの

今回閉じたものは、かなり多い。

```text
1. tail 7 mod 8 の mod16 split

2. tail 7 mod 8 が next exact-height-one reservoir に戻ること

3. tail 7 mod 8 が next 3 mod 8 + next 7 mod 8 へ入ること

4. current exact-height-one reservoir の one-step grammar

5. exact-height-one reservoir の budget-with-remainder

6. source continuation depth 2 の budget-with-tailSeven-remainder
```

これにより、delayed-reservoir tower の最初の再帰辺が本当に定理になった。

## 8. まだ閉じていないもの

まだ閉じていないのは、次の二つ。

```text
1. tail 15 mod 16 の次段 split / recursion

2. pressure-heavy range から、この reservoir tower へ十分な mass を送る橋
```

今回の `sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder` は、source continuation mass depth `2` についてはかなり良い。

ただし、pressure-heavy がどれだけ depth `2` continuation mass を保証するかはまだ別問題じゃ。

つまり今後は、

```text
pressure-heavy
  -> source continuation mass at useful depth
  -> delayed reservoir budget
```

という接続が必要になる。

この「pressure-heavy から useful depth への射影」が本命の一つになる。

## 9. 次の指示

次 checkpoint は、二本立てがよい。

## 9.1. 第一候補：level 2 remainder、つまり `15 mod 16`

まずは concrete に次段を足す。

```lean
noncomputable def orbitWindowResidueCountMod32EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 15))

noncomputable def orbitWindowResidueCountMod32EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 31))
```

split theorem：

```lean
theorem tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k =
      orbitWindowResidueCountMod32EqFifteenTail n k +
        orbitWindowResidueCountMod32EqThirtyOneTail n k := by
  unfold orbitWindowResidueCountMod16EqFifteenTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases hfifteen : oddOrbitLabel n (k + 1) % 32 = 15
      · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
          omega
        have hnot31 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
          omega
        simp [ih, hmod16, hfifteen, hnot31, Nat.add_assoc, Nat.add_comm]
      · by_cases h31 : oddOrbitLabel n (k + 1) % 32 = 31
        · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
            omega
          simp [ih, hmod16, h31, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod16 : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
            intro hmod16
            have hchild :
                oddOrbitLabel n (k + 1) % 32 = 15 ∨
                  oddOrbitLabel n (k + 1) % 32 = 31 := by
              omega
            cases hchild with
            | inl h =>
                exact hfifteen h
            | inr h =>
                exact h31 h
          simp [ih, hnotMod16, hfifteen, h31]
```

これは前回の mod16 split と同型なので、かなり通る可能性が高い。

## 9.2. 第二候補：`15 mod 16` continuing recursion edge

報告では既存 theorem として、次が使えそうと出ている。

```lean
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
```

ここから、

```text
tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

を作る。

まず count 定義は既に `7 mod 16` と `15 mod 16` がある。
狙う theorem：

```lean
theorem tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k ≤
      orbitWindowResidueCountMod16EqSevenTail n (k + 1) +
        orbitWindowResidueCountMod16EqFifteenTail n (k + 1) := by
  -- pointwise transition from mod32 children:
  -- 15 mod32 -> next 7 mod16
  -- 31 mod32 -> next 15 mod16
  sorry
```

これは `tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven` の level 2 版じゃ。

## 9.3. 第三候補：level API を作る

いきなり一般化せず、まず名前だけで level を固定する。

```lean
def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowHeightCountEqTail n k 1

def TailRemainderLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqSevenTail n k

def TailRemainderLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqFifteenTail n k
```

落ちる側も定義するなら：

```lean
def TailFallingLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqThreeTail n k

def TailFallingLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqSevenTail n k
```

この naming を入れるだけで、次の theorem が読みやすくなる。

```lean
theorem tailRemainderLevel0_budget_with_level1_remainder ...
theorem tailRemainderLevel1_step_grammar ...
```

## 10. 一歩先の推論

次に見える大きな形は、有限 level (L) までの remainder accounting じゃ。

例えば level 2 までなら、

```text
level 0 reservoir
  -> falling level 1
  -> remainder level 1

remainder level 1
  -> falling level 2
  -> remainder level 2
```

したがって、理想形はこう。

```text
base + level0 reservoir
  <= sumS contribution
     + level2 remainder
```

より具体的には、既存の `tailExactHeightOneReservoir_budget_with_remainder` は level 1 remainder まで。

次は、

```text
base + exact-height-one reservoir
  <= larger sumS contribution
     + tail 15 mod 16 remainder
```

を狙う。

候補 theorem：

```lean
theorem tailExactHeightOneReservoir_budget_with_mod16Fifteen_remainder
    (n : OddNat) (k : ℕ) :
    ((k + 1) + 1) + orbitWindowHeightCountEqTail n k 1 ≤
      sumS n (((k + 1) + 1) + 1) +
        orbitWindowResidueCountMod16EqFifteenTail n k := by
  -- level 0 budget with 7 mod8 remainder
  -- then split / charge 7 mod16 falling child one step later
  sorry
```

ただし index は慎重に確認が必要じゃ。
`sumS n ((k+1)+1)` からさらに一手進めるので、window が `k+3` になる可能性がある。

## 11. さらに次の一手

delayed-reservoir tower が level 2 まで安定したら、次は **pressure-heavy から tower に入る mass** を探す。

いま一番使いやすい入口は、

```lean
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

これを pressure 側と接続するには、

```text
pressure-heavy
  -> source continuation sibling mass at depth 2 が正 / 大きい
```

が欲しい。

既に pressure は、

```text
MoreThanHalf continuation retention
```

なので、depth `2` に限れば、

```text
pressure at depth 2
  -> continuationMass depth 2 is positive
```

は簡単かもしれない。

候補：

```lean
theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
    (n : OddNat) (k : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 := by
  unfold MoreThanHalf at h
  omega
```

これが通れば、

```text
pressure at depth 2
  -> source continuation mass depth 2 positive
  -> delayed budget with remainder
```

へ接続できる。

さらに、range pressure から depth 2 pressure を得るには、`r=2`, `len=1` の特殊化が使える。

## 12. 賢狼が試して欲しい実験補題

## 実験 A: mod32 split for `15 mod 16`

```lean
noncomputable def orbitWindowResidueCountMod32EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 15))

noncomputable def orbitWindowResidueCountMod32EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 31))
```

```lean
theorem tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k =
      orbitWindowResidueCountMod32EqFifteenTail n k +
        orbitWindowResidueCountMod32EqThirtyOneTail n k := by
  unfold orbitWindowResidueCountMod16EqFifteenTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases hfifteen : oddOrbitLabel n (k + 1) % 32 = 15
      · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
          omega
        have hnot31 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
          omega
        simp [ih, hmod16, hfifteen, hnot31, Nat.add_assoc, Nat.add_comm]
      · by_cases h31 : oddOrbitLabel n (k + 1) % 32 = 31
        · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
            omega
          simp [ih, hmod16, h31, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod16 : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
            intro hmod16
            have hchild :
                oddOrbitLabel n (k + 1) % 32 = 15 ∨
                  oddOrbitLabel n (k + 1) % 32 = 31 := by
              omega
            cases hchild with
            | inl h =>
                exact hfifteen h
            | inr h =>
                exact h31 h
          simp [ih, hnotMod16, hfifteen, h31]
```

## 実験 B: pointwise transition for `15 mod 16`

既存 theorem の alias でよい。

```lean
theorem oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen_alias
    (n : OddNat) (i : ℕ)
    (h : oddOrbitLabel n i % 32 = 15) :
    oddOrbitLabel n (i + 1) % 16 = 7 :=
  oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen n i h
```

```lean
theorem oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone_alias
    (n : OddNat) (i : ℕ)
    (h : oddOrbitLabel n i % 32 = 31) :
    oddOrbitLabel n (i + 1) % 16 = 15 :=
  oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone n i h
```

実際に既存名が報告通り使えるか確認。

## 実験 C: count-level recursion for `15 mod 16`

```lean
theorem tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k ≤
      orbitWindowResidueCountMod16EqSevenTail n (k + 1) +
        orbitWindowResidueCountMod16EqFifteenTail n (k + 1) := by
  unfold orbitWindowResidueCountMod16EqFifteenTail
  unfold orbitWindowResidueCountMod16EqSevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- likely same pattern as tailMod8Seven_le_nextTail...
      -- split source by mod32 = 15 / 31
      sorry
```

この実験は、tower level 2 の再帰辺。

## 実験 D: level aliases

```lean
def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowHeightCountEqTail n k 1

def TailRemainderLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqSevenTail n k

def TailRemainderLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqFifteenTail n k

def TailFallingLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqThreeTail n k

def TailFallingLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqSevenTail n k
```

これは後で一般化する前の読み替え API。

## 実験 E: level 1 remainder step grammar

```lean
theorem tailRemainderLevel1_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel1 n k ≤
      TailFallingLevel1 n (k + 1) +
        TailRemainderLevel1 n (k + 1) := by
  unfold TailRemainderLevel1
  unfold TailFallingLevel1
  exact tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven n k
```

## 実験 F: level 2 remainder static split

```lean
theorem tailRemainderLevel1_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel1 n k =
      TailFallingLevel2 n k +
        TailRemainderLevel2 n k := by
  unfold TailRemainderLevel1
  unfold TailFallingLevel2
  unfold TailRemainderLevel2
  exact tailResidueCountMod8EqSeven_split_mod16_seven_fifteen n k
```

## 実験 G: source pressure at depth 2 gives continuation mass positive

```lean
theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
    (n : OddNat) (k : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 := by
  unfold MoreThanHalf at h
  omega
```

これは pressure-heavy から tower budget へ入る入口。

## 実験 H: one-depth pressure gives delayed budget

```lean
theorem sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
    (n : OddNat) (k : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k :=
  sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder n k
```

仮定 `h` はこの theorem 自体には不要だが、将来の API では「pressure からこの budget を使う」ための wrapper として意味がある。不要引数になるのが気になるなら、`_h` にするか、まずは入れない方がよい。

## 13. 次コミットの推奨順

```text
1. mod32 tail count を追加:
   15 mod 32 / 31 mod 32

2. tail 15 mod 16 split を追加

3. 既存 pointwise transition theorem の型確認

4. tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen を試す

5. TailRemainderLevel0/1/2 と TailFallingLevel1/2 alias を追加

6. level alias 版の step grammar を追加

7. sourceContinuationMass depth 2 と pressure depth 2 の接続補題を試す

8. docs:
   DelayedReservoirTower から Level2Remainder へ接続
```

## 14. 総括

checkpoint `116` はかなり強い。

今回で、

```text
tail 7 mod 8
  -> next exact-height-one reservoir
  -> next 3 mod 8 + next 7 mod 8
```

という再帰辺が定理になった。

さらに、

```text
falling part は sumS に入る
continuing part は remainder として残る
```

という budget-with-remainder が通った。

これは Collatz 証明そのものではまだない。
しかし、局所 grammar と会計構造としては、明らかに一段進んでいる。

次は `15 mod 16`。
つまり level 2 remainder を作る。

```text
7 mod 8
  -> 7 mod 16 + 15 mod 16

15 mod 16
  -> 15 mod 32 + 31 mod 32

falling child を sumS へ
continuing child を次 remainder へ
```

この流れが level 2 まで通れば、delayed-reservoir tower は単発の比喩ではなく、有限段の再帰会計としてかなり堅くなる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index f9bd59da..6e1d3478 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -976,6 +976,28 @@ noncomputable def orbitWindowResidueCountMod8EqSevenTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 8 = 7))
 
+/--
+Number of shifted-tail labels in residue class `7 mod 16`.
+
+This is the delayed-peeling child inside the shifted-tail `7 mod 8`
+continuing color.
+-/
+noncomputable def orbitWindowResidueCountMod16EqSevenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 7))
+
+/--
+Number of shifted-tail labels in residue class `15 mod 16`.
+
+This is the continuing child inside the shifted-tail `7 mod 8` continuing
+color.
+-/
+noncomputable def orbitWindowResidueCountMod16EqFifteenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 15))
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -3937,6 +3959,47 @@ theorem tailHeightCountEq_one_split_mod8_three_seven
           exact hheight (hiff.mpr (Or.inr hseven))
         simp [ih, hheight, hnotThree, hnotSeven]
 
+/--
+The shifted-tail `7 mod 8` continuing color splits into its two children
+modulo `16`: the delayed-peeling child `7 mod 16` and the continuing child
+`15 mod 16`.
+-/
+theorem tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSevenTail n k =
+      orbitWindowResidueCountMod16EqSevenTail n k +
+        orbitWindowResidueCountMod16EqFifteenTail n k := by
+  unfold orbitWindowResidueCountMod8EqSevenTail
+  unfold orbitWindowResidueCountMod16EqSevenTail
+  unfold orbitWindowResidueCountMod16EqFifteenTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      by_cases hseven : oddOrbitLabel n (k + 1) % 16 = 7
+      · have hmod8 : oddOrbitLabel n (k + 1) % 8 = 7 := by
+          omega
+        have hnotFifteen : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
+          omega
+        simp [ih, hmod8, hseven, Nat.add_assoc, Nat.add_comm]
+      · by_cases hfifteen : oddOrbitLabel n (k + 1) % 16 = 15
+        · have hmod8 : oddOrbitLabel n (k + 1) % 8 = 7 := by
+            omega
+          simp [ih, hmod8, hfifteen, Nat.add_comm, Nat.add_left_comm]
+        · have hnotMod8 : oddOrbitLabel n (k + 1) % 8 ≠ 7 := by
+            intro hmod8
+            have hchild :
+                oddOrbitLabel n (k + 1) % 16 = 7 ∨
+                  oddOrbitLabel n (k + 1) % 16 = 15 := by
+              omega
+            cases hchild with
+            | inl h =>
+                exact hseven h
+            | inr h =>
+                exact hfifteen h
+          simp [ih, hnotMod8, hseven, hfifteen]
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4257,6 +4320,78 @@ theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
   apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n (i + 1)).mpr
   exact oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
 
+/--
+Every shifted-tail `7 mod 8` entry remains in the shifted-tail exact-height-one
+reservoir one step later.
+
+This is the count-level recursion edge for the continuing color.
+-/
+theorem tailMod8Seven_le_nextTailHeightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSevenTail n k ≤
+      orbitWindowHeightCountEqTail n (k + 1) 1 := by
+  unfold orbitWindowResidueCountMod8EqSevenTail
+  unfold orbitWindowHeightCountEqTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransition :
+          oddOrbitLabel n (k + 1) % 8 = 7 →
+            orbitWindowHeight n ((k + 1) + 1) = 1 :=
+        orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 8 = 7
+      · have htarget : orbitWindowHeight n ((k + 1) + 1) = 1 :=
+          htransition hsource
+        simp [hsource, htarget]
+        omega
+      · by_cases htarget : orbitWindowHeight n ((k + 1) + 1) = 1
+        · simp [hsource, htarget]
+          omega
+        · simp [hsource, htarget]
+          omega
+
+/--
+The shifted-tail `7 mod 8` continuing color enters the next shifted-tail
+exact-height-one reservoir, which then splits again into `3 mod 8` and
+`7 mod 8` colors.
+-/
+theorem tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSevenTail n k ≤
+      orbitWindowResidueCountMod8EqThreeTail n (k + 1) +
+        orbitWindowResidueCountMod8EqSevenTail n (k + 1) := by
+  have h :
+      orbitWindowResidueCountMod8EqSevenTail n k ≤
+        orbitWindowHeightCountEqTail n (k + 1) 1 :=
+    tailMod8Seven_le_nextTailHeightCountEq_one n k
+  rw [tailHeightCountEq_one_split_mod8_three_seven] at h
+  exact h
+
+/--
+One-step grammar for the shifted-tail exact-height-one reservoir.
+
+Each current exact-height-one tail entry either contributes to the next tail
+`height >= 2` count through the `3 mod 8` delayed-peeling color, or remains in
+the next exact-height-one reservoir through the `7 mod 8` continuing color.
+-/
+theorem tailExactHeightOneReservoir_step_grammar
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountEqTail n k 1 ≤
+      orbitWindowHeightCountGeTail n (k + 1) 2 +
+        orbitWindowHeightCountEqTail n (k + 1) 1 := by
+  rw [tailHeightCountEq_one_split_mod8_three_seven]
+  have hthree :
+      orbitWindowResidueCountMod8EqThreeTail n k ≤
+        orbitWindowHeightCountGeTail n (k + 1) 2 :=
+    tailMod8Three_le_nextTailHeightCountGe_two n k
+  have hseven :
+      orbitWindowResidueCountMod8EqSevenTail n k ≤
+        orbitWindowHeightCountEqTail n (k + 1) 1 :=
+    tailMod8Seven_le_nextTailHeightCountEq_one n k
+  omega
+
 /--
 The `7 mod 16` branch recovers delayed peeling after two transitions.
 
@@ -5398,6 +5533,48 @@ theorem tailResidueCountMod8EqThree_delayed_drift
     (Nat.add_le_add_left htail (k + 1))
     (orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n (k + 1))
 
+/--
+Delayed-reservoir budget with a continuing-color remainder.
+
+The `3 mod 8` part of the current exact-height-one reservoir contributes to
+the next accumulated `sumS` lower bound.  The `7 mod 8` part is left explicit
+as the still-continuing remainder.
+-/
+theorem tailExactHeightOneReservoir_budget_with_remainder
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowHeightCountEqTail n k 1 ≤
+      sumS n ((k + 1) + 1) +
+        orbitWindowResidueCountMod8EqSevenTail n k := by
+  rw [tailHeightCountEq_one_split_mod8_three_seven]
+  have hthree :
+      (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
+        sumS n ((k + 1) + 1) :=
+    tailResidueCountMod8EqThree_delayed_drift n k
+  omega
+
+/--
+Source-continuation depth-two budget with a continuing-color remainder.
+
+Depth-two source continuation enters the shifted-tail exact-height-one
+reservoir.  The `3 mod 8` part contributes to the next `sumS` lower bound, and
+the `7 mod 8` part remains as an explicit delayed reservoir remainder.
+-/
+theorem sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+      sumS n ((k + 1) + 1) +
+        orbitWindowResidueCountMod8EqSevenTail n k := by
+  have hsource :
+      orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+        orbitWindowResidueCountMod8EqThreeTail n k +
+          orbitWindowResidueCountMod8EqSevenTail n k :=
+    sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven n k
+  have hthree :
+      (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
+        sumS n ((k + 1) + 1) :=
+    tailResidueCountMod8EqThree_delayed_drift n k
+  omega
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index ffa9361e..c3d9e320 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -150,6 +150,7 @@ docs/Collatz-CauseSideFrequencyAlias-112.md
 docs/Collatz-FrequencyHeightBridge-113.md
 docs/Collatz-TailFacingHeightBridge-114.md
 docs/Collatz-RecoveryDelayedBranch-115.md
+docs/Collatz-DelayedReservoirTower-116.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md
new file mode 100644
index 00000000..7c3e960a
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md
@@ -0,0 +1,181 @@
+# Collatz Delayed Reservoir Tower 116
+
+Checkpoint 116 builds the first recursive edge of the delayed-reservoir tower.
+
+Checkpoint 115 established:
+
+```text
+tail exact height 1
+  = tail 3 mod 8
+    + tail 7 mod 8
+```
+
+with the reading:
+
+```text
+3 mod 8:
+  delayed-peeling color
+
+7 mod 8:
+  continuing color
+```
+
+Checkpoint 116 asks what happens to the continuing color.
+
+## Static Refinement
+
+The continuing `7 mod 8` color splits into two children modulo `16`:
+
+```lean
+orbitWindowResidueCountMod16EqSevenTail
+orbitWindowResidueCountMod16EqFifteenTail
+tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+```
+
+Conceptually:
+
+```text
+tail 7 mod 8
+  = tail 7 mod 16
+    + tail 15 mod 16
+```
+
+The `7 mod 16` child is the next delayed-peeling child.
+The `15 mod 16` child is the next continuing child.
+
+## Dynamic Recursion Edge
+
+The pointwise theorem already existed:
+
+```lean
+orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+```
+
+Checkpoint 116 lifts it to count level:
+
+```lean
+tailMod8Seven_le_nextTailHeightCountEq_one
+```
+
+This says:
+
+```text
+tail 7 mod 8 at this step
+  -> next tail exact height 1
+```
+
+Using the checkpoint 115 split again gives:
+
+```lean
+tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+```
+
+So:
+
+```text
+tail 7 mod 8
+  -> next tail 3 mod 8 + next tail 7 mod 8
+```
+
+This is the first theorem-level recursive edge of the delayed-reservoir tower.
+
+## One-Step Grammar
+
+The combined grammar is:
+
+```lean
+tailExactHeightOneReservoir_step_grammar
+```
+
+It reads:
+
+```text
+current tail exact height 1
+  <= next tail height >= 2
+     +
+     next tail exact height 1
+```
+
+This is a finite count inequality.  It does not assert that every individual
+entry is independent or injective; it packages the already-proved color
+transitions as a count-level budget.
+
+## Budget With Remainder
+
+The stronger budget keeps the continuing color visible:
+
+```lean
+tailExactHeightOneReservoir_budget_with_remainder
+```
+
+Reading:
+
+```text
+base layer + current exact-height-one reservoir
+  <= next accumulated sumS
+     +
+     current 7 mod 8 continuing remainder
+```
+
+The source-continuation version is:
+
+```lean
+sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+```
+
+Reading:
+
+```text
+base layer + source continuation mass at depth 2
+  <= next accumulated sumS
+     +
+     tail 7 mod 8 continuing remainder
+```
+
+This is the useful compromise discovered at this checkpoint:
+
+```text
+do not claim that all continuation mass immediately peels;
+charge the delayed-peeling part to sumS and carry the continuing part as an
+explicit remainder.
+```
+
+## Interpretation
+
+The delayed-reservoir tower is no longer just a visual metaphor.
+
+The theorem-supported local grammar is:
+
+```text
+exact-height-one reservoir
+  -> falling color
+  -> continuing color
+
+continuing color
+  -> next reservoir
+  -> falling color
+  -> continuing color
+```
+
+The next likely resolution step is:
+
+```text
+tail 15 mod 16
+  -> split into tail 15 mod 32 and tail 31 mod 32
+```
+
+and then prove the matching recursive edge.
+
+## Next Targets
+
+Useful next theorem families:
+
+```text
+1. tail 15 mod 16 split modulo 32
+2. count-level transition from tail 15 mod 16 to next tail reservoir
+3. general finite remainder tower for levels 0, 1, 2
+```
+
+The current advice is to add one concrete level at a time.  The low-resolution
+API is still being discovered, and premature generalization may hide the
+usable theorem names.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 3532dbb5..a171bab9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -870,6 +870,77 @@ pressure or recovery channel
   -> the 3 mod 8 color supplies delayed extra peeling
 ```
 
+## Delayed Reservoir Tower
+
+Checkpoint 116 starts the recursive tower above the checkpoint 115 split.
+
+The continuing `7 mod 8` color itself splits at the next resolution:
+
+```lean
+orbitWindowResidueCountMod16EqSevenTail
+orbitWindowResidueCountMod16EqFifteenTail
+tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+```
+
+The reading is:
+
+```text
+tail 7 mod 8
+  = tail 7 mod 16
+    + tail 15 mod 16
+```
+
+This is not only a static refinement.  The existing pointwise theorem:
+
+```lean
+orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+```
+
+is now lifted to count level:
+
+```lean
+tailMod8Seven_le_nextTailHeightCountEq_one
+tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+```
+
+So the continuing color enters the next exact-height-one reservoir and is then
+split again:
+
+```text
+tail 7 mod 8 at this step
+  -> next tail exact height 1
+  -> next tail 3 mod 8 / next tail 7 mod 8
+```
+
+The one-step grammar is:
+
+```lean
+tailExactHeightOneReservoir_step_grammar
+```
+
+which says:
+
+```text
+current tail exact height 1
+  -> next tail height >= 2
+     or
+     next tail exact height 1
+```
+
+The budget form keeps the continuing part as an explicit remainder:
+
+```lean
+tailExactHeightOneReservoir_budget_with_remainder
+sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+```
+
+This is the current strongest finite reading:
+
+```text
+the delayed-peeling color pays into sumS;
+the continuing color is not discarded, but carried as the next remainder.
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 8b2611d6..5ba050f0 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -320,6 +320,14 @@ tailMod8Three_le_nextTailHeightCountGe_two
 sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
 sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
 tailResidueCountMod8EqThree_delayed_drift
+orbitWindowResidueCountMod16EqSevenTail
+orbitWindowResidueCountMod16EqFifteenTail
+tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+tailMod8Seven_le_nextTailHeightCountEq_one
+tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+tailExactHeightOneReservoir_step_grammar
+tailExactHeightOneReservoir_budget_with_remainder
+sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-116.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-116.md
new file mode 100644
index 00000000..65d8f572
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-116.md
@@ -0,0 +1,297 @@
+# Report Petal 116: Delayed Reservoir Tower
+
+## Summary
+
+Checkpoint 116 extends checkpoint 115 from a one-step delayed branch into the
+first recursive edge of a delayed-reservoir tower.
+
+Checkpoint 115 established:
+
+```text
+tail exact height 1
+  = tail 3 mod 8
+    + tail 7 mod 8
+```
+
+Checkpoint 116 proves that the continuing color is not a dead end:
+
+```text
+tail 7 mod 8
+  -> next tail exact height 1
+  -> next tail 3 mod 8 + next tail 7 mod 8
+```
+
+So the current grammar is:
+
+```text
+reservoir
+  -> falling color
+  -> continuing color
+     -> next reservoir
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
+New shifted-tail mod-16 counts:
+
+```lean
+orbitWindowResidueCountMod16EqSevenTail
+orbitWindowResidueCountMod16EqFifteenTail
+```
+
+Static refinement of the continuing color:
+
+```lean
+tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+```
+
+Count-level continuing-color recursion:
+
+```lean
+tailMod8Seven_le_nextTailHeightCountEq_one
+tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+```
+
+One-step reservoir grammar:
+
+```lean
+tailExactHeightOneReservoir_step_grammar
+```
+
+Budget-with-remainder forms:
+
+```lean
+tailExactHeightOneReservoir_budget_with_remainder
+sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+```
+
+## Experimental Results
+
+### Experiment A: mod16 split
+
+Succeeded.
+
+```lean
+tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
+```
+
+This proves:
+
+```text
+tail 7 mod 8 count
+  = tail 7 mod 16 count
+    + tail 15 mod 16 count
+```
+
+### Experiment B: pointwise `7 mod 8` continuation
+
+Already existed:
+
+```lean
+orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+```
+
+This was reused rather than duplicated.
+
+### Experiment C: count-level continuation
+
+Succeeded.
+
+```lean
+tailMod8Seven_le_nextTailHeightCountEq_one
+```
+
+Meaning:
+
+```text
+tail 7 mod 8 at this step
+  -> next tail exact height 1
+```
+
+### Experiment D: next reservoir split
+
+Succeeded.
+
+```lean
+tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
+```
+
+Meaning:
+
+```text
+tail 7 mod 8
+  -> next tail 3 mod 8 + next tail 7 mod 8
+```
+
+### Experiment E: one-step grammar
+
+Succeeded.
+
+```lean
+tailExactHeightOneReservoir_step_grammar
+```
+
+This packages the local grammar:
+
+```text
+current exact-height-one reservoir
+  -> next extra-height count
+     or
+     next exact-height-one reservoir
+```
+
+### Experiment F: budget with remainder
+
+Succeeded.
+
+```lean
+tailExactHeightOneReservoir_budget_with_remainder
+```
+
+This is stronger than a pure drift lower bound because it does not discard the
+continuing part.  It explicitly carries the `7 mod 8` remainder.
+
+### Experiment G: source continuation budget with remainder
+
+Succeeded.
+
+```lean
+sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
+```
+
+Meaning:
+
+```text
+base layer + source continuation depth 2
+  <= next sumS
+     + tail 7 mod 8 remainder
+```
+
+This is currently the most useful bridge back toward pressure-heavy arguments.
+
+## Main Mathematical Reading
+
+The key correction remains:
+
+```text
+continuation mass does not all immediately peel.
+```
+
+But checkpoint 116 gives a better replacement:
+
+```text
+continuation mass enters a reservoir;
+the falling color is charged to sumS;
+the continuing color is carried as a remainder.
+```
+
+This is closer to an accounting proof than a direct collapse proof.
+
+The important finite pattern is:
+
+```text
+falling part:
+  contributes to accumulated height
+
+continuing part:
+  remains visible and can be refined at the next resolution
+```
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-DelayedReservoirTower-116.md
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
+### 1. Add the next concrete continuation split
+
+The next static split should be:
+
+```text
+tail 15 mod 16
+  = tail 15 mod 32
+    + tail 31 mod 32
+```
+
+This mirrors the new `7 mod 8` split.
+
+### 2. Add the next count-level recursion edge
+
+The expected edge is:
+
+```text
+tail 15 mod 16
+  -> next tail 7 mod 16 + next tail 15 mod 16
+```
+
+Existing pointwise theorems around:
+
+```lean
+oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
+oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
+```
+
+should be reusable.
+
+### 3. Start a small level-indexed remainder API
+
+Do not generalize too early.  A useful next compromise is a named level-0 /
+level-1 API:
+
+```text
+level 0 remainder:
+  exact-height-one reservoir
+
+level 1 remainder:
+  tail 7 mod 8
+
+level 2 remainder:
+  tail 15 mod 16
+```
+
+This can later become a recursive definition once the low-level theorem names
+are stable.
````
`````
