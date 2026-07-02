# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: c5fac47ede036a8ea74e2d6bee849a388821d7b0

## Report

115 進めました。`DkMath.Collatz.PetalBridge` に、recovery / continuation が即時 extra peeling ではなく `3 mod 8` の delayed-peeling color へ入る構造を固定しました。

主な追加は以下です。

- `orbitWindowResidueCountMod8EqThreeTail`
- `orbitWindowResidueCountMod8EqSevenTail`
- `tailRecoveryMass_depth_one_le_heightCountGe_two`
- `tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three`
- `tailHeightCountEq_one_split_mod8_three_seven`
- `tailMod8Three_le_nextTailHeightCountGe_two`
- `tailResidueCountMod8EqThree_delayed_drift`
- `sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three`
- `sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven`

重要なリカバリー点は、`tail recovery depth 2 -> height >= 2` ではなく、`tail recovery depth 2 -> 3 mod 8 -> one-step later height >= 2` だったことです。これはレポートにも明記しました。

ドキュメントも同期済みです。

- [Collatz-RecoveryDelayedBranch-115.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md)
- [report-petal-115.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-115.md)
- README / Guide / Status も更新済み

検証結果:

- `lake build DkMath.Collatz.PetalBridge` 成功
- `lake build DkMath.Collatz.Collatz2K26` 成功
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean` 該当なし
- `git diff --check` 問題なし

既存の unrelated warning として、`DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は継続しています。

## Review

## 1. 状況分析

今回の `review-petal-116.md` の中身は、checkpoint `115`、つまり **Recovery Delayed Branch** の完了報告じゃ。前回 checkpoint `114` で、

```text
source continuation at parent depth 2
  -> shifted-tail exact height 1
```

までは見えた。今回はその exact-height-one reservoir をさらに分解し、どこに delayed extra peeling が潜んでいるかを Lean で固定した回じゃ。主な追加として、tail 側の `3 mod 8` / `7 mod 8` count、exact-height-one reservoir の split、`3 mod 8` から次 step の height \(\ge 2\) への delayed bridge、さらに source recovery / source continuation から tail color への接続が入っている。

今回の結論はかなり大きい。

```text
tail recovery, parent depth 1
  -> immediate height >= 2

tail recovery, parent depth 2
  -> 3 mod 8
  -> exact height 1 now
  -> height >= 2 one step later
```

つまり、extra peeling は消えていなかった。
ただし depth `2` では **即時** ではなく、**一手遅れて現れる**。

## 2. 今回の核心

checkpoint `115` の核心は、次の reservoir grammar が theorem-level で見えたことじゃ。

```text
tail exact height 1
  = tail 3 mod 8
    + tail 7 mod 8
```

Lean 名では、

```lean
tailHeightCountEq_one_split_mod8_three_seven
```

そして、

```text
tail 3 mod 8
  -> next tail height >= 2
```

Lean 名では、

```lean
tailMod8Three_le_nextTailHeightCountGe_two
tailResidueCountMod8EqThree_delayed_drift
```

つまり、exact height 1 はただの停滞ではない。
その内部には、次 step で extra peeling へ変わる色がある。

これが、今回の最重要発見じゃ。

## 3. レビュー

## 3.1. `3 mod 8` / `7 mod 8` の tail count を入れたのは正しい

今回追加された、

```lean
orbitWindowResidueCountMod8EqThreeTail
orbitWindowResidueCountMod8EqSevenTail
```

は、今後の delayed-reservoir 解析の基礎語彙になる。

前回までは、

```text
tail exact height 1
```

という一つの塊だった。

しかし今回、それを

```text
3 mod 8:
  delayed-peeling color

7 mod 8:
  continuing color
```

へ分解した。

この「色分け」はかなり重要じゃ。
exact height 1 は一色ではない。
中に「次に落ちる色」と「まだ残る色」がある。

## 3.2. `tailRecoveryMass_depth_one_le_heightCountGe_two` は即時橋

今回、recovery channel の低 depth の違いがかなり鮮明になった。

```lean
tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
tailRecoveryMass_depth_one_le_heightCountGe_two
```

これは、

```text
tail recovery at parent depth 1
  -> 1 mod 4
  -> height >= 2
```

を意味する。

つまり depth `1` の recovery は、素直に即時 extra peeling 側へ入る。

これは重要な positive result じゃ。
前回は「continuation-retention は exact height 1 だった」と補正されたが、今回、recovery の浅い層には即時 peeling があると確認できた。

## 3.3. `tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three` が深い

一方で、depth `2` の recovery は違った。

```lean
tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
```

これは、

```text
tail recovery at parent depth 2
  -> 3 mod 8
```

を言う。

そして \(3 \mod 8\) は、現在 step では exact height 1 だが、次 step で \(1 \mod 4\) に移る。

つまり、

```text
tail recovery depth 2
  -> immediate height >= 2
```

ではなく、

```text
tail recovery depth 2
  -> delayed height >= 2
```

だった。

これはとても綺麗な補正じゃ。

## 3.4. source hook も良い

source 側の hook はこの二つ。

```lean
sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
```

前者は、source recovery depth `3` が tail の delayed-peeling color `3 mod 8` に入ることを示す。

後者は、source continuation depth `2` が tail exact-height-one reservoir に入り、その reservoir が `3 mod 8` と `7 mod 8` に分かれることを示す。

この二つは役割が違う。

```text
sourceRecoveryMass_depth_three:
  delayed-peeling color へ直接入る

sourceContinuationMass_depth_two:
  reservoir 全体へ入るが、3/7 の内訳までは保証しない
```

この差が今後の主戦場になる。

## 4. 数学的解説

今回の構造を、軌道の局所遷移で見る。

奇数 \(q\) に対して exact height 1 とは、

$$
q\equiv 3\pmod 4
$$

である。

これを mod \(8\) で分けると、

$$
q\equiv 3\pmod 8
$$

または、

$$
q\equiv 7\pmod 8
$$

になる。

まず \(q\equiv 3\pmod 8\) の場合、

$$
q=8a+3
$$

なので、

$$
T(q)=\frac{3q+1}{2}=12a+5
$$

ここで \(12a+5\equiv 1\pmod 4\)。
したがって次の tail height は \(\ge 2\)。

一方、\(q\equiv 7\pmod 8\) の場合、

$$
q=8a+7
$$

なので、

$$
T(q)=\frac{3q+1}{2}=12a+11
$$

これは \(3\pmod 4\) 側に残る。
つまり height 1 reservoir に留まりやすい。

だから、

```text
3 mod 8:
  next step で height >= 2

7 mod 8:
  exact height 1 reservoir に継続
```

という読みになる。

この「3 は遅延 peeling、7 は継続」という分解が、今回の Lean 定理群で固定された。

## 5. 一歩先ゆく推論：これは reservoir tower の入口

今回の結果から、かなり大きな構図が見える。

前回までの期待は、

```text
pressure-heavy
  -> immediate extra peeling
```

だった。

しかし正しくは、

```text
pressure / continuation / recovery channel
  -> exact-height-one reservoir
  -> color split
  -> delayed extra peeling
```

だった。

つまり、Collatz の降下は一段で見てはいけない。
一段では exact height 1 に見えるものが、次の解像度で delayed peeling color を含んでいる。

これをさらに進めると、次は `7 mod 8` continuing color を見ることになる。

```text
7 mod 8
  -> 7 mod 16 / 15 mod 16
```

ただし、ここで注意がある。
`7 mod 16` と `15 mod 16` のどちらが次の delayed-peeling child になるかは、単純に名前だけで決めない方がよい。必ず Lean で遷移を確認するべきじゃ。

直感的には、continuing color は解像度を上げるたびに二つに割れる。

```text
continuing reservoir
  -> delayed-peeling child
  -> continuing child
```

これが繰り返されるなら、Collatz.PetalBridge は「有限 delayed-reservoir tower」を作れる。

これはかなり強い。
なぜなら、pressure-heavy が即時 height を作らなくても、reservoir tower のどこかで delayed peeling mass に変わる可能性があるからじゃ。

## 6. Gnomon / 一色線との接続

今回の結果は、さっきの「一色線」直感ともよく合う。

`tail exact height 1` は、まだ完全に一色ではない。

```text
tail exact height 1
  = 3 mod 8
    + 7 mod 8
```

つまり二色ある。

そのうち、

```text
3 mod 8
```

は、次に \(1 \mod 4\) へ移る。
これは一色線へ近づく色。

一方、

```text
7 mod 8
```

は、まだ continuing color として残る。
これはさらに解像度を上げる必要がある色。

だから Collatz の進行は、

```text
Gnomon 層の多色状態
  -> exact-height-one reservoir
  -> delayed-peeling color と continuing color に分裂
  -> delayed-peeling color が一手後に落ちる
  -> continuing color はさらに細かく分裂
```

と読める。

ここで Petal の「解像度が上がる」という直感がかなり噛み合う。

## 7. 今回閉じたもの

今回閉じたものは、次の五つ。

```text
1. tail exact-height-one reservoir を 3 mod 8 / 7 mod 8 に分解

2. tail recovery depth 1 は immediate height >= 2 である

3. tail recovery depth 2 は immediate ではなく delayed 3 mod 8 color である

4. tail 3 mod 8 は next tail height >= 2 に寄与する

5. source recovery depth 3 は delayed 3 mod 8 color へ入る
```

これは大きい。
特に、

```lean
tailResidueCountMod8EqThree_delayed_drift
```

が入ったことで、delayed color が `sumS` 側に接続された。

## 8. まだ閉じていないもの

まだ閉じていない本命は、

```text
pressure-heavy / continuation-heavy が、どれだけ 3 mod 8 delayed color を含むか
```

じゃ。

現状では、

```lean
sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
```

により、source continuation depth `2` は reservoir 全体には入る。

しかし、

```text
そのうち 3 mod 8 がどれだけあるか
```

まではまだ言えていない。

つまり、

```text
source continuation mass
  -> tail 3 mod 8 + tail 7 mod 8
```

までは見えた。

次は、

```text
tail 7 mod 8 continuing color はさらにどう分かれるか
```

を調べる段階じゃ。

## 9. 次の指示

次 checkpoint は、二つの方向がある。

## 9.1. 本命 A：continuing color `7 mod 8` の分解

まず、tail `7 mod 8` を mod `16` で split する。

追加候補：

```lean
noncomputable def orbitWindowResidueCountMod16EqSevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 7))
```

```lean
noncomputable def orbitWindowResidueCountMod16EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 15))
```

そして、

```lean
theorem tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k =
      orbitWindowResidueCountMod16EqSevenTail n k +
        orbitWindowResidueCountMod16EqFifteenTail n k := by
  -- countP split by residue refinement
  -- unfold definitions and induction on k
  sorry
```

これは reservoir tower の次の段になる。

## 9.2. 本命 B：`7 mod 8` の次 step 遷移を固定

次に、`7 mod 8` が次にどこへ行くかを theorem 化する。

候補：

```lean
theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    orbitWindowHeight n (i + 1) = 1 := by
  -- 既存の exact height one iff を使う
  -- next label が 3 mod 4 側に残ることを示す
  sorry
```

既に類似 theorem があるかもしれない。
名前としては、

```lean
orbitWindowNextHeight_one_of_mod_eight_eq_seven
```

または、

```lean
oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
```

がありそうじゃ。

## 9.3. 本命 C：`7 mod 8` continuing color の delayed split

`7 mod 8` が次 step で exact height 1 に残るなら、その次 step の exact-height-one reservoir を再び `3 mod 8` / `7 mod 8` に分けられる。

つまり、直接の split よりも、次の形が本質かもしれない。

```text
tail 7 mod 8 at time i
  -> tail exact height 1 at time i+1
  -> split into 3 mod 8 / 7 mod 8 at time i+1
```

Lean 候補：

```lean
theorem tailMod8Seven_le_nextTailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowHeightCountEqTail n (k + 1) 1 := by
  -- 7 mod 8 remains exact height one one step later
  sorry
```

これが通ると、continuing reservoir の再帰が見える。

## 10. 一歩先の次の一手

`tailMod8Seven_le_nextTailHeightCountEq_one` が通ったら、次に狙うのはこれじゃ。

```lean
theorem tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowResidueCountMod8EqThreeTail n (k + 1) +
        orbitWindowResidueCountMod8EqSevenTail n (k + 1) := by
  have h :
      orbitWindowResidueCountMod8EqSevenTail n k ≤
        orbitWindowHeightCountEqTail n (k + 1) 1 :=
    tailMod8Seven_le_nextTailHeightCountEq_one n k
  -- rw [tailHeightCountEq_one_split_mod8_three_seven] at h
  -- exact h
  sorry
```

これが通れば、

```text
continuing color は、次の tail window で再び reservoir split に入る
```

と言える。

つまり、delayed-reservoir tower の再帰辺が得られる。

そして `3 mod 8` 側には既に、

```lean
tailResidueCountMod8EqThree_delayed_drift
```

がある。

だから今後の tower は、

```text
7 mod 8 continuing color
  -> next reservoir
  -> 3 mod 8 delayed peeling
     or
     7 mod 8 continuing again
```

という有限文法になる。

## 11. さらに先の推論：これは「色数の減少」ではなく「色の選別」

以前の一色線の直感では、色数が減っていくと考えた。

今回の theorem 群を見ると、より精密にはこうじゃ。

```text
色数がただ減るのではない。
色が「落ちる色」と「残る色」に選別される。
```

`3 mod 8` は落ちる色。
`7 mod 8` は残る色。

残る色は、次の解像度でまた落ちる色と残る色に分かれる。

したがって、Collatz の delayed-reservoir は、

```text
peeling color extraction process
```

として読める。

DkMath 的には、これはかなり Petal らしい。

```text
Petal 解像度を上げる
  -> 外側層が二色に分かれる
  -> 一方は中心へ落ちる
  -> もう一方は次の花弁へ進む
```

## 12. 賢狼が試して欲しい実験補題

## 実験 A: tail 7 mod 8 count の mod16 split

```lean
noncomputable def orbitWindowResidueCountMod16EqSevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 7))

noncomputable def orbitWindowResidueCountMod16EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 15))
```

```lean
theorem tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k =
      orbitWindowResidueCountMod16EqSevenTail n k +
        orbitWindowResidueCountMod16EqFifteenTail n k := by
  unfold orbitWindowResidueCountMod8EqSevenTail
  unfold orbitWindowResidueCountMod16EqSevenTail
  unfold orbitWindowResidueCountMod16EqFifteenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      -- by_cases on oddOrbitLabel n (k+1) % 16 = 7 / 15
      -- use omega to relate mod16 child to mod8 parent
      sorry
```

## 実験 B: `7 mod 8` は次 step で exact height 1 に残る

```lean
theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    orbitWindowHeight n (i + 1) = 1 := by
  -- likely route:
  -- prove oddOrbitLabel n (i+1) % 8 is 7 -> next label mod4 = 3
  -- then exact-height-one iff mod8 = 3 or 7, or height=1 iff mod8=3/7
  sorry
```

既存で近いものがある可能性が高いので、まず検索。

```text
rg "mod_eight_eq_seven" DkMath/Collatz/PetalBridge.lean
rg "height.*one.*seven" DkMath/Collatz/PetalBridge.lean
rg "succ.*seven" DkMath/Collatz/PetalBridge.lean
```

## 実験 C: tail 7 mod 8 count は next exact-height-one count に入る

```lean
theorem tailMod8Seven_le_nextTailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowHeightCountEqTail n (k + 1) 1 := by
  unfold orbitWindowResidueCountMod8EqSevenTail
  unfold orbitWindowHeightCountEqTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransition :
          oddOrbitLabel n (k + 1) % 8 = 7 →
            orbitWindowHeight n ((k + 1) + 1) = 1 := by
        intro hmod
        exact orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven n (k + 1) hmod
      by_cases hsource : oddOrbitLabel n (k + 1) % 8 = 7
      · have htarget := htransition hsource
        simp [hsource, htarget]
        omega
      · by_cases htarget : orbitWindowHeight n ((k + 1) + 1) = 1
        · simp [hsource, htarget]
          omega
        · simp [hsource, htarget]
          omega
```

## 実験 D: tail 7 mod 8 は next reservoir split へ入る

```lean
theorem tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowResidueCountMod8EqThreeTail n (k + 1) +
        orbitWindowResidueCountMod8EqSevenTail n (k + 1) := by
  have h :
      orbitWindowResidueCountMod8EqSevenTail n k ≤
        orbitWindowHeightCountEqTail n (k + 1) 1 :=
    tailMod8Seven_le_nextTailHeightCountEq_one n k
  rw [tailHeightCountEq_one_split_mod8_three_seven] at h
  exact h
```

これは通る可能性が高い。
通れば continuing color の再帰辺が完成する。

## 実験 E: delayed-reservoir one-step grammar

`3 mod 8` と `7 mod 8` をまとめて grammar 化する。

```lean
theorem tailExactHeightOneReservoir_step_grammar
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 ≤
      orbitWindowHeightCountGeTail n (k + 1) 2 +
        orbitWindowHeightCountEqTail n (k + 1) 1 := by
  -- split current exact-height-one reservoir into 3/7
  -- 3 side -> next height >= 2
  -- 7 side -> next height = 1
  -- add inequalities
  sorry
```

これはかなり良い補題じゃ。
意味は、

```text
exact-height-one reservoir は、次 step で
extra peeling 側か exact-height-one reservoir 側へ送られる
```

になる。

## 実験 F: current reservoir gives next accumulated lower bound plus continuing reservoir

より強い形。

```lean
theorem tailExactHeightOneReservoir_delayed_budget
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
      sumS n ((k + 1) + 1) :=
  tailResidueCountMod8EqThree_delayed_drift n k
```

これは既にあるので、次は `7 mod 8` continuation を残差として明示したい。

```lean
theorem tailExactHeightOneReservoir_budget_with_remainder
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowHeightCountEqTail n k 1 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  -- split exact-height-one = three + seven
  -- three side contributes to sumS lower bound
  -- seven side remains as remainder
  sorry
```

この形はかなり重要。
「落ちた分」と「残った分」を同時に表す。

## 実験 G: source continuation reservoir with remainder

今回の source continuation bridge を使って、

```lean
theorem sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  -- source continuation <= three + seven
  -- three contributes to sumS
  -- seven remains as remainder
  sorry
```

これはかなり野心的だが、方向としては面白い。
pressure / continuation mass が全部すぐ落ちるとは言わず、落ちない分を remainder として右辺に残す。

この形は、将来の有限降下にかなり向いている。

## 実験 H: recursive remainder theorem の雛形

次段階の構想として、こういう形を目指す。

```lean
def TailContinuingRemainderLevel
    (level : ℕ) (n : OddNat) (k : ℕ) : ℕ :=
  -- level 0: orbitWindowHeightCountEqTail n k 1
  -- level 1: orbitWindowResidueCountMod8EqSevenTail n k
  -- level 2: mod16 continuing child
  -- ...
  0
```

最初は `def` だけでもよい。
いきなり一般定理は重い。まず level 0 / level 1 を手で固める。

## 13. 次コミットの推奨順

```text
1. 既存 theorem 検索:
   mod_eight_eq_seven / height one / succ seven

2. orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven を追加
   既存なら meaning-name alias でよい

3. tailMod8Seven_le_nextTailHeightCountEq_one を追加

4. tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven を追加

5. tailExactHeightOneReservoir_step_grammar を試す

6. tailExactHeightOneReservoir_budget_with_remainder を試す

7. 余裕があれば mod16 split の count 定義だけ追加

8. docs:
   RecoveryDelayedBranch から DelayedReservoirTower へ接続
```

## 14. 総括

checkpoint `115` は非常に良い。

前回わかった exact-height-one reservoir を、今回ついに色分けできた。

$$
\text{tail exact height 1}=\text{tail }3\text{ mod }8+\text{tail }7\text{ mod }8
$$

そして、

```text
3 mod 8:
  one-step later height >= 2

7 mod 8:
  continuing color
```

が見えた。

これは Collatz.PetalBridge の見方を一段進めた。
もう「pressure-heavy がすぐ height を増やすか」だけを見る段階ではない。

これからは、

```text
reservoir に入る
色を分ける
落ちる色を sumS に加える
残る色を次の reservoir へ送る
```

という grammar を作る段階じゃ。

この grammar ができれば、Gnomon / 一色線の直感とも綺麗に合う。

```text
多色の Gnomon 層
  -> 落ちる色
  -> 残る色
  -> 次の解像度で再分解
```

次は `7 mod 8` continuing color を一手進める。
そこが通れば、delayed-reservoir tower の入口が本当に開く。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 88860ab2..f9bd59da 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -954,6 +954,28 @@ noncomputable def orbitWindowResidueCountMod4EqThreeTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3))
 
+/--
+Number of shifted-tail labels in residue class `3 mod 8`.
+
+This is one delayed-peeling color inside the shifted-tail exact-height-one
+reservoir.
+-/
+noncomputable def orbitWindowResidueCountMod8EqThreeTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 8 = 3))
+
+/--
+Number of shifted-tail labels in residue class `7 mod 8`.
+
+This is the continuing color inside the shifted-tail exact-height-one
+reservoir.
+-/
+noncomputable def orbitWindowResidueCountMod8EqSevenTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 8 = 7))
+
 /--
 Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
 
@@ -3395,6 +3417,30 @@ theorem orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
           exact hheight (hiff.mpr h)
         simp [ih, hheight, hres]
 
+/--
+At parent depth `1`, shifted-tail recovery sibling mass is exactly the
+shifted-tail `1 mod 4` cell.
+-/
+theorem tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k 1 =
+      orbitWindowResidueCountMod4EqOneTail n k := by
+  unfold orbitWindowRecoverySiblingMassPow2Tail
+  unfold orbitWindowResidueCountPow2Tail
+  unfold orbitWindowResidueCountMod4EqOneTail
+  simp
+
+/--
+At parent depth `1`, shifted-tail recovery sibling mass is contained in the
+tail `height >= 2` count.
+-/
+theorem tailRecoveryMass_depth_one_le_heightCountGe_two
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k 1 ≤
+      orbitWindowHeightCountGeTail n k 2 := by
+  rw [tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one]
+  rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]
+
 /--
 Counting `height >= 3` entries is the same as counting odd-state labels in
 residue class `5 mod 8`.
@@ -3770,6 +3816,32 @@ theorem tailRetentionMass_depth_two_le_heightCountEq_one
       orbitWindowHeightCountEqTail n k 1 := by
   rw [tailRetentionMass_depth_two_eq_heightCountEq_one]
 
+/--
+At parent depth `2`, shifted-tail recovery sibling mass is exactly the
+shifted-tail `3 mod 8` cell.
+
+Thus this channel is not immediate `height >= 2`; it is the delayed-peeling
+color inside exact height `1`.
+-/
+theorem tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k 2 =
+      orbitWindowResidueCountMod8EqThreeTail n k := by
+  unfold orbitWindowRecoverySiblingMassPow2Tail
+  unfold orbitWindowResidueCountPow2Tail
+  unfold orbitWindowResidueCountMod8EqThreeTail
+  simp
+
+/--
+At parent depth `2`, shifted-tail recovery sibling mass is bounded by the
+delayed-peeling `3 mod 8` tail color.
+-/
+theorem tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
+      orbitWindowResidueCountMod8EqThreeTail n k := by
+  rw [tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three]
+
 /--
 The shifted tail splits into exact height `1` and height at least `2`.
 
@@ -3833,6 +3905,38 @@ theorem orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
     | inr hSeven =>
         omega
 
+/--
+The shifted-tail exact-height-one reservoir splits into the delayed-peeling
+color `3 mod 8` and the continuing color `7 mod 8`.
+-/
+theorem tailHeightCountEq_one_split_mod8_three_seven
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountEqTail n k 1 =
+      orbitWindowResidueCountMod8EqThreeTail n k +
+        orbitWindowResidueCountMod8EqSevenTail n k := by
+  unfold orbitWindowHeightCountEqTail
+  unfold orbitWindowResidueCountMod8EqThreeTail
+  unfold orbitWindowResidueCountMod8EqSevenTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n (k + 1)
+      by_cases hheight : orbitWindowHeight n (k + 1) = 1
+      · cases hiff.mp hheight with
+        | inl hthree =>
+            simp [ih, hheight, hthree, Nat.add_assoc, Nat.add_comm]
+        | inr hseven =>
+            simp [ih, hheight, hseven, Nat.add_comm, Nat.add_left_comm]
+      · have hnotThree : oddOrbitLabel n (k + 1) % 8 ≠ 3 := by
+          intro hthree
+          exact hheight (hiff.mpr (Or.inl hthree))
+        have hnotSeven : oddOrbitLabel n (k + 1) % 8 ≠ 7 := by
+          intro hseven
+          exact hheight (hiff.mpr (Or.inr hseven))
+        simp [ih, hheight, hnotThree, hnotSeven]
+
 /--
 Orbit-level transition from the `3 mod 8` height-one channel.
 
@@ -4105,6 +4209,40 @@ theorem orbitWindowNextHeight_two_le_of_mod_eight_eq_three
   apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n (i + 1)).mpr
   exact oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n i hmod
 
+/--
+Every shifted-tail `3 mod 8` entry contributes a shifted-tail `height >= 2`
+entry one step later.
+
+The source side counts labels at times `1..k`; the target side counts heights
+at times `1..k+1`, so the delayed image fits into the one-step-longer tail
+window.
+-/
+theorem tailMod8Three_le_nextTailHeightCountGe_two
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThreeTail n k ≤
+      orbitWindowHeightCountGeTail n (k + 1) 2 := by
+  unfold orbitWindowResidueCountMod8EqThreeTail
+  unfold orbitWindowHeightCountGeTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ, List.range_succ]
+      have htransition :
+          oddOrbitLabel n (k + 1) % 8 = 3 →
+            2 ≤ orbitWindowHeight n ((k + 1) + 1) :=
+        orbitWindowNextHeight_two_le_of_mod_eight_eq_three n (k + 1)
+      by_cases hsource : oddOrbitLabel n (k + 1) % 8 = 3
+      · have htarget : 2 ≤ orbitWindowHeight n ((k + 1) + 1) :=
+          htransition hsource
+        simp [hsource, htarget]
+        omega
+      · by_cases htarget : 2 ≤ orbitWindowHeight n ((k + 1) + 1)
+        · simp [hsource, htarget]
+          omega
+        · simp [hsource, htarget]
+          omega
+
 /--
 The `7 mod 8` height-one channel remains an exact height-one channel at the
 next label.
@@ -4312,6 +4450,28 @@ theorem orbitWindowRecoveryMass_forces_tailRecovery
       orbitWindowRecoverySiblingMassPow2Tail n k r :=
   orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass r hr n k
 
+/--
+Source recovery mass at parent depth `3` lands in the shifted-tail delayed
+`3 mod 8` color.
+
+This is the recovery-side counterpart to the continuation-retention reservoir
+result: recovery does not land directly in `height >= 2` at this depth, but it
+does land in the color that peels on the next step.
+-/
+theorem sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRecoverySiblingMassPow2 n k 3 ≤
+      orbitWindowResidueCountMod8EqThreeTail n k := by
+  have hflow :
+      orbitWindowRecoverySiblingMassPow2 n k (2 + 1) ≤
+        orbitWindowRecoverySiblingMassPow2Tail n k 2 :=
+    orbitWindowRecoveryMass_forces_tailRecovery 2 (by omega) n k
+  have htail :
+      orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
+        orbitWindowResidueCountMod8EqThreeTail n k :=
+    tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three n k
+  simpa using le_trans hflow htail
+
 /--
 Count-level recursive Petal transition for the continuation sibling.
 
@@ -4465,6 +4625,23 @@ theorem sourceContinuationMass_depth_two_le_tailHeightCountEq_one
     tailRetentionMass_depth_two_le_heightCountEq_one n k
   simpa using le_trans hflow hheight
 
+/--
+Source continuation mass at parent depth `2` enters the shifted-tail
+exact-height-one reservoir, which splits into the delayed `3 mod 8` color and
+the continuing `7 mod 8` color.
+-/
+theorem sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
+    (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+      orbitWindowResidueCountMod8EqThreeTail n k +
+        orbitWindowResidueCountMod8EqSevenTail n k := by
+  have h :
+      orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+        orbitWindowHeightCountEqTail n k 1 :=
+    sourceContinuationMass_depth_two_le_tailHeightCountEq_one n k
+  rw [tailHeightCountEq_one_split_mod8_three_seven] at h
+  exact h
+
 /--
 Tail continuation sibling mass is definitionally the same as tail retention at
 the next depth.
@@ -5202,6 +5379,25 @@ theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
       (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k) (k + 1))
     (orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two n k)
 
+/--
+Tail-facing delayed-drift theorem from the shifted-tail `3 mod 8` channel.
+
+The shifted-tail `3 mod 8` color does not represent immediate extra peeling in
+the same tail window.  It contributes a `height >= 2` tail entry one step later,
+so it supplies an extra layer over the next accumulated window.
+-/
+theorem tailResidueCountMod8EqThree_delayed_drift
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
+      sumS n ((k + 1) + 1) := by
+  have htail :
+      orbitWindowResidueCountMod8EqThreeTail n k ≤
+        orbitWindowHeightCountGeTail n (k + 1) 2 :=
+    tailMod8Three_le_nextTailHeightCountGe_two n k
+  exact le_trans
+    (Nat.add_le_add_left htail (k + 1))
+    (orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n (k + 1))
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 9a3916b9..ffa9361e 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -149,6 +149,7 @@ docs/Collatz-CauseSideDepthDistribution-111.md
 docs/Collatz-CauseSideFrequencyAlias-112.md
 docs/Collatz-FrequencyHeightBridge-113.md
 docs/Collatz-TailFacingHeightBridge-114.md
+docs/Collatz-RecoveryDelayedBranch-115.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 241916cd..3532dbb5 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -794,6 +794,82 @@ So the next height-growth attempt should inspect the recovery sibling or a
 deeper delayed branch, rather than using depth-2 continuation retention as an
 extra-peeling source.
 
+## Recovery And Delayed Branch
+
+Checkpoint 115 follows the correction from checkpoint 114 and separates two
+different recovery readings.
+
+At parent depth `1`, shifted-tail recovery is the immediate extra-height cell:
+
+```lean
+tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
+tailRecoveryMass_depth_one_le_heightCountGe_two
+```
+
+At parent depth `2`, shifted-tail recovery is not the same object.  It is the
+`3 mod 8` color inside the exact-height-one reservoir:
+
+```lean
+tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
+tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
+```
+
+This is the main recovery correction:
+
+```text
+tail recovery, parent depth 1
+  -> 1 mod 4
+  -> immediate height >= 2
+
+tail recovery, parent depth 2
+  -> 3 mod 8
+  -> exact height 1 now
+  -> height >= 2 one step later
+```
+
+The exact-height-one reservoir is now split into its two visible colors:
+
+```lean
+tailHeightCountEq_one_split_mod8_three_seven
+```
+
+with reading:
+
+```text
+tail exact height 1
+  = tail 3 mod 8 delayed-peeling color
+    + tail 7 mod 8 continuing color
+```
+
+The delayed-peeling color has its own tail transition:
+
+```lean
+tailMod8Three_le_nextTailHeightCountGe_two
+tailResidueCountMod8EqThree_delayed_drift
+```
+
+Finally, the source-side checkpoint hooks are:
+
+```lean
+sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
+sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
+```
+
+The working model is no longer:
+
+```text
+pressure-heavy -> immediate extra peeling
+```
+
+It is:
+
+```text
+pressure or recovery channel
+  -> exact-height-one reservoir
+  -> 3 mod 8 / 7 mod 8 color split
+  -> the 3 mod 8 color supplies delayed extra peeling
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index ca0bf848..8b2611d6 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -309,6 +309,17 @@ tailRetentionMass_depth_two_le_heightCountEq_one
 sourceContinuationMass_le_tailRetentionMass
 sourceContinuationMass_le_tailSplitMass
 sourceContinuationMass_depth_two_le_tailHeightCountEq_one
+orbitWindowResidueCountMod8EqThreeTail
+orbitWindowResidueCountMod8EqSevenTail
+tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
+tailRecoveryMass_depth_one_le_heightCountGe_two
+tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
+tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
+tailHeightCountEq_one_split_mod8_three_seven
+tailMod8Three_le_nextTailHeightCountGe_two
+sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
+sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
+tailResidueCountMod8EqThree_delayed_drift
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md
new file mode 100644
index 00000000..266ed615
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md
@@ -0,0 +1,155 @@
+# Collatz Recovery Delayed Branch 115
+
+Checkpoint 115 revisits the extra-peeling question after checkpoint 114.
+
+Checkpoint 114 ruled out the tempting shortcut:
+
+```text
+source continuation at parent depth 2
+  -> shifted-tail height >= 2
+```
+
+The actual result was weaker and more precise:
+
+```text
+source continuation at parent depth 2
+  -> shifted-tail exact height 1
+```
+
+Checkpoint 115 asks where the missing extra peeling goes.
+
+## Main Correction
+
+The recovery channel has two different low-depth readings.
+
+At parent depth `1`, shifted-tail recovery is immediate extra peeling:
+
+```lean
+tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
+tailRecoveryMass_depth_one_le_heightCountGe_two
+```
+
+This is the ordinary `1 mod 4` tail cell, which is equivalent to
+`height >= 2`.
+
+At parent depth `2`, shifted-tail recovery is not `1 mod 4`.  It is:
+
+```lean
+tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
+tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
+```
+
+So the parent-depth-2 recovery channel is the `3 mod 8` delayed-peeling color
+inside the exact-height-one reservoir.
+
+## Exact-Height-One Reservoir
+
+The shifted-tail exact-height-one reservoir is now split into two visible
+colors:
+
+```lean
+orbitWindowResidueCountMod8EqThreeTail
+orbitWindowResidueCountMod8EqSevenTail
+tailHeightCountEq_one_split_mod8_three_seven
+```
+
+Conceptually:
+
+```text
+tail exact height 1
+  = tail 3 mod 8
+    + tail 7 mod 8
+```
+
+The two colors have different dynamical meanings:
+
+```text
+3 mod 8
+  delayed-peeling color
+
+7 mod 8
+  continuing color
+```
+
+## Delayed Peeling
+
+The `3 mod 8` tail color contributes to `height >= 2` one step later:
+
+```lean
+tailMod8Three_le_nextTailHeightCountGe_two
+```
+
+The accumulated-height form is:
+
+```lean
+tailResidueCountMod8EqThree_delayed_drift
+```
+
+This says that the shifted-tail `3 mod 8` count supplies an extra layer in the
+next accumulated `sumS` window.
+
+## Source-Side Hooks
+
+Checkpoint 115 also provides two source-facing bridges.
+
+Source recovery at parent depth `3` lands in the delayed `3 mod 8` tail color:
+
+```lean
+sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
+```
+
+Source continuation at parent depth `2` lands in the exact-height-one reservoir,
+and the reservoir splits into the delayed and continuing colors:
+
+```lean
+sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
+```
+
+## Current Working Model
+
+The model has shifted from immediate peeling to delayed reservoir flow.
+
+Old expectation:
+
+```text
+pressure-heavy channel
+  -> immediate extra height
+```
+
+Current theorem-supported reading:
+
+```text
+pressure or recovery channel
+  -> exact-height-one reservoir
+  -> 3 mod 8 / 7 mod 8 color split
+  -> 3 mod 8 supplies extra peeling one step later
+```
+
+This is still a finite, natural-valued observation.  It does not prove global
+Collatz convergence.  It gives a sharper local channel grammar for future
+finite-window arguments.
+
+## Next Targets
+
+The next useful questions are:
+
+```text
+1. Can the 7 mod 8 continuing color be split at mod 16?
+
+2. Can repeated continuing colors be organized as a finite delayed-reservoir
+   tower?
+
+3. Can a pressure-heavy depth range force enough delayed 3 mod 8 mass to
+   improve the global sumS lower bound?
+```
+
+The likely next Lean layer is a reusable recursive color split:
+
+```text
+tail exact height 1 at resolution 2^r
+  -> delayed-peeling color
+  -> continuing color
+```
+
+This should be attempted only after the low-depth `3 mod 8` / `7 mod 8`
+surface remains stable under review.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-115.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-115.md
new file mode 100644
index 00000000..172915fd
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-115.md
@@ -0,0 +1,230 @@
+# Report Petal 115: Recovery Delayed Branch
+
+## Summary
+
+Checkpoint 115 rechecked the route toward extra peeling after checkpoint 114.
+
+The important recovery result is not:
+
+```text
+tail recovery at parent depth 2 -> immediate height >= 2
+```
+
+The theorem-supported correction is:
+
+```text
+tail recovery at parent depth 1 -> immediate height >= 2
+tail recovery at parent depth 2 -> delayed 3 mod 8 color
+```
+
+Thus the extra-peeling channel exists, but at parent depth `2` it is delayed by
+one step.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New shifted-tail color counts:
+
+```lean
+orbitWindowResidueCountMod8EqThreeTail
+orbitWindowResidueCountMod8EqSevenTail
+```
+
+Immediate recovery at parent depth `1`:
+
+```lean
+tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
+tailRecoveryMass_depth_one_le_heightCountGe_two
+```
+
+Delayed recovery at parent depth `2`:
+
+```lean
+tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
+tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
+```
+
+Exact-height-one reservoir split:
+
+```lean
+tailHeightCountEq_one_split_mod8_three_seven
+```
+
+Delayed tail extra-height bridge:
+
+```lean
+tailMod8Three_le_nextTailHeightCountGe_two
+tailResidueCountMod8EqThree_delayed_drift
+```
+
+Source-side hooks:
+
+```lean
+sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
+sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
+```
+
+## Main Mathematical Reading
+
+The checkpoint converts the vague phrase "continuation pressure may create
+extra peeling" into a more precise finite channel grammar.
+
+Checkpoint 114:
+
+```text
+source continuation at parent depth 2
+  -> tail exact height 1
+```
+
+Checkpoint 115:
+
+```text
+tail exact height 1
+  = tail 3 mod 8 + tail 7 mod 8
+```
+
+Then:
+
+```text
+tail 3 mod 8
+  -> next tail height >= 2
+  -> delayed contribution to sumS
+```
+
+The current theorem-level reading is:
+
+```text
+pressure or recovery channel
+  -> exact-height-one reservoir
+  -> color split
+  -> delayed extra peeling from the 3 mod 8 color
+```
+
+## Corrected Expectations
+
+The proposed theorem
+
+```lean
+tailRecoveryMass_depth_two_le_heightCountGe_two
+```
+
+is not the right local target.  At parent depth `2`, tail recovery is the
+`3 mod 8` cell, which is exact height `1` at the current tail index.
+
+The valid immediate theorem is instead:
+
+```lean
+tailRecoveryMass_depth_one_le_heightCountGe_two
+```
+
+The valid delayed theorem is:
+
+```lean
+tailMod8Three_le_nextTailHeightCountGe_two
+```
+
+and its accumulated-height version:
+
+```lean
+tailResidueCountMod8EqThree_delayed_drift
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-RecoveryDelayedBranch-115.md
+```
+
+The new public note records the distinction:
+
+```text
+parent depth 1 recovery = immediate extra peeling
+parent depth 2 recovery = delayed 3 mod 8 color
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
+### 1. Split the continuing color
+
+The next natural experiment is to split the continuing color:
+
+```text
+tail 7 mod 8
+  -> tail 7 mod 16 / tail 15 mod 16
+```
+
+and identify which child becomes delayed-peeling at the next resolution.
+
+### 2. Build a recursive delayed-reservoir tower
+
+The low-resolution pattern suggests a reusable finite grammar:
+
+```text
+continuing reservoir at resolution 2^r
+  -> delayed-peeling child
+  -> continuing child
+```
+
+This should be attempted as a thin theorem family only after the `3 mod 8` /
+`7 mod 8` checkpoint is accepted.
+
+### 3. Connect pressure-heavy ranges to delayed mass
+
+The current bridge still does not prove that pressure-heavy depth ranges
+produce enough `3 mod 8` mass.  A future theorem should connect:
+
+```text
+sourceContinuationPressureOnRange
+```
+
+or the cause-side outruns vocabulary to:
+
+```text
+orbitWindowResidueCountMod8EqThreeTail
+```
+
+or to the recursive delayed-reservoir tower.
+
+That is the likely next route from local channel grammar back to `sumS`
+growth.
````
`````
