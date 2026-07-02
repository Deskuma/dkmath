# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 31aee0e748262e3be06dda4d019463d261d157a0

## Report

Checkpoint 114 完了です。今回は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) で tail-facing height bridge を実験し、重要な補正結果が出ました。

追加した Lean 名:

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass

tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
```

当初狙っていた

```text
source continuation mass
  -> tail height >= 2
  -> sumS lower bound
```

は、この depth では成立しない方向でした。Lean 上で正しく見えた構造は、

```text
source continuation mass at parent depth 2
  -> tail retention depth 2
  -> tail 3 mod 4
  -> tail exact height 1
```

です。つまり continuation-retention channel はこの層では「追加 peeling」ではなく「base retention / exact height 1」側に入ります。これは偽方向を早めに切れたので、かなり有用な checkpoint です。

ドキュメントも同期済みです。新規に [Collatz-TailFacingHeightBridge-114.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md) と [report-petal-114.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-114.md) を追加し、README / Guide / Status も更新しました。

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

すべて通過。`PetalBridge.lean` に `sorry` はありません。統合ビルド中の `ZsigmondyCyclotomicResearch.lean:152:6 uses sorry` は既知の upstream warning です。

次は recovery-side extra-height bridge を見るのが自然です。`source recovery sibling mass -> tail recovery sibling -> tail height >= 2` が成立するか、あるいは delayed continuation branch を追うのが次の候補です。

## Review

## 1. 状況分析

checkpoint `114` は、かなり重要な **補正 checkpoint** じゃ。

当初の狙いは、

```text
source continuation mass
  -> tail retention
  -> tail height >= 2
  -> sumS lower bound
```

だった。

しかし Lean が示した安全な構造は違った。

```text
source continuation mass at parent depth 2
  -> tail retention depth 2
  -> tail 3 mod 4
  -> tail exact height 1
```

つまり、今回の checkpoint は「extra peeling へ進む橋」を得たのではなく、**continuation-retention channel はこの層では extra height ではなく exact height 1 側に入る**ことを確定した回じゃ。報告でも、これは偽方向を早めに切れた有用な checkpoint と整理されている。

これは深い。
単なる失敗ではない。
むしろ、Collatz.PetalBridge の流れの中で、どの channel が「降下燃料」ではなく「遅延・滞留層」なのかが定理として見えた。

## 2. 今回の核心

追加された主な定理はこれ。

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass

tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
```

核心は特にこれ。

```lean
tailRetentionMass_depth_two_eq_heightCountEq_one
```

これは、

```text
tail retention depth 2 = tail exact height 1
```

を言っている。

つまり depth `2` の tail retention は、

```text
tail height >= 2
```

ではなく、

```text
tail height = 1
```

に入る。

これは `sumS` 下界を増やす側ではなく、基礎 peeling 一回で止まる側じゃ。

## 3. 深い推論：これは「失敗」ではなく channel 分解の発見

ここで大事なのは、`exact height 1` は Collatz 的には無意味ではない、ということじゃ。

odd step の height は最低でも 1 ある。
だから exact height 1 は「基礎剥離」ではある。

しかし、extra drift に欲しいのは、

```text
height >= 2
```

つまり「基礎の一回に加えて、さらに剥がれる」こと。

今回わかったのは、

```text
source continuation mass at depth 2
```

は、すぐには extra peeling を生まない。
それは tail 側で exact height 1 に入る。

言い換えると、

```text
continuation-retention channel は即時降下ではなく、遅延状態を作る
```

ということじゃ。

これは、直感的にはかなり Collatz らしい。

```text
上がったように見える branch が、すぐには落ちない。
しかし exact height 1 として次の odd core へ送られる。
そこでさらに residue が分かれる。
```

つまり今回見えたものは、**即時 drift ではなく delayed drift の入口** じゃ。

## 4. residue の読み替え

今回の定理は、こう読める。

```text
tail retention depth 2
  = 3 mod 4
  = exact height 1
```

一方で、

```text
tail height >= 2
  = 1 mod 4
```

だから、`3 mod 4` に入った時点では extra peeling ではない。

しかし、ここで止めてはいけない。
`3 mod 4` はさらに `mod 8` で二つに分かれる。

```text
3 mod 4
  = 3 mod 8
  or
  = 7 mod 8
```

ここが次の分岐点じゃ。

実際、奇数 \(q\) に対して exact height 1 の後の odd core は、

$$
T(q)=\frac{3q+1}{2}
$$

である。

もし \(q\equiv 3\pmod 8\) なら、

$$
q=8a+3,\quad T(q)=12a+5\equiv 1\pmod 4
$$

したがって次は height \(\ge 2\) 側へ入る。

一方、\(q\equiv 7\pmod 8\) なら、

$$
q=8a+7,\quad T(q)=12a+11\equiv 3\pmod 4
$$

なので exact height 1 側に残る。

つまり、

```text
3 mod 8:
  delayed extra peeling

7 mod 8:
  delayed continuation
```

という分解になる。

ここが深い。
今回の `tail exact height 1` は終点ではなく、**次の delayed split の母集団** じゃ。

## 5. 数学的意味

今回の補正によって、次のことが見えた。

```text
continuation mass は、すぐには height >= 2 を生まない。
しかし exact height 1 の tail 状態を作る。
その exact height 1 状態は、mod 8 で delayed peeling と delayed continuation に分岐する。
```

これは DkMath 的にはかなり良い。

いままでの pressure / continuation / outruns は、「悪いもの」や「失敗」と見えがちだった。

しかし今回の結果で、より精密にはこう言える。

```text
continuation は即時降下ではない。
continuation は delayed branch を作る。
その delayed branch の中に、次段で height >= 2 へ落ちる色が含まれる。
```

これは、さっき話していた **一色線** の直感にも合う。

`3 mod 4` はまだ一色ではない。
`3 mod 8` と `7 mod 8` という二色に分かれている。

そのうち `3 mod 8` は次に \(1 \mod 4\) へ移り、extra peeling 側に染まる。
`7 mod 8` はまだ exact height 1 に残る。

つまり色が減る／揃う過程を、Lean の residue theorem として追える可能性が出てきた。

## 6. レビュー

## 6.1. 偽ルートを API に入れなかったのが非常に良い

今回一番良いのは、誤った theorem を無理に作らなかったことじゃ。

当初の誘惑は、

```text
source continuation mass at depth 2
  -> tail height >= 2
```

だった。

だが実際には、

```text
source continuation mass at depth 2
  -> tail exact height 1
```

だった。

ここで無理に `sumS` 下界へ接続していたら、後で危ない drift argument になっていた。
Lean が「そこは違う」と教えてくれた。

これは本当に価値が高い。

## 6.2. `tailRetentionMass_depth_two_eq_heightCountEq_one` は強い

不等式ではなく equality として入ったのが良い。

```lean
tailRetentionMass_depth_two_eq_heightCountEq_one
```

これにより、この channel の意味が完全に固定された。

```text
tail retention depth 2 は exact height 1 である
```

曖昧さがない。

これは今後の探索で、

```text
この channel に extra height を期待してはいけない
```

という安全柵になる。

## 6.3. meaning-name alias も良い

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass
```

は、既存 theorem の意味名 alias として良い。

特にこの段階では theorem 名が増えても、意味で読めることが重要じゃ。

```text
source continuation mass が tail のどこへ行くのか
```

が名前で見える。

これは後続の recovery / delayed branch 実験で効いてくる。

## 7. まだ閉じていないもの

まだ閉じていない本命は、

```text
extra peeling を生む channel はどれか
```

じゃ。

今回わかったのは、

```text
depth-2 continuation retention は違う
```

ということ。

次に見るべき候補は二つ。

```text
1. recovery-side extra-height bridge

2. delayed continuation branch
```

特に delayed branch はかなり有力じゃ。

なぜなら今回の exact height 1 は、

```text
3 mod 4
```

であり、その内部に

```text
3 mod 8
```

が含まれるから。

そして `3 mod 8` は、次 step で \(1 \mod 4\) に入る。
これは delayed peeling の典型形じゃ。

## 8. 次の指示

次 checkpoint は二方面で攻めるのが良い。

## 8.1. 第一候補：recovery-side extra-height bridge

まずは recovery sibling が tail height \(\ge 2\) へ入るか確認する。

狙いはこう。

```text
source recovery sibling mass
  -> tail recovery sibling
  -> tail residue 1 mod 4
  -> tail height >= 2
```

Lean 実験候補：

```lean
theorem tailRecoveryMass_depth_two_le_heightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  -- tail recovery depth 2 が mod4 = 1 側なら通る
  -- orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one を使う
  sorry
```

これが通るなら、次は source recovery から tail recovery への flow を探す。

```lean
theorem sourceRecoveryMass_depth_two_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k 2 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  -- source recovery -> tail recovery の bridge があれば合成
  sorry
```

これは本命候補じゃ。

## 8.2. 第二候補：delayed continuation branch

今回の result から、continuation-retention は exact height 1 へ入る。
だから、次 step を見る。

狙いは、

```text
tail exact height 1
  -> split into mod8 = 3 / mod8 = 7
```

そして、

```text
mod8 = 3
  -> next tail height >= 2
```

既に report に出ている既存 theorem 名が重要じゃ。

```lean
orbitWindowResidueCountMod8EqThree_delayed_drift
```

これを中心に見るべき。

候補補題：

```lean
theorem tailHeightEqOne_mod8_three_delayed_heightGeTwo
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThreeTail n k ≤
      orbitWindowHeightCountGeTail n (k + 1) 2 := by
  -- 既存 delayed_drift theorem の向きに合わせる
  sorry
```

実際の index は既存 theorem に合わせる必要がある。
ただし、方向性はこれ。

```text
exact height 1 の中の 3 mod 8 成分は、次 step の height >= 2 に変わる
```

## 9. 一歩先ゆく推論

ここで、今後の設計が少し変わる。

これまでは、

```text
pressure-heavy
  -> immediate extra height
```

を期待していた。

しかし今回の結果により、より正確には、

```text
pressure-heavy
  -> exact height 1 reservoir
  -> delayed split
  -> some part becomes extra height
```

という構造になる。

つまり pressure は直接の降下ではなく、**delayed reservoir** を作る。

この reservoir が `3 mod 8` と `7 mod 8` に分かれる。
`3 mod 8` は次で落ちる。
`7 mod 8` はさらに continuation する。

この流れは、まさに色分けじゃ。

```text
3 mod 4 reservoir:
  色A: 3 mod 8 -> next extra peeling
  色B: 7 mod 8 -> delayed continuation
```

さらに `7 mod 8` も次の解像度では `7 mod 16` / `15 mod 16` などへ分かれていく可能性がある。

つまり Collatz.PetalBridge の今後の本質は、

```text
exact height 1 reservoir の中で、
どれだけの色が delayed peeling 側へ移るか
```

を見ることになる。

これはかなり深い。
`continuation` を失敗と見るのではなく、**解像度を上げる reservoir** と見るべきじゃ。

## 10. Gnomon / 一色線との接続

ここで、さっきの Gnomon 視点にも繋がる。

今回の continuation-retention channel は、

```text
Gnomon 層を足したあと、すぐに 2^n の一色線へ乗ったわけではない
```

状態じゃ。

ただし完全にバラバラでもない。

```text
3 mod 4
```

という大きな色には揃った。

でもまだ、

```text
3 mod 8
7 mod 8
```

という二色が残っている。

そのうち `3 mod 8` は次に \(1 \mod 4\) へ進み、一色線側へ近づく。
`7 mod 8` はまだ色を残す。

つまり、今後見るべきものは、

```text
色数がどう減るか
```

じゃ。

これは DkMath 的にはかなり良い解釈になる。

```text
continuation:
  色が残る

recovery:
  色が減る

delayed drift:
  次 step で色が減る

exact height 1:
  基礎 peeling だけで、色の分解を次へ送る
```

## 11. 賢狼が試して欲しい実験補題

## 実験 A: tail recovery depth 2 が height >= 2 側か確認

```lean
theorem tailRecoveryMass_depth_two_le_heightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  -- まず unfold して tail recovery depth 2 の residue を確認
  -- それが mod4 = 1 なら:
  -- rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]
  sorry
```

## 実験 B: tail recovery depth 2 の residue equality

まずはこちらを直接作るのが安全。

```lean
theorem tailRecoveryMass_depth_two_eq_tailResidueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 2 =
      orbitWindowResidueCountMod4EqOneTail n k := by
  -- unfold orbitWindowRecoverySiblingMassPow2Tail
  -- unfold orbitWindowResidueCountPow2Tail
  -- unfold orbitWindowResidueCountMod4EqOneTail
  -- simp
  sorry
```

これが通れば、実験 A はほぼ `rw` で通るはず。

## 実験 C: source recovery mass から tail recovery mass への bridge

既存に似た theorem がないか検索。

```text
rg "Recovery.*tail" DkMath/Collatz/PetalBridge.lean
rg "recovery.*Tail" DkMath/Collatz/PetalBridge.lean
rg "RecoverySiblingMassPow2Tail" DkMath/Collatz/PetalBridge.lean
```

候補 theorem 形：

```lean
theorem sourceRecoveryMass_le_tailRecoveryMass
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) := by
  -- 既存 flow theorem があれば alias
  sorry
```

## 実験 D: source recovery depth 2 to tail height >= 2

実験 A/C が通ったら合成。

```lean
theorem sourceRecoveryMass_depth_two_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k 2 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  have hflow :
      orbitWindowRecoverySiblingMassPow2 n k 2 ≤
        orbitWindowRecoverySiblingMassPow2Tail n k 2 := by
    -- sourceRecoveryMass_le_tailRecoveryMass 1 ...
    sorry
  have hheight :
      orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
        orbitWindowHeightCountGeTail n k 2 :=
    tailRecoveryMass_depth_two_le_heightCountGe_two n k
  exact le_trans hflow hheight
```

## 実験 E: tail exact height 1 を mod8 に分解

今回得た exact height 1 をさらに分解する。

```lean
theorem tailHeightCountEq_one_split_mod8_three_seven
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 =
      orbitWindowResidueCountMod8EqThreeTail n k +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  -- exact height 1 iff mod8 = 3 or 7 の tail count 版
  sorry
```

これは既に似たものがある可能性が高い。
なければ重要。

## 実験 F: source continuation depth 2 を delayed split へ送る

今回の theorem と実験 E を合わせたい。

```lean
theorem sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
    (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      orbitWindowResidueCountMod8EqThreeTail n k +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  have h :
      orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        orbitWindowHeightCountEqTail n k 1 :=
    sourceContinuationMass_depth_two_le_tailHeightCountEq_one n k
  -- rw [tailHeightCountEq_one_split_mod8_three_seven] at h
  -- exact h
  sorry
```

## 実験 G: mod8 = 3 delayed drift を height >= 2 へ送る

既存の `orbitWindowResidueCountMod8EqThree_delayed_drift` を使う。

```lean
theorem tailMod8Three_le_nextTailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThreeTail n k ≤
      orbitWindowHeightCountGeTail n (k + 1) 2 := by
  -- orbitWindowResidueCountMod8EqThree_delayed_drift の実際の型に合わせる
  sorry
```

ここが delayed route の本命。

## 実験 H: delayed branch から sumS 下界

```lean
theorem heightSeq_sum_ge_window_add_tailMod8Three
    (n : OddNat) (k : ℕ) :
    k + orbitWindowResidueCountMod8EqThreeTail n k ≤
      (orbitWindowHeightSeq n (k + 1)).sum := by
  have htail :
      orbitWindowResidueCountMod8EqThreeTail n k ≤
        orbitWindowHeightCountGeTail n k 2 := by
    -- delayed theorem の index 次第
    sorry
  have hsum :=
    orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n k
  omega
```

index が `k+1` なのか `k+2` なのかは既存 theorem の型確認が必要。
ここは慎重に。

## 12. 次コミットの推奨順

```text
1. tail recovery depth 2 の residue を unfold で確認

2. 通るなら:
   tailRecoveryMass_depth_two_eq_tailResidueCount_mod4_eq_one

3. それを:
   tailRecoveryMass_depth_two_le_heightCountGe_two
   に接続

4. source recovery -> tail recovery flow theorem を検索

5. あれば:
   sourceRecoveryMass_depth_two_le_tailHeightCountGe_two

6. 並行して:
   tailHeightCountEq_one_split_mod8_three_seven
   を探す / 作る

7. 既存:
   orbitWindowResidueCountMod8EqThree_delayed_drift
   の型を確認

8. delayed continuation route を:
   mod8 three -> future height >= 2
   へ接続
```

## 13. 総括

checkpoint `114` は、表面上は狙いが外れたように見える。
しかし中身は非常に重要じゃ。

今回わかったのは、

$$
\text{source continuation mass at depth 2}\Longrightarrow\text{tail exact height 1}
$$

であって、

$$
\text{source continuation mass at depth 2}\Longrightarrow\text{tail height}\ge 2
$$

ではない、ということ。

これは悪い知らせではない。
むしろ、channel の正体が見えた。

```text
continuation-retention channel:
  immediate extra peeling ではない
  exact height 1 reservoir である
```

この reservoir は `3 mod 4`。
さらに `3 mod 8` と `7 mod 8` に分かれる。
`3 mod 8` は delayed extra peeling 側。
`7 mod 8` は delayed continuation 側。

したがって次の本命は、

```text
recovery-side extra-height bridge
```

または、

```text
exact height 1 reservoir の delayed split
```

じゃ。

うむ。
ここは深い。Lean が「その道は違う」と言ったことで、むしろ次の正しい道が見えた。
次は **recovery sibling** と **mod8 delayed branch** を調べる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index df4fa628..88860ab2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -3738,6 +3738,38 @@ theorem orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
           exact hheight (hiff.mpr h)
         simp [ih, hheight, hres]
 
+/--
+At depth `2`, shifted-tail retention is exactly the shifted-tail `3 mod 4`
+cell, hence it is the same mass as the tail exact-height-one count.
+
+This is the safe tail-facing height bridge for the continuation-retention
+channel.  It also records why the tempting `height >= 2` target is the wrong
+one at this depth.
+-/
+theorem tailRetentionMass_depth_two_eq_heightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRetentionMassPow2Tail n k 2 =
+      orbitWindowHeightCountEqTail n k 1 := by
+  have htail :
+      orbitWindowRetentionMassPow2Tail n k 2 =
+        orbitWindowResidueCountMod4EqThreeTail n k := by
+    unfold orbitWindowRetentionMassPow2Tail
+    unfold orbitWindowResidueCountPow2Tail
+    unfold orbitWindowResidueCountMod4EqThreeTail
+    simp
+  rw [htail]
+  rw [← orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]
+
+/--
+At depth `2`, shifted-tail retention is bounded by the tail exact-height-one
+count.
+-/
+theorem tailRetentionMass_depth_two_le_heightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowRetentionMassPow2Tail n k 2 ≤
+      orbitWindowHeightCountEqTail n k 1 := by
+  rw [tailRetentionMass_depth_two_eq_heightCountEq_one]
+
 /--
 The shifted tail splits into exact height `1` and height at least `2`.
 
@@ -4389,6 +4421,50 @@ theorem orbitWindowContinuationMass_tailBudget
         orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
   orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k
 
+/--
+Meaning-name alias for the continuation-to-tail-retention channel.
+
+At parent depth `r + 1`, source continuation mass lands inside shifted-tail
+retention at the same depth.
+-/
+theorem sourceContinuationMass_le_tailRetentionMass
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
+  orbitWindowContinuationMass_forces_tailRetention r hr n k
+
+/--
+Meaning-name alias for the shifted-tail split budget of source continuation
+mass.
+-/
+theorem sourceContinuationMass_le_tailSplitMass
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
+      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
+        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
+  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k
+
+/--
+Source continuation mass at parent depth `2` lands inside the shifted-tail
+exact-height-one count.
+
+This is the corrected direct source-continuation-mass to tail-height bridge:
+the continuation-retention channel feeds `3 mod 4`, not `1 mod 4`.
+-/
+theorem sourceContinuationMass_depth_two_le_tailHeightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k 2 ≤
+      orbitWindowHeightCountEqTail n k 1 := by
+  have hflow :
+      orbitWindowContinuationSiblingMassPow2 n k (1 + 1) ≤
+        orbitWindowRetentionMassPow2Tail n k (1 + 1) :=
+    sourceContinuationMass_le_tailRetentionMass 1 (by omega) n k
+  have hheight :
+      orbitWindowRetentionMassPow2Tail n k 2 ≤
+        orbitWindowHeightCountEqTail n k 1 :=
+    tailRetentionMass_depth_two_le_heightCountEq_one n k
+  simpa using le_trans hflow hheight
+
 /--
 Tail continuation sibling mass is definitionally the same as tail retention at
 the next depth.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 030e3944..9a3916b9 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -148,6 +148,7 @@ docs/Collatz-CauseSideFailureCount-110.md
 docs/Collatz-CauseSideDepthDistribution-111.md
 docs/Collatz-CauseSideFrequencyAlias-112.md
 docs/Collatz-FrequencyHeightBridge-113.md
+docs/Collatz-TailFacingHeightBridge-114.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 460b955f..241916cd 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -750,6 +750,50 @@ orbitWindowHeightCountGe n k 2
 orbitWindowHeightCountGeTail n k 2
 ```
 
+## Tail-Facing Height Bridge
+
+Checkpoint 114 tests the expected bridge from source continuation mass to tail
+height counts.
+
+The meaning-name aliases are:
+
+```lean
+sourceContinuationMass_le_tailRetentionMass
+sourceContinuationMass_le_tailSplitMass
+```
+
+The experiment showed an important correction.  At parent depth `2`, source
+continuation mass lands in shifted-tail retention depth `2`; this is the
+`3 mod 4` tail cell, hence exact height `1`, not height at least `2`.
+
+The theorem-level bridge is:
+
+```lean
+tailRetentionMass_depth_two_eq_heightCountEq_one
+tailRetentionMass_depth_two_le_heightCountEq_one
+sourceContinuationMass_depth_two_le_tailHeightCountEq_one
+```
+
+This rules out the tempting route:
+
+```text
+source continuation mass at depth 2
+  -> tail height >= 2
+  -> extra sumS lower bound
+```
+
+The correct reading is:
+
+```text
+source continuation mass at depth 2
+  -> tail exact height 1
+  -> base retention / no extra peeling at this layer
+```
+
+So the next height-growth attempt should inspect the recovery sibling or a
+deeper delayed branch, rather than using depth-2 continuation retention as an
+extra-peeling source.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index f3d83782..ca0bf848 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -304,6 +304,11 @@ sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
 tailPressureDepthCount_pos_of_outrunsMoreThanHalf
 sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
 tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+tailRetentionMass_depth_two_eq_heightCountEq_one
+tailRetentionMass_depth_two_le_heightCountEq_one
+sourceContinuationMass_le_tailRetentionMass
+sourceContinuationMass_le_tailSplitMass
+sourceContinuationMass_depth_two_le_tailHeightCountEq_one
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md
new file mode 100644
index 00000000..c806765d
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md
@@ -0,0 +1,147 @@
+# Collatz Tail-Facing Height Bridge 114
+
+## Purpose
+
+Checkpoint 114 tests the first direct bridge from source continuation mass to
+tail height counts.
+
+The initial target was:
+
+```text
+source continuation mass
+  -> tail retention
+  -> tail height >= 2
+  -> sumS lower bound
+```
+
+Lean showed that the middle interpretation needs correction.
+
+At parent depth `2`, source continuation mass flows into shifted-tail retention
+depth `2`.  That cell is:
+
+```text
+3 mod 4
+```
+
+and therefore corresponds to:
+
+```text
+tail exact height 1
+```
+
+not:
+
+```text
+tail height >= 2
+```
+
+## Meaning-Name Aliases
+
+The checkpoint adds readable aliases for existing mass-flow theorems:
+
+```lean
+sourceContinuationMass_le_tailRetentionMass
+sourceContinuationMass_le_tailSplitMass
+```
+
+These preserve the existing theorem order and make future arguments easier to
+read.
+
+## Correct Tail Height Bridge
+
+The safe bridge is:
+
+```lean
+tailRetentionMass_depth_two_eq_heightCountEq_one
+tailRetentionMass_depth_two_le_heightCountEq_one
+sourceContinuationMass_depth_two_le_tailHeightCountEq_one
+```
+
+The mathematical reading is:
+
+```text
+source continuation mass at parent depth 2
+  -> shifted-tail retention at depth 2
+  -> shifted-tail 3 mod 4
+  -> shifted-tail exact height 1
+```
+
+This is a retention/base-layer result, not an extra-peeling result.
+
+## Ruled-Out Route
+
+The tempting route was:
+
+```text
+source continuation mass at parent depth 2
+  -> shifted-tail height >= 2
+  -> k + continuationMass <= sumS n (k + 1)
+```
+
+This route is not correct at depth `2`.
+
+The reason is the residue:
+
+```text
+tail retention depth 2 = 3 mod 4
+```
+
+while:
+
+```text
+tail height >= 2 = 1 mod 4
+```
+
+So this checkpoint does not produce a new extra `sumS` lower bound.  It
+clarifies which tail side the continuation-retention channel occupies.
+
+## Consequence
+
+Checkpoint 114 redirects the next search.
+
+To obtain extra height, the likely routes are:
+
+```text
+3 mod 8 delayed-peeling source
+recovery sibling channels
+deeper continuation branches that later move into a peeling cell
+```
+
+The already-proved theorem:
+
+```lean
+orbitWindowResidueCountMod8EqThree_delayed_drift
+```
+
+is still the model: find a source channel that maps into shifted-tail
+`height >= 2`, then consume:
+
+```lean
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+```
+
+## Next Candidate
+
+The next checkpoint should inspect recovery-side or delayed continuation
+channels.
+
+Candidate search:
+
+```text
+source recovery mass
+  -> tail recovery sibling
+  -> tail residue 1 mod 4?
+  -> tail height >= 2?
+```
+
+or:
+
+```text
+deeper continuation residue
+  -> exact height 1 now
+  -> delayed transition later
+  -> eventual height >= 2
+```
+
+The important outcome of checkpoint 114 is that depth-2 continuation retention
+is not the extra-peeling bridge.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-114.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-114.md
new file mode 100644
index 00000000..33e23414
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-114.md
@@ -0,0 +1,130 @@
+# Report Petal 114
+
+## Summary
+
+Checkpoint 114 tested the tail-facing height bridge from source continuation
+mass.
+
+The expected route was:
+
+```text
+continuation mass
+  -> tail retention
+  -> tail height >= 2
+  -> sumS lower bound
+```
+
+The experiment found a correction:
+
+```text
+source continuation mass at parent depth 2
+  -> tail retention depth 2
+  -> tail exact height 1
+```
+
+So the direct extra-peeling bridge at this depth is false in the intended
+direction.
+
+## Lean Additions
+
+Meaning-name aliases:
+
+```lean
+sourceContinuationMass_le_tailRetentionMass
+sourceContinuationMass_le_tailSplitMass
+```
+
+Correct tail height bridge:
+
+```lean
+tailRetentionMass_depth_two_eq_heightCountEq_one
+tailRetentionMass_depth_two_le_heightCountEq_one
+sourceContinuationMass_depth_two_le_tailHeightCountEq_one
+```
+
+## Important Negative Finding
+
+The review suggested testing:
+
+```text
+tail retention depth 1 or continuation depth zero
+  -> tail residue mod4 = 1
+  -> tail height >= 2
+```
+
+The actual residue arithmetic shows the safe nearby bridge is different:
+
+```text
+tail retention depth 2 = 3 mod 4 = exact height 1
+```
+
+Therefore this checkpoint does not add:
+
+```lean
+sumS_ge_window_add_sourceContinuationMass_depth_two
+```
+
+That statement would use the wrong tail height side.
+
+## Mathematical Reading
+
+The continuation-retention channel is a base-retention channel at this layer.
+It preserves an exact height-one tail state rather than forcing extra peeling.
+
+This is useful because it prevents a bad drift argument from entering the API.
+The next extra-height bridge should instead look at:
+
+```text
+3 mod 8 delayed-peeling source
+recovery sibling channels
+deeper delayed continuation branches
+```
+
+## Documentation Updates
+
+Updated:
+
+```text
+DkMath/Collatz/README.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+DkMath/Collatz/docs/Collatz-TailFacingHeightBridge-114.md
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
+git diff --check
+```
+
+The no-sorry check returned no matches in `DkMath/Collatz/PetalBridge.lean`.
+
+```text
+Known upstream warning during the integration build:
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 uses sorry.
+```
+
+## Next Candidate
+
+The next checkpoint should inspect a recovery-side extra-height bridge.
+
+Candidate:
+
+```text
+source recovery sibling mass
+  -> tail recovery sibling
+  -> tail height >= 2, if the residue is 1 mod 4
+```
+
+If that route fails, the next likely candidate is a delayed continuation
+branch, following the existing `3 mod 8` delayed-drift pattern.
````
`````
