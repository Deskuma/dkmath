# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 26da0f450d362881f9c1178722b0c7287b49705e

## Report

Checkpoint 113 完了です。今回は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) で、cause-side frequency から height/drift 側へ渡す前半の bridge API を追加しました。

追加した主な Lean 名:

```lean
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
tailPressureMoreThanHalf_of_outrunsMoreThanHalf

sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf

sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf

sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
```

一点、レビュー案から少し改善しました。`dominance positive` 補題では `0 < len` は不要でした。`outrunsDepthCount < len` が空範囲をすでに排除するので、最終 API は `not_all_outruns` だけを要求する形にしています。

既存 hook 調査も実施し、次の landing point を整理しました。特に次へ効くのは:

```lean
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowContinuationMass_forces_tailRetention
```

ドキュメントは新規に [Collatz-FrequencyHeightBridge-113.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md) と [report-petal-113.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-113.md) を追加し、README / Guide / Status も同期しました。

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

すべて通過。`PetalBridge.lean` に `sorry` はありません。統合ビルド中の `ZsigmondyCyclotomicResearch.lean:152:6 uses sorry` は既知の upstream warning です。

次は tail-facing の height bridge が本命です。`pressure/continuation mass -> tail retention/residue -> tail height >= 2 count -> sumS n (k+1)` の順で攻めるのが一番近そうです。

## Review

## 1. 状況分析

checkpoint `113` は、前回の **cause-side frequency alias** から、いよいよ **height / drift 側へ渡す前半橋** に入った回じゃ。

今回の到達点は、まだ `sumS` の下界そのものではない。
しかし、そこへ向かうための前半ルートが整理された。

```text
outruns-heavy
  -> pressure-heavy
  -> controlled / pressure count imbalance
  -> positive pressure count
```

追加された theorem 群も、まさにこの順になっている。

```lean
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
tailPressureMoreThanHalf_of_outrunsMoreThanHalf

sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf

sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf
```

レポートでも、今回は `cause-side frequency` から `height/drift` 側へ渡す前半の bridge API を追加した、と整理されている。さらに既存 hook として `orbitWindowHeightSeq_sum_eq_sumS`、`orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two`、`orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one`、`orbitWindowContinuationMass_forces_tailRetention` などが次の landing point として挙げられている。

ここまで来ると、分類・頻度・原因側の整備は十分に厚い。
次は本当に height 側へ刺しに行く段階じゃ。

## 2. 今回の核心

今回の核心は、cause-side の強い仮定を、height 側へ使いやすい形に落とすことじゃ。

まず、

$$
\text{SourceOutrunsMoreThanHalfOnDepthRange}\Longrightarrow\text{SourcePressureMoreThanHalfOnDepthRange}
$$

が入った。

さらに、

$$
\text{SourceOutrunsMoreThanHalfOnDepthRange}\\
\Longrightarrow\text{sourceContinuationControlledDepthCount}<\text{sourceContinuationPressureDepthCount}
$$

が入った。

そして最小存在として、

$$
0<\text{sourceContinuationPressureDepthCount}
$$

も得られる。

tail 版も同様。

これはかなり良い。
強い frequency 仮定を、いきなり height に突っ込まず、まず `pressure-heavy`、次に `count imbalance`、最後に `positive pressure` へ落としている。

後続証明が使いやすい。

## 3. レビュー

## 3.1. 前半 bridge として正しい

今回の checkpoint は、まだ本命の height theorem ではない。
だが、いきなり

```text
outruns-heavy -> sumS lower bound
```

を狙わなかったのが良い。

その前に、

```text
outruns-heavy -> pressure-heavy
```

```text
outruns-heavy -> pressure count positive
```

を API として固定した。

これは正しい順序じゃ。
証明の主語を一段ずつ下ろしている。

## 3.2. `0 < len` を消した改善が良い

報告にある改善点も良い。

当初案では dominance positive lemma に `0 < len` を要求していたが、最終版では不要になっている。

```lean
sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
```

ここで必要なのは、

```lean
sourceContinuationOutrunsDepthCount n k r len < len
```

だけ。

これは確かに空範囲を排除している。
`len = 0` なら count も `0` なので、`0 < 0` はあり得ない。

したがって `0 < len` を別仮定にしない方が API として綺麗じゃ。

## 3.3. 既存 hook 調査が非常に重要

今回の一番の価値は、実装追加そのものに加えて、次の landing point が明確になったことじゃ。

特に重要なのはこのあたり。

```lean
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowContinuationMass_forces_tailRetention
```

この組み合わせから見ると、次は source 側より tail-facing が近い。

理由は、Collatz の一歩遷移では source の continuation が、次 step の tail retention / residue に現れるからじゃ。

つまり次の目標は、

```text
continuation / pressure mass
  -> tail retention / tail residue mass
  -> tail height >= 2 count
  -> sumS lower bound
```

になる。

## 4. 数学的意味

いままでの定理群は、depth-mode の分布を見ていた。

```text
controlled / pressure
dominance / outruns
at most half / more than half
```

今回から、その frequency 情報を height へ送る準備が始まった。

Collatz の height は、

$$
v_2(3n+1)
$$

であり、直感的には「どれだけ \(2^r\) ラインに乗ったか」を測る量じゃ。

今の DkMath 語彙では、

```text
tail residue mod 4 = 1
  <-> tail height >= 2
```

のような橋がある。

したがって、pressure-heavy が tail retention/residue mass を押し上げるなら、その先に height count lower bound が出る。

つまり次の大きな狙いは、

$$
\text{pressure-heavy}\Longrightarrow\text{tail height count lower bound}
$$

じゃ。

## 5. 今回閉じたもの

今回閉じたのは、次の前半ルート。

```text
cause-side outruns-heavy
  -> descriptive pressure-heavy
```

```text
cause-side outruns-heavy
  -> pressure depths outnumber controlled depths
```

```text
cause-side outruns-heavy
  -> pressure depth exists
```

そして反対側として、

```text
not all outruns
  -> dominance depth exists
```

も得た。

これは、今後の case split で非常に便利じゃ。

```text
outruns-heavy:
  pressure 側へ進む

not-all-outruns:
  dominance/recovery 側の存在を取る
```

という二面展開ができる。

## 6. まだ閉じていないもの

まだ閉じていない本命はこれじゃ。

```text
pressure-heavy or outruns-heavy
  -> lower bound on height-count mass
```

特に候補は、

```lean
orbitWindowHeightCountGeTail n k 2
```

または、

```lean
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
```

を経由するルート。

ここで注意が必要なのは、**pressure depth count** と **height count** の対象が違うことじゃ。

pressure depth count は depth range の \(j<len\) を数える。

height count は orbit window 内の \(i<k\) を数える。

したがって、次の bridge ではこのズレを吸収する必要がある。

つまり、いきなり

```text
pressureDepthCount <= orbitWindowHeightCountGeTail ...
```

を言うのは危ない。

まずは、より局所的に、

```text
continuation mass at depth r
  -> tail retention mass at depth r+1
```

あるいは、

```text
continuation sibling mass
  -> tail residue count mod 4 = 1
```

のような、同じ mass-count 系の橋を固めるのが安全じゃ。

## 7. 次の指示

次 checkpoint は **tail-facing height bridge** を狙う。

ただし、最初は height sum まで行かず、tail residue / tail height count への橋を作る。

## 7.1. 既存 theorem の薄い alias を作る

まず、既存の

```lean
orbitWindowContinuationMass_forces_tailRetention
```

を、次のルートで使いやすい名前にしておく。

仮の形はこう。

```lean
theorem sourceContinuationMass_le_tailRetentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_forces_tailRetention n k r
```

実際の既存 theorem の引数順や depth shift は、実装側の型に合わせて調整。

目的は、名前で意味が読める alias を置くことじゃ。

## 7.2. tail retention を tail residue mod4 へ接続する

もし tail retention at depth `1` や `r = 1` が `mod4 = 1` と一致するなら、次はここを狙う。

```lean
theorem tailRetentionMass_depth_one_le_tailResidueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowRetentionMassPow2Tail n k 1 ≤
      orbitWindowResidueCountMod4EqOneTail n k := by
  -- 既存の pow2 residue count 定義と mod4 alias を使う
```

ただし名前は実際の既存 API に合わせる。
もし `orbitWindowResidueCountPow2Tail` 経由なら、直接それを使う方がよい。

## 7.3. tail residue count を height count へ接続する

既にあるらしい。

```lean
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
```

これを使って、

```lean
theorem tailRetentionMass_depth_one_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRetentionMassPow2Tail n k 1 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  -- residue bridge を rw して使う
```

が狙える。

ここが通れば、かなり大きい。

## 7.4. height count から sumS lower bound

既存の

```lean
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
```

を使う。

狙いは、

```lean
theorem sumS_ge_window_add_tailRetentionMass_depth_one
    (n : OddNat) (k : ℕ) :
    k + orbitWindowRetentionMassPow2Tail n k 1 ≤ sumS n (k + 1) := by
  -- height seq sum bridge + tail height count lower bound
```

ただし `sumS n (k+1)` との index は既存 theorem に合わせる必要がある。

## 8. 一歩先ゆく推論

ここで一つ重要な予測がある。

今の pressure-depth frequency は depth 方向の count だが、height lower bound は orbit-window の label count。
したがって、最初の height bridge は「frequency」から直接ではなく、**mass theorem** から入る方がよい。

つまり次は、

```text
outruns-heavy
```

からではなく、

```text
orbitWindowContinuationSiblingMassPow2 n k r
```

を source として tail height count へ繋ぐ。

その後で、frequency theorem からその mass theorem へ接続できるかを探す。

順序としては、

```text
A. continuation mass -> tail height count

B. pressure-heavy -> continuation mass lower bound

C. pressure-heavy -> height lower bound
```

が良い。

いまは A を狙う段階じゃ。

## 9. さらに次の一手

tail-facing height bridge が通ったら、次は Nat drift に向かう。

実数や \(\log_2 3\) はまだ要らない。

目標はこれ。

$$
3^k<2^{\text{sumS}\ n\ k}
$$

または十分条件として、

$$
2k\le \text{sumS}\ n\ k
$$

なら、

$$
3^k<2^{\text{sumS}\ n\ k}
$$

を使う。

これは完全に Nat の指数比較で行ける。

将来の theorem 名候補：

```lean
def BinaryDriftWins (k S : ℕ) : Prop :=
  3 ^ k < 2 ^ S
```

```lean
theorem binaryDriftWins_of_two_mul_le
    (k S : ℕ)
    (h : 2 * k ≤ S) :
    BinaryDriftWins k S := by
  -- 3^k < 4^k = 2^(2*k) ≤ 2^S
```

ただし、これは次々段階。
まずは `sumS` 下界を強くする。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: continuation mass to tail retention alias

```lean
theorem sourceContinuationMass_le_tailRetentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_forces_tailRetention n k r
```

これは既存 theorem の引数が違えば調整。

## 実験 B: continuation mass to tail recovery+continuation budget

既存の

```lean
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

を使う alias。

```lean
theorem sourceContinuationMass_le_tailSplitMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRecoverySiblingMassPow2Tail n k r +
        orbitWindowContinuationSiblingMassPow2Tail n k r :=
  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation n k r
```

これも実際の theorem 型に合わせる。

## 実験 C: tail retention depth one to tail height count

```lean
theorem tailRetentionMass_depth_one_le_heightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRetentionMassPow2Tail n k 1 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  -- orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
  -- tail retention depth 1 = tail residue mod4 eq1
  -- を使う
  sorry
```

ここが次 checkpoint の本命候補じゃ。

## 実験 D: continuation mass depth zero to tail height count

もし depth shift が合うなら、さらに直接。

```lean
theorem sourceContinuationMass_depth_zero_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k 0 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  have h1 := sourceContinuationMass_le_tailRetentionMass n k 0
  have h2 := tailRetentionMass_depth_one_le_heightCountGe_two n k
  omega
```

これはかなり狙い目。

## 実験 E: tail height count to height sequence sum

```lean
theorem heightSeq_sum_ge_window_add_sourceContinuationMass_depth_zero
    (n : OddNat) (k : ℕ) :
    k + orbitWindowContinuationSiblingMassPow2 n k 0 ≤
      (orbitWindowHeightSeq n (k + 1)).sum := by
  have hmass :
      orbitWindowContinuationSiblingMassPow2 n k 0 ≤
        orbitWindowHeightCountGeTail n k 2 :=
    sourceContinuationMass_depth_zero_le_tailHeightCountGe_two n k
  have hsum :=
    orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n k
  omega
```

型や向きは要調整。
ここが通れば、frequency から height への本橋にかなり近い。

## 実験 F: sumS 版へ変換

```lean
theorem sumS_ge_window_add_sourceContinuationMass_depth_zero
    (n : OddNat) (k : ℕ) :
    k + orbitWindowContinuationSiblingMassPow2 n k 0 ≤
      sumS n (k + 1) := by
  rw [← orbitWindowHeightSeq_sum_eq_sumS]
  exact heightSeq_sum_ge_window_add_sourceContinuationMass_depth_zero n k
```

これも既存 theorem の向きに合わせる。

## 実験 G: pressure positive gives existence of continuation mass

いまは pressure count positive がある。
次に欲しいのは、それをどこかの mass positive に変換できるか。

```lean
theorem exists_pressure_depth_of_sourcePressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (h : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j)) := by
  -- List.countP positive -> exists
  sorry
```

これは少し重いが、pressure depth count を「ある depth の mass theorem」へ変換するのに必要になるかもしれない。

## 実験 H: pressure depth existence to positive continuation mass

```lean
theorem exists_positive_continuationMass_of_sourcePressureDepthCount_pos
    (n : OddNat) (k r len : ℕ)
    (h : 0 < sourceContinuationPressureDepthCount n k r len) :
    ∃ j, j < len ∧
      0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) := by
  -- MoreThanHalf count total -> 0 < count
  -- countP positive -> exists
  sorry
```

これは次々段階。
ただし、ここが通ると `outruns-heavy` から「どこかの continuation mass が正」と言える。

## 11. 次コミットの推奨順

```text
1. 既存 theorem の型確認:
   orbitWindowContinuationMass_forces_tailRetention
   orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
   orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
   orbitWindowHeightSeq_sum_eq_sumS

2. sourceContinuationMass_le_tailRetentionMass alias を追加

3. tailRetentionMass_depth_one_le_heightCountGe_two を試す

4. sourceContinuationMass_depth_zero_le_tailHeightCountGe_two を試す

5. heightSeq_sum_ge_window_add_sourceContinuationMass_depth_zero を試す

6. sumS_ge_window_add_sourceContinuationMass_depth_zero を試す

7. docs:
   FrequencyHeightBridge から TailHeightBridge へ接続
```

## 12. 総括

checkpoint 113 は、height/drift に入る前半橋として良い。

今回で、

$$
\text{outruns-heavy}\Longrightarrow\text{pressure-heavy}\Longrightarrow\text{pressure count positive}
$$

まで閉じた。

次は本命の tail-facing bridge。

```text
continuation mass
  -> tail retention / residue
  -> tail height >= 2 count
  -> sumS lower bound
```

これが通れば、ようやく `Collatz.PetalBridge` の有限観測分布が、実際の Collatz height data に接続される。

うむ。
ここからが山場じゃ。いままで積んできた `controlled / pressure / dominance / outruns` の語彙を、いよいよ \(v_2\) と `sumS` へ食い込ませる段階に入った。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 280eeb34..df4fa628 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -3091,6 +3091,110 @@ theorem tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
   have hpart := tailCauseSideDepthCount_add_eq_len n k r len
   omega
 
+/--
+Source cause-side outruns-heavy frequency gives descriptive source pressure
+heavy frequency.
+-/
+theorem sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    SourcePressureMoreThanHalfOnDepthRange n k r len :=
+  (sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
+
+/--
+Tail cause-side outruns-heavy frequency gives descriptive tail pressure heavy
+frequency.
+-/
+theorem tailPressureMoreThanHalf_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
+    TailPressureMoreThanHalfOnDepthRange n k r len :=
+  (tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
+
+/--
+Source cause-side outruns-heavy frequency forces descriptive pressure depths to
+outnumber controlled depths.
+-/
+theorem sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    sourceContinuationControlledDepthCount n k r len <
+      sourceContinuationPressureDepthCount n k r len :=
+  sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+    n k r len
+    (sourcePressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)
+
+/--
+Tail cause-side outruns-heavy frequency forces descriptive pressure depths to
+outnumber controlled depths.
+-/
+theorem tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
+    tailContinuationControlledDepthCount n k r len <
+      tailContinuationPressureDepthCount n k r len :=
+  tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+    n k r len
+    (tailPressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)
+
+/--
+Source cause-side outruns-heavy frequency guarantees that at least one source
+pressure depth exists.
+-/
+theorem sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    0 < sourceContinuationPressureDepthCount n k r len := by
+  have hlt :
+      sourceContinuationControlledDepthCount n k r len <
+        sourceContinuationPressureDepthCount n k r len :=
+    sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
+  omega
+
+/--
+Tail cause-side outruns-heavy frequency guarantees that at least one tail
+pressure depth exists.
+-/
+theorem tailPressureDepthCount_pos_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
+    0 < tailContinuationPressureDepthCount n k r len := by
+  have hlt :
+      tailContinuationControlledDepthCount n k r len <
+        tailContinuationPressureDepthCount n k r len :=
+    tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
+  omega
+
+/--
+If the source outruns side does not fill a nonempty range, then the source
+dominance side is present.
+
+This is a small partition-consumption lemma for later recovery-side arguments.
+-/
+theorem sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+    (n : OddNat) (k r len : ℕ)
+    (_h : SourceOutrunsAtMostHalfOnDepthRange n k r len)
+    (hnotAllOutruns :
+      sourceContinuationOutrunsDepthCount n k r len < len) :
+    0 < sourceRecoveryDominanceDepthCount n k r len := by
+  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
+  omega
+
+/--
+If the tail outruns side does not fill a nonempty range, then the tail
+dominance side is present.
+
+This is the shifted-tail counterpart of the source partition-consumption lemma.
+-/
+theorem tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+    (n : OddNat) (k r len : ℕ)
+    (_h : TailOutrunsAtMostHalfOnDepthRange n k r len)
+    (hnotAllOutruns :
+      tailContinuationOutrunsDepthCount n k r len < len) :
+    0 < tailRecoveryDominanceDepthCount n k r len := by
+  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
+  omega
+
 /--
 If source continuation pressure holds at every depth of the range, then the
 source pressure-depth count fills the whole range.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 493d961c..030e3944 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -147,6 +147,7 @@ docs/Collatz-DepthPressureFrequency-109.md
 docs/Collatz-CauseSideFailureCount-110.md
 docs/Collatz-CauseSideDepthDistribution-111.md
 docs/Collatz-CauseSideFrequencyAlias-112.md
+docs/Collatz-FrequencyHeightBridge-113.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md
new file mode 100644
index 00000000..7e85cd00
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md
@@ -0,0 +1,157 @@
+# Collatz Frequency Height Bridge 113
+
+## Purpose
+
+Checkpoint 113 begins the route from cause-side frequency toward the original
+Collatz height and drift data.
+
+It does not yet prove a new drift lower bound.  Instead, it makes the existing
+frequency layer easier to consume from later height arguments.
+
+The key route is:
+
+```text
+cause-side outruns-heavy
+  -> descriptive pressure-heavy
+  -> controlled/pressure count imbalance
+  -> positive pressure count
+  -> future height-count lower bound
+```
+
+## New Cause-To-Pressure Aliases
+
+Source:
+
+```lean
+sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
+```
+
+Tail:
+
+```lean
+tailPressureMoreThanHalf_of_outrunsMoreThanHalf
+```
+
+These are one-way aliases extracted from the checkpoint 112 equivalences:
+
+```lean
+sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+```
+
+They let later proofs state the hypothesis in cause-side terms and immediately
+use the descriptive pressure-frequency API.
+
+## Count Imbalance
+
+The next bridge consumes the existing pressure-more-than-half comparison
+theorems:
+
+```lean
+sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+```
+
+These say:
+
+```text
+if outruns is more than half of the depth range,
+then pressure depths outnumber controlled depths.
+```
+
+This is descriptive count imbalance, but triggered by a cause-side hypothesis.
+
+## Positive Pressure Count
+
+Checkpoint 113 also records the minimal existence consequence:
+
+```lean
+sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
+tailPressureDepthCount_pos_of_outrunsMoreThanHalf
+```
+
+These are useful when a later proof only needs:
+
+```text
+there exists at least one pressure depth
+```
+
+rather than a full count imbalance.
+
+## Recovery-Side Partition Test
+
+The checkpoint also adds partition-consumption lemmas for the opposite side:
+
+```lean
+sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+```
+
+The original experimental shape included a separate `0 < len` hypothesis.
+Lean showed that this hypothesis is unnecessary: the assumption
+
+```text
+outrunsDepthCount < len
+```
+
+already excludes the empty-range obstruction.  The final API therefore uses
+only the stronger and more informative not-all-outruns hypothesis.
+
+## Existing Height Hooks
+
+The search pass found the current landing points for a future height bridge:
+
+```lean
+orbitWindowHeightSeq_sum_eq_sumS
+orbitWindowHeightSeq_sum_ge_of_forall_ge
+orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
+```
+
+The low residue bridges are also already present:
+
+```lean
+orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
+orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
+orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
+```
+
+This means the missing bridge is more specific:
+
+```text
+pressure-heavy or outruns-heavy depth range
+  -> lower bound on a source/tail height count
+```
+
+Once that exists, the `sumS` lower-bound API can consume it.
+
+## Next Candidate
+
+The next checkpoint should search for a theorem connecting pressure/retention
+mass to one of these height-count objects:
+
+```text
+orbitWindowHeightCountGe n k 2
+orbitWindowHeightCountGeTail n k 2
+orbitWindowResidueCountMod4EqOne n k
+orbitWindowResidueCountMod4EqOneTail n k
+```
+
+The strongest likely near-term route is tail-facing:
+
+```text
+pressure or continuation mass
+  -> tail retention / tail residue mass
+  -> tail height >= 2 count
+  -> sumS n (k + 1) lower bound
+```
+
+This keeps the argument in finite `Nat` arithmetic and avoids importing real
+drift estimates too early.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 8436df62..460b955f 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -688,6 +688,68 @@ if outruns depths occupy more than half of the depth range,
 then outruns depths strictly outnumber dominance depths.
 ```
 
+## Frequency To Height Preparation
+
+Checkpoint 113 starts the bridge from cause-side frequency toward height and
+drift data.
+
+The first step is a one-way alias from cause-side high frequency to descriptive
+pressure high frequency:
+
+```lean
+sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
+tailPressureMoreThanHalf_of_outrunsMoreThanHalf
+```
+
+The next step consumes the existing pressure-frequency API and produces the
+descriptive count imbalance:
+
+```lean
+sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+```
+
+For later existence-style arguments, checkpoint 113 also exposes positivity of
+the pressure count:
+
+```lean
+sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
+tailPressureDepthCount_pos_of_outrunsMoreThanHalf
+```
+
+The recovery-side partition consumption test is:
+
+```lean
+sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+```
+
+This records a useful finite reading:
+
+```text
+if the outruns side does not fill the range,
+then the dominance side has positive count.
+```
+
+The direct height/drift hook is not yet proved from pressure frequency.
+However, the existing height API already has the likely landing points:
+
+```lean
+orbitWindowHeightSeq_sum_eq_sumS
+orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+```
+
+So the next real bridge should convert a pressure-heavy or outruns-heavy range
+into a lower bound for a height-count object such as:
+
+```text
+orbitWindowHeightCountGe n k 2
+orbitWindowHeightCountGeTail n k 2
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index cbb92e9b..f3d83782 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -296,6 +296,14 @@ tailOutrunsAtMostHalf_iff_pressureAtMostHalf
 tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
 sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
 tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
+tailPressureMoreThanHalf_of_outrunsMoreThanHalf
+sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
+tailPressureDepthCount_pos_of_outrunsMoreThanHalf
+sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-113.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-113.md
new file mode 100644
index 00000000..12f3a2f3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-113.md
@@ -0,0 +1,177 @@
+# Report Petal 113
+
+## Summary
+
+Checkpoint 113 begins the bridge from cause-side frequency toward height and
+drift data in `DkMath.Collatz.PetalBridge`.
+
+The checkpoint does not yet prove a new `sumS` lower bound.  It closes the
+front half of the route:
+
+```text
+outruns-heavy
+  -> pressure-heavy
+  -> controlled/pressure count imbalance
+  -> positive pressure count
+```
+
+This gives later height arguments a small API surface that avoids unfolding
+the frequency predicates.
+
+## Lean Additions
+
+Cause-side high frequency to descriptive pressure high frequency:
+
+```lean
+sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
+tailPressureMoreThanHalf_of_outrunsMoreThanHalf
+```
+
+Cause-side high frequency to descriptive count imbalance:
+
+```lean
+sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
+```
+
+Positive pressure-count consequences:
+
+```lean
+sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
+tailPressureDepthCount_pos_of_outrunsMoreThanHalf
+```
+
+Partition-consumption tests for the recovery side:
+
+```lean
+sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
+```
+
+## Implementation Note
+
+The review suggested a dominance-positive lemma with an explicit `0 < len`
+hypothesis.  Lean showed that this hypothesis is unnecessary once we assume:
+
+```text
+outrunsDepthCount < len
+```
+
+That assumption already rules out the empty-range obstruction.  The final
+theorem names therefore use `not_all_outruns` rather than `len_pos`.
+
+This is a small API improvement: callers only need to prove the operational
+condition that the failure side does not fill the range.
+
+## Search Findings
+
+The existing height and `sumS` bridge hooks are concentrated in
+`DkMath.Collatz.PetalBridge`.
+
+Direct height-sum bridge:
+
+```lean
+orbitWindowHeightSeq_sum_eq_sumS
+```
+
+Finite layer-cake and count lower bounds:
+
+```lean
+orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
+orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
+orbitWindowHeightSeq_sum_ge_sum_countGe_range
+orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
+```
+
+Practical second-layer lower bounds:
+
+```lean
+orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
+```
+
+Residue-to-height hooks:
+
+```lean
+orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
+orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
+orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
+```
+
+## Mathematical Reading
+
+Checkpoint 113 proves that a cause-side failure-heavy range is already visible
+as a descriptive pressure-heavy range, and that it forces pressure depths to
+outnumber controlled depths.
+
+This is still a depth-mode statement.  The next missing bridge is:
+
+```text
+pressure-heavy depth range
+  -> lower bound on source or tail height-count mass
+```
+
+Once that bridge exists, the current height API can turn it into a `sumS`
+lower bound.
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
+DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md
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
+The next checkpoint should try a tail-facing height bridge.
+
+Candidate target:
+
+```text
+pressure or continuation mass
+  -> tail retention / tail residue mass
+  -> orbitWindowHeightCountGeTail n k 2 lower bound
+  -> sumS n (k + 1) lower bound
+```
+
+Relevant existing hooks:
+
+```lean
+orbitWindowContinuationMass_forces_tailRetention
+orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
+orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+```
+
+The first experiment should stay in `Nat` and should avoid real drift
+estimates until a clean height-count lower bound is available.
````
`````
