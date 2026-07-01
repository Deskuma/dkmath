# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: eafa75b02fae4b7a7f7d36b69ba521ec722d6258

## Report

Checkpoint 112 完了です。今回の本体は [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に cause-side frequency alias を追加したことです。

追加した主な Lean 名:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange

sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange

sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf

sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
```

112 の意味は、`ContinuationOutrunsRecovery` 側の頻度を、既存の pressure frequency と theorem-level で同一視できるようにしたことです。さらにおまけとして、outruns が過半なら dominance count を strict に上回る、という有限 obstruction 読みも固定しました。

ドキュメントも同期済みです。新規に [Collatz-CauseSideFrequencyAlias-112.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md) と [report-petal-112.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-112.md) を追加し、README / Guide / Status も更新しました。

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

すべて通過。`PetalBridge.lean` に `sorry` はありません。統合ビルド中の `ZsigmondyCyclotomicResearch.lean:152:6 uses sorry` は既知の upstream warning です。

次は、frequency alias から height / drift 側へ接続する段階です。特に `SourceOutrunsMoreThanHalfOnDepthRange -> pressure frequency -> count comparison -> mass imbalance -> height/drift lower bound` の順が自然です。

## Review

## 1. 状況分析

checkpoint `112` は、前回までに完成した **cause-side depth distribution** に、薄い frequency alias を載せた回じゃ。

今回の追加は重い新定理ではなく、既存の

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

を使って、pressure frequency を cause-side の名前で読めるようにした API 整備じゃ。報告でも、`ContinuationOutrunsRecovery` 側の頻度を既存の pressure frequency と theorem-level で同一視できるようにした、と整理されている。

今回の主な追加はこの層。

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

そして pressure frequency との橋。

```lean
sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
```

これで、次からは

```text
continuation outruns recovery が多い
```

という機構側の仮定を、そのまま既存の pressure API に渡せる。

## 2. 今回の核心

今回の核心は、次の読み替えじゃ。

$$
\text{SourceOutrunsMoreThanHalfOnDepthRange}\leftrightarrow\text{SourcePressureMoreThanHalfOnDepthRange}
$$

tail 版も同様。

つまり、

```text
cause-side:
  outruns が depth range の半分超え

descriptive side:
  pressure が depth range の半分超え
```

が theorem-level で同一視された。

これは小さく見えるが、かなり大事。
今後、構造的な仮定は cause-side で立て、有限予算・比率の消費は descriptive side で行う、という分担ができる。

## 3. レビュー

## 3.1. alias layer として正しい

今回の checkpoint は、新しい count を増やしていない。
既存の

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

に `AtMostHalf` / `MoreThanHalf` をかぶせただけじゃ。

これは良い。
新しい計数定義を増やしすぎると API が散らかるが、今回は既存 count の読みだけを増やしている。

## 3.2. dichotomy も自然

追加された分岐定理、

```lean
sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
```

は、既存の `atMostHalf_or_moreThanHalf` の薄い wrapper じゃ。

これで cause-side でも、

```text
outruns は半分以下
または
outruns は半分超え
```

と直接 case split できる。

今後の証明で、

```lean
cases sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange n k r len with
| inl hlow =>
    ...
| inr hhigh =>
    ...
```

のように書けるのは大きい。

## 3.3. obstruction 読みも良い

今回のおまけ定理、

```lean
sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
```

はかなり良い追加じゃ。

これは、

$$
\text{len}<2\cdot\text{outrunsDepthCount}
$$

かつ、

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

から、

$$
\text{dominanceDepthCount}<\text{outrunsDepthCount}
$$

を出している。

つまり、

```text
outruns が過半なら、dominance を個数で上回る
```

という有限 obstruction 読みが固定された。

## 4. 数学的意味

ここまでで depth range は三つの層で読める。

```text
1. 記述側:
   controlled / pressure

2. 原因側:
   dominance / outruns

3. frequency 側:
   半分以下 / 半分超え
```

今回、三つ目の frequency を cause-side にも移した。

これにより、今後の証明では次のような流れが自然になる。

```text
SourceOutrunsMoreThanHalfOnDepthRange
  -> SourcePressureMoreThanHalfOnDepthRange
  -> controlledDepthCount < pressureDepthCount
  -> source/tail mass imbalance
  -> height / drift 側の下界
```

今回の checkpoint は、まさにこの入口を作った。

## 5. 今回閉じたもの

今回閉じたものは次の三つ。

```text
1. cause-side frequency predicate

2. cause-side frequency と pressure frequency の theorem-level 同一視

3. outruns 過半なら dominance count を strict に上回る obstruction 読み
```

これで `Collatz.PetalBridge` の有限 depth-mode 言語はかなり整った。

ここから先は、alias を増やすより、そろそろ **height / drift への橋** に入る段階じゃ。

## 6. まだ閉じていないもの

まだ閉じていないのは、

```text
frequency が高さに何を強制するか
```

じゃ。

現在は、

$$
\text{outrunsDepthCount}
$$

や、

$$
\text{pressureDepthCount}
$$

の多寡を言える。

しかし、それが実際の Collatz orbit の

$$
\text{sumS}
$$

あるいは

$$
v_2(3n+1)
$$

にどう効くかはまだ直接つながっていない。

ここが次の大きな橋になる。

## 7. 次の指示

次は **frequency から height / drift へ接続する準備補題** を作るのがよい。

ただし、いきなり強い drift theorem を狙わず、まずは既存の frequency theorem を height 側で消費しやすくする薄い bridge を作る。

## 7.1. cause-side high-frequency から pressure high-frequency

これは既に iff があるので、片方向 alias を作る。

```lean
theorem sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len :=
  (sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
```

tail 版も同様。

```lean
theorem tailPressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len :=
  (tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
```

## 7.2. cause-side high-frequency から descriptive count imbalance

既存の pressure theorem を使って、cause-side から controlled/pressure 比較へ直行する。

```lean
theorem sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len := by
  exact
    sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
      n k r len
      ((sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h)
```

tail 版も同様。

## 7.3. cause-side high-frequency から pressure count lower relation

次に、strict 比較を Nat の形で使いやすくする。

```lean
theorem sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < sourceContinuationPressureDepthCount n k r len := by
  have hlt :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len :=
    sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega
```

これは小さいが、後で「少なくとも一つ pressure depth がある」を引き出せる。

## 8. 一歩先ゆく推論

次に本当に欲しいのは、pressure depth が height に寄与するという橋じゃ。

たとえば、ある depth \(r+j\) で pressure が起きるなら、それは retention cylinder の中で continuation が支配的ということ。
これがどの residue class と結びつくかを見つければ、height count に接続できる。

既存 API には height count / residue count の橋があるはずじゃ。

記憶上では、次のような系がある。

```lean
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

このあたりを探して、pressure / outruns frequency が最終的に

$$
\text{sumS}
$$

の下界に変換できるかを見る段階じゃ。

## 9. さらに次の一手

今後の本命ルートはこう。

```text
1. SourceOutrunsMoreThanHalfOnDepthRange

2. pressure frequency に変換

3. controlled/pressure imbalance を得る

4. imbalance が tail 側 retention/recovery/continuation mass に何を強制するかを見る

5. tail residue が height >= 2 や height >= 3 に接続できるかを見る

6. height sum lower bound を得る

7. Nat のまま drift 判定へ進む
```

ここで重要なのは、まだ \(\log_2 3\) や実数平均へ行かないこと。

height 側へ行くなら、まずは Nat の指数比較でよい。

$$
3^k<2^{\text{sumS}}
$$

この形へ持ち込むのが理想じゃ。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source cause-side high frequency to pressure high frequency

```lean
theorem sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len :=
  (sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
```

## 実験 B: tail cause-side high frequency to pressure high frequency

```lean
theorem tailPressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len :=
  (tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h
```

## 実験 C: source outruns high frequency to controlled/pressure imbalance

```lean
theorem sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len := by
  exact
    sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
      n k r len
      ((sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h)
```

## 実験 D: tail outruns high frequency to controlled/pressure imbalance

```lean
theorem tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailContinuationControlledDepthCount n k r len <
      tailContinuationPressureDepthCount n k r len := by
  exact
    tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
      n k r len
      ((tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h)
```

## 実験 E: source pressure count positive

```lean
theorem sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < sourceContinuationPressureDepthCount n k r len := by
  have hlt :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len :=
    sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega
```

## 実験 F: tail pressure count positive

```lean
theorem tailPressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < tailContinuationPressureDepthCount n k r len := by
  have hlt :
      tailContinuationControlledDepthCount n k r len <
        tailContinuationPressureDepthCount n k r len :=
    tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega
```

## 実験 G: source dominance count positive from at-most-half side

対称側も必要になるかもしれない。

```lean
theorem sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_len_pos
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsAtMostHalfOnDepthRange n k r len)
    (hlen : 0 < len)
    (hnotAllOutruns :
      sourceContinuationOutrunsDepthCount n k r len < len) :
    0 < sourceRecoveryDominanceDepthCount n k r len := by
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega
```

これは仮定が少し多いが、cause-side partition の消費テストになる。

## 実験 H: 次に探すべき既存補題

これは新規 theorem ではなく、検索指示。

```text
rg "HeightCountGe" DkMath/Collatz
rg "sum_ge" DkMath/Collatz
rg "residueCount.*mod4" DkMath/Collatz
rg "orbitWindowHeightSeq_sum" DkMath/Collatz
```

目的は、pressure / outruns 側の count を、height sum 下界へ接続できる既存の hook を探すことじゃ。

## 11. 次コミットの推奨順

```text
1. sourcePressureMoreThanHalf_of_outrunsMoreThanHalf を追加

2. tailPressureMoreThanHalf_of_outrunsMoreThanHalf を追加

3. sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf を追加

4. tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf を追加

5. source/tail の pressureDepthCount_pos_of_outrunsMoreThanHalf を追加

6. 既存の height / residue / sumS bridge を検索

7. docs:
   CauseSideFrequencyAlias から HeightDriftBridge への候補ルートを追記
```

## 12. 総括

checkpoint 112 は、予定通りの薄い API checkpoint として綺麗に通っている。

今回で、

$$
\text{outruns frequency}\leftrightarrow\text{pressure frequency}
$$

が theorem-level で読めるようになった。

次からは alias を増やすより、**height / drift 側へ橋を掛ける段階**じゃ。

焦って大きな Collatz 降下定理を狙わず、まずは

```text
outruns-heavy
  -> pressure-heavy
  -> count imbalance
  -> mass imbalance
  -> height lower bound
```

のうち、前半を小さく固めるのが良い。

ここまで来れば、`Collatz.PetalBridge` は単なる分類器ではなく、height/drift へ進むための有限観測エンジンとして働き始める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 131d59ca..280eeb34 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2963,6 +2963,134 @@ theorem tailCauseSideDepthCount_add_eq_len
   rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
   exact tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
 
+/--
+Cause-side source frequency predicate: source continuation outruns recovery in
+at most half of the observed depth range.
+-/
+def SourceOutrunsAtMostHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  AtMostHalf (sourceContinuationOutrunsDepthCount n k r len) len
+
+/--
+Cause-side source frequency predicate: source continuation outruns recovery in
+more than half of the observed depth range.
+-/
+def SourceOutrunsMoreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalf (sourceContinuationOutrunsDepthCount n k r len) len
+
+/--
+Cause-side tail frequency predicate: tail continuation outruns recovery in at
+most half of the observed depth range.
+-/
+def TailOutrunsAtMostHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  AtMostHalf (tailContinuationOutrunsDepthCount n k r len) len
+
+/--
+Cause-side tail frequency predicate: tail continuation outruns recovery in
+more than half of the observed depth range.
+-/
+def TailOutrunsMoreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalf (tailContinuationOutrunsDepthCount n k r len) len
+
+/-- Source cause-side outruns frequency has the same dichotomy as pressure. -/
+theorem sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) :
+    SourceOutrunsAtMostHalfOnDepthRange n k r len ∨
+      SourceOutrunsMoreThanHalfOnDepthRange n k r len := by
+  unfold SourceOutrunsAtMostHalfOnDepthRange
+  unfold SourceOutrunsMoreThanHalfOnDepthRange
+  exact atMostHalf_or_moreThanHalf
+    (sourceContinuationOutrunsDepthCount n k r len) len
+
+/-- Tail cause-side outruns frequency has the same dichotomy as pressure. -/
+theorem tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) :
+    TailOutrunsAtMostHalfOnDepthRange n k r len ∨
+      TailOutrunsMoreThanHalfOnDepthRange n k r len := by
+  unfold TailOutrunsAtMostHalfOnDepthRange
+  unfold TailOutrunsMoreThanHalfOnDepthRange
+  exact atMostHalf_or_moreThanHalf
+    (tailContinuationOutrunsDepthCount n k r len) len
+
+/--
+Source cause-side at-most-half frequency is equivalent to descriptive source
+pressure at-most-half frequency.
+-/
+theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
+    (n : OddNat) (k r len : ℕ) :
+    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
+      SourcePressureAtMostHalfOnDepthRange n k r len := by
+  unfold SourceOutrunsAtMostHalfOnDepthRange
+  unfold SourcePressureAtMostHalfOnDepthRange
+  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
+
+/--
+Source cause-side more-than-half frequency is equivalent to descriptive source
+pressure more-than-half frequency.
+-/
+theorem sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+    (n : OddNat) (k r len : ℕ) :
+    SourceOutrunsMoreThanHalfOnDepthRange n k r len ↔
+      SourcePressureMoreThanHalfOnDepthRange n k r len := by
+  unfold SourceOutrunsMoreThanHalfOnDepthRange
+  unfold SourcePressureMoreThanHalfOnDepthRange
+  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
+
+/--
+Tail cause-side at-most-half frequency is equivalent to descriptive tail
+pressure at-most-half frequency.
+-/
+theorem tailOutrunsAtMostHalf_iff_pressureAtMostHalf
+    (n : OddNat) (k r len : ℕ) :
+    TailOutrunsAtMostHalfOnDepthRange n k r len ↔
+      TailPressureAtMostHalfOnDepthRange n k r len := by
+  unfold TailOutrunsAtMostHalfOnDepthRange
+  unfold TailPressureAtMostHalfOnDepthRange
+  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
+
+/--
+Tail cause-side more-than-half frequency is equivalent to descriptive tail
+pressure more-than-half frequency.
+-/
+theorem tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+    (n : OddNat) (k r len : ℕ) :
+    TailOutrunsMoreThanHalfOnDepthRange n k r len ↔
+      TailPressureMoreThanHalfOnDepthRange n k r len := by
+  unfold TailOutrunsMoreThanHalfOnDepthRange
+  unfold TailPressureMoreThanHalfOnDepthRange
+  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
+
+/--
+If source outruns depths occupy more than half of the depth range, then they
+strictly outnumber source dominance depths.
+-/
+theorem sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
+    sourceRecoveryDominanceDepthCount n k r len <
+      sourceContinuationOutrunsDepthCount n k r len := by
+  unfold SourceOutrunsMoreThanHalfOnDepthRange at h
+  unfold MoreThanHalf at h
+  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
+  omega
+
+/--
+If tail outruns depths occupy more than half of the depth range, then they
+strictly outnumber tail dominance depths.
+-/
+theorem tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
+    tailRecoveryDominanceDepthCount n k r len <
+      tailContinuationOutrunsDepthCount n k r len := by
+  unfold TailOutrunsMoreThanHalfOnDepthRange at h
+  unfold MoreThanHalf at h
+  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
+  omega
+
 /--
 If source continuation pressure holds at every depth of the range, then the
 source pressure-depth count fills the whole range.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index a11d00e2..493d961c 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -146,6 +146,7 @@ docs/Collatz-MixedDepthModeDistribution-108.md
 docs/Collatz-DepthPressureFrequency-109.md
 docs/Collatz-CauseSideFailureCount-110.md
 docs/Collatz-CauseSideDepthDistribution-111.md
+docs/Collatz-CauseSideFrequencyAlias-112.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md
new file mode 100644
index 00000000..1349686b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md
@@ -0,0 +1,153 @@
+# Collatz Cause-Side Frequency Alias 112
+
+## Purpose
+
+Checkpoint 112 adds a thin cause-side frequency layer to
+`DkMath.Collatz.PetalBridge`.
+
+Checkpoint 109 introduced descriptive pressure-frequency predicates:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+Checkpoint 110 proved that the cause-side outruns count is the same count as
+the descriptive pressure count:
+
+```lean
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+Checkpoint 112 exposes that same frequency question under cause-side names.
+
+## New Frequency Predicates
+
+Source:
+
+```lean
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+```
+
+Tail:
+
+```lean
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+```
+
+These predicates count:
+
+```text
+how often continuation outruns recovery over the depth range [r, r + len)
+```
+
+They do not introduce a new count.  They reuse:
+
+```lean
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+```
+
+## Dichotomy
+
+The finite half dichotomy is available directly on the cause-side names:
+
+```lean
+sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+So the cause-side question can now be split as:
+
+```text
+outruns is at most half of the depth range
+or
+outruns is more than half of the depth range
+```
+
+This is intentionally division-free.  It stays in `Nat` inequalities through
+`AtMostHalf` and `MoreThanHalf`.
+
+## Bridge To Pressure Frequency
+
+The cause-side aliases are theorem-equivalent to the descriptive pressure
+frequency predicates:
+
+```lean
+sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
+sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+tailOutrunsAtMostHalf_iff_pressureAtMostHalf
+tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+```
+
+This lets future proofs choose their input language.
+
+Mechanism-side hypothesis:
+
+```text
+ContinuationOutrunsRecovery occurs often.
+```
+
+Budget-side API:
+
+```text
+MoreThanHalf continuation pressure occurs often.
+```
+
+The checkpoint 112 bridge identifies these two readings at frequency level.
+
+## Extra Count Comparison
+
+Checkpoint 112 also records the count comparison forced by cause-side
+more-than-half:
+
+```lean
+sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+```
+
+These theorems use the checkpoint 111 cause-side partition:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+and the definition of `MoreThanHalf`:
+
+```text
+len < 2 * outrunsDepthCount
+```
+
+to conclude:
+
+```text
+dominanceDepthCount < outrunsDepthCount
+```
+
+This is a small but useful obstruction reading: if the failure side occupies
+more than half the range, then it has already beaten the recovery-dominance
+side as a finite depth count.
+
+## Next Candidate
+
+The next useful bridge is not another alias layer.  It should ask what a
+pressure-heavy or outruns-heavy depth range forces on the original Collatz
+height data.
+
+Candidate route:
+
+```text
+cause-side frequency
+  -> pressure frequency
+  -> controlled/pressure count comparison
+  -> source/tail mass imbalance
+  -> possible height or drift lower bound
+```
+
+The current checkpoint prepares the language needed to state that route
+without unfolding the count definitions.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index f3716258..8436df62 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -631,6 +631,63 @@ RecoveryDominatesContinuation
 ContinuationOutrunsRecovery
 ```
 
+## Cause-Side Frequency Alias
+
+Checkpoint 112 gives the failure side its own frequency vocabulary:
+
+```lean
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+```
+
+These predicates are thin aliases around the cause-side outruns counts:
+
+```text
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+```
+
+They have the same finite dichotomy as pressure frequency:
+
+```lean
+sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+The bridge back to the descriptive pressure vocabulary is explicit:
+
+```lean
+sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
+sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+tailOutrunsAtMostHalf_iff_pressureAtMostHalf
+tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+```
+
+So a later proof can state a hypothesis on the mechanism side:
+
+```text
+continuation outruns recovery in more than half of the depths
+```
+
+and immediately consume the existing pressure-frequency API.
+
+Checkpoint 112 also records the direct count comparison forced by cause-side
+more-than-half:
+
+```lean
+sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+```
+
+This reads:
+
+```text
+if outruns depths occupy more than half of the depth range,
+then outruns depths strictly outnumber dominance depths.
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index d14801ca..cbb92e9b 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -284,6 +284,18 @@ sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
 tailRecoveryDominanceDepthCount_eq_controlledDepthCount
 sourceCauseSideDepthCount_add_eq_len
 tailCauseSideDepthCount_add_eq_len
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
+sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+tailOutrunsAtMostHalf_iff_pressureAtMostHalf
+tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-112.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-112.md
new file mode 100644
index 00000000..56cf99f3
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-112.md
@@ -0,0 +1,140 @@
+# Report Petal 112
+
+## Summary
+
+Checkpoint 112 adds cause-side frequency aliases to
+`DkMath.Collatz.PetalBridge`.
+
+The previous checkpoints proved that:
+
+```text
+outrunsDepthCount = pressureDepthCount
+dominanceDepthCount = controlledDepthCount
+```
+
+Checkpoint 112 uses the first equality to expose pressure-frequency predicates
+under cause-side names.  No new count induction was needed.
+
+## Lean Additions
+
+New source cause-side frequency predicates:
+
+```lean
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+```
+
+New tail cause-side frequency predicates:
+
+```lean
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+```
+
+Finite dichotomies:
+
+```lean
+sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+Pressure-frequency bridges:
+
+```lean
+sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
+sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+tailOutrunsAtMostHalf_iff_pressureAtMostHalf
+tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
+```
+
+Extra cause-side count comparisons:
+
+```lean
+sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
+```
+
+## Mathematical Reading
+
+Checkpoint 112 makes the frequency question readable on the mechanism side:
+
+```text
+How often does continuation outrun recovery?
+```
+
+The same question was already readable on the descriptive pressure side:
+
+```text
+How often is continuation more than half of retention?
+```
+
+The new bridge theorems identify these two frequency readings.
+
+The extra count comparison records the finite obstruction:
+
+```text
+if outruns occurs in more than half of the depth range,
+then outruns depths strictly outnumber recovery-dominance depths.
+```
+
+This follows from the cause-side partition:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+and the `MoreThanHalf` inequality.
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
+DkMath/Collatz/docs/Collatz-CauseSideFrequencyAlias-112.md
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
+The next step should connect frequency to actual Collatz height or drift
+information.
+
+Suggested route:
+
+```text
+cause-side frequency
+  -> pressure frequency
+  -> controlled/pressure count comparison
+  -> source/tail mass imbalance
+  -> height or drift lower bound
+```
+
+The likely next small theorem is a named bridge from
+`SourceOutrunsMoreThanHalfOnDepthRange` to the existing controlled/pressure
+comparison theorem, then a search for where that comparison can feed a height
+or shifted-tail mass estimate.
````
`````
