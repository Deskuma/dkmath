# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 2eb1c384e0266aa7d568b616e153c202f9bf58c1

## Report

実装・文書同期まで完了しました。

`DkMath.Collatz.PetalBridge` に checkpoint 106 の MoreThanHalf 圧力層を追加しました。主な追加は `MoreThanHalf`、`atMostHalf_or_moreThanHalf`、source/tail の dominance-or-outruns 分岐、outruns から dominance 否定、range 抽出、そして `ContinuationOutrunsRecovery` から「continuation が retention の半分超え」と読める theorem 群です。

文書も同期済みです。

- [Collatz-MoreThanHalfPressure-106.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md)
- [report-petal-106.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-106.md)
- [README.md](/lean/dk_math/DkMath/Collatz/README.md)
- [Collatz-PetalBridge-Guide.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md)
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)

検証結果:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

既知の上流警告として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` は引き続き表示されますが、今回の Collatz 変更範囲外です。

次は report に書いた通り、`MoreThanHalfOnRange` / `ContinuationPressureOnRange` のような「失敗圧力プロファイル」を薄く作るのが自然です。支配できない場合も、破綻ではなく有限範囲の圧力として記録できる段階に入りました。

## Review

## 1. 状況分析

うむ。checkpoint `106` は、前回 No.105 で名前を付けた **failure-mode** を、単なる失敗ではなく **MoreThanHalf pressure** として読めるようにした回じゃ。

No.105 では、

```text id="5uzjtz"
RecoveryDominatesContinuation
ContinuationOutrunsRecovery
```

という分岐の名前を作った。

今回 No.106 では、その分岐がこう閉じた。

```text id="u4lyyq"
RecoveryDominatesContinuation
  -> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

つまり、比較条件が成功しても失敗しても、どちらも有限質量の読みへ落ちるようになった。レポートでも、checkpoint 106 は `MoreThanHalf`、局所分岐、range 抽出、そして `ContinuationOutrunsRecovery` から「continuation が retention の半分超え」と読める theorem 群を追加した、と整理されている。

これはかなり良い。
「失敗したので終わり」ではなく、

```text id="3hk41n"
失敗したなら、そこには半分超え圧力がある
```

と言えるようになった。

## 2. 今回の核心

今回の新しい述語はこれじゃ。

```lean id="hxj5vr"
def MoreThanHalf (count k : ℕ) : Prop :=
  k < 2 * count
```

これは `AtMostHalf` の strict complement。

```lean id="nnrml7"
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

したがって、有限自然数上では必ず分岐できる。

```lean id="fxaf04"
theorem atMostHalf_or_moreThanHalf
    (count k : ℕ) :
    AtMostHalf count k ∨ MoreThanHalf count k
```

数学的には、

$$
2C\le M
$$

または、

$$
M<2C
$$

のどちらかになる。

ここで \(C\) は continuation mass、\(M\) は retention mass と読める。

さらに、今回の最重要 theorem はこれ。

```lean id="fjgv82"
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
```

これにより、

$$
R<K
$$

なら、

$$
M<2K
$$

が Lean 上で確定した。

ここで、

$$
M=R+K
$$

だから、これは完全に自然な算術じゃ。

## 3. レビュー

## 3.1. failure branch を正の情報に変換したのが良い

今回の一番良い点は、`ContinuationOutrunsRecovery` を単なる否定条件として放置しなかったことじゃ。

以前の状態では、

```text id="n3u0ft"
RecoveryDominatesContinuation が証明できない
```

というのは、ただの未解決 Gap だった。

しかし今は、

```text id="qnen3o"
ContinuationOutrunsRecovery
  -> MoreThanHalf continuation retention
```

がある。

つまり、desired branch が失敗したら、その失敗は

```text id="mjzfl1"
continuation pressure
```

として測定できる。

これは obstruction route にとって非常に重要じゃ。

## 3.2. dichotomy が入ったことで分岐論理が閉じた

今回、

```lean id="t39z2w"
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
```

が入った。

これで各 depth において、必ず次のどちらかになる。

```text id="efuzp6"
recovery が continuation を支配する

continuation が recovery を上回る
```

つまり、比較不能な第三状態がない。

これは Nat の線形順序に基づく小さな補題だが、後続 proof ではかなり効く。
今後は各 depth で case split できる。

```lean id="yhlhyv"
cases recoveryDominates_or_continuationOutruns n k r with
| inl hgood =>
    -- AtMostHalf branch
| inr hbad =>
    -- MoreThanHalf pressure branch
```

という形で進められる。

## 3.3. range 抽出が正しい

今回、

```lean id="mh15xn"
continuationOutrunsRecovery_of_onRange
tailContinuationOutrunsRecovery_of_onRange
moreThanHalf_continuation_of_outRunsOnRange
moreThanHalf_tailContinuation_of_outRunsOnRange
```

が入った。

これは薄い theorem だが、かなり重要。

`OnRange` 述語は、

$$
\forall j<len,\;\text{failure at }r+j
$$

という形なので、後続で個々の \(j\) を取り出して使うための API が必要になる。

ここを先に整えたのは良い判断じゃ。

## 4. 数学的解説

いま、各 depth \(r\) で retention mass \(M_r\)、recovery mass \(R_r\)、continuation mass \(K_r\) がある。

すでに、

$$
M_r=R_r+K_r
$$

が証明されている。

No.104 では、良い側の分岐として、

$$
K_r\le R_r
$$

なら、

$$
2K_r\le M_r
$$

が得られた。

今回 No.106 では、悪い側の分岐として、

$$
R_r<K_r
$$

なら、

$$
M_r<2K_r
$$

が得られた。

したがって、各 depth は次の二つに分かれる。

```text id="c42z6p"
controlled branch:
  continuation は retention の半分以下

pressure branch:
  continuation は retention の半分超え
```

これは非常に良い整理じゃ。

Collatz の low-peeling path が「悪い」方向へ進むとき、それはただ悪いのではない。
その depth には、明確に **more-than-half continuation pressure** が発生している。

## 5. 今回閉じたもの

今回で閉じたのは、局所比較の完全分岐じゃ。

```text id="sry851"
RecoveryDominatesContinuation
  -> AtMostHalf

ContinuationOutrunsRecovery
  -> MoreThanHalf
```

source 版と tail 版の両方で閉じた。

さらに range 版でも、

```text id="i98iu5"
ContinuationOutrunsRecoveryOnRange
  -> 各 depth で MoreThanHalf pressure
```

まで読めるようになった。

つまり、finite mass calculus は次の段階に入った。

```text id="bmlbvf"
単発の質量比較
  -> 分岐
  -> range pressure profile
```

この `pressure profile` が次の主役になる。

## 6. まだ閉じていないもの

今回まだ証明していないのは、**more-than-half pressure が長く続くと何が起こるか** じゃ。

今あるのは、

$$
\forall j<len,\;R_{r+j}<K_{r+j}
$$

なら、

$$
\forall j<len,\;M_{r+j}<2K_{r+j}
$$

という局所変換。

しかし、まだ次は言っていない。

```text id="u6d4rh"
MoreThanHalf が長く続くと finite budget が逼迫する

MoreThanHalf が長く続くと height drift が増える

MoreThanHalf が長く続くと address collision が起きる

MoreThanHalf が長く続くと odd factor carrier が必要になる
```

ここから先が、次の数学的課題じゃ。

## 7. 次の指示

次は report の通り、**MoreThanHalfOnRange / ContinuationPressureOnRange** を作るのが良い。

いまは `ContinuationOutrunsRecoveryOnRange` から各 depth の `MoreThanHalf` を取り出せる。
しかし、range 全体としての pressure profile に名前がない。

したがって次 checkpoint では、まず predicate を作る。

## 7.1. generic MoreThanHalfOnRange

```lean id="ks0alo"
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
```

これは汎用的で良い。

## 7.2. source continuation pressure

```lean id="os4vs5"
def SourceContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
    (fun d => orbitWindowRetentionMassPow2 n k d)
    r len
```

## 7.3. tail continuation pressure

```lean id="zk3ea0"
def TailContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
    (fun d => orbitWindowRetentionMassPow2Tail n k d)
    r len
```

## 7.4. outruns range から pressure range

```lean id="2betqb"
theorem sourceContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len) :
    SourceContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_continuation_of_outRunsOnRange n k r len j h hj
```

tail 版も同様。

これで、range failure が range pressure に昇格する。

## 8. 一歩先ゆく推論

次の本質は、`pressure profile` を **数える** ことじゃ。

今は、

```text id="5ivh8z"
範囲内すべてが pressure
```

という強い述語を作ろうとしている。

しかし実際には、すべての depth で pressure ではなく、

```text id="ia14mx"
len 個の depth のうち、何個が pressure か
```

が欲しくなるはずじゃ。

そこで、さらに次には pressure depth count が欲しい。

```lean id="wtlk4p"
noncomputable def continuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  (List.range len).countP
    (fun j =>
      decide
        (MoreThanHalf
          (orbitWindowContinuationSiblingMassPow2 n k (r + j))
          (orbitWindowRetentionMassPow2 n k (r + j))))
```

これが入ると、

```text id="vvyr5v"
len 個中 p 個が continuation pressure
```

を Nat で言える。

そして将来的には、

$$
2p\le len
$$

や、

$$
len<2p
$$

のように、depth range 自体にも finite ratio を導入できる。

これは、`window 内の mass ratio` から `depth range 内の pressure frequency` へ一段上がることを意味する。

## 9. さらに次の一手

MoreThanHalfOnRange の次は、`MixedPressureProfile` が見えてくる。

各 depth には dichotomy がある。

```text id="o0k15n"
AtMostHalf branch
MoreThanHalf branch
```

したがって、depth range 内で、

```text id="gwwnsh"
controlled depth count
pressure depth count
```

を数えられる。

将来形はこうじゃ。

```lean id="zuky1g"
noncomputable def continuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

```lean id="na1gx8"
noncomputable def continuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

そして、

$$
\text{controlledCount}+\text{pressureCount}=len
$$

を示す。

これは checkpoint 100 の source distribution と同じ哲学じゃ。

```text id="02az94"
window mass distribution
```

から、

```text id="5y2oug"
depth-mode distribution
```

へ進む。

これはかなり DkMath 的に美しい。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: generic MoreThanHalfOnRange

```lean id="nv3olh"
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
```

## 実験 B: source pressure profile

```lean id="ewy3s3"
def SourceContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
    (fun d => orbitWindowRetentionMassPow2 n k d)
    r len
```

## 実験 C: tail pressure profile

```lean id="do8mlk"
def TailContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
    (fun d => orbitWindowRetentionMassPow2Tail n k d)
    r len
```

## 実験 D: source outruns range gives pressure profile

```lean id="gkz9oi"
theorem sourceContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len) :
    SourceContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_continuation_of_outRunsOnRange n k r len j h hj
```

## 実験 E: tail outruns range gives pressure profile

```lean id="wylh8v"
theorem tailContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len) :
    TailContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_tailContinuation_of_outRunsOnRange n k r len j h hj
```

## 実験 F: pressure profile extraction

```lean id="d0sk19"
theorem moreThanHalf_of_sourceContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  h j hj
```

tail 版も。

```lean id="t3b5uh"
theorem moreThanHalf_of_tailContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  h j hj
```

## 実験 G: pressure count skeleton

これは少し重いので、No.107 でなく No.108 でもよい。

```lean id="hhnyav"
noncomputable def sourceContinuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  (List.range len).countP
    (fun j =>
      decide
        (MoreThanHalf
          (orbitWindowContinuationSiblingMassPow2 n k (r + j))
          (orbitWindowRetentionMassPow2 n k (r + j))))
```

tail 版も同様。

## 実験 H: all-pressure range implies count equals len

pressure count を入れたら欲しい theorem。

```lean id="yniex5"
theorem sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
    (n : OddNat) (k r len : ℕ)
    (h : SourceContinuationPressureOnRange n k r len) :
    sourceContinuationPressureDepthCount n k r len = len
```

これは `List.countP_eq_length` 的な補題が必要になるかもしれない。
少し重ければ後回しでよい。

## 11. 次コミットの推奨順

```text id="h3d88x"
1. MoreThanHalfOnRange を追加

2. SourceContinuationPressureOnRange を追加

3. TailContinuationPressureOnRange を追加

4. outRunsOnRange -> PressureOnRange を source/tail で追加

5. PressureOnRange -> 各 depth の MoreThanHalf 抽出 theorem

6. docs:
   MoreThanHalfPressure から PressureProfile への接続を追記

7. 余裕があれば pressure depth count の skeleton だけ追加
```

## 12. 総括

checkpoint `106` は、失敗分岐をついに正の観測量へ変えた。

$$
R<K
$$

なら、

$$
M<2K
$$

であり、これは

```text id="ae7yss"
continuation が retention の半分超え
```

を意味する。

これで、各 depth の局所分岐は完全に読める。

```text id="jvy1r4"
RecoveryDominatesContinuation
  -> AtMostHalf

ContinuationOutrunsRecovery
  -> MoreThanHalf
```

次はこれを range profile にまとめる。
つまり、

```text id="udof5d"
failure range
  -> pressure range
```

を作る。

そこまで行けば、その次に

```text id="zzj4e2"
pressure depth count
```

を導入して、長く続く failure を有限予算として測れる。

うむ。
Collatz.PetalBridge は、ついに「失敗も観測資源に変える」段階へ入った。これは非常に良い流れじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 2a6fef01..e80fb837 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1455,6 +1455,21 @@ This intentionally avoids division: `2 * count <= k` is the finite form of
 def AtMostHalf (count k : ℕ) : Prop :=
   2 * count ≤ k
 
+/--
+Finite natural-number witness that a count occupies more than half of a window.
+
+This is the strict counterpart of `AtMostHalf`.
+-/
+def MoreThanHalf (count k : ℕ) : Prop :=
+  k < 2 * count
+
+/-- Every finite count is either at most half or more than half. -/
+theorem atMostHalf_or_moreThanHalf
+    (count k : ℕ) :
+    AtMostHalf count k ∨ MoreThanHalf count k := by
+  unfold AtMostHalf MoreThanHalf
+  omega
+
 /--
 Finite natural-number witness for `count / k <= num / den`.
 
@@ -2011,6 +2026,110 @@ def TailContinuationOutrunsRecoveryOnRange
     (n : OddNat) (k r len : ℕ) : Prop :=
   ∀ j, j < len → TailContinuationOutrunsRecovery n k (r + j)
 
+/-- Each source depth is either recovery-dominant or continuation-outrunning. -/
+theorem recoveryDominates_or_continuationOutruns
+    (n : OddNat) (k r : ℕ) :
+    RecoveryDominatesContinuation n k r ∨
+      ContinuationOutrunsRecovery n k r := by
+  unfold RecoveryDominatesContinuation ContinuationOutrunsRecovery
+  omega
+
+/-- Each tail depth is either recovery-dominant or continuation-outrunning. -/
+theorem tailRecoveryDominates_or_tailContinuationOutruns
+    (n : OddNat) (k r : ℕ) :
+    TailRecoveryDominatesContinuation n k r ∨
+      TailContinuationOutrunsRecovery n k r := by
+  unfold TailRecoveryDominatesContinuation TailContinuationOutrunsRecovery
+  omega
+
+/-- Source continuation outrunning recovery rules out recovery dominance. -/
+theorem not_recoveryDominates_of_continuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : ContinuationOutrunsRecovery n k r) :
+    ¬ RecoveryDominatesContinuation n k r := by
+  intro hdom
+  unfold ContinuationOutrunsRecovery at h
+  unfold RecoveryDominatesContinuation at hdom
+  omega
+
+/-- Tail continuation outrunning recovery rules out tail recovery dominance. -/
+theorem not_tailRecoveryDominates_of_tailContinuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : TailContinuationOutrunsRecovery n k r) :
+    ¬ TailRecoveryDominatesContinuation n k r := by
+  intro hdom
+  unfold TailContinuationOutrunsRecovery at h
+  unfold TailRecoveryDominatesContinuation at hdom
+  omega
+
+/-- Extract a source failure observation from a finite-depth failure range. -/
+theorem continuationOutrunsRecovery_of_onRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : ContinuationOutrunsRecoveryOnRange n k r len)
+    (hj : j < len) :
+    ContinuationOutrunsRecovery n k (r + j) :=
+  h j hj
+
+/-- Extract a tail failure observation from a finite-depth failure range. -/
+theorem tailContinuationOutrunsRecovery_of_onRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
+    (hj : j < len) :
+    TailContinuationOutrunsRecovery n k (r + j) :=
+  h j hj
+
+/--
+If source continuation outruns recovery, then source continuation occupies more
+than half of the parent retention mass.
+-/
+theorem moreThanHalf_continuation_of_continuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : ContinuationOutrunsRecovery n k r) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r) := by
+  unfold MoreThanHalf
+  unfold ContinuationOutrunsRecovery at h
+  rw [orbitWindowRetentionMass_split]
+  omega
+
+/--
+If tail continuation outruns tail recovery, then tail continuation occupies
+more than half of tail retention mass.
+-/
+theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : TailContinuationOutrunsRecovery n k r) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r) := by
+  unfold MoreThanHalf
+  unfold TailContinuationOutrunsRecovery at h
+  rw [orbitWindowRetentionMassPow2Tail_split]
+  omega
+
+/-- A source failure range gives more-than-half pressure at each depth. -/
+theorem moreThanHalf_continuation_of_outRunsOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : ContinuationOutrunsRecoveryOnRange n k r len)
+    (hj : j < len) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+      (orbitWindowRetentionMassPow2 n k (r + j)) :=
+  moreThanHalf_continuation_of_continuationOutruns
+    n k (r + j) (continuationOutrunsRecovery_of_onRange n k r len j h hj)
+
+/-- A tail failure range gives more-than-half pressure at each depth. -/
+theorem moreThanHalf_tailContinuation_of_outRunsOnRange
+    (n : OddNat) (k r len j : ℕ)
+    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
+    (hj : j < len) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
+  moreThanHalf_tailContinuation_of_tailContinuationOutruns
+    n k (r + j) (tailContinuationOutrunsRecovery_of_onRange n k r len j h hj)
+
 /--
 Predicate-facing source half criterion.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 7651efe2..06b26b6c 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -140,6 +140,7 @@ docs/Collatz-DepthRefinement-102.md
 docs/Collatz-TailDepthRefinement-103.md
 docs/Collatz-FiniteHalfCriterion-104.md
 docs/Collatz-ComparisonPredicates-105.md
+docs/Collatz-MoreThanHalfPressure-106.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -299,3 +300,29 @@ TailRecoveryDominatesOnRange
 These are deliberately hypothesis packages.  They mark the exact gap between
 the current finite budget calculus and a future structural contraction
 argument.
+
+Checkpoint 106 adds the complementary failure-pressure layer:
+
+```lean
+MoreThanHalf
+atMostHalf_or_moreThanHalf
+recoveryDominates_or_continuationOutruns
+tailRecoveryDominates_or_tailContinuationOutruns
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+```
+
+This turns each local comparison into a finite case split:
+
+```text
+recovery dominates continuation
+  -> continuation is at most half of retention
+
+continuation outruns recovery
+  -> continuation is more than half of retention
+```
+
+The new layer still does not assert that either branch is globally preferred.
+It makes the failure branch measurable: if dominance fails, the obstruction is
+not vague; it is strict more-than-half continuation pressure inside the
+retention cylinder.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md
new file mode 100644
index 00000000..784bd6bf
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md
@@ -0,0 +1,193 @@
+# Collatz More-Than-Half Pressure 106
+
+## Purpose
+
+Checkpoint 106 closes the local comparison split introduced at checkpoint 105.
+
+Checkpoint 105 named the desirable comparison hypotheses:
+
+```lean
+RecoveryDominatesContinuation
+TailRecoveryDominatesContinuation
+RecoveryCoversHalfRetention
+TailRecoveryCoversHalfRetention
+```
+
+Those predicates are still hypotheses.  They do not say that recovery always
+dominates continuation.  Checkpoint 106 adds the complementary branch and gives
+that branch a finite arithmetic meaning.
+
+## New Predicate
+
+The strict counterpart of `AtMostHalf` is:
+
+```lean
+def MoreThanHalf (count k : ℕ) : Prop :=
+  k < 2 * count
+```
+
+The basic finite dichotomy is:
+
+```lean
+theorem atMostHalf_or_moreThanHalf
+    (count k : ℕ) :
+    AtMostHalf count k ∨ MoreThanHalf count k
+```
+
+This keeps the layer entirely in `Nat`.  No division, rational frequency, real
+density, limit, or measure interpretation is required.
+
+## Comparison Dichotomy
+
+At each source depth:
+
+```lean
+theorem recoveryDominates_or_continuationOutruns
+    (n : OddNat) (k r : ℕ) :
+    RecoveryDominatesContinuation n k r ∨
+      ContinuationOutrunsRecovery n k r
+```
+
+At each shifted-tail depth:
+
+```lean
+theorem tailRecoveryDominates_or_tailContinuationOutruns
+    (n : OddNat) (k r : ℕ) :
+    TailRecoveryDominatesContinuation n k r ∨
+      TailContinuationOutrunsRecovery n k r
+```
+
+The reading is:
+
+```text
+either continuation is bounded by recovery,
+or continuation strictly outruns recovery.
+```
+
+The outrunning branch also refutes the dominance branch:
+
+```lean
+not_recoveryDominates_of_continuationOutruns
+not_tailRecoveryDominates_of_tailContinuationOutruns
+```
+
+These theorems are small, but they are useful for future case analyses.  They
+prevent later proofs from repeatedly unfolding the same natural-number
+comparison.
+
+## Failure Becomes Pressure
+
+The main checkpoint result is that failure is not merely a negative statement.
+It becomes a positive pressure statement.
+
+Source version:
+
+```lean
+theorem moreThanHalf_continuation_of_continuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : ContinuationOutrunsRecovery n k r) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k r)
+      (orbitWindowRetentionMassPow2 n k r)
+```
+
+Tail version:
+
+```lean
+theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
+    (n : OddNat) (k r : ℕ)
+    (h : TailContinuationOutrunsRecovery n k r) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k r)
+      (orbitWindowRetentionMassPow2Tail n k r)
+```
+
+The arithmetic proof uses the split:
+
+```text
+retention = recovery + continuation
+```
+
+and the strict comparison:
+
+```text
+recovery < continuation
+```
+
+Therefore:
+
+```text
+retention < 2 * continuation
+```
+
+This is the more-than-half pressure signature.
+
+## Range Extraction
+
+Checkpoint 106 also adds thin extraction theorems:
+
+```lean
+continuationOutrunsRecovery_of_onRange
+tailContinuationOutrunsRecovery_of_onRange
+```
+
+and range-to-pressure theorems:
+
+```lean
+moreThanHalf_continuation_of_outRunsOnRange
+moreThanHalf_tailContinuation_of_outRunsOnRange
+```
+
+Thus a finite range of failure hypotheses can be consumed one depth at a time
+without unfolding the range predicate.
+
+## Mathematical Reading
+
+The local picture is now:
+
+```text
+RecoveryDominatesContinuation
+  -> AtMostHalf continuation retention
+
+ContinuationOutrunsRecovery
+  -> MoreThanHalf continuation retention
+```
+
+This is not a Collatz proof.  It is a verified observation law for the finite
+Petal channel model.  It says that every local depth is forced into one of two
+readable modes:
+
+```text
+controlled branch:
+  continuation is at most half
+
+obstruction branch:
+  continuation is more than half
+```
+
+That is useful because an obstruction can now be accumulated, counted, or
+compared against future drift and collision constraints.
+
+## Next Candidate
+
+The next useful layer is an accumulated pressure surface over a finite depth
+range.
+
+Possible targets:
+
+```lean
+def MoreThanHalfOnRange ...
+def ContinuationPressureOnRange ...
+```
+
+or a counting theorem for the number of depths where:
+
+```text
+ContinuationOutrunsRecovery n k r
+```
+
+holds.
+
+The point is not yet to prove that the failure branch is impossible.  The next
+goal is to make prolonged failure visible as a finite, auditable pressure
+profile.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index e72ffd37..7b533a6d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -355,6 +355,46 @@ wants to consume it without unfolding recovery/continuation counts.
 
 This is the theorem to reach for before writing a custom induction over `k`.
 
+## More-Than-Half Pressure
+
+Checkpoint 106 adds the strict complement to `AtMostHalf`:
+
+```lean
+MoreThanHalf
+atMostHalf_or_moreThanHalf
+```
+
+The comparison predicates now split locally:
+
+```lean
+recoveryDominates_or_continuationOutruns
+tailRecoveryDominates_or_tailContinuationOutruns
+```
+
+The failure branch is not treated as a dead end.  It has a measurable
+consequence:
+
+```lean
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+moreThanHalf_continuation_of_outRunsOnRange
+moreThanHalf_tailContinuation_of_outRunsOnRange
+```
+
+Read this as:
+
+```text
+recovery dominates continuation
+  -> continuation is at most half of retention
+
+continuation outruns recovery
+  -> continuation is more than half of retention
+```
+
+This gives the obstruction route a concrete finite signature.  If the desired
+dominance condition fails over a range, each failed depth carries strict
+continuation pressure inside the corresponding retention cylinder.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 5634b157..18446f1e 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -177,7 +177,9 @@ tailPow2Distribution_total
 pow2ChannelFlow_of_pointwise
 AtMostHalf
 AtMostRatioNat
+MoreThanHalf
 atMostHalf_of_count_le_half
+atMostHalf_or_moreThanHalf
 atMostRatioNat_refl
 atMostHalf_iff_atMostRatioNat_one_two
 atMostRatioNat_one_one_of_le
@@ -223,6 +225,16 @@ ContinuationOutrunsRecovery
 TailContinuationOutrunsRecovery
 ContinuationOutrunsRecoveryOnRange
 TailContinuationOutrunsRecoveryOnRange
+recoveryDominates_or_continuationOutruns
+tailRecoveryDominates_or_tailContinuationOutruns
+not_recoveryDominates_of_continuationOutruns
+not_tailRecoveryDominates_of_tailContinuationOutruns
+continuationOutrunsRecovery_of_onRange
+tailContinuationOutrunsRecovery_of_onRange
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+moreThanHalf_continuation_of_outRunsOnRange
+moreThanHalf_tailContinuation_of_outRunsOnRange
 atMostHalf_continuation_of_recoveryDominates
 atMostHalf_tailContinuation_of_tailRecoveryDominates
 atMostHalf_continuation_of_recoveryCoversHalf
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-106.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-106.md
new file mode 100644
index 00000000..71dffcb7
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-106.md
@@ -0,0 +1,203 @@
+# Report Petal 106: More-Than-Half Pressure
+
+## Summary
+
+Checkpoint 106 implements the comparison split requested by
+`__next_implementation-106.md`.
+
+The previous checkpoint introduced named comparison predicates such as:
+
+```lean
+RecoveryDominatesContinuation
+ContinuationOutrunsRecovery
+```
+
+Checkpoint 106 turns them into a usable local dichotomy and gives the failure
+branch a positive finite interpretation:
+
+```text
+if continuation outruns recovery,
+then continuation is more than half of the parent retention mass.
+```
+
+This is still a finite `Nat` counting layer.  It does not use probability,
+limits, or real-valued frequency.
+
+## Lean Additions
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New finite strict-half predicate:
+
+```lean
+MoreThanHalf
+atMostHalf_or_moreThanHalf
+```
+
+Local comparison dichotomy:
+
+```lean
+recoveryDominates_or_continuationOutruns
+tailRecoveryDominates_or_tailContinuationOutruns
+```
+
+Failure excludes dominance:
+
+```lean
+not_recoveryDominates_of_continuationOutruns
+not_tailRecoveryDominates_of_tailContinuationOutruns
+```
+
+Range extraction:
+
+```lean
+continuationOutrunsRecovery_of_onRange
+tailContinuationOutrunsRecovery_of_onRange
+```
+
+Failure-pressure theorems:
+
+```lean
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+moreThanHalf_continuation_of_outRunsOnRange
+moreThanHalf_tailContinuation_of_outRunsOnRange
+```
+
+## Mathematical Result
+
+The local Petal channel split is:
+
+```text
+retention = recovery + continuation
+```
+
+Checkpoint 104 proved the controlled branch:
+
+```text
+continuation <= recovery
+  -> continuation is at most half of retention
+```
+
+Checkpoint 106 proves the obstruction branch:
+
+```text
+recovery < continuation
+  -> continuation is more than half of retention
+```
+
+So every local depth now has a readable two-way interpretation:
+
+```text
+RecoveryDominatesContinuation
+  -> AtMostHalf continuation retention
+
+ContinuationOutrunsRecovery
+  -> MoreThanHalf continuation retention
+```
+
+This is the requested False/obstruction philosophy in a small formal form.  A
+failure of the desired comparison is not thrown away; it becomes a measurable
+pressure signal.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-MoreThanHalfPressure-106.md
+```
+
+## Additional Inference
+
+The useful next observation is not an immediate global Collatz contraction.
+The proof surface now suggests a finite pressure-profile layer.
+
+If the failure branch persists over a range:
+
+```text
+ContinuationOutrunsRecoveryOnRange n k r len
+```
+
+then each depth in the range carries strict more-than-half continuation
+pressure.  This suggests the next API should package repeated pressure rather
+than trying to prove the branch impossible too early.
+
+Candidate next predicates:
+
+```lean
+def MoreThanHalfOnRange ...
+def ContinuationPressureOnRange ...
+```
+
+Candidate next theorem shape:
+
+```text
+ContinuationOutrunsRecoveryOnRange
+  -> MoreThanHalfOnRange continuation retention
+```
+
+or a count of pressure depths:
+
+```text
+number of depths j < len where continuation outruns recovery
+```
+
+This would turn prolonged obstruction into a finite object that can later be
+compared with height drift, collision, or retention-cylinder depletion.
+
+## Verification
+
+Commands run for this checkpoint:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched files>
+```
+
+Results:
+
+```text
+lake build DkMath.Collatz.PetalBridge: passed
+lake build DkMath.Collatz.Collatz2K26: passed
+rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
+git diff --check on touched files: passed
+```
+
+Known upstream warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
+```
+
+This warning is outside the Collatz `PetalBridge` checkpoint.
+
+## Next Implementation Candidate
+
+Proceed to a pressure-profile checkpoint.
+
+Recommended minimal surface:
+
+```lean
+def MoreThanHalfOnRange
+    (count total : ℕ -> ℕ) (r len : ℕ) : Prop :=
+  ∀ j, j < len -> MoreThanHalf (count (r + j)) (total (r + j))
+```
+
+Then add source/tail specializations using the existing range-to-pressure
+theorems.  Keep it thin: package the repeated observation first, and postpone
+any attempt to prove long failure ranges impossible.
````
`````
