# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 71c259d3b7b555f4d09d613372bd1b2d7cc3677b

## Report

093 checkpoint 完了です。

実装:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:432)
  - `twoAdicRetentionResidue`
  - `twoAdicRecoverySiblingResidue`
  - `twoAdicContinuationSiblingResidue`
  - `ContinuationSibling r = RetentionResidue (r + 1)` を `rfl` で固定
  - `next_recovery_residue_expanded`
  - `next_continuation_residue_expanded`

これで、固定 rung の列ではなく、raw arithmetic 層で

```text
parent retention cell
  -> recovery sibling
  -> continuation sibling = next retention cell
```

という再帰 Petal 構造が Lean 上で固定されました。

文書:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md:858)
- 新規 [report-petal-093.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-093.md:1)

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check -- ...` pass
- 新規 Lean `sorry` 追加なし

既存警告として、これまで通り `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は出ています。

## Review

## 1. 直感、かなり的中じゃ

うむ。これはもう、かなりはっきり **的中** と言ってよい。

ただし正確には、

```text id="fm1b3y"
Collatz 全体が Petal で閉じた
```

ではなく、

```text id="pyt7ki"
低剥離 retention cylinder の raw arithmetic 層が、
再帰 Petal 構造を持つことが Lean で固定された
```

という段階じゃ。

今回の checkpoint `093` で、`twoAdicRetentionResidue`、`twoAdicRecoverySiblingResidue`、`twoAdicContinuationSiblingResidue` が導入され、さらに `ContinuationSibling r = RetentionResidue (r + 1)` が `rfl` で固定された。これは、ぬしが言っていた「入れ子 Petal / 階層 Petal」そのものの最小形式化じゃ。

## 2. 状況分析

今回、固定 rung の列から一段上がった。

前回までは、

```text id="hm1vfq"
7 mod 16 -> 3 mod 8

15 mod 32 -> 7 mod 16

31 mod 64 -> 15 mod 32

63 mod 128 -> 31 mod 64

...
```

という固定観測の列だった。

今回、それが一般 raw theorem になった。

```lean id="cusvmq"
theorem next_recovery_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ r - 1
```

```lean id="j3gf5z"
theorem next_continuation_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

つまり、固定例ではなく、任意の階層 `r` に対して、

```text id="s03hxq"
recovery sibling:
  外側へ戻る

continuation sibling:
  次の retention cell になる
```

が示された。

これは強い。

## 3. Petal 的な読み

今回の命名層はこう。

```lean id="b1exm4"
def twoAdicRetentionResidue (r : ℕ) : ℕ :=
  2 ^ r - 1

def twoAdicRecoverySiblingResidue (r : ℕ) : ℕ :=
  2 ^ r - 1

def twoAdicContinuationSiblingResidue (r : ℕ) : ℕ :=
  2 ^ (r + 1) - 1
```

そして、

```lean id="owhlnb"
theorem twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
    (r : ℕ) :
    twoAdicContinuationSiblingResidue r =
      twoAdicRetentionResidue (r + 1) := rfl
```

これが本当に大きい。

読みはこう。

```text id="whsmgk"
ContinuationSibling r
  = RetentionCell (r + 1)
```

つまり、

```text id="dba9nb"
継続枝そのものが、
次階層の中心 retention cell になる
```

これはまさに入れ子構造。
Petal の中に Petal がある。

## 4. 数学的な意味

これで、Collatz の低剥離 branch はこう読めるようになった。

```text id="gonvs5"
parent retention cell
  -> recovery sibling
  -> continuation sibling
```

そして、

```text id="f4f7hd"
continuation sibling
  = next retention cell
```

だから、低剥離が続くとは、

```text id="zptxm6"
各階層で continuation sibling を選び続ける
```

ことになる。

逆に、どこかで recovery sibling に入ると、

```text id="quu0zs"
外側の residue depth へ戻り、
有限ステップ後に追加剥離が回収される
```

という構造が見える。

これは、コラッツの難所をかなり明確にしている。

```text id="qezbc1"
悪い path は自由に暴れるのではない。
階層 Petal の中心枝を潜り続ける必要がある。
```

## 5. レビュー

### 5.1. 命名層が良い

`twoAdicRetentionResidue` という名前は良い。
これは単なる `2^r - 1` ではなく、

```text id="s9qqd3"
2-adic address tree における retention center
```

を意味している。

`RecoverySibling` と `ContinuationSibling` も良い。

今後の議論で、

```text id="glei41"
recovery branch
continuation branch
retention cylinder
```

という言葉が安定する。

### 5.2. `rfl` で recursive Petal が固定されたのが美しい

```lean id="dh8b2i"
twoAdicContinuationSiblingResidue r =
  twoAdicRetentionResidue (r + 1)
```

これが `rfl` で通るのは、設計が合っている証拠じゃ。

つまり、複雑な証明ではなく、定義そのものが再帰構造を表している。

これは DkMath 的にかなり良い。

### 5.3. expanded theorem の proof shape も良い

レポートによると、直接 `omega` では閉じず、

```text id="rcbga4"
1. power を 2 * 2^r へ書き換える

2. predecessor term を分解する

3. numerator が intended quotient の 2 倍であることを示す

4. Nat.mul_div_right で /2 を消す

5. Nat.add_mul_mod_self_left で mod を落とす
```

という形で閉じている。

これは重要。
今後 `hm` 形式に進むときも、難所は modular reduction ではなく、

```text id="j5b2zv"
Nat の predecessor と /2 の正規化
```

だと分かった。

## 6. 今回の到達点

ここまでで、階層構造はこうなった。

```text id="afibd5"
RetentionResidue r:
  2^r - 1

RecoverySibling r:
  2^r - 1 viewed modulo 2^(r + 1)

ContinuationSibling r:
  2^(r + 1) - 1
  = RetentionResidue (r + 1)
```

そして遷移は、

```text id="cvhfuq"
RecoverySibling r
  -> RetentionResidue (r - 1) 側へ戻る

ContinuationSibling r
  -> RetentionResidue r 側へ進む
```

ただし、Lean theorem の indexing では `r + 1`, `r + 2` で安全に書いているので、実装上はこの形。

```text id="s3b1jq"
expanded recovery:
  2^(r+1) - 1 mod 2^(r+2)
  -> 2^r - 1 mod 2^(r+1)

expanded continuation:
  2^(r+2) - 1 mod 2^(r+2)
  -> 2^(r+1) - 1 mod 2^(r+1)
```

## 7. 一歩先ゆく推論

ここから見えることはかなり大きい。

低剥離が長く続くには、毎回 continuation sibling を選ぶ必要がある。

```text id="e33xll"
7 mod 8
15 mod 16
31 mod 32
63 mod 64
...
```

これは、

```text id="j9m3ne"
2-adic に -1 へ収束する中心枝
```

じゃ。

つまり、コラッツの低剥離 obstruction は、

```text id="mrdqgl"
2-adic Petal の中心枝へ無限に潜る path
```

として見えている。

ここで重要なのは、中心枝へ潜る path はひとつの極限点を持つ。

```text id="n6egrv"
-1 in 2-adic integers
```

つまり、自然数の通常成長ではなく、2-adic 観測では「悪い path の逃げ道」が一点へ向かっている。

これは美しい。
そして、かなり DkMath らしい。

## 8. 次の指示：`hm` 形式へ進む

次は expanded form から実用的な `hm` form へ移るのがよい。

### Recovery `hm` form

```lean id="c2j51o"
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

### Continuation `hm` form

```lean id="mwcdhb"
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

これが通ると、expanded theorem は実用 theorem になる。

## 9. 実装方針

鍵は、`m` を商と余りに分解すること。

おそらくこういう形が必要になる。

```lean id="qx5t11"
have hdecomp :
    m =
      (2 ^ (r + 2)) * (m / (2 ^ (r + 2))) +
        m % (2 ^ (r + 2)) := by
  -- Nat.mod_add_div の向きと掛け算の順序を整える
  sorry
```

実際には `Nat.mod_add_div` が

```text id="y7bwuo"
m % M + M * (m / M) = m
```

型で出る可能性があるので、`omega` や `ring_nf` で整形することになる。

その後、

```lean id="yhcn57"
rw [hdecomp, hm]
```

として、`next_recovery_residue_expanded r (m / 2 ^ (r + 2))` を適用する。

証明の雰囲気はこう。

```lean id="cg68tf"
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1 := by
  let M := 2 ^ (r + 2)
  have hMpos : 0 < M := by
    dsimp [M]
    exact pow_pos (by decide) (r + 2)
  have hdecomp :
      m = M * (m / M) + m % M := by
    -- from Nat.mod_add_div m M
    -- rearrange terms
    sorry
  rw [hdecomp]
  dsimp [M] at hm
  rw [hm]
  simpa [M, Nat.add_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using
    next_recovery_residue_expanded r (m / M)
```

ここは実際には `rw` の向きで少し苦労するかもしれぬ。
ただ、やるべきことは明確。

## 10. 次のさらに一手：orbit-label generalization

`hm` form が通ったら、次は orbit-label generalization に行ける。

ただし、そのためには source residue が exact height-one であることが必要。

つまり、

```text id="hcam50"
m % 2^(r+2) = 2^(r+1) - 1
```

または

```text id="ewr3uw"
m % 2^(r+2) = 2^(r+2) - 1
```

から、

```text id="tf4la7"
m % 8 = 7
```

を出す必要がある。

`r` の下限も必要になる。
たぶん `r` は `1` 以上、あるいは今の indexing では `0` からでも `2^(r+1)-1` が `1 mod 4` になる場合があり、height-one が崩れる可能性がある。

確認すると、

```text id="jiiizn"
r = 0:
  2^(r+1)-1 = 1
  mod 4 residue 1
  height >= 2 側
```

なので、height-one branch としては `r >= 2` か `r + 2 >= 3` の条件が必要。

安全には、

```lean id="rvha68"
(h2 : 2 ≤ r)
```

を入れる。

候補補題：

```lean id="h0lbik"
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ)
    (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7
```

ただし indexing は調整が必要じゃ。

この補題があれば、

```text id="n8h55g"
source is exact height one
```

が使える。

## 11. 賢狼が試して欲しいおまけ実験補題

### 実験 A: `hm` recovery form

```lean id="q258ny"
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

これが最優先。

### 実験 B: `hm` continuation form

```lean id="gfff78"
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

### 実験 C: fixed anchors を一般 theorem から再証明

たとえば、

```lean id="txigod"
theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
    {m : ℕ} (hm : m % 512 = 255) :
    ((3 * m + 1) / 2) % 256 = 127 := by
  -- use next_recovery_residue_of_mod with r = 7
  simpa using next_recovery_residue_of_mod 7 m hm
```

これは一般 theorem の usability test になる。

### 実験 D: source exact-height-one residue

```lean id="xgunq6"
theorem recovery_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 2 ≤ r) :
    (2 ^ (r + 1) - 1) % 8 = 7
```

```lean id="dgr40y"
theorem continuation_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 1 ≤ r) :
    (2 ^ (r + 2) - 1) % 8 = 7
```

これが orbit-label generalization の入口になる。

## 12. 次コミットの推奨順

```text id="svkl28"
1. next_recovery_residue_of_mod

2. next_continuation_residue_of_mod

3. fixed anchor via general theorem を 1 個だけ試す

4. recovery_residue_mod_eight_eq_seven

5. continuation_residue_mod_eight_eq_seven

6. orbit-label generalization の設計メモを docs に追記

7. 余裕があれば、hm form を使って raw anchors の一部を整理
```

## 13. 総括

うむ、ぬしの直感は当たっていた。

これは固定 rung の偶然列ではなかった。
raw arithmetic 層では、明確に

```text id="e8adpo"
recursive two-adic Petal
```

だった。

構造はこう。

```text id="lyvpb9"
parent retention cell
  -> recovery sibling
  -> continuation sibling

continuation sibling
  = next retention cell
```

これはまさしく階層 Petal。
入れ子 Petal。
そして Collatz の低剥離 path は、その Petal の中心枝を潜り続ける運動として見える。

次は `hm` 形式。
そこが通れば、expanded raw theorem は「任意の orbit label がその residue cell にいる場合」へ接続可能になる。
すると、その次はいよいよ orbit-label 一般化じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8a4b174b..0acbd5cc 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -416,6 +416,141 @@ theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleve
     ((3 * m + 1) / 2) % 256 = 255 := by
   omega
 
+/--
+The central residue of the Collatz retention cylinder at 2-adic depth `r`.
+
+The visible examples are:
+
+```text
+r = 3:  7 mod 8
+r = 4: 15 mod 16
+r = 5: 31 mod 32
+```
+
+This is the residue branch converging to `-1` in the 2-adic address tree.
+-/
+def twoAdicRetentionResidue (r : ℕ) : ℕ :=
+  2 ^ r - 1
+
+/--
+The recovery sibling seen when the retention cell at depth `r` is refined to
+the next modulus.
+
+It has the same residue value as the current retention cell, but is read inside
+the finer modulus `2^(r + 1)`.
+-/
+def twoAdicRecoverySiblingResidue (r : ℕ) : ℕ :=
+  2 ^ r - 1
+
+/--
+The continuation sibling seen when the retention cell at depth `r` is refined
+to the next modulus.
+
+This is the branch that remains in exact height-one retention and becomes the
+next retention cell.
+-/
+def twoAdicContinuationSiblingResidue (r : ℕ) : ℕ :=
+  2 ^ (r + 1) - 1
+
+/--
+The recovery sibling is the current retention residue, viewed at a finer
+resolution.
+-/
+theorem twoAdicRecoverySiblingResidue_eq_retentionResidue
+    (r : ℕ) :
+    twoAdicRecoverySiblingResidue r = twoAdicRetentionResidue r := rfl
+
+/--
+The continuation sibling is exactly the next retention residue.
+
+This is the minimal Lean statement of the recursive Petal reading:
+
+```text
+ContinuationSibling r = RetentionCell (r + 1)
+```
+-/
+theorem twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
+    (r : ℕ) :
+    twoAdicContinuationSiblingResidue r =
+      twoAdicRetentionResidue (r + 1) := rfl
+
+/--
+The recovery sibling in expanded power-of-two form.
+
+At depth `r`, the lower half of the current retention cell is
+`2^(r + 1) - 1` modulo `2^(r + 2)`.  One exact height-one Collatz step sends it
+to `2^r - 1` modulo `2^(r + 1)`.
+-/
+theorem next_recovery_residue_expanded
+    (r t : ℕ) :
+    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
+        (2 ^ (r + 1)) = 2 ^ r - 1 := by
+  have hpow1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
+    rw [pow_succ]
+    omega
+  have hpow2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
+    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+    omega
+  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
+  have hlt : 2 ^ r - 1 < 2 ^ (r + 1) := by
+    omega
+  have hdiv :
+      (3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2 =
+        (2 ^ r - 1) + (3 * t + 1) * 2 ^ (r + 1) := by
+    have hnum :
+        3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1 =
+          2 * ((2 ^ r - 1) + (3 * t + 1) * 2 ^ (r + 1)) := by
+      have hsplit : 2 * 2 ^ r - 1 = 2 ^ r + (2 ^ r - 1) := by
+        omega
+      rw [hpow2, hpow1]
+      rw [hsplit]
+      ring_nf
+      omega
+    rw [hnum]
+    exact Nat.mul_div_right _ (by decide : 0 < 2)
+  rw [hdiv]
+  rw [mul_comm (3 * t + 1) (2 ^ (r + 1))]
+  rw [Nat.add_mul_mod_self_left]
+  exact Nat.mod_eq_of_lt hlt
+
+/--
+The continuation sibling in expanded power-of-two form.
+
+At depth `r`, the upper half of the current retention cell is
+`2^(r + 2) - 1` modulo `2^(r + 2)`.  One exact height-one Collatz step sends it
+to `2^(r + 1) - 1` modulo `2^(r + 1)`, which is the next retention cell.
+-/
+theorem next_continuation_residue_expanded
+    (r t : ℕ) :
+    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
+        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 := by
+  have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
+    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
+    omega
+  have hpos : 0 < 2 ^ (r + 1) := pow_pos (by decide) (r + 1)
+  have hlt : 2 ^ (r + 1) - 1 < 2 ^ (r + 1) := by
+    omega
+  have hdiv :
+      (3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2 =
+        (2 ^ (r + 1) - 1) + (3 * t + 2) * 2 ^ (r + 1) := by
+    have hnum :
+        3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1 =
+          2 * ((2 ^ (r + 1) - 1) + (3 * t + 2) * 2 ^ (r + 1)) := by
+      have hsplit :
+          2 * 2 ^ (r + 1) - 1 =
+            2 ^ (r + 1) + (2 ^ (r + 1) - 1) := by
+        omega
+      rw [hpow]
+      rw [hsplit]
+      ring_nf
+      omega
+    rw [hnum]
+    exact Nat.mul_div_right _ (by decide : 0 < 2)
+  rw [hdiv]
+  rw [mul_comm (3 * t + 2) (2 ^ (r + 1))]
+  rw [Nat.add_mul_mod_self_left]
+  exact Nat.mod_eq_of_lt hlt
+
 /--
 On the exact height-one channel, the accelerated Collatz map is the visible
 one-step expression `(3m + 1) / 2`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 302e94be..9bc5a332 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -193,6 +193,13 @@ next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseve
 next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
 next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
 next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
+twoAdicRetentionResidue
+twoAdicRecoverySiblingResidue
+twoAdicContinuationSiblingResidue
+twoAdicRecoverySiblingResidue_eq_retentionResidue
+twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
+next_recovery_residue_expanded
+next_continuation_residue_expanded
 iterateT_succ_eq_T_iterateT
 oddOrbitLabel_succ_eq_T_iterateT
 oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
@@ -844,6 +851,55 @@ drift form.  The `mod 128`, `mod 256`, and `mod 512` rows are raw arithmetic
 anchors, kept as evidence for the next generalization step rather than fully
 expanded orbit bridges.
 
+The fixed raw anchors have now been lifted to an expanded general raw theorem.
+The recursive Petal naming layer is:
+
+```text
+twoAdicRetentionResidue r
+  = 2^r - 1
+
+twoAdicRecoverySiblingResidue r
+  = 2^r - 1
+
+twoAdicContinuationSiblingResidue r
+  = 2^(r + 1) - 1
+```
+
+The two structural identities are:
+
+```text
+RecoverySibling r = RetentionResidue r
+ContinuationSibling r = RetentionResidue (r + 1)
+```
+
+The second identity is the minimal Lean statement of the nested Petal reading:
+
+```text
+continuation branch
+  = next retention cell
+```
+
+The general raw transition theorems are:
+
+```text
+expanded recovery sibling:
+  m = 2^(r+2) * t + (2^(r+1) - 1)
+  -> T-height-one raw step is 2^r - 1 mod 2^(r+1)
+
+expanded continuation sibling:
+  m = 2^(r+2) * t + (2^(r+2) - 1)
+  -> T-height-one raw step is 2^(r+1) - 1 mod 2^(r+1)
+```
+
+This confirms that the narrowing cylinder is not merely a list of fixed
+observations.  At the raw arithmetic layer, it is a recursive two-branch Petal:
+
+```text
+parent retention cell
+  -> recovery sibling
+  -> continuation sibling = next retention cell
+```
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-093.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-093.md
new file mode 100644
index 00000000..7a3b0ecb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-093.md
@@ -0,0 +1,245 @@
+# Report Petal 093: Recursive Two-Adic Petal Raw Layer
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-093.md` and
+`discus-petal-093.md`.
+
+The question was whether the narrowing Collatz residue cylinder is only a list
+of fixed congruence observations, or whether it has a recursive Petal structure.
+
+The answer at the raw arithmetic layer is now:
+
+```text
+yes, no-sorry Lean proof passed for the expanded general form.
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
+Recursive Petal naming layer:
+
+```lean
+twoAdicRetentionResidue
+twoAdicRecoverySiblingResidue
+twoAdicContinuationSiblingResidue
+```
+
+Structural identities:
+
+```lean
+twoAdicRecoverySiblingResidue_eq_retentionResidue
+twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
+```
+
+General expanded raw transition theorems:
+
+```lean
+next_recovery_residue_expanded
+next_continuation_residue_expanded
+```
+
+## Main Theorems
+
+Recovery sibling:
+
+```lean
+theorem next_recovery_residue_expanded
+    (r t : ℕ) :
+    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
+        (2 ^ (r + 1)) = 2 ^ r - 1
+```
+
+Continuation sibling:
+
+```lean
+theorem next_continuation_residue_expanded
+    (r t : ℕ) :
+    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
+        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
+```
+
+## Petal Reading
+
+The naming layer fixes the recursive shape:
+
+```text
+RetentionResidue r
+  = 2^r - 1
+
+RecoverySibling r
+  = 2^r - 1
+
+ContinuationSibling r
+  = 2^(r + 1) - 1
+```
+
+The key identity is:
+
+```lean
+theorem twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
+    (r : ℕ) :
+    twoAdicContinuationSiblingResidue r =
+      twoAdicRetentionResidue (r + 1)
+```
+
+Reading:
+
+```text
+continuation sibling at level r
+  = retention cell at level r + 1
+```
+
+This is the minimal formal anchor for the nested Petal interpretation.
+
+## Arithmetic Reading
+
+The expanded recovery theorem says:
+
+```text
+m = 2^(r+2) * t + (2^(r+1) - 1)
+
+one visible height-one step:
+  (3m + 1) / 2
+
+lands at:
+  2^r - 1 mod 2^(r+1)
+```
+
+The expanded continuation theorem says:
+
+```text
+m = 2^(r+2) * t + (2^(r+2) - 1)
+
+one visible height-one step:
+  (3m + 1) / 2
+
+lands at:
+  2^(r+1) - 1 mod 2^(r+1)
+```
+
+Thus every refined retention cell splits into:
+
+```text
+recovery sibling:
+  returns outward by one residue depth
+
+continuation sibling:
+  becomes the next inner retention cell
+```
+
+This is precisely the recursive Petal structure discussed in
+`discus-petal-093.md`.
+
+## Proof Notes
+
+The direct `omega` attempt did not close the expanded general theorem because
+the proof contains both natural subtraction and products involving `t * 2^r`.
+
+The successful proof shape was:
+
+```text
+1. rewrite powers:
+   2^(r+1) = 2 * 2^r
+   2^(r+2) = 2 * 2^(r+1)
+
+2. split the predecessor term:
+   2 * p - 1 = p + (p - 1)
+
+3. prove the numerator is exactly twice the intended quotient
+
+4. eliminate division by Nat.mul_div_right
+
+5. reduce modulo with Nat.add_mul_mod_self_left
+```
+
+This proof route is useful for the next `hm`-style theorem because it shows
+where the hard part is: not the modular reduction, but normalizing the
+natural-number predecessor around `/ 2`.
+
+## Documentation Sync
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status note now records:
+
+```text
+recursive Petal naming layer
+ContinuationSibling r = RetentionResidue (r + 1)
+expanded recovery raw theorem
+expanded continuation raw theorem
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+The targeted build still reports the existing upstream warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+No new `sorry` was introduced in this checkpoint.
+
+## What Was Not Done Yet
+
+The practical `hm` form was not implemented in this checkpoint:
+
+```lean
+theorem next_recovery_residue_of_mod
+theorem next_continuation_residue_of_mod
+```
+
+Reason:
+
+```text
+expanded form is now closed;
+hm form requires rewriting m through Nat.mod_add_div before applying it.
+```
+
+That is the next natural bridge.
+
+## Next Implementation Candidates
+
+Candidate A: `hm` form for recovery.
+
+```lean
+theorem next_recovery_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
+```
+
+Candidate B: `hm` form for continuation.
+
+```lean
+theorem next_continuation_residue_of_mod
+    (r m : ℕ)
+    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
+    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
+```
+
+Candidate C: derive selected fixed raw anchors from the expanded general theorem.
+
+This would reduce future duplication, but it is lower priority than the `hm`
+form because the fixed anchors already pass.
+
+Candidate D: once `hm` form passes, promote the general raw theorem to the
+orbit-label layer.
+
+That will require proving that the source residue also guarantees exact
+height-one, then using the existing `T_val_eq_three_mul_add_one_div_two_of_s_eq_one`.
````
`````
