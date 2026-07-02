# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: aade40a9dc06f28f4dbe701794812c3ca9ee9b56

## Report

実装完了です。Checkpoint 102 として、`DkMath.Collatz.PetalBridge` に depth refinement と retention split を追加しました。

主な追加:

- `orbitWindowResidueCountPow2_refine_succ`
- `orbitWindowRetentionMass_split`
- `orbitWindowRecoverySiblingMassPow2_le_retentionMass`
- `orbitWindowContinuationSiblingMassPow2_le_retentionMass`
- tail sibling mass の window bound
- pointwise / indicator split 補題群

ドキュメントも同期しました。

- [Collatz-DepthRefinement-102.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md)
- [report-petal-102.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-102.md)
- README / Guide / Status も更新済み

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `DkMath.Collatz.PetalBridge.lean` 内の `sorry` は一致なし

既知の上流 warning として、従来通り `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152` の `sorry` 警告は出ています。今回の追加とは別件です。

## Review

## 1. 状況分析

うむ。checkpoint `102` は、かなり重要な山を越えた。

No.100 で finite channel-flow を閉じ、No.101 で retention / recovery / continuation mass の名前を付けた。
そして今回 No.102 で、その named mass が本当に **親 cell と子 cell の分解** として働くことを Lean で証明した。

主成果はこれじゃ。

```lean
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
```

レポートでも、checkpoint 102 の主結果は `orbitWindowRetentionMass_split`、つまり retention mass at depth `r` が recovery sibling mass と continuation sibling mass の和に等しいことだと整理されている。

数学的に言えば、ついにこの式が閉じた。

$$
M_r(n,k)=R_r(n,k)+K_r(n,k)
$$

ここで、

$$
M_r(n,k)=C_{r,\,2^r-1}(n,k)
$$

$$
R_r(n,k)=C_{r+1,\,2^r-1}(n,k)
$$

$$
K_r(n,k)=C_{r+1,\,2^{r+1}-1}(n,k)
$$

じゃ。

これは、Collatz の low-peeling retention cylinder が、次の深さで recovery sibling と continuation sibling に正確に分かれることを意味する。

## 2. 今回の核心

今回の proof chain は非常に良い。

```text
pointwise residue split
  -> reverse collapse lemma
  -> indicator split
  -> count refinement
  -> retention split
  -> child mass <= parent mass
```

特に重要なのは、いきなり count theorem に行かず、まず一点 \(x\) の residue 分解を示したことじゃ。

固定 depth \(d\)、valid residue \(a < 2^d\) について、

$$
x\bmod 2^d=a
$$

ならば、次の深さでは必ず二つのどちらかに入る。

$$
x\bmod 2^{d+1}=a
$$

または、

$$
x\bmod 2^{d+1}=a+2^d
$$

これが `mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq`。

逆向きもある。

```lean
mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
```

そしてこの二つを使って indicator equality を作った。

```lean
pow2ResidueIndicator_refine_succ
```

これが非常に大事。
count theorem は、結局 `0/1` indicator の和なので、ここが通れば自然に count split に持ち上がる。

## 3. レビュー

## 3.1. 一般 refinement を先に閉じたのが正解

今回、retention 専用に逃げず、

```lean
orbitWindowResidueCountPow2_refine_succ
```

を一般形で通したのは大きい。

この theorem は、今後 retention 以外にも使える。

数学的には、

$$
C_{d,a}(n,k)=C_{d+1,a}(n,k)+C_{d+1,a+2^d}(n,k)
$$

である。

これは `mod 2^d` の cell が、`mod 2^(d+1)` で左右二つの child cell に分かれるという、Petal refinement の基本法則じゃ。

ここが一般 theorem として入ったので、次から任意の residue cell を depth refinement できる。

## 3.2. retention split が美しい

今回の特殊化、

```lean
orbitWindowRetentionMass_split
```

は、DkMath 的にはかなり重要。

$$
\text{RetentionMass}=\text{RecoverySiblingMass}+\text{ContinuationSiblingMass}
$$

が Lean theorem になった。

これは、「recovery と continuation は別々に追加された質量ではない」ということを保証する。
同じ親 retention cylinder の中の二つの子 cell であり、合計すると親に戻る。

つまり、

```text
retention cylinder
  -> recovery child
  -> continuation child
```

という Petal の入れ子構造が count-level で閉じた。

## 3.3. child mass bound は次の ratio 層に効く

今回追加された二つ、

```lean
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
```

は、一見すると `omega` で落ちる小補題に見える。

しかし意味は大きい。

$$
R_r(n,k)\le M_r(n,k)
$$

$$
K_r(n,k)\le M_r(n,k)
$$

これにより、No.101 で導入した `AtMostRatioNat` の対象が明確になった。

たとえば次に、

$$
2K_r(n,k)\le M_r(n,k)
$$

のような「continuation が親の半分以下」という命題を考えられる。

まだ証明はない。
しかし、比率を語る対象ができた。

## 4. 数学的解説

今回閉じた事実は、合同算術としては素朴じゃ。

任意の自然数 \(x\) は、mod \(2^{d+1}\) で見れば、mod \(2^d\) の情報に 1 bit 追加したものになる。

親 cell が

$$
a\pmod {2^d}
$$

なら、子 cell は二つ。

$$
a\pmod {2^{d+1}}
$$

$$
a+2^d\pmod {2^{d+1}}
$$

である。

したがって、有限 window の中で親 cell にいる label 数は、二つの子 cell にいる label 数の和に等しい。

$$
\#{i<k\mid q_i\bmod 2^d=a} =
\#{i<k\mid q_i\bmod 2^{d+1}=a} +
\#{i<k\mid q_i\bmod 2^{d+1}=a+2^d}
$$

これを retention residue \(a=2^r-1\) に適用すると、

$$
2^r-1+2^r=2^{r+1}-1
$$

なので、

$$
C_{r,\,2^r-1}=C_{r+1,\,2^r-1}+C_{r+1,\,2^{r+1}-1}
$$

となる。

これはまさに、

```text
retention
  = recovery sibling + continuation sibling
```

じゃ。

## 5. 今回閉じたもの

今回で閉じたのは、次の層じゃ。

```text
No.100:
  source / tail finite distribution

No.101:
  retention / sibling mass names

No.102:
  parent retention mass split into child sibling masses
```

つまり、これで Petal の階層構造が count-level で動き始めた。

以前は、

```text
continuation sibling は次の retention cell である
```

という residue の話だった。

今は、

```text
retention mass は recovery mass と continuation mass に分かれる
```

という有限質量の話になった。

ここは大きな進展じゃ。

## 6. 注意点

今回の theorem は source-window 側の refinement である。

```lean
orbitWindowResidueCountPow2_refine_succ
```

tail 側の対応 theorem は、まだ追加されていないように見える。

今後、tail retention mass も同じように split したくなるはずじゃ。

$$
M^{tail}_r(n,k)=R^{tail}_r(n,k)+K^{tail}_r(n,k)
$$

これはおそらく同じ証明パターンで通る。

したがって、No.103 では tail refinement を補っておくと、source / tail symmetry がかなり良くなる。

## 7. 次の指示

次は二択じゃ。

```text
A. tail 側の refinement / retention split を閉じる

B. source split を使って continuation forcing theorem へ進む
```

賢狼としては、先に A を推す。

理由は、No.100 で source / tail distribution を対で扱ったから。
No.102 の split も source / tail 両方にある方が後で使いやすい。

## 7.1. tail count refinement

まずは一般形。

```lean
theorem orbitWindowResidueCountPow2Tail_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2Tail n k depth residue =
      orbitWindowResidueCountPow2Tail n k (depth + 1) residue +
        orbitWindowResidueCountPow2Tail n k (depth + 1) (residue + 2 ^ depth)
```

証明は source 版とほぼ同じはず。

`orbitWindowResidueCountPow2Tail_succ` と `pow2ResidueIndicator_refine_succ` を使えば行ける。

## 7.2. tail retention split

その特殊化。

```lean
theorem orbitWindowRetentionMassTail_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r =
      orbitWindowRecoverySiblingMassPow2Tail n k r +
        orbitWindowContinuationSiblingMassPow2Tail n k r
```

これが通れば、tail 側でも

$$
M^{tail}_r=R^{tail}_r+K^{tail}_r
$$

が言える。

## 8. 一歩先ゆく推論

tail split が入ると、いよいよ continuation forcing を美しく書ける。

すでにある theorem は、

```lean
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
```

これを数式で読むと、

$$
K_{r+1}(n,k)\le M^{tail}_{r+1}(n,k)
$$

である。

tail split が入れば、

$$
M^{tail}*{r+1}(n,k)=R^{tail}*{r+1}(n,k)+K^{tail}_{r+1}(n,k)
$$

だから、

$$
K_{r+1}(n,k)\le R^{tail}*{r+1}(n,k)+K^{tail}*{r+1}(n,k)
$$

と読める。

これは当たり前の上界に見えるが、意味はこうじゃ。

```text
source continuation mass が大きければ、
次窓の retention cylinder 全体も大きくなければならない
```

つまり、低剥離を続ける質量は、次窓でも retention cylinder に押し込まれる。

ここからさらに、

```text
tail retention が次に recovery / continuation にどう分かれるか
```

を追える。

これが iterative mass-flow の入口になる。

## 9. さらに次の一手

tail split の後は、次の命題が欲しい。

```lean
theorem orbitWindowContinuationMass_forces_tailRetention
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1)
```

これは既存 theorem と同じ、または alias で済むかもしれない。
すでに `orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass` があるので、No.103 ではこれにより読みやすい alias を置く程度でも良い。

さらに、tail split と組み合わせて、

```lean
theorem orbitWindowContinuationMass_forces_tailRecovery_or_tailContinuation
```

のような名前を docs-only で考えられる。

ただし、Lean theorem として `or` にするより、まずは等式と不等式のままが良い。

```text
K_source <= M_tail
M_tail = R_tail + K_tail
```

この二本を組み合わせる方が柔軟じゃ。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: tail refinement general

```lean
theorem orbitWindowResidueCountPow2Tail_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2Tail n k depth residue =
      orbitWindowResidueCountPow2Tail n k (depth + 1) residue +
        orbitWindowResidueCountPow2Tail n k (depth + 1) (residue + 2 ^ depth) := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [ih]
      have hindicator :=
        pow2ResidueIndicator_refine_succ (oddOrbitLabel n (k + 1)) depth residue hres
      omega
```

## 実験 B: tail retention split

```lean
theorem orbitWindowRetentionMassPow2Tail_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r =
      orbitWindowRecoverySiblingMassPow2Tail n k r +
        orbitWindowContinuationSiblingMassPow2Tail n k r := by
  unfold orbitWindowRetentionMassPow2Tail
  unfold orbitWindowRecoverySiblingMassPow2Tail
  unfold orbitWindowContinuationSiblingMassPow2Tail
  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
  have hsplit :=
    orbitWindowResidueCountPow2Tail_refine_succ n k r (2 ^ r - 1) hres
  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega
  simpa [hright] using hsplit
```

## 実験 C: tail child masses bounded by tail retention

```lean
theorem orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega
```

```lean
theorem orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega
```

## 実験 D: forcing alias

```lean
theorem orbitWindowContinuationMass_forces_tailRetention
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass r hr n k
```

名前を少し変えるだけでも、次章で読みやすくなる。

## 実験 E: source recovery forcing alias

```lean
theorem orbitWindowRecoveryMass_forces_tailRecovery
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k r :=
  orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass r hr n k
```

## 11. 次コミットの推奨順

```text
1. orbitWindowResidueCountPow2Tail_refine_succ

2. orbitWindowRetentionMassPow2Tail_split

3. tail recovery / continuation child <= tail retention

4. continuation forcing alias

5. recovery forcing alias

6. docs:
   source split / tail split / forcing の関係を追記
```

ここまで行くと、source と tail の両方で retention cylinder の分解が閉じる。

その後に、いよいよ `AtMostHalf` を使った finite contraction candidate に入るとよい。

## 12. 総括

checkpoint `102` は、No.101 で名前を付けた retention mass に、数学的な中身を与えた。

今回の核心は、

$$
M_r=R_r+K_r
$$

である。

これは、低剥離 retention cylinder が、recovery sibling と continuation sibling に正確に分かれることを示す。

ここまでで、

```text
finite channel-flow
  -> finite ratio witness
  -> retention mass
  -> depth refinement
  -> retention split
```

まで到達した。

次は tail 側の split を揃え、source continuation mass が tail retention mass を強制する流れを名前付きで固定するのが良い。

うむ。
Petal が Collatz にしっかり根を張ってきた。
これはかなり良い進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index eeb91d2c..8dcdb4e9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1576,6 +1576,200 @@ theorem orbitWindowContinuationSiblingMassPow2_le_window
   unfold orbitWindowContinuationSiblingMassPow2
   exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ (r + 1) - 1)
 
+/-- Shifted-tail recovery sibling mass is bounded by the window size. -/
+theorem orbitWindowRecoverySiblingMassPow2Tail_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRecoverySiblingMassPow2Tail n k r ≤ k := by
+  unfold orbitWindowRecoverySiblingMassPow2Tail
+  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ r - 1)
+
+/-- Shifted-tail continuation sibling mass is bounded by the window size. -/
+theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowContinuationSiblingMassPow2Tail n k r ≤ k := by
+  unfold orbitWindowContinuationSiblingMassPow2Tail
+  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ (r + 1) - 1)
+
+/-- The all-ones retention residue is inside its power-of-two modulus. -/
+theorem twoAdicRetentionResidue_lt_pow
+    (r : ℕ) :
+    2 ^ r - 1 < 2 ^ r := by
+  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
+  omega
+
+/--
+Pointwise refinement of a power-of-two residue cell.
+
+If `residue` is a valid cell at depth `depth`, then a number in that cell has
+one of exactly two residues at depth `depth + 1`: the left child `residue` or
+the right child `residue + 2^depth`.
+-/
+theorem mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+    (x depth residue : ℕ)
+    (_hres : residue < 2 ^ depth)
+    (h : x % (2 ^ depth) = residue) :
+    x % (2 ^ (depth + 1)) = residue ∨
+      x % (2 ^ (depth + 1)) = residue + 2 ^ depth := by
+  let m := 2 ^ depth
+  let y := x % (2 ^ (depth + 1))
+  have hmpos : 0 < m := by
+    dsimp [m]
+    exact pow_pos (by decide) depth
+  have hpow : 2 ^ (depth + 1) = 2 * m := by
+    dsimp [m]
+    rw [pow_succ]
+    ring
+  have hmod : y % m = residue := by
+    dsimp [y, m]
+    rw [← h]
+    rw [Nat.mod_mod_of_dvd]
+    · exact ⟨2, by rw [hpow, Nat.mul_comm]⟩
+  have hylt : y < 2 * m := by
+    dsimp [y]
+    rw [hpow]
+    exact Nat.mod_lt _ (Nat.mul_pos (by decide) hmpos)
+  have hdecomp : y = y % m + m * (y / m) := by
+    exact (Nat.mod_add_div y m).symm
+  have hydiv_lt : y / m < 2 := by
+    exact (Nat.div_lt_iff_lt_mul hmpos).2 hylt
+  have hydiv_cases : y / m = 0 ∨ y / m = 1 :=
+    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hydiv_lt)
+  cases hydiv_cases with
+  | inl hzero =>
+      left
+      rw [hzero, mul_zero, add_zero, hmod] at hdecomp
+      dsimp [y] at hdecomp
+      exact hdecomp
+  | inr hone =>
+      right
+      rw [hone, mul_one, hmod] at hdecomp
+      dsimp [y, m] at hdecomp
+      exact hdecomp
+
+/--
+The two child residues at the next power-of-two depth both collapse back to
+the parent residue.
+-/
+theorem mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+    (x depth residue : ℕ)
+    (hres : residue < 2 ^ depth)
+    (h :
+      x % (2 ^ (depth + 1)) = residue ∨
+        x % (2 ^ (depth + 1)) = residue + 2 ^ depth) :
+    x % (2 ^ depth) = residue := by
+  have hdvd : 2 ^ depth ∣ 2 ^ (depth + 1) := by
+    exact ⟨2, by rw [pow_succ, Nat.mul_comm]⟩
+  cases h with
+  | inl hleft =>
+      calc
+        x % (2 ^ depth)
+            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
+                rw [Nat.mod_mod_of_dvd _ hdvd]
+        _ = residue % (2 ^ depth) := by rw [hleft]
+        _ = residue := Nat.mod_eq_of_lt hres
+  | inr hright =>
+      calc
+        x % (2 ^ depth)
+            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
+                rw [Nat.mod_mod_of_dvd _ hdvd]
+        _ = (residue + 2 ^ depth) % (2 ^ depth) := by rw [hright]
+        _ = residue := by
+          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hres]
+
+/--
+Pointwise `0/1` indicator split for a valid power-of-two residue cell.
+
+The parent cell at depth `depth` is the disjoint union of the left child
+`residue` and the right child `residue + 2^depth` at depth `depth + 1`.
+-/
+theorem pow2ResidueIndicator_refine_succ
+    (x depth residue : ℕ)
+    (hres : residue < 2 ^ depth) :
+    (if x % (2 ^ depth) = residue then 1 else 0) =
+      (if x % (2 ^ (depth + 1)) = residue then 1 else 0) +
+        if x % (2 ^ (depth + 1)) = residue + 2 ^ depth then 1 else 0 := by
+  by_cases hparent : x % (2 ^ depth) = residue
+  · have hsplit :=
+      mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq x depth residue hres hparent
+    cases hsplit with
+    | inl hleft =>
+        simp [hparent, hleft]
+    | inr hright =>
+        simp [hparent, hright]
+  · have hleft_not : x % (2 ^ (depth + 1)) ≠ residue := by
+      intro hleft
+      exact hparent
+        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+          x depth residue hres (Or.inl hleft))
+    have hright_not :
+        x % (2 ^ (depth + 1)) ≠ residue + 2 ^ depth := by
+      intro hright
+      exact hparent
+        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+          x depth residue hres (Or.inr hright))
+    simp [hparent, hleft_not, hright_not]
+
+/--
+Depth refinement for generic source-window residue counts.
+
+Counting a valid parent cell at depth `depth` is the same as counting both of
+its child cells at depth `depth + 1`.
+-/
+theorem orbitWindowResidueCountPow2_refine_succ
+    (n : OddNat) (k depth residue : ℕ)
+    (hres : residue < 2 ^ depth) :
+    orbitWindowResidueCountPow2 n k depth residue =
+      orbitWindowResidueCountPow2 n k (depth + 1) residue +
+        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth) := by
+  induction k with
+  | zero =>
+      simp [orbitWindowResidueCountPow2]
+  | succ k ih =>
+      rw [orbitWindowResidueCountPow2_succ]
+      rw [orbitWindowResidueCountPow2_succ]
+      rw [orbitWindowResidueCountPow2_succ]
+      rw [ih]
+      have hindicator :=
+        pow2ResidueIndicator_refine_succ (oddOrbitLabel n k) depth residue hres
+      omega
+
+/--
+Retention mass splits into the recovery and continuation sibling masses at the
+next depth.
+-/
+theorem orbitWindowRetentionMass_split
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRetentionMassPow2 n k r =
+      orbitWindowRecoverySiblingMassPow2 n k r +
+        orbitWindowContinuationSiblingMassPow2 n k r := by
+  unfold orbitWindowRetentionMassPow2
+  unfold orbitWindowRecoverySiblingMassPow2
+  unfold orbitWindowContinuationSiblingMassPow2
+  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
+  have hsplit :=
+    orbitWindowResidueCountPow2_refine_succ n k r (2 ^ r - 1) hres
+  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
+    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
+    rw [pow_succ]
+    omega
+  simpa [hright] using hsplit
+
+/-- Recovery sibling mass is bounded by the parent retention mass. -/
+theorem orbitWindowRecoverySiblingMassPow2_le_retentionMass
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowRecoverySiblingMassPow2 n k r ≤
+      orbitWindowRetentionMassPow2 n k r := by
+  rw [orbitWindowRetentionMass_split]
+  omega
+
+/-- Continuation sibling mass is bounded by the parent retention mass. -/
+theorem orbitWindowContinuationSiblingMassPow2_le_retentionMass
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowContinuationSiblingMassPow2 n k r ≤
+      orbitWindowRetentionMassPow2 n k r := by
+  rw [orbitWindowRetentionMass_split]
+  omega
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 30ba08f2..d3b92801 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -103,6 +103,8 @@ orbitWindowResidueCountPow2Tail
 sourcePow2Distribution_total
 tailPow2Distribution_total
 pow2ChannelFlow_of_pointwise
+orbitWindowResidueCountPow2_refine_succ
+orbitWindowRetentionMass_split
 ```
 
 The central No.100 layer is:
@@ -134,6 +136,7 @@ docs/Collatz-Overview.md
 docs/Collatz-Package-Structure.md
 docs/Collatz-FiniteChannelFlow-100.md
 docs/Collatz-FiniteRatioRetention-101.md
+docs/Collatz-DepthRefinement-102.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -218,3 +221,27 @@ See:
 ```text
 docs/Collatz-FiniteRatioRetention-101.md
 ```
+
+Checkpoint 102 then turns the named retention channels into a recursive
+two-adic decomposition:
+
+```lean
+mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+pow2ResidueIndicator_refine_succ
+orbitWindowResidueCountPow2_refine_succ
+orbitWindowRetentionMass_split
+orbitWindowRecoverySiblingMassPow2_le_retentionMass
+orbitWindowContinuationSiblingMassPow2_le_retentionMass
+```
+
+The key reading is:
+
+```text
+retention mass at depth r
+  = recovery sibling mass at depth r+1
+    + continuation sibling mass at depth r+1
+```
+
+This is still finite `Nat` counting.  It does not use probability, limits, or
+real-valued density.  It gives the next local tool for saying that a long
+low-peeling path must keep occupying a nested retention cylinder.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md
new file mode 100644
index 00000000..8336a71a
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md
@@ -0,0 +1,181 @@
+# Collatz Depth Refinement 102
+
+Checkpoint 102 closes the first recursive residue-cell split in
+`DkMath.Collatz.PetalBridge`.
+
+The previous checkpoints established:
+
+```text
+100:
+  finite source/tail residue distributions
+  pointwise channel flow -> count inequality
+
+101:
+  division-free ratio predicates
+  named retention/recovery/continuation masses
+```
+
+Checkpoint 102 adds the missing local fact:
+
+```text
+a residue cell modulo 2^r splits into exactly two residue cells modulo 2^(r+1)
+```
+
+This is the finite Petal recursion layer for Collatz residue observations.
+
+## Pointwise Split
+
+The basic pointwise theorem is:
+
+```lean
+mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+```
+
+For a valid residue `residue < 2^depth`, if
+
+```text
+x % 2^depth = residue
+```
+
+then at the next depth:
+
+```text
+x % 2^(depth+1) = residue
+```
+
+or
+
+```text
+x % 2^(depth+1) = residue + 2^depth
+```
+
+The reverse direction is also available:
+
+```lean
+mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+```
+
+Together these identify the parent cell with the two child cells.
+
+## Indicator Split
+
+The pointwise split is converted into a `0/1` indicator equality:
+
+```lean
+pow2ResidueIndicator_refine_succ
+```
+
+This theorem is the small API hinge used to lift pointwise residue logic to
+finite `countP` statements.
+
+## Count Split
+
+The count-level theorem is:
+
+```lean
+orbitWindowResidueCountPow2_refine_succ
+```
+
+It states:
+
+```text
+count(depth, residue)
+  =
+count(depth+1, residue)
+  + count(depth+1, residue + 2^depth)
+```
+
+inside the finite source window.
+
+This is still purely finite `Nat` arithmetic.  It does not use density,
+probability, or limits.
+
+## Retention Split
+
+The retention residue at depth `r` is:
+
+```text
+2^r - 1
+```
+
+The two child residues are:
+
+```text
+recovery:
+  2^r - 1
+
+continuation:
+  2^(r+1) - 1
+```
+
+The specialized theorem is:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+It states:
+
+```text
+orbitWindowRetentionMassPow2 n k r
+  =
+orbitWindowRecoverySiblingMassPow2 n k r
+  + orbitWindowContinuationSiblingMassPow2 n k r
+```
+
+This is the main mathematical result of checkpoint 102.
+
+## Immediate Corollaries
+
+Both child masses are bounded by the parent retention mass:
+
+```lean
+orbitWindowRecoverySiblingMassPow2_le_retentionMass
+orbitWindowContinuationSiblingMassPow2_le_retentionMass
+```
+
+The shifted-tail sibling masses also have window bounds:
+
+```lean
+orbitWindowRecoverySiblingMassPow2Tail_le_window
+orbitWindowContinuationSiblingMassPow2Tail_le_window
+```
+
+## Interpretation
+
+The recovery and continuation channels are not independent masses.
+
+They are the two child cells of the same parent retention cylinder:
+
+```text
+retention_r
+  = recovery_r + continuation_r
+```
+
+This is important for later low-peeling arguments.  If a long Collatz segment
+keeps avoiding large 2-adic peeling, then its mass must remain inside nested
+retention cylinders.  Checkpoint 102 provides the exact finite split needed to
+measure that nesting.
+
+## Next Candidate
+
+The next useful layer is a finite contraction or obstruction statement, still
+without real-valued frequencies.
+
+Candidate shapes:
+
+```lean
+AtMostHalf (orbitWindowContinuationSiblingMassPow2 n k r)
+  (orbitWindowRetentionMassPow2 n k r)
+```
+
+or a weaker theorem saying that large continuation mass forces a large
+shifted-tail retention mass through the existing channel-flow lemmas.
+
+The key strategic point is that such a theorem should now use:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+instead of unfolding raw residue counts.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 723f3aa4..47c6bb71 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -218,6 +218,55 @@ The helper returns:
 source cell count <= target tail cell count
 ```
 
+## Depth Refinement
+
+Checkpoint 102 adds the recursive residue-cell split.
+
+The pointwise theorem is:
+
+```lean
+mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+```
+
+It says that a valid residue cell at depth `depth` has exactly two children at
+depth `depth + 1`:
+
+```text
+residue
+residue + 2^depth
+```
+
+The count-level theorem is:
+
+```lean
+orbitWindowResidueCountPow2_refine_succ
+```
+
+It upgrades the pointwise split to finite window occupation counts:
+
+```text
+count(parent cell)
+  = count(left child) + count(right child)
+```
+
+The retention-channel specialization is:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+This reads:
+
+```text
+retention mass at depth r
+  = recovery sibling mass at depth r+1
+    + continuation sibling mass at depth r+1
+```
+
+Use this theorem when an argument needs to show that recovery and continuation
+are not independent extra mass.  They are the two subcells of the previous
+retention cylinder.
+
 This is the theorem to reach for before writing a custom induction over `k`.
 
 ## Recursive Petal Residues
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 10d1985c..2b9a3743 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -191,6 +191,16 @@ orbitWindowRetentionMassPow2_le_window
 orbitWindowRetentionMassPow2Tail_le_window
 orbitWindowRecoverySiblingMassPow2_le_window
 orbitWindowContinuationSiblingMassPow2_le_window
+orbitWindowRecoverySiblingMassPow2Tail_le_window
+orbitWindowContinuationSiblingMassPow2Tail_le_window
+twoAdicRetentionResidue_lt_pow
+mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+pow2ResidueIndicator_refine_succ
+orbitWindowResidueCountPow2_refine_succ
+orbitWindowRetentionMass_split
+orbitWindowRecoverySiblingMassPow2_le_retentionMass
+orbitWindowContinuationSiblingMassPow2_le_retentionMass
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-102.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-102.md
new file mode 100644
index 00000000..17d5ec0b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-102.md
@@ -0,0 +1,139 @@
+# Report Petal 102
+
+## Summary
+
+Checkpoint 102 implemented the depth-refinement split for power-of-two residue
+cells in `DkMath.Collatz.PetalBridge`.
+
+The main result is now verified:
+
+```lean
+orbitWindowRetentionMass_split
+```
+
+which states that retention mass at depth `r` is exactly the sum of the
+recovery and continuation sibling masses at depth `r + 1`.
+
+## Implemented Lean Surface
+
+New window bounds:
+
+```lean
+orbitWindowRecoverySiblingMassPow2Tail_le_window
+orbitWindowContinuationSiblingMassPow2Tail_le_window
+```
+
+Residue validity:
+
+```lean
+twoAdicRetentionResidue_lt_pow
+```
+
+Pointwise refinement:
+
+```lean
+mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
+mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
+```
+
+Indicator and count refinement:
+
+```lean
+pow2ResidueIndicator_refine_succ
+orbitWindowResidueCountPow2_refine_succ
+```
+
+Retention split and child bounds:
+
+```lean
+orbitWindowRetentionMass_split
+orbitWindowRecoverySiblingMassPow2_le_retentionMass
+orbitWindowContinuationSiblingMassPow2_le_retentionMass
+```
+
+## Mathematical Reading
+
+For a valid cell modulo `2^depth`, the next modulus `2^(depth+1)` has exactly
+two child cells:
+
+```text
+residue
+residue + 2^depth
+```
+
+The finite source-window count of the parent cell is therefore the sum of the
+two child counts.
+
+Specialized to the retention residue `2^r - 1`, this becomes:
+
+```text
+retention_r = recovery_r + continuation_r
+```
+
+This closes the first recursive Petal decomposition for Collatz residue mass.
+
+## Docs Updated
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-DepthRefinement-102.md
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
+No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.
+
+Known upstream warning remains unchanged:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Inference
+
+The next useful theorem should use `orbitWindowRetentionMass_split` as the
+starting point, not raw residue-count unfolding.
+
+Two natural directions:
+
+```text
+1. contraction / ratio:
+   show continuation is at most half of retention under a suitable condition
+
+2. forcing / flow:
+   large continuation mass forces large shifted-tail retention mass through
+   the existing channel-flow theorems
+```
+
+The second direction is probably easier because the file already contains
+channel-flow inequalities such as:
+
+```lean
+orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
+orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
+```
+
+Suggested next checkpoint:
+
+```lean
+theorem orbitWindowContinuationMass_forces_tailRetention
+```
+
+with the exact statement chosen by matching existing mass names rather than
+creating another raw residue-count theorem.
````
`````
