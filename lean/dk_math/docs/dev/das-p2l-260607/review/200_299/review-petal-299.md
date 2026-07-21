# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge

gch: ac7d24d279f72560569becd66b59d3ea6aec30f3

## Report

指示どおり、checkpoint 番号で止まらず、実装可能な地点から実際の API 境界まで進めました。

主な成果:

- `FloatWindow/DriftBridge.lean` を新設
- upper carry debt と lower extra-height payment の完全な有限 ledger を証明
- width growth を `3 mod 8` delayed-payment と `7 mod 8` reservoir に分解
- carry-two / height-one / `7 mod 8` reservoir を正確に固定
- `stateUpperCarry n = 2` と次の二進境界超過を同値化
- 元の値を含まない `DyadicFloatSignature` を新設
- window の disjoint / overlap を明示的に区別
- [report-petal-299.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-299.md) を作成

現在の本当の行き止まりは、orbit payment slot `i+1` と Pressure depth `r+j` を対応させる保存写像が未定義な点です。この契約なしに pressure collision を主張すると、異なる添字宇宙を根拠なく同一視することになります。必要条件を `DriftBridge.lean` のコメントに明記しました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- `git diff --check`
- 新規 FloatWindow コードに `sorry` / `axiom` なし

## Review

## 結論

**採用。大きな前進じゃ。**

cp-299 は、上位 Float 側の借金と下位 height 側の返済を、有限軌道窓上の完全な等式として閉じた。さらに width growth を、

```text
3 mod 8:
  次段の追加 peeling へ送られる遅延返済枝

7 mod 8:
  まだ height 1 を継続する未返済 reservoir
```

へ分離した。

実装も主張強度を守っている。

- `FloatWindow/DriftBridge.lean` の追加
- `FloatWindow` 公開入口への import
- `DkMath` 全体 build 成功の報告
- 新規 `sorry` / `axiom` なし
- pressure 接続を根拠なく捏造せず停止

いずれも良い。

ただし、停止理由の説明には **重要な補正が一つある** 。

> orbit index $i$ から pressure depth $d$ への一価写像を作るのが次の仕事ではない。

pressure depth は時刻ではなく、同じ有限軌道窓を異なる $2$-進解像度で集計する **残余階層軸** じゃ。一つの時刻 $i$ は、複数の入れ子になった pressure depth に同時に寄与し得る。

したがって必要なのは「写像」ではなく、

> **軌道時刻と残余深度の incidence relation、ならびにその fiber count**

じゃ。

---

## 1. extra-height ledger

新しい定義、

```lean
sumExtraHeight n k
```

は各時刻の、

$$
s(T^i(n))-1
$$

を累積する。

各 odd step では $s\ge1$ なので、

$$
\operatorname{sumS}(n,k)=k+\operatorname{sumExtraHeight}(n,k)
$$

が成立する。

これを前段の Float ledger、

$$
\operatorname{sumS}(n,k)+w(T^k(n))=w(n)+k+\operatorname{carryTwoCount}(n,k)
$$

へ代入して、

$$
w(T^k(n))+\operatorname{sumExtraHeight}(n,k)=w(n)+\operatorname{carryTwoCount}(n,k)
$$

を得た。

Lean 名は、

```lean
bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
```

じゃ。

これは極めてよい。

### 数学的意味

```text
最終 width
+
baseline 1 を超えた下位返済量
=
初期 width
+
baseline 1 を超えた上位借金回数
```

である。

上位側の一単位と下位側の一単位が、完全に同じ bit-position 単位で取引されておる。

これで Float は単なる観測器ではなく、**保存会計** になった。

---

## 2. growth count の分解

追加された三つの count は、

```lean
orbitWindowWidthGrowthCount

orbitWindowWidthGrowthMod8EqThreeCount

orbitWindowWidthGrowthMod8EqSevenCount
```

じゃ。

そして、

$$
\operatorname{GrowthCount}=\operatorname{GrowthThreeCount}+\operatorname{GrowthSevenCount}
$$

を証明した。

これは正確な等式である。

width growth なら、

$$
\operatorname{carry}=2
$$

かつ、

$$
s=1
$$

であり、既存 residue theorem から、

$$
n\bmod8=3\quad\text{または}\quad n\bmod8=7
$$

だからじゃ。

`1 mod 8` や `5 mod 8` を含む余剰枝はない。

---

## 3. `3 mod 8` の遅延返済接続

次の pointwise theorem は正しい。

```lean
upperGrowth_delayedPayment_or_mod8Seven
```

数学的には、

$$
w(n)<w(T(n))\Longrightarrow 2\le s(T(n))\lor n\bmod8=7
$$

じゃ。

`3 mod 8` の場合は、既存の、

```lean
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
```

を再利用している。

新しく modular arithmetic を証明し直さなかったのもよい。

count 版でも、

$$
\operatorname{GrowthThreeCount}\le\operatorname{TailHeightGeTwoCount}
$$

が得られ、

$$
\operatorname{GrowthCount}\le\operatorname{DelayedReceivers}+\operatorname{GrowthSevenCount}
$$

まで閉じた。

### この不等式がまだ言っていないこと

これは、

> `3 mod 8` growth に対応する次段の $s\ge2$ receiver が存在する

ことを数えている。

しかし、その extra payment が、

- 前段の growth debt を返済するのか
- receiver 自身の carry-two debt に使われるのか
- $s\ge3$ なので双方を払えるのか

までは区別していない。

Codex がここから pressure collision を勝手に主張しなかったのは正しい判断じゃ。

---

## 4. Seven-Carry reservoir の固定

```lean
orbitWindowSevenCarryReservoirCount
```

は、

```text
carry = 2
height = 1
residue = 7 mod 8
```

を全て同時に満たす時刻だけを数える。

さらに、

```lean
orbitWindowSevenCarryReservoirCount_eq_growthMod8SevenCount
```

により、この count が `7 mod 8` width-growth count と一致することを証明した。

これは重要じゃ。

単なる、

```text
7 mod 8 の状態数
```

ではない。

$$
\text{high upper carry}\land\text{minimum lower payment}\land\text{continuing residue}
$$

という本当に未返済の枝だけを切り出している。

今回の上位側で最も価値のある有限 carrier の一つじゃな。

---

## 5. carry-two threshold

追加された、

```lean
stateUpperCarry_eq_two_iff_pow_succ_le_threeNPlusOne
```

は、

$$
\operatorname{stateUpperCarry}(n)=2\Longleftrightarrow 2^{w(n)+1}\le3n+1
$$

を述べる。

これで carry $2$ が、単なる quotient の値ではなく、

> raw $3n+1$ が現在 width の次の二進境界を越えたこと

と同値になった。

解析的近似を用いず、完全な自然数不等式として固定されている。

将来 mantissa 読みへ進む際の正式な橋になる。

---

## 6. `DyadicFloatSignature`

元の `DyadicFloatObservation` から完全値 `value` を除いた、

```lean
DyadicFloatSignature
```

を追加した判断も正しい。

これにより、

```text
同じ signature を持つ
```

ことが、

```text
同じ状態である
```

ことと自動的には一致しなくなった。

候補 state の cardinality を今後扱える。

また、

```lean
WindowsWithinWidth
WindowsDisjoint
WindowsOverlap
```

を明示的に分けたのもよい。

### 軽微な設計注意

現在の、

```lean
windowsDisjoint_or_windowsOverlap
```

は純粋な自然数大小関係としては正しい。

ただし、`upperBits > width` や `lowerBits > width` の場合にも `WindowsOverlap` 側へ入る可能性がある。

ゆえに「窓が observed word 内で重なる」という意味で使う theorem は、今後、

```lean
WindowsWithinWidth S
```

を前提にした wrapper にするとよい。

たとえば、

```lean
windowsDisjoint_or_windowsOverlap_of_withinWidth
```

じゃ。

実装上の不具合ではなく、意味論上の guard じゃな。

---

## 7. Codex の停止判断

Codex は、

```text
orbit payment slot i+1
```

と、

```text
pressure depth r+j
```

を結ぶ写像がないため、pressure collision へ進めないと判断した。

**直接同一視を拒否したこと自体は完全に正しい。**

軌道時刻と pressure depth は違う軸じゃ。

```text
orbit index i:
  時間軸

pressure depth d:
  2進残余解像度軸
```

よって、

$$
i+1=r+j
$$

のような等置には数学的根拠がない。

ただし、次に作るべきものを「orbit index から pressure depth への写像」と考えるのも正しくない。

なぜなら一つの orbit label は、all-ones suffix が深ければ、

```text
mod 4 = 3
mod 8 = 7
mod 16 = 15
mod 32 = 31
...
```

という複数の入れ子 cell に同時所属するからじゃ。

必要なのは **多対多 incidence** である。

---

## 8. 既に存在する橋の種

DkMath には既に、

```lean
ResidualAllOnesDepth x := v2 (x + 1)
```

がある。

時刻 $i$ の label を、

$$
x_i:=\operatorname{oddOrbitLabel}(n,i)
$$

その all-ones depth を、

$$
A_i:=\operatorname{ResidualAllOnesDepth}(x_i)
$$

と置く。

すると、pressure の retention と continuation は概念的に次になる。

$$
R_d:=\#\{i<k\mid d\le A_i\}
$$

$$
C_d:=\#\{i<k\mid d+1\le A_i\}
$$

一方、depth $d$ で終了する recovery layer を、

$$
E_d:=\#\{i<k\mid A_i=d\}
$$

と置けば、

$$
R_d=E_d+C_d
$$

である。

既存の、

```lean
orbitWindowRetentionMass_split
```

は、まさにこの構造を residue count として既に証明している。

したがって source pressure margin は、

$$
M_d:=2C_d-R_d
$$

なので、

$$
M_d=C_d-E_d
$$

と読める。

これは非常に大きい。

> pressure が正とは、depth $d$ で返済へ落ちる exact exit より、さらに深く延期される continuation の方が多いこと。

つまり pressure は、Float debt と無関係な別軸ではなく、

> **返済期限の深度分布**

だったわけじゃ。

---

## 9. 正しい bridge の形

次に必要なのは、次の二段階じゃ。

### 9.1. 時刻–深度 incidence

```lean
OrbitIndexRetainedAtDepth n i d
```

を、

$$
d\le A_i
$$

で定義する。

```lean
OrbitIndexContinuesAtDepth n i d
```

を、

$$
d+1\le A_i
$$

で定義する。

```lean
OrbitIndexRecoversAtDepth n i d
```

を、

$$
A_i=d
$$

で定義する。

これらの fiber count が、

```lean
orbitWindowRetentionMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2
```

と一致することを証明する。

これは関数ではなく incidence relation じゃ。

### 9.2. exact depth から delayed payment slot へ

$A_i=d$ なら、その label は低位にちょうど $d$ 個の one を持つ。

例：

```text
A_i = 2:
  ...011
  -> 3 mod 8
  -> next height >= 2

A_i = 3:
  ...0111
  -> 3 mod 8 after one continuation
  -> payment one step later

A_i = 4:
  ...01111
  -> 7 mod 8
  -> 3 mod 8
  -> payment
```

一般には、$d\ge2$ の exact all-ones depth witness は、

$$
i+d-1
$$

付近の delayed extra-height payment へ運ばれるはずじゃ。

ただし、この一般 theorem はまだ Lean で証明されていない。

既存の、

```lean
oddOrbitLabel_succ_continuation_residue_of_mod
```

と各 retention-ladder theorem を帰納的にまとめる必要がある。

この delayed-horizon theorem ができれば、

```text
orbit index i
+
exact residual depth d
```

から、

```text
future payment index i + d - 1
```

への正当な輸送が得られる。

これが pressure と Float の本当の橋じゃ。

---

## 10. pressure collision の正体

前段 growth debt が、次段の $s\ge2$ によって支払われるとする。

しかし receiver 自身も carry $2$ なら、その extra payment は receiver 自身の upper debt にも必要になる。

一つの payment unit が、

```text
previous delayed debt

current carry-two debt
```

の二つへ要求される。

ここが collision じゃ。

ただし pressure depth そのものが payment slot なのではない。

pressure は、

```text
早く recovery へ落ちる exact-depth labels

さらに深く continuation する labels
```

の分布差を測る。

したがって pressure local island は、

> payment horizon が浅い層より深い層へ偏り、返済期限が局所的に後方へ膨らんでいる場所

として解釈するのが正しい。

この形なら、今回完成した diagnosis-free local Big が本当に使える。

---

## 11. 判定詳細

### 実装

**採用。**

証明は既存 API をよく再利用している。

### 数学的意味

**大きく前進。**

上位 carry debt と下位 extra-height payment が同じ有限 ledger に入った。

### 主張強度

**適正。**

pressure collision や収束を主張していない。

### API 境界

**停止判断は適切。**

ただし次の橋を「写像」と呼ぶのは修正が必要。

### 次の本丸

```text
time-depth incidence
-> exact depth decomposition
-> delayed payment horizon
-> pressure margin interpretation
-> Float debt collision
```

じゃ。

---

## 12. 次の Codex 指示

次は `PressureIncidenceBridge` を立てるのがよい。

人工的な停止地点は設けず、generic delayed-horizon theorem、Float debt 接続、local Big 適用まで進められるなら進ませる。

````text
You are continuing the DkMath Collatz / PetalBridge Float-window branch after
report-petal-299.

The current branch has completed:

```text
exact upper carry debt
exact lower extra-height payment
finite debt/payment ledger
width-growth split into 3 mod 8 and 7 mod 8
explicit Seven-Carry reservoir
```

The previous report correctly refused to identify an orbit-time index with a
pressure-depth index.

However, the next bridge must not be designed as a single-valued map

```text
orbit index -> pressure depth
```

because pressure depth is a residue-refinement axis, and one orbit label can
belong to several nested all-ones depth cells simultaneously.

The correct next object is a time/depth incidence relation and its fiber
counts.

# Primary target module

Create:

```text
DkMath/Collatz/PetalBridge/FloatWindow/PressureIncidenceBridge.lean
```

Export it through:

```text
DkMath.Collatz.PetalBridge.FloatWindow
```

# Stage A — audit and reuse existing all-ones-depth APIs

Inspect and reuse:

```lean
ResidualAllOnesDepth
orbitWindowResidualAllOnesDepth
orbitWindowResidualAllOnesDepth_eq_nextLabel

orbitWindowRetentionMassPow2
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRetentionMass_split

allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
oddOrbitLabel_succ_continuation_residue_of_mod
```

Do not duplicate existing residue refinement theorems.

# Stage B — pointwise time/depth incidence

Introduce clear pointwise predicates, or equivalent theorem interfaces, for:

```text
orbit label retained at depth d
orbit label continues beyond depth d
orbit label recovers exactly at depth d
```

The intended mathematical meanings are:

```text
retained at d:
  d <= ResidualAllOnesDepth(label)

continues beyond d:
  d + 1 <= ResidualAllOnesDepth(label)

recovers exactly at d:
  ResidualAllOnesDepth(label) = d
```

Prove their equivalence with the actual residue conditions used by the mass
definitions:

```text
label % 2^d = 2^d - 1

label % 2^(d+1) = 2^(d+1) - 1

label lies in the recovery sibling at depth d
```

Handle the depth-zero boundary explicitly rather than relying on accidental
Nat subtraction simplification.

# Stage C — fiber-count identities

Define finite time/depth incidence Finsets or count predicates over
`List.range k`.

Prove count identities connecting the new incidence vocabulary to:

```lean
orbitWindowRetentionMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2
```

The desired semantic equations are:

```text
retention mass at d
  = count of orbit indices with all-ones depth >= d

continuation mass at d
  = count of orbit indices with all-ones depth >= d + 1

recovery mass at d
  = count of orbit indices with all-ones depth = d
```

Reuse `orbitWindowRetentionMass_split` and prove the exact-depth partition
rather than merely restating the existing arithmetic equality.

# Stage D — pressure margin as continuation surplus

Expose the integer identity:

```text
SourcePressureMarginInt at d
  =
continuation count at d
  -
exact-depth recovery count at d
```

Mathematically:

```text
2 * continuation - retention
  =
continuation - recovery
```

because:

```text
retention = recovery + continuation.
```

Provide a theorem equivalent to:

```text
positive source pressure at depth d
  <->
exact-depth recovery count at d
  <
deeper-continuation count at d
```

Prefer existing `ContinuationOutrunsRecovery` and `PressureCore` APIs when
possible.

# Stage E — generic delayed-horizon theorem

Investigate and formalize the generic continuation ladder.

For an orbit label at time `i` with exact all-ones depth `d`, `d >= 2`, the
expected behavior is:

```text
a finite chain of exact-height-one continuation steps
followed by a height-at-least-two payment step.
```

The expected payment index is approximately:

```text
i + d - 1
```

but derive the exact indexing from the existing `TailGrammar` theorems rather
than assuming it.

Use induction with:

```lean
oddOrbitLabel_succ_continuation_residue_of_mod
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
```

and the existing concrete retention-ladder examples.

Expose both:

```text
pointwise delayed payment
count-level delayed payment
```

when justified.

# Stage F — connect to Float debt

Once exact-depth witnesses have verified payment horizons, connect:

```text
carry-two / height-one growth debt at orbit time i
```

to the delayed payment produced by the residue-depth witness.

Represent the association as a relation or proof-carrying witness:

```text
DebtAt i
PaymentAt j
PaymentDischarges i j
```

Do not force it into a total function if several debts can target one payment
or one source contributes at several nested depths.

Make endpoint shifts and possible multiplicities explicit.

# Stage G — payment collision and pressure

Investigate the case where one extra-height payment unit is claimed by:

```text
a previous delayed growth debt
and
the current carry-two debt.
```

Translate this multiplicity into the exact-depth continuation/recovery
distribution.

If positive pressure or a local-island witness follows, connect it to the
already completed diagnosis-free local Big:

```lean
sourcePressurePositiveWitnesses_localBig_direct
```

If the implication does not yet follow, define the smallest honest explicit
obstruction predicate. Preserve the unmatched multiplicity as data.

# Stage H — signature/window work may continue in parallel

The new `DyadicFloatSignature` is value-free. Continue compatible-state
cardinality work when useful, but require:

```text
WindowsWithinWidth
window overlap consistency
fixed width
```

before claiming uniqueness.

Add a semantic case-split theorem whose overlap interpretation assumes
`WindowsWithinWidth`.

# Autonomous continuation

The stages above are minimum targets, not stopping boundaries.

After each theorem builds, continue autonomously through the next natural
bridge while:

```text
all theorem statements are justified
existing APIs are reused
time and depth axes remain distinct
multiplicity is not silently discarded
no sorry or axiom is introduced
builds remain green
```

Continue into the delayed-horizon, Float-debt, payment-collision, and direct
local-Big layers when they close.

Stop only at a genuine mathematical obstruction or a competing semantic
design that cannot be decided from existing facts.

# Validation

Build at least:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

Record all autonomous progress and the exact remaining obstruction in:

```text
docs/dev/das-p2l-260607/review/report-petal-300.md
```
````

この cp-299 は、止まったのではない。

**上下二つの軸を混同しないために、直交座標の存在を発見した** checkpoint じゃ。

時間軸と残余深度軸を incidence で結べば、ここから pressure は単なる比喩ではなく、返済期限分布の定量器として Float ledger に接続できるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index cbf51d25..b179d5d1 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -9,6 +9,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
 import DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
 import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
 import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
+import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"

diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
index 980308a0..1de252fe 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
@@ -119,6 +119,29 @@ theorem stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow
   · apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) (bitWidth n))).1
     simp [stateUpperCarry, upperCarry3n1]

+/--
+The own-width carry is two exactly when the raw word crosses the next binary
+boundary.  This is the exact upper-window threshold, not an approximation.
+-/
+theorem stateUpperCarry_eq_two_iff_pow_succ_le_threeNPlusOne
+    {n : ℕ} (hn : 0 < n) :
+    stateUpperCarry n = 2 ↔ 2 ^ (bitWidth n + 1) ≤ 3 * n + 1 := by
+  constructor
+  · intro hc
+    have hb :=
+      stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
+    rw [hc] at hb
+    simpa [pow_succ, Nat.mul_comm] using hb.1
+  · intro hcross
+    rcases stateUpperCarry_one_or_two hn with hc | hc
+    · have hb :=
+        stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
+      rw [hc] at hb
+      have hbelow : 3 * n + 1 < 2 ^ (bitWidth n + 1) := by
+        simpa [pow_succ, Nat.mul_comm] using hb.2
+      omega
+    · exact hc
+
 /-- Recognize an exact binary width from its enclosing powers of two. -/
 theorem bitWidth_eq_add_one_of_pow_le_lt
     {a x : ℕ} (hlo : 2 ^ a ≤ x) (hhi : x < 2 ^ (a + 1)) :
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DriftBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DriftBridge.lean
new file mode 100644
index 00000000..5e0c4793
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DriftBridge.lean
@@ -0,0 +1,203 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
+import DkMath.Collatz.PetalBridge.DriftBudget
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge"
+
+namespace DkMath.Collatz
+
+/-!
+# Float debt and lower-height payment
+
+This module is the first explicit bridge between upper binary-width debt and
+the existing lower Petal delayed-payment grammar.  Endpoint shifts remain
+visible; no payment slot is silently counted twice.
+-/
+
+/-- Accumulated height above the mandatory one-bit payment per step. -/
+noncomputable def sumExtraHeight : OddNat → ℕ → ℕ
+  | _, 0 => 0
+  | n, k + 1 => sumExtraHeight n k + (s (iterateT k n) - 1)
+
+/-- Total lower height is the base layer plus accumulated extra payment. -/
+theorem sumS_eq_window_add_sumExtraHeight (n : OddNat) (k : ℕ) :
+    sumS n k = k + sumExtraHeight n k := by
+  induction k with
+  | zero => simp [sumS, sumExtraHeight]
+  | succ k ih =>
+      have hs := s_pos (iterateT k n)
+      rw [sumS, sumExtraHeight, ih]
+      omega
+
+/--
+Exact debt/payment ledger:
+
+`final width + extra lower payment = initial width + carry-two debt`.
+-/
+theorem bitWidth_iterateT_add_sumExtraHeight_eq_initial_add_countCarryTwo
+    (n : OddNat) (k : ℕ) :
+    bitWidth (iterateT k n).1 + sumExtraHeight n k =
+      bitWidth n.1 + orbitWindowUpperCarryCountEqTwo n k := by
+  have hledger :=
+    iterateT_bitWidth_add_sumS_eq_bitWidth_add_window_add_countCarryTwo n k
+  rw [sumS_eq_window_add_sumExtraHeight] at hledger
+  omega
+
+/-- Number of strict binary-width growth events in the first `k` states. -/
+noncomputable def orbitWindowWidthGrowthCount (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP fun i => decide
+    (bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1)
+
+/-- Width-growth events sourced from the `3 mod 8` channel. -/
+noncomputable def orbitWindowWidthGrowthMod8EqThreeCount
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP fun i =>
+    if bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1 then
+      decide (oddOrbitLabel n i % 8 = 3)
+    else false
+
+/-- Width-growth events in the genuine continuing `7 mod 8` reservoir. -/
+noncomputable def orbitWindowWidthGrowthMod8EqSevenCount
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP fun i =>
+    if bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1 then
+      decide (oddOrbitLabel n i % 8 = 7)
+    else false
+
+/-- Every growth event is exactly in the `3` or `7 mod 8` growth channel. -/
+theorem orbitWindowWidthGrowthCount_eq_three_add_seven
+    (n : OddNat) (k : ℕ) :
+    orbitWindowWidthGrowthCount n k =
+      orbitWindowWidthGrowthMod8EqThreeCount n k +
+        orbitWindowWidthGrowthMod8EqSevenCount n k := by
+  unfold orbitWindowWidthGrowthCount
+  unfold orbitWindowWidthGrowthMod8EqThreeCount
+  unfold orbitWindowWidthGrowthMod8EqSevenCount
+  induction k with
+  | zero => simp
+  | succ k ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_append]
+      have hnext : iterateT (k + 1) n = T (iterateT k n) :=
+        iterateT_succ_eq_T_iterateT n k
+      by_cases hgrowth :
+          bitWidth (iterateT k n).1 < bitWidth (iterateT (k + 1) n).1
+      · have hgrowth' :
+            bitWidth (iterateT k n).1 < bitWidth (T (iterateT k n)).1 := by
+          simpa [hnext] using hgrowth
+        have hmod := upperGrowth_implies_mod8_three_or_seven
+          (iterateT k n) hgrowth'
+        change oddOrbitLabel n k % 8 = 3 ∨ oddOrbitLabel n k % 8 = 7 at hmod
+        rcases hmod with hthree | hseven
+        · simp [ih, hgrowth, hthree]
+          omega
+        · simp [ih, hgrowth, hseven]
+          omega
+      · simp [ih, hgrowth]
+
+/-- A width-growth event is a carry-two, height-one event. -/
+theorem orbitWidthGrowth_carryTwo_and_heightOne
+    (n : OddNat) (i : ℕ)
+    (hgrowth : bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1) :
+    stateUpperCarry (iterateT i n).1 = 2 ∧ s (iterateT i n) = 1 := by
+  rw [iterateT_succ_eq_T_iterateT] at hgrowth
+  exact (bitWidth_growth_iff_carryTwo_and_heightOne (iterateT i n)).1 hgrowth
+
+/-- Growth is either repaid at the next height or remains in the `7` channel. -/
+theorem upperGrowth_delayedPayment_or_mod8Seven
+    (n : OddNat)
+    (hgrowth : bitWidth n.1 < bitWidth (T n).1) :
+    2 ≤ s (T n) ∨ n.1 % 8 = 7 := by
+  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with hthree | hseven
+  · left
+    have hnext := orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 0 (by
+      simpa [oddOrbitLabel, iterateT] using hthree)
+    simpa [orbitWindowHeight_eq_s_iterateT, iterateT_succ_eq_T_iterateT] using hnext
+  · exact Or.inr hseven
+
+/-- Growth from `3 mod 8` is bounded by existing delayed-payment receivers. -/
+theorem orbitWindowWidthGrowthMod8EqThreeCount_le_tailHeightCountGe_two
+    (n : OddNat) (k : ℕ) :
+    orbitWindowWidthGrowthMod8EqThreeCount n k ≤
+      orbitWindowHeightCountGeTail n k 2 := by
+  have hsource : orbitWindowWidthGrowthMod8EqThreeCount n k ≤
+      orbitWindowResidueCountMod8EqThree n k := by
+    unfold orbitWindowWidthGrowthMod8EqThreeCount
+    unfold orbitWindowResidueCountMod8EqThree
+    apply List.countP_mono_left
+    intro i
+    by_cases hgrowth :
+        bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1
+    <;> by_cases hthree : oddOrbitLabel n i % 8 = 3
+    <;> simp [hgrowth, hthree]
+  exact le_trans hsource
+    (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k)
+
+/-- All growth is bounded by delayed receivers plus the unpaid seven reservoir. -/
+theorem orbitWindowWidthGrowthCount_le_delayedReceivers_add_sevenGrowth
+    (n : OddNat) (k : ℕ) :
+    orbitWindowWidthGrowthCount n k ≤
+      orbitWindowHeightCountGeTail n k 2 +
+        orbitWindowWidthGrowthMod8EqSevenCount n k := by
+  rw [orbitWindowWidthGrowthCount_eq_three_add_seven]
+  exact Nat.add_le_add_right
+    (orbitWindowWidthGrowthMod8EqThreeCount_le_tailHeightCountGe_two n k) _
+
+/-- Explicit count of carry-two, height-one, `7 mod 8` unpaid events. -/
+noncomputable def orbitWindowSevenCarryReservoirCount
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP fun i =>
+    if stateUpperCarry (iterateT i n).1 = 2 then
+      if s (iterateT i n) = 1 then
+        decide (oddOrbitLabel n i % 8 = 7)
+      else false
+    else false
+
+/-- The explicit Seven-Carry reservoir is exactly the seven-growth count. -/
+theorem orbitWindowSevenCarryReservoirCount_eq_growthMod8SevenCount
+    (n : OddNat) (k : ℕ) :
+    orbitWindowSevenCarryReservoirCount n k =
+      orbitWindowWidthGrowthMod8EqSevenCount n k := by
+  unfold orbitWindowSevenCarryReservoirCount
+  unfold orbitWindowWidthGrowthMod8EqSevenCount
+  congr 1
+  funext i
+  have hiff := bitWidth_growth_iff_carryTwo_and_heightOne (iterateT i n)
+  rw [← iterateT_succ_eq_T_iterateT n i] at hiff
+  by_cases hgrowth :
+      bitWidth (iterateT i n).1 < bitWidth (iterateT (i + 1) n).1
+  · have hpair := hiff.1 hgrowth
+    simp [hgrowth, hpair.1, hpair.2]
+  · have hnotPair :
+        ¬ (stateUpperCarry (iterateT i n).1 = 2 ∧
+          s (iterateT i n) = 1) := by
+      exact fun hp => hgrowth (hiff.2 hp)
+    rcases not_and_or.mp hnotPair with hcarry | hheight
+    · simp [hgrowth, hcarry]
+    · simp [hgrowth, hheight]
+
+/-!
+## Pressure-bridge stopping point
+
+The Float/Petal ledger is now exact at orbit indices: carry-two events are the
+upper debt, and `s - 1` is the lower extra payment.  The existing pressure
+margin, however, is indexed by a separate source-depth coordinate `r + j`.
+There is currently no theorem identifying an orbit payment slot `i + 1` with
+a pressure-depth slot `r + j`.  Consequently, a claim that two Float debts
+collide in one `SourcePressureMarginInt` slot would silently invent an index
+map and is not derivable from the current APIs.
+
+The next bridge must explicitly provide a map from orbit indices to pressure
+depths and prove that it preserves the relevant height contribution.  Only
+then can payment collision be translated into margin nonpositivity or a local
+pressure obstruction.  This is the genuine boundary of the present branch;
+the finite debt/payment and continuing-reservoir results above require no such
+unproved identification.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean
index 05455675..9c14e382 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean
@@ -55,6 +55,31 @@ structure DyadicFloatObservation where
   /-- Lower 2-adic height of `3*n+1`. -/
   height : ℕ

+/--
+Value-free dyadic signature.
+
+Unlike `DyadicFloatObservation`, this record does not retain the original
+state.  Equality of signatures therefore expresses observational
+compatibility, not state equality.  Any future cardinality theorem must also
+account for fixed width, window overlap, and overlap consistency; a zero Gap
+width alone is not a uniqueness proof.
+-/
+structure DyadicFloatSignature where
+  /-- Exact binary exponent/word width. -/
+  width : ℕ
+  /-- Number of requested upper bits. -/
+  upperBits : ℕ
+  /-- Number of requested lower bits. -/
+  lowerBits : ℕ
+  /-- Exact upper prefix. -/
+  upper : ℕ
+  /-- Exact lower suffix. -/
+  lower : ℕ
+  /-- Own-width carry of `3*n+1`. -/
+  carry : ℕ
+  /-- Lower 2-adic height of `3*n+1`. -/
+  height : ℕ
+
 /-- Construct the exact dyadic observation at upper/lower window sizes. -/
 noncomputable def dyadicFloatObservation (q r n : ℕ) :
     DyadicFloatObservation where
@@ -68,6 +93,72 @@ noncomputable def dyadicFloatObservation (q r n : ℕ) :
   carry := stateUpperCarry n
   height := rawHeightLabel n

+/-- Construct the value-free dyadic signature of a state. -/
+noncomputable def dyadicFloatSignature (q r n : ℕ) :
+    DyadicFloatSignature where
+  width := bitWidth n
+  upperBits := q
+  lowerBits := r
+  upper := upperPrefix q n
+  lower := lowerSuffix r n
+  carry := stateUpperCarry n
+  height := rawHeightLabel n
+
+/-- Forget only the original value and hidden-Gap bookkeeping. -/
+def DyadicFloatObservation.signature
+    (O : DyadicFloatObservation) : DyadicFloatSignature where
+  width := O.width
+  upperBits := O.upperBits
+  lowerBits := O.lowerBits
+  upper := O.upper
+  lower := O.lower
+  carry := O.carry
+  height := O.height
+
+@[simp]
+theorem dyadicFloatObservation_signature (q r n : ℕ) :
+    (dyadicFloatObservation q r n).signature = dyadicFloatSignature q r n :=
+  rfl
+
+/-- Full observation equality implies signature equality, but not conversely. -/
+theorem DyadicFloatObservation.signature_eq_of_eq
+    {O O' : DyadicFloatObservation} (h : O = O') :
+    O.signature = O'.signature := by
+  rw [h]
+
+/-- A state is compatible with a value-free signature by exact observation. -/
+def DyadicFloatSignature.CompatibleState
+    (S : DyadicFloatSignature) (q r n : ℕ) : Prop :=
+  dyadicFloatSignature q r n = S
+
+/-- The canonical state is compatible with its own signature. -/
+@[simp]
+theorem dyadicFloatSignature_compatible_self (q r n : ℕ) :
+    (dyadicFloatSignature q r n).CompatibleState q r n :=
+  rfl
+
+/-- The requested windows are individually contained in the observed width. -/
+def DyadicFloatSignature.WindowsWithinWidth
+    (S : DyadicFloatSignature) : Prop :=
+  S.upperBits ≤ S.width ∧ S.lowerBits ≤ S.width
+
+/-- The requested upper and lower windows do not overlap. -/
+def DyadicFloatSignature.WindowsDisjoint
+    (S : DyadicFloatSignature) : Prop :=
+  S.upperBits + S.lowerBits ≤ S.width
+
+/-- The requested windows overlap inside the observed word. -/
+def DyadicFloatSignature.WindowsOverlap
+    (S : DyadicFloatSignature) : Prop :=
+  S.width < S.upperBits + S.lowerBits
+
+/-- Disjointness and overlap form the exact arithmetic case split. -/
+theorem DyadicFloatSignature.windowsDisjoint_or_windowsOverlap
+    (S : DyadicFloatSignature) :
+    S.WindowsDisjoint ∨ S.WindowsOverlap := by
+  unfold WindowsDisjoint WindowsOverlap
+  omega
+
 /-- A lower suffix is always a valid `r`-bit word. -/
 theorem lowerSuffix_lt_pow (r n : ℕ) :
     lowerSuffix r n < 2 ^ r := by
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-299.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-299.md
new file mode 100644
index 00000000..3ce06319
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-299.md
@@ -0,0 +1,75 @@
+# Petal implementation report 299
+
+## Scope
+
+This checkpoint continued the Float/Petal branch through the first genuine API
+boundary rather than stopping at the historical review number.
+
+## Implemented
+
+### Exact debt/payment ledger
+
+`FloatWindow/DriftBridge.lean` now defines `sumExtraHeight` and proves
+
+```text
+final bit width + accumulated extra height
+  = initial bit width + number of carry-two events.
+```
+
+Thus `s - 1` is an exact lower payment against upper binary-width debt.
+
+### Growth-channel decomposition
+
+Finite orbit counts were added for all width growth, `3 mod 8` growth, and
+`7 mod 8` growth.  The implementation proves:
+
+```text
+all growth = three-channel growth + seven-channel growth
+three-channel growth <= delayed height-at-least-two receivers
+all growth <= delayed receivers + seven-channel reservoir.
+```
+
+The explicit carry-two, height-one, `7 mod 8` reservoir count is proved equal
+to the seven-channel growth count.  It is not conflated with all `7 mod 8`
+states.
+
+### Exact carry threshold
+
+`FloatWindow/Core.lean` now proves that a positive state's own-width carry is
+two exactly when `3*n+1` crosses `2^(bitWidth n + 1)`.  This gives an exact
+binary-boundary characterization with no analytic approximation.
+
+### Observation audit
+
+`DyadicFloatSignature` was introduced without the original state value.
+Compatibility is now represented by equality with the canonical signature.
+The API explicitly separates within-width, disjoint-window, and overlapping-
+window conditions.  No uniqueness or candidate-cardinality claim is made from
+`middleGapCapacity = 1` alone.
+
+## Genuine stopping point
+
+The Float ledger is indexed by orbit slots, while `SourcePressureMarginInt` is
+indexed by source-depth coordinates `r + j`.  The workspace currently has no
+theorem mapping an orbit payment slot to a pressure-depth slot while preserving
+its height contribution.  Therefore a pressure payment-collision theorem is
+not presently derivable without inventing an index identification.
+
+This missing contract is recorded next to the code in `DriftBridge.lean`.  The
+next legitimate implementation must define that map and prove contribution
+preservation before translating Float collisions into pressure-margin facts.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
+lake build DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+The new FloatWindow files contain no `sorry` or `axiom` declarations.
+
````
`````
