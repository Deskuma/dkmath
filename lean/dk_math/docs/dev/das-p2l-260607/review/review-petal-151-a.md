# Git diff / Report / Review

## Upd: research: DkMath.Collatz.PetalBridge.OneCycle

gch: fe89197f4b0a4114a51fe459bac40e0dc66cdbaa

## Report

割り込み調査を `DkMath.Collatz.PetalBridge.OneCycle` に反映しました。

やったことは主に 2 つです。

1. `OneCycle.lean` 冒頭コメントに、`DkMath.ABC.ValuationFlowBridge` との研究メモを追加  
   直接 import せず、まず Collatz 側を `unit boundary` として固定する方針を書いてあります。理由は、ABC 側の主語が `a^d - b^d` の primitive flow で、OneCycle 側は `3*n + 1 = 2^h*n` なので、いきなり混ぜると主語がずれるためです。

2. 実装可能な事実を追加  
   追加した theorem は以下です。

```lean
theorem collatz_scaled_one_cycle_int_unit_product
theorem collatz_scaled_one_cycle_nat_unit_product
theorem collatz_scaled_one_cycle_is_unit_boundary
theorem collatz_scaled_one_cycle_no_prime_channel_on_base
theorem collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
theorem collatz_scaled_one_cycle_no_prime_channel_on_unit_product
```

意味としては、

```text
3*n + 1 = 2^h*n
=> ((2^h)-3) * n = 1
=> base n にも scale gap 2^h-3 にも prime channel は残らない
```

という形です。これは ValuationFlowBridge 的に読むと「閉じるなら unit。unit で閉じたなら support channel は残らない」という局所事実になります。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.OneCycle
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
git diff --check
```

`OneCycle.lean` に `sorry` はありません。既存の `ZsigmondyCyclotomicResearch.lean` の warning は今回範囲外です。

## Review

## 結論

うむ、これは **採用** じゃ 👍️
割り込み調査として、かなり良い実装になっておる。

今回の実装は、前回の `OneCycle` 唯一性をさらに一段読み替えて、

```text id="ohgzjr"
closed one-step loop
  -> unit product
  -> no prime channel remains
```

という **ValuationFlowBridge 的な実体** へ落としている。報告にも、`ABC.ValuationFlowBridge` を直接 import せず、まず Collatz 側で `unit boundary` として固定する方針が明記されておる。これは正しい。ABC 側の主語は `a^d - b^d` の primitive flow、OneCycle 側の主語は `3*n + 1 = 2^h*n` なので、いきなり混ぜると主語がずれるからじゃ。

## 実装内容の解説

今回追加された主な theorem はこれじゃ。

```lean id="5fq2lk"
collatz_scaled_one_cycle_int_unit_product
collatz_scaled_one_cycle_nat_unit_product
collatz_scaled_one_cycle_is_unit_boundary
collatz_scaled_one_cycle_no_prime_channel_on_base
collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
collatz_scaled_one_cycle_no_prime_channel_on_unit_product
```

中心はこの変形じゃな。

$$
3n+1=2^h n
$$

を移項して、

$$
(2^h-3)n=1
$$

と読む。

つまり、同じ odd state へ戻る一段巡回が閉じるなら、base \(n\) と scale gap \(2^h-3\) の積は unit \(1\) に潰れる。

これが今回の実体調査の芯じゃ。

## 良い点

## 1. `Int` 版と `Nat` 版を分けたのが良い

`collatz_scaled_one_cycle_int_unit_product` は、整数上で

```lean id="98okmn"
(((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1
```

を示している。これは Nat 減算の丸めを避けた、本当に代数的な unit-product 形じゃ。

一方、`collatz_scaled_one_cycle_nat_unit_product` は、すでに証明済みの唯一性

```lean id="vr8yzj"
n = 1 ∧ h = 2
```

を使って、

```lean id="714ncw"
n * (2 ^ h - 3) = 1
```

へ落としている。これは Lean 的に安全な判断じゃ。Nat subtraction を直接がんばらず、唯一解に潰してから `norm_num` で閉じる。良い実装じゃ。

## 2. “no prime channel” の三段が良い

今回の三つ、

```lean id="ish3eh"
collatz_scaled_one_cycle_no_prime_channel_on_base
collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
collatz_scaled_one_cycle_no_prime_channel_on_unit_product
```

は、かなり使いやすい。

それぞれ意味はこうじゃ。

```text id="whq6wa"
base n に prime channel は残らない
scale gap 2^h - 3 に prime channel は残らない
unit product n * (2^h - 3) に prime channel は残らない
```

つまり、閉じた one-step loop は、support を生成しない。
ABC / valuation-flow 語彙で言えば、

```text id="fxlkg6"
support channel が残るなら閉じていない。
閉じるなら support は unit へ潰れている。
```

という形になる。

## 3. ABC を import しなかったのが正しい

これは大事じゃ。
`OneCycle.lean` はまだ Collatz 側の局所 obstruction ファイルとして保つべきじゃ。

今回のコメントにも、`DkMath.ABC.ValuationFlowBridge` との関係は研究メモとして置き、実際の import はまだしない方針が書かれている。これは良い分離じゃ。

すでに以前の整理でも、最初は `Collatz/PetalBridge/ValuationFlowBridge.lean` あるいは `ABCBridge.lean` を薄く作り、`OneCycle` 側には unit boundary 語彙を足す方がよい、としていた。今回の実装はその方針に沿っておる。

## 注意点

## 1. `no_prime_channel` は閉路仮定つき

今回の no-prime 補題は、あくまで

```lean id="fnfsxl"
hcycle : 3 * n + 1 = 2 ^ h * n
```

を仮定した上での結論じゃ。

つまり、

```text id="r8h60h"
閉じた one-step loop なら prime channel は残らない
```

であって、

```text id="gdmr0f"
Collatz の任意の step で prime channel が残らない
```

ではない。

ここは今後も明記が必要じゃ。

## 2. `Nat` の `2^h - 3` は通常文脈では危険

今回の theorem 内では、唯一性から \(h=2\) に潰しているので問題ない。
ただし一般文脈では、Nat subtraction のため \(h=0,1\) では丸めが起きる。

したがって、今後 bridge 側で一般の scale gap を主語にするなら、

```lean id="rxdrjj"
ScaleGapInt h := ((2 ^ h : ℕ) : ℤ) - 3
```

のような `Int` 版を先に置く方が安全じゃ。

`Nat` 版は「closed loop のもとでは unit に潰れる」という corollary として使うのがよい。

## 3. レポートを残すとよい

今回の `review-petal-151-a.md` は割り込み報告として十分読めるが、リポジトリ側にも

```text id="9o231r"
report-petal-151-a.md
```

または

```text id="4w0xaa"
report-petal-151-interruption.md
```

のような報告を置くとよい。
これは通常 checkpoint ではなく「実体調査」なので、後から見返したときに流れが分かるようにしておきたい。

## 数学的な意味

今回で、`OneCycle` はただの唯一性補題ではなくなった。

以前は、

```text id="zdbr87"
1 -> 4 -> 2 -> 1 の scaled one-cycle は n = 1, h = 2 だけ
```

だった。

今回からは、

```text id="rvym7t"
閉じるなら unit product。
unit product なら prime channel は残らない。
```

になった。

これは、DkMath 的にかなり大事じゃ。

```text id="h5i3bx"
閉じる = unit
閉じない = channel / flow / beam が残る
```

という語彙に一歩近づいたからじゃ。

## 次 checkpoint の方向

次は、`OneCycle.lean` 自体をこれ以上重くせず、薄い bridge ファイルを作るのがよい。

候補はこれじゃ。

```text id="g1i11z"
DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean
```

ここで初めて `DkMath.ABC.ValuationFlowBridge` を import する。ただし、primitive witness を無理に作らず、まずは **unit boundary / no channel / supportMass = 1** の読みを alias と wrapper で固定する。

## 次の Codex 依頼

```text id="brt3wt"
Checkpoint 151-b: Thin Collatz/PetalBridge ValuationFlowBridge for OneCycle unit boundary.

Context:
An interruption implementation extended
DkMath.Collatz.PetalBridge.OneCycle with unit-product and no-prime-channel
facts for the scaled one-step odd cycle equation.

Existing OneCycle facts include:

- collatz_scaled_one_cycle_eq_one
- collatz_scaled_one_cycle_int_unit_product
- collatz_scaled_one_cycle_nat_unit_product
- collatz_scaled_one_cycle_is_unit_boundary
- collatz_scaled_one_cycle_no_prime_channel_on_base
- collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
- collatz_scaled_one_cycle_no_prime_channel_on_unit_product

The intended reading is:

  3*n + 1 = 2^h*n
  -> ((2^h)-3) * n = 1
  -> closed one-step loop has unit support
  -> no prime channel remains

Goal:
Create a thin bridge file that connects this Collatz/Petal one-cycle language
to the existing valuation-flow vocabulary without forcing the ABC primitive
flow subject into the Collatz equation.

Preferred new file:

  DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean

Imports:

  import DkMath.Collatz.PetalBridge.OneCycle
  import DkMath.ABC.ValuationFlowBridge

If the ABC import is too heavy or creates cycles, instead import the smallest
ABC files needed for supportMass / rad facts and report the adjusted import.

Also update:

  DkMath/Collatz/PetalBridge.lean

to import the new bridge file if there is no cycle.

Global rules:
- Do not claim general Collatz cycle uniqueness.
- Do not claim Collatz convergence.
- Do not claim arbitrary nontrivial cycles are impossible.
- Keep every theorem explicitly about the equation
    3*n + 1 = 2^h*n
  or its unit-product consequences.

Part A: project-facing aliases.

In the new bridge file, add aliases with valuation-flow names:

  theorem oneCycle_unit_boundary_only
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      n = 1 ∧ h = 2 :=
    collatz_scaled_one_cycle_is_unit_boundary hn hcycle

  theorem oneCycle_unit_product_nat
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      n * (2 ^ h - 3) = 1 :=
    collatz_scaled_one_cycle_nat_unit_product hn hcycle

  theorem oneCycle_unit_product_int
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      (((2 ^ h : Nat) : Int) - 3) * (n : Int) = 1 :=
    collatz_scaled_one_cycle_int_unit_product hn hcycle

Part B: no-channel bridge aliases.

Add bridge-facing aliases:

  theorem oneCycle_no_prime_channel_on_base
      {p n h : Nat}
      (hp : Nat.Prime p)
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      ¬ p ∣ n :=
    collatz_scaled_one_cycle_no_prime_channel_on_base hp hn hcycle

  theorem oneCycle_no_prime_channel_on_scaleGap
      {p n h : Nat}
      (hp : Nat.Prime p)
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      ¬ p ∣ 2 ^ h - 3 :=
    collatz_scaled_one_cycle_no_prime_channel_on_scale_gap hp hn hcycle

  theorem oneCycle_no_prime_channel_on_unitProduct
      {p n h : Nat}
      (hp : Nat.Prime p)
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      ¬ p ∣ n * (2 ^ h - 3) :=
    collatz_scaled_one_cycle_no_prime_channel_on_unit_product hp hn hcycle

Part C: supportMass / rad unit support theorem.

If supportMass is available from ABC, prove:

  theorem oneCycle_supportMass_unitProduct_eq_one
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      DkMath.ABC.supportMass (n * (2 ^ h - 3)) = 1

Expected proof:
  use oneCycle_unit_product_nat, then simp [DkMath.ABC.supportMass]

If `simp` does not unfold supportMass/rad enough, use the existing
supportMass_eq_abc_rad and rad_one theorem.

Optional theorem:

  theorem oneCycle_rad_unitProduct_eq_one
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      DkMath.ABC.rad (n * (2 ^ h - 3)) = 1

Only add this if `rad` is in the imported namespace and the statement is
project-compatible.

Part D: negative support theorem.

If supportMass theorem is easy, add:

  theorem oneCycle_no_supportMass_growth
      {n h : Nat}
      (hn : 0 < n)
      (hcycle : 3 * n + 1 = 2 ^ h * n) :
      DkMath.ABC.supportMass (n * (2 ^ h - 3)) ≤ 1

This is a convenience form for future bridge code.

Part E: keep OneCycle clean.

Do not move ABC imports into OneCycle.lean.
OneCycle.lean should remain the local Collatz obstruction file.
The new ValuationFlowBridge file should be the only place where the ABC bridge
is imported.

Part F: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-151-b.md

Include:
- which imports were used,
- whether the bridge file imported ABC.ValuationFlowBridge directly or only a smaller ABC file,
- which one-cycle aliases were added,
- whether supportMass/rad unit theorems were proved,
- whether the aggregate PetalBridge import was updated,
- explicit note that this bridge does not prove general Collatz cycle uniqueness or convergence,
- explicit note that it only treats the one-step scaled equation
    3*n + 1 = 2^h*n.

Verification:

  lake build DkMath.Collatz.PetalBridge.OneCycle
  lake build DkMath.Collatz.PetalBridge.ValuationFlowBridge
  lake build DkMath.Collatz.PetalBridge

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/ValuationFlowBridge.lean

Also run:

  git diff --check
```

## 総評

これは良い割り込みじゃ。
`OneCycle` は、ただの

```text id="1quxw2"
n = 1, h = 2
```

の分類補題から、

```text id="bf4s2r"
unit boundary
no prime channel
support collapse
```

の補題へ育った。

このまま `OneCycle` を肥大化させず、次に薄い `ValuationFlowBridge` を置けば、Collatz/PetalBridge と ABC/ValuationFlowBridge の間に、かなり綺麗な橋が架かるぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
index 68e327d3..aa4a82bc 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
@@ -21,6 +21,32 @@ It proves only that the one-step accelerated odd cycle equation
 has no positive scaled copies except the genuine boundary point `n = 1`,
 `h = 2`.  It does not rule out arbitrary nontrivial Collatz cycles and does
 not prove convergence.
+
+Interruption research note after checkpoint 151: relation to
+`DkMath.ABC.ValuationFlowBridge`.
+
+The tempting bridge is:
+
+```text
+ABC.ValuationFlowBridge:
+  non-unit diff/support produces primitive prime channels and support mass.
+
+Collatz.OneCycle:
+  a one-step return to the same odd state forces
+  3*n + 1 = 2^h*n, hence ((2^h)-3)*n = 1.
+```
+
+So this file should first expose the Collatz side as a **unit-boundary**
+statement.  Do not import the ABC bridge here yet: its main primitive-flow
+subject is `a^d - b^d`, while this file's subject is the local Collatz equation
+`3*n + 1 = 2^h*n`.  The safe common language is:
+
+```text
+closed one-step loop -> unit product -> no prime channel remains
+```
+
+This is exactly the information a later thin
+`DkMath.Collatz.PetalBridge.ValuationFlowBridge` can consume.
 -/
 
 /--
@@ -154,4 +180,111 @@ theorem one_four_two_one_petal_scaled_cycle_unique
     n = 1 ∧ h = 2 :=
   collatz_scaled_one_cycle_eq_one hn hcycle
 
+/--
+Integer unit-product form of the scaled one-step cycle equation.
+
+This is the algebraic bridge to the valuation-flow reading: a closed one-step
+loop has no room for a non-unit support channel, because the product
+`((2^h)-3) * n` is exactly `1`.
+-/
+theorem collatz_scaled_one_cycle_int_unit_product
+    {n h : ℕ}
+    (_hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ) = 1 := by
+  have hcycle_int :
+      (3 : ℤ) * (n : ℤ) + 1 =
+        ((2 ^ h : ℕ) : ℤ) * (n : ℤ) := by
+    exact_mod_cast hcycle
+  calc
+    (((2 ^ h : ℕ) : ℤ) - 3) * (n : ℤ)
+        = ((2 ^ h : ℕ) : ℤ) * (n : ℤ) - (3 : ℤ) * (n : ℤ) := by
+          ring
+    _ = ((3 : ℤ) * (n : ℤ) + 1) - (3 : ℤ) * (n : ℤ) := by
+          rw [← hcycle_int]
+    _ = 1 := by
+          ring
+
+/--
+Natural-number unit-product form of the scaled one-step cycle equation.
+
+This uses the uniqueness theorem to avoid Nat-subtraction noise.  In the only
+positive solution, `2^h - 3 = 1` and `n = 1`.
+-/
+theorem collatz_scaled_one_cycle_nat_unit_product
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n * (2 ^ h - 3) = 1 := by
+  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
+  rcases hsol with ⟨rfl, rfl⟩
+  norm_num
+
+/--
+Project-facing alias: the scaled one-cycle closes only at the unit boundary.
+
+The phrase "unit boundary" is intentional.  It marks the shared vocabulary with
+the valuation-flow view without importing the ABC bridge into this local file.
+-/
+theorem collatz_scaled_one_cycle_is_unit_boundary
+    {n h : ℕ}
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    n = 1 ∧ h = 2 :=
+  collatz_scaled_one_cycle_eq_one hn hcycle
+
+/--
+No prime channel can remain on the base `n` of a positive scaled one-step
+cycle.
+
+Valuation-flow reading: if the loop closes, the base support has collapsed to
+the unit `1`.
+-/
+theorem collatz_scaled_one_cycle_no_prime_channel_on_base
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ n := by
+  intro hpn
+  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
+  rw [hsol.1] at hpn
+  exact hp.not_dvd_one hpn
+
+/--
+No prime channel can remain on the scale gap `2^h - 3` of a positive scaled
+one-step cycle.
+
+Valuation-flow reading: the scale gap is also forced to the unit `1`.
+-/
+theorem collatz_scaled_one_cycle_no_prime_channel_on_scale_gap
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ 2 ^ h - 3 := by
+  intro hpgap
+  have hsol := collatz_scaled_one_cycle_eq_one hn hcycle
+  rw [hsol.2] at hpgap
+  norm_num at hpgap
+  have hp_two : 2 ≤ p := hp.two_le
+  omega
+
+/--
+No prime channel can divide the explicit unit product of a positive scaled
+one-step cycle.
+
+This is the most compact no-channel form for later bridge files.
+-/
+theorem collatz_scaled_one_cycle_no_prime_channel_on_unit_product
+    {p n h : ℕ}
+    (hp : Nat.Prime p)
+    (hn : 0 < n)
+    (hcycle : 3 * n + 1 = 2 ^ h * n) :
+    ¬ p ∣ n * (2 ^ h - 3) := by
+  intro hpdiv
+  have hunit := collatz_scaled_one_cycle_nat_unit_product hn hcycle
+  rw [hunit] at hpdiv
+  exact hp.not_dvd_one hpdiv
+
 end DkMath.Collatz
````
`````
