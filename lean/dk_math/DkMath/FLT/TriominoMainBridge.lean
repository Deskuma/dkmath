/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Main
import DkMath.CosmicFormula.TriominoFLT

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Triomino -> FLT.Main Bridge

`TriominoFLT` 側で family 形の供給ができたときに、
`Main` の triomino 接続口へ委譲するアダプタモジュール。

注意:
- `Main` 本体は変更しない（依存方向固定のため）。
- 本ファイルは橋渡し専用。
-/

namespace DkMath.FLT

/-- Triomino 側から供給する `NoSq` family の型。 -/
abbrev TriominoHasNoSqFamily :=
  ∀ {c b : ℕ}, b < c → Nat.Coprime c b → NoSqOnS0 c b

/-- Triomino 側から供給する `NonLiftable` family の型。 -/
abbrev TriominoHasNonLiftableFamily :=
  ∀ {c b : ℕ}, b < c → Nat.Coprime c b → ∀ q : ℕ, NonLiftableS0 c b q

/--
Triomino 系 `NoSq` family を `Main` 入口へ接続する薄いアダプタ。
-/
theorem FLT_d3_by_padicValNat_via_triominoHasNoSqFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNoSqTriomino : TriominoHasNoSqFamily) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_triominoHasNoSqFamily_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime hasNoSqTriomino

/--
Triomino 系 `NonLiftable` family を `Main` 入口へ接続する薄いアダプタ。
-/
theorem FLT_d3_by_padicValNat_via_triominoHasNonLiftableFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNonLiftTriomino : TriominoHasNonLiftableFamily) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_triominoHasNonLiftableFamily_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime hasNonLiftTriomino

/--
`TriominoFLT` の確定版 API（global prime provider 版）への橋渡し。
`Main` 接続口ではなく、Triomino 側の完成度確認用に提供する。
-/
theorem FLT_general_via_triominoGlobalProvider
    {x y z n : ℕ}
    (hglobal : DkMath.GlobalPrimeExponentFLTProvider)
    (hn : 3 ≤ n)
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (h_eq : x ^ n + y ^ n = z ^ n) : False := by
  exact DkMath.FLT_general_via_tromino_of_globalPrimeProvider n hglobal hn hpos h_eq

/--
global prime provider を直接受ける `d=3` 版。
`Main` の family 接続とは独立した、Triomino 側確定版 API の橋渡し。
-/
theorem FLT_d3_via_triominoGlobalProvider
    {a b c : ℕ}
    (hglobal : DkMath.GlobalPrimeExponentFLTProvider)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hEq
  exact FLT_general_via_triominoGlobalProvider
    (x := a) (y := b) (z := c) (n := 3)
    hglobal (by decide) ⟨ha, hb, hc⟩ hEq

/--
`Main` の coprime-support 入口と同じ引数形で、
global prime provider を直接受ける `d=3` ラッパ。
-/
theorem FLT_d3_by_padicValNat_via_triominoGlobalProvider_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : Nat.Coprime a b)
    (_hbc : b < c)
    (_hcb_coprime : Nat.Coprime c b)
    (hglobal : DkMath.GlobalPrimeExponentFLTProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_via_triominoGlobalProvider
    (a := a) (b := b) (c := c) hglobal ha hb hc

end DkMath.FLT
