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

end DkMath.FLT
