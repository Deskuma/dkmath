/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5
import DkMath.FLT.CosmicPetalBridge
import DkMath.NumberTheory.ZsigmondyCyclotomic

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.GcdNext

/--
Triomino/Cosmic 側が最終的に供給すべき「反例文脈では Wieferich 例外が起きない」橋。

`q` が `(z^p - y^p)` の原始素因子（`q ∤ z-y`）である限り、
`q^2 ∤ (z^p - y^p)` を要求する。
-/
abbrev TriominoNoWieferichBridge : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
    ¬ q ^ 2 ∣ (z ^ p - y ^ p)

/--
`TriominoNoWieferichBridge` が供給されれば、一般 `GN` の nonlift family は no-`sorry` で得られる。

ここでは `z^p - y^p = (z-y) * GN p (z-y) y` を使い、
`q^2 ∤ (z^p - y^p)` から `q^2 ∤ GN` を引き戻す。
-/
theorem triominoCosmicNonLiftableGNBridge_of_noWieferich
    (hNW : TriominoNoWieferichBridge) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ∀ q : ℕ,
        (Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ∣ (z - y)) ->
        ¬ q ^ 2 ∣ GN p (z - y) y := by
  intro p x y z hpack q hPrim
  rcases hPrim with ⟨hqP, hq_dvd_GN, hq_not_dvd_gap⟩
  have hp_pos : 0 < p := hpack.hp.pos
  have hfactor : z ^ p - y ^ p = (z - y) * GN p (z - y) y := by
    simpa using pow_sub_pow_factor_cosmic_N hp_pos hpack.hyz_lt
  have hq_dvd_diff : q ∣ z ^ p - y ^ p := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right hq_dvd_GN (z - y)
  intro hq2_dvd_GN
  have hq2_dvd_diff : q ^ 2 ∣ z ^ p - y ^ p := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right hq2_dvd_GN (z - y)
  exact (hNW hpack hqP hq_dvd_diff hq_not_dvd_gap) hq2_dvd_diff

/--
一般 `GN` nonlift bridge の本丸インターフェイス。

現時点では、`Triomino/Cosmic` 側の no-`sorry` 一般理論は未実装のため、
未解決点をこの 1 定理に隔離する。
-/
theorem triominoNoWieferichBridge_impl : TriominoNoWieferichBridge := by
  intro p x y z q hpack hqP hq_dvd_diff hq_not_dvd_gap
  -- TODO:
  -- prime-ge5 の反例文脈で、原始素因子 `q` は `(z^p - y^p)` に 2 段持ち上がらない
  -- （Wieferich 型例外が起きない）ことを、
  -- Triomino / Cosmic / Phase / NonLiftable の理論から供給する。
  sorry

end DkMath.FLT
