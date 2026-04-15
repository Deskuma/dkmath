/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5
import DkMath.FLT.CosmicPetalBridge
import DkMath.NumberTheory.ZsigmondyCyclotomic

#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore"

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
    ¬ p ∣ (z - y) →
    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
    ¬ q ^ 2 ∣ (z ^ p - y ^ p)

/--
`p = 3` 専用の NoWieferich bridge。

`PrimeGe5CounterexamplePack` では `p = 3` が到達不能なため、
FLT3 実パスに刺す入口は別契約として分離する。
-/
abbrev TriominoNoWieferichBridge3 : Prop :=
  ∀ {x y z q : ℕ}, PrimeCounterexamplePack 3 x y z →
    ¬ 3 ∣ (z - y) →
    Nat.Prime q → q ∣ (z ^ 3 - y ^ 3) → ¬ q ∣ (z - y) →
    ¬ q ^ 2 ∣ (z ^ 3 - y ^ 3)

/-- 反例文脈での Wieferich 型 lift（原始素因子が 2 段刺さる）を表す。 -/
def WieferichLift (p y z q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ (z ^ p - y ^ p) ∧ ¬ q ∣ (z - y) ∧ q ^ 2 ∣ (z ^ p - y ^ p)

/--
Triomino/Cosmic 側が最終的に供給すべき「Wieferich lift は反例文脈で起きない」橋。

将来的には、`WieferichLift` からより小さな反例を構成する下降補題を経由して
この命題を示すことを想定する。
-/
abbrev TriominoWieferichLiftExclusion : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) ->
    WieferichLift p y z q -> False

/-- prime-ge5 反例パックに最小性（`z` 最小）を付加した版。 -/
abbrev MinimalPrimeGe5CounterexamplePack (p x y z : ℕ) : Prop :=
  PrimeGe5CounterexamplePack p x y z ∧
  ∀ {x' y' z' : ℕ}, PrimeGe5CounterexamplePack p x' y' z' -> z' < z -> False

/-- Branch B 条件（`¬ p ∣ (z - y)`）付きの最小反例 pack。 -/
abbrev MinimalPrimeGe5CounterexamplePackB (p x y z : ℕ) : Prop :=
  PrimeGe5CounterexamplePack p x y z ∧ ¬ p ∣ (z - y) ∧
  ∀ {x' y' z' : ℕ}, PrimeGe5CounterexamplePack p x' y' z' ->
    ¬ p ∣ (z' - y') -> z' < z -> False

/-- 任意の prime-ge5 反例パックから Wieferich lift を 1 つ取り出せる、という入力仕様。 -/
abbrev CounterexampleHasWieferichLift : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    ∃ q : ℕ, WieferichLift p y z q

/-- Branch B 専用: `¬ p ∣ (z - y)` の領域なら Wieferich lift を 1 つ取り出せる。 -/
abbrev CounterexampleHasWieferichLiftB : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    ¬ p ∣ (z - y) ->
    ∃ q : ℕ, WieferichLift p y z q

/-- Wieferich lift が起きたら、より小さい反例を構成できるという下降仕様。 -/
abbrev WieferichDescent : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    WieferichLift p y z q ->
    ∃ x' y' z' : ℕ, PrimeGe5CounterexamplePack p x' y' z' ∧ z' < z

/-- Branch B 専用: `¬ p ∣ (z - y)` の領域での下降仕様。 -/
abbrev WieferichDescentB : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    ¬ p ∣ (z - y) ->
    WieferichLift p y z q ->
    ∃ x' y' z' : ℕ, PrimeGe5CounterexamplePack p x' y' z' ∧ ¬ p ∣ (z' - y') ∧ z' < z

/--
Wieferich lift を起こす反例があれば、その中から `z` 最小のものを選べるという選択仕様。
-/
abbrev MinimalWieferichLiftSelection : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    ¬ p ∣ (z - y) ->
    WieferichLift p y z q ->
    ∃ x₀ y₀ z₀ q₀ : ℕ,
      MinimalPrimeGe5CounterexamplePackB p x₀ y₀ z₀ ∧ WieferichLift p y₀ z₀ q₀

/-- 任意の反例パックから、`z` 最小の反例パックを no-`so#rry` で選べる。 -/
theorem minimalPrimeGe5CounterexampleSelection_impl :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z ->
      ∃ x₀ y₀ z₀ : ℕ, MinimalPrimeGe5CounterexamplePack p x₀ y₀ z₀ := by
  classical
  intro p x y z hpack
  let P : ℕ → Prop := fun z₀ => ∃ x₀ y₀ : ℕ, PrimeGe5CounterexamplePack p x₀ y₀ z₀
  have hExists : ∃ z₀ : ℕ, P z₀ := ⟨z, x, y, hpack⟩
  let z₀ := Nat.find hExists
  have hz₀ : P z₀ := Nat.find_spec hExists
  rcases hz₀ with ⟨x₀, y₀, hpack₀⟩
  refine ⟨x₀, y₀, z₀, hpack₀, ?_⟩
  intro x' y' z' hpack' hz'lt
  have hz₀_le : z₀ ≤ z' := by
    simpa [z₀] using (Nat.find_min' hExists ⟨x', y', hpack'⟩)
  exact (not_le_of_gt hz'lt) hz₀_le

/-- Branch B 条件付きで、`z` 最小の反例 pack を no-`so#rry` で選べる。 -/
theorem minimalPrimeGe5CounterexampleSelectionB_impl :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z ->
      ¬ p ∣ (z - y) ->
      ∃ x₀ y₀ z₀ : ℕ, MinimalPrimeGe5CounterexamplePackB p x₀ y₀ z₀ := by
  classical
  intro p x y z hpack hp_not_dvd_gap
  let P : ℕ → Prop := fun z₀ => ∃ x₀ y₀ : ℕ,
    PrimeGe5CounterexamplePack p x₀ y₀ z₀ ∧ ¬ p ∣ (z₀ - y₀)
  have hExists : ∃ z₀ : ℕ, P z₀ := ⟨z, x, y, hpack, hp_not_dvd_gap⟩
  let z₀ := Nat.find hExists
  have hz₀ : P z₀ := Nat.find_spec hExists
  rcases hz₀ with ⟨x₀, y₀, hpack₀, hb₀⟩
  refine ⟨x₀, y₀, z₀, hpack₀, hb₀, ?_⟩
  intro x' y' z' hpack' hb' hz'lt
  have hz₀_le : z₀ ≤ z' := by
    simpa [z₀] using (Nat.find_min' hExists ⟨x', y', hpack', hb'⟩)
  exact (not_le_of_gt hz'lt) hz₀_le

/-- Branch B の `反例 => lift` が供給されれば、最小反例 + lift の選択仕様は no-`so#rry` で得られる。 -/
theorem minimalWieferichLiftSelection_of_liftExists
    (hLiftAll : CounterexampleHasWieferichLiftB) :
    MinimalWieferichLiftSelection := by
  intro p x y z q hpack hp_not_dvd_gap _hLift
  rcases minimalPrimeGe5CounterexampleSelectionB_impl hpack hp_not_dvd_gap with ⟨x₀, y₀, z₀, hMin⟩
  rcases hLiftAll hMin.1 hMin.2.1 with ⟨q₀, hLift₀⟩
  exact ⟨x₀, y₀, z₀, q₀, hMin, hLift₀⟩

/-- 最小反例と下降仕様があれば、その最小反例では Wieferich lift は起きえない。 -/
theorem wieferichLiftExclusion_of_descent_on_minimal
    (hDesc : WieferichDescentB) :
    ∀ {p x y z q : ℕ}, MinimalPrimeGe5CounterexamplePackB p x y z ->
      WieferichLift p y z q -> False := by
  intro p x y z q hMin hLift
  rcases hMin with ⟨hpack, hp_not_dvd_gap, hmin⟩
  rcases hDesc hpack hp_not_dvd_gap hLift with ⟨x', y', z', hpack', hp_not_dvd_gap', hz'lt⟩
  exact hmin hpack' hp_not_dvd_gap' hz'lt

/-- 最小反例選択と下降仕様があれば、全ての反例文脈で Wieferich lift を排除できる。 -/
theorem wieferichLiftExclusion_of_selection_and_descent
    (hSelect : MinimalWieferichLiftSelection)
    (hDesc : WieferichDescentB) :
    TriominoWieferichLiftExclusion := by
  intro p x y z q hpack hp_not_dvd_gap hLift
  rcases hSelect hpack hp_not_dvd_gap hLift with ⟨x₀, y₀, z₀, q₀, hMin, hLift₀⟩
  exact wieferichLiftExclusion_of_descent_on_minimal hDesc hMin hLift₀

/-- `WieferichLift` の排除があれば、`TriominoNoWieferichBridge` は直ちに従う。 -/
theorem triominoNoWieferichBridge_of_wieferichLiftExclusion
    (hExcl : TriominoWieferichLiftExclusion) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap hq2_dvd_diff
  exact hExcl hpack hp_not_dvd_gap ⟨hqP, hq_dvd_diff, hq_not_dvd_gap, hq2_dvd_diff⟩

/--
`TriominoNoWieferichBridge` が供給されれば、一般 `GN` の nonlift family は no-`so#rry` で得られる。

ここでは `z^p - y^p = (z-y) * GN p (z-y) y` を使い、
`q^2 ∤ (z^p - y^p)` から `q^2 ∤ GN` を引き戻す。
-/
theorem triominoCosmicNonLiftableGNBridge_of_noWieferich
    (hNW : TriominoNoWieferichBridge) :
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) ->
      ∀ q : ℕ,
        (Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ∣ (z - y)) ->
        ¬ q ^ 2 ∣ GN p (z - y) y := by
  intro p x y z hpack hp_not_dvd_gap q hPrim
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
  exact (hNW hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap) hq2_dvd_diff

/--
`p = 3` 専用: `TriominoNoWieferichBridge3` から `GN` 側 no-lift を引き戻す。
-/
theorem triominoCosmicNonLiftableGN3Bridge_of_noWieferich3
    (hNW3 : TriominoNoWieferichBridge3) :
  ∀ {x y z : ℕ}, PrimeCounterexamplePack 3 x y z →
      ¬ 3 ∣ (z - y) ->
      ∀ q : ℕ,
        (Nat.Prime q ∧ q ∣ GN 3 (z - y) y ∧ ¬ q ∣ (z - y)) ->
        ¬ q ^ 2 ∣ GN 3 (z - y) y := by
  intro x y z hpack h3_not_dvd_gap q hPrim
  rcases hPrim with ⟨hqP, hq_dvd_GN, hq_not_dvd_gap⟩
  have hfactor : z ^ 3 - y ^ 3 = (z - y) * GN 3 (z - y) y := by
    simpa using pow_sub_pow_factor_cosmic_N (a := z) (b := y) (d := 3) (by norm_num) hpack.hyz_lt
  have hq_dvd_diff : q ∣ z ^ 3 - y ^ 3 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right hq_dvd_GN (z - y)
  intro hq2_dvd_GN
  have hq2_dvd_diff : q ^ 2 ∣ z ^ 3 - y ^ 3 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right hq2_dvd_GN (z - y)
  exact (hNW3 hpack h3_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap) hq2_dvd_diff

/--
Triomino/Cosmic 側が最終的に供給すべき「最小反例選択 + 下降」のカーネル。
-/
abbrev TriominoWieferichLiftKernel : Prop :=
  CounterexampleHasWieferichLiftB ∧ WieferichDescentB

/-- `反例 => lift` と下降仕様があれば、Wieferich lift 排除は no-`so#rry` で従う。 -/
theorem wieferichLiftExclusion_of_liftExists_and_descent
    (hLiftAll : CounterexampleHasWieferichLiftB)
    (hDesc : WieferichDescentB) :
    TriominoWieferichLiftExclusion := by
  exact wieferichLiftExclusion_of_selection_and_descent
    (minimalWieferichLiftSelection_of_liftExists hLiftAll)
    hDesc

/--
Branch B のみを見れば、反例パックからの Wieferich lift 供給は no-`so#rry` で閉じる。

`¬ p ∣ (z - y)` のもとで Zsigmondy の原始素因子 `q` を取り、
`z^p - y^p = x^p` を使って `q^2 ∣ z^p - y^p` を付加する。
-/
theorem counterexampleHasWieferichLiftB_impl :
    CounterexampleHasWieferichLiftB := by
  intro p x y z hpack hp_not_dvd_gap
  have hyz_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  rcases exists_primitive_prime_factor_prime
      (a := z) (b := y) (d := p)
      hpack.hp
      (le_trans (by decide : 3 ≤ 5) hpack.hp5)
      hpack.hyz_lt
      hpack.y_pos
      hyz_coprime
      hp_not_dvd_gap with
    ⟨q, hqP, hq_dvd_diff, hq_not_dvd_gap⟩
  have hyz_pow : y ^ p ≤ z ^ p := by
    exact Nat.pow_le_pow_left hpack.hyz p
  have hdiff : z ^ p - y ^ p = x ^ p := by
    have hcancel : z ^ p - y ^ p + y ^ p = x ^ p + y ^ p := by
      rw [Nat.sub_add_cancel hyz_pow, hpack.hEq]
    exact Nat.add_right_cancel hcancel
  have hq_dvd_xpow : q ∣ x ^ p := by
    simpa [hdiff] using hq_dvd_diff
  have hq_dvd_x : q ∣ x := hqP.dvd_of_dvd_pow hq_dvd_xpow
  have hp_ge_two : 2 ≤ p := by
    exact le_trans (by decide : 2 ≤ 5) hpack.hp5
  have hq2_dvd_qp : q ^ 2 ∣ q ^ p := by
    exact pow_dvd_pow q hp_ge_two
  have hqp_dvd_xp : q ^ p ∣ x ^ p := by
    exact pow_dvd_pow_of_dvd hq_dvd_x p
  have hq2_dvd_xpow : q ^ 2 ∣ x ^ p := by
    exact dvd_trans hq2_dvd_qp hqp_dvd_xp
  have hq2_dvd_diff : q ^ 2 ∣ z ^ p - y ^ p := by
    simpa [hdiff] using hq2_dvd_xpow
  exact ⟨q, hqP, hq_dvd_diff, hq_not_dvd_gap, hq2_dvd_diff⟩

end DkMath.FLT
