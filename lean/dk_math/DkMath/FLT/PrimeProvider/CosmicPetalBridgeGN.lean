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
    WieferichLift p y z q -> False

/-- prime-ge5 反例パックに最小性（`z` 最小）を付加した版。 -/
abbrev MinimalPrimeGe5CounterexamplePack (p x y z : ℕ) : Prop :=
  PrimeGe5CounterexamplePack p x y z ∧
  ∀ {x' y' z' : ℕ}, PrimeGe5CounterexamplePack p x' y' z' -> z' < z -> False

/-- 任意の prime-ge5 反例パックから Wieferich lift を 1 つ取り出せる、という入力仕様。 -/
abbrev CounterexampleHasWieferichLift : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    ∃ q : ℕ, WieferichLift p y z q

/-- Wieferich lift が起きたら、より小さい反例を構成できるという下降仕様。 -/
abbrev WieferichDescent : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    WieferichLift p y z q ->
    ∃ x' y' z' : ℕ, PrimeGe5CounterexamplePack p x' y' z' ∧ z' < z

/--
Wieferich lift を起こす反例があれば、その中から `z` 最小のものを選べるという選択仕様。
-/
abbrev MinimalWieferichLiftSelection : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z ->
    WieferichLift p y z q ->
    ∃ x₀ y₀ z₀ q₀ : ℕ,
      MinimalPrimeGe5CounterexamplePack p x₀ y₀ z₀ ∧ WieferichLift p y₀ z₀ q₀

/-- 任意の反例パックから、`z` 最小の反例パックを no-`sorry` で選べる。 -/
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

/-- `反例 => lift` が供給されれば、最小反例 + lift の選択仕様は no-`sorry` で得られる。 -/
theorem minimalWieferichLiftSelection_of_liftExists
    (hLiftAll : CounterexampleHasWieferichLift) :
    MinimalWieferichLiftSelection := by
  intro p x y z q hpack _hLift
  rcases minimalPrimeGe5CounterexampleSelection_impl hpack with ⟨x₀, y₀, z₀, hMin⟩
  rcases hLiftAll hMin.1 with ⟨q₀, hLift₀⟩
  exact ⟨x₀, y₀, z₀, q₀, hMin, hLift₀⟩

/-- 最小反例と下降仕様があれば、その最小反例では Wieferich lift は起きえない。 -/
theorem wieferichLiftExclusion_of_descent_on_minimal
    (hDesc : WieferichDescent) :
    ∀ {p x y z q : ℕ}, MinimalPrimeGe5CounterexamplePack p x y z ->
      WieferichLift p y z q -> False := by
  intro p x y z q hMin hLift
  rcases hMin with ⟨hpack, hmin⟩
  rcases hDesc hpack hLift with ⟨x', y', z', hpack', hz'lt⟩
  exact hmin hpack' hz'lt

/-- 最小反例選択と下降仕様があれば、全ての反例文脈で Wieferich lift を排除できる。 -/
theorem wieferichLiftExclusion_of_selection_and_descent
    (hSelect : MinimalWieferichLiftSelection)
    (hDesc : WieferichDescent) :
    TriominoWieferichLiftExclusion := by
  intro p x y z q hpack hLift
  rcases hSelect hpack hLift with ⟨x₀, y₀, z₀, q₀, hMin, hLift₀⟩
  exact wieferichLiftExclusion_of_descent_on_minimal hDesc hMin hLift₀

/-- `WieferichLift` の排除があれば、`TriominoNoWieferichBridge` は直ちに従う。 -/
theorem triominoNoWieferichBridge_of_wieferichLiftExclusion
    (hExcl : TriominoWieferichLiftExclusion) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hqP hq_dvd_diff hq_not_dvd_gap hq2_dvd_diff
  exact hExcl hpack ⟨hqP, hq_dvd_diff, hq_not_dvd_gap, hq2_dvd_diff⟩

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
Triomino/Cosmic 側が最終的に供給すべき「最小反例選択 + 下降」のカーネル。
-/
abbrev TriominoWieferichLiftKernel : Prop :=
  CounterexampleHasWieferichLift ∧ WieferichDescent

/-- `反例 => lift` と下降仕様があれば、Wieferich lift 排除は no-`sorry` で従う。 -/
theorem wieferichLiftExclusion_of_liftExists_and_descent
    (hLiftAll : CounterexampleHasWieferichLift)
    (hDesc : WieferichDescent) :
    TriominoWieferichLiftExclusion := by
  exact wieferichLiftExclusion_of_selection_and_descent
    (minimalWieferichLiftSelection_of_liftExists hLiftAll)
    hDesc

/--
一般 `GN` nonlift bridge の本丸インターフェイス。

現時点では、最後の未解決点を「最小反例選択 + 下降」カーネルに隔離する。
-/
theorem triominoWieferichLiftKernel_impl : TriominoWieferichLiftKernel := by
  -- TODO:
  -- 1. Wieferich lift を起こす反例から `z` 最小のものを選ぶ。
  -- 2. その最小反例で Wieferich lift が起きたなら、より小さい反例を構成する。
  -- この 2 段（最小反例選択 + 下降）が、最後の未解決カーネル。
  sorry

/-- 現段階の `TriominoWieferichLiftExclusion` は、最小反例選択と下降のカーネルへ委譲する。 -/
theorem triominoWieferichLiftExclusion_impl : TriominoWieferichLiftExclusion := by
  exact wieferichLiftExclusion_of_liftExists_and_descent
    triominoWieferichLiftKernel_impl.1
    triominoWieferichLiftKernel_impl.2

/-- 現段階の `TriominoNoWieferichBridge` 実装は、Wieferich lift 排除ブリッジへ委譲する。 -/
theorem triominoNoWieferichBridge_impl : TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_wieferichLiftExclusion
    triominoWieferichLiftExclusion_impl

end DkMath.FLT
