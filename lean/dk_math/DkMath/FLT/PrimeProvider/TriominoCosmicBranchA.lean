/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/--
`Basic.lean` から呼ぶ Branch A（`p ∣ z - y`）専用の gap-power 供給仕様。

`GapInvariant` の本線 API とは切り離し、`Basic` が依存循環なしで参照できる
最小入口として lower layer に固定する。
-/
abbrev PrimeGe5BranchAGapPowFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∀ q : ℕ, p ∣ (z - y).factorization q

/--
Branch A の因数分解指数仕様が供給されれば、`gap = z - y` は pure `p` 乗に落ちる。
-/
theorem primeGe5BranchAGapPow_of_factorization
    (hFac : PrimeGe5BranchAGapPowFactorizationTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ t : ℕ, (z - y) = t ^ p := by
  intro p x y z hpack hp_dvd_gap
  have hp0 : 0 < p := hpack.hp.pos
  have hgap_ne0 : (z - y) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  exact exists_eq_pow_of_factorization_dvd
    (u := z - y) (p := p)
    hgap_ne0 hp0
    (hFac hpack hp_dvd_gap)

/--
`FLT_of_coprime` の residual branch から呼ぶ Branch A 専用 refuter 入口。

将来は `PrimeGe5BranchAGapPowFactorizationTarget` と shape/descent kernel を
ここで合成する。現段階では残差 `sorry` を `Basic.lean` から切り離して
この lower layer に局所化する。
-/
theorem primeGe5BranchARefuter_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  /-
  TODO:
  1. `q ≠ p` / `q = p` の Branch A factorization spine を接続する。
  2. shape もしくは pure gap-pow を既存 descent/refuter kernel へ送る。
  3. `Basic.lean` 側はこの入口だけを呼び続ける。
  -/
  sorry

end DkMath.FLT
