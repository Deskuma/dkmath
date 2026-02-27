/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/-!
# Triomino/Cosmic Gap Invariant

`TriominoCosmicGapInvariant` の本体証明を育てる隔離モジュール。
`TriominoCosmicPrimeGe5` は staging として維持し、このファイル側にのみ
研究中の本丸を閉じ込める。
-/

/--
Triomino/Cosmic 本丸:
primitive 反例パックがあるなら gap は `p` 乗になれない。

現時点では本体未実装。`TODO-2` の未解決点をこのファイル 1 箇所へ隔離する。
-/
theorem triominoCosmicGapInvariant : TriominoCosmicGapInvariant := by
  intro p x y z hpack
  let u : ℕ := hpack.gap
  have hu_pos : 0 < u := by
    simpa [u] using hpack.gap_pos
  have hcop_uy : Nat.Coprime u y := by
    simpa [u] using hpack.gap_coprime_right
  have hxpow := by
    simpa [u, PrimeCounterexamplePack.gap] using
      (pow_eq_sub_mul_GN_of_add_pow_eq p x y z hpack.hyz hpack.hEq)
  clear hu_pos hcop_uy hxpow
  sorry

end DkMath.FLT
