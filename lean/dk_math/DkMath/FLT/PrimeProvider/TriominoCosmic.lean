/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProviderCore

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Triomino/Cosmic Prime Provider Staging

Triomino/Cosmic 側の理屈で `GlobalPrimeExponentFLTProvider` を構成するための
段階的な staging モジュール。

この段階では、まだ `TriominoFLT` 本体へは依存しない。
まずは「`p ≥ 5` の素数指数 FLT が供給できれば global provider が得られる」
という配線だけを確定する。
-/

namespace DkMath.FLT

/--
Triomino/Cosmic 側で最終的に埋めるべき中間ターゲット:
`5 ≤ p` の素数指数に対する FLT 供給。
-/
abbrev PrimeGe5FLTProvider : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p → FermatLastTheoremFor p

/--
素数 `p` が `2,3` 以外なら `5 ≤ p`。
`GlobalPrimeExponentFLTProvider` を作る際の入口整理用補題。
-/
lemma prime_ge_five_of_prime_ne_two_ne_three {p : ℕ}
    (hp : Nat.Prime p)
    (hp_ne2 : p ≠ 2)
    (hp_ne3 : p ≠ 3) :
    5 ≤ p := by
  have hp_ge2 : 2 ≤ p := hp.two_le
  by_contra hp_lt5
  have hp_le4 : p ≤ 4 := by omega
  interval_cases p
  · exact hp_ne2 rfl
  · exact hp_ne3 rfl
  · exact (by decide : ¬ Nat.Prime 4) hp

/--
`p ≥ 5` の素数指数 FLT 供給から、global provider を得る。
残る本質的な作業は `PrimeGe5FLTProvider` を Triomino/Cosmic 側で埋めること。
-/
theorem triominoCosmic_globalProvider_of_primeGe5
    (hprimeGe5 : PrimeGe5FLTProvider) :
    GlobalPrimeExponentFLTProvider := by
  intro p hp hp_ne2 hp_ne3
  exact hprimeGe5 p hp (prime_ge_five_of_prime_ne_two_ne_three hp hp_ne2 hp_ne3)

/--
`PrimeGe5FLTProvider` から `TriominoPrimeProvider` を得る。
既存の provider 系 API へ直接接続するための別名。
-/
theorem triominoPrimeProvider_of_primeGe5
    (hprimeGe5 : PrimeGe5FLTProvider) :
    TriominoPrimeProvider := by
  exact triominoCosmic_globalProvider_of_primeGe5 hprimeGe5

end DkMath.FLT
