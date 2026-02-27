/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Core

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Prime Provider Core

provider 系の型・alias・仮定変換だけを置く薄い共有層。

方針:
- ここには「結論を返す橋渡し定理」は置かない。
- `TriominoMainBridge` と `TriominoPrimeProvider` は、このファイルを共有依存先にする。
- 依存循環を避けるため、ここから bridge / triomino 本体へは依存しない。
-/

namespace DkMath

/-- 高指数核で要求する「`n` に対する素数指数 FLT 供給」の型。 -/
abbrev PrimeExponentFLTProvider (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ≠ 2 → p ≠ 3 → FermatLastTheoremFor p

/-- グローバル版（`p ≠ 2,3` の全素数に対する供給）。 -/
abbrev GlobalPrimeExponentFLTProvider : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≠ 3 → FermatLastTheoremFor p

/-- グローバル供給から、固定 `n` の供給へ落とす。 -/
lemma primeExponentFLTProvider_of_global {n : ℕ}
    (hglobal : GlobalPrimeExponentFLTProvider) :
    PrimeExponentFLTProvider n := by
  intro p hpprime hpdvdn hp_ne2 hp_ne3
  exact hglobal p hpprime hp_ne2 hp_ne3

end DkMath

namespace DkMath.FLT

/-- Triomino 高指数核で要求する global provider の別名。 -/
abbrev TriominoPrimeProvider :=
  DkMath.GlobalPrimeExponentFLTProvider

/--
`FermatLastTheorem` 仮定から `TriominoPrimeProvider` を生成する。
-/
lemma triominoPrimeProvider_of_fermatLastTheorem
    (hFLT : FermatLastTheorem) :
    TriominoPrimeProvider := by
  intro p hpprime hp_ne2 hp_ne3
  have hp_ge3 : 3 ≤ p := by
    have hp_ge2 : 2 ≤ p := hpprime.two_le
    omega
  exact hFLT p hp_ge3

/--
odd prime 指数の FLT 供給から `FermatLastTheorem` を経由して
`TriominoPrimeProvider` を生成する。
-/
lemma triominoPrimeProvider_of_oddPrimes
    (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremFor p) :
    TriominoPrimeProvider := by
  exact triominoPrimeProvider_of_fermatLastTheorem
    (FermatLastTheorem.of_odd_primes hprimes)

end DkMath.FLT
