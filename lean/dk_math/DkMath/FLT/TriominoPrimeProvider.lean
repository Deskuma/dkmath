/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.TriominoMainBridge

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Triomino Prime Provider Entry

`GlobalPrimeExponentFLTProvider` を受け取り、
Triomino 側の確定版 API（bridge 公開）から FLT 結論を得る入口。
-/

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

/--
global provider から一般指数版（`n ≥ 3`）の結論を得る。
-/
theorem FLT_general_via_triominoPrimeProvider
    {x y z n : ℕ}
    (hprov : TriominoPrimeProvider)
    (hn : 3 ≤ n)
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (h_eq : x ^ n + y ^ n = z ^ n) : False := by
  exact FLT_general_via_triominoGlobalProvider
    (x := x) (y := y) (z := z) (n := n)
    hprov hn hpos h_eq

/--
global provider から `d=3` 版の結論を得る（正値仮定付き）。
-/
theorem FLT_d3_via_triominoPrimeProvider
    {a b c : ℕ}
    (hprov : TriominoPrimeProvider)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hEq
  exact FLT_general_via_triominoPrimeProvider
    (x := a) (y := b) (z := c) (n := 3)
    hprov (by decide) ⟨ha, hb, hc⟩ hEq

/--
`FermatLastTheorem` 仮定から一般指数版（`n ≥ 3`）を得る。
-/
theorem FLT_general_via_fermatLastTheorem
    {x y z n : ℕ}
    (hFLT : FermatLastTheorem)
    (hn : 3 ≤ n)
    (hpos : 0 < x ∧ 0 < y ∧ 0 < z)
    (h_eq : x ^ n + y ^ n = z ^ n) : False := by
  exact FLT_general_via_triominoPrimeProvider
    (x := x) (y := y) (z := z) (n := n)
    (triominoPrimeProvider_of_fermatLastTheorem hFLT) hn hpos h_eq

/--
`FermatLastTheorem` 仮定から `d=3` 版を得る。
-/
theorem FLT_d3_via_fermatLastTheorem
    {a b c : ℕ}
    (hFLT : FermatLastTheorem)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_via_triominoPrimeProvider
    (a := a) (b := b) (c := c)
    (triominoPrimeProvider_of_fermatLastTheorem hFLT) ha hb hc

end DkMath.FLT
