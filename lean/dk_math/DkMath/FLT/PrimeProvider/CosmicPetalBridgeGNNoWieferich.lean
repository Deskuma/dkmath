/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
import DkMath.NumberTheory.Gcd
import DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree

#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
Branch B の lift 抽出と下降仕様が揃えば、NoWieferich bridge は直ちに従う。

このファイルは phase-15 の研究室として作られたが、現時点では
`CosmicPetalBridgeGNCore` にある no-`so#rry` の合成だけで閉じる。
-/
theorem triominoNoWieferichBridge_of_descent
    (hDesc : WieferichDescentB) :
    TriominoNoWieferichBridge := by
  exact
    triominoNoWieferichBridge_of_wieferichLiftExclusion <|
      wieferichLiftExclusion_of_liftExists_and_descent
        counterexampleHasWieferichLiftB_impl
        hDesc

/--
`padicValNat q (z^p - y^p) ≤ 1` が一様に供給できれば、NoWieferich bridge は直ちに従う。

この定理自体は pure glue であり、上界の供給源はここでは抽象化したままにする。
-/
theorem triominoNoWieferichBridge_of_padicValNat_le_one
    (hVal :
      ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ p ∣ (z - y) →
        Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
        padicValNat q (z ^ p - y ^ p) ≤ 1) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have hdiff_ne0 : z ^ p - y ^ p ≠ 0 := by
    have hyz_pow_lt : y ^ p < z ^ p := by
      exact Nat.pow_lt_pow_left hpack.hyz_lt hpack.hp.ne_zero
    exact Nat.sub_ne_zero_of_lt hyz_pow_lt
  intro hq2_dvd_diff
  have h2_le : 2 ≤ padicValNat q (z ^ p - y ^ p) := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hqP) (z ^ p - y ^ p) 2 hdiff_ne0).1 hq2_dvd_diff
  exact (not_le_of_gt h2_le) <|
    hVal hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap

/--
Branch B の primitive prime 文脈では、`z^p - y^p` の `q`-進付値は
`GN p (z - y) y` の `q`-進付値と一致する。

`q ∤ (z - y)` により、差の因数分解の左因子の付値が 0 になるため。
-/
theorem triominoWieferichShrink_GN_ne_zero_core
    {p x y z q : ℕ} (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hpB : ¬ p ∣ (z - y))
    (_hqP : Nat.Prime q)
    (_hq_dvd_diff : q ∣ (z ^ p - y ^ p))
    (_hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    GN p (z - y) y ≠ 0 := by
  have hgap_pos : 0 < z - y := Nat.sub_pos_of_lt hpack.hyz_lt
  exact
    GN_ne_zero_nat_of_two_le
      (d := p) (x := z - y) (u := y)
      (le_trans (by decide : 2 ≤ 5) hpack.hp5)
      hgap_pos
      hpack.y_pos

/--
Branch B の primitive prime 文脈では、`z^p - y^p` の `q`-進付値は
`GN p (z - y) y` の `q`-進付値と一致する。

`q ∤ (z - y)` により、差の因数分解の左因子の付値が 0 になるため。
-/
theorem triominoWieferichShrink_padicValNat_diff_eq_GN_core
    {p x y z q : ℕ} (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (_hq_dvd_diff : q ∣ (z ^ p - y ^ p))
    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
    padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) := by
  exact DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
    (hp2 := le_trans (by decide : 2 ≤ 5) hpack.hp5)
    (hyz := hpack.hyz_lt) (hy := hpack.y_pos) (hqP := hqP) (hq_not_dvd_gap := hq_not_dvd_gap)

/--
Honest phase-15 bridge under the explicit hypothesis that the cyclotomic factor is squarefree.

This is the usable statement-repair target behind the old false placeholder:
if `GN p (z - y) y` is squarefree, the primitive-prime valuation bound follows.
-/
theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core :
    ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ¬ p ∣ (z - y) →
      Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
      Squarefree (GN p (z - y) y) →
      padicValNat q (z ^ p - y ^ p) ≤ 1 := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap hG_sq
  have hzy_coprime : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact
    DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
      (a := z) (b := y) (d := p) (q := q)
      hpack.hp
      (le_trans (by decide : 3 ≤ 5) hpack.hp5)
      hpack.hyz_lt
      hpack.y_pos
      hzy_coprime
      hpB
      hqP
      hq_dvd_diff
      hq_not_dvd_gap
      hG_sq

/--
Phase-15 のさらに弱い honest bridge 仕様:
primitive-prime branch で、対象の `q` について `GN p (z - y) y` に 2 段 lift が起きないことだけを供給する。

`Squarefree (GN ...)` は十分条件だが、この命題は phase-15 が本質的に欲しい最小条件である。
-/
abbrev NoLift (q X : ℕ) : Prop := ¬ q ^ 2 ∣ X

/--
Phase-15 のさらに弱い honest bridge 仕様:
primitive-prime branch で、対象の `q` について `GN p (z - y) y` に 2 段 lift が起きないことだけを供給する。

`Squarefree (GN ...)` は十分条件だが、この命題は phase-15 が本質的に欲しい最小条件である。
-/
abbrev TriominoNoLiftGNBridge : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    Nat.Prime q -> q ∣ (z ^ p - y ^ p) -> ¬ q ∣ (z - y) ->
    NoLift q (GN p (z - y) y)

/--
If the primitive-prime branch supplies the direct non-lift condition `¬ q^2 ∣ GN`,
the phase-15 NoWieferich bridge closes without requiring full squarefreeness.
-/
theorem triominoNoWieferichBridge_of_not_sq_GN
    (hNoLift : TriominoNoLiftGNBridge) :
    TriominoNoWieferichBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap hq2_dvd_diff
  have hGN_ne : GN p (z - y) y ≠ 0 :=
    triominoWieferichShrink_GN_ne_zero_core
      hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have hEq :
      padicValNat q (z ^ p - y ^ p) = padicValNat q (GN p (z - y) y) :=
    triominoWieferichShrink_padicValNat_diff_eq_GN_core
      hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have h2_le_diff : 2 ≤ padicValNat q (z ^ p - y ^ p) := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hqP) (z ^ p - y ^ p) 2
      (by
        have hyz_pow_lt : y ^ p < z ^ p := by
          exact Nat.pow_lt_pow_left hpack.hyz_lt hpack.hp.ne_zero
        exact Nat.sub_ne_zero_of_lt hyz_pow_lt)).1 hq2_dvd_diff
  have h2_le_GN : 2 ≤ padicValNat q (GN p (z - y) y) := by
    rw [← hEq]
    exact h2_le_diff
  have hq2_dvd_GN : q ^ 2 ∣ GN p (z - y) y := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hqP) (GN p (z - y) y) 2 hGN_ne).2 h2_le_GN
  exact (hNoLift hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap) hq2_dvd_GN

/--
Phase-15 の honest bridge 仕様:
primitive-prime branch で cyclotomic factor `GN p (z - y) y` が squarefree であることを供給する。

この仮定があれば、false である一般 placeholder を経由せずに NoWieferich bridge を閉じられる。
-/
abbrev TriominoSquarefreeGNBridge : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ¬ p ∣ (z - y) →
    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
    Squarefree (GN p (z - y) y)

/--
If the cyclotomic factor is squarefree in the primitive-prime branch, then the direct
no-lift condition `¬ q^2 ∣ GN p (z - y) y` follows immediately.
-/
theorem triominoNoLiftGNBridge_of_squarefree_GN
    (hSq : TriominoSquarefreeGNBridge) :
    TriominoNoLiftGNBridge := by
  intro p x y z q hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  have hGN_ne : GN p (z - y) y ≠ 0 :=
    triominoWieferichShrink_GN_ne_zero_core
      hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap
  exact DkMath.NumberTheory.Gcd.not_sq_dvd_of_squarefree hqP hGN_ne
    (hSq hpack hp_not_dvd_gap hqP hq_dvd_diff hq_not_dvd_gap)

/--
If the cyclotomic factor is squarefree in the primitive-prime branch, the phase-15 NoWieferich
bridge closes without touching the false global placeholder.
-/
theorem triominoNoWieferichBridge_of_squarefree_GN
    (hSq : TriominoSquarefreeGNBridge) :
    TriominoNoWieferichBridge := by
  exact triominoNoWieferichBridge_of_not_sq_GN <|
    triominoNoLiftGNBridge_of_squarefree_GN hSq

/--
PrimeProvider 側 no-lift 仮定（`GN 3 (c-b) b`）から
`Main` が要求する `hS0_not_sq` 形へ移す wrapper。

実体は `hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3` への薄い接続で、
`cyclotomicPrimeCore = GN`（`x = c-b > 0`）を使って no-lift 仮定を移し替える。
-/
lemma hS0_not_sq_of_noLift_GN_d3 {c b : ℕ}
    (hNoLiftGN :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
        ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
      ¬ q ^ 2 ∣ DkMath.FLT.PetalDetect.S0_nat c b := by
  have hNoLiftCore :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
        ¬ q ^ 2 ∣ DkMath.CFBRC.cyclotomicPrimeCore 3 (c - b) b := by
    intro q hq hq_dvd hq_ndvd
    have hbc : b < c := by
      by_contra hbc_not
      have hcb : c ≤ b := Nat.not_lt.mp hbc_not
      have hdiff_zero : c - b = 0 := Nat.sub_eq_zero_of_le hcb
      exact hq_ndvd (hdiff_zero ▸ dvd_zero q)
    have hx : 0 < c - b := Nat.sub_pos_of_lt hbc
    have hcore_eq_GN :
        DkMath.CFBRC.cyclotomicPrimeCore 3 (c - b) b = GN 3 (c - b) b :=
      DkMath.CFBRC.cyclotomicPrimeCore_eq_GN_nat
        (p := 3) (x := c - b) (u := b) hx
    intro hq2_core
    have hq2_gn : q ^ 2 ∣ GN 3 (c - b) b := by
      rw [← hcore_eq_GN]
      exact hq2_core
    exact (hNoLiftGN hq hq_dvd hq_ndvd) hq2_gn
  intro q hq hq_dvd hq_ndvd
  exact (hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3
    (c := c) (b := b) hNoLiftCore) hq hq_dvd hq_ndvd

/--
PrimeProvider 側 squarefree 仮定（`GN 3 (c-b) b`）から
`hS0_not_sq` を得る wrapper。

`Squarefree` から `¬ q^2 ∣ GN` を引き出して
`hS0_not_sq_of_noLift_GN_d3` に渡すだけの glue。
-/
lemma hS0_not_sq_of_squarefree_GN_d3 {c b : ℕ}
    (hSq : Squarefree (GN 3 (c - b) b))
    (hGN_ne : GN 3 (c - b) b ≠ 0) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
      ¬ q ^ 2 ∣ DkMath.FLT.PetalDetect.S0_nat c b := by
  apply hS0_not_sq_of_noLift_GN_d3 (c := c) (b := b)
  intro q hq _hq_dvd _hq_ndvd
  exact DkMath.NumberTheory.Gcd.not_sq_dvd_of_squarefree hq hGN_ne hSq

end DkMath.FLT
