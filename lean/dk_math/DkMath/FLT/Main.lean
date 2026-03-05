/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

-- no-import DkMath.FLT.Basic 依存しないように外す
import DkMath.FLT.PetalDetect
import DkMath.FLT.OctagonCore
import DkMath.FLT.PhaseLift
import DkMath.FLT.CounterexamplePattern
import DkMath.FLT.GEisensteinBridge
import DkMath.NumberTheory.GcdNext
import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.ABC.PadicValNat
import DkMath.Algebra.DiffPow

#print "file: DkMath.FLT.Main"  --  (別解：Zsigmondy + padicValNat)

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# FLT Main: 別解による形式化証明

**ファイル位置づけ:**
```
理論モジュール (Basic, CosmicFormula, ZsigmondyCyclotomic, ...)
        ↓
    Core.lean     （基本補題：Cosmic Formula の因数分解）
        ↓
    Basic.lean    （FLT d=3 の既存証明）
        ↓
    Main.lean     （別解：Zsigmondy層A + PetalDetect層B）
```

**目的:**
- わっちたちの成果（Zsigmondy原始素因子 + padicValNat上界）による FLT d=3 の別解を形式化
- 既存の Cosmic Formula + coprimality アプローチとは異なる p-adic値評価による証明戦略
- 一般化への展開（d ≥ 5）への基盤構築

**証明方針（3層統合）:**

1. **層A（Zsigmondy原始素因子）**: ZsigmondyCyclotomic.leanの既存補題を活用
   - 原始素因子 q の存在保証
   - q ∤ (a-b) の条件

2. **層B（PetalDetect + padicValNat評価）**: PetalDetect.leanの既存補題を活用
   - S0(a,b) = a²+ab+b²the相対多角数構造
   - (a+b)割り切り検出による φビット判定
   - padicValNat上界 v_q(a³-b³) ≤ 1

3. **矛盾導出**: 層AとBの統合
   - 層A: v_q(a³-b³) ≥ 3（完全3乗仮定）
   - 層B: v_q(a³-b³) ≤ 1（padicValNat上界）
   - 矛盾: 3 ≤ 1
-/

namespace DkMath.FLT

open scoped BigOperators
open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.GcdNext
open DkMath.ABC
open DkMath.Algebra.DiffPow

/--
`descentClassify` だけを使う下流定理へ接続するための最小内部 bundle。

公開入口は `GEisensteinBaseInput` 側へ寄せ、こちらは内部の compatibility layer として扱う。
-/
structure DescentBaseInput (c b : ℕ) where
  hbc : b < c
  hcb_coprime : Nat.Coprime c b
  hDescentClass : DescentClassifyImpossibleOnPrimitive c b

/--
`GEisensteinBaseInput` から、最小の `descentClassify` 束を回収する内部変換。
-/
def GEisensteinBaseInput.toDescentBaseInput {c b : ℕ}
    (hIn : GEisensteinBaseInput c b) :
    DescentBaseInput c b where
  hbc := hIn.hbc
  hcb_coprime := hIn.hcb_coprime
  hDescentClass := descentClassifyImpossibleOnPrimitive_of_GEisensteinCore hIn.hCore

/--
`GEisensteinDescentCore` から `DescentBaseInput` を組み立てる内部 constructor。

`DescentBaseInput.hDescentClass` は、今後はこの constructor を経由して
`GEisenstein` 側の descent kernel から供給するのを標準ルートとみなす。
-/
def DescentBaseInput.ofGEisensteinCore {c b : ℕ}
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hCore : GEisensteinDescentCore c b) :
    DescentBaseInput c b := by
  exact (GEisensteinBaseInput.mk hbc hcb_coprime hCore).toDescentBaseInput

-- ========================================
-- § 1. 層A（Zsigmondy原始素因子）
-- ========================================

-- ========================================
-- § 3. 矛盾導出（層A + 層B統合）
-- ========================================

section CoreRoute

/-- **メイン定理：別解による FLT d=3 証明**

Zsigmondy原始素因子 + padicValNat評価による背理法：
平方自由性仮定の下で、完全3乗仮定と矛盾を導出。

**入力（仮定）:**
- `ha : 0 < a`, `hb : 0 < b`, `hc : 0 < c` - 正の整数
- `hab : Nat.Coprime a b` - a と b は互いに素
- `hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c^3 - b^3 → ¬ q ∣ c - b → ¬ q² ∣ S0_nat c b`
  - 相対多角数S0(c,b) = c²+cb+b² は各原始素因子 q に対して平方自由
  - すなわち：q が c³-b³ を割り、かつ q が (c-b) を割らない任意の素数 q について、
    q² は S0(c,b) を割らない

**証明戦略（層統合）:**

1. **層A（Zsigmondy原始素因子）**
   - 存在補題により、q | (c³-b³) かつ ¬ q | (c-b) を満たす素数 q が存在

2. **層B（padicValNat上界）**
   - 仮定 hS0_not_sq から ¬ q² ∣ S0(c,b)
   - padicValNat上界：v_q(c³-b³) ≤ 1

3. **矛盾導出**
   - 完全3乗仮定：q | a より v_q(a³-b³) ≥ 3
   - 層B下界：v_q(c³-b³) = v_q(a³-b³)（cube_sub_eq_of_add_eq より）
   - 矛盾：3 ≤ v_q(c³-b³) ≤ 1

**出力（結論):**
`a³ + b³ ≠ c³`（FLT d=3）
-/
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro h_eq

  have hcop_cb : Nat.Coprime c b := coprime_cb_of_eq hab h_eq
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hc3_le : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hcb 3
    have hsum_le : a ^ 3 + b ^ 3 ≤ b ^ 3 := by simpa [h_eq] using hc3_le
    have ha3_pos : 0 < a ^ 3 := by positivity
    omega

  obtain ⟨q, hq_prime, hq_dvd_diff, hq_ndiv_diff⟩ :=
    exists_prime_factor_cube_diff hbc hb hcop_cb

  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq h_eq
  have hq_dvd_a3 : q ∣ a ^ 3 := by simpa [hsub] using hq_dvd_diff
  have hq_dvd_a : q ∣ a := hq_prime.dvd_of_dvd_pow hq_dvd_a3

  have h_lower_a3 : 3 ≤ padicValNat q (a ^ 3) :=
    padicValNat_lower_bound_of_dvd_d3 ha hq_prime hq_dvd_a
  have h_lower : 3 ≤ padicValNat q (c ^ 3 - b ^ 3) := by
    simpa [hsub] using h_lower_a3

  have h_upper : padicValNat q (c ^ 3 - b ^ 3) ≤ 1 :=
    padicValNat_upper_bound_d3 hbc hc hb hq_prime hq_dvd_diff hq_ndiv_diff
      (hS0_not_sq hq_prime hq_dvd_diff hq_ndiv_diff)

  have : (3 : ℕ) ≤ 1 := le_trans h_lower h_upper
  omega

/--
`NoSqOnS0 c b` を入力にした `FLT_d3_by_padicValNat` の派生版。

`Main` 内の NoSq 系 canonical entry。
以後の adapter 群は、最終的にこの定理へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_NoSqOnS0 {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNoSq : NoSqOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  apply FLT_d3_by_padicValNat ha hb hc hab
  intro q hq hq_dvd_diff hq_ndiv_diff
  exact hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff

end CoreRoute

section NoSqRecoveryAdapters

/--
phase-04: 非例外調和条件（skeleton）から
`AllNonLiftableOnS0` -> `NoSqOnS0` を経由して供給する版。
-/
theorem FLT_d3_by_padicValNat_of_nonExceptionalHarmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNH : NonExceptionalHarmonicOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hAll : AllNonLiftableOnS0 c b :=
    AllNonLiftableOnS0_of_nonExceptionalHarmonic hNH
  have hNoSq : NoSqOnS0 c b := NoSqOnS0_of_AllNonLiftableOnS0 hAll
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab
    hNoSq

/--
phase-04: `ExceptThree + mod3分離 + harmonic witness` から
`NoSqOnS0` を経由して供給する版。
現在は互換レイヤー（推奨は `..._coprime` 系）。
-/
theorem FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_exceptThree_mod3_separated_harmonic
      hHarm hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
phase-08: `hSuppEx3 + hNonLift + mod3分離` から
`NoSqOnS0` を直接回復して供給する版。
現在は互換レイヤー（推奨は `..._coprime` 系）。
-/
theorem FLT_d3_by_padicValNat_of_support_nonLiftable_mod3_separated {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_support_nonLiftable_mod3_separated
      hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
`hNonLift` と `coprime(c,b)` から `NoSqOnS0` を回復して供給する版。
`mod3` 分離仮定を使わない。
-/
theorem FLT_d3_by_padicValNat_of_support_nonLiftable_coprime {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b ≤ c)
    (hcb_coprime : Nat.Coprime c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_support_nonLiftable_coprime hbc hcb_coprime hNonLift
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
`hNonLiftAll` と `coprime(c,b)` から直接供給する共通入口。

`NoSqOnS0` を直接持たない場合の canonical recovery point。
`nonLiftable` family から `NoSqOnS0` を回復する役をこの定理に集約する。
-/
theorem FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_support_nonLiftable_coprime
    ha hb hc hab hbc.le hcb_coprime hNonLiftAll

/--
phase-08: `NoSqOnS0` を分岐軸にした A+B 合流版。
- A: `NoSqOnS0 c b` なら `...of_NoSqOnS0`
- B: `¬ NoSqOnS0 c b` でも `coprime(c,b) + hNonLift` から供給可能
-/
theorem FLT_d3_by_padicValNat_by_cases_NoSq {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b ≤ c)
    (hcb_coprime : Nat.Coprime c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  by_cases hNoSq : NoSqOnS0 c b
  · exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq
  · exact FLT_d3_by_padicValNat_of_support_nonLiftable_coprime
      ha hb hc hab hbc hcb_coprime hNonLift

/--
phase-04: `harmonic envelope + nonLiftable family` から
`AllNonLiftableOnS0` を経由して供給する版。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hAll : AllNonLiftableOnS0 c b :=
    allNonLiftableOnS0_of_harmonicEnvelope_nonLiftable hbc
      hasPhaseUnitInfrastructure hHarm hNoExcAll
      hSuppEx3 hNonLiftAll hc_nz hb_nz hsep
  have hNoSq : NoSqOnS0 c b := NoSqOnS0_of_AllNonLiftableOnS0 hAll
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
phase-05: `hSuppEx3` を `Coprime c b` から自動生成して
`harmonicEnvelope_nonLiftable` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport
    ha hb hc hab hbc hcb_coprime hNonLiftAll

end NoSqRecoveryAdapters

section DescentAdapters

/--
phase-05: `classifyLift = impossible` family から `hNonLiftAll` を生成して
`harmonicEnvelope_nonLiftable_coprimeSupport` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hClassPrim :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible)
    :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_classifyLift_impossible hbc hClassPrim
  exact FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport
    ha hb hc hab hbc hcb_coprime hNonLiftAll

/--
phase-10 橋渡し入口:
下降法側から `PrimitiveOnS0 -> classifyLift = impossible` を供給できれば、
`NonLiftable` 経由で FLT 入口に接続できる。

descent 系の canonical bridge。
`DescentClassifyImpossibleOnPrimitive` を `nonLiftable` family へ落とし、
そこから先は NoSq recovery 側へ委譲する。
-/
theorem FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hDescentClass : DescentClassifyImpossibleOnPrimitive c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_descentClassify hbc hDescentClass
  exact FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport
    ha hb hc hab hbc hcb_coprime hNonLiftAll

/--
phase-11 入口:
`PrimitiveOnS0` 上の strict descent ステップを与え、
`NoSq` 仮定なしで `GEisenstein` kernel を組み立てて接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_descentStep_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  let hCore : GEisensteinDescentCore c b :=
    GEisensteinDescentCore_of_harmonicEnvelope_descentStep
      hbc hInfra hHarm hNoExcAll hStep
  let hIn : GEisensteinBaseInput c b := {
    hbc := hbc
    hcb_coprime := hcb_coprime
    hCore := hCore
  }
  exact FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport
    ha hb hc hab hIn.hbc hIn.hcb_coprime hIn.toDescentBaseInput.hDescentClass

/--
phase-11 直結入口:
`strict descent + coprime(c,b)` から `NoSqOnS0` を回復して接続する。
-/
theorem FLT_d3_by_padicValNat_of_descentStep_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_descentStep_coprime hbc.le hcb_coprime hStep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
phase-11 入口（engine 入力版）:
strict descent を構造体で受け取り、`GEisenstein` kernel 経由で接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_descentEngine_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  let hCore : GEisensteinDescentCore c b :=
    GEisensteinDescentCore_of_harmonicEnvelope_descentEngine
      hbc hInfra hHarm hNoExcAll hEngine
  let hIn : GEisensteinBaseInput c b := {
    hbc := hbc
    hcb_coprime := hcb_coprime
    hCore := hCore
  }
  exact FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport
    ha hb hc hab hIn.hbc hIn.hcb_coprime hIn.toDescentBaseInput.hDescentClass

/--
phase-11 直結入口（engine 版）:
`descent engine + coprime(c,b)` から `NoSqOnS0` を回復して接続する。
-/
theorem FLT_d3_by_padicValNat_of_descentEngine_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_descentEngine_coprime hbc.le hcb_coprime hEngine
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

end DescentAdapters

section ProviderCompatibility

/--
phase-11 直結入口（reduce 版）:
局所縮小関数 `reduce` から `NoSqOnS0` を回復して接続する。
-/
theorem FLT_d3_by_padicValNat_of_reduce_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_reduce_coprime hbc.le hcb_coprime reduce
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
phase-11 最小 reduce 実装確認:
`step` から `reduce` を生成して、reduce 直結入口へ流す。
-/
theorem FLT_d3_by_padicValNat_of_step_via_reduce_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_reduce_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime
    (primitiveSquareReduce_of_step hStep)

/--
`reduce` 候補（数論系）を直接刺す入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryReduce_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduceNT : NumberTheoryReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_reduce_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime reduceNT

/--
`reduce` 候補（トロミノ/幾何系）を直接刺す入口。
-/
theorem FLT_d3_by_padicValNat_of_trominoReduce_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduceGeom : TrominoReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_reduce_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime reduceGeom

/--
数論系ルート専用入口:
`PrimitiveSquareDescentStep` を数論 `reduce` として解釈し、
`numberTheoryReduce` 直結入口へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStep_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_numberTheoryReduce_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime (numberTheoryReduce_of_step hStep)

/--
数論系最小実装（`numberTheoryReduce_basic`）を使う入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryReduce_basic_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_numberTheoryReduce_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime (numberTheoryReduce_basic hStep)

/--
数論状態遷移仕様 `StepExists`（global）から直接接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStepExists_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hex : NumberTheoryDescentState.StepExists) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryStepExists_coprime hex hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
固定 `(c,b)` の数論状態遷移仕様 `StepExists` から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStepExistsOn_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hex : NumberTheoryDescentOn.StepExists c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b := by
    exact NoSqOnS0_of_numberTheoryHasKernel_coprime
      (numberTheoryHasKernel_of_stepExistsOn hbc hcb_coprime hex)
      hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
固定 `(c,b)` の数論 `step` から、`StepExistsOn` 経由で接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStepOn_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b := by
    exact NoSqOnS0_of_numberTheoryHasKernel_coprime
      (numberTheoryHasKernel_of_step hStep) hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
固定 `(c,b)` の数論 `reduce` から、`StepExistsOn` 経由で接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryReduceOn_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduceNT : NumberTheoryReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b := by
    exact NoSqOnS0_of_numberTheoryHasKernel_coprime
      (numberTheoryHasKernel_of_reduce reduceNT) hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
固定 `(c,b)` の数論 `ReductionKernel` から、`StepExistsOn` 経由で接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryKernel_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (ker : NumberTheoryDescentOn.ReductionKernel c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b := by
    exact NoSqOnS0_of_numberTheoryHasKernel_coprime ⟨ker⟩ hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
固定 `(c,b)` の数論 kernel の存在だけを受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasKernel_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  rcases hker with ⟨ker⟩
  exact FLT_d3_by_padicValNat_of_numberTheoryKernel_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime ker

/--
数論 kernel provider（全 `(c,b)` 供給）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryKernelProvider_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (prov : NumberTheoryKernelProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryKernelProvider prov hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 kernel family（全 `(c,b)` で `ReductionKernel` 存在）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasKernelFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasKernel :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasKernelFamily hbc hcb_coprime hasKernel
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 step provider（全 `(c,b)` で `PrimitiveSquareDescentStep` 供給）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStepProvider_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (provStep : NumberTheoryStepProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryStepProvider provStep hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 step family（全 `(c,b)` で `PrimitiveSquareDescentStep` 供給）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasStepFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasStep :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        PrimitiveSquareDescentStep c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasStepFamily hbc hcb_coprime hasStep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 reduce provider（全 `(c,b)` で `NumberTheoryReduce` 供給）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryReduceProvider_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (provReduce : NumberTheoryReduceProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryReduceProvider provReduce hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 reduce family（全 `(c,b)` で `NumberTheoryReduce` 供給）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasReduceFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasReduceFamily hbc hcb_coprime hasReduce
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 stepExists provider（全 `(c,b)` で `StepExistsOn` 供給）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryStepExistsProvider_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (provExists : NumberTheoryStepExistsProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryStepExistsProvider provExists hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 stepExists family（全 `(c,b)` で `StepExistsOn` 供給）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasStepExistsFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasStepExists :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.StepExists c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasStepExistsFamily hbc hcb_coprime hasStepExists
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 localReduce provider（全 `(c,b)` で `LocalReduce` 供給）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryLocalReduceProvider_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (provLocal : NumberTheoryLocalReduceProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryLocalReduceProvider provLocal hbc hcb_coprime
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 localReduce family（全 `(c,b)` で `LocalReduce` 供給）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasLocalReduceFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasLocalReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.LocalReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasLocalReduceFamily hbc hcb_coprime hasLocalReduce
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 nonLiftable family（全 `(c,b,q)` で `NonLiftableS0`）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasNonLiftableFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNonLift :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasNonLiftableFamily hbc hcb_coprime hasNonLift
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
数論 NoSq family（全 `(c,b)` で `NoSqOnS0`）を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryHasNoSqFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNoSq :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_numberTheoryHasNoSqFamily hbc hcb_coprime hasNoSq
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
トロミノ系 `NoSq` family（全 `(c,b)`）から接続する入口。
`TriominoFLT` 側で `hasNoSq` を構成したら、この入口にそのまま接続する。
-/
theorem FLT_d3_by_padicValNat_of_triominoHasNoSqFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNoSqTriomino :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_numberTheoryHasNoSqFamily_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime hasNoSqTriomino

/--
トロミノ系 `NonLiftable` family（全 `(c,b,q)`）から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_triominoHasNonLiftableFamily_coprimeSupport_direct
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hasNonLiftTriomino :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        ∀ q : ℕ, NonLiftableS0 c b q) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_numberTheoryHasNonLiftableFamily_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime hasNonLiftTriomino

/--
固定 `(c,b)` の数論ローカル降下入力 (`LocalReduce`) から接続する入口。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryLocalReduceOn_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduce : NumberTheoryDescentOn.LocalReduce c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_numberTheoryHasKernel_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime
    (numberTheoryHasKernel_of_localReduce hbc hcb_coprime reduce)

/--
互換入口:
旧 global 版 `LocalReduce` を受ける場合は従来の global `StepExists` 入口に委譲する。
-/
theorem FLT_d3_by_padicValNat_of_numberTheoryLocalReduce_coprimeSupport_direct {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (reduce : NumberTheoryDescentState.LocalReduce) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hex : NumberTheoryDescentState.StepExists :=
    NumberTheoryDescentState.stepExists_of_localReduce reduce
  exact FLT_d3_by_padicValNat_of_numberTheoryStepExists_coprimeSupport_direct
    ha hb hc hab hbc hcb_coprime hex

end ProviderCompatibility

section DescentBridgeAdapters

/--
GEisenstein 下降法コア述語を直接受ける入口。
-/
theorem FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hGECore : GEisensteinDescentCore c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  let hIn : GEisensteinBaseInput c b := {
    hbc := hbc
    hcb_coprime := hcb_coprime
    hCore := hGECore
  }
  exact FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport
    ha hb hc hab hIn.hbc hIn.hcb_coprime hIn.toDescentBaseInput.hDescentClass

/--
`GEisensteinCore` に加えて停止到達情報を受け取る補助版。
現段階では `core` 版に委譲し、到達情報は将来拡張の受け口として保持する。
-/
theorem FLT_d3_by_padicValNat_of_GEisensteinCore_with_reachability_coprimeSupport
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hGECore : GEisensteinDescentCore c b)
    (_hReach :
      ∀ s : hGECore.frame.State,
        ∃ n : ℕ,
          hGECore.frame.measure (GEisensteinDescentFrame.descend hGECore.frame s n) = 0) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_GEisensteinCore_coprimeSupport
    ha hb hc hab hbc hcb_coprime hGECore

/--
`GEisenstein_descent_reaches_zero_of_core` を使って
reachability 受け口付き定理へ接続するラッパー。
-/
theorem FLT_d3_by_padicValNat_of_GEisensteinCore_via_reachability_coprimeSupport
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hGECore : GEisensteinDescentCore c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hReach :
      ∀ s : hGECore.frame.State,
        ∃ n : ℕ,
          hGECore.frame.measure (GEisensteinDescentFrame.descend hGECore.frame s n) = 0 := by
    intro s
    exact GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred hGECore s
  exact FLT_d3_by_padicValNat_of_GEisensteinCore_with_reachability_coprimeSupport
    ha hb hc hab hbc hcb_coprime hGECore hReach

/--
`GEisensteinDescentCore` から、任意初期状態での停止到達（`measure = 0`）を取り出す API。
-/
theorem GEisenstein_descent_reaches_zero_of_core {c b : ℕ}
    (hCore : GEisensteinDescentCore c b)
    (s : hCore.frame.State) :
    ∃ n : ℕ,
      hCore.frame.measure (GEisensteinDescentFrame.descend hCore.frame s n) = 0 := by
  exact GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred hCore s

/--
`primitiveSized` 非empty core 橋の公開 API 版。
-/
theorem GEisenstein_descent_reaches_zero_of_descentClassify_primitiveSized
    {c b q size : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b)
    (hPrim : PrimitiveOnS0 c b q)
    (hsize : size ≤ q) :
    ∃ n : ℕ,
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend
          (primitiveSizedCandidateGEisensteinDescentFrame c b)
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize)
          n) = 0 := by
  exact exists_descend_measure_eq_zero_of_descentClassify_primitiveSized
    hDescent hPrim size hsize

/--
`DescentBaseInput` を入口にした薄いラッパー。

`descentClassify` だけを持つ内部 compatibility entry。
公開の canonical entry は後段の `FLT_d3_by_padicValNat_of_GEisensteinBaseInput` とする。
-/
theorem FLT_d3_by_padicValNat_of_DescentBaseInput {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hIn : DescentBaseInput c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_descentClassify_coprimeSupport
    ha hb hc hab hIn.hbc hIn.hcb_coprime hIn.hDescentClass

/--
`GEisensteinBaseInput` を入口にした public canonical entry。

本件で「どの仮定を証明しに行くか」を追うときの基準点は、この定理の
入力束 `GEisensteinBaseInput` である。
-/
theorem FLT_d3_by_padicValNat_of_GEisensteinBaseInput {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hIn : GEisensteinBaseInput c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_DescentBaseInput
    ha hb hc hab hIn.toDescentBaseInput

/--
`GEisensteinBaseInputProvider` から公開 canonical entry へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_GEisensteinBaseInputProvider {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (prov : GEisensteinBaseInputProvider) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_of_GEisensteinBaseInput
    ha hb hc hab (prov.hasBaseInput hbc hcb_coprime)

/--
phase-05: `NoSqOnS0` から classification impossible family を自動生成し、
`harmonicEnvelope_classify_coprimeSupport` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hNoSq : NoSqOnS0 c b)
    :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hGECore : GEisensteinDescentCore c b := by
    exact GEisensteinDescentCore_of_descentClassify
      (descentClassifyImpossibleOnPrimitive_via_GEisenstein
        hbc hasPhaseUnitInfrastructure hHarm hNoExcAll hNoSq)
  exact FLT_d3_by_padicValNat_of_GEisensteinCore_via_reachability_coprimeSupport
    ha hb hc hab hbc hcb_coprime hGECore

end DescentBridgeAdapters

section CompatibilityInputs

/--
`NoSqBaseInput` から A+B 合流定理へ直結する薄いラッパー。
`mod3` 分離を要求せず、`coprime(c,b)` で供給する。
-/
theorem FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hIn : NoSqBaseInput c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  exact FLT_d3_by_padicValNat_by_cases_NoSq
    ha hb hc hab hIn.hbc.le hIn.hcb_coprime hIn.hNonLift

/--
`NoSqInput` を入口にして `NoSq` ルートへ接続する版。
`hNoExcAll` は互換性のため受け取り、実装は合流ラッパーに委譲。
-/
theorem FLT_d3_by_padicValNat_of_NoSqInput {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hIn : NoSqInput c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hBase : NoSqBaseInput c b := {
    hbc := hIn.hbc
    hcb_coprime := hIn.hcb_coprime
    hHarm := hIn.hHarm
    hNonLift := nonLiftableS0_all_of_NoSqOnS0 hIn.hNoSq
  }
  exact FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput
    ha hb hc hab hBase

/--
`CounterexamplePattern.classifyLift` を経由して `hS0_not_sq` を供給する版。
-/
theorem FLT_d3_by_padicValNat_of_classifyLift {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hClassify :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  apply FLT_d3_by_padicValNat ha hb hc hab
  intro q hq hq_dvd_diff hq_ndiv_diff
  let x : CounterexampleInput := { c := c, b := b, q := q }
  have hprim : primitivePrimeGate x := by
    exact ⟨hq, hq_dvd_diff, hq_ndiv_diff⟩
  have hcls : classifyLift x = LiftStatus.impossible := by
    simpa [x] using hClassify hq hq_dvd_diff hq_ndiv_diff
  have hnosq : noSquareGate x :=
    noSquareGate_of_classifyLift_impossible hprim hcls
  simpa [x, noSquareGate] using hnosq

end CompatibilityInputs

section DefinitionalEqualities

/-- FLT_d3_by_padicValNat_of_NoSqOnS0 と FLT_d3_by_padicValNat は等価である -/
example
  {a b c : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.Coprime a b)
  (hNoSq : NoSqOnS0 c b) :
  FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq =
    let hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b :=
      (fun hq hq_dvd_diff hq_ndiv_diff => hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff)
    FLT_d3_by_padicValNat ha hb hc hab hS0_not_sq := by rfl

/-- `FLT_d3_by_padicValNat_of_NoSqOnS0` は `FLT_d3_by_padicValNat` に
`hS0_not_sq_of_NoSqOnS0` を差し込んだものと定義的に同一。 -/
lemma FLT_d3_by_padicValNat_of_NoSqOnS0_eq
  {a b c : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.Coprime a b)
  (hNoSq : NoSqOnS0 c b) :
  FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq
    =
    (let hS0_not_sq :
        ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b :=
        fun hq hq_dvd_diff hq_ndiv_diff =>
          hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff;
     FLT_d3_by_padicValNat ha hb hc hab hS0_not_sq) := by
  rfl

end DefinitionalEqualities

end DkMath.FLT
