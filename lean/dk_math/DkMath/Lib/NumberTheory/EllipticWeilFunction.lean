/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_WeilPairingFun.lean.
Upstream blob: 87db2103488123818b08bf0d9302badff87ac510
Modified for DkMath: require nonzero index and proved torsion condition; remove fallback branches and prove nonzero numerator/quotient.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationFiber
import DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal

#print "file: DkMath.Lib.NumberTheory.EllipticWeilFunction"

/-!
# ファイバーイデアルの主性とWeil関数の候補

ファイバーの総和=nTという点群の定理を、Point.toClassによって
イデアルの積の主性へ翻訳する。nT=0のとき、その非零生成元fを選ぶ。
零点Oのファイバーの生成元を分母としてf(n,T)/f(n,O)を実際の関数体内に構成する。
有限性・主性が不明な場合を1で埋めず、非零指数とtorsion条件を明示したAPIにする。
生成元は単元倍の不定性を持つ非標準的な選択であり、正規化された座標式ではない。
付値公式、平行移動での比例性、Weil対の双加法性・同変性・非退化性はまだ主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

open Classical in
/-- 同じファイバーの有限点イデアルの積。Oの寄与は単位イデアルなので、Oを除いた積に等しい。 -/
noncomputable def fiberIdeal (n : ℕ) (hn : n ≠ 0) (T : Points E) :
    Ideal (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing :=
  ∏ P ∈ (fiber_finite E n hn T).toFinset, pointIdeal P

open Classical in
/-- ファイバーイデアルは非零。空積の場合にも単位イデアルなので非零である。 -/
theorem fiberIdeal_ne_bot (n : ℕ) (hn : n ≠ 0) (T : Points E) : fiberIdeal E n hn T ≠ ⊥ :=
  prod_pointIdeal_ne_bot _ id

open Classical in
/-- 主性の正確な判定。任意の目標点Tについて、積が主になるのはnT=0のときに限る。 -/
theorem fiberIdeal_isPrincipal_iff (n : ℕ) (hn : n ≠ 0) (T : Points E) :
    (fiberIdeal E n hn T).IsPrincipal ↔ n • T = 0 := by
  have h := isPrincipal_prod_pointIdeal_iff
    (W := E.toAffine⁄(AlgebraicClosure K)) (fiber_finite E n hn T).toFinset
    (fun P : Points E => P)
  apply h.trans
  change (∑ P ∈ (fiber_finite E n hn T).toFinset, P) = (0 : Points E) ↔ n • T = 0
  rw [sum_fiber E n hn T]

open Classical in
/-- torsion条件から実際の整イデアルの主性を供給する。類群の消滅を仮定しない。 -/
theorem fiberIdeal_isPrincipal (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    (fiberIdeal E n hn T).IsPrincipal :=
  (fiberIdeal_isPrincipal_iff E n hn T).mpr hT

open Classical in
/-- 主イデアルの生成元として選ぶWeil分子。幾何学的なtorsion条件を入力として保持する。 -/
noncomputable def weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing := by
  have := fiberIdeal_isPrincipal E n hn T hT
  exact Submodule.IsPrincipal.generator (fiberIdeal E n hn T)

open Classical in
/-- 選んだ分子が生成するイデアルは、実際のファイバーイデアルそのものである。 -/
theorem span_weilNumerator (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    Ideal.span {weilNumerator E n hn T hT} = fiberIdeal E n hn T := by
  have := fiberIdeal_isPrincipal E n hn T hT
  exact Ideal.span_singleton_generator _

open Classical in
/-- ファイバーイデアルの非零性により、選んだ生成元も非零となる。 -/
theorem weilNumerator_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    weilNumerator E n hn T hT ≠ 0 := by
  intro h
  have hs := span_weilNumerator E n hn T hT
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hs
  exact fiberIdeal_ne_bot E n hn T hs.symm

open Classical in
/-- 座標環の生成元の非零性を、同じ関数体への包含で保つ。 -/
theorem algebraMap_weilNumerator_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField (weilNumerator E n hn T hT) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField).ne (weilNumerator_ne_zero E n hn T hT)

open Classical in
/-- Weil関数の候補w(n,T)=f(n,T)/f(n,O)。分子・分母ともに同じ座標環から来る。
この定義だけで平行移動の比例定数やWeil対を得たとは解釈しない。 -/
noncomputable def weilFunction (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  algebraMap _ _ (weilNumerator E n hn T hT) /
    algebraMap _ _ (weilNumerator E n hn 0 (smul_zero n))

open Classical in
/-- 実際の関数体内の商は非零である。分母が零でないことを証明から供給する。 -/
theorem weilFunction_ne_zero (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    weilFunction E n hn T hT ≠ 0 :=
  div_ne_zero (algebraMap_weilNumerator_ne_zero E n hn T hT)
    (algebraMap_weilNumerator_ne_zero E n hn 0 (smul_zero n))

open Classical in
/-- 零点を目標にしたときは同じ非零分子同士の商となり、候補関数は1に正規化される。 -/
theorem weilFunction_zero (n : ℕ) (hn : n ≠ 0) :
    weilFunction E n hn 0 (smul_zero n) = 1 :=
  div_self (algebraMap_weilNumerator_ne_zero E n hn 0 (smul_zero n))

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
