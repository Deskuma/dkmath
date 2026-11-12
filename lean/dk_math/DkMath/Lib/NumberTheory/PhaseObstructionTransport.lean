/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.PhaseClassPacket

#print "file: DkMath.Lib.NumberTheory.PhaseObstructionTransport"

/-!
# IRR-003: 乗法的な位相障害の輸送

単元倍と添字変更は障害を保ち、因子の積は類の積へ送られる。
GN の三項加法関係から類の加法関係を勝手に導くことはできない。
積全体が単元倍 p 乗なら全障害の積は1だが、個々が1とは限らない。
-/

namespace DkMath.Lib.NumberTheory

open scoped nonZeroDivisors

namespace IdealPowerObstruction
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {a b : R}

/-- 単元を掛けても主イデアルは変わらず、同じイデアル根を使える。 -/
def unitScale (E : IdealPowerObstruction R p a) (u : Rˣ) :
    IdealPowerObstruction R p ((u : R) * a) where
  root := E.root
  equation := by rw [Ideal.span_singleton_mul_left_unit u.isUnit]; exact E.equation

/-- 単元倍は類障害を変えない。単元自身の冪障害が消えるという意味ではない。 -/
theorem obstruction_unitScale (E : IdealPowerObstruction R p a) (u : Rˣ) :
    (E.unitScale u).obstruction = E.obstruction := rfl

/-- 因子を掛けると、記録するイデアル根も掛ける。 -/
def mul (E : IdealPowerObstruction R p a) (F : IdealPowerObstruction R p b) :
    IdealPowerObstruction R p (a * b) where
  root := E.root * F.root
  equation := by
    change Ideal.span ({a * b} : Set R) = ((E.root : Ideal R) * (F.root : Ideal R)) ^ p
    rw [← Ideal.span_singleton_mul_span_singleton, E.equation, F.equation, mul_pow]

/-- 乗法的な GN 操作は実際の類群の乗法と両立する。 -/
theorem obstruction_mul (E : IdealPowerObstruction R p a) (F : IdealPowerObstruction R p b) :
    (E.mul F).obstruction = E.obstruction * F.obstruction := map_mul ClassGroup.mk0 _ _

end IdealPowerObstruction

namespace PhaseClassPacket
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {ι κ : Type*}

/-- 位相の添字変更。特に巡回置換や位相の交換を含む。 -/
def reindex (P : PhaseClassPacket R p ι) (f : κ → ι) : PhaseClassPacket R p κ where
  factor i := P.factor (f i)
  power i := P.power (f i)

/-- 添字を変えただけなら観測する障害も同じ添字変更を受ける。 -/
theorem obstruction_reindex (P : PhaseClassPacket R p ι) (f : κ → ι) (i : κ) :
    (P.reindex f).obstruction i = P.obstruction (f i) := rfl

/-- 全位相の値の積に対応する、非零イデアル根の積。 -/
def product [Fintype ι] (P : PhaseClassPacket R p ι) :
    IdealPowerObstruction R p (∏ i, P.factor i) where
  root := ∏ i, (P.power i).root
  equation := by
    simp only [SubmonoidClass.coe_finsetProd]
    rw [← Ideal.prod_span_singleton, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => (P.power i).equation)

/-- 全位相障害の積は、積因子の障害そのもの。 -/
theorem obstruction_product [Fintype ι] (P : PhaseClassPacket R p ι) :
    P.product.obstruction = ∏ i, P.obstruction i := map_prod ClassGroup.mk0 _ _

/-- GN の積保存則が単元倍 p 乗を与える場合、全障害の積は1となる。
個々の障害消滅や、新しい State の存在は結論しない。 -/
theorem product_obstruction_eq_one [Fintype ι] (P : PhaseClassPacket R p ι) (hp : p ≠ 0)
    (u : Rˣ) (b : R) (hprod : (∏ i, P.factor i) = u * b ^ p) :
    (∏ i, P.obstruction i) = 1 := by
  rw [← P.obstruction_product]
  exact P.product.trivial_of_unit_power hp u b hprod

end PhaseClassPacket
end DkMath.Lib.NumberTheory
