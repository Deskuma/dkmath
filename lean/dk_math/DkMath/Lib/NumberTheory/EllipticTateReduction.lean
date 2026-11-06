/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PrimePowerTateReduction
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.Lib.NumberTheory.EllipticTateReduction"

/-!
# 同じ楕円曲線の標準 Tate 加群 mod p と実際の E[p]

幾何学的な倍写像全射性から第0評価の全射性を内部供給する。
核は p 倍像であり、商は実際の E[p] と ZMod p 線形同型になる。
この mod p の次元2は全 Tate 加群の自由階数2とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra.PrimePowerTateSequence
noncomputable section
variable {K : Type*} [Field K] (E : WeierstrassCurve K) (p : ℕ)

/-- 同じ全幾何学的 Tate 点列の第0評価。 -/
def tateReduction : Tate p (Points E) →+ Torsion E p := reduction

/-- p 倍による実際の商。p 進 scalar p 倍と自然数 p 倍は同じ。 -/
abbrev TateModP := Tate p (Points E) ⧸ (nsmulAddMonoidHom p : Tate p (Points E) →+ Tate p (Points E)).range

instance tateModPModule : Module (ZMod p) (TateModP E p) :=
  QuotientAddGroup.zmodModule (fun x => ⟨x, rfl⟩)

/-- 第0評価は元の同じ Galois 点作用と可換する。 -/
theorem tateReduction_equivariant [Fact p.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : Tate p (Points E)) :
    tateReduction E p (mapLinear (pointAction E σ) x) = representation E p σ (tateReduction E p x) := rfl

variable [CharZero K] [E.IsElliptic] [Fact p.Prime]

/-- 実際の点の p 倍全射性から、互換点列を作って評価の全射性を得る。 -/
theorem tateReduction_surjective : Function.Surjective (tateReduction E p) :=
  reduction_surjective (multiplication_surjective E p (Fact.out : p.Prime).ne_zero)

/-- 商は同じ点を評価して得た実際の E[p] と加法同型。 -/
def tateModPEquiv : TateModP E p ≃+ Torsion E p :=
  quotientEquiv (multiplication_surjective E p (Fact.out : p.Prime).ne_zero)

/-- p で消える商の標準 ZMod p 作用のもとで、同じ加法同型は線形となる。 -/
def tateModPLinearEquiv : TateModP E p ≃ₗ[ZMod p] Torsion E p :=
  (tateModPEquiv E p).toLinearEquiv (fun c x => ZMod.map_smul (tateModPEquiv E p) c x)

/-- 実際の mod p 商の濃度は p²。全 Tate 加群の濃度ではない。 -/
theorem tateModP_card : Nat.card (TateModP E p) = p ^ 2 :=
  (Nat.card_congr (tateModPEquiv E p).toEquiv).trans (card_torsion_prime_sq E p)

/-- 実際の mod p 商は二次元。全 Tate 加群の自由性を仮定しない。 -/
theorem tateModP_finrank : Module.finrank (ZMod p) (TateModP E p) = 2 :=
  (tateModPLinearEquiv E p).finrank_eq.trans (finrank_torsion_prime E p)

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
