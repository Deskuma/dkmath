import DkMath.FLT.FreyFiniteKernelZeroComponent

#print "file: Note032ZeroComponentSmoke"

/-! 同じSource37・同じ残余直線・同じ付値環標的で、無限遠近傍と特異核側を検査する。 -/
namespace Note032ZeroComponentSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open EllipticGoodReductionSeparation ValuationInertia
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 2を除外しない任意のq≠37で、同じ実点準同型が無限遠近傍を保つ。 -/
theorem source37_formal (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ 37)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (P : Points S.rationalCurve) (hx : P.xc ∉ A) :
    (S.residualOddKernelPointHom (by decide) L hl P).xc ∉ A :=
  S.residual_pointHom_x_not_mem (by decide) L hl hq hqp A hA P hx

/-- 悪い奇素数の特異核側で、全零成分の像を同じ付値環標的へ輸送する。 -/
theorem source37_singular_kernel (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ 37)
    (hbad : (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Fact.out hqp A hA)
      (S.residualOddKernelPointHom (by decide) L hl P) :=
  S.residual_pointHom_smooth_at_bad_prime_of_disjoint (by decide) L hl hq2 hqp hbad A hA hd P hP

/-- 2進場所でも同じ特異核の条件を保ち、Source37の全零成分を運ぶ。 -/
theorem source37_singular_kernel_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hd : Disjoint L (S.residualZeroComponent A)) (P : Points S.rationalCurve)
    (hP : HasSmoothReduction (S.valuationModel A) P) :
    HasSmoothReduction (S.residualValuationKernelModel L hl Nat.prime_two (by decide) A hA)
      (S.residualOddKernelPointHom (by decide) L hl P) :=
  S.residual_pointHom_smooth_at_two_of_disjoint (by decide) L hl A hA hd P hP

end Note032ZeroComponentSmoke

#print axioms Note032ZeroComponentSmoke.source37_formal
#print axioms Note032ZeroComponentSmoke.source37_singular_kernel
#print axioms Note032ZeroComponentSmoke.source37_singular_kernel_two
