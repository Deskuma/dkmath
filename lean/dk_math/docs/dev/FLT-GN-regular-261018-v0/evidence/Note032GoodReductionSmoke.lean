import DkMath.FLT.FreyFiniteKernelGoodReduction

#print "file: Note032GoodReductionSmoke"

/-! 同じSource37・同じ安定直線・同じ整数標的で、良い住所と全ての37以外の住所を検査する。 -/
namespace Note032GoodReductionSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 良い3での正式な良還元。標的非特異性の追加仮定を要求しない。 -/
theorem source37_good_at_three (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (hd : ¬ (3 : ℤ) ∣ S.a * S.b * S.c) :
    HasGoodReduction (FreyLocalReduction.LocalRing 3)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_good_at_prime (by decide) L hl hs (by decide) (by decide) hd

/-- 任意の良い奇素数q≠37でも同じ既存標的を使う。 -/
theorem source37_good_at_prime (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ 37)
    (hd : ¬ (q : ℤ) ∣ S.a * S.b * S.c) :
    HasGoodReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_good_at_prime (by decide) L hl hs hq2 hqp hd

/-- 2を含む全てのq≠37で、同じ整数標的の還元型を供給する。 -/
theorem source37_semistable_away (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ 37) :
    HasGoodReduction (FreyLocalReduction.LocalRing q)
        ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) ∨
      HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
        ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_semistable_away (by decide) L hl hs hqp

end Note032GoodReductionSmoke

#print axioms Note032GoodReductionSmoke.source37_good_at_three
#print axioms Note032GoodReductionSmoke.source37_good_at_prime
#print axioms Note032GoodReductionSmoke.source37_semistable_away
