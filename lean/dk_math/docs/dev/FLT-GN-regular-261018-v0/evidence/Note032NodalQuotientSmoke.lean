import DkMath.FLT.FreyFiniteKernelNodalReduction

#print "file: Note032NodalQuotientSmoke"

/-! Source37の同じ既存整数標的。局所核の側・住所・中心・方向のproviderを公開終点に残さない。 -/
namespace Note032NodalQuotientSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 同じSource37の整数標的は、局所分岐の入力なしで2で乗法的還元を持つ。 -/
theorem source37_multiplicative_at_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing 2)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_multiplicative_at_two (by decide) L hl hs

/-- 悪い3上でも、同じ整数標的の乗法的還元をDisjoint仮定なしで得る。 -/
theorem source37_multiplicative_at_bad_three (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (hbad : (3:ℤ) ∣ S.a * S.b * S.c) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing 3)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_multiplicative_at_bad_prime (by decide) L hl hs (by decide) (by decide) hbad

/-- 任意の悪い奇素数q≠37について、同じ既存標的への正式な還元保持。 -/
theorem source37_multiplicative_at_bad_prime (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q:ℕ} [Fact q.Prime] (hq2:q≠2) (hqp:q≠37) (hbad:(q:ℤ)∣S.a*S.b*S.c) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_multiplicative_at_bad_prime (by decide) L hl hs hq2 hqp hbad

/-- 2とabc支持を一つの入口で扱う。良い素数場所への結論は追加しない。 -/
theorem source37_multiplicative_at_bad_place (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q:ℕ} [Fact q.Prime] (hqp:q≠37) (hbad:q=2 ∨ (q:ℤ)∣S.a*S.b*S.c) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_multiplicative_at_bad_place (by decide) L hl hs hqp hbad

end Note032NodalQuotientSmoke
