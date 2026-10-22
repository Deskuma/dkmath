import DkMath

#print "file: RootSmokeNOTE031DyadicInertia"

/-!
# NOTE-031-003: 通常ルートから算術終点へ到達することの確認

数論の供給を含む終点と中間定理が、個別モジュールでなくDkMath入口から参照できる。
-/
#check DkMath.Lib.RepresentationTheory.ConjugateSquare.eq_id_on_line_of_conj_eq_sq
#check DkMath.Lib.NumberTheory.ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime
#check DkMath.Lib.NumberTheory.ValuationTameCharacter.exists_conjugate_pow_wild
#check DkMath.Lib.NumberTheory.EllipticDyadicWildInertia.fixed_of_wild
#check DkMath.FLT.Frey.Source.residual_exists_dyadic_conjugate_square
#check DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two
#print axioms DkMath.FLT.Frey.Source.residual_fixed_and_cofixed_at_two
