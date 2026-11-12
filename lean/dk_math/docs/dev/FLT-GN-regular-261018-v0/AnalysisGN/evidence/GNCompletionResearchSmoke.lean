import DkMath.Completion

#print "file: GNCompletionResearchSmoke"

/-! Completion公開入口の参照検証。一般恒等式と応用側の条件付き入口を区別する。 -/

#check DkMath.NumberTheory.prime_allInnerChooseDivisible_self
#check DkMath.NumberTheory.Primitive.unitSquare_body_eq
#check DkMath.NumberTheory.Primitive.mem_squarePrimeExpansion_iff
#check DkMath.NumberTheory.Primitive.dvd_primeWorldModulus_of_mem
#check DkMath.NumberTheory.Primitive.mem_primeWorldResidues_iff_supportDisjointFrom
#check DkMath.NumberTheory.Primitive.supportDisjointFrom_insert_prime_iff
#check DkMath.NumberTheory.PrimorialUniverse.finitePrimeBasis_subset_primeScalesUpTo_product
#check DkMath.NumberTheory.PrimorialUniverse.primeBasis235_subset_primeScalesUpTo_thirty
#check DkMath.NumberTheory.PrimorialUniverse.unitCoordinate_unique
#check DkMath.NumberTheory.Legendre.primeWorldResidues_eq_packetBase
#check DkMath.NumberTheory.Legendre.primeScalesUpTo_isFinitePrimeBasis
#check DkMath.NumberTheory.Legendre.gnomonPascalCell_mul_factorial
#check DkMath.NumberTheory.Legendre.coprime_squarePacketPoints_of_coprime_offset
#check DkMath.NumberTheory.Legendre.squareOffset_iff_open_oddGnomon
#check DkMath.CosmicFormulaBinom.mul_G_eq_GZ
#check DkMath.Gnomon.oddGnomon_succ
#check DkMath.Gnomon.GTail_two_one_eq_square_shell
#check DkMath.CosmicFormula.GTail_seven_six
#check DkMath.CosmicFormula.coprime_left_seven_quadratic

#check DkMath.Lib.Cosmic.completionLoan_primitive_triple
#check DkMath.Lib.NumberTheory.gcd_cofactor_completionDefect
#check DkMath.Lib.NumberTheory.prime_dvd_homogeneousCyclotomicEval_iff_order_ray
#check DkMath.NumberTheory.Legendre.legendreConjecture_iff_projectedWheelEscape_from_two
#check DkMath.NumberTheory.Legendre.legendreConjecture_iff_pascalOldBudget
#check DkMath.NumberTheory.Legendre.legendreConjecture_iff_open_oddGnomon_prime
#check DkMath.Gnomon.squareGnomonBand_eq_mul_GTail_two_one
#check DkMath.NumberTheory.PrimorialUniverse.squareBody_thirty_add_one_eq_thirtyOne_sq

-- 数値例ではなく、任意の平方殻に対する所有者の定理を利用する。
example (P : ℕ) : DkMath.NumberTheory.Primitive.squareBody P + 1 = (P + 1) ^ 2 :=
  DkMath.NumberTheory.Primitive.squareBody_add_one_eq P

example (x : ℕ) : x ^ 2 + DkMath.Gnomon.oddGnomon x = (x + 1) ^ 2 :=
  DkMath.Gnomon.square_add_oddGnomon x
