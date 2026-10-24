import DkMath.Lib.Cosmic.Completion

#print "file: GNCompletionPublicSmoke"

/-! Six-layer public API smoke: one theorem from every direct owner. -/

#check DkMath.CosmicFormula.add_pow_eq_prefix_add_xpow_mul_GTail
#check DkMath.NumberTheory.GapFocusing.GN_succ_right
#check DkMath.NumberTheory.GapFocusing.dvd_anchor_pow_of_dvd_adjacent_GN
#check DkMath.Lib.NumberTheory.prod_cyclotomicEval_eq_geomSum
#check DkMath.CosmicFormula.gcd_GTail_eq_gcd_boundary
#check DkMath.CosmicFormula.GTail_congr_of_modEq
#check DkMath.CosmicFormula.pow_dvd_higher_tail
#check DkMath.CosmicFormula.padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
#check DkMath.CosmicFormula.GTail_split_at
#check DkMath.Algebra.BinomTail.add_pow_tail_exists
#check DkMath.Lib.Algebra.square_add_band
#check DkMath.Lib.Cosmic.completion_body_add_gap
#check DkMath.Lib.Cosmic.powerDifferenceCofactor_add_eq_GTail
#check DkMath.Lib.Cosmic.powerDifferenceCofactor_symm
#check DkMath.Lib.Cosmic.signedCompletionDefect_add_cofactor
#check DkMath.Lib.NumberTheory.gcd_gap_powerDifferenceCofactor_eq_gcd_degree
#check DkMath.Lib.NumberTheory.coprime_powerDifferenceCofactor_right
#check DkMath.Lib.NumberTheory.gcd_eq_of_padicValNat_eq_on_support
#check DkMath.Lib.Cosmic.completionLoan_numerators_add
#check DkMath.Lib.NumberTheory.padicValNat_split
#check DkMath.Lib.NumberTheory.padicValNat_choose_prime_pow
#check DkMath.NumberTheory.GapFocusing.primeRatio_ne_zero
#check DkMath.NumberTheory.GapFocusing.isRoot_cyclotomic_iff_prime_pow_mul_orderOf
#check DkMath.NumberTheory.GapFocusing.padicValInt_cyclotomicEval_eq_pow_sub_one_of_orderOf_eq
#check DkMath.Lib.NumberTheory.padicValNat_pow_sub_pow_of_four_dvd
#check DkMath.Lib.NumberTheory.primeOrder_eq_one_iff_dvd_gap
#check DkMath.CFBRC.cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow
#check DkMath.NumberTheory.GapFocusing.map_cyclotomicShiftedEval
#check DkMath.NumberTheory.GapFocusing.eval_homogenize_zero_second
#check DkMath.Lib.NumberTheory.map_homogeneousCyclotomicEval

/-! Integrated endpoints retain their mathematical hypotheses. -/
#check DkMath.Lib.Cosmic.powerDifferenceCofactor_recurrence
#check DkMath.Lib.Cosmic.completionDefect_pos
#check DkMath.Lib.Cosmic.completion_pairwise_coprime
#check DkMath.Lib.NumberTheory.isStrongDvdSequence_powerDifferenceCofactor
#check DkMath.Lib.NumberTheory.gcd_cofactor_completionDefect
#check DkMath.Lib.Cosmic.completionLoan_primitive_triple
#check DkMath.Lib.NumberTheory.prime_dvd_homogeneousCyclotomicEval_iff_order_ray
#check DkMath.Lib.NumberTheory.prime_dvd_homogeneousCyclotomicEval_iff_dvd_first_of_dvd_second

example {n x y : ℕ} (hn : 0 < n) (hxy : x.Coprime y) :
    Nat.gcd (DkMath.Lib.Cosmic.powerDifferenceCofactor n x y)
      (DkMath.Lib.Cosmic.completionDefect n x y) =
        if Odd n then 1 else (x + y) * Nat.gcd (n / 2) ((x + y) ^ (n - 2)) :=
  DkMath.Lib.NumberTheory.gcd_cofactor_completionDefect hn hxy

example (x u : ℕ) : x ^ 2 + u * (2 * x + u) = (x + u) ^ 2 :=
  DkMath.Lib.Algebra.square_add_band x u
