import DkMath.FLT.QuadraticEssence

open DkMath.NumberTheory.TraceOneQuadratic

#print axioms DkMath.NumberTheory.TraceOneQuadratic.traceOne_norm_mul
#print axioms DkMath.NumberTheory.TraceOneQuadratic.four_mul_traceOneNorm_eq_discriminant
#print axioms DkMath.FLT.S0_nat_eq_traceOneNorm_negOne
#print axioms DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
#print axioms DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one
#print axioms DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink

example (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-1)) = a ^ 2 + a * b + b ^ 2 :=
  traceOneNorm_neg_one a b

example (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt 1) = a ^ 2 + a * b - b ^ 2 :=
  traceOneNorm_one a b
