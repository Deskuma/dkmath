/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry

/-!
# Axiom audit for the NGEO-008 prime-scale API

The audit checks the labelled step, irreducibility, finite-chain, and
prime-power declarations and prints their transitive axioms.
-/

#check DkMath.NumberGeometry.PrimeScaleStep
#check DkMath.NumberGeometry.PrimeScaleStep.prime
#check DkMath.NumberGeometry.PrimeScaleStep.massScalesBy
#check DkMath.NumberGeometry.PrimeScaleStep.label_unique
#check DkMath.NumberGeometry.PrimeScaleStep.target_active
#check DkMath.NumberGeometry.primeScaleStep_retarget_of_onNatShell
#check DkMath.NumberGeometry.PrimeScaleStep.irreducible
#check DkMath.NumberGeometry.PrimeScaleStep.dist_sq_eq_prime_mul_dist_sq
#check DkMath.NumberGeometry.PrimeScaleChain
#check DkMath.NumberGeometry.PrimeScaleChain.massScalesBy_prod
#check DkMath.NumberGeometry.PrimeScaleChain.target_active
#check DkMath.NumberGeometry.PrimeScaleChain.massScalesBy_pow

#print axioms DkMath.NumberGeometry.PrimeScaleStep.label_unique
#print axioms DkMath.NumberGeometry.PrimeScaleStep.target_active
#print axioms DkMath.NumberGeometry.primeScaleStep_retarget_of_onNatShell
#print axioms DkMath.NumberGeometry.PrimeScaleStep.irreducible
#print axioms DkMath.NumberGeometry.PrimeScaleStep.dist_sq_eq_prime_mul_dist_sq
#print axioms DkMath.NumberGeometry.PrimeScaleChain.massScalesBy_prod
#print axioms DkMath.NumberGeometry.PrimeScaleChain.target_active
#print axioms DkMath.NumberGeometry.PrimeScaleChain.massScalesBy_pow
