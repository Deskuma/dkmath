/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.EuclideanGeometry

#print "file: DkMathTest.EuclideanGeometry.Basic"

/-!
# Public-surface and axiom audit for EuclideanGeometry v0

This inspection module checks the stable theorem chain without adding proof
content to the public library.
-/

open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory.EuclideanGeometry

-- Generic algebra and normalized return.
#check KernelFamily.kernel_nsmul
#check regularKernel_pow_eq_one
#check ExactKernelOrder
#check regularKernel_exactOrder

-- Finite algebraic orbit.
#check regularVertex
#check regularVertex_q2
#check regularVertex_injective
#check regularVertex_ncard_range

-- Euclidean interpretation.
#check realTrigKernel_act_euclidean_eq_rotation
#check euclideanRegularVertex_mem_unitSphere
#check euclideanRegularVertex_next_two_pi_div
#check euclideanRegularVertex_injective

-- Arithmetic and algebraic constructibility boundaries.
#check IsGaussWantzelIndex
#check IsGaussWantzelIndex.exists_totient_eq_two_pow
#check QuadraticallyConstructibleScalar
#check QuadraticallyConstructibleUnitKernel.pow
#check QuadraticallyConstructibleRegularOrbit
#check quadraticallyConstructibleRegularOrbit_of_regularKernel

-- Representative dependency-surface audit.
#print axioms regularKernel_exactOrder
#print axioms regularVertex_injective
#print axioms realTrigKernel_act_euclidean_eq_rotation
#print axioms IsGaussWantzelIndex.exists_totient_eq_two_pow
#print axioms quadraticallyConstructibleRegularOrbit_of_regularKernel
