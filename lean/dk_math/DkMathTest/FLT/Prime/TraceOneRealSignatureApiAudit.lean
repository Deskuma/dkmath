/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.TraceOneQuadraticField
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Complex.Basic

#print "file: DkMathTest.FLT.Prime.TraceOneRealSignatureApiAudit"

#check NumberField.IsTotallyReal
#check NumberField.isTotallyReal_iff
#check NumberField.isTotallyReal_iff_ofRingEquiv
#check NumberField.maximalRealSubfield
#check NumberField.mem_maximalRealSubfield_iff
#check NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal
#check NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
#check NumberField.IsTotallyReal.finrank
#check NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
#check NumberField.Units.rank
#check NumberField.Units.fundSystem
#check NumberField.Units.exist_unique_eq_mul_prod
#check NumberField.Units.torsion
#check NumberField.RingOfIntegers.equiv
#check RingEquiv.toMonoidHom
#check Units.map
#check Units.val_zpow_eq_zpow_val
#check Complex.re
#check Complex.im
#check Complex.ext
#check map_add
#check map_mul
#check map_pow
#check star
#check Complex.conj_eq_iff_im
#check NumberField.ComplexEmbedding.isReal_iff
#check NumberField.InfinitePlace.isReal_iff
#check QuadraticAlgebra.omega_mul_omega_eq_add
#check QuadraticAlgebra.mk_eq_add_smul_omega
#check QuadraticAlgebra.ext
#check QuadraticAlgebra.re_mul
#check QuadraticAlgebra.im_mul
#check QuadraticAlgebra.finrank_eq_two
#check orderOf_units
#check orderOf_submonoid
#check IsPrimitiveRoot.orderOf
