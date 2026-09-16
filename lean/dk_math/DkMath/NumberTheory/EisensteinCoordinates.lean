/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EisensteinCoordinates

#print "file: DkMath.NumberTheory.EisensteinCoordinates"

/-!
# Historical compatibility facade

The canonical Eisenstein coordinate implementation now lives under
`DkMath.Lib.NumberTheory`.  This module preserves the historical namespace and
names by exporting those declarations without duplicating any proofs.
-/

namespace DkMath.NumberTheory.EisensteinCoordinates

export DkMath.Lib.NumberTheory
  (eisensteinCoord eisensteinCoord_fst eisensteinCoord_snd
    norm_eisensteinCoord eisensteinCoord_mul eisensteinCoord_sq
    eisensteinCoord_mul_sq norm_eisensteinCoord_mul_sq
    norm_eisensteinCoord_mul_sq_polynomial
    eisenstein_square_coefficient_coprime
    eisenstein_mul_sq_eq_cubicCoord_fst
    eisenstein_mul_sq_eq_cubicCoord_snd
    eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime
    eisenstein_mul_sq_eq_cubicCoord_norm
    eisenstein_mul_sq_eq_cubicCoord_polynomial_norm)
end DkMath.NumberTheory.EisensteinCoordinates
