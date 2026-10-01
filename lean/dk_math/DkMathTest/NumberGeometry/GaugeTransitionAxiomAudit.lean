/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry

/-!
# Axiom audit for the NGEO-007 gauge-transition API

The audit checks the public transition, ratio, similarity, and retarget
declarations and prints their transitive axioms.
-/

#check DkMath.NumberGeometry.MassScalesBy
#check DkMath.NumberGeometry.massScalesBy_refl
#check DkMath.NumberGeometry.MassScalesBy.trans
#check DkMath.NumberGeometry.MassScalesBy.factor_unique
#check DkMath.NumberGeometry.MassScalesBy.factor_pos
#check DkMath.NumberGeometry.MassScalesBy.factor_ne_zero
#check DkMath.NumberGeometry.MassScalesBy.inv
#check DkMath.NumberGeometry.massGaugeRatio
#check DkMath.NumberGeometry.massGaugeRatio_eq_of_massScalesBy
#check DkMath.NumberGeometry.massScalesBy_of_massGaugeRatio_eq
#check DkMath.NumberGeometry.massGaugeRatio_trans
#check DkMath.NumberGeometry.massScalesBy_iff_dist_sq
#check DkMath.NumberGeometry.massScalesBy_similarity
#check DkMath.NumberGeometry.MassScalesBy.similarity
#check DkMath.NumberGeometry.TwoPointKernel.retarget
#check DkMath.NumberGeometry.massGauge_retarget
#check DkMath.NumberGeometry.massScalesBy_retarget_of_onNatShell
#check DkMath.NumberGeometry.natShell_massLevel_scale

#print axioms DkMath.NumberGeometry.massScalesBy_refl
#print axioms DkMath.NumberGeometry.MassScalesBy.trans
#print axioms DkMath.NumberGeometry.MassScalesBy.factor_unique
#print axioms DkMath.NumberGeometry.MassScalesBy.factor_pos
#print axioms DkMath.NumberGeometry.MassScalesBy.factor_ne_zero
#print axioms DkMath.NumberGeometry.MassScalesBy.inv
#print axioms DkMath.NumberGeometry.massGaugeRatio_eq_of_massScalesBy
#print axioms DkMath.NumberGeometry.massScalesBy_of_massGaugeRatio_eq
#print axioms DkMath.NumberGeometry.massGaugeRatio_trans
#print axioms DkMath.NumberGeometry.massScalesBy_iff_dist_sq
#print axioms DkMath.NumberGeometry.massScalesBy_similarity
#print axioms DkMath.NumberGeometry.MassScalesBy.similarity
#print axioms DkMath.NumberGeometry.massGauge_retarget
#print axioms DkMath.NumberGeometry.massScalesBy_retarget_of_onNatShell
#print axioms DkMath.NumberGeometry.natShell_massLevel_scale
