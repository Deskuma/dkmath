/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.Restoration

#print "file: DkMathTest.Tromino.RestorationAxiomAudit"

namespace DkMathTest.Tromino.RestorationAxiomAudit

open DkMath.Polyomino
open DkMath.Polyomino.Tromino
open DkMath.Tromino

example : shapeRestoreRel block2 L_tromino hole2 :=
  atomic_shapeRestoreRel

example : restoreShape L_tromino hole2 = block2 :=
  atomic_restoreShape

example : shapeGapFiber block2 L_tromino :=
  atomicGapFiber

example : shapeGapCrystal block2 :=
  atomicGapCrystal

example {target core gap₁ gap₂ : Shape}
    (h₁ : shapeRestoreRel target core gap₁)
    (h₂ : shapeRestoreRel target core gap₂) :
    gap₁ = gap₂ :=
  shapeRestoreRel_gap_unique h₁ h₂

example :
    DkMath.BookOfMagic.UniqueGap (shapeRestoreRel block2) L_tromino :=
  atomic_uniqueGap

#print axioms DkMath.Tromino.atomic_shapeRestoreRel
#print axioms DkMath.Tromino.shapeRestoreRel_gap_unique
#print axioms DkMath.Tromino.uniqueGap_of_shapeRestoreRel
#print axioms DkMath.Tromino.atomic_uniqueGap

end DkMathTest.Tromino.RestorationAxiomAudit
