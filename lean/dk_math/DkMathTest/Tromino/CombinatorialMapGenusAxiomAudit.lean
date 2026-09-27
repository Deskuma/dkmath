/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.Tromino.CombinatorialMapAxiomAudit

#print "file: DkMathTest.Tromino.CombinatorialMapGenusAxiomAudit"

namespace DkMathTest.Tromino.CombinatorialMapGenusAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.CombinatorialMapAxiomAudit

example {g h : Nat} (hg : HasCombinatorialGenus twoTwoMap g)
    (hh : HasCombinatorialGenus twoTwoMap h) : g = h :=
  combinatorialGenus_unique twoTwoMap hg hh

example : HasCombinatorialGenus twoTwoMap 0 ↔
    twoTwoMap.eulerCharacteristic = 2 :=
  combinatorialGenus_zero_iff twoTwoMap

example : HasCombinatorialGenus twoThreeMap 1 ↔
    twoThreeMap.eulerCharacteristic = 0 :=
  combinatorialGenus_one_iff twoThreeMap

example {g : Nat} (hg : HasCombinatorialGenus twoThreeMap g) :
    twoThreeMap.eulerCharacteristic ≤ 2 :=
  combinatorialGenus_characteristic_le_two twoThreeMap hg

example {g : Nat} (hg : HasCombinatorialGenus twoThreeMap g) :
    Even twoThreeMap.eulerCharacteristic :=
  combinatorialGenus_characteristic_even twoThreeMap hg

end DkMathTest.Tromino.CombinatorialMapGenusAxiomAudit
