/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.Tromino.PortCombinatorialMapAxiomAudit

#print "file: DkMathTest.Tromino.PortCombinatorialMapGenusAxiomAudit"

namespace DkMathTest.Tromino.PortCombinatorialMapGenusAxiomAudit

open DkMath.Tromino
open DkMathTest.Tromino.PortCombinatorialMapAxiomAudit
open DkMathTest.Tromino.PortRotationSystemAxiomAudit

example {g h : Nat} (hg : PortHasCombinatorialGenus portTwoMap g)
    (hh : PortHasCombinatorialGenus portTwoMap h) : g = h :=
  portCombinatorialGenus_unique portTwoMap hg hh

example : PortHasCombinatorialGenus portTwoMap 0 ↔
    portTwoMap.eulerCharacteristic = 2 :=
  portCombinatorialGenus_zero_iff portTwoMap

example : PortHasCombinatorialGenus portThreeMap 1 ↔
    portThreeMap.eulerCharacteristic = 0 :=
  portCombinatorialGenus_one_iff portThreeMap

example {g : Nat} (hg : PortHasCombinatorialGenus portTwoMap g) :
    portTwoMap.eulerCharacteristic ≤ 2 :=
  portCombinatorialGenus_characteristic_le_two portTwoMap hg

example {g : Nat} (hg : PortHasCombinatorialGenus portTwoMap g) :
    Even portTwoMap.eulerCharacteristic :=
  portCombinatorialGenus_characteristic_even portTwoMap hg

example : PortHasSphereCharacteristic portTwoMap ↔
    PortHasCombinatorialGenus portTwoMap 0 :=
  portHasSphereCharacteristic_iff_genus_zero portTwoMap

example : PortGenusZeroCombinatorialMap portTwoNetwork :=
  portTwoGenusZero

example : PortHasSphereCharacteristic portTwoGenusZero.map :=
  portTwoGenusZero.hasSphereCharacteristic

example {N : FlowNetwork} (M : FlowCombinatorialMap N) (g : Nat) :
    HasCombinatorialGenus M g ↔
      PortHasCombinatorialGenus M.toPortCombinatorialMap g :=
  M.toPortCombinatorialMap_genus_iff g

example {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) (g : Nat) :
    PortHasCombinatorialGenus M g ↔
      HasCombinatorialGenus (M.toFlowCombinatorialMap A) g :=
  M.toFlowCombinatorialMap_genus_iff A g

example {N : FlowNetwork} (M : FlowCombinatorialMap N) :
    HasSphereCharacteristic M ↔
      PortHasSphereCharacteristic M.toPortCombinatorialMap :=
  M.toPortCombinatorialMap_sphere_iff

example {P : PortNetwork} (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    PortHasSphereCharacteristic M ↔
      HasSphereCharacteristic (M.toFlowCombinatorialMap A) :=
  M.toFlowCombinatorialMap_sphere_iff A

#print axioms DkMath.Tromino.portCombinatorialGenus_unique
#print axioms DkMath.Tromino.portCombinatorialGenus_zero_iff
#print axioms DkMath.Tromino.portCombinatorialGenus_one_iff
#print axioms DkMath.Tromino.portCombinatorialGenus_characteristic_le_two
#print axioms DkMath.Tromino.portCombinatorialGenus_characteristic_even
#print axioms DkMath.Tromino.portHasSphereCharacteristic_iff_genus_zero
#print axioms DkMath.Tromino.PortGenusZeroCombinatorialMap.hasSphereCharacteristic

end DkMathTest.Tromino.PortCombinatorialMapGenusAxiomAudit
