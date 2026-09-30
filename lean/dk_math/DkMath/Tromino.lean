/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.Basic
import DkMath.Tromino.BoundaryPairing
import DkMath.Tromino.BoundarySignature
import DkMath.Tromino.CombinatorialMap
import DkMath.Tromino.CosmicBridge
import DkMath.Tromino.EulerCount
import DkMath.Tromino.Exchange
import DkMath.Tromino.ExchangeRescue
import DkMath.Tromino.FaceOrbit
import DkMath.Tromino.FlowPairing
import DkMath.Tromino.FlowSignature
import DkMath.Tromino.FlowTransition
import DkMath.Tromino.FlowTransitionXor
import DkMath.Tromino.FourColorCell
import DkMath.Tromino.GraphColoringBridge
import DkMath.Tromino.IntegralMod2Bridge
import DkMath.Tromino.KempeRepair
import DkMath.Tromino.LocalFrameEquiv
import DkMath.Tromino.MacroCell
import DkMath.Tromino.MacroTromino
import DkMath.Tromino.PieceExchange
import DkMath.Tromino.PortCombinatorialMap
import DkMath.Tromino.PortDualityKernel
import DkMath.Tromino.PortEulerCount
import DkMath.Tromino.PortF2Chains
import DkMath.Tromino.PortF2Exactness
import DkMath.Tromino.PortFaceOrbit
import DkMath.Tromino.PortFaceStarColorReduction
import DkMath.Tromino.PortFaceStarEuler
import DkMath.Tromino.PortFaceStarMap
import DkMath.Tromino.PortFaceStarSubdivision
import DkMath.Tromino.PortGenusZeroHolonomy
import DkMath.Tromino.PortKirchhoffFlow
import DkMath.Tromino.PortNetwork
import DkMath.Tromino.PortRegionWalk
import DkMath.Tromino.PortRotationSystem
import DkMath.Tromino.PortTensionColoring
import DkMath.Tromino.PortTriangularReduction
import DkMath.Tromino.PortTriangularTetrahedral
import DkMath.Tromino.PortTriangulationReduction
import DkMath.Tromino.PortV4Chains
import DkMath.Tromino.RecursiveCosmicBridge
import DkMath.Tromino.RecursiveMacro
import DkMath.Tromino.RegionPotential
import DkMath.Tromino.RegionWalk
import DkMath.Tromino.RepairChamber
import DkMath.Tromino.RepairDistance
import DkMath.Tromino.Restoration
import DkMath.Tromino.RestorationFlipTransport
import DkMath.Tromino.RestorationRepairState
import DkMath.Tromino.RotationSystem
import DkMath.Tromino.State
import DkMath.Tromino.StateProjectionTransport
import DkMath.Tromino.StateSector
import DkMath.Tromino.TetrahedralClosure
import DkMath.Tromino.TransitionGraph
import DkMath.Tromino.TransitionXor

#print "file: DkMath.Tromino"

/-!
# Public Tromino facade

This file is the import-only public facade for the Tromino package.

The elementary polyomino geometry that previously lived in this root module is
now in `DkMath.Tromino.Basic`.  Importing `DkMath.Tromino` intentionally loads
the complete production Tromino surface so the package participates in the
normal `DkMath` aggregate build.

Submodules should import the narrow dependencies they need (in particular
`DkMath.Tromino.Basic` for the legacy `DkMath.Polyomino.Tromino` geometry)
rather than importing this facade, which avoids facade dependency cycles.

The facade is a discovery/build boundary only.  It does not strengthen any
Four-Color, preserving-flip, repair-height, or Port-chain theorem claims.
-/
