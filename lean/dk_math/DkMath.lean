/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic  -- Basic Definitions and Utilities
import DkMath.Samples  -- Sample Theorems and Examples
-- ABC: abc Conjecture Module
import DkMath.ABC.Basic  -- ABC Conjecture Basics
import DkMath.ABC.PadicValNat  -- ABC: p-adic Valuation on Natural Numbers
import DkMath.ABC.CountPowersDividing2n1  -- ABC: Counting Powers Dividing 2n+1
-- Collatz Module (2026 Cartography Research)
import DkMath.Collatz.Collatz2K26  -- Collatz2K26: Accelerated Collatz Dynamics
-- Cosmic Formula Module
import DkMath.CellDim  -- Cell Dimensionality
import DkMath.CosmicFormula  -- Cosmic Formula Basics
import DkMath.CosmicFormulaDim  -- Cosmic Formula Dimensionality
import DkMath.CosmicFormulaGeom  -- Cosmic Formula Geometry
import DkMath.CosmicFormulaLinear  -- Cosmic Formula Linearity
import DkMath.CosmicFormulaTrominoLink  -- Cosmic Formula and Tromino Link
import DkMath.CosmicFormulaCellDim  -- Cosmic Formula Cell Dimensionality
import DkMath.CosmicFormulaExp  -- Cosmic Formula Exponent
import DkMath.CosmicFormulaBinom  -- Cosmic Formula Binomial Expansion
-- Polyomino Module
import DkMath.Polyomino  -- Polyomino Basics
import DkMath.PolyominoPrototype  -- Polyomino Prototype
import DkMath.Tromino  -- Polyomino: Tromino Basics
-- Silver Ratio Module
import DkMath.SilverRatio  -- Silver Ratio Unit
-- Silver Ratio Module Tests
import DkMath.UniqueRepSimple  -- Unique Representation in ℚ(√2)
import DkMath.UniqueRepresentation  -- Silver Ratio Unique Representation
-- DHNT: Dynamic Harmonic Number Theory
import DkMath.DHNT  -- DHNT: Units and Quantities (Dynamic Harmonic Number Theory)
-- RH: Riemann Hypothesis Module
import DkMath.RH  -- RH: Riemann Hypothesis Module

-- >|---|-----------|------------------|-------------------|-------------------|----------|---------

/-!

# DkMath Library

This is the main module file for the DkMath library, which encompasses various mathematical
concepts and theories. The library is organized into several submodules, each focusing on
specific areas of mathematics, including the ABC conjecture, Cosmic Formula, Polyominoes,
Silver Ratio, Dynamic Harmonic Number Theory (DHNT), and the Riemann Hypothesis (RH).

## Modules Included:

- Basic Definitions and Utilities
- ABC Conjecture Module
- Cosmic Formula Module
- Polyomino Module
- Silver Ratio Module
- DHNT: Dynamic Harmonic Number Theory
- RH: Riemann Hypothesis Module

Each submodule contains definitions, theorems, and proofs relevant to its area of study.
-/

-- build check marker: sh: $ lake build -v --no-ansi --log-level=info | grep -B1 "file: "
#print "file: DkMath"

namespace DkMath

-- None

end DkMath
