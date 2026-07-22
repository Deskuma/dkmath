/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.KernelPower
import DkMath.CosmicFormula.Rotation.CF2D.CycleDivision
import DkMath.CosmicFormula.Rotation.CF2D.RegularOrbit
import DkMath.CosmicFormula.Rotation.CF2D.EuclideanRegularOrbit
import DkMath.NumberTheory.EuclideanGeometry.FermatForm
import DkMath.NumberTheory.EuclideanGeometry.QuadraticConstructible

#print "file: DkMath.EuclideanGeometry"

/-!
# Euclidean geometry from CF2D regular orbits

This public entry point aggregates the stable v0 layers established by the
EuclideanGeometry project:

* generic unit-kernel powers and normalized cycle division;
* exact finite CF2D regular orbits;
* their oriented Euclidean interpretation;
* the independent Gauss-Wantzel Fermat-form predicate;
* algebraic quadratic-expression constructibility through the kernel-to-orbit
  lift.

The aggregate does not claim a complete Gauss-Wantzel theorem.  In particular,
it does not identify the algebraic expression semantics with geometric
straightedge-and-compass constructions and does not prove that every
Gauss-Wantzel index has a constructible regular kernel.
-/
