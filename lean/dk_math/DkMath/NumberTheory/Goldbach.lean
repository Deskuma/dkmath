/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Basic
import DkMath.NumberTheory.Goldbach.Obstruction
import DkMath.NumberTheory.Goldbach.PrimeWorld
import DkMath.NumberTheory.Goldbach.Cardinality
import DkMath.NumberTheory.Goldbach.Capacity
import DkMath.NumberTheory.Goldbach.Conservation
import DkMath.NumberTheory.Goldbach.Signature
import DkMath.NumberTheory.Goldbach.Limitations
import DkMath.NumberTheory.Goldbach.Overlap
import DkMath.NumberTheory.Goldbach.PairOverlap

#print "file: DkMath.NumberTheory.Goldbach"

/-!
# Goldbach via fixed-center GN fibers

This facade exports exact reformulations, finite obstruction search, paired
CRT cardinality, interval capacity bounds, and bridges to existing PCK and
GN signature APIs. `StrongGoldbach` is a proposition. Its conditional closure
requires `GoldbachCapacityEscape`, which is proved equivalent to it; no
unconditional provider is present. `Limitations` records kernel-checked
counterexamples to stronger shortcuts, including the strict incidence bound.

`Overlap` and `PairOverlap` add exact finite ledger identities, including the
Pascal pair-overlap residual decomposition. They stop at this finite ledger
layer and do not provide a universal escape theorem.
-/
