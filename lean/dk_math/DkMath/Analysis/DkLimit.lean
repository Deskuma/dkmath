/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.Analysis.DkLimit"

/-!
# DkMath limit vocabulary

This module is the first public entrance for DkMath limit language.

The implementation deliberately uses Mathlib's `Filter.Tendsto`, `nhds`,
`atTop`, and `nhdsWithin`. The DkMath layer only names the recurring roles:

* finite refinement indices tend to infinity;
* a finite Gap vanishes;
* a punctured Gap vanishes while remaining nonzero.

This keeps the current implementation compatible with Mathlib analysis while
leaving room for a later computable or interval-native `DkLimit` layer. In the
`Big = Body + Gap` reading, these abbreviations name the collapse operation;
they do not change the underlying topology.

[TODO: dk-limit/import-scope] The current module imports all of `Mathlib` for
stability while the surrounding analysis layer is still moving. Once the API
settles, reduce this to the specific filter and topology imports actually
used here.

[TODO: dk-limit/cosmic-derivative-alias] Add DkMath-named wrappers for the
existing cosmic derivative limit theorems, for example power-kernel Gap
collapse at zero. This will connect `DkGapCollapsesTo` with the older
`CosmicDerivativePowerLimit` surface without changing either proof.

[TODO: dk-limit/punctured-gap-spelling] If later bridge theorems benefit from
`simp`, consider replacing the current punctured neighborhood spelling with
`{u : ℝ | u ≠ 0}` or adding a lemma equating the two forms.
-/

namespace DkMath.Analysis

/--
DkMath name for sequence convergence along finite refinement depth.

The current implementation is exactly Mathlib's `Filter.Tendsto` at
`Filter.atTop`. The name records the DkMath role: a finite observation indexed
by refinement depth stabilizes to a semantic value.
-/
abbrev DkTendstoAtTop
    {α : Type*} [TopologicalSpace α] (f : ℕ → α) (a : α) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds a)

/--
DkMath name for full-neighborhood Gap collapse.

This is used when the finite Body kernel is already defined at `gap = 0`, so
the Gap may vanish through an ordinary neighborhood of zero.
-/
abbrev DkGapCollapsesTo
    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
  Filter.Tendsto f (nhds (0 : ℝ)) (nhds a)

/--
DkMath name for punctured Gap collapse.

This is used for observations such as difference quotients where the finite
expression is meaningful only while the Gap is nonzero.
-/
abbrev DkPuncturedGapCollapsesTo
    {α : Type*} [TopologicalSpace α] (f : ℝ → α) (a : α) : Prop :=
  Filter.Tendsto f
    (nhdsWithin (0 : ℝ) (Set.compl ({(0 : ℝ)} : Set ℝ)))
    (nhds a)

end DkMath.Analysis
