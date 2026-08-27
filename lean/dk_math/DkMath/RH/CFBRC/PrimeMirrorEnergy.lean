/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy

#print "file: DkMath.RH.CFBRC.PrimeMirrorEnergy"

/-!
# Prime-mirror energy entry point

This module exports the first two implementation checkpoints of the
Pascal-prime-wave CFBRC energy design:

* the one-mode mirror-offset algebra Core;
* the finite nonnegative coordinate energy and `(N, N + 1)` increment law.

It intentionally does not export a zero-locus collapse provider or an RH
closure theorem.  Those remain later analytic checkpoints.
-/
