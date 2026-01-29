/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.Basic
import DkMath.Collatz.V2
import DkMath.Collatz.Shift

/-
# Collatz2K26: Cartography of the Accelerated Collatz Dynamics

Main module for the 2026 research into the accelerated Collatz map, focusing on:

1. **Block Cartography**: Petal structure at scale 2^k (core block size)
2. **Singularity Map**: Anomaly detection via v₂-based filaments
3. **Drift Statistics**: Comparing D_m(n) across related trajectories
4. **Conservation Laws**: Shift-invariance and phase transitions

Structure:
  - Basic.lean:  Core definitions (C, T, OddNat, s, S_m, D_m)
  - V2.lean:     2-adic valuation v₂ and foundational lemmas
  - Shift.lean:  Block shift, petal conservation (v₂ invariance)
  - This file:   Integration and higher-level properties
-/
