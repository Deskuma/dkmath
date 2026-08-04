/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFramePowerTailAbelian

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFramePowerTailAbelian"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

example {alpha : ℝ} (halpha : 0 < alpha) (K : ℕ) :
    ((((K + 1 : ℕ) : ℝ) ^ (-alpha)) / alpha) ≤
      shiftedRpowModelTail alpha K :=
  shifted_rpow_model_tail_lower halpha K

example {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ alpha) * shiftedRpowModelTail alpha K)
      atTop (nhds ((1 : ℝ) / alpha)) :=
  normalized_shiftedRpowModelTail_tendsto_inv halpha

example {a : ℕ → ℝ} {alpha D : ℝ}
    (hterm : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n)
      atTop (nhds D)) :
    Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) *
          powerTailResidual a alpha D n)
      atTop (nhds 0) :=
  powerTailResidual_scaled_tendsto_zero hterm

example {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha)
    (ha : Summable a) :
    Summable (powerTailResidual a alpha D) :=
  summable_powerTailResidual halpha ha

example {a : ℕ → ℝ} {alpha D : ℝ}
    (halpha : 0 < alpha)
    (ha : Summable a)
    (hterm : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (alpha + 1)) * a n)
      atTop (nhds D)) :
    Tendsto
      (fun K : ℕ =>
        ((K : ℝ) ^ alpha) * realSequenceTail a K)
      atTop (nhds (D / alpha)) :=
  normalized_realSequenceTail_tendsto halpha ha hterm

end DkMath.RH.CFBRCProjection
