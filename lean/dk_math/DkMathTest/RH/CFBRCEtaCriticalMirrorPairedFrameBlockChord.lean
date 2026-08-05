/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameBlockChord

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockChord"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockChord

open Filter
open scoped BigOperators Topology
open DkMath.RH.CFBRCProjection

example
    (s : ℂ) (K N : ℕ) :
    |(Finset.range N).sum
        (fun j : ℕ => etaPairFrameStepPhase s (K + j))| =
      etaPairFrameBlockSpan s K N :=
  abs_sum_range_etaPairFrameStepPhase_nat_add_eq_blockSpan s K N

example
    (s : ℂ) (K N : ℕ)
    (hspan : etaPairFrameBlockSpan s K N ≤ 1) :
    ‖etaPairFrameBlockRotation s K N - 1‖ ≤
      2 * etaPairFrameBlockSpan s K N :=
  norm_etaPairFrameBlockRotation_sub_one_le_two_mul_blockSpan
    s K N hspan

example
    (s : ℂ) (N : ℕ) :
    Tendsto
      (fun K : ℕ => ‖etaPairFrameBlockRotation s K N - 1‖)
      atTop (nhds 0) :=
  norm_etaPairFrameBlockRotation_sub_one_tendsto_zero s N

example
    (s : ℂ) (K N : ℕ) :
    etaPairBaseRotation s (K + N) =
      etaPairBaseRotation s K * etaPairFrameBlockRotation s K N :=
  etaPairBaseRotation_add_eq_mul_blockRotation s K N

example
    (s : ℂ) (K j : ℕ)
    (hspan : etaPairFrameBlockSpan s K j ≤ 1) :
    ‖etaCriticalMirrorBlockStartRotatedDefectPairTerm s K j -
        etaCriticalMirrorRotatedDefectPairTerm s (K + j)‖ ≤
      2 * etaPairFrameBlockSpan s K j *
        ‖etaCriticalMirrorDefectPairTerm s (K + j)‖ :=
  norm_etaCriticalMirrorBlockStartRotatedDefectPairTerm_sub_local_le
    s K j hspan

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameBlockChord
