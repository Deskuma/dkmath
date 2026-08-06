/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFixedLimitObstruction

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameFixedLimitObstruction"

noncomputable section

namespace DkMathTest.RH

open Filter
open scoped Topology
open DkMath.RH.CFBRCProjection

example (s : ℂ) (K N : ℕ) :
    ‖etaPairFrameBlockRotation s K N - 1‖ =
      ‖etaPairBaseRotation s (K + N) - etaPairBaseRotation s K‖ :=
  norm_etaPairFrameBlockRotation_sub_one_eq_baseRotation_chord s K N

example {s L : ℂ}
    (hbase : Tendsto (etaPairBaseRotation s) atTop (nhds L)) :
    Tendsto
      (etaPairHalfDensityBlockSchedule.scheduledBlockRotation s)
      atTop (nhds 1) :=
  etaPairHalfDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
    hbase

example {s L : ℂ}
    (hbase : Tendsto (etaPairBaseRotation s) atTop (nhds L)) :
    Tendsto
      (etaPairFullDensityBlockSchedule.scheduledBlockRotation s)
      atTop (nhds 1) :=
  etaPairFullDensityBlockSchedule_scheduledBlockRotation_tendsto_one_of_baseRotation_tendsto
    hbase

example {s L : ℂ} (him : s.im ≠ 0) :
    ¬ Tendsto (etaPairBaseRotation s) atTop (nhds L) :=
  not_tendsto_etaPairBaseRotation_of_im_ne_zero him

example {s : ℂ} (him : s.im ≠ 0) :
    ¬ ∃ L : ℂ, Tendsto (etaPairBaseRotation s) atTop (nhds L) :=
  not_exists_etaPairBaseRotation_limit_of_im_ne_zero him

example {s : ℂ} (him : s.im ≠ 0) :
    EtaPairFixedLimitObstructionCertificate s :=
  etaPairFixedLimitObstructionCertificate_of_im_ne_zero him

end DkMathTest.RH
