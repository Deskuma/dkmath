import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicWeightedGapObstruction
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSuccessorAudit

namespace DkMath.FLT.Seven
open SevenRealCubicInt
noncomputable section

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    IsCoprime s.gapRoot s.quotientRoot := by
  have hcores :
      IsCoprime
        ((s.gapUnit : SevenRealCubicInt) * s.gapRoot ^ 7)
        ((s.quotientUnit : SevenRealCubicInt) * s.quotientRoot ^ 7) := by
    simpa [s.gapCore_eq, s.quotientCore_eq] using s.cores_isCoprime
  have hpow : IsCoprime (s.gapRoot ^ 7) (s.quotientRoot ^ 7) :=
    (isCoprime_mul_units_left s.gapUnit.isUnit s.quotientUnit.isUnit
      (s.gapRoot ^ 7) (s.quotientRoot ^ 7)).mp hcores
  exact
    (IsCoprime.pow_iff (m := 7) (n := 7)
      (by norm_num) (by norm_num)).mp hpow

end
end DkMath.FLT.Seven
