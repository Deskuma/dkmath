/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenCoprimeFactor
import DkMath.FLT.Five.GoldenFifthPowerCoordinates

#print "file: DkMath.FLT.Five.SignedGoldenUnitClasses"

namespace DkMath.FLT.Five

/--
The exact unit-classification contract needed downstream: modulo fifth powers,
every golden unit has one of the five representatives `1, phi, ..., phi^4`.
The sign needs no separate representative because `(-delta)^5 = -(delta^5)`.
-/
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)

/-- The finite five-sector form obtained from unit classification and factor splitting. -/
abbrev SignedGoldenFiniteUnitSectorCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ i : Fin 5, ∃ gamma : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)

/-- Unit classes modulo fifth powers are sufficient to reduce every packet to five sectors. -/
theorem signedGoldenFiniteUnitSectorCore_of_unitClasses
    (hClasses : GoldenUnitClassesModFifth) :
    SignedGoldenFiniteUnitSectorCore := by
  intro u v w p
  obtain ⟨epsilon, gamma, hepsilon, hbeta⟩ :=
    signedGoldenFifthPowerUpToUnitCore p
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  refine ⟨i, goldenMul delta gamma, ?_⟩
  rw [hbeta, hdelta]
  simp only [golden_mul_eq, golden_pow_eq]
  rw [mul_pow]
  ring

/-- The packet's large five-adic coordinate survives in every finite unit sector. -/
theorem SignedGoldenRamifierStrippedPacket.unitSector_snd_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} {gamma : GoldenInt}
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) :
    (goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd =
      -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  rw [← hbeta, p.beta_snd]

/--
The exact remaining packet arithmetic proposition after unconditional factor
splitting: no packet's `beta` is a unit times a fifth power.
-/
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False

/-- The remaining unit/coordinate exclusion is sufficient for the stripped core. -/
theorem signedGoldenRamifierStrippedCore_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    SignedGoldenRamifierStrippedCore := by
  intro u v w p
  obtain ⟨epsilon, gamma, hepsilon, hbeta⟩ :=
    signedGoldenFifthPowerUpToUnitCore p
  exact hExclude p epsilon gamma hepsilon hbeta

/-- The unit-times-fifth-power exclusion is exactly the stripped packet core. -/
theorem signedGoldenUnitFifthPowerExclusion_iff_strippedCore :
    SignedGoldenUnitFifthPowerExclusion ↔ SignedGoldenRamifierStrippedCore := by
  constructor
  · exact signedGoldenRamifierStrippedCore_of_unitFifthPowerExclusion
  · intro hCore u v w p epsilon gamma hepsilon hbeta
    exact hCore p

/-- Consequently the same exact exclusion closes both signed Branch-A orientations. -/
theorem signedBranchARefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) : SignedBranchARefuter :=
  signedBranchARefuter_of_goldenRamifierStrippedCore
    (signedGoldenRamifierStrippedCore_of_unitFifthPowerExclusion hExclude)

/-- The exact unit/coordinate exclusion also closes every routed Branch-B packet. -/
theorem branchB_false_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False :=
  branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_unitFifthPowerExclusion hExclude) hPack hBranch

end DkMath.FLT.Five
