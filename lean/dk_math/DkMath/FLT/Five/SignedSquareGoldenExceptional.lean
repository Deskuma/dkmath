/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedFiveAdicPowerSplit
import DkMath.FLT.Five.SquareGoldenBridge

#print "file: DkMath.FLT.Five.SignedSquareGoldenExceptional"

namespace DkMath.FLT.Five

/-!
# The common signed square-to-norm packet

Both signed five-adic orientations are represented by integral coordinates `M,N` with

`GoldenNorm M N = 5*b^5`, `M-2N = 5^8*a^10`,

and a retained square discriminant.  The sign of `N` distinguishes difference from sum
factorization; the norm and boundary formulas are otherwise common.  This packet is the
input from which the unique visible ramified factor above five is removed.
-/

/-- The sum residual is the golden norm with a negative cross-beam coordinate. -/
theorem sumGN5_eq_goldenNorm_signed (u v : ℕ) :
    GoldenNorm
        ((u : ℤ) ^ 2 + (v : ℤ) ^ 2)
        (-((u : ℤ) * (v : ℤ))) =
      (SumGN5 u v : ℤ) := by
  unfold GoldenNorm SumGN5
  by_cases h : v ≤ u
  · rw [if_pos h]
    push_cast
    rw [Nat.cast_sub h]
    ring
  · rw [if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    push_cast
    rw [Nat.cast_sub huv]
    ring

/-- The signed endpoint coordinates retain a square discriminant. -/
theorem signed_endpoint_square_discriminant (x y : ℤ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * (-(x * y)) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 := by
  ring

/-- Provenance of the square-golden coordinates in the two signed orientations. -/
inductive SignedSquareGoldenSource
    (u v w : ℕ) (M N delta : ℤ) : Prop
  | difference :
      M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = (w : ℤ) * (v : ℤ) →
      delta = (w : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
  | sum :
      M = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = -((u : ℤ) * (v : ℤ)) →
      delta = (u : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta

/--
The exceptional square-golden packet common to both signed five-adic sources.
The single residual five-layer becomes a golden norm `5*b^5`, while the
carrier becomes the tenth-power square boundary `5^8*a^10`.
-/
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  source : SignedSquareGoldenSource u v w M N delta
  golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
  tenth_boundary : M - 2 * N = (5 : ℤ) ^ 8 * (powerSplit.a : ℤ) ^ 10
  square_discriminant : M ^ 2 - 4 * N ^ 2 = delta ^ 2
  discriminant_five_eq :
    (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (powerSplit.b : ℤ) ^ 5

private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  let p := s.fiveAdic
  cases p.source with
  | difference hcarrier hresidual _ =>
      have hvw : v ≤ w :=
        (right_lt_of_fermat5Equation p.normal.pack.hx p.normal.pack.hEq).le
      let M : ℤ := (w : ℤ) ^ 2 + (v : ℤ) ^ 2
      let N : ℤ := (w : ℤ) * (v : ℤ)
      let delta : ℤ := (w : ℤ) ^ 2 - (v : ℤ) ^ 2
      have hGoldenBase :
          GoldenNorm M N = (GN5 (w - v) v : ℤ) := by
        have hlink := (GN5_eq_goldenNorm_squareLink (w - v) v).symm
        have hsum : w - v + v = w := Nat.sub_add_cancel hvw
        simpa [M, N, hsum] using hlink
      have hGolden : GoldenNorm M N = 5 * (s.b : ℤ) ^ 5 := by
        calc
          GoldenNorm M N = (GN5 (w - v) v : ℤ) := hGoldenBase
          _ = (p.residual : ℤ) := by rw [hresidual]
          _ = ((5 * s.b ^ 5 : ℕ) : ℤ) := by rw [s.residual_eq]
          _ = 5 * (s.b : ℤ) ^ 5 := by norm_num
      have hBoundaryBase : M - 2 * N = (p.carrier : ℤ) ^ 2 := by
        rw [hcarrier, Nat.cast_sub hvw]
        dsimp [M, N]
        ring
      have hBoundary :
          M - 2 * N = (5 : ℤ) ^ 8 * (s.a : ℤ) ^ 10 := by
        calc
          M - 2 * N = (p.carrier : ℤ) ^ 2 := hBoundaryBase
          _ = (((5 ^ 4 * s.a ^ 5 : ℕ) : ℤ)) ^ 2 := by rw [s.carrier_eq]
          _ = (5 : ℤ) ^ 8 * (s.a : ℤ) ^ 10 := by
            push_cast
            ring
      have hSquare : M ^ 2 - 4 * N ^ 2 = delta ^ 2 := by
        dsimp [M, N, delta]
        exact endpoint_square_discriminant (w : ℤ) (v : ℤ)
      have hDiscFive :
          (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (s.b : ℤ) ^ 5 := by
        calc
          (2 * M + N) ^ 2 - 5 * N ^ 2 = 4 * GoldenNorm M N :=
            (four_mul_goldenNorm_eq_discriminant_five M N).symm
          _ = 4 * (5 * (s.b : ℤ) ^ 5) := by rw [hGolden]
          _ = 20 * (s.b : ℤ) ^ 5 := by ring
      exact ⟨{
        powerSplit := s
        M := M
        N := N
        delta := delta
        source := .difference rfl rfl rfl
        golden_eq := hGolden
        tenth_boundary := hBoundary
        square_discriminant := hSquare
        discriminant_five_eq := hDiscFive }⟩
  | sum hcarrier hresidual _ =>
      let M : ℤ := (u : ℤ) ^ 2 + (v : ℤ) ^ 2
      let N : ℤ := -((u : ℤ) * (v : ℤ))
      let delta : ℤ := (u : ℤ) ^ 2 - (v : ℤ) ^ 2
      have hGoldenBase : GoldenNorm M N = (SumGN5 u v : ℤ) := by
        simpa [M, N] using sumGN5_eq_goldenNorm_signed u v
      have hGolden : GoldenNorm M N = 5 * (s.b : ℤ) ^ 5 := by
        calc
          GoldenNorm M N = (SumGN5 u v : ℤ) := hGoldenBase
          _ = (p.residual : ℤ) := by rw [hresidual]
          _ = ((5 * s.b ^ 5 : ℕ) : ℤ) := by rw [s.residual_eq]
          _ = 5 * (s.b : ℤ) ^ 5 := by norm_num
      have hBoundaryBase : M - 2 * N = (p.carrier : ℤ) ^ 2 := by
        rw [hcarrier]
        push_cast
        dsimp [M, N]
        ring
      have hBoundary :
          M - 2 * N = (5 : ℤ) ^ 8 * (s.a : ℤ) ^ 10 := by
        calc
          M - 2 * N = (p.carrier : ℤ) ^ 2 := hBoundaryBase
          _ = (((5 ^ 4 * s.a ^ 5 : ℕ) : ℤ)) ^ 2 := by rw [s.carrier_eq]
          _ = (5 : ℤ) ^ 8 * (s.a : ℤ) ^ 10 := by
            push_cast
            ring
      have hSquare : M ^ 2 - 4 * N ^ 2 = delta ^ 2 := by
        dsimp [M, N, delta]
        exact signed_endpoint_square_discriminant (u : ℤ) (v : ℤ)
      have hDiscFive :
          (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (s.b : ℤ) ^ 5 := by
        calc
          (2 * M + N) ^ 2 - 5 * N ^ 2 = 4 * GoldenNorm M N :=
            (four_mul_goldenNorm_eq_discriminant_five M N).symm
          _ = 4 * (5 * (s.b : ℤ) ^ 5) := by rw [hGolden]
          _ = 20 * (s.b : ℤ) ^ 5 := by ring
      exact ⟨{
        powerSplit := s
        M := M
        N := N
        delta := delta
        source := .sum rfl rfl rfl
        golden_eq := hGolden
        tenth_boundary := hBoundary
        square_discriminant := hSquare
        discriminant_five_eq := hDiscFive }⟩

/-- Chosen signed square-golden exceptional packet from an exact power split. -/
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)

/-- Chosen signed square-golden packet obtained directly from a signed normal form. -/
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)

/-- Receiver contract for contradictions stated on the common signed square/norm packet. -/
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False

/-- A refuter for every exceptional square-golden packet closes both signed orientations. -/
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)

/-- The same square-golden core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_squareGoldenExceptionalCore hCore) hPack hBranch

end DkMath.FLT.Five
