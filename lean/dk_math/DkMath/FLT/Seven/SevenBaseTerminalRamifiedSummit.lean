/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore
import DkMath.FLT.Seven.AwaySecondCoordinateLoad

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

@[simp] theorem traceOneInt_intCast_fst (s a : ℤ) :
    ((a : TraceOneInt s).fst) = a := rfl

@[simp] theorem traceOneInt_intCast_snd (s a : ℤ) :
    ((a : TraceOneInt s).snd) = 0 := rfl

@[simp] theorem traceOneInt_natCast_fst (s : ℤ) (a : ℕ) :
    ((a : TraceOneInt s).fst) = a := rfl

@[simp] theorem traceOneInt_natCast_snd (s : ℤ) (a : ℕ) :
    ((a : TraceOneInt s).snd) = 0 := rfl

@[simp] theorem traceOneInt_intCast_pow_fst (s a : ℤ) (n : ℕ) :
    (((a : TraceOneInt s) ^ n).fst) = a ^ n := by
  rw [← Int.cast_pow]
  rfl

@[simp] theorem traceOneInt_intCast_pow_snd (s a : ℤ) (n : ℕ) :
    (((a : TraceOneInt s) ^ n).snd) = 0 := by
  rw [← Int.cast_pow]
  rfl

/-- The common integer ramified summit reached by both terminal Row-Y and
Row-Z.  Positivity and the two seven-unit facts are retained because they are
exactly the hypotheses used by the second-coordinate depth transfer. -/
structure PrimitiveRamifiedSummitPacket : Type where
  endpointLeft : ℤ
  endpointRight : ℤ
  distinguished : ℤ
  gapRoot : ℕ
  residualRoot : ℕ
  root : TraceOneInt (-2)
  gapRoot_pos : 0 < gapRoot
  residualRoot_pos : 0 < residualRoot
  endpoint_coprime : IsCoprime endpointLeft endpointRight
  endpointLeft_ne_zero : endpointLeft ≠ 0
  endpointRight_ne_zero : endpointRight ≠ 0
  endpointSum_ne_zero : endpointLeft + endpointRight ≠ 0
  coordinate_coprime :
    IsCoprime
      (cyclotomicSevenFst endpointLeft endpointRight)
      (cyclotomicSevenSnd endpointLeft endpointRight)
  endpointRight_not_seven_dvd : ¬ (7 : ℤ) ∣ endpointRight
  residualRoot_not_seven_dvd : ¬ 7 ∣ residualRoot
  fermat_eq :
    endpointLeft ^ 7 - endpointRight ^ 7 = distinguished ^ 7
  gap_eq :
    endpointLeft - endpointRight = 7 ^ 6 * (gapRoot : ℤ) ^ 7
  residual_eq :
    cyclotomicSeven endpointLeft endpointRight =
      7 * (residualRoot : ℤ) ^ 7
  distinguished_eq :
    distinguished = 7 * gapRoot * residualRoot
  coordinate_eq :
    cyclotomicSevenToTraceOne endpointLeft endpointRight =
      sevenAxis * root ^ 7
  root_norm_eq : tqNorm root = residualRoot

theorem traceOne_norm_pow_ramified (a : TraceOneInt (-2)) (n : ℕ) :
    tqNorm (a ^ n) = tqNorm a ^ n := by
  induction n with
  | zero => simp [DkMath.NumberTheory.TraceOneQuadratic.norm]
  | succ n ih => rw [pow_succ, traceOne_norm_mul, ih, pow_succ]

private theorem root_norm_eq_of_residual_power
    {root residual : TraceOneInt (-2)} {b : ℕ}
    (hpower : residual = root ^ 7)
    (hnorm : tqNorm residual = (b : ℤ) ^ 7) :
    tqNorm root = b := by
  have hpows : tqNorm root ^ 7 = (b : ℤ) ^ 7 := by
    rw [← traceOne_norm_pow_ramified, ← hpower, hnorm]
  have hnonneg : 0 ≤ tqNorm root := traceOneNegTwo_norm_nonneg root
  have habspows :
      Int.natAbs (tqNorm root) ^ 7 = b ^ 7 := by
    calc
      _ = Int.natAbs (tqNorm root ^ 7) := by
        rw [Int.natAbs_pow]
      _ = Int.natAbs ((b : ℤ) ^ 7) := congrArg Int.natAbs hpows
      _ = _ := by simp
  have habs : Int.natAbs (tqNorm root) = b :=
    Nat.pow_left_injective (by decide : 7 ≠ 0) habspows
  calc
    tqNorm root = (Int.natAbs (tqNorm root) : ℤ) :=
      (Int.natAbs_of_nonneg hnonneg).symm
    _ = b := congrArg Nat.cast habs

/-- Natural Row-Y ramified charts inhabit the common integer summit. -/
noncomputable def AwaySevenBaseTerminalRowYProfile.ramifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hy : AwaySevenBaseTerminalRowYProfile terminal) :
    PrimitiveRamifiedSummitPacket := by
  let packet := Classical.choice hy.to_swapped_ramified
  let q := packet.seventhPower.residual
  let split := q.powerSplit
  have hzx : x ≤ z :=
    (right_lt_of_fermat7Equation source.swapXY.hx source.swapXY.hEq).le
  have hcyclo :
      cyclotomicSeven (z : ℤ) (x : ℤ) =
        7 * (split.b : ℤ) ^ 7 := by
    calc
      _ = ((DkMath.CosmicFormulaBinom.GN 7 (z - x) x : ℕ) : ℤ) := by
        rw [GN_seven_sub_eq_traceOneNorm_negTwo z x hzx,
          cyclotomicSeven_eq_traceOneNorm_negTwo]
      _ = _ := by exact_mod_cast split.residual_eq
  exact {
    endpointLeft := z
    endpointRight := x
    distinguished := y
    gapRoot := split.a
    residualRoot := split.b
    root := packet.seventhPower.root
    gapRoot_pos := split.a_pos
    residualRoot_pos := split.b_pos
    endpoint_coprime :=
      (coprime_y_z_of_counterexamplePack source.swapXY).symm.isCoprime
    endpointLeft_ne_zero := by exact_mod_cast source.hz.ne'
    endpointRight_ne_zero := by exact_mod_cast source.hx.ne'
    endpointSum_ne_zero := by
      have hzpos : (0 : ℤ) < z := by exact_mod_cast source.hz
      have hxpos : (0 : ℤ) < x := by exact_mod_cast source.hx
      omega
    coordinate_coprime :=
      counterexample_cyclotomicSeven_coordinates_isCoprime source.swapXY
    endpointRight_not_seven_dvd := by
      intro hx
      exact split.sevenAdic.seven_not_dvd_y (Int.ofNat_dvd.mp hx)
    residualRoot_not_seven_dvd := split.seven_not_dvd_b
    fermat_eq := by
      have h := source.hEq
      unfold Fermat7Equation at h
      nlinarith
    gap_eq := by exact_mod_cast split.gap_eq
    residual_eq := hcyclo
    distinguished_eq := by exact_mod_cast split.distinguished_eq
    coordinate_eq := packet.seventhPower.coordinate_eq
    root_norm_eq := root_norm_eq_of_residual_power
      packet.seventhPower.residual_eq q.residual_norm_eq }

/-- Signed Row-Z ramified charts inhabit the same common integer summit. -/
noncomputable def AwaySevenBaseTerminalRowZProfile.ramifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    PrimitiveRamifiedSummitPacket := by
  let q := hz.signedResidualCore
  let split := q.powerSplit
  let root := Classical.choose q.exists_residualCore_eq_seventh_power
  have hroot : q.residualCore = root ^ 7 :=
    Classical.choose_spec q.exists_residualCore_eq_seventh_power
  exact {
    endpointLeft := x
    endpointRight := -(y : ℤ)
    distinguished := z
    gapRoot := split.a
    residualRoot := split.b
    root := root
    gapRoot_pos := split.a_pos
    residualRoot_pos := split.b_pos
    endpoint_coprime := source.hxy.isCoprime.neg_right
    endpointLeft_ne_zero := by exact_mod_cast source.hx.ne'
    endpointRight_ne_zero := by
      simp only [neg_ne_zero]
      exact_mod_cast source.hy.ne'
    endpointSum_ne_zero := by
      intro hsum
      have hxy : x = y := by
        exact_mod_cast (sub_eq_zero.mp hsum)
      subst y
      have hx1 : x = 1 :=
        Nat.eq_one_of_dvd_coprimes source.hxy dvd_rfl dvd_rfl
      subst x
      have heq := source.hEq
      norm_num [Fermat7Equation] at heq
      by_cases hz1 : z = 1
      · simp [hz1] at heq
      · have hzpos := source.hz
        have hz2 : 2 ≤ z := by omega
        have hpows : 2 ^ 7 ≤ z ^ 7 := Nat.pow_le_pow_left hz2 7
        omega
    coordinate_coprime :=
      rowZ_signed_cyclotomicSeven_coordinates_isCoprime source.hxy
    endpointRight_not_seven_dvd := by
      simpa only [dvd_neg] using
        (show ¬ (7 : ℤ) ∣ (y : ℤ) by
          intro hy
          exact hz.seven_not_dvd_y (Int.ofNat_dvd.mp hy))
    residualRoot_not_seven_dvd := by
      intro hb
      apply q.residual_norm_not_seven_dvd
      rw [q.residual_norm_eq]
      exact dvd_pow (Int.ofNat_dvd.mpr hb) (by norm_num)
    fermat_eq := by
      have h := source.hEq
      unfold Fermat7Equation at h
      nlinarith
    gap_eq := by
      simp only [sub_neg_eq_add]
      exact_mod_cast split.sum_eq
    residual_eq := by
      rw [← alternatingCyclotomicSeven_intCast]
      exact_mod_cast split.residual_eq
    distinguished_eq := by exact_mod_cast split.distinguished_eq
    coordinate_eq := by rw [q.coordinate_eq, hroot]
    root_norm_eq :=
      root_norm_eq_of_residual_power hroot q.residual_norm_eq }

/-- Every surviving terminal away row reaches one common primitive ramified
summit; the impossible Row-Sum branch is eliminated. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.nonempty_ramifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Nonempty PrimitiveRamifiedSummitPacket := by
  rcases terminal.row_profile_decision with hy | hz | hs
  · exact ⟨hy.ramifiedSummit⟩
  · exact ⟨hz.ramifiedSummit⟩
  · exact hs.false_of_swapped_away.elim

/-- Canonical common ramified summit selected from the terminal row
classification. -/
noncomputable def
    AwaySevenBaseTerminalUnitSectorPacket.ramifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    PrimitiveRamifiedSummitPacket :=
  Classical.choice terminal.nonempty_ramifiedSummit

/-- The quotient left after expanding a ramified cyclotomic coordinate around
the seven-divisible endpoint gap. -/
def ramifiedGapQuotient (h e : ℤ) : TraceOneInt (-2) :=
  ⟨7 * h ^ 2 - e ^ 2, -e ^ 2 - 7 * e * h - 14 * h ^ 2⟩

/-- Exact expansion of the trace-one cyclotomic coordinate at `e + 7*h`. -/
theorem cyclotomicSevenToTraceOne_add_seven_mul
    (h e : ℤ) :
    cyclotomicSevenToTraceOne (e + 7 * h) e =
      sevenAxis *
        (((-e ^ 3 : ℤ) : TraceOneInt (-2)) +
          ((7 * h : ℤ) : TraceOneInt (-2)) *
            ramifiedGapQuotient h e) := by
  ext <;>
    simp [cyclotomicSevenToTraceOne, cyclotomicSevenFst,
      cyclotomicSevenSnd, sevenAxis_eq, ramifiedGapQuotient,
      show ((7 : TraceOneInt (-2)).fst) = 7 by rfl,
      show ((7 : TraceOneInt (-2)).snd) = 0 by rfl] <;>
    ring

/-- Linear ramified factor in the second coordinate of
`sevenAxis * (u+vα)^7`. -/
def ramifiedLinear (u v : ℤ) : ℤ := 2 * u + v

/-- Left cubic ramified factor. -/
def ramifiedLeftCubic (u v : ℤ) : ℤ :=
  u ^ 3 - 2 * u ^ 2 * v - 15 * u * v ^ 2 - 13 * v ^ 3

/-- Right cubic ramified factor. -/
def ramifiedRightCubic (u v : ℤ) : ℤ :=
  u ^ 3 + 5 * u ^ 2 * v - 8 * u * v ^ 2 + v ^ 3

/-- The ramified second coordinate splits into one linear and two cubic
factors. -/
theorem ramifiedSeventhSnd_factorization (u v : ℤ) :
    ramifiedSeventhSnd u v =
      ramifiedLinear u v * ramifiedLeftCubic u v *
        ramifiedRightCubic u v := by
  simp [ramifiedSeventhSnd, ramifiedLinear, ramifiedLeftCubic,
    ramifiedRightCubic]
  ring

/-- The difference of the ramified cubics is controlled by the root norm. -/
theorem ramifiedRightCubic_sub_left (u v : ℤ) :
    ramifiedRightCubic u v - ramifiedLeftCubic u v =
      7 * v * tqNorm (⟨u, v⟩ : TraceOneInt (-2)) := by
  simp [ramifiedLeftCubic, ramifiedRightCubic,
    DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

/-- The sum of the ramified cubics splits into three linear factors. -/
theorem ramifiedLeftCubic_add_right (u v : ℤ) :
    ramifiedLeftCubic u v + ramifiedRightCubic u v =
      (u - 3 * v) * (u + 4 * v) * ramifiedLinear u v := by
  simp [ramifiedLeftCubic, ramifiedRightCubic, ramifiedLinear]
  ring

/-- The common summit coordinate equation exposes the ramified root triple
against the three endpoint factors. -/
theorem PrimitiveRamifiedSummitPacket.endpoint_product_eq
    (p : PrimitiveRamifiedSummitPacket) :
    -(p.endpointLeft * p.endpointRight *
        (p.endpointLeft + p.endpointRight)) =
      ramifiedLinear p.root.fst p.root.snd *
        ramifiedLeftCubic p.root.fst p.root.snd *
        ramifiedRightCubic p.root.fst p.root.snd := by
  have hsnd := congrArg TraceOneInt.snd p.coordinate_eq
  rw [show
      (cyclotomicSevenToTraceOne p.endpointLeft p.endpointRight).snd =
        cyclotomicSevenSnd p.endpointLeft p.endpointRight by rfl] at hsnd
  rw [show
      (sevenAxis * p.root ^ 7).snd =
        ramifiedSeventhSnd p.root.fst p.root.snd by
          rcases p.root with ⟨u, v⟩
          exact congrArg TraceOneInt.snd
            (sevenAxis_mul_pow_seven_eq u v)] at hsnd
  rw [cyclotomicSevenSnd_eq_neg_endpoint_product,
    ramifiedSeventhSnd_factorization] at hsnd
  simpa [mul_comm, add_comm] using hsnd

end DkMath.FLT.Seven
