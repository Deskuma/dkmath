/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedBranchA

#print "file: DkMath.FLT.Five.SignedFiveAdic"

namespace DkMath.FLT.Five

/-- The positive fifth-power residual for the sum factorization. -/
def SumGN5 (u v : ℕ) : ℕ :=
  if h : v ≤ u then
    (u - v) ^ 4 +
      3 * (u - v) ^ 3 * v +
      4 * (u - v) ^ 2 * v ^ 2 +
      2 * (u - v) * v ^ 3 +
      v ^ 4
  else
    (v - u) ^ 4 +
      3 * (v - u) ^ 3 * u +
      4 * (v - u) ^ 2 * u ^ 2 +
      2 * (v - u) * u ^ 3 +
      u ^ 4

/-- The sum of fifth powers factors through `u+v` with positive residual `SumGN5`. -/
theorem add_mul_sumGN5_eq_add_pow_five (u v : ℕ) :
    (u + v) * SumGN5 u v = u ^ 5 + v ^ 5 := by
  unfold SumGN5
  by_cases h : v ≤ u
  · simp only [if_pos h]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp
    ring
  · simp only [if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
    simp
    ring

private theorem five_not_dvd_left_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ u := by
  intro h5u
  have h5v : 5 ∣ v := (Nat.dvd_add_right h5u).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop

private theorem five_not_dvd_right_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ v := by
  intro h5v
  have h5u : 5 ∣ u := (Nat.dvd_add_left h5v).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop

private theorem fourth_power_mod_five_eq_one
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    n ^ 4 % 5 = 1 := by
  rw [Nat.pow_mod]
  have hnlt : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hn0 : n % 5 ≠ 0 := by
    intro hn0
    exact h5n (Nat.dvd_of_mod_eq_zero hn0)
  interval_cases h : n % 5 <;> norm_num [h] at hn0 ⊢

private theorem fourth_power_zmod25_decomposition
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    ∃ q : ℕ, (n : ZMod 25) ^ 4 = 1 + 5 * (q : ZMod 25) := by
  let q : ℕ := n ^ 4 / 5
  have hmod : n ^ 4 % 5 = 1 := fourth_power_mod_five_eq_one h5n
  have hsplit := Nat.mod_add_div (n ^ 4) 5
  have hdecomp : n ^ 4 = 1 + 5 * q := by
    dsimp [q]
    omega
  refine ⟨q, ?_⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod 25)) hdecomp
  simpa using hcast

private theorem GN5_cast_mod25_eq_five
    {g y : ℕ} (h5g : 5 ∣ g) (h5y : ¬ 5 ∣ y) :
    (GN5 g y : ZMod 25) = 5 := by
  rcases h5g with ⟨k, rfl⟩
  rcases fourth_power_zmod25_decomposition h5y with ⟨q, hq⟩
  unfold GN5
  push_cast
  rw [hq]
  ring

private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5 := by
  have h5u : ¬ 5 ∣ u :=
    five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
  have h5v : ¬ 5 ∣ v :=
    five_not_dvd_right_of_coprime_of_dvd_add hcop h5sum
  by_cases h : v ≤ u
  · simp only [SumGN5, if_pos h]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    subst u
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * v = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (v : ZMod 25) = 5 * (k : ZMod 25) := by
      exact_mod_cast hcarrier
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (v : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5v with ⟨q, hq⟩
    simp
    push_cast
    rw [hdZ, hq]
    ring
  · simp only [SumGN5, if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
    subst v
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * u = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (u : ZMod 25) = 5 * (k : ZMod 25) := by
      exact_mod_cast hcarrier
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (u : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5u with ⟨q, hq⟩
    simp
    push_cast
    rw [hdZ, hq]
    ring

private theorem mod_twentyFive_eq_five_of_zmod_eq_five
    {n : ℕ} (h : (n : ZMod 25) = 5) :
    n % 25 = 5 := by
  have hmod : n ≡ 5 [MOD 25] :=
    (ZMod.natCast_eq_natCast_iff n 5 25).mp (by simpa using h)
  simpa [Nat.ModEq] using hmod

private theorem eq_five_add_twentyFive_mul_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ∃ M : ℕ, n = 5 + 25 * M := by
  refine ⟨n / 25, ?_⟩
  have hsplit := Nat.mod_add_div n 25
  omega

private theorem five_dvd_of_eq_five_add_twentyFive_mul
    {n M : ℕ} (h : n = 5 + 25 * M) :
    5 ∣ n := by
  use 1 + 5 * M
  omega

private theorem not_twentyFive_dvd_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ¬ 25 ∣ n := by
  intro h25
  have hzero : n % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
  omega

/-- Exact residual valuation from divisibility by five and non-divisibility by twenty-five. -/
theorem padicValNat_five_eq_one_of_dvd_not_sq
    {n : ℕ} (h5 : 5 ∣ n) (h25 : ¬ 25 ∣ n) :
    padicValNat 5 n = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hnz : n ≠ 0 := by
    intro hn0
    apply h25
    simp [hn0]
  have hge : 1 ≤ padicValNat 5 n :=
    (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 1 hnz).mp (by simpa using h5)
  have hle : padicValNat 5 n ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ padicValNat 5 n := by omega
    have hsq : 5 ^ 2 ∣ n :=
      (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 2 hnz).mpr htwo
    exact h25 (by simpa using hsq)
  exact le_antisymm hle hge

/-- If one factor has valuation one in a fifth-power product, the other has valuation `4 mod 5`. -/
theorem padicValNat_carrier_shape_of_mul_eq_fifth
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 5)
    (hrVal : padicValNat 5 residual = 1) :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow :
      padicValNat 5 (distinguished ^ 5) = 5 * padicValNat 5 distinguished := by
    simpa using (padicValNat.pow (p := 5) (a := distinguished) 5 hd0)
  have hmul :
      padicValNat 5 (carrier * residual) =
        padicValNat 5 carrier + padicValNat 5 residual := by
    simpa using (padicValNat.mul (p := 5) hc0 hr0)
  have hvalEq :
      5 * padicValNat 5 distinguished = padicValNat 5 carrier + 1 := by
    calc
      5 * padicValNat 5 distinguished =
          padicValNat 5 (distinguished ^ 5) := hpow.symm
      _ = padicValNat 5 (carrier * residual) := by rw [hEq]
      _ = padicValNat 5 carrier + padicValNat 5 residual := hmul
      _ = padicValNat 5 carrier + 1 := by rw [hrVal]
  have hdValPos : 0 < padicValNat 5 distinguished := by
    have : 0 < 5 * padicValNat 5 distinguished := by
      rw [hvalEq]
      exact Nat.succ_pos _
    exact Nat.pos_of_mul_pos_left this
  have hcVal :
      padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 :=
    Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat 5 distinguished - 1, ?_⟩
  have hsplit :
      (padicValNat 5 distinguished - 1) + 1 = padicValNat 5 distinguished :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hdValPos)
  calc
    padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 := hcVal
    _ = 5 * ((padicValNat 5 distinguished - 1) + 1) - 1 := by rw [hsplit]
    _ = 4 + 5 * (padicValNat 5 distinguished - 1) := by omega

/-- Provenance of the carrier/residual pair inside the two signed orientations. -/
inductive SignedFiveAdicSource
    (u v w carrier residual distinguished : ℕ) : Prop
  | difference :
      carrier = w - v →
      residual = GN5 (w - v) v →
      distinguished = u →
      SignedFiveAdicSource u v w carrier residual distinguished
  | sum :
      carrier = u + v →
      residual = SumGN5 u v →
      distinguished = w →
      SignedFiveAdicSource u v w carrier residual distinguished

/-- Common five-adic packet obtained from either signed Branch-A orientation. -/
structure SignedFiveAdicPacket (u v w : ℕ) : Prop where
  normal : SignedBranchANormalForm u v w
  carrier : ℕ
  residual : ℕ
  distinguished : ℕ
  source : SignedFiveAdicSource u v w carrier residual distinguished
  factor_eq : carrier * residual = distinguished ^ 5
  carrier_pos : 0 < carrier
  residual_pos : 0 < residual
  distinguished_pos : 0 < distinguished
  five_dvd_carrier : 5 ∣ carrier
  five_dvd_distinguished : 5 ∣ distinguished
  residual_mod_twentyFive : residual % 25 = 5
  residual_shape : ∃ M : ℕ, residual = 5 + 25 * M
  residual_padicValNat : padicValNat 5 residual = 1
  carrier_padicValNat_shape :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m

/-- Both signed orientations produce the same exact five-adic load packet. -/
theorem signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w := by
  rcases hNF with ⟨hPack, hOrientation⟩
  cases hOrientation with
  | differenceGap h5u h5gap =>
      have hvw : v ≤ w :=
        (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
      have hcarrierPos : 0 < w - v :=
        gap_pos_of_fermat5Equation hPack.hx hPack.hEq
      have h5v : ¬ 5 ∣ v := by
        intro h5v
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hPack.hxy
      have hfactor : (w - v) * GN5 (w - v) v = u ^ 5 := by
        simpa [Body5] using body5_eq_fifth_power_of_fermat hvw hPack.hEq
      have hcast : (GN5 (w - v) v : ZMod 25) = 5 :=
        GN5_cast_mod25_eq_five h5gap h5v
      have hmod : GN5 (w - v) v % 25 = 5 :=
        mod_twentyFive_eq_five_of_zmod_eq_five hcast
      rcases eq_five_add_twentyFive_mul_of_mod_eq_five hmod with ⟨M, hshape⟩
      have h5res : 5 ∣ GN5 (w - v) v :=
        five_dvd_of_eq_five_add_twentyFive_mul hshape
      have h25res : ¬ 25 ∣ GN5 (w - v) v :=
        not_twentyFive_dvd_of_mod_eq_five hmod
      have hresVal : padicValNat 5 (GN5 (w - v) v) = 1 :=
        padicValNat_five_eq_one_of_dvd_not_sq h5res h25res
      have hresPos : 0 < GN5 (w - v) v := by omega
      have hcarrierShape :
          ∃ m : ℕ, padicValNat 5 (w - v) = 4 + 5 * m :=
        padicValNat_carrier_shape_of_mul_eq_fifth
          hcarrierPos.ne' hresPos.ne' hPack.hx.ne' hfactor hresVal
      exact
        { normal := ⟨hPack, .differenceGap h5u h5gap⟩
          carrier := w - v
          residual := GN5 (w - v) v
          distinguished := u
          source := .difference rfl rfl rfl
          factor_eq := hfactor
          carrier_pos := hcarrierPos
          residual_pos := hresPos
          distinguished_pos := hPack.hx
          five_dvd_carrier := h5gap
          five_dvd_distinguished := h5u
          residual_mod_twentyFive := hmod
          residual_shape := ⟨M, hshape⟩
          residual_padicValNat := hresVal
          carrier_padicValNat_shape := hcarrierShape }
  | sumGap h5w h5sum =>
      have hcarrierPos : 0 < u + v := by omega
      have hfactor : (u + v) * SumGN5 u v = w ^ 5 := by
        calc
          (u + v) * SumGN5 u v = u ^ 5 + v ^ 5 :=
            add_mul_sumGN5_eq_add_pow_five u v
          _ = w ^ 5 := by simpa [Fermat5Equation] using hPack.hEq
      have hcast : (SumGN5 u v : ZMod 25) = 5 :=
        SumGN5_cast_mod25_eq_five hPack.hxy h5sum
      have hmod : SumGN5 u v % 25 = 5 :=
        mod_twentyFive_eq_five_of_zmod_eq_five hcast
      rcases eq_five_add_twentyFive_mul_of_mod_eq_five hmod with ⟨M, hshape⟩
      have h5res : 5 ∣ SumGN5 u v :=
        five_dvd_of_eq_five_add_twentyFive_mul hshape
      have h25res : ¬ 25 ∣ SumGN5 u v :=
        not_twentyFive_dvd_of_mod_eq_five hmod
      have hresVal : padicValNat 5 (SumGN5 u v) = 1 :=
        padicValNat_five_eq_one_of_dvd_not_sq h5res h25res
      have hresPos : 0 < SumGN5 u v := by omega
      have hcarrierShape :
          ∃ m : ℕ, padicValNat 5 (u + v) = 4 + 5 * m :=
        padicValNat_carrier_shape_of_mul_eq_fifth
          hcarrierPos.ne' hresPos.ne' hPack.hz.ne' hfactor hresVal
      exact
        { normal := ⟨hPack, .sumGap h5w h5sum⟩
          carrier := u + v
          residual := SumGN5 u v
          distinguished := w
          source := .sum rfl rfl rfl
          factor_eq := hfactor
          carrier_pos := hcarrierPos
          residual_pos := hresPos
          distinguished_pos := hPack.hz
          five_dvd_carrier := h5sum
          five_dvd_distinguished := h5w
          residual_mod_twentyFive := hmod
          residual_shape := ⟨M, hshape⟩
          residual_padicValNat := hresVal
          carrier_padicValNat_shape := hcarrierShape }

/-- The remaining common arithmetic kernel after exact signed five-adic reduction. -/
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False

/-- A contradiction for every exact five-adic packet refutes both signed orientations. -/
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)

/-- The same common five-adic core consequently closes every routed Branch-B candidate. -/
theorem branchB_false_of_fiveAdicCore
    (hCore : SignedFiveAdicCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_fiveAdicCore hCore) hPack hBranch

end DkMath.FLT.Five
