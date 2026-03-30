/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
restore 前半の arithmetic core を表す canonical alias。

付録:
- `RestoreFromArithmetic`
  のうち、
  arithmetic witness から smaller counterexample の bare existence を作る段を
  今後この module で育てる。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget : Prop :=
  PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget

/--
restore arithmetic core の residue/root 段。

付録:
- arithmetic witness `q` から取り出せる
  `q ∣ x`, `q ∤ y`, `q ∤ z`, `q ∤ (z - y)`, `p ∣ (q - 1)` などの
  structural data を bundle 化して返す。
- 現段階では
  `RestoreWitnessProperties`
  がこの段の canonical datum である。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreResidueRootTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      RestoreWitnessProperties p x y z t s q

/--
restore arithmetic core の本当の未完核を表す descent assembly 段。

付録:
- `RestoreWitnessProperties`
  までの residue/root 情報は既に取れるので、
  今後の真正な数学核は
  この datum から smaller counterexample を組み立てる部分だと読む。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      RestoreWitnessProperties p x y z t s q →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
restore arithmetic core の q-adic lift seed。

付録:
- residue/root 段で得た arithmetic witness `q` から、
  `ZMod q` 上の nontrivial `p`-torsion witness を取り出したもの。
- 以後の restore assembly は、
  まずこの seed を作り、
  そこから smaller counterexample を組む 2 段として読める。
-/
structure PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed
    (p x y z t s q : ℕ) where
  ω : ZMod q
  hω_pow : ω ^ p = 1
  hω_ne_one : ω ≠ 1

/--
restore descent assembly の前半、q-adic lift 段。

付録:
- `RestoreWitnessProperties`
  から `ZMod q` 上の nontrivial `p`-torsion witness を回収する段である。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      RestoreWitnessProperties p x y z t s q →
      Nonempty (PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q)

/--
restore descent assembly の後半、lift seed から smaller counterexample を組む段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      RestoreWitnessProperties p x y z t s q →
      PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
restore assembly の最後で消費される bundled datum。

付録:
- `RestoreWitnessProperties`
  と `QAdicLiftSeed`
  をひとつの data object に束ねる。
- smaller-counterexample assembly を
  「datum を作る段」
  と
  「datum から counterexample を作る段」
  に分けるときの中間媒体である。
-/
structure PrimeGe5BranchAPrimitiveRestoreDescentDatum
    (p x y z t s q : ℕ) where
  hData : RestoreWitnessProperties p x y z t s q
  hLift : PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q

/--
descent datum から smaller counterexample へ行く直前の seed。

付録:
- ここではまだ actual な
  `x' y' z'`
  は作らず、
  それを組み立てるための arithmetic seed だけを bundle 化する。
- 現段階では datum 自体をそのまま持ち上げた minimal seed として置く。
-/
structure PrimeGe5BranchAPrimitiveRestoreDescentSeed
    (p x y z t s q : ℕ) where
  hDatum : PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q

/--
actual smaller counterexample を実現する直前の候補データ。

付録:
- `x' y' z'`
  の候補だけを bundle 化する。
- 以後の realization 段は、
  候補の抽出と候補の検証の 2 段へ分けて読める。
-/
structure PrimeGe5BranchAPrimitiveRestoreRealizationSeed
    (p x y z t s q : ℕ) where
  hSeed : PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q
  x' : ℕ
  y' : ℕ
  z' : ℕ

/--
q-adic lift seed から descent datum を bundle 化する段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      RestoreWitnessProperties p x y z t s q →
      PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q →
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q)

/--
bundled descent datum から smaller counterexample を作る本丸段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
descent datum から smaller-counterexample seed を抽出する段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q →
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q)

/--
smaller-counterexample seed から actual smaller counterexample を作る最後の段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
descent seed から actual candidate triple を抽出する段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q →
      Nonempty (PrimeGe5BranchAPrimitiveRestoreRealizationSeed p x y z t s q)

/--
candidate triple を actual smaller counterexample として検証する最後の段。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∀ hR : PrimeGe5BranchAPrimitiveRestoreRealizationSeed p x y z t s q,
        PrimeGe5CounterexamplePack p hR.x' hR.y' hR.z' ∧
        p ∣ (hR.z' - hR.y') ∧
        hR.z' < z

/--
restore 後半の packet packaging core を表す canonical alias。

付録:
- smaller counterexample を
  Branch A normal-form packet に包装する purely structural な段である。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget : Prop :=
  PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget

/--
restore sub-target 2 本が揃えば、
元の `RestoreFromArithmetic` target は橋だけで閉じる。

付録:
- 以後の restore 作業は、
  この theorem を canonical recompose bridge として参照すればよい。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_restoreSubtargets
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackCore : PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget :=
  primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet
    hArithCore hPackCore

/--
residue/root 段は、現在の Branch A restore work では default 実装済みである。
-/
theorem primeGe5BranchAPrimitiveRestoreResidueRoot_default :
    PrimeGe5BranchAPrimitiveRestoreResidueRootTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p
  exact restore_witness_properties_default hpack hp_dvd_gap hgap hsx
    hq_prime hqs hqt hcop_qy hq_ne_p

/--
q-adic lift 段は、既に `restore_witness_cong_one_mod_p` の証明内容から default 実装できる。
-/
theorem primeGe5BranchAPrimitiveRestoreQAdicLift_default :
    PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p hData
  have hq_dvd_x := hData.hq_dvd_x
  have hq_not_dvd_y := hData.hq_not_dvd_y
  have hq_not_dvd_z := hData.hq_not_dvd_z
  have hq_not_dvd_gap := hData.hq_not_dvd_gap
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  have hy_ne_zero : (y : ZMod q) ≠ 0 := by
    intro hy_zero
    exact hq_not_dvd_y ((ZMod.natCast_eq_zero_iff y q).mp hy_zero)
  have hz_ne_zero : (z : ZMod q) ≠ 0 := by
    intro hz_zero
    exact hq_not_dvd_z ((ZMod.natCast_eq_zero_iff z q).mp hz_zero)
  have hx_eq_zero : (x : ZMod q) = 0 := by
    exact (ZMod.natCast_eq_zero_iff x q).mpr hq_dvd_x
  have hzp_eq_yp : (z : ZMod q) ^ p = (y : ZMod q) ^ p := by
    have hFLT : (x : ZMod q) ^ p + (y : ZMod q) ^ p = (z : ZMod q) ^ p := by
      have hEq := hpack.hEq
      have : (↑(x ^ p + y ^ p) : ZMod q) = (↑(z ^ p) : ZMod q) := by
        congr 1
      simpa [Nat.cast_add, Nat.cast_pow] using this
    rw [hx_eq_zero, zero_pow hpack.hp.ne_zero, zero_add] at hFLT
    exact hFLT.symm
  have hz_ne_y : (z : ZMod q) ≠ (y : ZMod q) := by
    intro hzy
    have hsub : (z : ZMod q) - (y : ZMod q) = 0 := sub_eq_zero.mpr hzy
    have hq_dvd_gap' : q ∣ (z - y) := by
      rw [← Nat.cast_sub hpack.hyz] at hsub
      exact (ZMod.natCast_eq_zero_iff (z - y) q).mp hsub
    exact hq_not_dvd_gap hq_dvd_gap'
  let ω : ZMod q := (z : ZMod q) * ((y : ZMod q)⁻¹)
  have hω_pow : ω ^ p = 1 := by
    change ((z : ZMod q) * ((y : ZMod q)⁻¹)) ^ p = 1
    rw [mul_pow, hzp_eq_yp, ← mul_pow]
    rw [mul_inv_cancel₀ hy_ne_zero, one_pow]
  have hω_ne_one : ω ≠ 1 := by
    change (z : ZMod q) * ((y : ZMod q)⁻¹) ≠ 1
    intro hω_eq
    have : (z : ZMod q) = (y : ZMod q) := by
      have h := hω_eq
      field_simp at h
      exact h
    exact hz_ne_y this
  exact ⟨⟨ω, hω_pow, hω_ne_one⟩⟩

/--
descent datum 段は、既に得られた data を bundle 化するだけなので default 実装済みである。
-/
theorem primeGe5BranchAPrimitiveRestoreDescentDatum_default :
    PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p hData hLift
  exact ⟨⟨hData, hLift⟩⟩

/--
descent seed 段は、現在は datum を minimal に包み直すだけなので default 実装済みである。
-/
theorem primeGe5BranchAPrimitiveRestoreDescentSeed_default :
    PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p hDatum
  exact ⟨⟨hDatum⟩⟩

/--
realization seed 段は、現段階では元の triple を仮候補として包むだけなので default 実装済みである。
-/
theorem primeGe5BranchAPrimitiveRestoreRealizationSeed_default :
    PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p hSeed
  exact ⟨⟨hSeed, x, y, z⟩⟩

/--
residue/root 段と descent assembly 段が揃えば、
restore arithmetic core は橋だけで閉じる。

付録:
- 未完核を
  `RestoreWitnessProperties`
  以降の assembly 1 本へ押し込む canonical wrapper である。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly
    (hResidue : PrimeGe5BranchAPrimitiveRestoreResidueRootTarget)
    (hAsm : PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  have hData : RestoreWitnessProperties p x y z t s q :=
    hResidue hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p
  exact hAsm hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p hData

/--
q-adic lift 段と smaller-counterexample assembly 段が揃えば、
descent assembly は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveRestoreDescentAssembly_of_qAdicLift_and_smallerCounterexampleAssembly
    (hLift : PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget)
    (hAsm : PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget) :
    PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hData
  have hLiftSeed :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q) :=
    hLift hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData
  rcases hLiftSeed with ⟨hLiftSeed⟩
  exact hAsm hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p hData hLiftSeed

/--
descent datum 段と、datum から smaller counterexample を作る段が揃えば、
smaller-counterexample assembly は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssembly_of_descentDatum_and_fromDatum
    (hDatum : PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget)
    (hAsm : PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget) :
    PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hData hLift
  have hDatum' :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q) :=
    hDatum hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData hLift
  rcases hDatum' with ⟨hDatum'⟩
  exact hAsm hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p hDatum'

/--
descent seed 段と seed から smaller counterexample を作る段が揃えば、
datum consumer は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatum_of_descentSeed_and_fromSeed
    (hSeed : PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget)
    (hAsm : PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget) :
    PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hDatum
  have hSeed' :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q) :=
    hSeed hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hDatum
  rcases hSeed' with ⟨hSeed'⟩
  exact hAsm hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p hSeed'

/--
realization seed 段と verification 段が揃えば、
seed realization は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeed_of_realizationSeed_and_verification
    (hSeed : PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget)
    (hVerify : PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget) :
    PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed0
  have hRealization :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreRealizationSeed p x y z t s q) :=
    hSeed hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed0
  rcases hRealization with ⟨hRealization⟩
  rcases hVerify hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hRealization with ⟨hpack', hp_gap', hzlt⟩
  exact ⟨hRealization.x', hRealization.y', hRealization.z', hpack', hp_gap', hzlt⟩

end DkMath.FLT
