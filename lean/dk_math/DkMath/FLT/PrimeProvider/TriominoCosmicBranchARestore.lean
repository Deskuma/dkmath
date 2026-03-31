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
- `x' y' z'` の候補を bundle 化する。
- `x' = x / q`（`hxMul : x = q * x'`）と `y' = y`（`hyEq`）は数学的根拠により固定。
- `hzEq : x'^p + y'^p = z'^p` が `z'` の算術的定義式。
  これが RealizationSeed を "arithmetic evidence 付き入れ物" にする核心 field。
  この field の存在証明が、残存する genuinely hard kernel そのものである。
-/
structure PrimeGe5BranchAPrimitiveRestoreRealizationSeed
    (p x y z t s q : ℕ) where
  hSeed : PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q
  x' : ℕ
  y' : ℕ
  z' : ℕ
  -- x' = x / q の数学的根拠（q ∣ x から）
  hxMul : x = q * x'
  -- y' = y（arithmetic witness q は y を割らないので降下先でも y は不変）
  hyEq  : y' = y
  -- z' の算術的定義：x'^p + y'^p = z'^p を満たす p 乗根（これが本丸の evidence）
  hzEq  : x' ^ p + y' ^ p = z' ^ p

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

/-!
## VerificationTarget の 3 分割

`SmallerCounterexampleVerificationTarget` を以下の 3 段に分割する：
1. `StrictDescentTarget`      : `z' < z`
2. `GapDivisibilityTarget`    : `p ∣ (z' - y')`
3. `CounterexamplePackTarget` : `PrimeGe5CounterexamplePack p x' y' z'`

現在の未完核はこの 3 段のうち **どれが hardest kernel か** を特定する段にある。
いずれも `RealizationSeed.hxMul`（`x = q * x'`）と `hyEq`（`y' = y`）を利用できる。
-/

/--
strict descent 検証段：`hR.z' < z`。

付録:
- `x' = x / q < x ≤ z - p*... ≤ z` のような chain で示すことが期待される。
- `hR.z'^p = (x/q)^p + y^p < x^p + y^p = z^p` から `z' < z` を導く方針もある。
  （p 乗は単調なので `a^p < b^p ↔ a < b`）
- ただし `(x/q)^p + y^p = z'^p` 自体を持っていないので、現段階では target のみ。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreStrictDescentTarget : Prop :=
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
        hR.z' < z

/--
gap divisibility 検証段：`p ∣ (hR.z' - hR.y')`。

付録:
- `hR.hyEq : y' = y` により `hR.z' - hR.y' = hR.z' - y`。
- Branch A を維持するためには `p ∣ (z' - y)` が必要。
- `z'^p = (x/q)^p + y^p` と `x/q = p * t * (s/q)` から
  `z' - y ≡ 0 [MOD p]` を示す方針がある。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreGapDivisibilityTarget : Prop :=
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
        p ∣ (hR.z' - hR.y')

/--
counterexample pack 検証段：`PrimeGe5CounterexamplePack p hR.x' hR.y' hR.z'`。

付録:
- `hR.hxMul : x = q * hR.x'` と `hR.hyEq : y' = y` を使い、
  `hR.x'^p + hR.y'^p = hR.z'^p` と各種 positivity / coprimality を確認する段。
- `hR.x'^p + y^p = z'^p` が成立するかが真の核心。
  現状ではこの等式は evidence として `RealizationSeed` 内に持っていない。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreCounterexamplePackTarget : Prop :=
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
        PrimeGe5CounterexamplePack p hR.x' hR.y' hR.z'

/--
3 段の sub-verification が揃えば、verification target は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerification_of_three_parts
    (hStrictDescent : PrimeGe5BranchAPrimitiveRestoreStrictDescentTarget)
    (hGapDiv : PrimeGe5BranchAPrimitiveRestoreGapDivisibilityTarget)
    (hContrPack : PrimeGe5BranchAPrimitiveRestoreCounterexamplePackTarget) :
    PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hq_prime hqs hqt hcop_qy hq_ne_p hR
  exact ⟨hContrPack hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hq_prime hqs hqt hcop_qy hq_ne_p hR,
    hGapDiv hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hq_prime hqs hqt hcop_qy hq_ne_p hR,
    hStrictDescent hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hq_prime hqs hqt hcop_qy hq_ne_p hR⟩

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
  exact restore_witness_properties_default hpack hp_dvd_gap hgap hsGN hsx
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

/- NOTE: realization seed 構成段のターゲット。

`RealizationSeed` に `hzEq : x'^p + y'^p = z'^p` が加わったため、
このターゲットは実質的に「`(x/q)^p + y^p` の p 乗根 `z'` の存在」を要求する。
これが現在の **genuinely undischarged kernel** である。

前回までの thin-wrapper default はもはや意味を持たないため、
このターゲットはまだ open のまま保持する。

証明戦略候補:
  1. Kummer 理論経由: ℤ[ζ_p] でのイデアル分解
  2. q-adic 持ち上げ: GN の q^p 因子を使って z' を構成
  3. Cosmic Formula 独自の降下構造を使う手法（研究中）
-/

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

/-!
## hzEq を前提とした 3 つの verification 定理

`RealizationSeed.hzEq : x'^p + y'^p = z'^p` を所与として、
`StrictDescentTarget`・`GapDivisibilityTarget`・`CounterexamplePackTarget`
の 3 段を no-sorry で証明する。

これにより、genuinely undischarged kernel は `RealizationSeedTarget`
（= `(x/q)^p + y^p` の p 乗根 z' の存在）1 本へ収束する。
-/

/--
strict descent 定理：`hzEq` から `z' < z` を証明する。

証明の核心：
- `x = q * x'`, `q ≥ 2` より `x' < x`
- `z^p = q^p * x'^p + y^p` と `z'^p = x'^p + y^p` の差が `(q^p - 1) * x'^p > 0`
- `z'^p < z^p` → `z' < z` (p 乗は`ℕ`上で単調)
-/
theorem primeGe5BranchAPrimitiveRestoreStrictDescent_of_hzEq :
    PrimeGe5BranchAPrimitiveRestoreStrictDescentTarget := by
  intro p x y z t s hpack _ _ _ hsx _ _ _ _ _ _
    q hq_prime _ _ _ _ hR
  -- x' > 0
  have hx'_pos : 0 < hR.x' := by
    have hx_pos : 0 < x := Nat.pos_of_ne_zero hpack.hx0
    have : 0 < q * hR.x' := hR.hxMul ▸ hx_pos
    exact Nat.pos_of_mul_pos_left this
  -- z^p = q^p * x'^p + y^p
  have hz_pow_eq : z ^ p = q ^ p * hR.x' ^ p + hR.y' ^ p := by
    have hxp : x ^ p = q ^ p * hR.x' ^ p := by
      calc x ^ p = (q * hR.x') ^ p := by congr 1; exact hR.hxMul
        _ = q ^ p * hR.x' ^ p     := mul_pow q hR.x' p
    rw [← hpack.hEq, hxp, hR.hyEq]
  -- z'^p < z^p  (hR.z'^p = x'^p + y'^p < q^p * x'^p + y'^p = z^p)
  have hqp_ge2 : 2 ≤ q ^ p :=
    le_trans hq_prime.two_le (Nat.le_self_pow hpack.hp.ne_zero q)
  have hx'p_pos : 0 < hR.x' ^ p := pow_pos hx'_pos p
  have hz'_lt_z_pow : hR.z' ^ p < z ^ p := by
    rw [hz_pow_eq]
    linarith [hR.hzEq.symm, Nat.mul_le_mul_right (hR.x' ^ p) hqp_ge2]
  -- z'^p < z^p → z' < z
  by_contra h
  push_neg at h
  exact Nat.not_lt.mpr (Nat.pow_le_pow_left h p) hz'_lt_z_pow

/--
gap divisibility 定理：`hzEq` + フェルマーの小定理から `p ∣ (z' - y')` を証明する。

証明の核心：
1. `p ∣ x'`（`x = p*(t*s) = q*x'` と `gcd(p,q)=1` より）
2. ZMod p で Frobenius: `a^p = a` (= フェルマーの小定理)
3. `hzEq` を ZMod p へ降ろすと `z' ≡ y' (mod p)`
4. `z' ≥ y'`（`hzEq` と `x' > 0` より）→ `p ∣ (z' - y')`
-/
theorem primeGe5BranchAPrimitiveRestoreGapDivisibility_of_hzEq :
    PrimeGe5BranchAPrimitiveRestoreGapDivisibilityTarget := by
  intro p x y z t s hpack _ _ _ hsx _ _ _ _ _ _
    q hq_prime _ _ _ hq_ne_p hR
  -- Step 1: p ∣ x' (x = q*x' = p*(t*s) と gcd(p,q)=1 より)
  have hcop_pq : Nat.Coprime p q := by
    apply (Nat.Prime.coprime_iff_not_dvd hpack.hp).mpr
    intro h
    exact hq_ne_p.symm
      ((Nat.dvd_prime hq_prime).mp h |>.resolve_left hpack.hp.ne_one)
  have hp_dvd_x' : p ∣ hR.x' := by
    have h_eq : q * hR.x' = p * (t * s) := by
      rw [← hR.hxMul, hsx]
    have hp_dvd_mul : p ∣ q * hR.x' := ⟨t * s, h_eq⟩
    exact hcop_pq.dvd_of_dvd_mul_left hp_dvd_mul
  -- Step 2: ZMod p で Frobenius (フェルマーの小定理)
  haveI : Fact (Nat.Prime p) := ⟨hpack.hp⟩
  have frobenius : ∀ (a : ZMod p), a ^ p = a := fun a => by
    by_cases ha : a = 0
    · exact ha ▸ zero_pow hpack.hp.ne_zero
    · have hcard := ZMod.pow_card_sub_one_eq_one ha
      have hp_pos : 0 < p := hpack.hp.pos
      calc a ^ p = a ^ (p - 1 + 1) := by congr 1; omega
        _ = a ^ (p - 1) * a     := pow_succ a (p - 1)
        _ = 1 * a               := by rw [hcard]
        _ = a                   := one_mul a
  -- Step 3: hzEq を ZMod p へ cast — z' ≡ y' (mod p)
  have hx'_zmod : (hR.x' : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff hR.x' p).mpr hp_dvd_x'
  have hzEq_mod : (hR.z' : ZMod p) = (hR.y' : ZMod p) := by
    have h := congr_arg (Nat.cast : ℕ → ZMod p) hR.hzEq
    push_cast at h
    rw [frobenius, frobenius, frobenius, hx'_zmod, zero_add] at h
    exact h.symm
  -- Step 4: y' ≤ z' (hzEq と x' > 0 より)
  have hx'_pos : 0 < hR.x' := by
    have hx_pos : 0 < x := Nat.pos_of_ne_zero hpack.hx0
    have : 0 < q * hR.x' := hR.hxMul ▸ hx_pos
    exact Nat.pos_of_mul_pos_left this
  have hy'_le_z' : hR.y' ≤ hR.z' := by
    by_contra h
    push_neg at h
    have hlt : hR.z' ^ p < hR.y' ^ p :=
      Nat.pow_lt_pow_left h hpack.hp.ne_zero
    linarith [hR.hzEq, Nat.zero_le (hR.x' ^ p)]
  -- Step 5: p ∣ (z' - y')
  have h_sub : (↑(hR.z' - hR.y') : ZMod p) = 0 := by
    rw [Nat.cast_sub hy'_le_z']
    rw [hzEq_mod, sub_self]
  exact (ZMod.natCast_eq_zero_iff (hR.z' - hR.y') p).mp h_sub

/--
counterexample pack 定理：`hzEq` から `PrimeGe5CounterexamplePack p x' y' z'` を構成する。

証明の核心：
- `hEq` : `hzEq` そのもの
- `Coprime x' y'` : `x' ∣ x` と `hpack.hxy : Coprime x y` より
- `y' < z'` : `0 < x'` と `hzEq : x'^p + y'^p = z'^p` より
- `p ≥ 5`, `x' ≠ 0`, `y' ≠ 0`, `z' ≠ 0` : 各条件より
-/
theorem primeGe5BranchAPrimitiveRestoreCounterexamplePack_of_hzEq :
    PrimeGe5BranchAPrimitiveRestoreCounterexamplePackTarget := by
  intro p x y z t s hpack _ _ _ _ _ _ _ _ _ _
    q hq_prime _ _ _ _ hR
  -- x' > 0
  have hx'_pos : 0 < hR.x' := by
    have hx_pos : 0 < x := Nat.pos_of_ne_zero hpack.hx0
    have : 0 < q * hR.x' := hR.hxMul ▸ hx_pos
    exact Nat.pos_of_mul_pos_left this
  -- y' > 0 (= y > 0)
  have hy'_pos : 0 < hR.y' := by
    rw [hR.hyEq]; exact Nat.pos_of_ne_zero hpack.hy0
  -- Coprime x' y'
  have hcop_x'y' : Nat.Coprime hR.x' hR.y' := by
    rw [hR.hyEq]
    exact hpack.hxy.coprime_dvd_left
      ⟨q, hR.hxMul.trans (mul_comm q hR.x')⟩
  -- y' < z'
  have hy'_lt_z' : hR.y' < hR.z' := by
    have h : hR.y' ^ p < hR.z' ^ p := by
      rw [← hR.hzEq]
      linarith [pow_pos hx'_pos p]
    by_contra hle
    push_neg at hle
    exact Nat.not_lt.mpr (Nat.pow_le_pow_left hle p) h
  -- z' > 0
  have hz'_pos : 0 < hR.z' := Nat.lt_trans hy'_pos hy'_lt_z'
  -- PrimeGe5CounterexamplePack p x' y' z'
  exact {
    hp    := hpack.hp
    hxy   := hcop_x'y'
    hyz   := Nat.le_of_lt hy'_lt_z'
    hyz_lt := hy'_lt_z'
    hEq   := hR.hzEq
    hp5   := hpack.hp5
    hx0   := Nat.pos_iff_ne_zero.mp hx'_pos
    hy0   := Nat.pos_iff_ne_zero.mp hy'_pos
    hz0   := Nat.pos_iff_ne_zero.mp hz'_pos
  }

/-!
## §F. 矛盾路線（Contradiction Route）

### 設計背景

`RealizationSeedTarget` は「`(x/q)^p + y^p = z'^p` なる z' の存在」を要求する。
しかし Branch B の分析から、Branch B の z' 構成は `False.elim`
（NoWieferich bridge による前提矛盾）で行われていることが判明した。

Branch A でも同様に、前提から直接 `False` を導くのが正しい攻略路線である。
`False` が得られれば `RealizationSeedTarget` は vacuously satisfied になり、
6 段の分割チェーン全体を bypass できる。

### 数学的根拠

Branch A の前提には FLT 反例の存在が含まれる。
Wiles の定理により FLT 反例は存在しないため、前提は数学的に矛盾している。
ゆえに `ContradictionTarget` は数学的には真であるが、
Lean で形式的に証明するには Wiles 定理とは独立な矛盾源が必要。

候補:
1. Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]` と `q ≡ 1 [MOD p]` の組み合わせ
2. Kummer 理論: ℤ[ζ_p] のイデアル分解と正則素数理論
3. Cosmic Formula / GN 構造の deeper analysis

現段階ではこの矛盾源は open kernel として保持する。
-/

/--
Branch A primitive restore の前提から直接 `False` を導く target。

これは `RealizationSeedTarget`（z' の存在構成）の **代替路線** であり、
前提そのものが矛盾していることを示せば 6 段チェーン全体を bypass できる。

数学的には「FLT の反例 + Branch A 正規形 + 原始素因子の全性質」
が inconsistent であることの形式証明に相当する。

用語: 「矛盾路線」（contradiction route）。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreContradictionTarget : Prop :=
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
      False

/--
矛盾路線 → `RealizationSeedTarget`。

`False` が得られれば、z' の存在は vacuously 構成できる。
-/
theorem primeGe5BranchAPrimitiveRestoreRealizationSeed_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  have hData : RestoreWitnessProperties p x y z t s q :=
    restore_witness_properties_default
      hpack hp_dvd_gap hgap hsGN hsx
      hqprime hqs hqt hcop_qy hq_ne_p
  exact absurd
    (hContra hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData)
    id

/--
矛盾路線 → `SmallerCounterexampleFromArithmeticTarget`。

6 段チェーン全体を bypass する最も直截な bridge。
`False` が得られれば smaller counterexample は trivially 構成できる。
-/
theorem primeGe5BranchAPrimitiveSmallerCounterexampleFromArithmetic_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  have hData : RestoreWitnessProperties p x y z t s q :=
    restore_witness_properties_default
      hpack hp_dvd_gap hgap hsGN hsx
      hqprime hqs hqt hcop_qy hq_ne_p
  exact absurd
    (hContra hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData)
    id

/--
矛盾路線 → `RestoreFromArithmeticTarget`。

6 段チェーン + packet packaging を含めて全て bypass する最上位 bridge。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  have hData : RestoreWitnessProperties p x y z t s q :=
    restore_witness_properties_default
      hpack hp_dvd_gap hgap hsGN hsx
      hqprime hqs hqt hcop_qy hq_ne_p
  exact absurd
    (hContra hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData)
    id

/-!
## §Q. q-adic descent 構造補題群

`RealizationSeedTarget` の攻略に向けた足場補題。
Branch A 固有の `gap = p^{p-1}*t^p`, `GN = p*s^p`, `x = p*t*s` の構造から
q-adic 降下データを明示的に露出させる。

### 数学的背景

`q ∣ s` → `s = q * s'` と書くと：
- `GN = p * (q*s')^p = p * q^p * s'^p`
- `x = p * t * q * s' = q * (p * t * s')`（→ `x/q = p * t * s'`）
- `(x/q)^p = (p * t * s')^p = p^p * t^p * s'^p = p^p * (t*s')^p`
- `(x/q)^p + y^p = p^p * (t*s')^p + y^p`

これらの identity は `RealizationSeedTarget` を
「`p^p * (t*s')^p + y^p` が p 乗数であるか」に還元する。
-/

/--
`q ∣ s` から `s = q * s'` を明示分解する。
`s'` は `s` の q-free quotient。
-/
structure BranchAQFreeQuotient (s q : ℕ) where
  s' : ℕ
  hs_eq : s = q * s'

/--
`q ∣ s` であれば `s = q * s'` なる `s'` が取れる。
-/
def branchAQFreeQuotient_of_dvd
    {s q : ℕ} (hqs : q ∣ s) : BranchAQFreeQuotient s q := by
  exact ⟨s / q, (Nat.mul_div_cancel' hqs).symm⟩

/--
Branch A の q-adic 降下構造を明示的に束ねたデータ。

`q ∣ s` から `s = q * s'` を取り、以下の identity を同時に保持する。
-/
structure BranchAQAdicDescentData (p x y z t s q : ℕ) where
  s' : ℕ
  hs_eq  : s = q * s'
  hx_eq  : x = q * (p * (t * s'))
  hxq_eq : p * (t * s') * (p * (t * s')) ^ (p - 1) = (p * (t * s')) ^ p

/--
`RestoreWitnessProperties` + 正規形から、q-adic descent data を構成する。

`sorry` なし。
-/
def branchA_qadic_descent_data
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s))
    (_hq_prime : Nat.Prime q)
    (hqs : q ∣ s)
    (_hData : RestoreWitnessProperties p x y z t s q) :
    BranchAQAdicDescentData p x y z t s q := by
  set s' := s / q with hs'_def
  have hs_eq : s = q * s' := by
    rw [hs'_def]; exact (Nat.mul_div_cancel' hqs).symm
  have hx_eq : x = q * (p * (t * s')) := by
    rw [hsx, hs_eq]; ring
  have hxq_eq : p * (t * s') * (p * (t * s')) ^ (p - 1) = (p * (t * s')) ^ p := by
    set a := p * (t * s')
    have hp_pos : 0 < p := hpack.hp.pos
    calc a * a ^ (p - 1)
        = a ^ (p - 1) * a := by ring
      _ = a ^ (p - 1 + 1) := pow_succ a (p - 1)
      _ = a ^ p           := by congr 1; omega
  exact ⟨s', hs_eq, hx_eq, hxq_eq⟩

/--
`x = q * x'` から `x' = p * (t * s')` を回収する。

`q ∣ s` → `s = q * s'` → `x = p * t * q * s' = q * (p * t * s')` → `x/q = p * t * s'`。
-/
theorem branchA_xdiv_eq_p_mul_t_mul_s'
    {p x _y _z t s q : ℕ}
    (hsx : x = p * (t * s))
    (hqs : q ∣ s)
    (hq_prime : Nat.Prime q)
    (hxMul : x = q * x') :
    x' = p * (t * (s / q)) := by
  set s' := s / q with hs'_def
  have hs_eq : s = q * s' := by
    rw [hs'_def]; exact (Nat.mul_div_cancel' hqs).symm
  have hx_q : x = q * (p * (t * s')) := by
    rw [hsx, hs_eq]; ring
  have h_mul_eq : q * x' = q * (p * (t * s')) := by linarith
  exact Nat.eq_of_mul_eq_mul_left hq_prime.pos h_mul_eq

/--
`(x/q)^p + y^p` の展開式。

Branch A setting: `x/q = p * t * s'` なので
`(x/q)^p = (p * t * s')^p = p^p * (t * s')^p`。

ゆえに `(x/q)^p + y^p = p^p * (t * s')^p + y^p`。

この identity は、`RealizationSeedTarget` を
**「`p^p * (t*s')^p + y^p` が p 乗数であるか」**
に直接還元する。
-/
theorem branchA_xdiv_pow_expansion
    {p t s' : ℕ}
    (x' : ℕ)
    (hx'_eq : x' = p * (t * s')) :
    x' ^ p = p ^ p * (t * s') ^ p := by
  subst hx'_eq
  ring

/--
Branch A の最終還元：`z'^p = (x/q)^p + y^p` は以下と等価。

  `z'^p = p^p * (t*s')^p + y^p`

ここで `s = q * s'`。

これが `RealizationSeedTarget` の数学的核心への最小距離の identity。
-/
theorem branchA_realization_reduced_form
    {p y t s' : ℕ}
    (x' z' : ℕ)
    (hx'_eq : x' = p * (t * s'))
    (hzEq : x' ^ p + y ^ p = z' ^ p) :
    p ^ p * (t * s') ^ p + y ^ p = z' ^ p := by
  rwa [branchA_xdiv_pow_expansion x' hx'_eq] at hzEq

/-!
## 干渉縞集合 (Interference Fringe Bundle)

Branch A の二系統の構造的縞を統一的に束ねる structure 群。

- **第一縞 (p-adic head fringe)**: Branch A normal form から自動で従う p-adic 側の全制約
  - gap shape, GN shape, x-shape
  - coprimality (t ⟂ s, t ⟂ y, s ⟂ y)
  - 非整除性 (p ∤ s, p ∤ t)
  - Wieferich 条件 y^{p-1} ≡ 1 [MOD p^2]
  - head congruence s^p ≡ y^{p-1} [MOD p^2] および [MOD p^3]
  - s ≡ 1 [MOD p], s^p ≡ 1 [MOD p^2]

- **第二縞 (witness q / cyclotomic fringe)**: witness q の構造的性質
  - q の基本性質 (Prime q, q ∣ s, q ∤ t, Coprime q y, q ≠ p)
  - RestoreWitnessProperties (q ∣ x, q ∤ y, q ∤ z, q ∤ gap, p ∣ (q-1), q^p ∣ GN)

干渉縞の共存不可能性（= False）が FLT Branch A 側の本丸 open kernel。
-/

/--
Branch A の **第一縞**: p-adic head fringe。

Branch A normal form pack に加え、normal form から自動で導かれる
coprimality、非整除性、Wieferich 条件、head congruence を全て束ねる。
これらは全て既存 default 補題で sorry なしに構成可能。
-/
structure BranchAPadicFringe (p x y z t s : ℕ) : Prop where
  -- Normal form base
  pack : PrimeGe5CounterexamplePack p x y z
  hp_dvd_gap : p ∣ (z - y)
  hgap : z - y = p ^ (p - 1) * t ^ p
  hsGN : GN p (z - y) y = p * s ^ p
  hsx : x = p * (t * s)
  -- Coprimality
  hcop_ts : Nat.Coprime t s
  hcop_ty : Nat.Coprime t y
  hcop_sy : Nat.Coprime s y
  -- p-divisibility
  hp_not_dvd_s : ¬ p ∣ s
  hp_not_dvd_t : ¬ p ∣ t
  -- Wieferich condition
  hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]
  -- Head congruences
  hhead_mod_p2 : s ^ p ≡ y ^ (p - 1) [MOD p ^ 2]
  hhead_mod_p3 : s ^ p ≡ y ^ (p - 1) [MOD p ^ 3]
  -- Derived: s ≡ 1 [MOD p]
  hs_cong_one : s ≡ 1 [MOD p]
  -- Derived: s^p ≡ 1 [MOD p^2]
  hspow_cong_one : s ^ p ≡ 1 [MOD p ^ 2]

/--
Branch A の **第二縞**: witness q / cyclotomic fringe。

witness prime q の基本性質と、q から導かれる全構造的性質を束ねる。
第二縞は第一縞の存在を前提として、その上に追加的制約層を形成する。
-/
structure BranchAWitnessFringe (p x y z t s q : ℕ) : Prop where
  -- witness q basic
  hqprime : Nat.Prime q
  hqs : q ∣ s
  hqt : ¬ q ∣ t
  hcop_qy : Nat.Coprime q y
  hq_ne_p : q ≠ p
  -- Structural properties (RestoreWitnessProperties fields)
  hq_dvd_x : q ∣ x
  hq_not_dvd_y : ¬ q ∣ y
  hq_not_dvd_z : ¬ q ∣ z
  hq_not_dvd_gap : ¬ q ∣ (z - y)
  hq_cong : p ∣ (q - 1)
  hqp_dvd_GN : q ^ p ∣ GN p (z - y) y

/--
Branch A の **干渉縞集合**: p-adic head 縞と witness q 縞の全体。

FLT 反例の存在は、この bundle の全 field が同時に成立することを要求する。
逆に、FLT の Branch A 側証明とは、この bundle から `False` を導くことに他ならない。

`BranchAContradictionWithWitnessSourceTarget` は、
この束の全 field を引数として受け取り `False` を返す target と見てよい。
-/
structure BranchAInterferenceFringeBundle (p x y z t s q : ℕ) : Prop where
  padic : BranchAPadicFringe p x y z t s
  witness : BranchAWitnessFringe p x y z t s q

/--
第一縞 (p-adic fringe) の default 構成。

Branch A normal form pack とcoprime / Wieferich / head congruence は
全て既存 default 補題で自動供給される。`¬ p ∣ t` のみ外部引数。
-/
theorem branchAPadicFringe_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hsx : x = p * (t * s))
    (hp_not_dvd_t : ¬ p ∣ t) :
    BranchAPadicFringe p x y z t s where
  pack := hpack
  hp_dvd_gap := hp_dvd_gap
  hgap := hgap
  hsGN := hsGN
  hsx := hsx
  hcop_ts := primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN
  hcop_ty := primeGe5BranchANormalForm_coprime_t_right hpack hsx
  hcop_sy := primeGe5BranchANormalForm_coprime_s_right hpack hsx
  hp_not_dvd_s := primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN
  hp_not_dvd_t := hp_not_dvd_t
  hWieferich := primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN
  hhead_mod_p2 := branchA_spow_congr_head_mod_p2 hpack hp_dvd_gap hgap hsGN
  hhead_mod_p3 := branchA_spow_congr_head_mod_p3 hpack hp_dvd_gap hgap hsGN
  hs_cong_one := primeGe5BranchANormalForm_s_congr_one_mod_p hpack hp_dvd_gap hgap hsGN
  hspow_cong_one := primeGe5BranchANormalForm_spow_congr_one_mod_p_sq hpack hp_dvd_gap hgap hsGN

/--
第二縞 (witness q fringe) の default 構成。

`RestoreWitnessProperties` が構成済みなら、全 field を展開するだけ。
-/
theorem branchAWitnessFringe_of_restoreProperties
    {p x y z t s q : ℕ}
    (hqprime : Nat.Prime q)
    (hqs : q ∣ s)
    (hqt : ¬ q ∣ t)
    (hcop_qy : Nat.Coprime q y)
    (hq_ne_p : q ≠ p)
    (hData : RestoreWitnessProperties p x y z t s q) :
    BranchAWitnessFringe p x y z t s q where
  hqprime := hqprime
  hqs := hqs
  hqt := hqt
  hcop_qy := hcop_qy
  hq_ne_p := hq_ne_p
  hq_dvd_x := hData.hq_dvd_x
  hq_not_dvd_y := hData.hq_not_dvd_y
  hq_not_dvd_z := hData.hq_not_dvd_z
  hq_not_dvd_gap := hData.hq_not_dvd_gap
  hq_cong := hData.hq_cong
  hqp_dvd_GN := hData.hqp_dvd_GN

/--
干渉縞集合の一括構成。

第一縞 + 第二縞を同時に構成する。
-/
theorem branchAInterferenceFringeBundle_default
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hsx : x = p * (t * s))
    (hp_not_dvd_t : ¬ p ∣ t)
    (hqprime : Nat.Prime q)
    (hqs : q ∣ s)
    (hqt : ¬ q ∣ t)
    (hcop_qy : Nat.Coprime q y)
    (hq_ne_p : q ≠ p)
    (hData : RestoreWitnessProperties p x y z t s q) :
    BranchAInterferenceFringeBundle p x y z t s q where
  padic := branchAPadicFringe_default hpack hp_dvd_gap hgap hsGN hsx hp_not_dvd_t
  witness := branchAWitnessFringe_of_restoreProperties hqprime hqs hqt hcop_qy hq_ne_p hData

/--
干渉縞集合から `False` を導く target。

`BranchAContradictionWithWitnessSourceTarget` の bundle 版。
干渉縞集合の共存不可能性を 1 つの structure 引数で表現する。
-/
abbrev BranchAFringeContradictionTarget : Prop :=
  ∀ {p x y z t s q : ℕ},
    BranchAInterferenceFringeBundle p x y z t s q → False

/--
fringe contradiction → witness source。

bundle 版から個別引数版への unbundle。
-/
theorem branchAContradictionWithWitnessSource_of_fringeContradiction
    (hContra : BranchAFringeContradictionTarget) :
    BranchAContradictionWithWitnessSourceTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
    hq_dvd_x hq_not_dvd_y hq_not_dvd_z hq_not_dvd_gap hq_cong hqp_dvd_GN
  exact hContra ⟨
    ⟨hpack, hp_dvd_gap, hgap, hsGN, hsx,
     hcop_ts, hcop_ty, hcop_sy, hp_not_dvd_s, hp_not_dvd_t,
     hWieferich,
     branchA_spow_congr_head_mod_p2 hpack hp_dvd_gap hgap hsGN,
     branchA_spow_congr_head_mod_p3 hpack hp_dvd_gap hgap hsGN,
     primeGe5BranchANormalForm_s_congr_one_mod_p hpack hp_dvd_gap hgap hsGN,
     primeGe5BranchANormalForm_spow_congr_one_mod_p_sq hpack hp_dvd_gap hgap hsGN⟩,
    ⟨hqprime, hqs, hqt, hcop_qy, hq_ne_p,
     hq_dvd_x, hq_not_dvd_y, hq_not_dvd_z, hq_not_dvd_gap, hq_cong, hqp_dvd_GN⟩⟩

/--
witness source → fringe contradiction。

個別引数版から bundle 版への逆方向（bundle 構成を内部で行う）。
-/
theorem branchAFringeContradiction_of_witnessSource
    (hSource : BranchAContradictionWithWitnessSourceTarget) :
    BranchAFringeContradictionTarget := by
  intro p x y z t s q ⟨hP, hW⟩
  exact hSource hP.pack hP.hp_dvd_gap hP.hgap hP.hsGN hP.hsx
    hP.hcop_ts hP.hcop_ty hP.hcop_sy hP.hp_not_dvd_s hP.hp_not_dvd_t hP.hWieferich
    hW.hqprime hW.hqs hW.hqt hW.hcop_qy hW.hq_ne_p
    hW.hq_dvd_x hW.hq_not_dvd_y hW.hq_not_dvd_z hW.hq_not_dvd_gap hW.hq_cong hW.hqp_dvd_GN

/-!
### 干渉縞 Cross-Analysis

干渉縞集合の field を組み合わせて得られる cross-modular 制約。
p-adic head 展開 (`s^p = y^{p-1} + p^3 * M`) と
witness `q` の整除性 (`q ∣ s`) を結合することで、
tail 係数 `M` の q-adic 構造を決定する。

主要結果:
- `branchA_fringe_q_not_dvd_tail_coeff`: `q ∤ M`
  tail 係数は witness q に coprime。
  これは p-adic head 縞と q-adic witness 縞の干渉の直接的帰結。
- `branchA_fringe_sprime_congr_one_mod_p`: `s' ≡ 1 [MOD p]`
  q-free 商 `s' = s/q` は s と同じ mod p 合同類を保つ。
  descent の各段で mod p 合同が不変に保たれることの証拠。
-/

/--
`p ∣ (q - 1)` の `Nat.ModEq` 版: `q ≡ 1 [MOD p]`。

witness q の合同条件を ModEq 形式に変換する。
-/
theorem branchA_fringe_q_congr_one_mod_p
    {p q : ℕ}
    (hqprime : Nat.Prime q)
    (hq_cong : p ∣ (q - 1)) :
    q ≡ 1 [MOD p] :=
  ((Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr hqprime.ne_zero)).mpr hq_cong).symm

/--
干渉縞の cross-modular 制約 (基本):
`q ∣ s` のとき、head sum `y^{p-1} + p^3 * M` は `q` の倍数。
-/
theorem branchA_fringe_q_dvd_head_sum
    {p y s q M : ℕ}
    (hpack_hp : Nat.Prime p)
    (hqs : q ∣ s)
    (hexp : s ^ p = y ^ (p - 1) + p ^ 3 * M) :
    q ∣ (y ^ (p - 1) + p ^ 3 * M) := by
  rw [← hexp]
  exact dvd_pow hqs hpack_hp.ne_zero

/--
干渉縞の cross-modular 制約 (深層):
`q^p ∣ (y^{p-1} + p^3 * M)` — head sum は `q^p` の倍数。

`s^p = y^{p-1} + p^3*M` で `q ∣ s` → `q^p ∣ s^p` から従う。
v_q(y^{p-1}) = 0 かつ v_q(p^3*M) = 0 であるため、
`q^p` の深さでの整除は **二項の massive cancellation** を意味する。
-/
theorem branchA_fringe_qpow_dvd_head_sum
    {p y s q M : ℕ}
    (hqs : q ∣ s)
    (hexp : s ^ p = y ^ (p - 1) + p ^ 3 * M) :
    q ^ p ∣ (y ^ (p - 1) + p ^ 3 * M) := by
  rw [← hexp]
  exact pow_dvd_pow_of_dvd hqs p

/--
干渉縞の核心的 cross-modular 制約:
**witness `q` は tail 係数 `M` を割らない。**

`s^p = y^{p-1} + p^3 * M` で `q ∣ s` のとき、仮に `q ∣ M` ならば:
- `q ∣ (p^3 * M)` (trivial)
- `q ∣ s^p = y^{p-1} + p^3*M` (from `q ∣ s`)
- → `q ∣ y^{p-1}` → `q ∣ y` (since `q` is prime)
- しかし `q ∤ y` (witness fringe) なので矛盾。

この補題は p-adic head 縞と q-adic witness 縞の **干渉** の直接的帰結:
二系統の縞が tail 係数の q-adic 構造を完全に決定する。
-/
theorem branchA_fringe_q_not_dvd_tail_coeff
    {p y s q M : ℕ}
    (hqprime : Nat.Prime q)
    (hqs : q ∣ s)
    (hq_not_dvd_y : ¬ q ∣ y)
    (hpack_hp : Nat.Prime p)
    (hexp : s ^ p = y ^ (p - 1) + p ^ 3 * M) :
    ¬ q ∣ M := by
  intro hqM
  have h_q_dvd_sp : q ∣ s ^ p := dvd_pow hqs hpack_hp.ne_zero
  rw [hexp] at h_q_dvd_sp
  have h_q_dvd_p3M : q ∣ p ^ 3 * M := dvd_mul_of_dvd_right hqM (p ^ 3)
  have h_q_dvd_ypow : q ∣ y ^ (p - 1) := by
    have h := Nat.dvd_sub h_q_dvd_sp h_q_dvd_p3M
    simp only [add_tsub_cancel_right] at h
    exact h
  exact hq_not_dvd_y (hqprime.dvd_of_dvd_pow h_q_dvd_ypow)

/--
`q + 1 ≤ q` ではなく `1 ≤ q` を witness prime から get する補助。
-/
private theorem one_le_of_prime {q : ℕ} (hq : Nat.Prime q) : 1 ≤ q :=
  Nat.one_le_iff_ne_zero.mpr hq.ne_zero

/--
descent 不変量: q-free 商 `s'` は `s` と同じ mod `p` 合同類を保つ。

`s ≡ 1 [MOD p]` と `q ≡ 1 [MOD p]` と `s = q * s'` から
`s' ≡ 1 [MOD p]` が従う。

これは descent の各段で **mod p 合同が不変** であることの証拠:
反例からの降下操作 (`s → s' = s/q`) は
`1 [MOD p]` 合同類を保存する。
-/
theorem branchA_fringe_sprime_congr_one_mod_p
    {p s q s' : ℕ}
    (hs_cong : s ≡ 1 [MOD p])
    (hqprime : Nat.Prime q)
    (hq_cong_dvd : p ∣ (q - 1))
    (hqs : s = q * s') :
    s' ≡ 1 [MOD p] := by
  have hq_cong : q ≡ 1 [MOD p] :=
    branchA_fringe_q_congr_one_mod_p hqprime hq_cong_dvd
  have h1 : q * s' ≡ 1 [MOD p] := hqs ▸ hs_cong
  have h2 : q * s' ≡ 1 * s' [MOD p] := Nat.ModEq.mul_right s' hq_cong
  rw [one_mul] at h2
  exact h2.symm.trans h1

/--
干渉縞集合からの cross-analysis:
fringe bundle を受け取り、tail 係数の非整除性を導く統合補題。

`BranchAInterferenceFringeBundle` の field だけから、
`∃ M, s^p = y^{p-1} + p^3 * M ∧ ¬ q ∣ M` を構成する。
-/
theorem branchA_fringe_tail_coeff_coprime_to_witness
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    ∃ M : ℕ, s ^ p = y ^ (p - 1) + p ^ 3 * M ∧ ¬ q ∣ M := by
  rcases primeGe5BranchA_spow_eq_head_add_p_cube_mul
    hBundle.padic.pack hBundle.padic.hp_dvd_gap
    hBundle.padic.hgap hBundle.padic.hsGN with ⟨M, hM⟩
  exact ⟨M, hM, branchA_fringe_q_not_dvd_tail_coeff
    hBundle.witness.hqprime
    hBundle.witness.hqs
    hBundle.witness.hq_not_dvd_y
    hBundle.padic.pack.hp
    hM⟩

/--
干渉縞集合からの cross-analysis:
fringe bundle を受け取り、q-free 商の mod p 合同を導く統合補題。

`s = q * s'` (q-free quotient) なら `s' ≡ 1 [MOD p]`。
descent 不変量として、降下の各段で合同類が保存されることを示す。
-/
theorem branchA_fringe_descent_preserves_mod_p
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q)
    {s' : ℕ} (hqs : s = q * s') :
    s' ≡ 1 [MOD p] :=
  branchA_fringe_sprime_congr_one_mod_p
    hBundle.padic.hs_cong_one
    hBundle.witness.hqprime
    hBundle.witness.hq_cong
    hqs

/-!
### Witness source → Contradiction adapter

`BranchAContradictionWithWitnessSourceTarget` は witness `q` の構造的性質を
個々の引数として受け取る。これを `RestoreWitnessProperties` structure 経由で
`PrimeGe5BranchAPrimitiveRestoreContradictionTarget` に変換する thin adapter。
-/

/--
`BranchAContradictionWithWitnessSourceTarget` から
`PrimeGe5BranchAPrimitiveRestoreContradictionTarget` への thin adapter。

witness `q` の個別引数は `RestoreWitnessProperties` の各 field に対応する。
-/
theorem primeGe5BranchAPrimitiveRestoreContradiction_of_witnessSource
    (hSource : BranchAContradictionWithWitnessSourceTarget) :
    PrimeGe5BranchAPrimitiveRestoreContradictionTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hData
  exact hSource hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p
    hData.hq_dvd_x hData.hq_not_dvd_y hData.hq_not_dvd_z
    hData.hq_not_dvd_gap hData.hq_cong hData.hqp_dvd_GN

end DkMath.FLT
