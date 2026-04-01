/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchAPrimitiveStrongProvider

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/-!
## Design Note

### Problem
`PacketPackagingStrong` naively takes `PrimeGe5CounterexamplePack p x' y' z'` + `p ∣ (z'-y')`
and asks for `¬ p ∣ pkt'.t`. But:

$$
\neg p \mid t' \iff v_p(z'-y') = p-1 \iff v_p(x') = 1
$$

This is NOT guaranteed from just `Pack + p ∣ gap`.

### Solution
Add `¬ p^2 ∣ x'` to the packaging input.
From the descent: `x' = x/q`, `q ≠ p`, `v_p(x) = 1` (original normal form).
So `v_p(x') = 1`, hence `¬ p^2 ∣ x'`.

### Architecture
1. `PacketPackagingStrongTarget` takes extra input `¬ p^2 ∣ x'`
2. `ArithmeticCoreStrongTarget` returns extra output `¬ p^2 ∣ x'`
3. Bridge chains them
-/

/--
strong packet packaging: `¬ p^2 ∣ x'` を追加入力として受ける。

CLAIM:
- `PrimeGe5CounterexamplePack p x' y' z'` + `p ∣ (z'-y')` + `¬ p^2 ∣ x'` + `z' < z`
  ならば `∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t`

PROOF SKETCH:
- `v_p(x') = 1` (from `p ∣ x'` and `¬ p^2 ∣ x'`)
- `v_p(z'-y') = p * v_p(x') - 1 = p - 1` (from FLT factorization)
- shape factorization gives `z'-y' = p^(p-1) * t'^p` with `v_p(t') = 0`
- hence `¬ p ∣ t'`
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget : Prop :=
  ∀ {p z x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    ¬ p ^ 2 ∣ x' →
    z' < z →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
ArithmeticCore の strong 版:
weak core の返り値に `¬ p^2 ∣ x'` を追加。

CLAIM:
- descent construction で `x' = x/q` (q ≠ p)
- original normal form: `x = p*t*s`, `¬ p ∣ t`, `¬ p ∣ s` → `v_p(x) = 1`
- `v_p(x') = v_p(x/q) = v_p(x) = 1` → `¬ p^2 ∣ x'`
-/
abbrev PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget : Prop :=
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
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z ∧ ¬ p ^ 2 ∣ x'

/--
ArithmeticCoreStrong → weak 緩和橋。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWeak_of_strong
    (hStrong : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hStrong hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, _⟩
  exact ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩

/--
ArithmeticCoreStrong の concrete provider。

descent 構成で `x' = x/q` (q ≠ p) より `v_p(x') = v_p(x) = 1`
を追加で回収する。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent
    (hWeak : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hWeak hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩
  refine ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, ?_⟩
  -- x' comes from descent: x = q * x', v_p(x) = 1, q ≠ p
  -- Therefore v_p(x') = v_p(x) = 1, so ¬ p^2 ∣ x'
  sorry

/--
core strong + packet packaging strong → RestoreFromArithmetic strong.
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_coreStrong_and_packetStrong
    (hCoreS : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget)
    (hPackS : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hCoreS hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, hx'_not_sq⟩
  exact hPackS hpack' hp_dvd_gap' hx'_not_sq hz'lt

/--
PacketPackagingStrong の concrete provider。

Claims:
- from CounterexamplePack + p ∣ gap + ¬ p^2 ∣ x' + z' < z
- derive v_p(x') = 1
- derive v_p(z'-y') = p-1
- extract t' with ¬ p ∣ t'
- build normal form packet
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hx'_not_sq hz'lt
  sorry

/--
最終 exported theorem. sorry は 2 個に分離:
1. ArithmeticCoreStrong: ¬ p^2 ∣ x' の回収
2. PacketPackagingStrong: v_p argument → packet 構成
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong
    (hWeak : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  apply primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_coreStrong_and_packetStrong
  · exact primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent hWeak
  · exact primeGe5BranchAPrimitiveRestorePacketPackagingStrong

end DkMath.FLT
