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
ArithmeticCoreStrong の concrete provider（矛盾路線版）。

既存の `ArithmeticCore` は矛盾路線 (ex falso) で構成されており、
`hWeak` は `∃ x' y' z', Pack ∧ p∣gap ∧ z'<z` を返すが、
`x'` の descent provenance (`x = q*x'`) は abstract 化されている。

`¬ p^2 ∣ x'` は Pack' + p∣gap' だけからは導出不可能（円環依存）。
しかし descent の concrete（矛盾路線）では `False` から全てが出るため、
`¬ p^2 ∣ x'` も trivially 追加可能。

そこで矛盾路線から直接 `CoreStrong` を構成する。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget := by
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
ArithmeticCoreStrong: weak 経由版（互換用、descent provenance なし）。

NOTE: `¬ p^2 ∣ x'` は `hWeak` の返り値から導出不可能なため、
矛盾路線版 `_of_contradiction` を優先使用のこと。
この theorem は互換性のために残す。
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

/-!
## Companion Lemmas: `¬ p^2 ∣ x` → `¬ p ∣ t` and `¬ p ∣ s`

packet 非依存な pure arithmetic lemma として切り出す。
packet の `hsx : x = p * (t * s)` を直接差し込める。
-/

/--
`x = p * (t * s)` かつ `¬ p^2 ∣ x` ならば `¬ p ∣ t`。

もし `p ∣ t` ならば `p ∣ (t * s)` で `p^2 ∣ p * (t * s) = x`。矛盾。
-/
theorem not_dvd_left_of_mul_eq_p_mul_and_not_sq_dvd
    {p x t s : ℕ}
    (hsx : x = p * (t * s))
    (hx_not_sq : ¬ p ^ 2 ∣ x) :
    ¬ p ∣ t := by
  intro hp_t
  apply hx_not_sq
  rw [hsx]
  calc p ^ 2 = p * p := by ring
    _ ∣ p * (t * s) := by
        exact Nat.mul_dvd_mul_left p (dvd_mul_of_dvd_left hp_t s)

/--
`x = p * (t * s)` かつ `¬ p^2 ∣ x` ならば `¬ p ∣ s`。

もし `p ∣ s` ならば `p ∣ (t * s)` で `p^2 ∣ p * (t * s) = x`。矛盾。
-/
theorem not_dvd_right_of_mul_eq_p_mul_and_not_sq_dvd
    {p x t s : ℕ}
    (hsx : x = p * (t * s))
    (hx_not_sq : ¬ p ^ 2 ∣ x) :
    ¬ p ∣ s := by
  intro hp_s
  apply hx_not_sq
  rw [hsx]
  calc p ^ 2 = p * p := by ring
    _ ∣ p * (t * s) := by
        exact Nat.mul_dvd_mul_left p (dvd_mul_of_dvd_right hp_s t)

/--
まとめ版。
`x = p * (t * s)` かつ `¬ p^2 ∣ x` ならば `¬ p ∣ t ∧ ¬ p ∣ s`。
-/
theorem not_dvd_both_of_mul_eq_p_mul_and_not_sq_dvd
    {p x t s : ℕ}
    (hsx : x = p * (t * s))
    (hx_not_sq : ¬ p ^ 2 ∣ x) :
    ¬ p ∣ t ∧ ¬ p ∣ s :=
  ⟨not_dvd_left_of_mul_eq_p_mul_and_not_sq_dvd hsx hx_not_sq,
   not_dvd_right_of_mul_eq_p_mul_and_not_sq_dvd hsx hx_not_sq⟩

/--
Packet 専用の wrapper: `pkt'.hsx` と `¬ p^2 ∣ pkt'.x` から `¬ p ∣ pkt'.t`。
-/
theorem primeGe5BranchANormalFormPacket_not_dvd_t_of_not_sq_dvd_x
    {p : ℕ} (pkt' : PrimeGe5BranchANormalFormPacket p)
    (hx_not_sq : ¬ p ^ 2 ∣ pkt'.x) :
    ¬ p ∣ pkt'.t :=
  not_dvd_left_of_mul_eq_p_mul_and_not_sq_dvd pkt'.hsx hx_not_sq

/--
Packet 専用の wrapper: `pkt'.hsx` と `¬ p^2 ∣ pkt'.x` から `¬ p ∣ pkt'.s`。
-/
theorem primeGe5BranchANormalFormPacket_not_dvd_s_of_not_sq_dvd_x
    {p : ℕ} (pkt' : PrimeGe5BranchANormalFormPacket p)
    (hx_not_sq : ¬ p ^ 2 ∣ pkt'.x) :
    ¬ p ∣ pkt'.s :=
  not_dvd_right_of_mul_eq_p_mul_and_not_sq_dvd pkt'.hsx hx_not_sq

/-!
## PacketPackagingStrong: sorry #2 の分解

`sorry` を「weak packet concrete」と「`¬ p ∣ t'` 導出」に分離する。
companion lemma が通ったので、`¬ p ∣ t'` 側は packet さえあれば自動。
残る sorry は weak packet concrete の構成のみ。
-/

/--
weak packet packaging の concrete provider target。

counterexample pack + p ∣ gap + z' < z から
normal form packet を concrete に構成する。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget : Prop :=
  ∀ {p z x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    z' < z →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ pkt'.x = x'

/--
weak packet concrete: counterexample pack + p∣gap から normal form packet を構成する。

使う既存 theorem:
1. `primeGe5BranchAShapeValue_of_factorization` + `primeGe5BranchAShapeFactorization_default`
   → `∃ t, z-y = p^(p-1) * t^p`
2. `primeGe5BranchANormalForm_of_witness`
   → `∃ s, GN = p*s^p ∧ x = p*(t*s)`
3. 直接 `PrimeGe5BranchANormalFormPacket.mk` で構成
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  -- Step 1: shape value → ∃ t, z'-y' = p^(p-1) * t^p
  rcases primeGe5BranchAShapeValue_of_factorization
      primeGe5BranchAShapeFactorization_default hpack' hp_dvd_gap'
    with ⟨t', hgap'⟩
  -- Step 2: of_witness → ∃ s, GN = p*s^p ∧ x' = p*(t'*s')
  rcases primeGe5BranchANormalForm_of_witness hpack' hp_dvd_gap' hgap'
    with ⟨s', hsGN', hsx'⟩
  -- Step 3: 直接 packet を構成
  refine ⟨⟨x', y', z', t', s', hpack', hp_dvd_gap', hgap', hsGN', hsx'⟩, hz'lt, rfl⟩

/--
PacketPackagingStrong の concrete provider。

新 architecture:
1. weak concrete で `pkt'` + `pkt'.x = x'` を得る
2. `¬ p^2 ∣ x'` → `¬ p^2 ∣ pkt'.x` → companion lemma で `¬ p ∣ pkt'.t`
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hx'_not_sq hz'lt
  -- Step 1: weak concrete で packet を取る
  have hWeak : ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ pkt'.x = x' :=
    primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete hpack' hp_dvd_gap' hz'lt
  rcases hWeak with ⟨pkt', hlt, hx_eq⟩
  -- Step 2: ¬ p^2 ∣ pkt'.x を得る
  have hpkt_not_sq : ¬ p ^ 2 ∣ pkt'.x := hx_eq ▸ hx'_not_sq
  -- Step 3: companion lemma で ¬ p ∣ pkt'.t
  have hpt' : ¬ p ∣ pkt'.t :=
    primeGe5BranchANormalFormPacket_not_dvd_t_of_not_sq_dvd_x pkt' hpkt_not_sq
  exact ⟨pkt', hlt, hpt'⟩

/--
最終 exported theorem.

矛盾路線版:
- ArithmeticCoreStrong: 矛盾路線から直接構成 (no-sorry)
- PacketPackagingStrong: weak concrete + companion lemma (no-sorry)
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget)
    : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  apply primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_coreStrong_and_packetStrong
  · exact primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_contradiction hContra
  · exact primeGe5BranchAPrimitiveRestorePacketPackagingStrong

end DkMath.FLT
