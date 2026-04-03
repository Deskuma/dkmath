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

/-!
## Converse Companion: `¬ p ∣ t` ∧ `¬ p ∣ s` → `¬ p^2 ∣ x`

companion lemma の逆方向。元の正規形 side で v_p(x) = 1 を示すのに使う。
-/

/--
`x = p * (t * s)` かつ `Nat.Prime p` かつ `¬ p ∣ t` かつ `¬ p ∣ s` なら `¬ p^2 ∣ x`。

もし `p^2 ∣ p*(t*s)` なら `p ∣ (t*s)`。
素数性より `p ∣ t ∨ p ∣ s`。仮定と矛盾。
-/
theorem not_sq_dvd_of_eq_p_mul_and_not_dvd_factors
    {p x t s : ℕ}
    (hp : Nat.Prime p)
    (hsx : x = p * (t * s))
    (ht : ¬ p ∣ t)
    (hs : ¬ p ∣ s) :
    ¬ p ^ 2 ∣ x := by
  intro hp2
  -- `p^2 ∣ p*(t*s) → p ∣ (t*s)`
  rw [hsx] at hp2
  have hp_ts : p ∣ t * s := by
    rw [show p ^ 2 = p * p from by ring] at hp2
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hp.ne_zero)).mp hp2
  rcases hp.dvd_mul.mp hp_ts with hp_t | hp_s
  · exact ht hp_t
  · exact hs hp_s

/-!
## Descent Preservation: `¬ p^2 ∣ x` → `¬ p^2 ∣ x'` when `x = q * x'`

descent で `x = q * x'` なら、p^2-非整除は x' に遺伝する。
`p^2 ∣ x' → p^2 ∣ q*x' = x` の対偶。
-/

/--
`x = q * x'` かつ `¬ p^2 ∣ x` なら `¬ p^2 ∣ x'`。

対偶: `p^2 ∣ x'` → `p^2 ∣ q*x'`。
-/
theorem not_sq_dvd_of_mul_left
    {p q x x' : ℕ}
    (hx : x = q * x')
    (hx_not_sq : ¬ p ^ 2 ∣ x) :
    ¬ p ^ 2 ∣ x' := by
  intro hp2x'
  exact hx_not_sq (hx ▸ dvd_mul_of_dvd_right hp2x' q)

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
## WithProvenance Target: weak core + descent provenance を同一 witness で返す

`hWeak` と `hProv` が別の witness を返すと貼り合わせ不可能。
同一 existential の中に `x = q * x'` (provenance) を入れることで解決。
-/

/--
weak arithmetic core の witness `(x',y',z')` に
descent provenance `x = q * x'` を追加した sharpen 版。

矛盾路線を仮定**しない**非循環 route の入口。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget : Prop :=
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
        PrimeGe5CounterexamplePack p x' y' z' ∧
        p ∣ (z' - y') ∧ z' < z ∧ x = q * x'

/--
WithProvenance → weak core 緩和橋。

provenance `x = q * x'` を落とすだけ。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWeak_of_withProvenance
    (hProvCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hProvCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, _⟩
  exact ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩

/--
WithProvenance → CoreStrong。

同一 witness なので貼り合わせ不要。
1. 元の normal form: `x = p*(t*s)`, `¬p∣t`, `¬p∣s` → `¬ p^2 ∣ x`
2. descent: `x = q*x'` → `¬ p^2 ∣ x'`
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_withProvenance
    (hProvCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hProvCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, hxMul⟩
  refine ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, ?_⟩
  -- Step 1: 元の ¬ p^2 ∣ x
  have hx_not_sq : ¬ p ^ 2 ∣ x :=
    not_sq_dvd_of_eq_p_mul_and_not_dvd_factors hpack.hp hsx hp_not_dvd_t hp_not_dvd_s
  -- Step 2: descent preservation x = q*x' → ¬ p^2 ∣ x'
  exact not_sq_dvd_of_mul_left hxMul hx_not_sq

/--
ArithmeticCoreStrong: WithProvenance 経由版（非循環 route）。

WithProvenance が返す同一 witness に対して descent preservation を適用。
`_of_contradiction` ルートと異なり、矛盾を仮定しない。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent
    (hWeak : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget :=
  primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_withProvenance hWeak

/-!
## PacketPackagingStrong: so#rry #2 の分解

`so#rry` を「weak packet concrete」と「`¬ p ∣ t'` 導出」に分離する。
companion lemma が通ったので、`¬ p ∣ t'` 側は packet さえあれば自動。
残る so#rry は weak packet concrete の構成のみ。
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
  -- Step 1: shape value → `∃ t, z'-y' = p^(p-1) * t^p`
  rcases primeGe5BranchAShapeValue_of_factorization
      primeGe5BranchAShapeFactorization_default hpack' hp_dvd_gap'
    with ⟨t', hgap'⟩
  -- Step 2: of_witness → `∃ s, GN = p*s^p ∧ x' = p*(t'*s')`
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
最終 exported theorem（矛盾路線版）。

矛盾路線: `ContradictionTarget` → ex falso で全て構成。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget)
    : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  apply primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_coreStrong_and_packetStrong
  · exact primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_contradiction hContra
  · exact primeGe5BranchAPrimitiveRestorePacketPackagingStrong

/--
最終 exported theorem（非循環版）。

非循環路線: `WithProvenanceTarget` → descent preservation で `¬ p^2 ∣ x'` を導出。
矛盾を仮定しない。`WithProvenance` の concrete が取れれば、完全に非循環。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_nonCircular
    (hProvCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget)
    : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  apply primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_coreStrong_and_packetStrong
  · exact primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_withProvenance hProvCore
  · exact primeGe5BranchAPrimitiveRestorePacketPackagingStrong

/-!
## WithProvenance concrete provider chain

`WithProvenanceTarget` の concrete provider を descent chain から構成する。

### Chain 構成:
- DescentDatum_default: concrete ✅ (non-circular)
- DescentSeed_default: concrete ✅ (non-circular)
- RealizationSeedTarget: **仮定として受ける** (concrete は矛盾路線のみ)
- Verification 3段: concrete ✅ (non-circular)

`RealizationSeed.hxMul : x = q * x'` が provenance の唯一の source。
-/

/--
FromSeed の WithProvenance 版。

`RealizationSeed` が `hxMul : x = q * x'` を直接フィールドに持つので、
既存 `FromSeed` の proof に `.hxMul` を追加するだけ。
-/
theorem primeGe5BranchAPrimitiveRestoreFromSeedWithProvenance
    (hRealSeed : PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget)
    (hVerify : PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget) :
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
          PrimeGe5CounterexamplePack p x' y' z' ∧
          p ∣ (z' - y') ∧ z' < z ∧ x = q * x' := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed0
  have hRealization :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreRealizationSeed p x y z t s q) :=
    hRealSeed hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed0
  rcases hRealization with ⟨hR⟩
  rcases hVerify hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hR with ⟨hpack', hp_gap', hzlt⟩
  exact ⟨hR.x', hR.y', hR.z', hpack', hp_gap', hzlt, hR.hxMul⟩

/--
WithProvenanceTarget の concrete provider。

`RealizationSeedTarget` を仮定として受け、他は全て既存 concrete を使用。
descent chain: RestoreWitnessProperties → DescentDatum → DescentSeed → RealizationSeed → Verification
のうち、最初の 3 段は concrete default が存在し、Verification も concrete。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance_of_realizationSeed
    (hRealSeed : PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  -- Step 1: RestoreWitnessProperties を構成
  have hData : RestoreWitnessProperties p x y z t s q :=
    restore_witness_properties_default
      hpack hp_dvd_gap hgap hsGN hsx
      hqprime hqs hqt hcop_qy hq_ne_p
  -- Step 2: QAdicLiftSeed を構成
  have hLift :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed p x y z t s q) :=
    primeGe5BranchAPrimitiveRestoreQAdicLift_default
      hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData
  rcases hLift with ⟨hLift⟩
  -- Step 3: DescentDatum を構成
  have hDatum :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentDatum p x y z t s q) :=
    primeGe5BranchAPrimitiveRestoreDescentDatum_default
      hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hData hLift
  rcases hDatum with ⟨hDatum⟩
  -- Step 4: DescentSeed を構成
  have hSeed :
      Nonempty (PrimeGe5BranchAPrimitiveRestoreDescentSeed p x y z t s q) :=
    primeGe5BranchAPrimitiveRestoreDescentSeed_default
      hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hDatum
  rcases hSeed with ⟨hSeed⟩
  -- Step 5: RealizationSeed + Verification で x=q*x' を取り出す
  exact primeGe5BranchAPrimitiveRestoreFromSeedWithProvenance hRealSeed
    (primeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerification_of_three_parts
      primeGe5BranchAPrimitiveRestoreStrictDescent_of_hzEq
      primeGe5BranchAPrimitiveRestoreGapDivisibility_of_hzEq
      primeGe5BranchAPrimitiveRestoreCounterexamplePack_of_hzEq)
    hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    hqprime hqs hqt hcop_qy hq_ne_p hSeed

/-!
## RealizationSeedTarget の二分構造化

`RealizationSeedTarget` の genuine hard kernel は `hzEq : x'^p + y'^p = z'^p` のみ。
残り（x', y', hxMul, hyEq, hSeed）は bookkeeping で concrete に構成可能。

二分する:
- **quotient side**: `x' = x/q`, `y' = y` — trivial
- **p-th root side**: `∃ z', x'^p + y^p = z'^p` — genuine kernel

`PthRootTarget` が真の最終 open kernel。他は全て concrete。
-/

/--
P-th root target: descent の genuine hard kernel。

「今の Branch A descent data から生じる特殊形 `(x/q)^p + y^p` が
  perfect p-th power であるか」だけを問う。

NOTE: `x/q` は `hq_dvd_x : q ∣ x` (from `RestoreWitnessProperties`) と
`hsx : x = p*(t*s)`, `hqs : q ∣ s` から `x/q = p*(t*(s/q))` と
具体的に記述できる。ゆえに target の実質は

  ∃ z', (p*(t*(s/q)))^p + y^p = z'^p

である。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePthRootTarget : Prop :=
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
      let x' := x / q
      ∃ z' : ℕ, x' ^ p + y ^ p = z' ^ p

/--
PthRootTarget → RealizationSeedTarget 橋。

quotient side (x', y', hxMul, hyEq) は concrete に構成し、
p-th root side (hzEq) は PthRootTarget から取る。
-/
theorem primeGe5BranchAPrimitiveRestoreRealizationSeed_of_pthRoot
    (hPthRoot : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  -- quotient side: x' = x / q
  set x' := x / q with hx'_def
  have hq_dvd_x : q ∣ x := by
    rw [hsx]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hqs t) p
  have hxMul : x = q * x' := by
    rw [hx'_def]; exact (Nat.mul_div_cancel' hq_dvd_x).symm
  -- p-th root side: ∃ z', x'^p + y^p = z'^p
  rcases hPthRoot hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed with ⟨z', hzEq⟩
  -- assemble RealizationSeed
  exact ⟨⟨hSeed, x', y, z', hxMul, rfl, hzEq⟩⟩

/--
PthRootTarget → WithProvenanceTarget 一気通貫橋。

PthRootTarget → RealizationSeedTarget → WithProvenanceTarget の chain を
1 本の theorem として提供。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance_of_pthRoot
    (hPthRoot : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget :=
  primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance_of_realizationSeed
    (primeGe5BranchAPrimitiveRestoreRealizationSeed_of_pthRoot hPthRoot)

/--
PthRootTarget → 非循環 mainline 全 chain 一気通貫。

PthRootTarget → WithProvenance → CoreStrong → PacketPackagingStrong
→ RestoreFromArithmeticStrong_nonCircular
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_pthRoot
    (hPthRoot : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget :=
  primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_nonCircular
    (primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance_of_pthRoot hPthRoot)

/--
矛盾路線 → PthRootTarget（vacuously true）。

ContradictionTarget があれば全て False から出るので、PthRootTarget も vacuously 成立。
これにより既存の矛盾 route と新 PthRoot route の互換が取れる。
-/
theorem primeGe5BranchAPrimitiveRestorePthRoot_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget := by
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

/-!
## PthRootTarget の足場補題群

PthRootTarget の直接証明に向けた preparatory lemmas。
今の Branch A descent data の特殊構造を最大限に活用する。

### 数学的背景

元 FLT: `x^p + y^p = z^p` で `x = q * x'`, `x' = p * (t * s')`, `s = q * s'`。
`z^p = q^p * x'^p + y^p` から:
- `z^p - y^p = q^p * x'^p`
- `q ∤ y`, `q ∤ z`, `q ∤ (z-y)` （RestoreWitnessProperties）
- `z ≡ ω*y (mod q)` where `ω^p = 1`, `ω ≠ 1` in ZMod q

PthRootTarget が問うのは:
  `∃ z', x'^p + y^p = z'^p`
等価形: `∃ z', p^p * (t*s')^p + y^p = z'^p`

### 攻略戦略

Route B: q-adic/Hensel 持ち上げ
- `z^p ≡ y^p (mod q^p)` は FLT equation から直接
- `z^p - y^p = (z-y) * GN p (z-y) y` で `q ∤ (z-y)` → q の power は GN 側に集中
- `GN = p * s^p = p * q^p * s'^p` → q^p factor が GN から剥がれる
- この q^p stripping が descent を駆動する
-/

/--
PthRootTarget の還元形 (GN descent 等価)。

`∃ z', x'^p + y^p = z'^p` を `∃ z', p^p * (t*s')^p + y^p = z'^p` に還元。
x' = p*(t*s') の特殊構造を use。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget : Prop :=
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
      let s' := s / q
      ∃ z' : ℕ, p ^ p * (t * s') ^ p + y ^ p = z' ^ p

/--
PthRootReducedTarget → PthRootTarget 橋。

`x' = x/q = p*(t*s')` の identity を使い、reduced form から original form へ戻す。
-/
theorem primeGe5BranchAPrimitiveRestorePthRoot_of_reduced
    (hReduced : PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  set x' := x / q with hx'_def
  set s' := s / q with hs'_def
  have hq_dvd_x : q ∣ x := by
    rw [hsx]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hqs t) p
  have hxMul : x = q * x' := by
    rw [hx'_def]; exact (Nat.mul_div_cancel' hq_dvd_x).symm
  have hs_eq : s = q * s' := by
    rw [hs'_def]; exact (Nat.mul_div_cancel' hqs).symm
  have hx'_eq : x' = p * (t * s') := by
    have h : x = q * (p * (t * s')) := by rw [hsx, hs_eq]; ring
    have : q * x' = q * (p * (t * s')) := by linarith
    exact Nat.eq_of_mul_eq_mul_left hqprime.pos this
  -- hReduced は let s' := s/q を使うが、こちらの s' は s/q そのもの
  rcases hReduced hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed with ⟨z', hz'⟩
  refine ⟨z', ?_⟩
  -- hz' : p^p * (t * (s/q))^p + y^p = z'^p
  -- goal : (x/q)^p + y^p = z'^p
  -- x/q = x' = p*(t*s') と s' = s/q から
  show x' ^ p + y ^ p = z' ^ p
  rw [hx'_eq, mul_pow, mul_pow]
  -- 目標: p ^ p * (t ^ p * s' ^ p) + y ^ p = z' ^ p
  -- hz' を同じ形に変形
  convert hz' using 2
  ring

/--
PthRootTarget → PthRootReducedTarget 橋（逆方向）。

2 つの target は等価。
-/
theorem primeGe5BranchAPrimitiveRestorePthRootReduced_of_pthRoot
    (hPthRoot : PrimeGe5BranchAPrimitiveRestorePthRootTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  set x' := x / q with hx'_def
  set s' := s / q with hs'_def
  have hq_dvd_x : q ∣ x := by
    rw [hsx]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hqs t) p
  have hxMul : x = q * x' := by
    rw [hx'_def]; exact (Nat.mul_div_cancel' hq_dvd_x).symm
  have hs_eq : s = q * s' := by
    rw [hs'_def]; exact (Nat.mul_div_cancel' hqs).symm
  have hx'_eq : x' = p * (t * s') := by
    have h : x = q * (p * (t * s')) := by rw [hsx, hs_eq]; ring
    have : q * x' = q * (p * (t * s')) := by linarith
    exact Nat.eq_of_mul_eq_mul_left hqprime.pos this
  rcases hPthRoot hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed with ⟨z', hz'⟩
  refine ⟨z', ?_⟩
  -- hz' : (x/q)^p + y^p = z'^p  where x/q = x' = p*(t*s')
  -- goal : p^p * (t * (s/q))^p + y^p = z'^p
  show p ^ p * (t * s') ^ p + y ^ p = z' ^ p
  have : x' ^ p + y ^ p = z' ^ p := hz'
  rw [hx'_eq, mul_pow, mul_pow] at this
  convert this using 2
  ring

/--
PthRoot 還元形の z^p identity。

元 FLT equation `z^p = x^p + y^p` から:
`z^p = q^p * p^p * (t*s')^p + y^p`

これは `z^p = q^p * x'^p + y^p` の展開形。
-/
theorem branchA_zpow_eq_qpow_mul_reduced_plus_ypow
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s))
    (hqs : q ∣ s) :
    let s' := s / q
    z ^ p = q ^ p * (p ^ p * (t * s') ^ p) + y ^ p := by
  intro s'
  have hEq := hpack.hEq
  have hs_eq : s = q * s' := (Nat.mul_div_cancel' hqs).symm
  calc z ^ p = x ^ p + y ^ p := hEq.symm
    _ = (p * (t * s)) ^ p + y ^ p := by rw [hsx]
    _ = (p * (t * (q * s'))) ^ p + y ^ p := by rw [hs_eq]
    _ = (q * (p * (t * s'))) ^ p + y ^ p := by ring_nf
    _ = q ^ p * (p * (t * s')) ^ p + y ^ p := by rw [mul_pow]
    _ = q ^ p * (p ^ p * (t * s') ^ p) + y ^ p := by rw [mul_pow]

/-!
## GN Reduced Gap Target — Cosmic Formula native な open kernel

PthRootReducedTarget を GN (Gcd-Next 多項式) の言葉に翻訳する。

核心公式: `(g'+y)^p = g' * GN p g' y + y^p` （Cosmic Formula: Big = Body + Gap）

PthRootReduced が「∃ z', p^p*(t*s')^p + y^p = z'^p」と問うのに対し、
GNReducedGap は「∃ g', g' * GN p g' y = p^p*(t*s')^p」と問う。

g' = z' - y, z' = g' + y の関係で等価。
GN が DkMath のコア理論であるため、この形式化が project-native な攻略の起点。
-/

/--
GN Reduced Gap Target: **Cosmic Formula native な PthRootTarget の等価形式**。

「descent 後の gap g' が存在して `g' * GN p g' y = p^p * (t*s')^p` を満たす」

これは：
- `g' * GN p g' y = (g' + y)^p - y^p` （Cosmic Body = Big - Gap）
- `z' := g' + y` と置けば `z'^p = p^p*(t*s')^p + y^p` （PthRootReduced）

のため、PthRootReducedTarget と等価。GN 路線での攻略の起点。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget : Prop :=
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
      let s' := s / q
      ∃ g' : ℕ, g' * GN p g' y = p ^ p * (t * s') ^ p

/--
GNReducedGapTarget → PthRootReducedTarget 橋。

Cosmic Formula `(g'+y)^p = g' * GN p g' y + y^p` を使い、
`z' := g' + y` で p 乗根を構成する。
-/
theorem primeGe5BranchAPrimitiveRestorePthRootReduced_of_gnReducedGap
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  rcases hGNGap hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed with ⟨g', hGN⟩
  -- z' := g' + y として構成
  refine ⟨g' + y, ?_⟩
  -- Cosmic Formula: (g'+y)^p = g' * GN p g' y + y^p
  have hCosmic := DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) p g' y
  -- hCosmic : (g' + y) ^ p = g' * GN p g' y + y ^ p
  rw [hGN] at hCosmic
  -- hCosmic : (g' + y) ^ p = p ^ p * (t * (s / q)) ^ p + y ^ p
  exact hCosmic.symm

/--
PthRootReducedTarget → GNReducedGapTarget 橋（逆方向）。

`z'` が与えられたとき `g' := z' - y` で GN gap を構成。
Cosmic Formula `(g'+y)^p - y^p = g' * GN p g' y` を使って identity を得る。
-/
theorem primeGe5BranchAPrimitiveRestoreGNReducedGap_of_pthRootReduced
    (hReduced : PrimeGe5BranchAPrimitiveRestorePthRootReducedTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p hSeed
  rcases hReduced hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p hSeed with ⟨z', hz'⟩
  -- hz' : p^p * (t * (s/q))^p + y^p = z'^p
  -- z'^p ≥ y^p → z' ≥ y
  have hz'_ge_y : y ≤ z' := by
    by_contra h
    push_neg at h
    have : z' ^ p < y ^ p := Nat.pow_lt_pow_left h hpack.hp.ne_zero
    omega
  -- g' := z' - y
  refine ⟨z' - y, ?_⟩
  -- Cosmic Formula: (g'+y)^p = g' * GN p g' y + y^p
  have hCosmic := DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℕ) p (z' - y) y
  -- (z' - y + y) = z'
  rw [Nat.sub_add_cancel hz'_ge_y] at hCosmic
  -- hCosmic : z' ^ p = (z' - y) * GN p (z' - y) y + y ^ p
  omega

/--
GNReducedGapTarget → PthRootTarget 一気通貫橋。

GNReducedGap → PthRootReduced → PthRoot の chain を 1 本にまとめる。
-/
theorem primeGe5BranchAPrimitiveRestorePthRoot_of_gnReducedGap
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitiveRestorePthRootTarget :=
  primeGe5BranchAPrimitiveRestorePthRoot_of_reduced
    (primeGe5BranchAPrimitiveRestorePthRootReduced_of_gnReducedGap hGNGap)

/--
GNReducedGapTarget → RestoreFromArithmeticStrong 全 chain 直通。

GN native target から非循環 mainline 最終段までの canonical path。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_gnReducedGap
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget :=
  primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_pthRoot
    (primeGe5BranchAPrimitiveRestorePthRoot_of_gnReducedGap hGNGap)

/--
矛盾路線 → GNReducedGapTarget（vacuously true）。

ContradictionTarget → PthRoot → PthRootReduced → GNReducedGap chain。
-/
theorem primeGe5BranchAPrimitiveRestoreGNReducedGap_of_contradiction
    (hContra : PrimeGe5BranchAPrimitiveRestoreContradictionTarget) :
    PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget :=
  primeGe5BranchAPrimitiveRestoreGNReducedGap_of_pthRootReduced
    (primeGe5BranchAPrimitiveRestorePthRootReduced_of_pthRoot
      (primeGe5BranchAPrimitiveRestorePthRoot_of_contradiction hContra))

/-!
## RestoreFromArithmeticStrong → RestoreFromArithmetic (弱化橋)

StrongTarget は `∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t` を返すが、
BranchA.lean の `PrimitivePacketRestoreFromArithmeticTarget` は
`∃ pkt', pkt'.z < z` だけを要求する。

ここでは Strong → nonStrong への弱化橋を固定し、
GNReducedGapTarget から BranchA mainline への接続を確立する。
-/

/--
`RestoreFromArithmeticStrong → RestoreFromArithmetic` の弱化。

Strong 版は `¬ p ∣ pkt'.t` を追加で保証するが、
BranchA mainline の `PrimitivePacketDescentTarget` / `SmallerPacketTarget` 系では
bare `∃ pkt', pkt'.z < z` だけで十分な場面がある。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_strong
    (hStrong : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hStrong hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨pkt', hlt, _hpt'⟩
  exact ⟨pkt', hlt⟩

/--
`GNReducedGapTarget → RestoreFromArithmeticTarget` の non-circular chain。

GN native open kernel から WithProvenance → CoreStrong → Strong → nonStrong
の確立された chain を通じて、BranchA mainline の restore 入力を供給する。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_gnReducedGap
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget :=
  primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_strong
    (primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_gnReducedGap hGNGap)

/--
`GNReducedGapTarget + CyclotomicExistenceTarget → PrimitivePacketDescentTarget`

2 つの open kernel を仮定として受け取り、
primitive descent（¬p ∣ t 側）を完全に確立する conditional chain。

これにより primitive descent の残る数学核が正確に 2 本であることが定理で保証される:
1. `GNReducedGapTarget`: 新 gap の GN Body が reduced RHS に一致
2. `CyclotomicExistenceTarget`: Wieferich 条件下の原始素因子存在
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_gnReducedGap_and_cyclotomicExistence
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_existence_and_restore hEx
    (primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_gnReducedGap hGNGap)

/--
`GNReducedGapTarget + CyclotomicExistenceTarget → PrimitivePacketDescentStrongTarget`

同上だが、Strong 版（`¬ p ∣ pkt'.t` 保証付き）。
FringeDescent の well-founded descent で使う。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_gnReducedGap_and_cyclotomicExistence
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget :=
  primeGe5BranchAPrimitivePacketDescentStrong_of_zsigmondy_arithmetic_restore
    (primeGe5BranchAPrimitiveZsigmondy_of_cyclotomicPrime
      (primeGe5BranchAPrimitiveCyclotomicPrime_of_existence hEx))
    primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default
    (primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_gnReducedGap hGNGap)

/--
`GNReducedGapTarget + CyclotomicExistenceTarget → BranchAFringeContradictionTarget`

2 つの open kernel があれば、FringeDescent の well-founded descent が回り、
`BranchAInterferenceFringeBundle` が存在しえないことを確定する。
-/
theorem branchAFringeContradiction_of_gnReducedGap_and_cyclotomicExistence
    (hGNGap : PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget) :
    BranchAFringeContradictionTarget :=
  branchAFringeContradiction_of_descent
    (primeGe5BranchAPrimitivePacketDescentStrong_of_gnReducedGap_and_cyclotomicExistence
      hGNGap hEx)
    hEx

end DkMath.FLT
