/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAFringeDescent"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
干渉縞 bundle から smaller packet を得る目標（StrongTarget 版）。

付録:
- `PrimeGe5BranchAPrimitivePacketDescentStrongTarget` は
  `pkt'.z < z ∧ ¬ p ∣ pkt'.t` を同時に返す。
- これにより `branchA_wf_contradiction_on_z` 内で `hpt'` を型から直接取り出せる。
-/
theorem branchA_smallerPacket_of_fringe
    (hStrong : PrimeGe5BranchAPrimitivePacketDescentStrongTarget)
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z ∧ ¬ p ∣ pkt'.t := by
  have hpack : PrimeGe5CounterexamplePack p x y z := hBundle.padic.pack
  exact hStrong
    hpack
    hBundle.padic.hp_dvd_gap
    hBundle.padic.hgap
    hBundle.padic.hsGN
    hBundle.padic.hsx
    hBundle.padic.hcop_ts
    hBundle.padic.hcop_ty
    hBundle.padic.hcop_sy
    hBundle.padic.hp_not_dvd_s
    hBundle.padic.hp_not_dvd_t

/--
smaller packet から再び干渉縞 bundle を構成する橋。
-/
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t)
    {q' : ℕ}
    (hqprime' : Nat.Prime q')
    (hqs' : q' ∣ pkt'.s)
    (hqt' : ¬ q' ∣ pkt'.t)
    (hcop_qy' : Nat.Coprime q' pkt'.y)
    (hq_ne_p' : q' ≠ p)
    (hData' : RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q') :
    BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  exact branchAInterferenceFringeBundle_default
    pkt'.pack
    pkt'.hp_dvd_gap
    pkt'.hgap
    pkt'.hsGN
    pkt'.hsx
    hp_not_dvd_t'
    hqprime'
    hqs'
    hqt'
    hcop_qy'
    hq_ne_p'
    hData'

/--
smaller packet から witness q' を再取得する補題（bridge）。

付録:
- Step 1: `PrimeGe5BranchACyclotomicExistenceTarget` から `q' ∣ (z'^p - y'^p) ∧ ¬ q' ∣ (z'-y')` を得る
- Step 2: `primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default` で `q' ∣ s', ¬ q' ∣ t', Coprime q' y', q' ≠ p` を no-so#rry 導出
- Step 3: `restore_witness_properties_default` で `RestoreWitnessProperties` を no-so#rry 構成
-/
theorem branchA_restoreWitness_of_smallerPacket
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t) :
    ∃ q' : ℕ,
      Nat.Prime q' ∧
      q' ∣ pkt'.s ∧
      ¬ q' ∣ pkt'.t ∧
      Nat.Coprime q' pkt'.y ∧
      q' ≠ p ∧
      RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  -- Step 1: CyclotomicExistenceTarget から distinguished prime の存在を取得
  -- q' ∣ (z'^p - y'^p) ∧ ¬ q' ∣ (z' - y')
  rcases hEx pkt'.pack pkt'.hp_dvd_gap with ⟨q', hqprime', hqdiff', hqgap'⟩
  -- z'^p - y'^p = (z' - y') * GN p (z' - y') y' の因数分解から q' ∣ GN を取り出す
  have hfactor : pkt'.z ^ p - pkt'.y ^ p = (pkt'.z - pkt'.y) * GN p (pkt'.z - pkt'.y) pkt'.y := by
    simpa using DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
      (a := pkt'.z) (b := pkt'.y) (d := p) pkt'.pack.hp.pos pkt'.pack.hyz_lt
  have hqmul' : q' ∣ (pkt'.z - pkt'.y) * GN p (pkt'.z - pkt'.y) pkt'.y := by
    rw [← hfactor]; exact hqdiff'
  have hqGN' : q' ∣ GN p (pkt'.z - pkt'.y) pkt'.y := by
    rcases (hqprime'.dvd_mul).mp hqmul' with hqgap'' | hqGN
    · exact False.elim (hqgap' hqgap'')
    · exact hqGN
  -- Step 2: DistinguishedPrimeArithmetic_default で q' ∣ s', ¬ q' ∣ t', Coprime q' y', q' ≠ p
  -- hqGN' : q' ∣ GN p (pkt'.z - pkt'.y) pkt'.y はそのまま渡せる
  have hq_arith := primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default
    pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN pkt'.hsx
    (primeGe5BranchANormalForm_coprime_ts_default pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN)
    (primeGe5BranchANormalForm_coprime_t_right pkt'.pack pkt'.hsx)
    (primeGe5BranchANormalForm_coprime_s_right pkt'.pack pkt'.hsx)
    (primeGe5BranchANormalForm_prime_not_dvd_s_default pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN)
    hp_not_dvd_t'
    (primeGe5BranchANormalForm_y_wieferich_mod_p_sq pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN)
    hqprime' hqGN' hqgap'
  obtain ⟨hqs', hqt', hcop_qy', hq_ne_p'⟩ := hq_arith
  -- Step 3: RestoreWitnessProperties を restore_witness_properties_default で構成（no so#rry）
  exact ⟨q', hqprime', hqs', hqt', hcop_qy', hq_ne_p',
    restore_witness_properties_default
      pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN pkt'.hsx
      hqprime' hqs' hqt' hcop_qy' hq_ne_p'⟩

/--
`z` に関する well-founded descent による矛盾導出。

付録:
- `PrimeGe5BranchAPrimitivePacketDescentStrongTarget` を使うことで、
  smaller packet から `pkt'.z < z ∧ ¬ p ∣ pkt'.t` を型から直接取り出せる。
- `PrimeGe5BranchACyclotomicExistenceTarget` から witness q' を再構成する。
- `Nat.find` による最小 z₀ の選択で well-founded descent を実現する。
-/
theorem branchA_wf_contradiction_on_z
    (hStrong : PrimeGe5BranchAPrimitivePacketDescentStrongTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget)
    {p : ℕ} :
    ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q := by
  classical
  intro hExists
  let P : ℕ → Prop := fun z =>
    ∃ x y t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q
  have hP : ∃ z : ℕ, P z := by
    rcases hExists with ⟨x, y, z, t, s, q, hB⟩
    exact ⟨z, ⟨x, y, t, s, q, hB⟩⟩
  let z0 : ℕ := Nat.find hP
  have hz0 : P z0 := Nat.find_spec hP
  rcases hz0 with ⟨x0, y0, t0, s0, q0, hB0⟩
  have hMin : ∀ z, P z → z0 ≤ z := by
    intro z hz
    exact Nat.find_min' hP hz
  -- StrongTarget から smaller packet と `¬ p ∣ pkt'.t` を同時に取得
  rcases branchA_smallerPacket_of_fringe hStrong hB0 with ⟨pkt', hzp, hpt'⟩
  -- CyclotomicExistenceTarget から witness q' を再構成
  rcases branchA_restoreWitness_of_smallerPacket hEx hpt' with
    ⟨q', hqprime', hqs', hqt', hcop_qy', hq_ne_p', hData'⟩
  have hB' : BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' :=
    branchA_smallerFringe_of_smallerPacket (p := p) (pkt' := pkt') hpt' (q' := q')
      hqprime' hqs' hqt' hcop_qy' hq_ne_p' hData'
  have hP' : P pkt'.z := ⟨pkt'.x, pkt'.y, pkt'.t, pkt'.s, q', hB'⟩
  have hz0le : z0 ≤ pkt'.z := hMin pkt'.z hP'
  exact Nat.not_lt_of_ge hz0le hzp


/--
干渉縞矛盾 target の確定。

付録:
- `PrimeGe5BranchAPrimitivePacketDescentStrongTarget` から `¬ p ∣ pkt'.t` を型で得る。
- `PrimeGe5BranchACyclotomicExistenceTarget` から witness q' を再構成する。
- この 2 本が揃えば、`BranchAFringeContradictionTarget` は well-founded descent で閉じる。
-/
theorem branchAFringeContradiction_of_descent
    (hStrong : PrimeGe5BranchAPrimitivePacketDescentStrongTarget)
    (hEx : PrimeGe5BranchACyclotomicExistenceTarget) :
    BranchAFringeContradictionTarget := by
  intro p x y z t s q hBundle
  have hNoInf : ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    branchA_wf_contradiction_on_z (hStrong := hStrong) (hEx := hEx) (p := p)
  have hExists : ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    ⟨x, y, z, t, s, q, hBundle⟩
  exact hNoInf hExists

end DkMath.FLT
