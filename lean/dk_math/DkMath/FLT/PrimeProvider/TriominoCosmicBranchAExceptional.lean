/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA
import DkMath.CosmicFormula.CosmicFormulaCellDim

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

/-- `Nat.ModEq` の下での `Finset.range` 和の項別合同。 -/
private theorem sum_range_modEq
    {n q : ℕ} {f g : ℕ → ℕ}
    (hfg : ∀ i, i < n → f i ≡ g i [MOD q]) :
    ((Finset.range n).sum f) ≡ ((Finset.range n).sum g) [MOD q] := by
  induction n with
  | zero =>
      exact Nat.ModEq.rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (ih (by
        intro i hi
        exact hfg i (Nat.lt_succ_of_lt hi))).add (hfg n (Nat.lt_succ_self n))

/-!
# Triomino/Cosmic Branch A Exceptional Existence

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget` の concrete 証明を
育てるための隔離モジュール。

[CFBRC] 現段階では theorem 本体はまだ Branch A 局所 target のまま保持し、
このファイルを concrete proof の canonical 置き場とする。
`CFBRC/Bridge` への昇格は、statement が十分薄いと確認できてから後回しにする。
-/

/--
Branch A exceptional existence proof file の canonical mainline target。

[CFBRC] 現段階の concrete 証明探索は、この local theorem を埋めることを意味する。
-/
abbrev PrimeGe5BranchAExceptionalExistenceMainlineTarget : Prop :=
  PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget

/--
proof file で concrete に埋める既定の pack-local right branch target。

[CFBRC] mainline target と同値だが、
proof 実装では `boundaryCyclotomicPrimeCore .right` の形を主目標にする。
-/
abbrev PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y)

/--
Branch A exceptional proof file で次に direct に埋めるべき concrete kernel。

[CFBRC] `review-025` 以降は、この theorem 名を
pack-local right branch existence の canonical missing theorem とみなす。
-/
abbrev ExceptionalRightBoundaryCorePrimeOfWieferichTarget : Prop :=
  PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget

/--
split reference theorem の right branch だけを供給する局所 target。

[CFBRC] `review-027` 以降は、
global split theorem 全体ではなくこの right branch supply を
exceptional 側の直接の missing input とみなす。
-/
abbrev ExceptionalSplitRightBranchSupplyTarget : Prop :=
  PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget

/--
pack をほどいた後に残る boundary-normalized exceptional 供給 target。

[CFBRC] concrete 証明本文では、
まず pack 由来の bundle をここへ落とし、
その後の新数学をこの target に集約する。
-/
abbrev ExceptionalBoundaryDataRightBranchSupplyTarget : Prop :=
  CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget

/--
proof file で次に direct に本文を書く concrete theorem 名。

[CFBRC] `review-030` 以降の「boundary-normalized exceptional statement」を
この theorem 名で受ける。missing math は実質これを埋めることに等しい。
-/
abbrev ExceptionalBoundaryDataRightBranchSupplyConcreteTarget : Prop :=
  ExceptionalBoundaryDataRightBranchSupplyTarget

/--
boundary-normalized concrete theorem を、
split theorem の right branch と同じ入力形で読む local target。

[CFBRC] 本文で truly new な入力は
`d ∣ x` と Wieferich 条件の組なので、
必要ならまずこの形で concrete theorem を書いてから
通常の concrete target へ戻せばよい。
-/
abbrev ExceptionalBoundaryDataSplitRightConcreteTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    (d ∣ x ∧ u ^ (d - 1) ≡ 1 [MOD d ^ 2]) →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ∧
      ¬ q ∣ x

/--
boundary-normalized exceptional branch で truly new な差分入力 1 個。

[CFBRC] ordinary 側との違いは、最終的には
`d ∣ x`
と Wieferich 条件の組だけなので、
proof file 本文ではこの datum を first-class に扱ってよい。
-/
abbrev ExceptionalBoundaryDatum (d x u : ℕ) : Prop :=
  d ∣ x ∧ u ^ (d - 1) ≡ 1 [MOD d ^ 2]

/--
boundary-normalized concrete theorem を、
共通入力と exceptional datum 1 個に完全分離して読む local target。

[CFBRC] `review-032` の「差分入力は datum 1 個だけ」という整理を
proof file 上の theorem 名として固定する。
-/
abbrev ExceptionalBoundaryDatumConcreteTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    ExceptionalBoundaryDatum d x u →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ∧
      ¬ q ∣ x

/--
proof file の truly new math を担う exceptional-only arithmetic / CFBRC core。

[CFBRC] `review-036` 以降は、
この theorem 名を datum concrete 本体の canonical missing kernel とみなす。
-/
abbrev ExceptionalBoundaryDatumArithmeticCoreTarget : Prop :=
  ExceptionalBoundaryDatumConcreteTarget

/--
datum の連言をほどいた後に残る prepared arithmetic core target。

[CFBRC] `rcases hDatum with ⟨hdvd, hWieferich⟩`
の直後から始まる concrete 本文は、
以後この prepared 形の target として追ってよい。
-/
abbrev ExceptionalBoundaryDatumPreparedArithmeticCoreTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ∧
      ¬ q ∣ x

/--
prepared arithmetic core の concrete 本文を置く既定の theorem 名。

[CFBRC] `review-039` 以降は、
`hdvd` と `hWieferich` が分離済みの concrete body を
この theorem 名で追う。
-/
abbrev ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget : Prop :=
  ExceptionalBoundaryDatumPreparedArithmeticCoreTarget

/--
prepared concrete 本体のうち、まず prime 候補を取り出す exceptional arithmetic 部。

[CFBRC] `review-041` 以降は、
prepared concrete 本体がまだ重ければ、
まずこの part で
`Nat.Prime q ∧ ¬ q ∣ x`
を返すところまで切り分ける。
-/
abbrev ExceptionalBoundaryDatumPreparedArithmeticPartTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧ ¬ q ∣ x

/--
prepared arithmetic part の concrete 本文を置く既定の theorem 名。

[CFBRC] 以後この part を直接攻めるときは、
この theorem 名を canonical な着手点とする。
-/
abbrev ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget : Prop :=
  ExceptionalBoundaryDatumPreparedArithmeticPartTarget

/--
prepared arithmetic part の実際の witness を保持する強化版 target。

[CFBRC] `review-044` の時点で arithmetic part 本体は閉じたが、
その `q` がどこから来たかを CFBRC existence 側へ渡すには
`q ∣ x + 1`
まで持った witness-aware 版が必要になる。
-/
abbrev ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ (x + 1) ∧ ¬ q ∣ x

/--
prepared concrete 本体のうち、候補 prime が boundary core を割ることを返す CFBRC existence 部。

[CFBRC] arithmetic part で選んだ
`q`
を受け取り、
`boundaryCyclotomicPrimeCore .right`
への可除性だけを担当する局所 target。
-/
abbrev ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    ¬ q ∣ x →
    q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u

/--
prepared arithmetic part の concrete theorem 名に対する canonical proof skeleton。

[CFBRC] 次にこの part の本文を書くなら、
この theorem 名に対して
`intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich`
から入ればよい。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_part_concrete_of_self
    (hArith : ExceptionalBoundaryDatumPreparedArithmeticPartTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget :=
  hArith

/--
prepared arithmetic part の concrete 本体。

[CFBRC] arithmetic part は、
`x + 1`
の素因子を 1 つ取れば十分である。
その prime がもし
`x`
も割るなら、
差を取って
`1`
を割ってしまう。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_part_concrete
    : ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  have hx1_gt1 : 1 < x + 1 := by omega
  obtain ⟨q, hqprime, hq_dvd_x1⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hx1_gt1)
  refine ⟨q, hqprime, ?_⟩
  intro hq_dvd_x
  have hq_dvd_one : q ∣ (x + 1) - x := Nat.dvd_sub hq_dvd_x1 hq_dvd_x
  have : q ∣ 1 := by simpa using hq_dvd_one
  exact hqprime.not_dvd_one this

/--
arithmetic part の concrete 証明は、
`q ∣ x + 1`
まで保持した witness-aware 版としても読める。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_witness_concrete
    : ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  have hx1_gt1 : 1 < x + 1 := by omega
  obtain ⟨q, hqprime, hq_dvd_x1⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hx1_gt1)
  refine ⟨q, hqprime, hq_dvd_x1, ?_⟩
  intro hq_dvd_x
  have hq_dvd_one : q ∣ (x + 1) - x := Nat.dvd_sub hq_dvd_x1 hq_dvd_x
  have : q ∣ 1 := by simpa using hq_dvd_one
  exact hqprime.not_dvd_one this

/--
witness-aware arithmetic part から、旧来の arithmetic part target は忘却で従う。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_part_of_witness
    (hWitness : ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticPartTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hWitness hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, _hq_dvd_x1, hq_not_dvd_x⟩
  exact ⟨q, hqprime, hq_not_dvd_x⟩

/--
witness-aware arithmetic part を受ける CFBRC existence 部。

[CFBRC] 実際に残っている local kernel は、
`arithmetic part` が選んだ
`q ∣ x + 1`
つきの prime に対して boundary-core divisibility を返す部分である。
-/
abbrev ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u

/--
`q ∣ x + 1` を用いて boundary core を residual sum へ還元した後段 target。

[CFBRC] witness-aware existence の残核を、
`x + u ≡ u - 1 [MOD q]`
で得られる residual sum の divisibility 1 本に押し込む。
-/
abbrev ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k)

/--
residual sum divisibility を差冪そのものへ還元した後段 target。

[CFBRC] `review-046` 以降は、
残る local kernel を
`q ∣ u^d - (u - 1)^d`
の形で追ってよい。
-/
abbrev ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ u ^ d - (u - 1) ^ d

/--
差冪 divisibility を `Nat.ModEq` で読む後段 target。

[CFBRC] `review-047` 以降は、
残る local kernel を
`(u - 1)^d ≡ u^d [MOD q]`
の形で追ってもよい。
-/
abbrev ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    (u - 1) ^ d ≡ u ^ d [MOD q]

/--
diffPow `ModEq` 版の next body を、
additional local congruence kernel 1 本へ押し込む補助 target。

[CFBRC] 現時点の exceptional datum だけでは
`(u - 1)^d ≡ u^d [MOD q]`
が直ちに出るとは限らないので、
proof file ではまず「何を追加で供給すればよいか」をこの target 名に隔離する。
-/
abbrev ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    (u - 1) ^ d ≡ u ^ d [MOD q]

/--
選んだ witness prime 1 個についてだけ diffPow congruence を与える局所 target。

[CFBRC] `review-049` 以降の universal kernel は強すぎる可能性があるので、
まずは arithmetic part が実際に選ぶ
`q ∣ x + 1`
つき witness 1 個だけで downstream を閉じる weaker target も並べて追う。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ (x + 1) ∧
      ¬ q ∣ x ∧
      (u - 1) ^ d ≡ u ^ d [MOD q]

/--
選んだ witness prime 1 個が `cyclotomicPrimeCore d 1 (u - 1)` を割ることを返す CFBRC 版 target。

[CFBRC] selected-witness route の next body を、
直接の合同
`(u - 1)^d ≡ u^d [MOD q]`
ではなく
`q ∣ cyclotomicPrimeCore d 1 (u - 1)`
として追えるようにする。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ (x + 1) ∧
      ¬ q ∣ x ∧
      q ∣ DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1)

/--
arithmetic part が選んだ witness prime に対して、
`cyclotomicPrimeCore d 1 (u - 1)` divisibility を返す局所 CFBRC target。

[CFBRC] selected-core route の current missing math は、
結局この witness-aware divisibility 1 本として追えばよい。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1)

/--
選んだ witness prime に対する residual sum divisibility target。

[CFBRC] `cyclotomicPrimeCore d 1 (u - 1)` と residual sum は一致するので、
selected-core-on-witness の direct body はこの形で追ってもよい。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k)

/--
選んだ witness prime に対する差冪 divisibility target。

[CFBRC] residual sum divisibility がまだ重ければ、
selected route の direct body を
`q ∣ u^d - (u - 1)^d`
として追ってよい。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ u ^ d - (u - 1) ^ d

/--
selected diffPow-on-witness の concrete 本文を置く既定の theorem 名。

[CFBRC] `review-052` 以降、
selected route の direct body を差冪 divisibility で追うなら、
まずこの theorem 名を canonical な着手点とする。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget : Prop :=
  ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget

/--
選んだ witness prime 1 個についての差冪 divisibility を返す existential 版 target。

[CFBRC] arithmetic witness と直接噛ませたいときは、
universal on-witness 版よりこちらの方が direct body に近い。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget : Prop :=
  ∀ {d x u : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ (x + 1) ∧
      ¬ q ∣ x ∧
      q ∣ u ^ d - (u - 1) ^ d

/--
selected diffPow witness の concrete 本文を置く既定の theorem 名。
-/
abbrev ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget : Prop :=
  ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget

/--
proof file で practical entrance として使う canonical concrete theorem 名。

[CFBRC] official direct body は
`ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget`
に残すが、
実際の本文探索はまず existential witness 版のこちらを入口として進めてよい。
-/
abbrev PrimeGe5BranchAExceptionalPracticalConcreteTarget : Prop :=
  ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget

/--
practical entrance の witness supply 部を表す local target。

[CFBRC] practical entrance は existential 版なので、
missing math を分けて読むなら
まず `q ∣ x + 1` を返すこの供給部と、
その `q` で差冪 divisibility を返す on-witness body に分かれる。
-/
abbrev PrimeGe5BranchAExceptionalPracticalWitnessSupplyTarget : Prop :=
  ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget

/--
practical entrance の on-witness body 部を表す local target。

[CFBRC] witness supply は既に concrete 実装済みなので、
practical entrance の truly new body は実質この on-witness 版として追える。
-/
abbrev PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget : Prop :=
  ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget

/--
practical body-on-witness の concrete 本文を置く既定の theorem 名。

[CFBRC] practical route の truly new body を直接書くなら、
まずこの theorem 名を canonical な着手点とする。
-/
abbrev PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget : Prop :=
  PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget

/--
practical body-on-witness を `GN d 1 (u - 1)` divisibility で読む local target。

[CFBRC] `u^d - (u-1)^d = GN d 1 (u-1)` なので、
on-witness body は宇宙式の `GN` slice としても追える。
-/
abbrev PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget : Prop :=
  ∀ {d x u q : ℕ}, Nat.Prime d → 5 ≤ d →
    0 < x → 0 < u →
    Nat.Coprime x u →
    d ∣ x →
    u ^ (d - 1) ≡ 1 [MOD d ^ 2] →
    Nat.Prime q →
    q ∣ (x + 1) →
    ¬ q ∣ x →
    q ∣ DkMath.CosmicFormulaBinom.GN d 1 (u - 1)

/--
practical body-on-witness を `Nat.ModEq` で読む local target。

[CFBRC] diffPow divisibility の本文を合同の顔でも追えるようにするため、
current missing body の同値な別読みとしてこれも保持する。
-/
abbrev PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqTarget : Prop :=
  ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget

/--
practical `ModEq` body の concrete 本文を置く既定の theorem 名。
-/
abbrev PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget : Prop :=
  PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqTarget

/--
practical GN slice の concrete 本文を置く既定の theorem 名。

[CFBRC] diffPow body を main target から外さず、
同値な `GN d 1 (u - 1)` 側の concrete 入口としてこれを使う。
-/
abbrev PrimeGe5BranchAExceptionalPracticalGNConcreteTarget : Prop :=
  PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget

/--
practical entrance の canonical self bridge。
-/
theorem primeGe5BranchAExceptionalPracticalConcrete_of_self
    (hDiff : PrimeGe5BranchAExceptionalPracticalConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  hDiff

/--
practical entrance は、
witness supply と on-witness body が揃えば橋だけで閉じる。
-/
theorem primeGe5BranchAExceptionalPracticalConcrete_of_witnessSupply_and_bodyOnWitness
    (hWitness : PrimeGe5BranchAExceptionalPracticalWitnessSupplyTarget)
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hWitness hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  exact hBody hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
concrete arithmetic witness は既にあるので、
practical entrance の missing body を on-witness concrete 1 本として読んでよい。
-/
theorem primeGe5BranchAExceptionalPracticalConcrete_of_bodyOnWitness
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  primeGe5BranchAExceptionalPracticalConcrete_of_witnessSupply_and_bodyOnWitness
    exceptional_boundary_datum_prepared_arithmetic_witness_concrete
    hBody

/--
practical body-on-witness concrete theorem 名に対する canonical self bridge。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitnessConcrete_of_self
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget :=
  hBody

/--
`GN d 1 (u - 1)` divisibility があれば、
practical body-on-witness は直ちに従う。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitness_of_GN
    (hGN : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hEq : u ^ d - (u - 1) ^ d = DkMath.CosmicFormulaBinom.GN d 1 (u - 1) := by
    simpa [hu_eq] using
      (DkMath.CosmicFormulaCellDim.pow_sub_pow_eq_mul_GN d 1 (u - 1))
  rw [hEq]
  exact hGN hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
practical body-on-witness が立てば、
同じ内容を `GN d 1 (u - 1)` divisibility としても読める。
-/
theorem primeGe5BranchAExceptionalPracticalGN_of_bodyOnWitness
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hEq : u ^ d - (u - 1) ^ d = DkMath.CosmicFormulaBinom.GN d 1 (u - 1) := by
    simpa [hu_eq] using
      (DkMath.CosmicFormulaCellDim.pow_sub_pow_eq_mul_GN d 1 (u - 1))
  rw [← hEq]
  exact hBody hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
practical body-on-witness の `Nat.ModEq` 読みがあれば、
divisibility 版の practical body は直ちに従う。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitness_of_ModEq
    (hMod : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).mp
    (hMod hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x)

/--
practical body-on-witness が立てば、
同じ内容を `Nat.ModEq` の practical body としても読める。
-/
theorem primeGe5BranchAExceptionalPracticalModEq_of_bodyOnWitness
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).2
    (hBody hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x)

/--
practical `ModEq` concrete theorem 名に対する canonical self bridge。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcrete_of_self
    (hMod : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget :=
  hMod

/--
practical `ModEq` concrete theorem 名が立てば、
practical body-on-witness concrete theorem 名にも直接戻れる。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitnessConcrete_of_ModEqConcrete
    (hMod : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget :=
  primeGe5BranchAExceptionalPracticalBodyOnWitness_of_ModEq hMod

/--
practical body-on-witness concrete theorem 名が立てば、
同じ内容を practical `ModEq` concrete theorem 名としても読める。
-/
theorem primeGe5BranchAExceptionalPracticalModEqConcrete_of_bodyOnWitnessConcrete
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget :=
  primeGe5BranchAExceptionalPracticalModEq_of_bodyOnWitness hBody

/--
practical GN concrete theorem 名に対する canonical self bridge。
-/
theorem primeGe5BranchAExceptionalPracticalGNConcrete_of_self
    (hGN : PrimeGe5BranchAExceptionalPracticalGNConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalGNConcreteTarget :=
  hGN

/--
practical GN concrete theorem 名が立てば、
practical body-on-witness concrete theorem 名にも直接戻れる。
-/
theorem primeGe5BranchAExceptionalPracticalBodyOnWitnessConcrete_of_GNConcrete
    (hGN : PrimeGe5BranchAExceptionalPracticalGNConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget :=
  primeGe5BranchAExceptionalPracticalBodyOnWitness_of_GN hGN

/--
practical body-on-witness concrete theorem 名が立てば、
同じ内容を practical GN concrete theorem 名としても読める。
-/
theorem primeGe5BranchAExceptionalPracticalGNConcrete_of_bodyOnWitnessConcrete
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalGNConcreteTarget :=
  primeGe5BranchAExceptionalPracticalGN_of_bodyOnWitness hBody

/-- `cyclotomicPrimeCore d 1 (u - 1)` は residual sum に一致する。 -/
private theorem cyclotomicPrimeCore_one_pred_eq_residual_sum
    (d u : ℕ) (hu : 0 < u) :
    DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1) =
      ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k) := by
  let f : ℕ → ℕ := fun k => u ^ k * (u - 1) ^ (d - 1 - k)
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  calc
    DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1)
        = ∑ k ∈ Finset.range d, f k := by
            unfold DkMath.CFBRC.cyclotomicPrimeCore
            simp [f, hu_eq]
    _ = ∑ k ∈ Finset.range d, f (d - 1 - k) := by
          simpa using (Finset.sum_range_reflect f d).symm
    _ = ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_lt : k < d := Finset.mem_range.1 hk
          have h1 : d - 1 - (d - 1 - k) = k := by omega
          have h2 : d - 1 - k = d - 1 - k := rfl
          dsimp [f]
          rw [h1, h2, mul_comm]

/--
ordinary branch における boundary-core prime existence の reference theorem。

[CFBRC] exceptional proof は、この ordinary theorem と仮定・中間結論を
1 対 1 で対応させながら起こすのを基本方針とする。
-/
theorem cfbrcBoundaryCorePrimeExistence_reference
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 5 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime x u)
    (hOrd : ¬ d ∣ x) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ∧
      ¬ q ∣ x := by
  have hd_ge3 : 3 ≤ d := by omega
  rcases DkMath.CFBRC.exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime
      DkMath.CFBRC.BoundarySide.right
      (d := d) (x := x) (u := u)
      hd_prime hd_ge3 hx hu hcop hOrd with
    ⟨q, hqprime, hqcore, hq_not_dvd_x, _hprim⟩
  exact ⟨q, hqprime, hqcore, hq_not_dvd_x⟩

/--
Branch A local exceptional proof で直接使う boundary-normalized input bundle。

[CFBRC] concrete proof 本体では、まず pack からこの形へ落としてから
ordinary reference theorem と比較する。
-/
theorem primeGe5BranchAExceptionalBoundaryData_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    Nat.Prime p ∧ 5 ≤ p ∧ 0 < (z - y) ∧ 0 < y ∧
      Nat.Coprime (z - y) y ∧
      p ∣ (z - y) ∧
      y ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  exact ⟨hpack.hp, hpack.hp5, hpack.gap_pos, hpack.y_pos,
    hpack.gap_coprime_right, hp_dvd_gap, hWieferich⟩

/--
proof file mainline target から、
Branch A の pack-local な boundary-core existence は直接回収できる。

[CFBRC] concrete proof をこのファイルで進める際の first reduction。
-/
theorem primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_mainline
    (hMain : PrimeGe5BranchAExceptionalExistenceMainlineTarget)
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y) := by
  rcases hMain hpack hp_dvd_gap hWieferich with
    ⟨q, hqprime, hqcore, hq_not_dvd_gap⟩
  refine ⟨q, hqprime, ?_, hq_not_dvd_gap⟩
  simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hqcore

/--
split reference theorem があれば、
Branch A exceptional pack 上の boundary-core existence は right branch 評価で従う。

[CFBRC] 以後の concrete 証明は、
通常枝 `¬ d ∣ x` を reference theorem で閉じ、
例外枝だけを local mainline で埋める構図で読める。
-/
theorem primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget)
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y) := by
  exact hSplit hpack.hp hpack.hp5 hpack.gap_pos hpack.y_pos
    hpack.gap_coprime_right (Or.inr ⟨hp_dvd_gap, hWieferich⟩)

/--
named concrete kernel があれば、
proof file の pack-local main target はそのまま閉じる。

[CFBRC] 今後は concrete 証明本体をこの theorem 名で積み、
target 名は bridge 越しにだけ参照する。
-/
theorem primeGe5BranchAExceptionalPackLocalBoundaryExistence_of_namedKernel
    (hKernel : ExceptionalRightBoundaryCorePrimeOfWieferichTarget) :
    PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget :=
  hKernel

/--
proof file mainline target があれば、
named concrete kernel は right branch 抽出として回収できる。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_mainline
    (hMain : PrimeGe5BranchAExceptionalExistenceMainlineTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_mainline hMain

/--
named concrete kernel の proof skeleton。

[CFBRC] `boundaryData_default` で pack 由来の入力を一括抽出し、
split reference theorem の right branch に流す形を
proof file 上の canonical skeleton として固定する。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  rcases primeGe5BranchAExceptionalBoundaryData_default
      hpack hp_dvd_gap hWieferich with
    ⟨hp, hp5, hgap_pos, hy_pos, hcop_gap_y, hp_dvd_gap, hWieferich⟩
  exact hSplit hp hp5 hgap_pos hy_pos hcop_gap_y
    (Or.inr ⟨hp_dvd_gap, hWieferich⟩)

/--
right branch supply 自体の proof skeleton。

[CFBRC] 以後の concrete 証明本文は、
まずこの theorem 名で書いてから named kernel / mainline へ戻せばよい。
-/
theorem exceptional_split_right_branch_supply_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalSplitRightBranchSupplyTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  rcases primeGe5BranchAExceptionalBoundaryData_default
      hpack hp_dvd_gap hWieferich with
    ⟨hp, hp5, hgap_pos, hy_pos, hcop_gap_y, hp_dvd_gap, hWieferich⟩
  exact hSplit hp hp5 hgap_pos hy_pos hcop_gap_y
    (Or.inr ⟨hp_dvd_gap, hWieferich⟩)

/--
boundary-normalized exceptional supply があれば、
pack-local right branch supply は bundle 展開だけで従う。

[CFBRC] これにより、
pack の解体と exceptional arithmetic / CFBRC 本体の責務を分離できる。
-/
theorem exceptional_split_right_branch_supply_of_boundaryData
    (hBoundary : ExceptionalBoundaryDataRightBranchSupplyTarget) :
    ExceptionalSplitRightBranchSupplyTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  exact hBoundary hpack.hp hpack.hp5 hpack.gap_pos hpack.y_pos
    hpack.gap_coprime_right hp_dvd_gap hWieferich

/--
boundary-normalized concrete theorem 名から pack-local right branch supply を回収する橋。

[CFBRC] concrete proof 本体はまずこの theorem 名で書き、
pack-local supply への復元はこの薄い橋に任せればよい。
-/
theorem exceptional_split_right_branch_supply_of_boundaryConcrete
    (hBoundary : ExceptionalBoundaryDataRightBranchSupplyConcreteTarget) :
    ExceptionalSplitRightBranchSupplyTarget :=
  exceptional_split_right_branch_supply_of_boundaryData hBoundary

/--
split-right 形の concrete theorem 名から、
通常の boundary-normalized concrete target へ戻る橋。

[CFBRC] concrete 本文を split theorem と完全に同じ right-branch 入力で
書きたい場合の canonical reducer。
-/
theorem exceptional_boundaryData_right_branch_supply_concrete_of_splitRight
    (hRight : ExceptionalBoundaryDataSplitRightConcreteTarget) :
    ExceptionalBoundaryDataRightBranchSupplyConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  exact hRight hd_prime hd_ge hx hu hcop ⟨hdvd, hWieferich⟩

/--
exceptional datum 形の concrete theorem 名から、
split-right concrete target へ戻る橋。
-/
theorem exceptional_boundaryData_splitRight_concrete_of_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalBoundaryDataSplitRightConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hExc
  exact hDatum hd_prime hd_ge hx hu hcop hExc

/--
exceptional-only arithmetic / CFBRC core から datum concrete target へ戻る橋。
-/
theorem exceptional_boundary_datum_concrete_of_arithmeticCore
    (hCore : ExceptionalBoundaryDatumArithmeticCoreTarget) :
    ExceptionalBoundaryDatumConcreteTarget :=
  hCore

/--
split theorem から arithmetic core へ入る canonical skeleton。

[CFBRC] proof file で concrete 本文を差し替える位置は
最終的にはこの theorem 名だとみなし、
現在は split assembler から供給する。
-/
theorem exceptional_boundary_datum_arithmetic_core_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalBoundaryDatumArithmeticCoreTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  exact hSplit hd_prime hd_ge hx hu hcop (Or.inr ⟨hdvd, hWieferich⟩)

/--
split theorem から prepared arithmetic core へ入る canonical skeleton。

[CFBRC] concrete proof を `hdvd` と `hWieferich` が分かれた形から
起こしたいときは、まずこの theorem 名を入口にすればよい。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  exact hSplit hd_prime hd_ge hx hu hcop (Or.inr ⟨hdvd, hWieferich⟩)

/--
prepared arithmetic core から canonical arithmetic core へ戻る橋。

[CFBRC] 今後の concrete 本文は、
この theorem を通じて `ExceptionalBoundaryDatumArithmeticCoreTarget`
へ接続すれば十分である。
-/
theorem exceptional_boundary_datum_arithmetic_core_of_prepared
    (hPrepared : ExceptionalBoundaryDatumPreparedArithmeticCoreTarget) :
    ExceptionalBoundaryDatumArithmeticCoreTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  exact hPrepared hd_prime hd_ge hx hu hcop hdvd hWieferich

/--
prepared arithmetic core の concrete theorem 名から、
canonical prepared target へ戻る橋。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_of_concrete
    (hConcrete : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreTarget :=
  hConcrete

/--
prepared concrete 本体は、
exceptional arithmetic part と CFBRC existence part の合成で閉じられる。

[CFBRC] 以後 prepared body が重ければ、
missing math はこの 2 part に割って追えばよい。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_parts
    (hArith : ExceptionalBoundaryDatumPreparedArithmeticPartTarget)
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hArith hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_not_dvd_x⟩
  exact ⟨q, hqprime,
    hCFBRC hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_not_dvd_x,
    hq_not_dvd_x⟩

/--
prepared arithmetic part の concrete theorem 名と CFBRC existence part があれば、
prepared concrete 本体は閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_arithmeticConcrete_and_cfbrc
    (hArith : ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget)
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_parts
    (exceptional_boundary_datum_prepared_arithmetic_part_concrete_of_self hArith)
    hCFBRC

/--
witness-aware arithmetic part と witness-aware CFBRC existence part からも、
prepared concrete 本体は閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_witnessAndCFBRC
    (hWitness : ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget)
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hWitness hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x⟩
  exact ⟨q, hqprime,
    hCFBRC hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x,
    hq_not_dvd_x⟩

/--
residual sum divisibility があれば、witness-aware CFBRC existence は boundary core へ戻せる。

[CFBRC] `q ∣ x + 1` から
`x + u ≡ u - 1 [MOD q]`
を得て、boundary core の各項を residual sum の各項へ項別合同で落とす。
-/
theorem exceptional_boundary_datum_prepared_cfbrc_existence_on_witness_of_residual
    (hResidual : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hx1_mod0 : x + 1 ≡ 0 [MOD q] := hq_dvd_x1.modEq_zero_nat
  have hxu_mod : x + u ≡ u - 1 [MOD q] := by
    have htmp := hx1_mod0.add_right (u - 1)
    have hu_eq : 1 + (u - 1) = u := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hu_eq] using htmp
  have hsum_mod :
      DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ≡
        ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k) [MOD q] := by
    unfold DkMath.CFBRC.boundaryCyclotomicPrimeCore DkMath.CFBRC.cyclotomicPrimeCore
    exact sum_range_modEq (fun k hk =>
      ((hxu_mod.pow k).mul_right (u ^ (d - 1 - k))))
  have hres0 :
      (∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k)) ≡ 0 [MOD q] :=
    (hResidual hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x).modEq_zero_nat
  exact Nat.modEq_zero_iff_dvd.mp (hsum_mod.trans hres0)

/--
差冪 divisibility があれば residual sum divisibility は従う。

[CFBRC] `u^d - (u - 1)^d`
を `cyclotomicPrimeCore d 1 (u - 1)` に戻し、
それを residual sum の表示へ読み替えるだけでよい。
-/
theorem exceptional_boundary_datum_prepared_cfbrc_residual_on_witness_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hq_dvd_core : q ∣ DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1) := by
    have hq_dvd_diff : q ∣ (1 + (u - 1)) ^ d - (u - 1) ^ d := by
      simpa [hu_eq] using
        hDiff hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
    exact DkMath.CFBRC.prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
      hqprime hq_dvd_diff hqprime.not_dvd_one
  rw [cyclotomicPrimeCore_one_pred_eq_residual_sum d u hu] at hq_dvd_core
  exact hq_dvd_core

/--
`Nat.ModEq` 版の差冪 target から divisibility 版の差冪 target を回収する橋。
-/
theorem exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).mp
    (hMod hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x)

/--
additional congruence kernel が立てば、diffPow の `ModEq` target はそのまま閉じる。

[CFBRC] current proof file では、
next body をまずこの congruence kernel 名で切っておけばよい。
-/
theorem exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget :=
  hKernel

/--
universal congruence kernel があれば、selected-witness 版は concrete arithmetic witness で直ちに従う。

[CFBRC] current proof exploration では selected-witness 版を主戦場にしたいので、
stronger な universal kernel からこちらへ落とす標準橋を先に置いておく。
-/
theorem exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases exceptional_boundary_datum_prepared_arithmetic_witness_concrete
      hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  exact hKernel hd_prime hd_ge hx hu hcop hdvd hWieferich
    hqprime hq_dvd_x1 hq_not_dvd_x

/--
選んだ witness prime が `cyclotomicPrimeCore d 1 (u - 1)` を割れば、
selected-witness congruence は従う。

[CFBRC] 既存の
`prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
を
`x := 1`, `u := u - 1`
に適用するだけでよい。
-/
theorem exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedCoreWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hCore hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, hq_dvd_core⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  have hq_dvd_diff : q ∣ (1 + (u - 1)) ^ d - (u - 1) ^ d := by
    exact (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
      (p := d) (x := 1) (u := u - 1) (q := q) hqprime hqprime.not_dvd_one).2 hq_dvd_core
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hDiff : q ∣ u ^ d - (u - 1) ^ d := by
    simpa [hu_eq] using hq_dvd_diff
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).2 hDiff

/--
witness-aware core divisibility があれば、selected-core witness target は concrete arithmetic witness で従う。

[CFBRC] selected route の missing theorem を
`∃ q ...`
全体ではなく、
選んだ witness 上の core divisibility 1 本へ押し込むための橋。
-/
theorem exceptional_boundary_datum_prepared_selectedCoreWitness_of_onWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases exceptional_boundary_datum_prepared_arithmetic_witness_concrete
      hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  exact hCore hd_prime hd_ge hx hu hcop hdvd hWieferich
    hqprime hq_dvd_x1 hq_not_dvd_x

/--
差冪 divisibility があれば、selected-core-on-witness target は直接従う。

[CFBRC] selected route を最後に支えている core divisibility は、
実際には既存の diffPow route から即座に回収できる。
-/
theorem exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hq_dvd_diff : q ∣ (1 + (u - 1)) ^ d - (u - 1) ^ d := by
    simpa [hu_eq] using
      hDiff hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  exact DkMath.CFBRC.prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
    hqprime hq_dvd_diff hqprime.not_dvd_one

/--
selected residual-on-witness があれば、selected core-on-witness は表示変換だけで従う。
-/
theorem exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_selectedResidual
    (hResidual : ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  rw [cyclotomicPrimeCore_one_pred_eq_residual_sum d u hu]
  exact hResidual hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
既存の residual-on-witness route があれば、selected residual-on-witness も直ちに従う。
-/
theorem exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_residual
    (hResidual : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  exact hResidual hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
差冪 divisibility があれば、selected residual-on-witness は既存 route を通じて従う。
-/
theorem exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_residual
    (exceptional_boundary_datum_prepared_cfbrc_residual_on_witness_of_diffPow hDiff)

/--
差冪 `ModEq` 版があれば、selected residual-on-witness は従う。
-/
theorem exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel があれば、selected residual-on-witness は従う。
-/
theorem exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
selected diffPow-on-witness があれば、selected residual-on-witness は従う。
-/
theorem exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_selectedDiffPow
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_diffPow hDiff

/--
既存の diffPow-on-witness route は、そのまま selected diffPow-on-witness としても読める。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget := by
  intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x
  exact hDiff hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
既存の diffPow `ModEq` route は、そのまま selected diffPow-on-witness へ落ちる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel は、そのまま selected diffPow-on-witness まで落とせる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
selected diffPow-on-witness の concrete theorem 名に対する canonical proof skeleton。

[CFBRC] direct body を差冪 divisibility で書くなら、
この theorem 名に対して
`intro d x u q hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x`
から入ればよい。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_concrete
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget :=
  hDiff

/--
selected diffPow-on-witness の concrete theorem 名に対する canonical self bridge。

[CFBRC] direct body をこの concrete 名で実装したあと、
以後の wrapper はまずこの theorem を起点に辿ればよい。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitnessConcrete_of_self
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget :=
  hDiff

/--
既存の diffPow-on-witness route は、
selected diffPow concrete theorem 名としてもそのまま読める。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitnessConcrete_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPow hDiff

/--
既存の diffPow `ModEq` route は、
selected diffPow concrete theorem 名へも直接落とせる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitnessConcrete_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPowModEq hMod

/--
additional congruence kernel が立てば、
selected diffPow concrete theorem 名まで直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowOnWitnessConcrete_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_congruenceKernel hKernel

/--
selected diffPow-on-witness があれば、arithmetic witness の既定値で existential diffPow witness 版も従う。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedDiffPowOnWitness
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases exceptional_boundary_datum_prepared_arithmetic_witness_concrete
      hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  exact hDiff hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x

/--
選んだ witness prime 1 個について差冪 divisibility があれば、
selected-witness congruence は直ちに従う。
-/
theorem exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedDiffPowWitness
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hDiff hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, hq_dvd_diff⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).2 hq_dvd_diff

/--
選んだ witness prime 1 個についての congruence があれば、
existential diffPow witness 版も直ちに従う。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCongruenceWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hSel hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, hq_mod⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  exact (Nat.modEq_iff_dvd' hle).mp hq_mod

/--
選んだ witness prime が `cyclotomicPrimeCore d 1 (u - 1)` を割れば、
existential diffPow witness 版も直接従う。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hCore hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, hq_dvd_core⟩
  refine ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, ?_⟩
  have hq_dvd_diff : q ∣ (1 + (u - 1)) ^ d - (u - 1) ^ d := by
    exact (DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat
      (p := d) (x := 1) (u := u - 1) (q := q) hqprime hqprime.not_dvd_one).2 hq_dvd_core
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  simpa [hu_eq] using hq_dvd_diff

/--
witness-aware core divisibility があれば、
existential diffPow witness 版は concrete arithmetic witness を通じて従う。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreOnWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreWitness
    (exceptional_boundary_datum_prepared_selectedCoreWitness_of_onWitness hCore)

/--
selected diffPow witness concrete theorem 名に対する canonical self bridge。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_self
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  hDiff

/--
official direct body の concrete theorem 名が立てば、
practical entrance の concrete theorem 名へも直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_selectedDiffPowConcrete
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedDiffPowOnWitness hDiff

/--
selected-witness congruence からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_selectedCongruenceWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCongruenceWitness hSel

/--
selected core witness からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_selectedCoreWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreWitness hCore

/--
witness-aware selected core divisibility からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_selectedCoreOnWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreOnWitness hCore

/--
差冪 divisibility からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedDiffPowOnWitness
    (exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPow hDiff)

/--
差冪 `ModEq` 版からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_practicalConcrete_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel からも、
practical entrance の concrete theorem 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_practicalConcrete_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    PrimeGe5BranchAExceptionalPracticalConcreteTarget :=
  exceptional_boundary_datum_prepared_practicalConcrete_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
selected diffPow-on-witness からは、existential diffPow witness concrete 名へも戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedDiffPowOnWitness
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedDiffPowOnWitness hDiff

/--
selected-witness congruence からも、
existential diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCongruenceWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCongruenceWitness hSel

/--
既存の diffPow-on-witness route からも、
existential diffPow witness concrete 名へ戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedDiffPowOnWitness
    (exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_diffPow hDiff)

/--
既存の diffPow `ModEq` route からも、
existential diffPow witness concrete 名へ戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel からも、
existential diffPow witness concrete 名へ戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
selected core witness からも、
existential diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreWitness hCore

/--
witness-aware selected core divisibility からも、
existential diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreOnWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreOnWitness hCore

/--
差冪 divisibility から selected-core-on-witness へ戻る route でも、
practical diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCoreOnWitness
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow hDiff)

/--
差冪 `ModEq` から selected-core-on-witness へ戻る route でも、
practical diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel から selected-core-on-witness へ戻る route でも、
practical diffPow witness concrete 名へ直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreCongruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget :=
  exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
差冪 `ModEq` 版があれば、divisibility 版を経由して selected-core-on-witness target は従う。
-/
theorem exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel が立てば、selected-core-on-witness target まで直接戻れる。
-/
theorem exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget :=
  exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
選んだ witness prime 上の diffPow congruence があれば、boundary core divisibility は直接従う。

[CFBRC] universal target を経由せず、
`∃ q, q ∣ x + 1 ∧ ¬ q ∣ x ∧ (u - 1)^d ≡ u^d [MOD q]`
から prepared concrete 本体へ入るための直橋。
-/
theorem exceptional_boundary_datum_prepared_boundary_core_dvd_of_selected_modEq
    {d x u q : ℕ}
    (_hd_prime : Nat.Prime d) (_hd_ge : 5 ≤ d)
    (_hx : 0 < x) (hu : 0 < u)
    (_hcop : Nat.Coprime x u)
    (_hdvd : d ∣ x)
    (_hWieferich : u ^ (d - 1) ≡ 1 [MOD d ^ 2])
    (hqprime : Nat.Prime q)
    (hq_dvd_x1 : q ∣ (x + 1))
    (_hq_not_dvd_x : ¬ q ∣ x)
    (hMod : (u - 1) ^ d ≡ u ^ d [MOD q]) :
    q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u := by
  have hle : (u - 1) ^ d ≤ u ^ d := by
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) d
  have hDiff : q ∣ u ^ d - (u - 1) ^ d := by
    exact (Nat.modEq_iff_dvd' hle).mp hMod
  have hu_eq : 1 + (u - 1) = u := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_pred_eq_of_pos hu
  have hq_dvd_core1 : q ∣ DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1) := by
    have hq_dvd_diff : q ∣ (1 + (u - 1)) ^ d - (u - 1) ^ d := by
      simpa [hu_eq] using hDiff
    exact DkMath.CFBRC.prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
      hqprime hq_dvd_diff hqprime.not_dvd_one
  rw [cyclotomicPrimeCore_one_pred_eq_residual_sum d u hu] at hq_dvd_core1
  have hx1_mod0 : x + 1 ≡ 0 [MOD q] := hq_dvd_x1.modEq_zero_nat
  have hxu_mod : x + u ≡ u - 1 [MOD q] := by
    have htmp := hx1_mod0.add_right (u - 1)
    have hu_eq' : 1 + (u - 1) = u := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hu_eq'] using htmp
  have hsum_mod :
      DkMath.CFBRC.boundaryCyclotomicPrimeCore .right d x u ≡
        ∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k) [MOD q] := by
    unfold DkMath.CFBRC.boundaryCyclotomicPrimeCore DkMath.CFBRC.cyclotomicPrimeCore
    exact sum_range_modEq (fun k hk =>
      ((hxu_mod.pow k).mul_right (u ^ (d - 1 - k))))
  have hres0 :
      (∑ k ∈ Finset.range d, (u - 1) ^ k * u ^ (d - 1 - k)) ≡ 0 [MOD q] :=
    hq_dvd_core1.modEq_zero_nat
  exact Nat.modEq_zero_iff_dvd.mp (hsum_mod.trans hres0)

/--
選んだ witness prime 1 個についての congruence だけでも、prepared concrete 本体は閉じる。

[CFBRC] 現時点で最も現実的な missing theorem 候補は、
universal kernel ではなくこちらの existential witness 版である。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_selectedCongruenceWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  rcases hSel hd_prime hd_ge hx hu hcop hdvd hWieferich with
    ⟨q, hqprime, hq_dvd_x1, hq_not_dvd_x, hMod⟩
  refine ⟨q, hqprime, ?_, hq_not_dvd_x⟩
  exact exceptional_boundary_datum_prepared_boundary_core_dvd_of_selected_modEq
    hd_prime hd_ge hx hu hcop hdvd hWieferich hqprime hq_dvd_x1 hq_not_dvd_x hMod

/--
concrete arithmetic witness を既定値に焼き付けると、
残る missing math は witness-aware CFBRC existence part 1 本になる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrcOnWitness
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_witnessAndCFBRC
    exceptional_boundary_datum_prepared_arithmetic_witness_concrete hCFBRC

/--
residual target が立てば、concrete arithmetic witness を既定値として prepared concrete 本体は閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_residual
    (hResidual : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrcOnWitness
    (exceptional_boundary_datum_prepared_cfbrc_existence_on_witness_of_residual hResidual)

/--
差冪 target が立てば、residual / witness-aware CFBRC existence を経由して prepared concrete 本体は閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_residual
    (exceptional_boundary_datum_prepared_cfbrc_residual_on_witness_of_diffPow hDiff)

/--
差冪の `Nat.ModEq` target が立てば、divisibility 版を経由して prepared concrete 本体は閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow
    (exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq hMod)

/--
additional congruence kernel が立てば、prepared concrete 本体まで閉じる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPowModEq
    (exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel hKernel)

/--
arithmetic concrete 本体が閉じた後は、
残る prepared concrete の missing math は CFBRC existence part 1 本だけである。

[CFBRC] arithmetic part の concrete 実装
`exceptional_boundary_datum_prepared_arithmetic_part_concrete`
を既定値として焼き付けた wrapper。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrc
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_arithmeticConcrete_and_cfbrc
    exceptional_boundary_datum_prepared_arithmetic_part_concrete hCFBRC

/--
prepared concrete theorem 名の canonical proof skeleton。

[CFBRC] いま concrete 本文を書き始めるなら、
まずこの theorem 名に対して
`intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich`
から入ればよい。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich
  exact hSplit hd_prime hd_ge hx hu hcop (Or.inr ⟨hdvd, hWieferich⟩)

/--
prepared arithmetic core の concrete theorem 名から、
canonical arithmetic core へ戻る橋。
-/
theorem exceptional_boundary_datum_arithmetic_core_of_preparedConcrete
    (hConcrete : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget) :
    ExceptionalBoundaryDatumArithmeticCoreTarget :=
  exceptional_boundary_datum_arithmetic_core_of_prepared
    (exceptional_boundary_datum_prepared_arithmetic_core_of_concrete hConcrete)

/--
exceptional datum 形の concrete theorem 名から、
通常の boundary-normalized concrete target へ戻る橋。
-/
theorem exceptional_boundaryData_right_branch_supply_concrete_of_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalBoundaryDataRightBranchSupplyConcreteTarget :=
  exceptional_boundaryData_right_branch_supply_concrete_of_splitRight
    (exceptional_boundaryData_splitRight_concrete_of_datum hDatum)

/--
exceptional-only arithmetic / CFBRC core から
boundary-normalized concrete target へ戻る橋。
-/
theorem exceptional_boundaryData_right_branch_supply_concrete_of_arithmeticCore
    (hCore : ExceptionalBoundaryDatumArithmeticCoreTarget) :
    ExceptionalBoundaryDataRightBranchSupplyConcreteTarget :=
  exceptional_boundaryData_right_branch_supply_concrete_of_datum
    (exceptional_boundary_datum_concrete_of_arithmeticCore hCore)

/--
exceptional datum 形の concrete theorem の proof skeleton。

[CFBRC] 本文では
`intro ...; rcases hDatum with ⟨hdvd, hWieferich⟩`
から始めれば十分だ、という入口を theorem 名として固定する。
-/
theorem exceptional_boundary_datum_concrete_of_split
    (hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget) :
    ExceptionalBoundaryDatumConcreteTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hDatum
  rcases hDatum with ⟨hdvd, hWieferich⟩
  exact hSplit hd_prime hd_ge hx hu hcop (Or.inr ⟨hdvd, hWieferich⟩)

/--
ordinary reference theorem と exceptional datum theorem が揃えば、
split theorem 全体は橋だけで閉じる。

[CFBRC] これにより proof file の truly new math は、
`CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
全体ではなく
`ExceptionalBoundaryDatumConcreteTarget`
1 本だと読める。
-/
theorem cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    CFBRCBoundaryCorePrimeExistenceOnSplitTarget := by
  intro d x u hd_prime hd_ge hx hu hcop hSplitCase
  rcases hSplitCase with hOrd | hExc
  · exact cfbrcBoundaryCorePrimeExistence_reference hd_prime hd_ge hx hu hcop hOrd
  · exact hDatum hd_prime hd_ge hx hu hcop hExc

/--
ordinary/reference 側の assembler と datum theorem が揃えば、
arithmetic core は split skeleton 経由で回収できる。

[CFBRC] downstream では datum concrete ではなく、
できるだけ arithmetic core 名を経由して参照する。
-/
theorem exceptional_boundary_datum_arithmetic_core_of_reference_and_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalBoundaryDatumArithmeticCoreTarget :=
  exceptional_boundary_datum_arithmetic_core_of_split
    (cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum hDatum)

/--
ordinary/reference theorem と datum theorem が揃えば、
prepared arithmetic core も split skeleton 経由で回収できる。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_of_reference_and_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_of_split
    (cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum hDatum)

/--
datum theorem から prepared concrete theorem 名へ入る canonical wrapper。
-/
theorem exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_reference_and_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget :=
  exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split
    (cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum hDatum)

/--
right branch supply があれば、
named kernel はそのまま閉じる。

[CFBRC] 以後の concrete 補題は、
まずこの supply target を返す形で切ってよい。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply
    (hSupply : ExceptionalSplitRightBranchSupplyTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  hSupply

/--
boundary-normalized concrete theorem 名があれば、
named kernel は pack-local supply 経由で回収できる。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete
    (hBoundary : ExceptionalBoundaryDataRightBranchSupplyConcreteTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply
    (exceptional_split_right_branch_supply_of_boundaryConcrete hBoundary)

/--
split-right 形の concrete theorem 名からも、
named kernel へは同じ配線で戻せる。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_splitRightConcrete
    (hRight : ExceptionalBoundaryDataSplitRightConcreteTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_splitRight hRight)

/--
exceptional datum 形の concrete theorem 名からも、
named kernel へは同じ配線で戻せる。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_datumConcrete
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_datum hDatum)

/--
exceptional-only arithmetic / CFBRC core からも、
named kernel へは同じ配線で戻せる。
-/
theorem exceptional_right_boundary_core_prime_of_wieferich_of_arithmeticCore
    (hCore : ExceptionalBoundaryDatumArithmeticCoreTarget) :
    ExceptionalRightBoundaryCorePrimeOfWieferichTarget :=
  exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_arithmeticCore hCore)

/--
named kernel があれば、
split right branch supply もそのまま回収できる。
-/
theorem exceptional_split_right_branch_supply_of_namedKernel
    (hKernel : ExceptionalRightBoundaryCorePrimeOfWieferichTarget) :
    ExceptionalSplitRightBranchSupplyTarget :=
  hKernel

/--
named concrete kernel があれば、
proof file mainline target へは thin bridge で戻せる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_namedKernel
    (hKernel : ExceptionalRightBoundaryCorePrimeOfWieferichTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  by
    intro p x y z hpack hp_dvd_gap hWieferich
    rcases hKernel hpack hp_dvd_gap hWieferich with
      ⟨q, hqprime, hqcore, hq_not_dvd_gap⟩
    refine ⟨q, hqprime, ?_, hq_not_dvd_gap⟩
    simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hqcore

/--
boundary-normalized concrete theorem 名から proof file mainline target へ戻る橋。

[CFBRC] local exceptional arithmetic / CFBRC theorem がこの形で立てば、
公開 mainline には thin bridge で戻せる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete
    (hBoundary : ExceptionalBoundaryDataRightBranchSupplyConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_namedKernel
    (exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete hBoundary)

/--
split-right 形の concrete theorem 名から proof file mainline へ戻る橋。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_splitRightConcrete
    (hRight : ExceptionalBoundaryDataSplitRightConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_splitRight hRight)

/--
exceptional datum 形の concrete theorem 名から proof file mainline へ戻る橋。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_datumConcrete
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_datum hDatum)

/--
exceptional-only arithmetic / CFBRC core から proof file mainline へ戻る橋。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_arithmeticCore
    (hCore : ExceptionalBoundaryDatumArithmeticCoreTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete
    (exceptional_boundaryData_right_branch_supply_concrete_of_arithmeticCore hCore)

/--
datum theorem があれば、
split assembler と datum skeleton の合成だけで proof file mainline は閉じる。

[CFBRC] downstream 側はこの theorem を入口にすれば、
ordinary/reference 側の配線を再度意識せずに済む。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_reference_and_datum
    (hDatum : ExceptionalBoundaryDatumConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_arithmeticCore
    (exceptional_boundary_datum_arithmetic_core_of_reference_and_datum hDatum)

/--
pack-local boundary existence があれば、
proof file mainline target へは `boundaryCyclotomicPrimeCore` の展開だけで戻れる。

[CFBRC] concrete proof の最終成果物は当面こちらを埋め、
公開 mainline にはこの橋で戻す。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_packLocalBoundary
    (hLocal : PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  rcases hLocal hpack hp_dvd_gap hWieferich with
    ⟨q, hqprime, hqcore, hq_not_dvd_gap⟩
  refine ⟨q, hqprime, ?_, hq_not_dvd_gap⟩
  simpa [DkMath.CFBRC.boundaryCyclotomicPrimeCore] using hqcore

/--
mainline target と pack-local boundary existence target は同値。

[CFBRC] 以後このファイルでは、
どちらを埋めても同じ concrete 証明探索だとみなしてよい。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_iff_packLocalBoundary :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget ↔
      PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget := by
  constructor
  · intro hMain p x y z hpack hp_dvd_gap hWieferich
    exact primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_mainline
      hMain hpack hp_dvd_gap hWieferich
  · intro hLocal
    exact primeGe5BranchAExceptionalExistenceMainline_of_packLocalBoundary hLocal

/--
proof file mainline target があれば、
primitive packet descent へは既存 wrapper でそのまま流せる。

[CFBRC] concrete proof はこのファイルに集め、packet descent への配線は
Branch A 本体の bridge を再利用する。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_exceptionalMainline_and_restore
    (hMain : PrimeGe5BranchAExceptionalExistenceMainlineTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_localExceptionalExistence_and_restore
    hMain hRestore

/--
boundary-normalized concrete theorem 名から primitive packet descent へは
mainline bridge を挟むだけで流せる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_boundaryConcrete_and_restore
    (hBoundary : ExceptionalBoundaryDataRightBranchSupplyConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_exceptionalMainline_and_restore
    (primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete hBoundary)
    hRestore

/--
split-right 形の concrete theorem 名から primitive packet descent へ戻る橋。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_splitRightConcrete_and_restore
    (hRight : ExceptionalBoundaryDataSplitRightConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_boundaryConcrete_and_restore
    (exceptional_boundaryData_right_branch_supply_concrete_of_splitRight hRight)
    hRestore

/--
exceptional datum 形の concrete theorem 名から primitive packet descent へ戻る橋。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_datumConcrete_and_restore
    (hDatum : ExceptionalBoundaryDatumConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_boundaryConcrete_and_restore
    (exceptional_boundaryData_right_branch_supply_concrete_of_datum hDatum)
    hRestore

/--
exceptional-only arithmetic / CFBRC core と restore theorem があれば、
primitive packet descent へもそのまま流せる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_arithmeticCore_and_restore
    (hCore : ExceptionalBoundaryDatumArithmeticCoreTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_boundaryConcrete_and_restore
    (exceptional_boundaryData_right_branch_supply_concrete_of_arithmeticCore hCore)
    hRestore

/--
prepared arithmetic core と restore theorem があれば、
primitive packet descent へもそのまま流せる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_preparedArithmeticCore_and_restore
    (hPrepared : ExceptionalBoundaryDatumPreparedArithmeticCoreTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_arithmeticCore_and_restore
    (exceptional_boundary_datum_arithmetic_core_of_prepared hPrepared)
    hRestore

/--
prepared arithmetic core から proof file mainline へ戻る橋。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_preparedArithmeticCore
    (hPrepared : ExceptionalBoundaryDatumPreparedArithmeticCoreTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_arithmeticCore
    (exceptional_boundary_datum_arithmetic_core_of_prepared hPrepared)

/--
prepared concrete theorem 名から proof file mainline へ戻る橋。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (hConcrete : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedArithmeticCore
    (exceptional_boundary_datum_prepared_arithmetic_core_of_concrete hConcrete)

/--
prepared arithmetic part の concrete 実装を既定値にすると、
mainline へ戻るための missing math も CFBRC existence part 1 本に縮む。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_cfbrcPart
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrc hCFBRC)

/--
concrete arithmetic witness を既定値にすると、
mainline へ戻る残りも witness-aware CFBRC existence part 1 本になる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_cfbrcOnWitness
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrcOnWitness hCFBRC)

/--
residual divisibility だけを示せば、proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_residual
    (hResidual : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_residual hResidual)

/--
差冪 divisibility だけを示せば、residual / prepared concrete を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_diffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow hDiff)

/--
差冪の `Nat.ModEq` target だけを示せば、divisibility 版を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_diffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPowModEq hMod)

/--
additional congruence kernel が立てば、proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_congruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_congruenceKernel hKernel)

/--
選んだ witness prime 1 個についての congruence だけでも、proof file mainline へ戻れる。

[CFBRC] universal congruence kernel が重すぎる場合の weaker mainline 入口。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruenceWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_selectedCongruenceWitness hSel)

/--
選んだ witness prime が `cyclotomicPrimeCore d 1 (u - 1)` を割るだけでも、
selected-witness congruence を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruenceWitness
    (exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedCoreWitness hCore)

/--
witness-aware core divisibility だけを示せば、selected-core witness を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreOnWitness
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreWitness
    (exceptional_boundary_datum_prepared_selectedCoreWitness_of_onWitness hCore)

/--
selected residual-on-witness だけを示せば、selected-core-on-witness を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedResidualOnWitness
    (hResidual : ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreOnWitness
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_selectedResidual hResidual)

/--
selected diffPow-on-witness だけを示せば、selected residual / core を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowOnWitness
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedResidualOnWitness
    (exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_selectedDiffPow hDiff)

/--
selected diffPow-on-witness の concrete theorem 名が立てば、
proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowConcrete
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowOnWitness
    (exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_concrete hDiff)

/--
選んだ witness prime 1 個についての差冪 divisibility だけでも、
selected-witness congruence を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitness
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruenceWitness
    (exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedDiffPowWitness hDiff)

/--
selected-witness congruence からも、
practical diffPow witness route を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruence_to_selectedDiffPowWitness
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitness
    (exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCongruenceWitness hSel)

/--
selected diffPow witness の concrete theorem 名が立てば、
proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitnessConcrete
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitness
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_self hDiff)

/--
practical entrance の concrete theorem 名が立てば、
proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_practicalConcrete
    (hDiff : PrimeGe5BranchAExceptionalPracticalConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitnessConcrete hDiff

/--
practical body-on-witness だけが立てば、
practical entrance を経由して proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_practicalBodyOnWitness
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_practicalConcrete
    (primeGe5BranchAExceptionalPracticalConcrete_of_bodyOnWitness hBody)

/--
`GN d 1 (u - 1)` divisibility だけが立てば、
practical body を経由して proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_practicalGN
    (hGN : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_practicalBodyOnWitness
    (primeGe5BranchAExceptionalPracticalBodyOnWitness_of_GN hGN)

/--
practical GN concrete theorem 名が立てば、
proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_practicalGNConcrete
    (hGN : PrimeGe5BranchAExceptionalPracticalGNConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_practicalGN hGN

/--
practical `ModEq` concrete theorem 名が立てば、
proof file mainline へ直接戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_practicalModEqConcrete
    (hMod : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_practicalBodyOnWitness
    (primeGe5BranchAExceptionalPracticalBodyOnWitness_of_ModEq hMod)

/--
selected-core diffPow route からも、
practical diffPow witness concrete を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCore_to_selectedDiffPowWitnessConcrete
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitnessConcrete
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPow hDiff)

/--
selected-core `ModEq` route からも、
practical diffPow witness concrete を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreDiffPowModEq_to_selectedDiffPowWitnessConcrete
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitnessConcrete
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPowModEq hMod)

/--
selected-core congruence kernel route からも、
practical diffPow witness concrete を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreCongruenceKernel_to_selectedDiffPowWitnessConcrete
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedDiffPowWitnessConcrete
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreCongruenceKernel hKernel)

/--
差冪 divisibility だけを示せば、selected-core-on-witness を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreDiffPow
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreOnWitness
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow hDiff)

/--
差冪 `ModEq` 版だけを示せば、selected-core-on-witness を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreDiffPowModEq
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreOnWitness
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPowModEq hMod)

/--
additional congruence kernel が立てば、selected-core-on-witness を経由して proof file mainline へ戻れる。
-/
theorem primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreCongruenceKernel
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget :=
  primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreOnWitness
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_congruenceKernel hKernel)

/--
prepared arithmetic core の concrete theorem 名と restore theorem があれば、
primitive packet descent へもそのまま流せる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (hConcrete : ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedArithmeticCore_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_of_concrete hConcrete)
    hRestore

/--
prepared arithmetic part を既定 concrete に固定すると、
primitive packet descent に残る missing math も CFBRC existence part 1 本だけである。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_cfbrcPart_and_restore
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrc hCFBRC)
    hRestore

/--
concrete arithmetic witness を既定値にすると、
primitive packet descent に残る missing math も witness-aware CFBRC existence part 1 本になる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_cfbrcOnWitness_and_restore
    (hCFBRC : ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrcOnWitness hCFBRC)
    hRestore

/--
residual divisibility と restore theorem があれば、primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_residual_and_restore
    (hResidual : ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_residual hResidual)
    hRestore

/--
差冪 divisibility と restore theorem があれば、primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_diffPow_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow hDiff)
    hRestore

/--
差冪の `Nat.ModEq` target と restore theorem があれば、primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_diffPowModEq_and_restore
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPowModEq hMod)
    hRestore

/--
additional congruence kernel と restore theorem があれば、primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_congruenceKernel_and_restore
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_congruenceKernel hKernel)
    hRestore

/--
選んだ witness prime 1 個についての congruence と restore theorem があれば、
primitive packet descent まで閉じる。

[CFBRC] current proof exploration では、
まずこちらの existential witness 版が立つかを優先して調べてよい。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCongruenceWitness_and_restore
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore
    (exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_selectedCongruenceWitness hSel)
    hRestore

/--
選んだ witness prime の `cyclotomicPrimeCore d 1 (u - 1)` divisibility と restore theorem があれば、
primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreWitness_and_restore
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCongruenceWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedCoreWitness hCore)
    hRestore

/--
witness-aware core divisibility と restore theorem があれば、
primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreOnWitness_and_restore
    (hCore : ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCoreWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCoreWitness_of_onWitness hCore)
    hRestore

/--
selected residual-on-witness と restore theorem があれば、selected-core-on-witness を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedResidualOnWitness_and_restore
    (hResidual : ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCoreOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_selectedResidual hResidual)
    hRestore

/--
selected diffPow-on-witness と restore theorem があれば、selected residual / core を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowOnWitness_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedResidualOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedResidualOnWitness_of_selectedDiffPow hDiff)
    hRestore

/--
selected diffPow-on-witness の concrete theorem 名と restore theorem があれば、
primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowConcrete_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowOnWitness_of_concrete hDiff)
    hRestore

/--
選んだ witness prime 1 個についての差冪 divisibility と restore theorem があれば、
primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitness_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCongruenceWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedDiffPowWitness hDiff)
    hRestore

/--
selected-witness congruence と restore theorem からも、
practical diffPow witness route を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCongruence_to_selectedDiffPowWitness_and_restore
    (hSel : ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowWitness_of_selectedCongruenceWitness hSel)
    hRestore

/--
selected diffPow witness の concrete theorem 名と restore theorem があれば、
primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitnessConcrete_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_self hDiff)
    hRestore

/--
practical entrance の concrete theorem 名と restore theorem があれば、
primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_practicalConcrete_and_restore
    (hDiff : PrimeGe5BranchAExceptionalPracticalConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitnessConcrete_and_restore hDiff hRestore

/--
practical body-on-witness と restore theorem があれば、
practical entrance を経由して primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_practicalBodyOnWitness_and_restore
    (hBody : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_practicalConcrete_and_restore
    (primeGe5BranchAExceptionalPracticalConcrete_of_bodyOnWitness hBody)
    hRestore

/--
`GN d 1 (u - 1)` divisibility と restore theorem があれば、
practical body を経由して primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_practicalGN_and_restore
    (hGN : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_practicalBodyOnWitness_and_restore
    (primeGe5BranchAExceptionalPracticalBodyOnWitness_of_GN hGN)
    hRestore

/--
practical GN concrete theorem 名と restore theorem があれば、
primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_practicalGNConcrete_and_restore
    (hGN : PrimeGe5BranchAExceptionalPracticalGNConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_practicalGN_and_restore hGN hRestore

/--
practical `ModEq` concrete theorem 名と restore theorem があれば、
primitive packet descent まで直接閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_practicalModEqConcrete_and_restore
    (hMod : PrimeGe5BranchAExceptionalPracticalBodyOnWitnessModEqConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_practicalBodyOnWitness_and_restore
    (primeGe5BranchAExceptionalPracticalBodyOnWitness_of_ModEq hMod)
    hRestore

/--
selected-core diffPow route からも、
practical diffPow witness concrete を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCore_to_selectedDiffPowWitnessConcrete_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitnessConcrete_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPow hDiff)
    hRestore

/--
selected-core `ModEq` route からも、
practical diffPow witness concrete を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreDiffPowModEq_to_selectedDiffPowWitnessConcrete_and_restore
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitnessConcrete_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreDiffPowModEq hMod)
    hRestore

/--
selected-core congruence kernel route からも、
practical diffPow witness concrete を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreCongruenceKernel_to_selectedDiffPowWitnessConcrete_and_restore
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedDiffPowWitnessConcrete_and_restore
    (exceptional_boundary_datum_prepared_selectedDiffPowWitnessConcrete_of_selectedCoreCongruenceKernel hKernel)
    hRestore

/--
差冪 divisibility と restore theorem があれば、selected-core-on-witness を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreDiffPow_and_restore
    (hDiff : ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCoreOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow hDiff)
    hRestore

/--
差冪 `ModEq` 版と restore theorem があれば、selected-core-on-witness を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreDiffPowModEq_and_restore
    (hMod : ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCoreOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPowModEq hMod)
    hRestore

/--
additional congruence kernel と restore theorem があれば、selected-core-on-witness を経由して primitive packet descent まで閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_selectedCoreCongruenceKernel_and_restore
    (hKernel : ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_selectedCoreOnWitness_and_restore
    (exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_congruenceKernel hKernel)
    hRestore

/--
datum theorem と restore theorem があれば、
primitive packet descent は ordinary/reference 側の assembler を含めて閉じる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_reference_and_datum_and_restore
    (hDatum : ExceptionalBoundaryDatumConcreteTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget :=
  primeGe5BranchAPrimitivePacketDescent_of_arithmeticCore_and_restore
    (exceptional_boundary_datum_arithmetic_core_of_reference_and_datum hDatum)
    hRestore

end DkMath.FLT
