/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

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
