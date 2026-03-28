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

end DkMath.FLT
