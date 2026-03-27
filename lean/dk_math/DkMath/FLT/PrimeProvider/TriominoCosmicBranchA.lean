/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core
import DkMath.NumberTheory.Gcd.GN
import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchA"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`Basic.lean` から呼ぶ Branch A（`p ∣ z - y`）専用の gap-power 供給仕様。

`GapInvariant` の本線 API とは切り離し、`Basic` が依存循環なしで参照できる
最小入口として lower layer に固定する。
-/
abbrev PrimeGe5BranchAGapPowFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∀ q : ℕ, p ∣ (z - y).factorization q

/--
Branch A の因数分解指数仕様が供給されれば、`gap = z - y` は pure `p` 乗に落ちる。
-/
theorem primeGe5BranchAGapPow_of_factorization
    (hFac : PrimeGe5BranchAGapPowFactorizationTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ t : ℕ, (z - y) = t ^ p := by
  intro p x y z hpack hp_dvd_gap
  have hp0 : 0 < p := hpack.hp.pos
  have hgap_ne0 : (z - y) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  exact exists_eq_pow_of_factorization_dvd
    (u := z - y) (p := p)
    hgap_ne0 hp0
    (hFac hpack hp_dvd_gap)

/--
Branch A 本線 target（shape-factorization 版）。

`u := z - y` について
- `q ≠ p` 側の指数は `p` の倍数
- `q = p` 側の指数は `(p - 1) + p * m` 形
を lower layer で要求する。
-/
abbrev PrimeGe5BranchAShapeFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q) ∧
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m

/-- Branch A の値域 shape 出口。 -/
abbrev PrimeGe5BranchAShapeValueTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p

/-- Branch A では `GN` 自体も `p * s^p` 形になる。 -/
abbrev PrimeGe5BranchAGNShapeTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p

/--
Branch A 専用の Wieferich-style witness target。

`p ∣ z-y` の normal form から最終的に取りたい新情報は
`y^(p-1) ≡ 1 [MOD p^2]`
なので、comparison route と独立にこの出力仕様を明示しておく。
-/
abbrev PrimeGe5BranchAWieferichOnYTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2]

/--
Branch A 専用の最終 refuter 契約。

Wieferich-style witness が lower layer で取れた後は、この target を埋めれば
Branch A 全体の refuter が comparison route から独立に閉じる。
-/
abbrev PrimeGe5BranchAWieferichRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    False

/--
Branch A / Wieferich route の local kernel。

Wieferich witness 単独ではなく、
Branch A normal form
`gap = p^(p-1) * t^p`, `GN = p * s^p`, `x = p * (t * s)`
および局所 coprime 情報と合わせて refute する中間契約である。
-/
abbrev PrimeGe5BranchAWieferichLocalKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    False

/-- Branch A 条件付きで `z` 最小の prime-ge5 反例 pack。 -/
abbrev MinimalPrimeGe5CounterexamplePackA (p x y z : ℕ) : Prop :=
  PrimeGe5CounterexamplePack p x y z ∧ p ∣ (z - y) ∧
  ∀ {x' y' z' : ℕ}, PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') → z' < z → False

/--
Branch A normal form を 1 パケットとして保持する構造体。

付録:
- smaller counterexample を直接返す前に、
  まずは smaller normal-form packet を返す target を切るほうが自然な場合がある。
- `PrimeGe5CounterexamplePack` への再包装は `pack` で既に持っている。
-/
structure PrimeGe5BranchANormalFormPacket (p : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  t : ℕ
  s : ℕ
  pack : PrimeGe5CounterexamplePack p x y z
  hp_dvd_gap : p ∣ (z - y)
  hgap : z - y = p ^ (p - 1) * t ^ p
  hsGN : GN p (z - y) y = p * s ^ p
  hsx : x = p * (t * s)

/-- Branch A normal-form packet から反例 pack を取り出すだけの補題。 -/
theorem counterexamplePack_of_branchANormalFormPacket
    {p : ℕ} (pkt : PrimeGe5BranchANormalFormPacket p) :
    PrimeGe5CounterexamplePack p pkt.x pkt.y pkt.z :=
  pkt.pack

/--
Branch A 専用の truly new kernel 候補。

Wieferich witness 自体ではなく、
`q = p` が distinguished prime になる Branch A normal form から
より小さい Branch A 反例を構成できることを要求する。
-/
abbrev PrimeGe5BranchADistinguishedPrimeDescentTarget : Prop :=
  ∀ {p x y z t s : ℕ}, MinimalPrimeGe5CounterexamplePackA p x y z →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ∃ x' y' z' : ℕ,
      PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
Branch A normal form から、
より小さい Branch A normal-form packet を直接返す stronger target。

付録:
- `PrimeGe5BranchASmallerCounterexampleTarget` に比べて、
  smaller packet の情報 `t'`, `s'`, `hgap`, `hsGN`, `hsx` まで保持できる。
- concrete 数学としては、
  まずこちらを埋めてから counterexample target へ落とすほうが自然な場合がある。
-/
abbrev PrimeGe5BranchASmallerPacketTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
`p ∣ t` のとき、余分な distinguished-prime 深さを 1 段剥いて
smaller packet を返す route。

付録:
- これは Nat / valuation 層で完結する候補契約である。
- `PrimeGe5BranchASmallerPacketTarget` のうち
  `p ∣ t`
  分岐だけを切り出している。
-/
abbrev PrimeGe5BranchAValuationPeelPacketTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
valuation peel route の直前段階となる seed contract。

付録:
- `p ∣ t` のとき、
  `s^p - y^(p-1)` が `p^(2p-1)` と `t1^p` を因子にもつ形へ落ちることを要求する。
- smaller packet の再構成自体はまだ要求しない。
-/
abbrev PrimeGe5BranchAValuationPeelSeedTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 B : ℕ, t = p * t1 ∧ s ^ p = y ^ (p - 1) + p ^ (2 * p - 1) * (t1 ^ p * B)

/--
valuation peel route の canonical tail 契約。

付録:
- `p ∣ t` のとき、
  `t = p * t1`
  に剥いたあとで
  `GN(p, p^(p-1) * t1^p, y)`
  自体を宇宙式の canonical tail 展開で読めることを要求する。
- これは seed から packet へ直接跳ぶ前に、
  `GN/p`
  の標準 tail と比較するための中間契約である。
-/
abbrev PrimeGe5BranchAValuationPeelCanonicalTailTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 C : ℕ,
      t = p * t1 ∧
      GN p (p ^ (p - 1) * t1 ^ p) y =
        p * y ^ (p - 1) + (p ^ (p - 1) * t1 ^ p) * C

/--
valuation peel route の tail comparison 契約。

付録:
- seed 側の tail 係数 `B` と、
  canonical tail 側の係数 `C`
  を同じ `t1`
  で比較可能な形に並べて返す。
- この段階ではまだ
  `B = C`
  や
  `C = p^p * B`
  のような stronger relation は要求しない。
  不足情報を exact に可視化するための中間契約である。
-/
abbrev PrimeGe5BranchAValuationPeelTailComparisonTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 B C : ℕ,
      t = p * t1 ∧
      s ^ p = y ^ (p - 1) + p ^ (2 * p - 1) * (t1 ^ p * B) ∧
      GN p (p ^ (p - 1) * t1 ^ p) y =
        p * y ^ (p - 1) + (p ^ (p - 1) * t1 ^ p) * C

/--
valuation peel comparison の first exact output。

付録:
- `B`
  と
  `C`
  が実際にどの `GTail p 2`
  係数を表しているかを固定する。
- これにより
  `B`
  と
  `C`
  の relation は、
  2 つの `GTail`
  の relation として読み替えられる。
-/
abbrev PrimeGe5BranchAValuationPeelTailExactTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 B C : ℕ,
      t = p * t1 ∧
      DkMath.CosmicFormula.GTail p 2 (z - y) y = p * B ∧
      DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y = C

/--
valuation peel comparison の mod-level output。

付録:
- exact tail identity を使って、
  最終的に見たい
  `p * B ≡ C [MOD p^(p-1) * t1^p]`
  を返す契約である。
- `analysis-BC.md`
  の first formal target に対応する。
-/
abbrev PrimeGe5BranchAValuationPeelTailModEqTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 B C : ℕ,
      t = p * t1 ∧
      p * B ≡ C [MOD p ^ (p - 1) * t1 ^ p]

/--
valuation peel comparison の exact error decomposition。

付録:
- `analysis-BC.md`
  の
  `p * B = C + u * E`
  型の first-order 差分分解に対応する。
- nat 上では
  `C = p * B + u * E`
  ではなく、
  大きい gap 側係数が canonical 側以上であることを使って
  `p * B = C + u * E`
  と書くのが自然である。
-/
abbrev PrimeGe5BranchAValuationPeelTailErrorTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∃ t1 B C E : ℕ,
      t = p * t1 ∧
      p * B = C + (p ^ (p - 1) * t1 ^ p) * E

/--
valuation peel route の最後の unresolved lift。

付録:
- valuation peel を `obstruction extraction`
  として読むなら、
  未完数学は
  `PrimeGe5BranchAValuationPeelTailErrorTarget`
  の error term から
  smaller packet
  を起こすこの 1 本に集約できる。
- primitive route と分離して扱うための target である。
-/
abbrev PrimeGe5BranchAValuationPeelPacketFromErrorTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    p ∣ t →
    ∀ {t1 B C E : ℕ},
      t = p * t1 →
      p * B = C + (p ^ (p - 1) * t1 ^ p) * E →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
`p ∤ t` の primitive core に入った後、
cyclotomic / distinguished-prime descent で smaller packet を返す route。

付録:
- これは Nat 直操作よりも algebraic descent を置くべき側の契約である。
- `PrimeGe5BranchASmallerPacketTarget` のうち
  `¬ p ∣ t`
  分岐だけを切り出している。
-/
abbrev PrimeGe5BranchAPrimitivePacketDescentTarget : Prop :=
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
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
primitive route の first-order local target。

付録:
- `¬ p ∣ t`
  だけではなく、
  Branch A normal form から既に得られる
  `y^(p-1) ≡ 1 [MOD p^2]`
  を明示入力として受ける。
- primitive mainline の本体が本当に欲している追加数論情報を、
  packet descent 契約から一段切り出した形である。
-/
abbrev PrimeGe5BranchAPrimitiveWieferichPacketTarget : Prop :=
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
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
primitive mainline の distinguished-prime selection 段。

付録:
- primitive route で本当に新しく必要なのは、
  まず `GN p (z-y) y`
  側に distinguished prime `q`
  を 1 つ取ることである。
- ここでは `q ∣ GN` かつ `¬ q ∣ (z-y)` だけを要求し、
  packet restoration とは分離して扱う。
-/
abbrev PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget : Prop :=
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
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ∣ (z - y)

/--
primitive route の Zsigmondy-lite / cyclotomic existence 段。

付録:
- `GN p (z-y) y`
  に対して、
  gap 側に埋もれない新しい素数 `q`
  が存在することだけを表す。
- `PrimitiveBeam` や `ZsigmondyCyclotomic`
  の既存存在論をここへ接続するのが自然である。
-/
abbrev PrimeGe5BranchAPrimitiveZsigmondyTarget : Prop :=
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
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ GN p (z - y) y ∧ ¬ q ∣ (z - y)

/--
distinguished prime が取れた後の smaller-packet restoration 段。

付録:
- primitive route の後半だけを isolated に表す target である。
- distinguished prime の existence と、
  actual な smaller packet 復元を分離するために置く。
-/
abbrev PrimeGe5BranchAPrimitivePacketRestoreTarget : Prop :=
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
      q ∣ GN p (z - y) y →
      ¬ q ∣ (z - y) →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z

/--
Branch A normal form から直接、
より小さい Branch A 反例を構成する stronger target。

付録:
- concrete 数学としては、minimality を仮定するよりこちらを直接埋めるほうが自然な可能性が高い。
- `PrimeGe5BranchADistinguishedPrimeDescentTarget` は、この stronger target から
  no-`sorry` で回収できる。
-/
abbrev PrimeGe5BranchASmallerCounterexampleTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ∃ x' y' z' : ℕ,
      PrimeGe5CounterexamplePack p x' y' z' ∧ p ∣ (z' - y') ∧ z' < z

/--
Branch A の shape 値を refute する lower-layer 契約。

ここを clean な descent/shrink kernel で埋めれば、
`Basic.lean` 側は `primeGe5BranchARefuter_default` をそのまま呼び続けてよい。
-/
abbrev PrimeGe5BranchAShapeValueToRefuterTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    (∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) →
    False

/--
Branch A の `q ≠ p` 側で必要な核仕様。

`u := z - y` に対し、`q` が素数で `q ≠ p` かつ `q ∣ u` なら `q ∤ GN p u y`。
-/
abbrev PrimeGe5BranchANoSharedPrimeOnGNTarget : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    Nat.Prime q → q ≠ p → q ∣ (z - y) →
    ¬ q ∣ GN p (z - y) y

/-- `p ∣ n` かつ `¬ p^2 ∣ n` なら `padicValNat p n = 1`。 -/
lemma primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq
    {p n : ℕ} (hp : Nat.Prime p)
    (hpd : p ∣ n) (hpsq : ¬ p ^ 2 ∣ n) :
    padicValNat p n = 1 := by
  have hnz : n ≠ 0 := by
    intro hn0
    apply hpsq
    simp [hn0]
  have hge : 1 ≤ padicValNat p n :=
    DkMath.ABC.padicValNat_one_le_of_prime_dvd hp hnz hpd
  have hle : padicValNat p n ≤ 1 := by
    by_contra hnot
    have h2 : 2 ≤ padicValNat p n := by omega
    have hsq : p ^ 2 ∣ n :=
      (@padicValNat_dvd_iff_le p (Fact.mk hp) n 2 hnz).2 h2
    exact hpsq hsq
  exact le_antisymm hle hge

/--
`x^p = u * N` かつ `padicValNat p N = 1` から、`u` の `p`-進指数形を回収する。
-/
lemma primeGe5BranchAPadicValNat_gap_shape_of_mul_eq_pow
    {p x u N : ℕ}
    (hp : Nat.Prime p)
    (hx0 : x ≠ 0)
    (hu0 : u ≠ 0)
    (hN0 : N ≠ 0)
    (hEq : x ^ p = u * N)
    (hNval : padicValNat p N = 1) :
    ∃ m : ℕ, padicValNat p u = (p - 1) + p * m := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpow : padicValNat p (x ^ p) = p * padicValNat p x := by
    simpa using (padicValNat.pow (p := p) (a := x) p hx0)
  have hmul : padicValNat p (u * N) = padicValNat p u + padicValNat p N := by
    simpa using (padicValNat.mul (p := p) hu0 hN0)
  have hvalEq : p * padicValNat p x = padicValNat p u + 1 := by
    calc
      p * padicValNat p x = padicValNat p (x ^ p) := hpow.symm
      _ = padicValNat p (u * N) := by simp [hEq]
      _ = padicValNat p u + padicValNat p N := hmul
      _ = padicValNat p u + 1 := by simp [hNval]
  have hx_pos : 0 < padicValNat p x := by
    have : 0 < p * padicValNat p x := by
      rw [hvalEq]
      exact Nat.succ_pos _
    exact Nat.pos_of_mul_pos_left this
  have hvu : padicValNat p u = p * padicValNat p x - 1 := by
    exact Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat p x - 1, ?_⟩
  have hx_decomp : (padicValNat p x - 1) + 1 = padicValNat p x := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hx_pos)
  calc
    padicValNat p u = p * padicValNat p x - 1 := hvu
    _ = p * ((padicValNat p x - 1) + 1) - 1 := by simp [hx_decomp]
    _ = (p * (padicValNat p x - 1) + p) - 1 := by simp [Nat.mul_add]
    _ = p * (padicValNat p x - 1) + (p - 1) := by
      have hp_ge1 : 1 ≤ p := Nat.succ_le_of_lt hp.pos
      simp [Nat.add_sub_assoc hp_ge1]
    _ = (p - 1) + p * (padicValNat p x - 1) := by ac_rfl

/--
Branch A では、`N := GN p (z - y) y` に対して `p ∣ N` かつ `¬ p^2 ∣ N` が成り立つ。
-/
theorem primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    p ∣ GN p (z - y) y ∧ ¬ p ^ 2 ∣ GN p (z - y) y := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let B : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hp_not_dvd_y : ¬ p ∣ y := by
    simpa [u, PrimeGe5CounterexamplePack.gap] using
      hpack.prime_not_dvd_right_of_prime_dvd_gap hp_dvd_gap
  have hsplitBA : B + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N
    rw [GN_eq_sum]
    unfold A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_sq : p ^ 2 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := Finset.mem_of_mem_erase hk
    have hk_lt : k < p := Finset.mem_range.mp hk_mem
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      have hp_dvd_uk : p ∣ u ^ k := by
        simpa [hk_one] using hp_dvd_gap
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k := by
        simpa [pow_two] using Nat.mul_dvd_mul hchoose hp_dvd_uk
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
    · have hk_ge_two : 2 ≤ k := by omega
      have hpp_dvd_u2 : p ^ 2 ∣ u ^ 2 := by
        simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_gap hp_dvd_gap
      have hpp_dvd_uk : p ^ 2 ∣ u ^ k := dvd_trans hpp_dvd_u2 (pow_dvd_pow u hk_ge_two)
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k :=
        dvd_mul_of_dvd_right hpp_dvd_uk _
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
  have hA_not_sq : ¬ p ^ 2 ∣ A := by
    intro hA_sq
    have hp_dvd_ypow : p ∣ y ^ (p - 1) := by
      have hmul : p * p ∣ p * y ^ (p - 1) := by
        simpa [A, pow_two] using hA_sq
      exact Nat.dvd_of_mul_dvd_mul_left hp_pos hmul
    exact hp_not_dvd_y (hpack.hp.dvd_of_dvd_pow hp_dvd_ypow)
  refine ⟨?_, ?_⟩
  · have hp_dvd_A : p ∣ A := by
      unfold A
      exact dvd_mul_right p (y ^ (p - 1))
    have hp_dvd_B : p ∣ B := by
      have hB_sq' : p * p ∣ B := by
        simpa [pow_two] using hB_sq
      exact dvd_trans (dvd_mul_right p p) hB_sq'
    have hp_dvd_N : p ∣ N := by
      simpa [hsplit] using (Nat.dvd_add hp_dvd_A hp_dvd_B)
    simpa [N, u] using hp_dvd_N
  · intro hN_sq
    have hA_sq : p ^ 2 ∣ A := by
      have hN_sq' : p ^ 2 ∣ N := by
        simpa [N, u] using hN_sq
      have hAB_sq : p ^ 2 ∣ A + B := by
        simpa [hsplit] using hN_sq'
      have hBA_sq : p ^ 2 ∣ B + A := by
        simpa [Nat.add_comm] using hAB_sq
      exact (Nat.dvd_add_right hB_sq).1 hBA_sq
    exact hA_not_sq hA_sq

/--
Branch A では、`GN p (z - y) y` は
`p * y^(p-1)` に `p^2` の tail を加えた形へ展開できる。

付録:
- これは `GN = p * s^p` 形と合わせて、`s^p` の `mod p^2` 情報を読む最初の入口である。
- 以後の Wieferich route では、この theorem を使って
  `GN` の head term と high-`p` tail を明示的に分離する。
-/
theorem primeGe5BranchA_GN_eq_head_add_p_sq_mul
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    ∃ M : ℕ, GN p (z - y) y = p * y ^ (p - 1) + p ^ 2 * M := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let B : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hsplitBA : B + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N
    rw [GN_eq_sum]
    unfold A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_sq : p ^ 2 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := Finset.mem_of_mem_erase hk
    have hk_lt : k < p := Finset.mem_range.mp hk_mem
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      have hp_dvd_uk : p ∣ u ^ k := by
        simpa [hk_one] using hp_dvd_gap
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k := by
        simpa [pow_two] using Nat.mul_dvd_mul hchoose hp_dvd_uk
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
    · have hk_ge_two : 2 ≤ k := by omega
      have hpp_dvd_u2 : p ^ 2 ∣ u ^ 2 := by
        simpa [pow_two] using Nat.mul_dvd_mul hp_dvd_gap hp_dvd_gap
      have hpp_dvd_uk : p ^ 2 ∣ u ^ k := dvd_trans hpp_dvd_u2 (pow_dvd_pow u hk_ge_two)
      have hprefix : p ^ 2 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k :=
        dvd_mul_of_dvd_right hpp_dvd_uk _
      have hmul : p ^ 2 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
        dvd_mul_of_dvd_left hprefix _
      simpa [Nat.mul_assoc] using hmul
  obtain ⟨M, hM⟩ := exists_eq_mul_left_of_dvd hB_sq
  refine ⟨M, ?_⟩
  calc
    GN p (z - y) y = N := by rfl
    _ = A + B := hsplit
    _ = p * y ^ (p - 1) + p ^ 2 * M := by
      rw [hM]
      simp [A, Nat.mul_comm]

/--
Branch A の `GN = p * s^p` 形を `head + p^2 * tail` 展開と合わせると、
`s^p` 自体は `y^(p-1)` に `p` の倍数を足した形へ落ちる。

付録:
- これは `s^p ≡ y^(p-1) [MOD p]` の concrete version であり、
  次段の `mod p^2` / Wieferich witness 化の前処理として使う。
- `GN = p * s^p` を一度 `p` で割った normal form と読むための helper である。
-/
theorem primeGe5BranchA_spow_eq_head_add_p_mul
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ∃ M : ℕ, s ^ p = y ^ (p - 1) + p * M := by
  rcases primeGe5BranchA_GN_eq_head_add_p_sq_mul hpack hp_dvd_gap with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  have hp_pos : 0 < p := hpack.hp.pos
  have hEq :
      p * s ^ p = p * (y ^ (p - 1) + p * M) := by
    rw [← hsGN, hM]
    ring
  exact Nat.eq_of_mul_eq_mul_left hp_pos hEq

/--
Branch A の gap-shape `z - y = p^(p-1) * t^p` を使うと、
`GN p (z - y) y` の tail は実際には `p^3` 以上を持つ。

付録:
- `GN = p * y^(p-1) + p^3 * M` は、
  次段で `GN = p * s^p` を 1 回割って
  `s^p ≡ y^(p-1) [MOD p^2]`
  を読むための直前段階である。
-/
theorem primeGe5BranchA_GN_eq_head_add_p_cube_mul
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p) :
    ∃ M : ℕ, GN p (z - y) y = p * y ^ (p - 1) + p ^ 3 * M := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let B : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hp3_dvd_u : p ^ 3 ∣ u := by
    unfold u
    rw [hgap]
    refine dvd_mul_of_dvd_left ?_ _
    have hp_ge5 : 5 ≤ p := hpack.hp5
    have h3_le : 3 ≤ p - 1 := by omega
    exact pow_dvd_pow p h3_le
  have hsplitBA : B + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N
    rw [GN_eq_sum]
    unfold A B u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + B := by
    simpa [Nat.add_comm] using hsplitBA.symm
  have hB_cube : p ^ 3 ∣ B := by
    unfold B
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    have hk_ge_one : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk_ne_zero)
    have hp3_dvd_uk : p ^ 3 ∣ u ^ k := by
      have hp3_dvd_u1 : p ^ 3 ∣ u ^ 1 := by simpa using hp3_dvd_u
      exact dvd_trans hp3_dvd_u1 (pow_dvd_pow u hk_ge_one)
    have hprefix : p ^ 3 ∣ (Nat.choose p (k + 1) : ℕ) * u ^ k :=
      dvd_mul_of_dvd_right hp3_dvd_uk _
    have hmul : p ^ 3 ∣ ((Nat.choose p (k + 1) : ℕ) * u ^ k) * y ^ (p - 1 - k) :=
      dvd_mul_of_dvd_left hprefix _
    simpa [Nat.mul_assoc] using hmul
  obtain ⟨M, hM⟩ := exists_eq_mul_left_of_dvd hB_cube
  refine ⟨M, ?_⟩
  calc
    GN p (z - y) y = N := by rfl
    _ = A + B := hsplit
    _ = p * y ^ (p - 1) + p ^ 3 * M := by
      rw [hM]
      simp [A, Nat.mul_comm]

/--
Branch A の gap-shape と `GN = p * s^p` を合わせると、
`s^p` は `y^(p-1)` に `p^2` の倍数を足した形へ落ちる。

付録:
- これは実質的に
  `s^p ≡ y^(p-1) [MOD p^2]`
  の concrete equality version である。
- 次段ではこの theorem を `Nat.ModEq` か Wieferich witness の入力仕様へ正規化する。
-/
theorem primeGe5BranchA_spow_eq_head_add_p_sq_mul
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ∃ M : ℕ, s ^ p = y ^ (p - 1) + p ^ 2 * M := by
  rcases primeGe5BranchA_GN_eq_head_add_p_cube_mul hpack hp_dvd_gap hgap with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  have hp_pos : 0 < p := hpack.hp.pos
  have hEq :
      p * s ^ p = p * (y ^ (p - 1) + p ^ 2 * M) := by
    rw [← hsGN, hM]
    ring
  exact Nat.eq_of_mul_eq_mul_left hp_pos hEq

/--
Branch A では、`s^p - y^(p-1)` 自体が gap `z - y` を 1 因子持つ。

付録:
- `GN = p * s^p` を `p` で 1 回割ったあと、
  tail 側に残る各項は `k ≥ 1` なので必ず `z - y` を 1 因子含む。
- valuation peel route では、この theorem を
  `z - y = p^(p-1) * t^p`
  と組み合わせて使う。
-/
theorem primeGe5BranchA_spow_eq_head_add_gap_mul
    {p x y z s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ∃ B : ℕ, s ^ p = y ^ (p - 1) + (z - y) * B := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  let A : ℕ := p * y ^ (p - 1)
  let T : ℕ := Finset.sum ((Finset.range p).erase 0) (fun k =>
    (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k))
  have hp_pos : 0 < p := hpack.hp.pos
  have hu_pos : 0 < u := by
    unfold u
    exact Nat.sub_pos_of_lt hpack.hyz_lt
  have hu_ne_zero : u ≠ 0 := Nat.ne_of_gt hu_pos
  obtain ⟨a, ha0⟩ : ∃ a : ℕ, u = a * p := exists_eq_mul_left_of_dvd hp_dvd_gap
  have ha : u = p * a := by simpa [Nat.mul_comm] using ha0
  have hsplitTA : T + A = N := by
    let f : ℕ → ℕ := fun k =>
      (Nat.choose p (k + 1) : ℕ) * (z - y) ^ k * y ^ (p - 1 - k)
    have hsum :
        Finset.sum ((Finset.range p).erase 0) f + f 0 = Finset.sum (Finset.range p) f := by
      simpa using
        (Finset.sum_erase_add (s := Finset.range p) (f := f) (a := 0)
          (by simpa using hp_pos))
    unfold N
    rw [GN_eq_sum]
    unfold A T u
    simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hsplit : N = A + T := by
    simpa [Nat.add_comm] using hsplitTA.symm
  have hT_dvd : p * u ∣ T := by
    unfold T
    refine Finset.dvd_sum ?_
    intro k hk
    have hk_mem : k ∈ Finset.range p := Finset.mem_of_mem_erase hk
    have hk_ne_zero : k ≠ 0 := Finset.mem_erase.mp hk |>.1
    have hk_ge_one : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk_ne_zero)
    by_cases hk_one : k = 1
    · have hchoose : p ∣ Nat.choose p (k + 1) := by
        rw [hk_one]
        apply hpack.hp.dvd_choose_self
        · decide
        · exact lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
      obtain ⟨c, hc0⟩ : ∃ c : ℕ, Nat.choose p (k + 1) = c * p :=
        exists_eq_mul_left_of_dvd hchoose
      have hc : Nat.choose p (k + 1) = p * c := by
        simpa [Nat.mul_comm] using hc0
      have hc2 : Nat.choose p 2 = p * c := by
        simpa [hk_one] using hc
      refine ⟨c * y ^ (p - 1 - k), ?_⟩
      calc
        (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k)
            = ((p * c) * u) * y ^ (p - 1 - k) := by
                rw [hk_one, hc2]
                simp [u, Nat.mul_assoc]
        _ = (p * u) * (c * y ^ (p - 1 - k)) := by
              ac_rfl
    · have hk_ge_two : 2 ≤ k := by omega
      have hk_decomp : k = (k - 2) + 2 := by omega
      have hu2 : u ^ 2 = (p * u) * a := by
        calc
          u ^ 2 = u * u := by simp [pow_two]
          _ = (p * a) * u := by simp [ha]
          _ = (p * u) * a := by ac_rfl
      refine ⟨(Nat.choose p (k + 1) : ℕ) * u ^ (k - 2) * a * y ^ (p - 1 - k), ?_⟩
      calc
        (Nat.choose p (k + 1) : ℕ) * u ^ k * y ^ (p - 1 - k)
            = (Nat.choose p (k + 1) : ℕ) * (u ^ (k - 2) * u ^ 2) * y ^ (p - 1 - k) := by
                rw [hk_decomp, pow_add]
                simp
        _ = (Nat.choose p (k + 1) : ℕ) * (u ^ (k - 2) * ((p * u) * a)) * y ^ (p - 1 - k) := by
              rw [hu2]
        _ = (p * u) * ((Nat.choose p (k + 1) : ℕ) * u ^ (k - 2) * a * y ^ (p - 1 - k)) := by
              ac_rfl
  obtain ⟨B, hB0⟩ : ∃ B : ℕ, T = B * (p * u) := exists_eq_mul_left_of_dvd hT_dvd
  have hB : T = (p * u) * B := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hB0
  refine ⟨B, ?_⟩
  have hEq : p * s ^ p = p * (y ^ (p - 1) + u * B) := by
    calc
      p * s ^ p = N := by simpa [N, u] using hsGN.symm
      _ = A + T := hsplit
      _ = p * y ^ (p - 1) + (p * u) * B := by rw [hB]
      _ = p * (y ^ (p - 1) + u * B) := by ring
  exact Nat.eq_of_mul_eq_mul_left hp_pos hEq

/--
`z - y = p^(p-1) * t^p` と組み合わせた gap-factor seed。

付録:
- `s^p - y^(p-1)` が
  `p^(p-1) * t^p`
  を 1 因子持つことを直接読むための theorem である。
- valuation peel route の seed として使う。
-/
theorem primeGe5BranchA_spow_eq_head_add_gapShape_mul
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ∃ B : ℕ, s ^ p = y ^ (p - 1) + (p ^ (p - 1) * t ^ p) * B := by
  rcases primeGe5BranchA_spow_eq_head_add_gap_mul hpack hp_dvd_gap hsGN with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rw [hB, hgap]

/--
`p ∣ t` なら、gap-shape の distinguished-prime 深さを 1 段剥ける。
-/
theorem primeGe5BranchA_gapShape_peel_of_dvd_t
    {p t : ℕ}
    (ht_dvd : p ∣ t) :
    ∃ t1 : ℕ, t = p * t1 ∧ p ^ (p - 1) * t ^ p = p ^ (2 * p - 1) * t1 ^ p := by
  obtain ⟨t1, ht0⟩ : ∃ t1 : ℕ, t = t1 * p := exists_eq_mul_left_of_dvd ht_dvd
  have ht : t = p * t1 := by simpa [Nat.mul_comm] using ht0
  refine ⟨t1, ht, ?_⟩
  calc
    p ^ (p - 1) * t ^ p = p ^ (p - 1) * ((p * t1) ^ p) := by rw [ht]
    _ = p ^ (p - 1) * (p ^ p * t1 ^ p) := by rw [Nat.mul_pow]
    _ = (p ^ (p - 1) * p ^ p) * t1 ^ p := by ac_rfl
    _ = p ^ ((p - 1) + p) * t1 ^ p := by rw [← Nat.pow_add]
    _ = p ^ (2 * p - 1) * t1 ^ p := by
      have hExp : (p - 1) + p = 2 * p - 1 := by omega
      simp [hExp]

/--
`p ∣ t` の valuation peel route に入るための concrete seed。

付録:
- これは `PrimeGe5BranchAValuationPeelSeedTarget` の default 実装である。
- smaller packet 自体はまだ構成しないが、
  `t = p * t1` と
  `s^p - y^(p-1)` の高い `p`-冪因子を同時に返す。
-/
theorem primeGe5BranchAValuationPeelSeed_default :
    PrimeGe5BranchAValuationPeelSeedTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  let _ := hsx
  let _ := hcop_ts
  let _ := hcop_ty
  let _ := hcop_sy
  let _ := hp_not_dvd_s
  rcases primeGe5BranchA_gapShape_peel_of_dvd_t ht_dvd with ⟨t1, ht, hpeel⟩
  rcases primeGe5BranchA_spow_eq_head_add_gapShape_mul hpack hp_dvd_gap hgap hsGN with ⟨B, hB⟩
  refine ⟨t1, B, ht, ?_⟩
  calc
    s ^ p = y ^ (p - 1) + (p ^ (p - 1) * t ^ p) * B := hB
    _ = y ^ (p - 1) + (p ^ (2 * p - 1) * t1 ^ p) * B := by rw [hpeel]
    _ = y ^ (p - 1) + p ^ (2 * p - 1) * (t1 ^ p * B) := by ac_rfl

/--
`p ∣ t` で 1 段剥いた canonical gap
`p^(p-1) * t1^p`
に対する `GN/p` tail の explicit 展開。

付録:
- これは `consider-005.md` でいう
  `seed -> canonical tail`
  の最初の concrete 実装である。
- まだ packet を返さず、
  宇宙式の標準 tail そのものを露出させる。
-/
theorem primeGe5BranchAValuationPeelCanonicalTail_default :
    PrimeGe5BranchAValuationPeelCanonicalTailTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  let _ := hp_dvd_gap
  let _ := hgap
  let _ := hsGN
  let _ := hsx
  let _ := hcop_ts
  let _ := hcop_ty
  let _ := hcop_sy
  let _ := hp_not_dvd_s
  rcases primeGe5BranchA_gapShape_peel_of_dvd_t ht_dvd with ⟨t1, ht, _hpeel⟩
  refine ⟨t1, DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y, ht, ?_⟩
  have hp_gt_one : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) hpack.hp5
  calc
    GN p (p ^ (p - 1) * t1 ^ p) y
        = (Nat.choose p 1 : ℕ) * y ^ (p - 1)
            + (p ^ (p - 1) * t1 ^ p) *
              DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y := by
            simpa [GN] using
              (DkMath.CosmicFormula.GN_tail_rec
                (d := p) (x := p ^ (p - 1) * t1 ^ p) (u := y) hp_gt_one)
    _ = p * y ^ (p - 1)
          + (p ^ (p - 1) * t1 ^ p) *
            DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y := by
          simp

/--
seed と canonical tail が揃えば、
valuation peel route の比較段は thin bridge で閉じる。

付録:
- ここで露出する本当の数学差分は
  `B`
  と
  `C`
  の関係だけである。
- 以後の段階分解では、
  `PrimeGe5BranchAValuationPeelTailComparisonTarget`
  を packet route の直前段として扱える。
-/
theorem primeGe5BranchAValuationPeelTailComparison_of_seed_and_canonical
    (hSeed : PrimeGe5BranchAValuationPeelSeedTarget)
    (hCanon : PrimeGe5BranchAValuationPeelCanonicalTailTarget) :
    PrimeGe5BranchAValuationPeelTailComparisonTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  rcases hSeed hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1, B, ht, hB⟩
  rcases hCanon hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1', C, ht', hC⟩
  have ht1_eq : t1 = t1' := by
    apply Nat.eq_of_mul_eq_mul_left hpack.hp.pos
    rw [← ht, ← ht']
  subst t1'
  exact ⟨t1, B, C, ht, hB, hC⟩

/-- comparison 段の default 実装。 -/
theorem primeGe5BranchAValuationPeelTailComparison_default :
    PrimeGe5BranchAValuationPeelTailComparisonTarget :=
  primeGe5BranchAValuationPeelTailComparison_of_seed_and_canonical
    primeGe5BranchAValuationPeelSeed_default
    primeGe5BranchAValuationPeelCanonicalTail_default

/--
`s^p = y^(p-1) + gap * B` と `GN p gap y = p * s^p` を合わせると、
`GTail p 2 gap y = p * B` となる。
-/
theorem primeGe5BranchA_gapTail_eq_p_mul_of_gapMul
    {p x y z s B : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hB : s ^ p = y ^ (p - 1) + (z - y) * B) :
    DkMath.CosmicFormula.GTail p 2 (z - y) y = p * B := by
  have hp_gt_one : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) hpack.hp5
  have hgap_pos : 0 < z - y := Nat.sub_pos_of_lt hpack.hyz_lt
  have hrec :
      GN p (z - y) y =
        p * y ^ (p - 1) + (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y := by
    calc
      GN p (z - y) y
          = (Nat.choose p 1 : ℕ) * y ^ (p - 1)
              + (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y := by
              simpa [GN] using
                (DkMath.CosmicFormula.GN_tail_rec (d := p) (x := z - y) (u := y) hp_gt_one)
      _ = p * y ^ (p - 1) + (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y := by
            simp
  have hEq :
      p * y ^ (p - 1) + (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y =
        p * y ^ (p - 1) + (z - y) * (p * B) := by
    calc
      p * y ^ (p - 1) + (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y
          = GN p (z - y) y := by simpa using hrec.symm
      _ = p * s ^ p := hsGN
      _ = p * (y ^ (p - 1) + (z - y) * B) := by rw [hB]
      _ = p * y ^ (p - 1) + (z - y) * (p * B) := by ring
  have hMul :
      (z - y) * DkMath.CosmicFormula.GTail p 2 (z - y) y =
        (z - y) * (p * B) := by
    exact Nat.add_left_cancel hEq
  exact Nat.eq_of_mul_eq_mul_left hgap_pos hMul

/--
`GN p u y = p * y^(p-1) + u * C` なら、
`C` は正確に `GTail p 2 u y` である。
-/
theorem primeGe5BranchA_canonicalTail_eq_coeff_of_expansion
    {p u y C : ℕ}
    (hp_gt_one : 1 < p)
    (hu_pos : 0 < u)
    (hC : GN p u y = p * y ^ (p - 1) + u * C) :
    DkMath.CosmicFormula.GTail p 2 u y = C := by
  have hrec :
      GN p u y =
        p * y ^ (p - 1) + u * DkMath.CosmicFormula.GTail p 2 u y := by
    calc
      GN p u y
          = (Nat.choose p 1 : ℕ) * y ^ (p - 1)
              + u * DkMath.CosmicFormula.GTail p 2 u y := by
              simpa [GN] using
                (DkMath.CosmicFormula.GN_tail_rec (d := p) (x := u) (u := y) hp_gt_one)
      _ = p * y ^ (p - 1) + u * DkMath.CosmicFormula.GTail p 2 u y := by simp
  have hEq :
      p * y ^ (p - 1) + u * DkMath.CosmicFormula.GTail p 2 u y =
        p * y ^ (p - 1) + u * C := by
    rw [← hrec, hC]
  have hMul :
      u * DkMath.CosmicFormula.GTail p 2 u y = u * C := by
    exact Nat.add_left_cancel hEq
  exact Nat.eq_of_mul_eq_mul_left hu_pos hMul

/--
`GTail p 2` は、`x = u` と `x = p^p * u` とで `mod u` では一致する。

付録:
- `GTail p 2 x y = head + x * GTail p 3 x y`
  の `head`
  は `x` に依らないので、
  `mod u`
  では両者とも同じ residue を持つ。
-/
theorem primeGe5BranchA_GTail_two_scaled_modEq
    {p u y : ℕ}
    (hp_gt_two : 2 < p) :
    DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y ≡
      DkMath.CosmicFormula.GTail p 2 u y [MOD u] := by
  let A : ℕ := (Nat.choose p 2 : ℕ) * y ^ (p - 2)
  have hScaled :
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y =
        A + u * (p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y) := by
    calc
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y
          = (Nat.choose p 2 : ℕ) * y ^ (p - 2)
              + (p ^ p * u) * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y := by
                simpa using
                  (DkMath.CosmicFormula.GTail_rec
                    (d := p) (r := 2) (x := p ^ p * u) (u := y) hp_gt_two)
      _ = A + u * (p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y) := by
            unfold A
            ac_rfl
  have hCanon :
      DkMath.CosmicFormula.GTail p 2 u y =
        A + u * DkMath.CosmicFormula.GTail p 3 u y := by
    calc
      DkMath.CosmicFormula.GTail p 2 u y
          = (Nat.choose p 2 : ℕ) * y ^ (p - 2)
              + u * DkMath.CosmicFormula.GTail p 3 u y := by
                simpa using
                  (DkMath.CosmicFormula.GTail_rec
                    (d := p) (r := 2) (x := u) (u := y) hp_gt_two)
      _ = A + u * DkMath.CosmicFormula.GTail p 3 u y := by rfl
  have hmodScaled : A ≡ DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y [MOD u] := by
    have hle : A ≤ DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y := by
      rw [hScaled]
      exact Nat.le_add_right _ _
    exact (Nat.modEq_iff_dvd' hle).2 ⟨p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y, by
      rw [hScaled]
      simp [A, Nat.mul_left_comm, Nat.mul_comm]⟩
  have hmodCanon : A ≡ DkMath.CosmicFormula.GTail p 2 u y [MOD u] := by
    have hle : A ≤ DkMath.CosmicFormula.GTail p 2 u y := by
      rw [hCanon]
      exact Nat.le_add_right _ _
    exact (Nat.modEq_iff_dvd' hle).2 ⟨DkMath.CosmicFormula.GTail p 3 u y, by
      rw [hCanon]
      simp [A]⟩
  exact hmodScaled.symm.trans hmodCanon

/--
`GTail p 2` は、`x = p^p * u` の方が `x = u` より大きい。

付録:
- `analysis-BC.md`
  の exact-error 版
  `p * B = C + u * E`
  を nat 上で書くための順序補題である。
-/
theorem primeGe5BranchA_GTail_two_scaled_ge
    {p u y : ℕ}
    (hp_gt_two : 2 < p) :
    DkMath.CosmicFormula.GTail p 2 u y ≤
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y := by
  unfold DkMath.CosmicFormula.GTail
  apply Finset.sum_le_sum
  intro k hk
  have hp_pos : 0 < p := lt_trans (by decide : 0 < 2) hp_gt_two
  have hu_le : u ≤ p ^ p * u := by
    calc
      u = 1 * u := by simp
      _ ≤ p ^ p * u := by
        apply Nat.mul_le_mul_right
        exact Nat.succ_le_of_lt (Nat.pow_pos hp_pos)
  have hpow : u ^ k ≤ (p ^ p * u) ^ k := Nat.pow_le_pow_left hu_le k
  have hmul1 :
      (Nat.choose p (2 + k) : ℕ) * u ^ k ≤
        (Nat.choose p (2 + k) : ℕ) * (p ^ p * u) ^ k := by
    exact Nat.mul_le_mul_left _ hpow
  have hmul2 :
      ((Nat.choose p (2 + k) : ℕ) * u ^ k) * y ^ (p - (2 + k)) ≤
        ((Nat.choose p (2 + k) : ℕ) * (p ^ p * u) ^ k) * y ^ (p - (2 + k)) := by
    exact Nat.mul_le_mul_right _ hmul1
  simpa [Nat.mul_assoc] using hmul2

/--
`GTail p 3 u y` も、scaled 側に `p^p` を掛けたもの以下で抑えられる。

付録:
- `GTail p 2` の explicit error を
  `GTail p 3`
  で書くための補助順序補題である。
-/
theorem primeGe5BranchA_GTail_three_scaled_mul_ge
    {p u y : ℕ}
    (hp_gt_two : 2 < p) :
    DkMath.CosmicFormula.GTail p 3 u y ≤
      p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y := by
  unfold DkMath.CosmicFormula.GTail
  have hsum :
      ∑ k ∈ Finset.range (p + 1 - 3), ↑(p.choose (3 + k)) * u ^ k * y ^ (p - (3 + k)) ≤
        ∑ k ∈ Finset.range (p + 1 - 3), ↑(p.choose (3 + k)) * (p ^ p * u) ^ k * y ^ (p - (3 + k)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hp_pos : 0 < p := lt_trans (by decide : 0 < 2) hp_gt_two
    have hu_le : u ≤ p ^ p * u := by
      calc
        u = 1 * u := by simp
        _ ≤ p ^ p * u := by
          apply Nat.mul_le_mul_right
          exact Nat.succ_le_of_lt (Nat.pow_pos hp_pos)
    have hpow : u ^ k ≤ (p ^ p * u) ^ k := Nat.pow_le_pow_left hu_le k
    have hmul1 :
        (Nat.choose p (3 + k) : ℕ) * u ^ k ≤
          (Nat.choose p (3 + k) : ℕ) * (p ^ p * u) ^ k := by
      exact Nat.mul_le_mul_left _ hpow
    have hmul2 :
        ((Nat.choose p (3 + k) : ℕ) * u ^ k) * y ^ (p - (3 + k)) ≤
          ((Nat.choose p (3 + k) : ℕ) * (p ^ p * u) ^ k) * y ^ (p - (3 + k)) := by
      exact Nat.mul_le_mul_right _ hmul1
    simpa [Nat.mul_assoc] using hmul2
  have hp_pos : 0 < p := lt_trans (by decide : 0 < 2) hp_gt_two
  calc
    ∑ k ∈ Finset.range (p + 1 - 3), ↑(p.choose (3 + k)) * u ^ k * y ^ (p - (3 + k))
      ≤ ∑ k ∈ Finset.range (p + 1 - 3), ↑(p.choose (3 + k)) * (p ^ p * u) ^ k * y ^ (p - (3 + k)) := hsum
    _ ≤ p ^ p *
        ∑ k ∈ Finset.range (p + 1 - 3), ↑(p.choose (3 + k)) * (p ^ p * u) ^ k * y ^ (p - (3 + k)) := by
          exact Nat.le_mul_of_pos_left _ (Nat.pow_pos hp_pos)

/--
`GTail p 2 (p^p * u) y` と `GTail p 2 u y` の差は `u` の倍数に分解できる。
-/
theorem primeGe5BranchA_GTail_two_scaled_exists_error
    {p u y : ℕ}
    (hp_gt_two : 2 < p) :
    ∃ E : ℕ,
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y =
        DkMath.CosmicFormula.GTail p 2 u y + u * E := by
  have hle :
      DkMath.CosmicFormula.GTail p 2 u y ≤
        DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y :=
    primeGe5BranchA_GTail_two_scaled_ge (p := p) (u := u) (y := y) hp_gt_two
  have hmod :
      DkMath.CosmicFormula.GTail p 2 u y ≡
        DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y [MOD u] :=
    (primeGe5BranchA_GTail_two_scaled_modEq (p := p) (u := u) (y := y) hp_gt_two).symm
  rcases (Nat.modEq_iff_dvd' hle).1 hmod with ⟨E, hE⟩
  refine ⟨E, ?_⟩
  simpa [Nat.add_comm] using (Nat.sub_eq_iff_eq_add hle).1 hE

/--
`GTail p 2` の scaled/canonical 差分は、
`GTail p 3`
の差から explicit に書ける。

付録:
- existential `E` にとどめず、
  `analysis-BC.md`
  の error term がどこから来るかを式で固定する。
- この式からは直ちに
  `E = 0`
  や
  `p ∣ E`
  は出ないため、
  valuation peel はやはり obstruction measurement と読むのが自然である。
-/
theorem primeGe5BranchA_GTail_two_scaled_error_explicit
    {p u y : ℕ}
    (hp_gt_two : 2 < p) :
    DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y =
      DkMath.CosmicFormula.GTail p 2 u y +
        u * (p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y
          - DkMath.CosmicFormula.GTail p 3 u y) := by
  let A : ℕ := (Nat.choose p 2 : ℕ) * y ^ (p - 2)
  let Ts : ℕ := DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y
  let Tc : ℕ := DkMath.CosmicFormula.GTail p 3 u y
  have hScaled :
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y = A + u * (p ^ p * Ts) := by
    calc
      DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y
          = (Nat.choose p 2 : ℕ) * y ^ (p - 2) + (p ^ p * u) * Ts := by
              simp [Ts]
              simpa using
                (DkMath.CosmicFormula.GTail_rec
                  (d := p) (r := 2) (x := p ^ p * u) (u := y) hp_gt_two)
      _ = A + u * (p ^ p * Ts) := by
            simp [A, Ts]
            ac_rfl
  have hCanon :
      DkMath.CosmicFormula.GTail p 2 u y = A + u * Tc := by
    calc
      DkMath.CosmicFormula.GTail p 2 u y
          = (Nat.choose p 2 : ℕ) * y ^ (p - 2) + u * Tc := by
              simp [Tc]
              simpa using
                (DkMath.CosmicFormula.GTail_rec
                  (d := p) (r := 2) (x := u) (u := y) hp_gt_two)
      _ = A + u * Tc := by simp [A, Tc]
  have hTc_le : Tc ≤ p ^ p * Ts := by
    simpa [Ts, Tc] using
      (primeGe5BranchA_GTail_three_scaled_mul_ge (p := p) (u := u) (y := y) hp_gt_two)
  have hmul_le : u * Tc ≤ u * (p ^ p * Ts) := Nat.mul_le_mul_left _ hTc_le
  calc
    DkMath.CosmicFormula.GTail p 2 (p ^ p * u) y = A + u * (p ^ p * Ts) := hScaled
    _ = A + (u * Tc + u * (p ^ p * Ts - Tc)) := by
          rw [Nat.mul_sub_left_distrib, Nat.add_sub_of_le hmul_le]
    _ = (A + u * Tc) + u * (p ^ p * Ts - Tc) := by ac_rfl
    _ = DkMath.CosmicFormula.GTail p 2 u y
          + u * (p ^ p * DkMath.CosmicFormula.GTail p 3 (p ^ p * u) y
              - DkMath.CosmicFormula.GTail p 3 u y) := by
          rw [← hCanon]

/--
comparison 段が与えられれば、
`B`
と
`C`
の exact tail identity は機械的に回収できる。
-/
theorem primeGe5BranchAValuationPeelTailExact_of_comparison
    (hCmp : PrimeGe5BranchAValuationPeelTailComparisonTarget) :
    PrimeGe5BranchAValuationPeelTailExactTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  rcases hCmp hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1, B, C, ht, hB, hC⟩
  have hp_gt_one : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) hpack.hp5
  have hgap_peel : z - y = p ^ (2 * p - 1) * t1 ^ p := by
    calc
      z - y = p ^ (p - 1) * t ^ p := hgap
      _ = p ^ (p - 1) * (p * t1) ^ p := by rw [ht]
      _ = p ^ (p - 1) * (p ^ p * t1 ^ p) := by rw [Nat.mul_pow]
      _ = (p ^ (p - 1) * p ^ p) * t1 ^ p := by ac_rfl
      _ = p ^ ((p - 1) + p) * t1 ^ p := by rw [Nat.pow_add]
      _ = p ^ (2 * p - 1) * t1 ^ p := by
            have hExp : (p - 1) + p = 2 * p - 1 := by omega
            simp [hExp]
  have hB_gap : s ^ p = y ^ (p - 1) + (z - y) * B := by
    calc
      s ^ p = y ^ (p - 1) + p ^ (2 * p - 1) * (t1 ^ p * B) := hB
      _ = y ^ (p - 1) + (p ^ (2 * p - 1) * t1 ^ p) * B := by ac_rfl
      _ = y ^ (p - 1) + (z - y) * B := by rw [hgap_peel]
  have hTailB :
      DkMath.CosmicFormula.GTail p 2 (z - y) y = p * B :=
    primeGe5BranchA_gapTail_eq_p_mul_of_gapMul hpack hsGN hB_gap
  have hu_pos : 0 < p ^ (p - 1) * t1 ^ p := by
    have hzy_pos : 0 < z - y := Nat.sub_pos_of_lt hpack.hyz_lt
    have hzy_eq : z - y = p ^ p * (p ^ (p - 1) * t1 ^ p) := by
      calc
        z - y = p ^ (2 * p - 1) * t1 ^ p := hgap_peel
        _ = p ^ ((p - 1) + p) * t1 ^ p := by
              have hExp : 2 * p - 1 = (p - 1) + p := by omega
              simp [hExp]
        _ = (p ^ (p - 1) * p ^ p) * t1 ^ p := by rw [Nat.pow_add]
        _ = p ^ p * (p ^ (p - 1) * t1 ^ p) := by ac_rfl
    exact Nat.pos_of_ne_zero (by
      intro hu0
      have hzero : z - y = 0 := by simp [hzy_eq, hu0]
      exact (Nat.ne_of_gt hzy_pos) hzero)
  have hTailC :
      DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y = C :=
    primeGe5BranchA_canonicalTail_eq_coeff_of_expansion hp_gt_one hu_pos hC
  exact ⟨t1, B, C, ht, hTailB, hTailC⟩

/--
exact tail identity が与えられれば、
`p * B ≡ C [MOD p^(p-1) * t1^p]`
が従う。
-/
theorem primeGe5BranchAValuationPeelTailModEq_of_exact
    (hExact : PrimeGe5BranchAValuationPeelTailExactTarget) :
    PrimeGe5BranchAValuationPeelTailModEqTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  rcases hExact hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1, B, C, ht, hTailB, hTailC⟩
  have hp_gt_two : 2 < p := lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
  have hgap_peel : z - y = p ^ p * (p ^ (p - 1) * t1 ^ p) := by
    calc
      z - y = p ^ (p - 1) * t ^ p := hgap
      _ = p ^ (p - 1) * (p * t1) ^ p := by rw [ht]
      _ = p ^ (p - 1) * (p ^ p * t1 ^ p) := by rw [Nat.mul_pow]
      _ = (p ^ (p - 1) * p ^ p) * t1 ^ p := by ac_rfl
      _ = p ^ ((p - 1) + p) * t1 ^ p := by rw [Nat.pow_add]
      _ = p ^ (p + (p - 1)) * t1 ^ p := by
            have hExp : (p - 1) + p = p + (p - 1) := by omega
            simp [hExp]
      _ = p ^ p * (p ^ (p - 1) * t1 ^ p) := by
            rw [Nat.pow_add]
            simp [Nat.mul_assoc]
  have hmodTail :
      DkMath.CosmicFormula.GTail p 2 (z - y) y ≡
        DkMath.CosmicFormula.GTail p 2 (p ^ (p - 1) * t1 ^ p) y [MOD p ^ (p - 1) * t1 ^ p] := by
    rw [hgap_peel]
    simpa using
      (primeGe5BranchA_GTail_two_scaled_modEq
        (p := p) (u := p ^ (p - 1) * t1 ^ p) (y := y) hp_gt_two)
  have hmodBC : p * B ≡ C [MOD p ^ (p - 1) * t1 ^ p] := by
    rw [← hTailB, ← hTailC]
    exact hmodTail
  exact ⟨t1, B, C, ht, hmodBC⟩

/-- mod-level comparison 段の default 実装。 -/
theorem primeGe5BranchAValuationPeelTailModEq_default :
    PrimeGe5BranchAValuationPeelTailModEqTarget :=
  primeGe5BranchAValuationPeelTailModEq_of_exact
    (primeGe5BranchAValuationPeelTailExact_of_comparison
      primeGe5BranchAValuationPeelTailComparison_default)

/-- exact-error 版の default 実装。 -/
theorem primeGe5BranchAValuationPeelTailError_of_exact
    (hExact : PrimeGe5BranchAValuationPeelTailExactTarget) :
    PrimeGe5BranchAValuationPeelTailErrorTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  rcases hExact hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1, B, C, ht, hTailB, hTailC⟩
  have hp_gt_two : 2 < p := lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
  let u : ℕ := p ^ (p - 1) * t1 ^ p
  have hgap_peel : z - y = p ^ p * u := by
    unfold u
    calc
      z - y = p ^ (p - 1) * t ^ p := hgap
      _ = p ^ (p - 1) * (p * t1) ^ p := by rw [ht]
      _ = p ^ (p - 1) * (p ^ p * t1 ^ p) := by rw [Nat.mul_pow]
      _ = p ^ p * (p ^ (p - 1) * t1 ^ p) := by ac_rfl
  rcases primeGe5BranchA_GTail_two_scaled_exists_error (p := p) (u := u) (y := y) hp_gt_two with
    ⟨E, hE⟩
  refine ⟨t1, B, C, E, ht, ?_⟩
  rw [← hTailB, ← hTailC]
  rw [hgap_peel]
  simpa [u, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hE

/-- exact-error comparison 段の default 実装。 -/
theorem primeGe5BranchAValuationPeelTailError_default :
    PrimeGe5BranchAValuationPeelTailErrorTarget :=
  primeGe5BranchAValuationPeelTailError_of_exact
    (primeGe5BranchAValuationPeelTailExact_of_comparison
      primeGe5BranchAValuationPeelTailComparison_default)

/--
tail-error lift があれば、valuation peel packet route は自動で従う。
-/
theorem primeGe5BranchAValuationPeelPacket_of_tailErrorLift
    (hErr : PrimeGe5BranchAValuationPeelTailErrorTarget)
    (hLift : PrimeGe5BranchAValuationPeelPacketFromErrorTarget) :
    PrimeGe5BranchAValuationPeelPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd
  rcases hErr hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd with
    ⟨t1, B, C, E, ht, hErrEq⟩
  exact hLift hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s ht_dvd ht hErrEq

/--
Branch A normal form から得る、`s^p ≡ y^(p-1) [MOD p^2]` の thin wrapper。

付録:
- `primeGe5BranchA_spow_eq_head_add_p_sq_mul` の concrete equality version を
  `Nat.ModEq` API に移し替えるだけの定理である。
- 次段で Wieferich witness の入力仕様が `Nat.ModEq` を要求するなら、
  まずこの theorem を経由すればよい。
-/
theorem primeGe5BranchA_spow_congr_head_mod_p_sq
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    s ^ p ≡ y ^ (p - 1) [MOD p ^ 2] := by
  rcases primeGe5BranchA_spow_eq_head_add_p_sq_mul hpack hp_dvd_gap hgap hsGN with ⟨M, hM⟩
  have hle : y ^ (p - 1) ≤ s ^ p := by
    rw [hM]
    exact Nat.le_add_right _ _
  have hmod : y ^ (p - 1) ≡ s ^ p [MOD p ^ 2] := by
    exact (Nat.modEq_iff_dvd' hle).2 ⟨M, by
      rw [hM]
      simp⟩
  exact hmod.symm

/--
Branch A の `q ≠ p` 側本丸:
`q ∣ gap` かつ `q ≠ p` なら `q ∤ GN p gap y`。
-/
theorem primeGe5BranchANoSharedPrimeOnGN_math :
    PrimeGe5BranchANoSharedPrimeOnGNTarget := by
  intro p x y z q hpack hp_dvd_gap hqP hqp hq_gap hq_GN
  have hcop_yz : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  have hq_gap_int : (q : ℤ) ∣ (((z - y : ℕ) : ℤ)) := by
    exact_mod_cast hq_gap
  have hq_GN_cast : (q : ℤ) ∣ ((GN p (z - y) y : ℕ) : ℤ) := by
    exact_mod_cast hq_GN
  have hq_GN_int :
      (q : ℤ) ∣ GN p (((z - y : ℕ) : ℤ)) (y : ℤ) := by
    simpa [GN] using hq_GN_cast
  have hq_gcd_int :
      q ∣ Int.gcd (((z - y : ℕ) : ℤ))
        (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    exact Int.dvd_gcd hq_gap_int hq_GN_int
  have hgapgcd_dvd_p :
      Int.gcd (((z - y : ℕ) : ℤ))
        (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
    exact DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int
      (hp1 := Nat.succ_le_of_lt hpack.hp.pos) (hyz := hpack.hyz_lt) (hcop := hcop_yz)
  have hq_dvd_p : q ∣ p := dvd_trans hq_gcd_int hgapgcd_dvd_p
  have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p
  exact hqp hq_eq_p

/--
`PrimeGe5BranchANoSharedPrimeOnGNTarget` が供給されれば、`q ≠ p` 側 factorization 条件が得られる。
-/
theorem primeGe5BranchAShapeFactorization_ne_p_of_noShared
    (hNoShared : PrimeGe5BranchANoSharedPrimeOnGNTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q := by
  intro p x y z hpack hp_dvd_gap q hqp
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hN0 : N ≠ 0 := by
    intro hN0
    have hx0pow : x ^ p = 0 := by simpa [hN0] using hxpow
    have hx0 : x = 0 := (Nat.pow_eq_zero.mp hx0pow).1
    exact hpack.hx0 hx0
  by_cases hqU : q ∣ u
  · by_cases hqP : Nat.Prime q
    · have hq_not_dvd_N : ¬ q ∣ N := by
        simpa [u, N] using hNoShared hpack hp_dvd_gap hqP hqp hqU
      have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
      have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
        simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
      have hpowq : (x ^ p).factorization q = p * x.factorization q := by
        simp [Nat.factorization_pow]
      have huq : u.factorization q = p * x.factorization q := by
        calc
          u.factorization q = u.factorization q + 0 := by simp
          _ = u.factorization q + N.factorization q := by simp [hNfac0]
          _ = (u * N).factorization q := by symm; exact hmulq
          _ = (x ^ p).factorization q := by simp [hxpow]
          _ = p * x.factorization q := hpowq
      exact ⟨x.factorization q, by simp [u, huq]⟩
    · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime u hqP
      exact ⟨0, by simp [u, hfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    exact ⟨0, by simp [u, hfac0]⟩

/-- Branch A shape-factorization の `q ≠ p` 側 clean 実装。 -/
theorem primeGe5BranchAShapeFactorization_ne_p_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q :=
  primeGe5BranchAShapeFactorization_ne_p_of_noShared
    primeGe5BranchANoSharedPrimeOnGN_math

/--
`q = p` 側の valuation 結論を factorization 形へ持ち上げる補助。
-/
theorem primeGe5BranchAShapeFactorization_p_of_padicValNat
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hVal : ∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m) :
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  have hgap_ne0 : (z - y) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  rcases hVal with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  calc
    (z - y).factorization p = padicValNat p (z - y) := by
      symm
      exact padicValNat_eq_factorization hpack.hp hgap_ne0
    _ = (p - 1) + p * m := hm

/-- Branch A shape-factorization の `q = p` 側 clean 実装（valuation 計算版）。 -/
theorem primeGe5BranchAShapeFactorization_p_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  intro p x y z hpack hp_dvd_gap
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
    simpa [u, N] using primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
  have hN0 : N ≠ 0 := by
    intro hN0
    exact hGN.2 (by simp [hN0])
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hNval : padicValNat p N = 1 :=
    primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp hGN.1 hGN.2
  have hVal : ∃ m : ℕ, padicValNat p u = (p - 1) + p * m := by
    exact primeGe5BranchAPadicValNat_gap_shape_of_mul_eq_pow
      (hp := hpack.hp)
      (hx0 := hpack.hx0)
      (hu0 := hu0)
      (hN0 := hN0)
      (hEq := hxpow)
      (hNval := hNval)
  simpa [u] using primeGe5BranchAShapeFactorization_p_of_padicValNat hpack hVal

/-- Branch A の shape witness `z - y = p^(p-1) * t^p` から `t > 0` を回収する。 -/
lemma primeGe5BranchAShapeWitness_t_pos
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    0 < t := by
  have hgap_pos : 0 < z - y := Nat.sub_pos_of_lt hpack.hyz_lt
  have ht_ne0 : t ≠ 0 := by
    intro ht0
    have hgap_zero : z - y = 0 := by
      calc
        z - y = p ^ (p - 1) * t ^ p := ht
        _ = 0 := by simp [ht0, hpack.hp.ne_zero]
    exact (Nat.ne_of_gt hgap_pos) hgap_zero
  exact Nat.pos_of_ne_zero ht_ne0

/--
shape-value から `q ≠ p` 側の指数整列
`p ∣ (z - y).factorization q`
を読み戻す。
-/
theorem primeGe5BranchAShapeFactorization_ne_p_of_value
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hShapeValue : ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) :
    ∀ q : ℕ, q ≠ p → p ∣ (z - y).factorization q := by
  intro q hq_ne
  rcases hShapeValue with ⟨t, ht⟩
  have ht_pos : 0 < t := primeGe5BranchAShapeWitness_t_pos hpack ht
  have hd0 : p ^ (p - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos hpack.hp.pos)
  have htp0 : t ^ p ≠ 0 := by
    exact pow_ne_zero p (Nat.ne_of_gt ht_pos)
  have hp_fac_q : p.factorization q = 0 := by
    by_cases hqP : Nat.Prime q
    · exact Nat.factorization_eq_zero_of_not_dvd (by
        intro hq_dvd_p
        exact hq_ne ((Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p))
    · exact Nat.factorization_eq_zero_of_not_prime p hqP
  have hd_fac_q : (p ^ (p - 1)).factorization q = 0 := by
    calc
      (p ^ (p - 1)).factorization q = (p - 1) * p.factorization q := by
        simp [Nat.factorization_pow]
      _ = 0 := by simp [hp_fac_q]
  have ht_fac_q : (t ^ p).factorization q = p * t.factorization q := by
    simp [Nat.factorization_pow]
  have hgap_fac_q : (z - y).factorization q = p * t.factorization q := by
    calc
      (z - y).factorization q = (p ^ (p - 1) * t ^ p).factorization q := by simp [ht]
      _ = (p ^ (p - 1)).factorization q + (t ^ p).factorization q := by
        simp [Nat.factorization_mul hd0 htp0]
      _ = 0 + p * t.factorization q := by
        rw [hd_fac_q, ht_fac_q]
      _ = p * t.factorization q := by simp
  exact ⟨t.factorization q, by simp [hgap_fac_q]⟩

/--
shape-value から `q = p` 側の指数形
`(z - y).factorization p = (p - 1) + p * m`
を読み戻す。
-/
theorem primeGe5BranchAShapeFactorization_p_of_value
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hShapeValue : ∃ t : ℕ, (z - y) = p ^ (p - 1) * t ^ p) :
    ∃ m : ℕ, (z - y).factorization p = (p - 1) + p * m := by
  rcases hShapeValue with ⟨t, ht⟩
  have ht_pos : 0 < t := primeGe5BranchAShapeWitness_t_pos hpack ht
  have hd0 : p ^ (p - 1) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos hpack.hp.pos)
  have htp0 : t ^ p ≠ 0 := by
    exact pow_ne_zero p (Nat.ne_of_gt ht_pos)
  have hd_fac_p : (p ^ (p - 1)).factorization p = p - 1 := by
    simpa using Nat.factorization_pow_self (p := p) (n := p - 1) hpack.hp
  have ht_fac_p : (t ^ p).factorization p = p * t.factorization p := by
    simp [Nat.factorization_pow]
  refine ⟨t.factorization p, ?_⟩
  calc
    (z - y).factorization p = (p ^ (p - 1) * t ^ p).factorization p := by simp [ht]
    _ = (p ^ (p - 1)).factorization p + (t ^ p).factorization p := by
      simp [Nat.factorization_mul hd0 htp0]
    _ = (p - 1) + p * t.factorization p := by
      rw [hd_fac_p, ht_fac_p]

/--
shape-value が供給されれば、Branch A の shape-factorization target へ戻せる。
-/
theorem primeGe5BranchAShapeFactorization_of_value
    (hValue : PrimeGe5BranchAShapeValueTarget) :
    PrimeGe5BranchAShapeFactorizationTarget := by
  intro p x y z hpack hp_dvd_gap
  have hShapeValue := hValue hpack hp_dvd_gap
  refine ⟨?_, ?_⟩
  · exact primeGe5BranchAShapeFactorization_ne_p_of_value hpack hp_dvd_gap hShapeValue
  · exact primeGe5BranchAShapeFactorization_p_of_value hpack hp_dvd_gap hShapeValue

/--
Branch A shape-factorization の clean 実装。

残る未完核を shape-value refuter 側へ押し込み、factorization spine は
BranchA lower layer だけで閉じる。
-/
theorem primeGe5BranchAShapeFactorization_default :
    PrimeGe5BranchAShapeFactorizationTarget := by
  intro p x y z hpack hp_dvd_gap
  exact ⟨primeGe5BranchAShapeFactorization_ne_p_default hpack hp_dvd_gap,
    primeGe5BranchAShapeFactorization_p_default hpack hp_dvd_gap⟩

/--
Branch A の shape-factorization から値域 shape へ送る clean 実装。

`z - y = p^(p-1) * t^p` を直接再構成する。
-/
theorem primeGe5BranchAShapeValue_of_factorization
    (hShape : PrimeGe5BranchAShapeFactorizationTarget) :
    PrimeGe5BranchAShapeValueTarget := by
  intro p x y z hpack hp_dvd_gap
  rcases hShape hpack hp_dvd_gap with ⟨hNe, hpPart⟩
  rcases hpPart with ⟨m, hm⟩
  let u : ℕ := z - y
  let d : ℕ := p ^ (p - 1)
  have hu_pos : 0 < u := by
    simpa [u] using Nat.sub_pos_of_lt hpack.hyz_lt
  have hu0 : u ≠ 0 := Nat.ne_of_gt hu_pos
  have hle : p - 1 ≤ u.factorization p := by
    rw [hm]
    exact Nat.le_add_right (p - 1) (p * m)
  have hdvd_u : d ∣ u := by
    unfold d
    exact (hpack.hp.pow_dvd_iff_le_factorization hu0).2 hle
  have hd_pos : 0 < d := by
    unfold d
    exact Nat.pow_pos hpack.hp.pos
  let w : ℕ := u / d
  have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd hu_pos hdvd_u) hd_pos
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw_pos
  have hfac_div : w.factorization = u.factorization - d.factorization := by
    simpa [w] using Nat.factorization_div hdvd_u
  have hall_w : ∀ q : ℕ, p ∣ w.factorization q := by
    intro q
    by_cases hq_eq : q = p
    · have hd_fac_p : d.factorization p = p - 1 := by
        unfold d
        simp [hpack.hp.factorization]
      have hm_u : u.factorization p = (p - 1) + p * m := by
        simpa [u] using hm
      have hw_fac_p : w.factorization p = p * m := by
        calc
          w.factorization p = u.factorization p - d.factorization p := by
            simpa using congrArg (fun f => f p) hfac_div
          _ = ((p - 1) + p * m) - (p - 1) := by simp [hm_u, hd_fac_p]
          _ = p * m := by omega
      exact ⟨m, by simp [hq_eq, hw_fac_p]⟩
    · by_cases hqP : Nat.Prime q
      · have hd_fac_q : d.factorization q = 0 := by
          unfold d
          rw [Nat.Prime.factorization_pow hpack.hp]
          simp [hq_eq]
        have hw_fac_q : w.factorization q = u.factorization q := by
          calc
            w.factorization q = u.factorization q - d.factorization q := by
              simpa using congrArg (fun f => f q) hfac_div
            _ = u.factorization q := by simp [hd_fac_q]
        rcases hNe q hq_eq with ⟨k, hk⟩
        exact ⟨k, by simpa [hw_fac_q, hk]⟩
      · have hw_fac0 : w.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime w hqP
        exact ⟨0, by simp [hw_fac0]⟩
  rcases exists_eq_pow_of_factorization_dvd
      (u := w) (p := p) hw0 hpack.hp.pos hall_w with ⟨t, ht⟩
  have hu_mul : u = d * w := by
    have hw_mul : w * d = u := by
      simpa [w] using Nat.div_mul_cancel hdvd_u
    simpa [Nat.mul_comm] using hw_mul.symm
  refine ⟨t, ?_⟩
  calc
    z - y = u := by rfl
    _ = d * w := hu_mul
    _ = p ^ (p - 1) * t ^ p := by simp [d, ht]

/--
Branch A では `q ≠ p` 側の `GN` 指数は `p` の倍数。
-/
theorem primeGe5BranchAGN_factorization_ne_p_math
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hqp : q ≠ p) :
    p ∣ (GN p (z - y) y).factorization q := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hN0 : N ≠ 0 := by
    intro hN0
    have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
      simpa [u, N] using primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
    exact hGN.2 (by simp [hN0])
  by_cases hqU : q ∣ u
  · have hq_not_dvd_N : ¬ q ∣ N := by
      simpa [u, N] using primeGe5BranchANoSharedPrimeOnGN_math hpack hp_dvd_gap hqP hqp hqU
    have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
    exact ⟨0, by simpa [N, hNfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
      simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
    have hpowq : (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    have hNq : N.factorization q = p * x.factorization q := by
      calc
        N.factorization q = 0 + N.factorization q := by simp
        _ = u.factorization q + N.factorization q := by simp [hfac0]
        _ = (u * N).factorization q := by symm; exact hmulq
        _ = (x ^ p).factorization q := by simp [hxpow]
        _ = p * x.factorization q := hpowq
    exact ⟨x.factorization q, by simpa [N, hNq]⟩

/--
Branch A では `GN` 自体が `p * s^p` 形になる。
`gapShape` はまだ使わない。
-/
theorem primeGe5BranchAGN_eq_p_mul_pow_math :
    PrimeGe5BranchAGNShapeTarget := by
  intro p x y z hpack hp_dvd_gap
  let N : ℕ := GN p (z - y) y
  have hp_dvd_N : p ∣ N := by
    simpa [N] using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).1
  have hN_not_sq : ¬ p ^ 2 ∣ N := by
    simpa [N] using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2
  have hN0 : N ≠ 0 := by
    intro hN0
    exact hN_not_sq (by simp [hN0])
  have hNfac_p : N.factorization p = 1 := by
    calc
      N.factorization p = padicValNat p N := by
        symm
        exact padicValNat_eq_factorization hpack.hp hN0
      _ = 1 := primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp hp_dvd_N hN_not_sq
  let w : ℕ := N / p
  have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hp_dvd_N) hpack.hp.pos
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw_pos
  have hfac_div : w.factorization = N.factorization - p.factorization := by
    simpa [w] using Nat.factorization_div hp_dvd_N
  have hall_w : ∀ q : ℕ, p ∣ w.factorization q := by
    intro q
    by_cases hq_eq : q = p
    · have hp_fac_p : p.factorization p = 1 := by
        simpa using congrArg (fun f => f p) hpack.hp.factorization
      have hw_fac_p : w.factorization p = 0 := by
        calc
          w.factorization p = N.factorization p - p.factorization p := by
            simpa using congrArg (fun f => f p) hfac_div
          _ = 1 - 1 := by simp [hNfac_p, hp_fac_p]
          _ = 0 := by simp
      exact ⟨0, by simp [hq_eq, hw_fac_p]⟩
    · by_cases hqP : Nat.Prime q
      · have hNq : p ∣ N.factorization q := by
          simpa [N] using primeGe5BranchAGN_factorization_ne_p_math hpack hp_dvd_gap hqP hq_eq
        have hp_fac_q : p.factorization q = 0 := by
          exact Nat.factorization_eq_zero_of_not_dvd (by
            intro hq_dvd_p
            exact hq_eq ((Nat.prime_dvd_prime_iff_eq hqP hpack.hp).1 hq_dvd_p))
        have hw_fac_q : w.factorization q = N.factorization q := by
          calc
            w.factorization q = N.factorization q - p.factorization q := by
              simpa using congrArg (fun f => f q) hfac_div
            _ = N.factorization q := by simp [hp_fac_q]
        rcases hNq with ⟨k, hk⟩
        exact ⟨k, by simp [hw_fac_q, hk]⟩
      · have hw_fac0 : w.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime w hqP
        exact ⟨0, by simp [hw_fac0]⟩
  rcases exists_eq_pow_of_factorization_dvd
      (u := w) (p := p) hw0 hpack.hp.pos hall_w with ⟨s, hs⟩
  have hN_mul : N = p * w := by
    have hw_mul : w * p = N := by
      simpa [w] using Nat.div_mul_cancel hp_dvd_N
    simpa [Nat.mul_comm] using hw_mul.symm
  refine ⟨s, ?_⟩
  calc
    GN p (z - y) y = N := by rfl
    _ = p * w := hN_mul
    _ = p * s ^ p := by simp [hs]

/--
Branch A witness から `gap`, `GN`, `x` の 3 つを同時に正規形へ揃える。
-/
theorem primeGe5BranchANormalForm_of_witness
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p ∧ x = p * (t * s) := by
  rcases primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  have hxpow : x ^ p = (z - y) * GN p (z - y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hpack.hp.pos)
  have hs' : GN p (p ^ (p - 1) * t ^ p) y = p * s ^ p := by
    simpa [ht] using hs
  have hpow_eq : x ^ p = (p * (t * s)) ^ p := by
    calc
      x ^ p = (z - y) * GN p (z - y) y := hxpow
      _ = (p ^ (p - 1) * t ^ p) * GN p (p ^ (p - 1) * t ^ p) y := by rw [ht]
      _ = (p ^ (p - 1) * t ^ p) * (p * s ^ p) := by rw [hs']
      _ = (p ^ (p - 1) * p) * (t ^ p * s ^ p) := by ac_rfl
      _ = p ^ ((p - 1) + 1) * (t ^ p * s ^ p) := by rw [← pow_succ]
      _ = p ^ p * (t ^ p * s ^ p) := by rw [hpred]
      _ = p ^ p * (t * s) ^ p := by rw [Nat.mul_pow]
      _ = (p * (t * s)) ^ p := by symm; exact Nat.mul_pow p (t * s) p
  exact (Nat.pow_left_injective hpack.hp.ne_zero) hpow_eq

/--
Branch A の `gcd(gap, GN)` が `p` を割るという制御を注入する abstract target。
-/
abbrev PrimeGe5BranchAGcdGapGNDvdPTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    Nat.gcd (z - y) (GN p (z - y) y) ∣ p

/--
`PrimeGe5CounterexamplePack` では、既存の gcd/GN API から
`gcd(gap, GN) ∣ p` を自然数版で直接回収できる。
-/
theorem primeGe5BranchAGcdGapGNDvdP_default :
    PrimeGe5BranchAGcdGapGNDvdPTarget := by
  intro p x y z hpack _hp_dvd_gap
  have hcop_zy : Nat.Coprime z y := by
    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
  exact DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
    (hp1 := Nat.succ_le_of_lt hpack.hp.pos) (hyz := hpack.hyz_lt) (hcop := hcop_zy)

/--
normal form から、`p * gcd(t,s)^p` は `gcd(gap, GN)` を割る。

gcd exactness の下半身。
-/
theorem primeGe5BranchANormalForm_p_mul_gcd_ts_pow_dvd_gcd_gap_GN
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    p * Nat.gcd t s ^ p ∣ Nat.gcd (z - y) (GN p (z - y) y) := by
  let g : ℕ := Nat.gcd t s
  have hg_t : g ∣ t := by
    exact Nat.gcd_dvd_left t s
  have hg_s : g ∣ s := by
    exact Nat.gcd_dvd_right t s
  have hgpow_tpow : g ^ p ∣ t ^ p := pow_dvd_pow_of_dvd hg_t p
  have hgpow_spow : g ^ p ∣ s ^ p := pow_dvd_pow_of_dvd hg_s p
  have hp_dvd_powPred : p ∣ p ^ (p - 1) := by
    exact dvd_pow_self p (Nat.sub_ne_zero_of_lt hpack.hp.one_lt)
  have hleft : p * g ^ p ∣ z - y := by
    have hmul : p * g ^ p ∣ p ^ (p - 1) * t ^ p := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_dvd_mul hp_dvd_powPred hgpow_tpow
    simpa [hgap] using hmul
  have hright : p * g ^ p ∣ GN p (z - y) y := by
    have hsGN' : GN p (z - y) y = p * s ^ p := hsGN
    have hmul : p * g ^ p ∣ p * s ^ p := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_dvd_mul (dvd_rfl : p ∣ p) hgpow_spow
    rw [hsGN']
    exact hmul
  exact Nat.dvd_gcd hleft hright

/--
`gcd(gap, GN) ∣ p` が与えられれば、normal form から `gcd(t,s) = 1` を抽出できる。
-/
theorem primeGe5BranchANormalForm_gcd_ts_eq_one_of_gcd_gap_GN_dvd_p
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hgcd_dvd_p : Nat.gcd (z - y) (GN p (z - y) y) ∣ p) :
    Nat.gcd t s = 1 := by
  let g : ℕ := Nat.gcd t s
  have hdiv : p * g ^ p ∣ p := by
    exact dvd_trans
      (primeGe5BranchANormalForm_p_mul_gcd_ts_pow_dvd_gcd_gap_GN hpack hp_dvd_gap hgap hsGN)
      hgcd_dvd_p
  rcases hdiv with ⟨k, hk⟩
  have hk' : p * 1 = p * (g ^ p * k) := by
    calc
      p * 1 = p := by simp
      _ = (p * g ^ p) * k := hk
      _ = p * (g ^ p * k) := by ac_rfl
  have h1 : 1 = g ^ p * k := Nat.eq_of_mul_eq_mul_left hpack.hp.pos hk'
  have hgpow_dvd_one : g ^ p ∣ 1 := ⟨k, h1⟩
  have hgpow_eq_one : g ^ p = 1 := Nat.eq_one_of_dvd_one hgpow_dvd_one
  have hg_eq : g ^ p = 1 ^ p := by simpa using hgpow_eq_one
  exact (Nat.pow_left_injective hpack.hp.ne_zero) hg_eq

/--
Branch A の既存 gcd 制御を使えば、normal form から `gcd(t,s) = 1` を default で抽出できる。
-/
theorem primeGe5BranchANormalForm_gcd_ts_eq_one_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.gcd t s = 1 := by
  exact primeGe5BranchANormalForm_gcd_ts_eq_one_of_gcd_gap_GN_dvd_p
    hpack hp_dvd_gap hgap hsGN
    (primeGe5BranchAGcdGapGNDvdP_default hpack hp_dvd_gap)

/--
normal form の `x = p * (t * s)` と反例 pack の `x ⟂ y` から、
`t * s` も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_ts_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime (t * s) y := by
  have hcop_y_pts : Nat.Coprime y (p * (t * s)) := by
    simpa [Nat.coprime_comm, hsx]
      using hpack.hxy
  have hparts : Nat.Coprime y p ∧ Nat.Coprime y (t * s) :=
    (Nat.coprime_mul_iff_right).1 hcop_y_pts
  simpa [Nat.coprime_comm] using hparts.2

/--
`t * s ⟂ y` なら、個別にも `t ⟂ y` と `s ⟂ y` が従う。
-/
theorem primeGe5BranchANormalForm_coprime_t_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime t y := by
  have hcop_y_ts : Nat.Coprime y (t * s) := by
    simpa [Nat.coprime_comm, mul_comm] using
      (primeGe5BranchANormalForm_coprime_ts_right hpack hsx)
  have hparts : Nat.Coprime y t ∧ Nat.Coprime y s :=
    (Nat.coprime_mul_iff_right).1 hcop_y_ts
  simpa [Nat.coprime_comm] using hparts.1

/--
`t * s ⟂ y` なら、個別にも `s ⟂ y` が従う。
-/
theorem primeGe5BranchANormalForm_coprime_s_right
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    Nat.Coprime s y := by
  have hcop_y_ts : Nat.Coprime y (t * s) := by
    simpa [Nat.coprime_comm, mul_comm] using
      (primeGe5BranchANormalForm_coprime_ts_right hpack hsx)
  have hparts : Nat.Coprime y t ∧ Nat.Coprime y s :=
    (Nat.coprime_mul_iff_right).1 hcop_y_ts
  simpa [Nat.coprime_comm] using hparts.2

/--
Branch A normal form では `t` と `s` 自体も互いに素になる。
-/
theorem primeGe5BranchANormalForm_coprime_ts_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.Coprime t s := by
  exact (Nat.coprime_iff_gcd_eq_one).2
    (primeGe5BranchANormalForm_gcd_ts_eq_one_default hpack hp_dvd_gap hgap hsGN)

/--
Branch A normal form では、既存の `gcd(gap, GN) ∣ p` と
`p ∣ gap`, `p ∣ GN` を合わせて `gcd(gap, GN) = p` まで exact に戻せる。
-/
theorem primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.gcd (z - y) (GN p (z - y) y) = p := by
  have hgcd_dvd_p :
      Nat.gcd (z - y) (GN p (z - y) y) ∣ p :=
    primeGe5BranchAGcdGapGNDvdP_default hpack hp_dvd_gap
  have hp_dvd_gcd :
      p ∣ Nat.gcd (z - y) (GN p (z - y) y) := by
    refine Nat.dvd_gcd hp_dvd_gap ?_
    rw [hsGN]
    exact dvd_mul_right p (s ^ p)
  rcases (Nat.dvd_prime hpack.hp).mp hgcd_dvd_p with hgcd_eq_one | hgcd_eq_p
  · have hp_dvd_one : p ∣ 1 := by
      rw [← hgcd_eq_one]
      exact hp_dvd_gcd
    have hp_eq_one : p = 1 := Nat.eq_one_of_dvd_one hp_dvd_one
    exact False.elim (hpack.hp.ne_one hp_eq_one)
  · exact hgcd_eq_p

/--
`GN = p * s^p` と `p^2 ∤ GN` から、normal form の `s` は `p` で割れない。
-/
theorem primeGe5BranchANormalForm_prime_not_dvd_s_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ¬ p ∣ s := by
  have hGN_not_sq : ¬ p ^ 2 ∣ GN p (z - y) y := by
    simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2
  intro hp_dvd_s
  have hp_dvd_spow : p ∣ s ^ p := dvd_pow hp_dvd_s hpack.hp.ne_zero
  have hp2_dvd_GN : p ^ 2 ∣ GN p (z - y) y := by
    rw [hsGN]
    have hmul : p * p ∣ p * s ^ p :=
      Nat.mul_dvd_mul_left p hp_dvd_spow
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  exact hGN_not_sq hp2_dvd_GN

/--
`p ∤ s` が取れれば、素数性から `p ⟂ s` へ直ちに上げられる。
-/
theorem primeGe5BranchANormalForm_coprime_p_s_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.Coprime p s := by
  exact (Nat.Prime.coprime_iff_not_dvd hpack.hp).2
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)

/--
Branch A では `p ∣ gap` と `gap ⟂ y` から `p ∤ y` が従う。
-/
theorem primeGe5BranchANormalForm_prime_not_dvd_y_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    ¬ p ∣ y := by
  simpa [PrimeGe5CounterexamplePack.gap] using
    hpack.prime_not_dvd_right_of_prime_dvd_gap hp_dvd_gap

/--
`p ∤ y` も、素数性から `p ⟂ y` の形へ上げておける。
-/
theorem primeGe5BranchANormalForm_coprime_p_y_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y)) :
    Nat.Coprime p y := by
  exact (Nat.Prime.coprime_iff_not_dvd hpack.hp).2
    (primeGe5BranchANormalForm_prime_not_dvd_y_default hpack hp_dvd_gap)

/--
For prime exponent `p`, we have `s^p ≡ s [MOD p]`.
-/
theorem primeGe5BranchANormalForm_spow_congr_self_mod_p
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p) :
    s ^ p ≡ s [MOD p] := by
  rw [← Int.natCast_modEq_iff, Nat.cast_pow]
  exact Int.ModEq.pow_prime_eq_self hpack.hp (s : ℤ)

/--
Branch A normal form forces `s ≡ 1 [MOD p]`.

付録:
- `s^p ≡ y^(p-1) [MOD p^2]` を mod `p` に落とし、
  Fermat on `y` と Frobenius on `s` を合わせた結果である。
-/
theorem primeGe5BranchANormalForm_s_congr_one_mod_p
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    s ≡ 1 [MOD p] := by
  have hspow_head_p2 :
      s ^ p ≡ y ^ (p - 1) [MOD p ^ 2] :=
    primeGe5BranchA_spow_congr_head_mod_p_sq hpack hp_dvd_gap hgap hsGN
  have hspow_head_p :
      s ^ p ≡ y ^ (p - 1) [MOD p] := by
    have htmp : s ^ p ≡ y ^ (p - 1) [MOD p * p] := by
      simpa [pow_two, Nat.mul_comm] using hspow_head_p2
    simpa using Nat.ModEq.of_mul_left p htmp
  have hy_one :
      y ^ (p - 1) ≡ 1 [MOD p] :=
    Nat.ModEq.pow_card_sub_one_eq_one (n := y) hpack.hp
      (primeGe5BranchANormalForm_coprime_p_y_default
        (p := p) (x := x) (y := y) (z := z) hpack hp_dvd_gap).symm
  have hspow_one : s ^ p ≡ 1 [MOD p] :=
    hspow_head_p.trans hy_one
  exact (primeGe5BranchANormalForm_spow_congr_self_mod_p hpack hp_dvd_gap hgap hsGN).symm.trans hspow_one

/--
If Branch A forces `s ≡ 1 [MOD p]`, then binomial expansion lifts it to
`s^p ≡ 1 [MOD p^2]`.

付録:
- `s = 1 + p * a` と書いて `exists_add_pow_prime_eq` を使うだけの局所補題である。
- 以後の Wieferich route では、`s^p ≡ y^(p-1) [MOD p^2]` と合成して
  `y^(p-1) ≡ 1 [MOD p^2]` を作る入口になる。
-/
theorem primeGe5BranchANormalForm_spow_congr_one_mod_p_sq
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    s ^ p ≡ 1 [MOD p ^ 2] := by
  have hs_congr_one : s ≡ 1 [MOD p] :=
    primeGe5BranchANormalForm_s_congr_one_mod_p hpack hp_dvd_gap hgap hsGN
  have hs_ne_zero : s ≠ 0 := by
    intro hs0
    have hGN_zero : GN p (z - y) y = 0 := by
      calc
        GN p (z - y) y = p * s ^ p := hsGN
        _ = 0 := by simp [hs0, hpack.hp.ne_zero]
    have hGN_ne :
        GN p (z - y) y ≠ 0 :=
      GN_ne_zero_nat_of_two_le
        (d := p) (x := z - y) (u := y)
        (le_trans (by decide : 2 ≤ 5) hpack.hp5)
        (Nat.sub_pos_of_lt hpack.hyz_lt)
        hpack.y_pos
    exact hGN_ne hGN_zero
  have hs_ge_one : 1 ≤ s := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs_ne_zero)
  have hp_dvd_s_sub_one : p ∣ s - 1 := by
    exact (Nat.modEq_iff_dvd' hs_ge_one).1 hs_congr_one.symm
  rcases hp_dvd_s_sub_one with ⟨a, ha⟩
  have hs_repr : s = 1 + p * a := by
    have htmp : s = p * a + 1 := by
      exact (Nat.sub_eq_iff_eq_add hs_ge_one).1 ha
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htmp
  rcases exists_add_pow_prime_eq hpack.hp (p * a) 1 with ⟨r, hr⟩
  have hs_pow_eq :
      s ^ p = (p * a) ^ p + 1 + p * (p * a) * r := by
    simpa [hs_repr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, one_pow] using hr
  have hp2_le_p : 2 ≤ p := le_trans (by decide : 2 ≤ 5) hpack.hp5
  have hp2_dvd_pow : p ^ 2 ∣ (p * a) ^ p := by
    refine ⟨p ^ (p - 2) * a ^ p, ?_⟩
    calc
      (p * a) ^ p = p ^ p * a ^ p := by rw [Nat.mul_pow]
      _ = p ^ (2 + (p - 2)) * a ^ p := by rw [Nat.add_sub_of_le hp2_le_p]
      _ = p ^ 2 * (p ^ (p - 2) * a ^ p) := by
        rw [Nat.pow_add]
        ring_nf
  have hp2_dvd_lin : p ^ 2 ∣ p * (p * a) * r := by
    refine ⟨a * r, ?_⟩
    simp [pow_two, Nat.mul_left_comm, Nat.mul_comm]
  have hs_pow_ge_one : 1 ≤ s ^ p := Nat.succ_le_of_lt (Nat.pow_pos (Nat.pos_of_ne_zero hs_ne_zero))
  have hmod : 1 ≡ s ^ p [MOD p ^ 2] := by
    refine (Nat.modEq_iff_dvd' hs_pow_ge_one).2 ?_
    have hs_sub_eq :
        s ^ p - 1 = (p * a) ^ p + p * (p * a) * r := by
      rw [hs_pow_eq]
      omega
    rw [hs_sub_eq]
    exact dvd_add hp2_dvd_pow hp2_dvd_lin
  exact hmod.symm

/--
Branch A normal form already yields a Wieferich-style witness on `y`.

付録:
- `s^p ≡ y^(p-1) [MOD p^2]` と `s^p ≡ 1 [MOD p^2]` を合成しただけの thin wrapper。
- この theorem は `False` を直接返さないが、Wieferich bridge へ渡す最初の concrete witness として使う。
-/
theorem primeGe5BranchANormalForm_y_wieferich_mod_p_sq
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hhead :
      s ^ p ≡ y ^ (p - 1) [MOD p ^ 2] :=
    primeGe5BranchA_spow_congr_head_mod_p_sq hpack hp_dvd_gap hgap hsGN
  have hspow_one :
      s ^ p ≡ 1 [MOD p ^ 2] :=
    primeGe5BranchANormalForm_spow_congr_one_mod_p_sq hpack hp_dvd_gap hgap hsGN
  exact hhead.symm.trans hspow_one

/--
Branch A 全体から直接取り出す、`y` 上の Wieferich-style witness。

付録:
- `gap` shape と `GN` shape の既定実装を使い、
  lower-layer output を `PrimeGe5BranchAWieferichOnYTarget` へ正規化する thin wrapper。
- `Basic` や gap-invariant 側が将来 Branch A を再配線する際の最小入口として使う。
-/
theorem primeGe5BranchAWieferichOnY_default :
    PrimeGe5BranchAWieferichOnYTarget := by
  intro p x y z hpack hp_dvd_gap
  rcases primeGe5BranchAShapeValue_of_factorization
      primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with ⟨t, hgap⟩
  rcases primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with ⟨s, hsGN⟩
  exact primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN

/--
反例 pack の基本恒等式 `x^p = gap * GN` と `x ⟂ y` から、
`GN p (z - y) y` 自体も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_GN_right_default
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z) :
    Nat.Coprime (GN p (z - y) y) y := by
  have hcop_xpow_y : Nat.Coprime (x ^ p) y :=
    Nat.Coprime.pow_left p hpack.hxy
  have hcop_prod_y : Nat.Coprime ((z - y) * GN p (z - y) y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using
      (hpack.xpow_eq_gap_mul_GN ▸ hcop_xpow_y)
  have hcop_y_prod : Nat.Coprime y ((z - y) * GN p (z - y) y) := hcop_prod_y.symm
  have hparts :
      Nat.Coprime y (z - y) ∧ Nat.Coprime y (GN p (z - y) y) :=
    (Nat.coprime_mul_iff_right).1 hcop_y_prod
  simpa [Nat.coprime_comm] using hparts.2

/--
`GN ⟂ y` と `GN = p * s^p` を合わせると、
`p * s^p` そのものも `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_pspow_y_default
    {p x y z s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_GNy : Nat.Coprime (GN p (z - y) y) y) :
    Nat.Coprime (p * s ^ p) y := by
  rw [← hsGN]
  exact hcop_GNy

/--
`p * s^p ⟂ y` から `s^p ⟂ y` を抜き出す。
-/
theorem primeGe5BranchANormalForm_coprime_spow_y_default
    {p x y z s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_GNy : Nat.Coprime (GN p (z - y) y) y) :
    Nat.Coprime (s ^ p) y := by
  have hcop_pspow_y : Nat.Coprime (p * s ^ p) y :=
    primeGe5BranchANormalForm_coprime_pspow_y_default hpack hsGN hcop_GNy
  exact (Nat.coprime_mul_iff_left).1 hcop_pspow_y |>.2

/--
`p ⟂ s` なら冪に上げても `p ⟂ s^p` は保たれる。
-/
theorem primeGe5BranchANormalForm_coprime_p_spow_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hcop_ps : Nat.Coprime p s) :
    Nat.Coprime p (s ^ p) := by
  exact Nat.Coprime.pow_right p hcop_ps

/--
`p ⟂ y` と `s ⟂ y` から、線形因子 `p * s` も `y` と互いに素である。
-/
theorem primeGe5BranchANormalForm_coprime_ps_y_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (_hsx : x = p * (t * s))
    (hcop_sy : Nat.Coprime s y) :
    Nat.Coprime (p * s) y := by
  have hcop_py : Nat.Coprime p y :=
    primeGe5BranchANormalForm_coprime_p_y_default hpack hp_dvd_gap
  exact Nat.Coprime.mul_left hcop_py hcop_sy

/--
normal form の `x = p * (t * s)` は、線形因子 `(t, p * s)` の積に並べ替えられる。
-/
theorem primeGe5BranchANormalForm_x_eq_t_mul_ps
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hsx : x = p * (t * s)) :
    x = t * (p * s) := by
  calc
    x = p * (t * s) := hsx
    _ = t * (p * s) := by ac_rfl

/--
`t ⟂ y` と `(p * s) ⟂ y` が揃えば、線形分解 `t * (p * s)` も `y` と互いに素。
-/
theorem primeGe5BranchANormalForm_coprime_t_ps_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (_hsx : x = p * (t * s))
    (hcop_ty : Nat.Coprime t y)
    (hcop_psy : Nat.Coprime (p * s) y) :
    Nat.Coprime (t * (p * s)) y := by
  exact Nat.Coprime.mul_left hcop_ty hcop_psy

/--
`x = t * (p * s)` を基準形にすると、`x^p` はそのまま `(t * (p * s))^p` に一致する。
-/
theorem primeGe5BranchANormalForm_xpow_eq_tps_pow
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s)) :
    x ^ p = (t * (p * s)) ^ p := by
  simp [hx_tps]

/--
`x = t * (p * s)` の基準形では、`x^p` の factorization も
`p * ((t * (p * s)).factorization q)` に exact に戻る。
-/
theorem primeGe5BranchANormalForm_xpow_factorization_exact
    {p x y z t s q : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hx_tps : x = t * (p * s)) :
    (x ^ p).factorization q = p * (t * (p * s)).factorization q := by
  calc
    (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    _ = p * (t * (p * s)).factorization q := by
      simp [hx_tps]

/--
`gap = p^(p-1) * t^p` と `GN = p * s^p` を掛け合わせると、
右辺全体は `(t * (p * s))^p` に再構成できる。
-/
theorem primeGe5BranchANormalForm_gapGN_eq_tps_pow
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p := by
  have hp_eq : p = (p - 1) + 1 := by
    simpa [Nat.pred_eq_sub_one] using (Nat.succ_pred_eq_of_pos hpack.hp.pos).symm
  calc
    (z - y) * GN p (z - y) y
        = (z - y) * (p * s ^ p) := by
            rw [hsGN]
    _ = (p ^ (p - 1) * t ^ p) * (p * s ^ p) := by
          rw [hgap]
    _ = p ^ p * (t ^ p * s ^ p) := by
          rw [show p ^ p = p ^ (p - 1) * p by
                rw [hp_eq, Nat.pow_succ']
                simp [Nat.mul_comm]]
          ac_rfl
    _ = p ^ p * (t * s) ^ p := by
          rw [Nat.mul_pow]
    _ = (p * (t * s)) ^ p := by
          symm
          rw [Nat.mul_pow]
    _ = (t * (p * s)) ^ p := by
          symm
          congr 1
          ac_rfl

/--
`gap * GN` 側も、normal form では `p * ((t * (p * s)).factorization q)` に
exact に戻る。
-/
theorem primeGe5BranchANormalForm_gapGN_factorization_exact
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q := by
  calc
    ((z - y) * GN p (z - y) y).factorization q
        = ((t * (p * s)) ^ p).factorization q := by
            rw [primeGe5BranchANormalForm_gapGN_eq_tps_pow hpack hp_dvd_gap hgap hsGN]
    _ = p * (t * (p * s)).factorization q := by
          simp [Nat.factorization_pow]

/-- Branch A の shape witness から `p^(p-1) ∣ z-y` を回収する。 -/
lemma primeGe5BranchAShapeWitness_powPred_dvd_gap
    {p y z t : ℕ}
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    p ^ (p - 1) ∣ (z - y) := by
  refine ⟨t ^ p, ?_⟩
  simpa [Nat.mul_comm] using ht

/-- Branch A shape witness から既存 descent 契約へ渡す最小入力。 -/
structure PrimeGe5BranchAShapeWitnessDescentInput (p x y z t : ℕ) : Prop where
  tPos : 0 < t
  powPredDvdGap : p ^ (p - 1) ∣ (z - y)
  gapShape : z - y = p ^ (p - 1) * t ^ p

/-- `ht` から Branch A witness の最小 descent 入力を組み立てる。 -/
theorem primeGe5BranchAShapeWitness_to_descent_input
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    PrimeGe5BranchAShapeWitnessDescentInput p x y z t := by
  exact ⟨primeGe5BranchAShapeWitness_t_pos hpack ht,
    primeGe5BranchAShapeWitness_powPred_dvd_gap ht, ht⟩

/--
Branch A の witness 直受け最終 kernel。

`hpack + hp_dvd_gap + ht` から `False` を導く一点集中の差し替え口として固定する。
-/
abbrev PrimeGe5BranchAShapeWitnessKernelTarget : Prop :=
  ∀ {p x y z t : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    PrimeGe5BranchAShapeWitnessDescentInput p x y z t →
    False

/--
Branch A の局所数学核。

normal form をどう矛盾へ送るかだけを担う最終差し替え口。
-/
abbrev PrimeGe5BranchANormalFormRefuterTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    False

/--
normal form refuter の残核。

ここでは既に抽出済みの
`gcd(gap, GN) = p`,
`t ⟂ s`,
`t ⟂ y`,
`s ⟂ y`,
`p ∤ s`
だけを入力として、最後の局所矛盾へ集中する。
-/
abbrev PrimeGe5BranchANormalFormArithmeticKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    False

/--
arithmetic kernel のさらに下の局所差し替え口。

`p ⟂ s` と `p ∤ y` まで明示入力にして、
最後の衝突だけへ責務をさらに寄せる。
-/
abbrev PrimeGe5BranchANormalFormLocalCoprimeKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    False

/--
local coprime kernel のさらに下で、`GN ⟂ y` を explicit に受ける差し替え口。

`GN` 側の局所情報へ戻して衝突させる場合、この契約 1 本を詰めればよい。
-/
abbrev PrimeGe5BranchANormalFormGNRightKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    False

/--
GN-side kernel のさらに下で、`GN = p * s^p` の factor-level coprime 情報
まで explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormGNFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    False

/--
GN factor kernel のさらに下で、`p ⟂ s^p` と `p * s ⟂ y` まで
explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormGNLinearFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    False

/--
GN linear-factor kernel のさらに下で、`x = t * (p * s)` と
`Nat.Coprime (t * (p * s)) y` まで explicit に並べる差し替え口。
-/
abbrev PrimeGe5BranchANormalFormXFactorKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    False

/--
`x` 側の最後の差し替え口。

ここでは `x = t * (p * s)` に加え、`x^p` の exactness を
等式と factorization の両方で explicit に受ける。
-/
abbrev PrimeGe5BranchANormalFormXPowExactKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    False

/--
`x^p` 側 / `gap * GN` 側の exactness 比較だけを残す最終差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowComparisonKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    False

/--
comparison kernel の equality-part。

shared normal form から `x^p = gap * GN` へ戻すだけの薄い橋を明示分離する。
-/
abbrev PrimeGe5BranchANormalFormPowEqualityPartTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    x ^ p = (z - y) * GN p (z - y) y

/--
comparison kernel の factorization-part。

equality-part で `x^p = gap * GN` を回収した後、指数比較だけに集中する。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationPartTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
factorization-part の `q = p` 側。

`p`-進指数の比較だけを isolated に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationAtPTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (x ^ p).factorization p = p * (t * (p * s)).factorization p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    ((z - y) * GN p (z - y) y).factorization p =
      p * (t * (p * s)).factorization p →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
factorization-part の `q ≠ p` 側。

`q ≠ p` に対する指数比較だけを isolated に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationNePTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    False

/--
`q = p` 側の valuation 文脈だけを explicit に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationAtPValuationTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (x ^ p).factorization p = p * (t * (p * s)).factorization p →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    ((z - y) * GN p (z - y) y).factorization p =
      p * (t * (p * s)).factorization p →
    x ^ p = (z - y) * GN p (z - y) y →
    (∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m) →
    padicValNat p (GN p (z - y) y) = 1 →
    False

/--
`q ≠ p` 側の factorization spine だけを explicit に受ける差し替え口。
-/
abbrev PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    x = t * (p * s) →
    Nat.gcd (z - y) (GN p (z - y) y) = p →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    Nat.Coprime p s →
    ¬ p ∣ y →
    Nat.Coprime (GN p (z - y) y) y →
    Nat.Coprime (p * s ^ p) y →
    Nat.Coprime (s ^ p) y →
    Nat.Coprime p (s ^ p) →
    Nat.Coprime (p * s) y →
    Nat.Coprime (t * (p * s)) y →
    x ^ p = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → (x ^ p).factorization q = p * (t * (p * s)).factorization q) →
    (z - y) * GN p (z - y) y = (t * (p * s)) ^ p →
    (∀ q : ℕ, q ≠ p → ((z - y) * GN p (z - y) y).factorization q =
      p * (t * (p * s)).factorization q) →
    x ^ p = (z - y) * GN p (z - y) y →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → p ∣ (z - y).factorization q) →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → p ∣ (GN p (z - y) y).factorization q) →
    False

/--
`q ≠ p` 側 comparison が実際に使っているのは、
support separation だけだと判明したので、
最後の残核をその形に切り出しておく。
-/
abbrev PrimeGe5BranchANormalFormNePSupportKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    Nat.Coprime t s →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ t → ¬ q ∣ s) →
    (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ s → ¬ q ∣ t) →
    False

/--
`q ≠ p` の support separation が本当に新情報でなければ、
最終核は `Nat.Coprime t s` だけを受ける checkpoint へさらに縮む。
-/
abbrev PrimeGe5BranchANormalFormNePCoprimeKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    Nat.Coprime t s →
    False

/--
shape-value refuter は、最終的には witness-kernel 1 本の注入へ還元する。
-/
theorem primeGe5BranchAShapeValueToRefuter_of_witness_kernel
    (hKernel : PrimeGe5BranchAShapeWitnessKernelTarget) :
    PrimeGe5BranchAShapeValueToRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hShape
  rcases hShape with ⟨t, ht⟩
  exact hKernel hpack hp_dvd_gap
    (primeGe5BranchAShapeWitness_to_descent_input hpack hp_dvd_gap ht)

/--
normal-form refuter があれば、witness kernel は薄い橋で閉じる。
-/
theorem primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter
    (hRef : PrimeGe5BranchANormalFormRefuterTarget) :
    PrimeGe5BranchAShapeWitnessKernelTarget := by
  intro p x y z t hpack hp_dvd_gap hInput
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap hInput.gapShape with
    ⟨s, hsGN, hsx⟩
  exact hRef hpack hp_dvd_gap hInput.gapShape hsGN hsx

/--
normal form refuter は、最後の arithmetic kernel 1 本へ further reduce できる。
-/
theorem primeGe5BranchANormalFormRefuter_of_arithmetic_kernel
    (hKernel : PrimeGe5BranchANormalFormArithmeticKernelTarget) :
    PrimeGe5BranchANormalFormRefuterTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_coprime_t_right hpack hsx)
    (primeGe5BranchANormalForm_coprime_s_right hpack hsx)
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)

/--
arithmetic kernel は、`p ⟂ s` と `p ∤ y` を明示入力にした
さらに小さい local kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormArithmeticKernel_of_localCoprimeKernel
    (hKernel : PrimeGe5BranchANormalFormLocalCoprimeKernelTarget) :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s
    (primeGe5BranchANormalForm_coprime_p_s_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_prime_not_dvd_y_default hpack hp_dvd_gap)

/--
local coprime kernel は、`GN ⟂ y` を explicit に受ける
さらに小さい GN-side kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormLocalCoprimeKernel_of_GNRightKernel
    (hKernel : PrimeGe5BranchANormalFormGNRightKernelTarget) :
    PrimeGe5BranchANormalFormLocalCoprimeKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y
    (primeGe5BranchANormalForm_coprime_GN_right_default hpack)

/--
GN-side kernel は、`p * s^p ⟂ y` と `s^p ⟂ y` を explicit に受ける
さらに小さい factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNRightKernel_of_factorKernel
    (hKernel : PrimeGe5BranchANormalFormGNFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNRightKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy
    (primeGe5BranchANormalForm_coprime_pspow_y_default hpack hsGN hp_cop_GNy)
    (primeGe5BranchANormalForm_coprime_spow_y_default hpack hsGN hp_cop_GNy)

/--
GN factor kernel は、`p ⟂ s^p` と `p * s ⟂ y` を explicit に受ける
さらに小さい linear-factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNFactorKernel_of_linearFactorKernel
    (hKernel : PrimeGe5BranchANormalFormGNLinearFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y
    (primeGe5BranchANormalForm_coprime_p_spow_default hpack hp_dvd_gap hgap hsGN hp_cop_ps)
    (primeGe5BranchANormalForm_coprime_ps_y_default hpack hp_dvd_gap hgap hsGN hsx hp_cop_sy)

/--
GN linear-factor kernel は、`x = t * (p * s)` と
`Nat.Coprime (t * (p * s)) y` を explicit に受ける
さらに小さい x-factor kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormGNLinearFactorKernel_of_xFactorKernel
    (hKernel : PrimeGe5BranchANormalFormXFactorKernelTarget) :
    PrimeGe5BranchANormalFormGNLinearFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_x_eq_t_mul_ps hpack hp_dvd_gap hgap hsGN hsx)
    hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y
    (primeGe5BranchANormalForm_coprime_t_ps_default hpack hp_dvd_gap hgap hsGN hsx hp_cop_ty hp_cop_ps_y)

/--
X-factor kernel は、`x^p` の基準形 exactness を explicit に受ける
さらに小さい xpow-exact kernel へ reduce できる。
-/
theorem primeGe5BranchANormalFormXFactorKernel_of_xpowExactKernel
    (hKernel : PrimeGe5BranchANormalFormXPowExactKernelTarget) :
    PrimeGe5BranchANormalFormXFactorKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y
    (primeGe5BranchANormalForm_xpow_eq_tps_pow hpack hp_dvd_gap hgap hsGN hx_tps)
    (fun q => primeGe5BranchANormalForm_xpow_factorization_exact hpack hp_dvd_gap hgap hsGN hx_tps)

/--
X-pow exact kernel は、`gap * GN` 側の exactness も explicit に受ける
comparison kernel へ further reduce できる。
-/
theorem primeGe5BranchANormalFormXPowExactKernel_of_powComparisonKernel
    (hKernel : PrimeGe5BranchANormalFormPowComparisonKernelTarget) :
    PrimeGe5BranchANormalFormXPowExactKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow
  exact hKernel hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow
    (primeGe5BranchANormalForm_gapGN_eq_tps_pow hpack hp_dvd_gap hgap hsGN)
    (fun q => primeGe5BranchANormalForm_gapGN_factorization_exact hpack hp_dvd_gap hgap hsGN)

/--
equality-part と factorization-part が揃えば、comparison kernel は橋だけで閉じる。
-/
theorem primeGe5BranchANormalFormPowComparisonKernel_of_parts
    (hEqPart : PrimeGe5BranchANormalFormPowEqualityPartTarget)
    (hFacPart : PrimeGe5BranchANormalFormPowFactorizationPartTarget) :
    PrimeGe5BranchANormalFormPowComparisonKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN
  have hEq :
      x ^ p = (z - y) * GN p (z - y) y :=
    hEqPart hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hgapGN_tps
  exact hFacPart hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq

/--
comparison kernel の equality-part 実装入口。

ここは obstruction ではなく、pack 由来の `x^p = gap * GN` を
explicit に戻すだけの薄い橋である。
-/
theorem primeGe5BranchANormalFormPowEqualityPart_default :
    PrimeGe5BranchANormalFormPowEqualityPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hgapGN_tps
  let _ := t
  let _ := s
  let _ := hp_dvd_gap
  let _ := hgap
  let _ := hsGN
  let _ := hsx
  let _ := hx_tps
  let _ := hgcd_eq
  let _ := hp_cop_ts
  let _ := hp_cop_ty
  let _ := hp_cop_sy
  let _ := hp_not_dvd_s
  let _ := hp_cop_ps
  let _ := hp_not_dvd_y
  let _ := hp_cop_GNy
  let _ := hp_cop_pspow_y
  let _ := hp_cop_spow_y
  let _ := hp_cop_pspow
  let _ := hp_cop_ps_y
  let _ := hp_cop_tps_y
  let _ := hxpow_tps
  let _ := hgapGN_tps
  simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN

/--
`q = p` / `q ≠ p` の 2 部品が揃えば、factorization-part は橋だけで閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_of_cases
    (hAtP : PrimeGe5BranchANormalFormPowFactorizationAtPTarget)
    (_hNeP : PrimeGe5BranchANormalFormPowFactorizationNePTarget) :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq
  have hAtPFalse : False := by
    exact hAtP hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps
      (hfac_xpow p) hgapGN_tps (hfac_gapGN p) hEq
  exact hAtPFalse

/--
`q ≠ p` 側だけで十分なら、factorization-part はそのまま thin bridge で閉じられる。

現状の mainline では、true obstruction はこちらに寄ると見てよい。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_of_neP
    (hNeP : PrimeGe5BranchANormalFormPowFactorizationNePTarget) :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow hgapGN_tps hfac_gapGN hEq
  exact hNeP hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps
    (fun q hqp => hfac_xpow q)
    hgapGN_tps
    (fun q hqp => hfac_gapGN q)
    hEq

/--
valuation kernel があれば、`q = p` 側 factorization target は薄い橋で閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationAtP_of_valuationKernel
    (hVal : PrimeGe5BranchANormalFormPowFactorizationAtPValuationTarget) :
    PrimeGe5BranchANormalFormPowFactorizationAtPTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_p hgapGN_tps hfac_gapGN_p hEq
  have hgapVal : ∃ m : ℕ, padicValNat p (z - y) = (p - 1) + p * m := by
    rcases primeGe5BranchAShapeFactorization_p_of_value hpack hp_dvd_gap ⟨t, hgap⟩ with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hgap_ne0 : (z - y) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
    calc
      padicValNat p (z - y) = (z - y).factorization p := by
        exact padicValNat_eq_factorization hpack.hp hgap_ne0
      _ = (p - 1) + p * m := hm
  have hGNVal : padicValNat p (GN p (z - y) y) = 1 := by
    exact primeGe5BranchAPadicValNat_eq_one_of_dvd_not_sq hpack.hp
      (by
        simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).1)
      (by
        simpa using (primeGe5BranchAP_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap).2)
  exact hVal hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_p hgapGN_tps hfac_gapGN_p hEq hgapVal hGNVal

/--
spine kernel があれば、`q ≠ p` 側 factorization target は薄い橋で閉じる。
-/
theorem primeGe5BranchANormalFormPowFactorizationNeP_of_spineKernel
    (hSpine : PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget) :
    PrimeGe5BranchANormalFormPowFactorizationNePTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq
  exact hSpine hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq
    (fun q _hqP hqp =>
      primeGe5BranchAShapeFactorization_ne_p_of_value hpack hp_dvd_gap ⟨t, hgap⟩ q hqp)
    (fun q hqP hqp =>
      primeGe5BranchAGN_factorization_ne_p_math hpack hp_dvd_gap hqP hqp)

/--
`q ≠ p` で `q ∣ t` なら、Branch A normal form では `q ∤ s`。

これは `q ∣ gap` と `q ∣ GN` の no-shared 版に戻しただけであり、
NeP spine がまず与える局所 separation を表す。
-/
theorem primeGe5BranchANormalForm_neP_dvd_t_not_dvd_s
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hqP : Nat.Prime q)
    (hqp : q ≠ p)
    (hq_t : q ∣ t) :
    ¬ q ∣ s := by
  have hq_gap : q ∣ (z - y) := by
    rw [hgap]
    exact dvd_mul_of_dvd_right (dvd_pow hq_t hpack.hp.ne_zero) (p ^ (p - 1))
  have hq_not_dvd_GN : ¬ q ∣ GN p (z - y) y := by
    simpa using primeGe5BranchANoSharedPrimeOnGN_math
      hpack hp_dvd_gap hqP hqp hq_gap
  intro hq_s
  have hq_GN : q ∣ GN p (z - y) y := by
    rw [hsGN]
    exact dvd_mul_of_dvd_right (dvd_pow hq_s hpack.hp.ne_zero) p
  exact hq_not_dvd_GN hq_GN

/--
`q ≠ p` で `q ∣ s` なら、Branch A normal form では `q ∤ t`。
-/
theorem primeGe5BranchANormalForm_neP_dvd_s_not_dvd_t
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hqP : Nat.Prime q)
    (hqp : q ≠ p)
    (hq_s : q ∣ s) :
    ¬ q ∣ t := by
  intro hq_t
  exact primeGe5BranchANormalForm_neP_dvd_t_not_dvd_s
    hpack hp_dvd_gap hgap hsGN hqP hqp hq_t hq_s

/--
互いに素な 2 数では、片側を割る素数はもう片側を割れない。
-/
theorem prime_not_dvd_right_of_coprime_of_dvd_left
    {a b q : ℕ}
    (hcop : Nat.Coprime a b)
    (hqP : Nat.Prime q)
    (hq_a : q ∣ a) :
    ¬ q ∣ b := by
  intro hq_b
  have hq_gcd : q ∣ Nat.gcd a b := Nat.dvd_gcd hq_a hq_b
  have hq_one : q ∣ 1 := by
    simpa [(Nat.coprime_iff_gcd_eq_one).1 hcop] using hq_gcd
  exact hqP.not_dvd_one hq_one

/--
support separation の `t -> s` 向きは、実は `Nat.Coprime t s` だけで従う。
-/
theorem primeGe5BranchANormalForm_neP_dvd_t_not_dvd_s_of_coprime
    {p x y z t s q : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hp_cop_ts : Nat.Coprime t s)
    (hqP : Nat.Prime q)
    (_hqp : q ≠ p)
    (hq_t : q ∣ t) :
    ¬ q ∣ s := by
  exact prime_not_dvd_right_of_coprime_of_dvd_left hp_cop_ts hqP hq_t

/--
support separation の `s -> t` 向きも、`Nat.Coprime t s` だけで従う。
-/
theorem primeGe5BranchANormalForm_neP_dvd_s_not_dvd_t_of_coprime
    {p x y z t s q : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hp_cop_ts : Nat.Coprime t s)
    (hqP : Nat.Prime q)
    (_hqp : q ≠ p)
    (hq_s : q ∣ s) :
    ¬ q ∣ t := by
  exact prime_not_dvd_right_of_coprime_of_dvd_left hp_cop_ts.symm hqP hq_s

/--
右側が `p` で割れない状況では、
`q ≠ p` の support separation と `Nat.Coprime t s` は同値になる。

Branch A で確定した局所 separation は、
結局この一般事実の specialized 版に過ぎない。

付録:
- 今回の Branch A 実装で得られた
  「`NeP` comparison route は新 obstruction を生まない」
  という評価を、再利用可能な一般辞書へ落とした定理である。
- support-level の比較が coprime 情報へ collapse することを明示するので、
  今後は FLT では route の打ち切り判断に、
  ABC では support/rad 観測の変換辞書に使える。

Refactor TODO:
- 将来 `support separation <-> coprime` の辞書を
  Branch A ファイルから独立 utility へ昇格させるか検討する。
-/
theorem coprime_iff_ne_p_support_separation_of_not_dvd_right
    {p t s : ℕ}
    (hp_not_dvd_s : ¬ p ∣ s) :
    Nat.Coprime t s ↔
      (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ t → ¬ q ∣ s) ∧
      (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ s → ¬ q ∣ t) := by
  constructor
  · intro hcop
    constructor
    · intro q hqP hqp hq_t
      exact prime_not_dvd_right_of_coprime_of_dvd_left hcop hqP hq_t
    · intro q hqP hqp hq_s
      exact prime_not_dvd_right_of_coprime_of_dvd_left hcop.symm hqP hq_s
  · rintro ⟨hsep_ts, hsep_st⟩
    refine (Nat.coprime_iff_gcd_eq_one).2 ?_
    by_contra hg_ne_one
    rcases Nat.exists_prime_and_dvd hg_ne_one with ⟨q, hqP, hq_gcd⟩
    have hq_t : q ∣ t := dvd_trans hq_gcd (Nat.gcd_dvd_left t s)
    have hq_s : q ∣ s := dvd_trans hq_gcd (Nat.gcd_dvd_right t s)
    by_cases hqp : q = p
    · exact hp_not_dvd_s (hqp ▸ hq_s)
    · exact (hsep_ts q hqP hqp hq_t) hq_s

/--
Branch A normal form では、
`q ≠ p` support separation と `Nat.Coprime t s` は同値である。

付録:
- これは generic iff の thin specialization であり、
  `primeGe5BranchANormalForm_prime_not_dvd_s_default` を使って
  Branch A の内部変数 `(t,s)` に刺さる形へ下ろしている。
- この定理により、`NeP` route の support separation は
  Branch A 文脈では genuinely new な obstruction でないと読める。

Refactor TODO:
- `PrimeGe5BranchANormalFormNePSupportKernelTarget` が不要になった後も、
  この specialization 自体は API として維持する。
-/
theorem primeGe5BranchANormalForm_neP_support_separation_iff_coprime
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsGN : GN p (z - y) y = p * s ^ p) :
    Nat.Coprime t s ↔
      (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ t → ¬ q ∣ s) ∧
      (∀ q : ℕ, Nat.Prime q → q ≠ p → q ∣ s → ¬ q ∣ t) := by
  exact coprime_iff_ne_p_support_separation_of_not_dvd_right
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)

/--
support-separation kernel が実は `Nat.Coprime t s` の焼き直しに過ぎないなら、
最終核は coprime-only checkpoint へさらに reduce できる。

付録:
- 現在の `NeP` route が comparison/factorization の大半を使わず、
  実質的には `Nat.Coprime t s` しか残していないことを型の上で固定する橋である。

Refactor TODO:
- Branch A の最終 refuter を別 route へ切り替えたら、
  この bridge は `deprecated` 相当の位置づけに下げるか、
  comparison-route-postmortem 用 helper として残す。
-/
theorem primeGe5BranchANormalFormNePSupportKernel_of_coprimeKernel
    (hKernel : PrimeGe5BranchANormalFormNePCoprimeKernelTarget) :
    PrimeGe5BranchANormalFormNePSupportKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hp_cop_ts hsep_ts hsep_st
  let _ := hsep_ts
  let _ := hsep_st
  exact hKernel hpack hp_dvd_gap hgap hsGN hp_cop_ts

/--
support-separation kernel があれば、`q ≠ p` 側 spine target は
薄い橋で閉じられる。
-/
theorem primeGe5BranchANormalFormPowFactorizationNePSpine_of_supportKernel
    (hKernel : PrimeGe5BranchANormalFormNePSupportKernelTarget) :
    PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hx_tps hgcd_eq hp_cop_ts hp_cop_ty hp_cop_sy hp_not_dvd_s hp_cop_ps hp_not_dvd_y hp_cop_GNy hp_cop_pspow_y hp_cop_spow_y hp_cop_pspow hp_cop_ps_y hp_cop_tps_y hxpow_tps hfac_xpow_ne hgapGN_tps hfac_gapGN_ne hEq hgapFac_ne hGNFac_ne
  let _ := x
  let _ := y
  let _ := z
  let _ := hsx
  let _ := hx_tps
  let _ := hgcd_eq
  let _ := hp_cop_ty
  let _ := hp_cop_sy
  let _ := hp_not_dvd_s
  let _ := hp_cop_ps
  let _ := hp_not_dvd_y
  let _ := hp_cop_GNy
  let _ := hp_cop_pspow_y
  let _ := hp_cop_spow_y
  let _ := hp_cop_pspow
  let _ := hp_cop_ps_y
  let _ := hp_cop_tps_y
  let _ := hxpow_tps
  let _ := hfac_xpow_ne
  let _ := hgapGN_tps
  let _ := hfac_gapGN_ne
  let _ := hEq
  let _ := hgapFac_ne
  let _ := hGNFac_ne
  exact hKernel hpack hp_dvd_gap hgap hsGN hp_cop_ts
    (fun q hqP hqp hq_t =>
      primeGe5BranchANormalForm_neP_dvd_t_not_dvd_s
        hpack hp_dvd_gap hgap hsGN hqP hqp hq_t)
    (fun q hqP hqp hq_s =>
      primeGe5BranchANormalForm_neP_dvd_s_not_dvd_t
        hpack hp_dvd_gap hgap hsGN hqP hqp hq_s)

/--
`q ≠ p` comparison の最終核。

現状ここまで削ると、残っている数学は support separation だけである。

付録:
- 実装上はまだ `sorry` を含むが、意味論的には
  「`NeP` comparison route の active 情報が coprime まで縮んだ後の final checkpoint」
  を表す。
- したがってこの定理は、未完の穴というより
  route 終了判定のための設計マーカーとして読むのが正しい。

Refactor TODO:
- minimality / descent / 別 arithmetic kernel の出口が固まったら、
  この declaration はその新 route への adapter に置き換える。
- もし comparison route を正式終了するなら、
  名前も `...Checkpoint` 系へ寄せることを検討する。
-/
theorem primeGe5BranchANormalFormNePCoprimeKernel_default :
    PrimeGe5BranchANormalFormNePCoprimeKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hp_cop_ts
  let _ := p
  let _ := x
  let _ := y
  let _ := z
  let _ := t
  let _ := s
  let _ := hpack
  let _ := hp_dvd_gap
  let _ := hgap
  let _ := hsGN
  let _ := hp_cop_ts
  /-
  TODO:
  1. `q ≠ p` support separation は既に `Nat.Coprime t s` から出るので、
     comparison-based refuter の active 情報はここで尽きている。
  2. したがって Branch A の最終矛盾は、
     `Nat.Coprime t s` 単独ではなく
     minimality / descent / 別 arithmetic kernel
     へ設計転換して取りに行く必要がある。
  -/
  sorry

/--
`q ≠ p` comparison の最終核。

現状ここまで削ると、残っている数学は support separation だけである。
-/
theorem primeGe5BranchANormalFormNePSupportKernel_default :
    PrimeGe5BranchANormalFormNePSupportKernelTarget := by
  exact primeGe5BranchANormalFormNePSupportKernel_of_coprimeKernel
    primeGe5BranchANormalFormNePCoprimeKernel_default

/--
`q ≠ p` 側の spine kernel 実装入口。
-/
theorem primeGe5BranchANormalFormPowFactorizationNePSpine_default :
    PrimeGe5BranchANormalFormPowFactorizationNePSpineTarget := by
  exact primeGe5BranchANormalFormPowFactorizationNePSpine_of_supportKernel
    primeGe5BranchANormalFormNePSupportKernel_default

/--
factorization-part の `q ≠ p` 側実装入口。

ここでは `q ≠ p` の指数比較だけを isolated に受ける。
-/
theorem primeGe5BranchANormalFormPowFactorizationNeP_default :
    PrimeGe5BranchANormalFormPowFactorizationNePTarget := by
  exact primeGe5BranchANormalFormPowFactorizationNeP_of_spineKernel
    primeGe5BranchANormalFormPowFactorizationNePSpine_default

/--
comparison kernel の factorization-part 実装入口。

ここでは prime ごとの指数比較だけを残し、
comparison の本当の算術 obstruction を 1 点へ集約する。
-/
theorem primeGe5BranchANormalFormPowFactorizationPart_default :
    PrimeGe5BranchANormalFormPowFactorizationPartTarget := by
  exact primeGe5BranchANormalFormPowFactorizationPart_of_neP
    primeGe5BranchANormalFormPowFactorizationNeP_default

/--
X-pow exact kernel の実装入口。

ここでは `x^p = (t * (p * s))^p` と factorization exactness まで explicit に受け、
最後の `x^p` 側衝突だけを残す。
-/
theorem primeGe5BranchANormalFormPowComparisonKernel_default :
    PrimeGe5BranchANormalFormPowComparisonKernelTarget := by
  exact primeGe5BranchANormalFormPowComparisonKernel_of_parts
    primeGe5BranchANormalFormPowEqualityPart_default
    primeGe5BranchANormalFormPowFactorizationPart_default

/--
X-pow exact kernel の実装入口。

ここでは `x^p` 側 exactness に加え、`gap * GN` 側 exactness も explicit に受け、
最後の比較核だけを残す。
-/
theorem primeGe5BranchANormalFormXPowExactKernel_default :
    PrimeGe5BranchANormalFormXPowExactKernelTarget := by
  exact primeGe5BranchANormalFormXPowExactKernel_of_powComparisonKernel
    primeGe5BranchANormalFormPowComparisonKernel_default

/--
x-factor kernel の実装入口。

ここでは `x = t * (p * s)` と `Nat.Coprime (t * (p * s)) y`
まで explicit に受け、最後の `x` 側 exactness との衝突だけを残す。
-/
theorem primeGe5BranchANormalFormXFactorKernel_default :
    PrimeGe5BranchANormalFormXFactorKernelTarget := by
  exact primeGe5BranchANormalFormXFactorKernel_of_xpowExactKernel
    primeGe5BranchANormalFormXPowExactKernel_default

/--
GN linear-factor kernel の実装入口。

ここでは `Nat.Coprime p (s ^ p)` と `Nat.Coprime (p * s) y`
まで explicit に受け、最後の線形/冪因子の局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNLinearFactorKernel_default :
    PrimeGe5BranchANormalFormGNLinearFactorKernelTarget := by
  exact primeGe5BranchANormalFormGNLinearFactorKernel_of_xFactorKernel
    primeGe5BranchANormalFormXFactorKernel_default

/--
GN factor kernel の実装入口。

ここでは `p * s^p ⟂ y` と `s^p ⟂ y` まで explicit に受け、
最後の factor-level 局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNFactorKernel_default :
    PrimeGe5BranchANormalFormGNFactorKernelTarget := by
  exact primeGe5BranchANormalFormGNFactorKernel_of_linearFactorKernel
    primeGe5BranchANormalFormGNLinearFactorKernel_default

/--
GN-side local kernel の実装入口。

ここでは `GN ⟂ y` まで explicit に受け取り、
最後の `GN` 側局所衝突だけを残す。
-/
theorem primeGe5BranchANormalFormGNRightKernel_default :
    PrimeGe5BranchANormalFormGNRightKernelTarget := by
  exact primeGe5BranchANormalFormGNRightKernel_of_factorKernel
    primeGe5BranchANormalFormGNFactorKernel_default

/--
local coprime kernel の実装入口。

ここでは `p ⟂ s` と `p ∤ y` まで explicit に並べた上で、
最後の局所 gcd / valuation 衝突だけを扱う。
-/
theorem primeGe5BranchANormalFormLocalCoprimeKernel_default :
    PrimeGe5BranchANormalFormLocalCoprimeKernelTarget := by
  exact primeGe5BranchANormalFormLocalCoprimeKernel_of_GNRightKernel
    primeGe5BranchANormalFormGNRightKernel_default

/--
Branch A arithmetic kernel の実装入口。

未完核を normal form そのものから切り離し、
抽出済みの算術拘束だけへ局所化する。
-/
theorem primeGe5BranchANormalFormArithmeticKernel_default :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  exact primeGe5BranchANormalFormArithmeticKernel_of_localCoprimeKernel
    primeGe5BranchANormalFormLocalCoprimeKernel_default

/--
Branch A の normal-form refuter 実装入口。

ここが clean な局所 gcd / valuation 衝突数学へ置換される最終穴。
-/
theorem primeGe5BranchANormalFormRefuter_default :
    PrimeGe5BranchANormalFormRefuterTarget := by
  exact primeGe5BranchANormalFormRefuter_of_arithmetic_kernel
    primeGe5BranchANormalFormArithmeticKernel_default

/--
Branch A の shape-witness kernel 実装入口。

ここが clean descent / shrink 数学へ最終的に置換される本当の残穴。
-/
theorem primeGe5BranchAShapeWitnessKernel_default :
    PrimeGe5BranchAShapeWitnessKernelTarget := by
  exact primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter
    primeGe5BranchANormalFormRefuter_default

/-- Branch A の shape-value refuter 実装入口。 -/
theorem primeGe5BranchAShapeValueToRefuter_default :
    PrimeGe5BranchAShapeValueToRefuterTarget :=
  primeGe5BranchAShapeValueToRefuter_of_witness_kernel
    primeGe5BranchAShapeWitnessKernel_default

/--
shape-factorization と shape-value refuter 契約が揃えば、
Branch A 専用 refuter が得られる。
-/
theorem primeGe5BranchARefuter_of_shape_pipeline
    (hShape : PrimeGe5BranchAShapeFactorizationTarget)
    (hRefuteValue : PrimeGe5BranchAShapeValueToRefuterTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  exact hRefuteValue hpack hp_dvd_gap
    (primeGe5BranchAShapeValue_of_factorization hShape hpack hp_dvd_gap)

/--
Wieferich-style witness target とその最終 refuter が揃えば、
Branch A 専用 refuter は comparison route を経由せずに閉じられる。
-/
theorem primeGe5BranchARefuter_of_wieferich
    (hWieferich : PrimeGe5BranchAWieferichOnYTarget)
    (hRefute : PrimeGe5BranchAWieferichRefuterTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  exact hRefute hpack hp_dvd_gap (hWieferich hpack hp_dvd_gap)

/--
local kernel が与えられれば、Wieferich witness refuter は既存 normal form 抽出だけで得られる。

付録:
- `PrimeGe5BranchAWieferichRefuterTarget` を直接 clean 化できなくても、
  欠けた数学をこの local kernel 1 本へ局所化できる。
-/
theorem primeGe5BranchAWieferichRefuter_of_localKernel
    (hK : PrimeGe5BranchAWieferichLocalKernelTarget) :
    PrimeGe5BranchAWieferichRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  rcases primeGe5BranchAShapeValue_of_factorization
      primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with ⟨t, hgap⟩
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap hgap with ⟨s, hsGN, hsx⟩
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN)
    (primeGe5BranchANormalForm_coprime_t_right hpack hsx)
    (primeGe5BranchANormalForm_coprime_s_right hpack hsx)
    (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)
    hWieferich

/--
arithmetic kernel が与えられれば、Wieferich local kernel は自動で閉じる。

付録:
- local kernel に入る witness は normal form から再生成できるので、
  arithmetic kernel より本質的に強い入力は要求していない。
-/
theorem primeGe5BranchAWieferichLocalKernel_of_arithmeticKernel
    (hK : PrimeGe5BranchANormalFormArithmeticKernelTarget) :
    PrimeGe5BranchAWieferichLocalKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hWieferich
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default hpack hp_dvd_gap hgap hsGN)
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s

/--
Wieferich local kernel が与えられれば、arithmetic kernel も閉じる。

付録:
- local kernel で要求する Wieferich witness 自体は、
  `primeGe5BranchANormalForm_y_wieferich_mod_p_sq`
  により normal form から既に得られる。
- したがって両者の差は、現段階では数学核というより
  witness を引数に出すかどうかの API 上の差に近い。
-/
theorem primeGe5BranchANormalFormArithmeticKernel_of_wieferichLocalKernel
    (hK : PrimeGe5BranchAWieferichLocalKernelTarget) :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx _hgcd_eq hcop_ts hcop_ty hcop_sy hp_not_dvd_s
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s
    (primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN)

/-- Branch A 条件付きで、`z` 最小の反例 pack を no-`sorry` で選べる。 -/
theorem minimalPrimeGe5CounterexampleSelectionA_impl :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      ∃ x₀ y₀ z₀ : ℕ, MinimalPrimeGe5CounterexamplePackA p x₀ y₀ z₀ := by
  classical
  intro p x y z hpack hp_dvd_gap
  let P : ℕ → Prop := fun z₀ => ∃ x₀ y₀ : ℕ,
    PrimeGe5CounterexamplePack p x₀ y₀ z₀ ∧ p ∣ (z₀ - y₀)
  have hExists : ∃ z₀ : ℕ, P z₀ := ⟨z, x, y, hpack, hp_dvd_gap⟩
  let z₀ := Nat.find hExists
  have hz₀ : P z₀ := Nat.find_spec hExists
  rcases hz₀ with ⟨x₀, y₀, hpack₀, hpA₀⟩
  refine ⟨x₀, y₀, z₀, hpack₀, hpA₀, ?_⟩
  intro x' y' z' hpack' hpA' hz'lt
  have hz₀_le : z₀ ≤ z' := by
    simpa [z₀] using (Nat.find_min' hExists ⟨x', y', hpack', hpA'⟩)
  exact (not_le_of_gt hz'lt) hz₀_le

/--
smaller-counterexample target があれば、minimality 付き distinguished-prime descent は自動で従う。
-/
theorem primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample
    (hSmall : PrimeGe5BranchASmallerCounterexampleTarget) :
    PrimeGe5BranchADistinguishedPrimeDescentTarget := by
  intro p x y z t s hMin hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s
  exact hSmall hMin.1 hMin.2.1 hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s

/--
smaller-packet target があれば、smaller-counterexample target は機械的に従う。
-/
theorem primeGe5BranchASmallerCounterexample_of_smallerPacket
    (hSmall : PrimeGe5BranchASmallerPacketTarget) :
    PrimeGe5BranchASmallerCounterexampleTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s
  rcases hSmall hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s with
    ⟨pkt', hz'lt⟩
  exact ⟨pkt'.x, pkt'.y, pkt'.z, counterexamplePack_of_branchANormalFormPacket pkt',
    pkt'.hp_dvd_gap, hz'lt⟩

/--
valuation peel と primitive-packet descent の 2 分岐が揃えば、
smaller-packet target は場合分けだけで閉じる。
-/
theorem primeGe5BranchASmallerPacket_of_routes
    (hPeel : PrimeGe5BranchAValuationPeelPacketTarget)
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    PrimeGe5BranchASmallerPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s
  by_cases hpt : p ∣ t
  · exact hPeel hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hpt
  · exact hPrim hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hpt

/--
Wieferich witness 付き primitive local target があれば、
primitive packet descent 契約は自動で従う。

付録:
- `PrimeGe5BranchAPrimitivePacketDescentTarget`
  の truly new 部分を、
  `y^(p-1) ≡ 1 [MOD p^2]`
  を明示引数に取る primitive core 1 本へ局所化する。
- witness 自体は Branch A normal form から既に得られる。
-/
theorem primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket
    (hPrim : PrimeGe5BranchAPrimitiveWieferichPacketTarget) :
    PrimeGe5BranchAPrimitivePacketDescentTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
  exact hPrim hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
    (primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN)

/--
primitive distinguished-prime selection と packet restoration が揃えば、
primitive witness-packet target は橋だけで閉じる。
-/
theorem primeGe5BranchAPrimitiveWieferichPacket_of_distinguishedPrime_and_restore
    (hPrime : PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget)
    (hRestore : PrimeGe5BranchAPrimitivePacketRestoreTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  rcases hPrime hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨q, hqprime, hqGN, hqgap⟩
  exact hRestore hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich hqprime hqGN hqgap

/--
Zsigmondy-lite existence 段があれば、distinguished-prime target は薄い橋で閉じる。

付録:
- 現段階では statement は同型だが、
  役割を
  「existing number-theory existence layer」
  と
  「primitive route internal target」
  で分けるために名前を分離する。
-/
theorem primeGe5BranchAPrimitiveDistinguishedPrime_of_zsigmondy
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget) :
    PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  exact hZ hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich

/--
valuation peel を error-lift 1 本に局所化した smaller-packet bridge。

付録:
- provider/mainline 側から見ると、
  valuation peel 側の残る未完は
  `PrimeGe5BranchAValuationPeelPacketFromErrorTarget`
  だけだと読める。
- したがって primitive route を本命に押し上げつつ、
  peel 側は exact-error からの lift として独立に詰められる。
-/
theorem primeGe5BranchASmallerPacket_of_errorLift_and_primitive
    (hErr : PrimeGe5BranchAValuationPeelTailErrorTarget)
    (hLift : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    PrimeGe5BranchASmallerPacketTarget :=
  primeGe5BranchASmallerPacket_of_routes
    (primeGe5BranchAValuationPeelPacket_of_tailErrorLift hErr hLift)
    hPrim

/--
distinguished-prime descent があれば、最小 Branch A 反例は存在しえない。
-/
theorem primeGe5BranchARefuter_on_minimal_of_distinguishedPrimeDescent
    (hDesc : PrimeGe5BranchADistinguishedPrimeDescentTarget) :
    ∀ {p x y z : ℕ}, MinimalPrimeGe5CounterexamplePackA p x y z → False := by
  intro p x y z hMin
  have hpack : PrimeGe5CounterexamplePack p x y z := hMin.1
  have hp_dvd_gap : p ∣ (z - y) := hMin.2.1
  rcases primeGe5BranchAShapeValue_of_factorization
      primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with ⟨t, hgap⟩
  rcases primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap hgap with ⟨s, hsGN, hsx⟩
  rcases hDesc hMin hgap hsGN hsx
      (primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN)
      (primeGe5BranchANormalForm_coprime_t_right hpack hsx)
      (primeGe5BranchANormalForm_coprime_s_right hpack hsx)
      (primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN) with
    ⟨x', y', z', hpack', hpA', hz'lt⟩
  exact hMin.2.2 hpack' hpA' hz'lt

/--
distinguished-prime descent があれば、任意の Branch A 反例を直接 refute できる。

付録:
- これは Wieferich witness の有無を経由せず、
  Branch A 専用 minimal selection と distinguished-prime descent だけで閉じる。
- 後段で truly new kernel を採るなら、この theorem が
  `PrimeGe5BranchAWieferichRefuterTarget` より自然な出口になる。
-/
theorem primeGe5BranchARefuter_of_distinguishedPrimeDescent
    (hDesc : PrimeGe5BranchADistinguishedPrimeDescentTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  intro p x y z hpack hp_dvd_gap
  rcases minimalPrimeGe5CounterexampleSelectionA_impl hpack hp_dvd_gap with
    ⟨x₀, y₀, z₀, hMin⟩
  exact primeGe5BranchARefuter_on_minimal_of_distinguishedPrimeDescent hDesc hMin

/--
peel 側の exact-error lift と primitive descent が揃えば、
Branch A refuter は smaller-packet route 経由で回収できる。

付録:
- これにより provider/mainline 側からは、
  primitive route を本命にしつつ
  peel 側の残核を error-lift 1 本として差し込めば十分だと読める。
-/
theorem primeGe5BranchARefuter_of_errorLift_and_primitive
    (hErr : PrimeGe5BranchAValuationPeelTailErrorTarget)
    (hLift : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False :=
  primeGe5BranchARefuter_of_distinguishedPrimeDescent
    (primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample
      (primeGe5BranchASmallerCounterexample_of_smallerPacket
        (primeGe5BranchASmallerPacket_of_errorLift_and_primitive hErr hLift hPrim)))

/--
primitive packet descent を本命 route として読む canonical wrapper。

付録:
- peel 側は
  `tail error -> packet`
  の補助 lift としてだけ受け取り、
  truly new descent の本体は
  `PrimeGe5BranchAPrimitivePacketDescentTarget`
  に置く、という現在の設計判断を名前に反映している。
-/
theorem primeGe5BranchARefuter_of_primitiveMainline
    (hErr : PrimeGe5BranchAValuationPeelTailErrorTarget)
    (hLift : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False :=
  primeGe5BranchARefuter_of_errorLift_and_primitive hErr hLift hPrim

/--
`FLT_of_coprime` の residual branch から呼ぶ Branch A 専用 refuter 入口。

将来は `PrimeGe5BranchAGapPowFactorizationTarget` と shape/descent kernel を
ここで合成する。現段階では残差 `sorry` を `Basic.lean` から切り離して
この lower layer に局所化する。
-/
theorem primeGe5BranchARefuter_default :
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      p ∣ (z - y) →
      False := by
  exact primeGe5BranchARefuter_of_shape_pipeline
    primeGe5BranchAShapeFactorization_default
    primeGe5BranchAShapeValueToRefuter_default

end DkMath.FLT
