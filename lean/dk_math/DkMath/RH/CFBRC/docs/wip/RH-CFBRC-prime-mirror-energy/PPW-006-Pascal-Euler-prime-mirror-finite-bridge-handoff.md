# Pascal–Euler–prime-mirror finite bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-005-Pascal-prime-coordinate-birth-decoder-handoff.md
```

PPW-005 は Green となり、次の一般数論 module が追加された。

```text
DkMath.NumberTheory.PascalPrimeCoordinateDecoder
```

公開入口は `DkMath.lean` に追加済みである。

## 2. PPW-005 レビュー結果

### 2.1 累積 support の特徴付けは exact

実装された中心 theorem は次である。

```lean
theorem mem_pascalPrimeCoordinateSupportUpTo_iff
    {p n : ℕ} :
    p ∈ pascalPrimeCoordinateSupportUpTo n ↔
      Nat.Prime p ∧ p ≤ n
```

したがって累積 support は、有限集合として exact に

$$
\{p\mid p\text{ is prime and }p\le n\}
$$

を表す。

### 2.2 birth support の singleton / empty 二分は妥当

```lean
theorem pascalPrimeCoordinateBirthSupport_eq (n : ℕ) :
    pascalPrimeCoordinateBirthSupport n =
      if Nat.Prime n then {n} else ∅
```

これにより、累積履歴の隣接差分は prime row で一つの新座標を追加し、非 prime row では何も追加しない。

### 2.3 log birth mass は prime-only Chebyshev 増分

```lean
theorem pascalPrimeBirthLogMass_eq (n : ℕ) :
    pascalPrimeBirthLogMass n =
      if Nat.Prime n then Real.log (n : ℝ) else 0
```

これは prime-only の `log p` 増分であり、prime-power multiplicity を含む von Mangoldt 関数ではない。

### 2.4 循環と過大主張はない

本 module は `Nat.Prime` を index predicate として使用する。Pascal 係数のみから独立な素数判定器を構成したとは主張しない。

また eta、Euler-zeta、非自明零点、CFBRC、RH を import していないため、算術 decoder として独立している。

## 3. 次の目的

同じ Pascal birth support を、二つの有限対象へ同時に供給する。

```text
Pascal cumulative prime support
  ├─ finite Euler product
  └─ finite prime-mirror log energy
```

ここで重要なのは、Euler product と正規化 energy が等しいと主張することではない。

両者が同じ prime birth event と同じ `log p` 座標を共有し、`(N,N+1)` 更新則を持つことを exact に固定する。

## 4. 新規 module

次を追加する。

```text
DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
```

推奨 import は次である。

```lean
import DkMath.NumberTheory.PascalPrimeCoordinateDecoder
import DkMath.RH.EulerZeta
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
import Mathlib.Tactic
```

namespace は既存 CFBRC 系と合わせる。

```lean
namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.RH.EulerZeta
```

## 5. Pascal support を有限 Euler product に供給する

### 5.1 Nat-indexed finite Euler product

まず既存 Pascal support 上の有限積を定義する。

```lean
noncomputable def pascalPrimeEulerProductUpTo
    (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p in pascalPrimeCoordinateSupportUpTo N,
    eulerZetaFactor p s
```

### 5.2 Birth Euler factor

```lean
noncomputable def pascalPrimeEulerBirthFactor
    (n : ℕ) (s : ℂ) : ℂ :=
  if Nat.Prime n then eulerZetaFactor n s else 1
```

### 5.3 `(N,N+1)` product update

中心 theorem は一式で次とする。

```lean
@[simp] theorem pascalPrimeEulerProductUpTo_succ
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerProductUpTo (N + 1) s =
      pascalPrimeEulerProductUpTo N s *
        pascalPrimeEulerBirthFactor (N + 1) s
```

必要なら先に場合分け theorem を置いてよい。

```lean
theorem pascalPrimeEulerProductUpTo_succ_of_prime
    {N : ℕ} (hprime : Nat.Prime (N + 1)) (s : ℂ) :
    pascalPrimeEulerProductUpTo (N + 1) s =
      pascalPrimeEulerProductUpTo N s *
        eulerZetaFactor (N + 1) s
```

```lean
theorem pascalPrimeEulerProductUpTo_succ_of_not_prime
    {N : ℕ} (hprime : ¬Nat.Prime (N + 1)) (s : ℂ) :
    pascalPrimeEulerProductUpTo (N + 1) s =
      pascalPrimeEulerProductUpTo N s
```

`Finset.prod_insert` を使う場合は、`N + 1` が `pascalPrimeCoordinateSupportUpTo N` に入らないことを membership theorem から証明する。

## 6. 既存 `eulerZetaFinite` との型 bridge

既存 `eulerZetaFinite` は次の subtype support を要求する。

```lean
Finset {p // Nat.Prime p}
```

Pascal support をこの型へ持ち上げる。

```lean
noncomputable def pascalPrimeEulerSubtypeSupportUpTo
    (N : ℕ) : Finset {p // Nat.Prime p}
```

実装方法は、`pascalPrimeCoordinateSupportUpTo N` の `attach` と
`mem_pascalPrimeCoordinateSupportUpTo_iff` を使う `Finset.map` を推奨する。

membership theorem を置く。

```lean
@[simp] theorem mem_pascalPrimeEulerSubtypeSupportUpTo_iff
    {p : {p // Nat.Prime p}} {N : ℕ} :
    p ∈ pascalPrimeEulerSubtypeSupportUpTo N ↔ p.1 ≤ N
```

Nat-indexed product と既存 Euler product の一致を証明する。

```lean
theorem pascalPrimeEulerProductUpTo_eq_eulerZetaFinite
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerProductUpTo N s =
      eulerZetaFinite (pascalPrimeEulerSubtypeSupportUpTo N) s
```

積の並び順は可換積なので問題にならない。必要なら `Finset.prod_bij` または support map 上の `Finset.prod_map` を使用する。

この subtype bridge が elaboration 上重い場合も、statement を弱めず補助 lemma に分割する。

## 7. Pascal prime-mirror log energy

同じ support と prime birth log weight を positive Gap へ供給する。

```lean
noncomputable def pascalPrimeMirrorLogEnergyUpTo
    (N : ℕ) (s : ℂ) : ℝ :=
  ∑ p in pascalPrimeCoordinateSupportUpTo N,
    Real.log (p : ℝ) * primeMirrorOffsetGapAt p s
```

既存 generic energy との一致を置く。

```lean
theorem pascalPrimeMirrorLogEnergyUpTo_eq_primeMirrorEnergyAt
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s =
      primeMirrorEnergyAt
        (pascalPrimeCoordinateSupportUpTo N)
        (fun p => Real.log (p : ℝ)) s
```

定義上の正規形に応じて `rfl`、`simp`、`Finset.sum_congr` を用いる。

## 8. Energy の非負性と臨界線特徴付け

support の各要素は prime なので、次を補助 lemma として用意してよい。

```lean
theorem one_lt_of_mem_pascalPrimeCoordinateSupportUpTo
    {p N : ℕ}
    (hp : p ∈ pascalPrimeCoordinateSupportUpTo N) :
    1 < p
```

```lean
theorem log_pos_of_mem_pascalPrimeCoordinateSupportUpTo
    {p N : ℕ}
    (hp : p ∈ pascalPrimeCoordinateSupportUpTo N) :
    0 < Real.log (p : ℝ)
```

非負性は cutoff 制約なしで置く。

```lean
theorem pascalPrimeMirrorLogEnergyUpTo_nonneg
    (N : ℕ) (s : ℂ) :
    0 ≤ pascalPrimeMirrorLogEnergyUpTo N s
```

`2 ≤ N` なら support に base-two prime が含まれるため、臨界線を特徴付ける。

```lean
theorem pascalPrimeMirrorLogEnergyUpTo_eq_zero_iff_re_eq_half
    {N : ℕ} (hN : 2 ≤ N) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s = 0 ↔
      s.re = (1 : ℝ) / 2
```

```lean
theorem pascalPrimeMirrorLogEnergyUpTo_pos_of_re_ne_half
    {N : ℕ} (hN : 2 ≤ N) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < pascalPrimeMirrorLogEnergyUpTo N s
```

既存 `primeMirrorEnergyAt_eq_zero_iff_re_eq_half` と
`primeMirrorEnergyAt_pos_of_re_ne_half` を再利用してよい。

## 9. `(N,N+1)` energy birth identity

最重要の算術–幾何接続は次の一式である。

```lean
@[simp] theorem pascalPrimeMirrorLogEnergyUpTo_succ_sub
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo (N + 1) s -
        pascalPrimeMirrorLogEnergyUpTo N s =
      pascalPrimeBirthLogMass (N + 1) *
        primeMirrorOffsetGapAt (N + 1) s
```

加法形も置く。

```lean
@[simp] theorem pascalPrimeMirrorLogEnergyUpTo_succ_eq
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo (N + 1) s =
      pascalPrimeMirrorLogEnergyUpTo N s +
        pascalPrimeBirthLogMass (N + 1) *
          primeMirrorOffsetGapAt (N + 1) s
```

prime の場合は新座標 `N + 1` が `log (N + 1)` weight で追加される。

非 prime の場合は birth log mass が零であり、energy は変化しない。

この theorem が、Pascal birth decoder と prime-mirror positive Core を一本に接続する中心となる。

## 10. 同期された二つの birth 更新

実装後、次の二つが同じ `N + 1` prime event で更新される。

```text
finite Euler product:
  multiply by eulerZetaFactor (N + 1) s

prime-mirror log energy:
  add log (N + 1) * primeMirrorOffsetGapAt (N + 1) s
```

これは積と和の同一性ではない。

Euler 側では prime mode が複素乗法因子として追加され、energy 側では同じ prime mode の横 mirror 不均衡が非負座標として追加される。

## 11. Export

単体 Green 後、次へ import を追加する。

```text
DkMath.RH
```

推奨 import は次である。

```lean
import DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
```

`DkMath.lean` は既に一般 decoder を export しているため、この RH 専用 bridge を重ねて追加する必要はない。

## 12. Build checkpoint

```bash
lake env lean DkMath/RH/CFBRC/PascalPrimeEulerEnergyBridge.lean
lake env lean DkMath/RH.lean
lake build DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
lake build DkMath.RH
lake build DkMath

git diff --check
```

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 13. 妥当性境界

この実装では次を主張しない。

1. finite Euler product が有限 cutoff で標準ゼータの非自明零点を持つこと
2. Euler product の値または位相が prime-mirror energy と等しいこと
3. 非自明零点から Pascal prime-mirror energy collapse が得られること
4. prime-power multiplicity または analytic von Mangoldt weight
5. PHZ または `-ζ'/ζ` との同一性
6. RH または既存 research `sorry` の閉鎖

この checkpoint の成果は、Pascal の prime birth 履歴を、有限 Euler 波と有限 positive mirror energy の共通座標源として exact に固定することである。

## 14. この checkpoint 後の進路

PPW-006 Green 後、二つの分岐を監査する。

```text
Phase route:
  pascalPrimeEulerProductUpTo
    → eulerZetaPhaseVelLocal / hopcPrimeLocalContribution
    → Pascal-born finite phase wave

Prime-power route:
  PrimitiveSet.PrimePowerLabel
    → VonMangoldtShadow
    → prime-power log p coordinate
    → PHZ / logarithmic derivative candidate
```

まず Phase route を一段実装し、Pascal-born support 上の有限位相速度和と `(N,N+1)` birth update を固定する。その後、prime-power route と比較する。
