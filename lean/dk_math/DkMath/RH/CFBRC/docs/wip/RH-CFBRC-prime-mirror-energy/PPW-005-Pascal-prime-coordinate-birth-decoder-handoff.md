# Pascal prime-coordinate birth decoder 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-004-Eta-normalized-gap-asymptotic-dichotomy-handoff.md
```

PPW-004 は Green となり、次の module が追加された。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy
```

この checkpoint では、eta 一項ごとの横 offset Gap の漸近監査を完了し、次の算術層へ進む。

## 2. PPW-004 レビュー結果

### 2.1 normalized Gap の完全二分

実装により、eta index `m` の normalized Gap は次の形へ展開された。

$$
U_m(s)
=
(m+1)^{2\delta(s)}
+
(m+1)^{-2\delta(s)}
-2
$$

ここで、

$$
\delta(s):=s.re-\frac12
$$

である。

次が Green である。

```lean
etaEndpointIncrementMirrorGap_tendsto_zero_of_re_eq_half
etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_pos
etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_neg
etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half
etaEndpointIncrementMirrorGap_tendsto_zero_iff_re_eq_half
```

したがって、

```text
critical line:
  normalized Gap は恒等的に 0

off-critical:
  normalized Gap は +∞ へ発散
```

という完全な二分が得られた。

### 2.2 raw Gap と normalized Gap の obstruction

open strip では、零点条件なしに raw amplitude Gap が零へ収束する。

一方、off-critical では同じ raw Gap を `m + 1` 倍した normalized Gap が正の無限大へ発散する。

```lean
etaMirrorAmplitudeGap_raw_zero_normalized_atTop
```

により、この二重挙動が同じ `s` に対して固定された。

したがって、単一 eta 項の decay をさらに精密化するだけでは zero-locus Beam は得られない。今後は複数の素数座標、有限 cutoff、隣接履歴を持つ算術側へ進む。

### 2.3 妥当性

PPW-004 は `RiemannHypothesis`、`NontrivialRiemannZetaZero`、RH-equivalent provider を使用していない。

今回得たものは点ごとの横 offset selector であり、標準ゼータ零点が臨界線上にあることはまだ導いていない。

## 3. 次の目的

次に、Pascal の二項係数が持つ prime dial を、有限 prime-coordinate の出生履歴として読み出す。

既存 module は次である。

```text
DkMath.NumberTheory.PascalPrimeDial
DkMath.NumberTheory.AKSBridge
```

既存 theorem として、少なくとも次が利用できる。

```lean
prime_uniformPrimeDialHeight_self
below_prime_uniformPrimeDialHeight_zero
pascalPrimeDialHeight_eq_zero_of_row_lt
prime_not_dvd_pascalCoeffMass_of_row_lt
pascalPrimeDialHeight_prime_pow_add_index
pascalPrimeDialHeight_prime_pow
prime_power_unitFilteredPrimeDialHeight
```

最初の算術 checkpoint では、prime power multiplicity や標準 von Mangoldt 関数まで一度に進めない。

まず、各素数 `p` の dial が、Pascal row `p` で確実に可視化され、それ以前の row では可視化されないことを有限 support として形式化する。

## 4. 重要な監査境界

この実装では prime coordinate の index に `Nat.Prime p` を使用する。

したがって、この checkpoint 単独を「素数判定器」または「素数生成式の完成」と呼ばない。

ここで証明するのは次である。

> prime-indexed dial の全座標が Pascal の行履歴により初めて現れる位置は、その素数自身の行である。

外部の `Nat.Prime` predicate を使わず、Pascal row の合同条件だけから primality を特徴付ける AKS converse は別 checkpoint とする。

この区別を文書と module comment に明記する。

## 5. 新規 module

次を追加する。

```text
DkMath.NumberTheory.PascalPrimeCoordinateDecoder
```

推奨 import は次である。

```lean
import DkMath.NumberTheory.PascalPrimeDial
import Mathlib.Tactic
```

namespace は既存 Pascal module と合わせる。

```lean
namespace DkMath
namespace NumberTheory
```

## 6. 行内の dial 可視性

### 6.1 可視性 predicate

prime predicate 自体は含めず、指定された dial base `p` が row `n` の内側係数で正の高さを持つことを定義する。

```lean
def PascalPrimeDialVisibleInRow (p n : ℕ) : Prop :=
  ∃ k : ℕ,
    0 < k ∧ k < n ∧
      0 < pascalPrimeDialHeight p n k
```

名前は既存命名規則に合わせて小文字開始へ調整してよい。

### 6.2 自身の prime row で可視

```lean
theorem prime_pascalPrimeDialVisibleInRow_self
    {p : ℕ} (hp : p.Prime) :
    PascalPrimeDialVisibleInRow p p
```

`k = 1` を witness とし、次を使う。

```lean
prime_uniformPrimeDialHeight_self hp
```

素数は `1 < p` であるため、`0 < 1` と `1 < p` が得られる。

### 6.3 自身より前では不可視

```lean
theorem prime_not_pascalPrimeDialVisibleInRow_of_row_lt
    {p n : ℕ} (hp : p.Prime) (hnp : n < p) :
    ¬ PascalPrimeDialVisibleInRow p n
```

可視性 witness `k` を取り出し、

```lean
pascalPrimeDialHeight_eq_zero_of_row_lt hp hnp
```

と正高さを衝突させる。

## 7. 一行の prime-coordinate support

### 7.1 定義

一行で可視な prime-indexed dial だけを有限集合として保持する。

```lean
def pascalRowPrimeCoordinateSupport (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p =>
    Nat.Prime p ∧ PascalPrimeDialVisibleInRow p n
```

`p ≤ n` の範囲に制限するため、有限性は定義から得られる。

### 7.2 membership

```lean
@[simp]
theorem mem_pascalRowPrimeCoordinateSupport_iff
    {p n : ℕ} :
    p ∈ pascalRowPrimeCoordinateSupport n ↔
      p ≤ n ∧ Nat.Prime p ∧
        PascalPrimeDialVisibleInRow p n
```

`Finset.mem_range` の正規形に合わせて、`p < n + 1` のまま保持してもよい。

### 7.3 prime row 自身の座標

```lean
theorem prime_mem_pascalRowPrimeCoordinateSupport_self
    {p : ℕ} (hp : p.Prime) :
    p ∈ pascalRowPrimeCoordinateSupport p
```

### 7.4 前の row には存在しない

```lean
theorem prime_not_mem_pascalRowPrimeCoordinateSupport_of_row_lt
    {p n : ℕ} (hp : p.Prime) (hnp : n < p) :
    p ∉ pascalRowPrimeCoordinateSupport n
```

## 8. 累積 prime-coordinate support

単一 row では prime dial が一度消えて再出現する場合がある。そのため「出生」は直前 row との差ではなく、過去全行の累積 support から定義する。

### 8.1 定義

実装しやすい方を選んでよい。

候補 A は `Finset.biUnion` である。

```lean
def pascalPrimeCoordinateSupportUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).biUnion pascalRowPrimeCoordinateSupport
```

候補 B は直接 filter する。

```lean
def pascalPrimeCoordinateSupportUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p =>
    Nat.Prime p ∧
      ∃ d ≤ n, PascalPrimeDialVisibleInRow p d
```

Lean API が簡単な方を採用する。

### 8.2 完全な membership characterization

中心 theorem は次である。

```lean
theorem mem_pascalPrimeCoordinateSupportUpTo_iff
    {p n : ℕ} :
    p ∈ pascalPrimeCoordinateSupportUpTo n ↔
      Nat.Prime p ∧ p ≤ n
```

順方向では、support に入った行 `d ≤ n` と有限範囲から `p ≤ d ≤ n` を得る。

逆方向では、prime `p` 自身の row を witness とする。

```lean
prime_mem_pascalRowPrimeCoordinateSupport_self
```

を再利用する。

この theorem は、prime-indexed Pascal dial の累積座標が `n` 以下の全素数を漏れなく保持することを示す。

## 9. prime-coordinate birth support

### 9.1 定義

```lean
def pascalPrimeCoordinateBirthSupport (n : ℕ) : Finset ℕ :=
  pascalPrimeCoordinateSupportUpTo n \
    pascalPrimeCoordinateSupportUpTo (n - 1)
```

### 9.2 membership characterization

```lean
theorem mem_pascalPrimeCoordinateBirthSupport_iff
    {p n : ℕ} :
    p ∈ pascalPrimeCoordinateBirthSupport n ↔
      Nat.Prime p ∧ p = n
```

等式の向きは `p = n` または `n = p` のどちらでもよい。

証明では二つの cumulative membership theorem を使い、自然数順序部分は `omega` で処理してよい。

### 9.3 singleton / empty dichotomy

```lean
theorem pascalPrimeCoordinateBirthSupport_eq
    (n : ℕ) :
    pascalPrimeCoordinateBirthSupport n =
      if Nat.Prime n then {n} else ∅
```

これが Pascal 行履歴から得られる prime-coordinate 出生イベントの有限集合形である。

## 10. prime birth indicator と log weight

### 10.1 indicator

```lean
def pascalPrimeBirthIndicator (n p : ℕ) : ℕ :=
  if p ∈ pascalPrimeCoordinateBirthSupport n then 1 else 0
```

```lean
@[simp]
theorem pascalPrimeBirthIndicator_self
    {p : ℕ} (hp : p.Prime) :
    pascalPrimeBirthIndicator p p = 1
```

### 10.2 log weight

```lean
noncomputable def pascalPrimeBirthLogWeight
    (n p : ℕ) : ℝ :=
  if p ∈ pascalPrimeCoordinateBirthSupport n then
    Real.log (p : ℝ)
  else
    0
```

次を証明する。

```lean
theorem pascalPrimeBirthLogWeight_nonneg
    (n p : ℕ) :
    0 ≤ pascalPrimeBirthLogWeight n p
```

membership branch では `Nat.Prime p` を birth membership theorem から回収し、`Real.log` の非負性を示す。

```lean
@[simp]
theorem pascalPrimeBirthLogWeight_self
    {p : ℕ} (hp : p.Prime) :
    pascalPrimeBirthLogWeight p p = Real.log (p : ℝ)
```

### 10.3 一行の birth log mass

```lean
noncomputable def pascalPrimeBirthLogMass (n : ℕ) : ℝ :=
  ∑ p ∈ pascalPrimeCoordinateBirthSupport n,
    Real.log (p : ℝ)
```

```lean
theorem pascalPrimeBirthLogMass_eq
    (n : ℕ) :
    pascalPrimeBirthLogMass n =
      if Nat.Prime n then Real.log (n : ℝ) else 0
```

これは prime-only の Chebyshev-theta 型 increment である。

prime power を含む von Mangoldt weight ではないため、そのように記述しない。

## 11. `(N, N + 1)` 累積更新

可能なら次も置く。

```lean
theorem pascalPrimeCoordinateSupportUpTo_succ
    (N : ℕ) :
    pascalPrimeCoordinateSupportUpTo (N + 1) =
      if Nat.Prime (N + 1) then
        insert (N + 1) (pascalPrimeCoordinateSupportUpTo N)
      else
        pascalPrimeCoordinateSupportUpTo N
```

または birth support を用いた一般形でもよい。

```lean
theorem pascalPrimeCoordinateSupportUpTo_eq_prev_union_birth
    (n : ℕ) :
    pascalPrimeCoordinateSupportUpTo n =
      pascalPrimeCoordinateSupportUpTo (n - 1) ∪
        pascalPrimeCoordinateBirthSupport n
```

この theorem が Pascal 側の `(N, N + 1)` coordinate decoder になる。

## 12. Build checkpoint

```bash
lake env lean DkMath/NumberTheory/PascalPrimeCoordinateDecoder.lean
```

単体 Green 後、適切な root へ import を追加する。

候補は次である。

```text
DkMath.NumberTheory
DkMath.RH.CFBRC.PrimeMirrorEnergy
DkMath.RH
```

ただし `PrimeMirrorEnergy` から直接 import すると NumberTheory → RH の依存方向を逆転させる可能性がある。まず NumberTheory root へ export し、RH 側の次 checkpoint で import する方を優先する。

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 13. 妥当性境界

この checkpoint は次を主張しない。

1. Pascal row condition だけから `Nat.Prime n` を判定できたこと
2. composite row の完全な dial support 分類
3. prime power multiplicity の出生履歴
4. standard von Mangoldt function との一致
5. Euler-zeta または PHZ との一致
6. 非自明零点 pattern の形成
7. RH または既存 research goal の閉鎖

今回の成果は、prime-indexed dial の有限座標が Pascal 行履歴のどこで初めて現れるかを exact に復元することである。

## 14. 次 checkpoint への接続

PPW-005 Green 後は、次の二方向を比較する。

```text
Prime-only Euler route:
  pascalPrimeCoordinateBirthSupport
    → log p birth weight
    → finite Euler prime mode
    → prime mirror finite energy

Prime-power / Mangoldt route:
  pascalPrimeDialHeight_prime_pow
    → prime-power label
    → existing VonMangoldtShadow
    → log p weight with multiplicity events
```

最初は prime-only Euler route を優先する。これは既存 `DkMath.RH.EulerZeta` の prime-indexed finite productへ直接接続しやすい。

prime-power route は、PHZ と `-ζ'/ζ` の形成則へ進む段階で追加する。

## 15. 完了報告に含めるもの

1. 追加・変更した file
2. Green になった theorem 一覧
3. row visibility predicate の定義
4. cumulative support membership theorem
5. birth support の singleton / empty dichotomy
6. log birth mass が prime-only weightであること
7. 実行した build command と結果
8. warning または linter 指摘
