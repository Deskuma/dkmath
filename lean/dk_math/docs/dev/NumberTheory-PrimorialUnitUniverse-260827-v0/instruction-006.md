# PUU-L006 — Primorial Wheel Survivor / Reflection

## 0. 判定

PUU-L005 は Outcome A+ とする。

L005 で有限 prime basis `S` の product

```text
M(S) = finitePrimeBasisProduct S
```

が divisibility-order における最小共通同期周期であり、`ReservedByPrimeBasis S` とその否定が `M(S)` 周期で反復することまで固定された。

次 checkpoint では周期の**内部模様**へ入る。

本 checkpoint の目標は、1周期内の非予約 residue（survivor）を定義し、その reflection symmetry を Lean に固定すること。

まだ next-prime lift / unique deletion / replication、Euler phi/cardinality、Legendre、PowerSwap へは進まない。

---

## 1. 新規 module

候補:

```text
DkMath/NumberTheory/PrimorialUniverse/WheelSurvivor.lean
```

import は既存 facade ではなく必要最小限を優先する。

最低でも:

```lean
import DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
```

必要なら gcd / Finset interval API の Mathlib import を追加してよい。

実装後:

```text
DkMath/NumberTheory/PrimorialUniverse.lean
```

へ公開 import を追加する。

---

## 2. 数学的対象

有限 prime basis `S` に対し

```text
M := finitePrimeBasisProduct S
```

とする。

1周期内部の survivor seat を概念的に

```text
0 < r
r < M
¬ ReservedByPrimeBasis S r
```

で定義する。

推奨 API:

```lean
def IsPrimeBasisWheelSurvivor (S : Finset ℕ) (r : ℕ) : Prop :=
  0 < r ∧
  r < finitePrimeBasisProduct S ∧
  ¬ ReservedByPrimeBasis S r
```

名称は既存 naming と整合する範囲で微調整可。

重要:

- `0` を survivor seat に含めない。
- period endpoint `M` も含めない。
- `M+1` 型 Euclid escape と混同しない。
- survivor は「prime である」という意味ではない。composite survivor も存在し得る。

---

## 3. Reduced-residue bridge

可能なら本 checkpoint で次を固定する。

有限 prime basis `S` について、`r` がどの basis prime にも予約されないことと、product `M(S)` と coprime であることの同値:

```lean
theorem not_reserved_iff_coprime_finitePrimeBasisProduct
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (r : ℕ) :
    ¬ ReservedByPrimeBasis S r ↔
      Nat.Coprime r (finitePrimeBasisProduct S)
```

向き・引数順は Mathlib API に合わせてよい。

これが重すぎる場合は、reflection theorem を先に閉じ、report で gcd bridge を次候補として明記して止めてもよい。ただし可能なら今回に含める。

数学的意味:

```text
wheel survivor
  = reduced residue modulo M
```

ただし、この checkpoint では Euler phi による cardinality 計算はしない。

---

## 4. Reflection theorem

核心はこれ。

`0 < r < M(S)` なら reflection seat

```text
M(S) - r
```

も同じ予約状態を持つ。

まず reservation predicate について、例えば:

```lean
theorem reserved_reflect_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {r : ℕ}
    (hr0 : 0 < r)
    (hrM : r < finitePrimeBasisProduct S) :
    ReservedByPrimeBasis S
        (finitePrimeBasisProduct S - r) ↔
      ReservedByPrimeBasis S r
```

または直接 non-reserved 版でもよい。

その上で主定理:

```lean
theorem wheelSurvivor_reflect
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {r : ℕ}
    (hr : IsPrimeBasisWheelSurvivor S r) :
    IsPrimeBasisWheelSurvivor S
      (finitePrimeBasisProduct S - r)
```

を閉じる。

必要な算術事実:

```text
0 < r < M
  -> 0 < M-r
  -> M-r < M
```

および、各 `p ∈ S` に対し `p ∣ M` なので

```text
p ∣ r  ↔  p ∣ M-r
```

が成立する。

Nat subtraction の side condition を明示的に処理すること。

---

## 5. Reflection involution

さらに reflection を2回適用すると元へ戻ることを固定する。

```lean
theorem wheelReflection_involutive
    {S : Finset ℕ} {r : ℕ}
    (hr : r ≤ finitePrimeBasisProduct S) :
    finitePrimeBasisProduct S -
        (finitePrimeBasisProduct S - r) = r
```

Mathlib に直接の既存 lemma があれば再利用する。

survivor 上では side condition は `hr.2.le` などから得る。

可能なら survivor pair をまとめる theorem も追加してよい:

```text
r survivor
  -> reflect r survivor
  -> reflect (reflect r) = r
```

---

## 6. Finset representation

後続の cardinality / lift theorem のため、1周期 survivor set を Finset として公開してよい。

候補:

```lean
def primeBasisWheelSurvivors (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (finitePrimeBasisProduct S - 1)).filter
    (fun r => ¬ ReservedByPrimeBasis S r)
```

ただし decidability / interval endpoint の扱いにより `Ico` 等へ変更可。

欲しい membership theorem:

```lean
@[simp] theorem mem_primeBasisWheelSurvivors_iff ... :
  r ∈ primeBasisWheelSurvivors S ↔
    IsPrimeBasisWheelSurvivor S r
```

reflection が set-level permutation になるところまで無理なく行けるなら追加可。ただし bijection/cardinality preservation の一般 theorem まで膨らませない。

---

## 7. Regression examples

最低限 `{2,3}` の period 6 で survivor pattern を固定する。

数学的には:

```text
M = 6
survivors = {1,5}
reflection: 1 <-> 5
```

候補 theorem:

```lean
theorem wheelSurvivors_two_three :
  primeBasisWheelSurvivors ({2,3} : Finset ℕ) = {1,5} := by
  ...
```

または membership facts を個別に固定してもよい。

余力があれば `{2,3,5}` の period 30 について

```text
{1,7,11,13,17,19,23,29}
```

を regression として入れてよいが、巨大な `decide` 展開や証明コストが高ければ不要。

今回の本質は reflection theorem であり、列挙そのものではない。

---

## 8. 意味境界

本 checkpoint で主張してよいのは:

```text
finite prime reservation sheet
  -> one-period survivor residues
  -> reduced-residue interpretation (可能なら)
  -> exact reflection symmetry
```

まだ主張しない:

- survivor が prime である
- survivor 数が `φ(M)` である
- next prime `q` を加えたとき exactly one lift が消える
- `(q-1)` 倍 replication
- wheel gap の propagation
- square anchor / Legendre
- PNT / sieve asymptotics
- PowerSwap / GN

特に `{2,3}` で `5` が survivor であることと、PUU-L001 の `M+1=7` escape を混同しないこと。

---

## 9. 実装順

推奨:

```text
A. survivor predicate
B. optional Finset survivor set + membership iff
C. reserved/nonreserved reflection iff
D. survivor reflection
E. reflection involution
F. optional gcd/reduced-residue bridge
G. 6-wheel regression
H. facade import / report
```

gcd bridge の方が reflection proof を短くするなら、F を C より前へ移動してよい。

---

## 10. Stop condition

以下が揃った時点で PUU-L006 を停止する。

```text
one-period survivor が Lean object になった
reflection symmetry が theorem になった
reflection が involution として固定された
6-wheel の {1,5} 模様が regression で確認された
```

その先の next-prime lift は PUU-L007 とする。

実装レポートには、

- survivor は prime predicate ではないこと
- reflection は product period に由来すること
- L005 の periodic reservation sheet から1周期を切り出したこと
- Euclid escape `M+1` との違い

を明記する。
