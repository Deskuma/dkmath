# NumberTheory Primorial Unit Universe — Roadmap

## 0. 目的

この branch は、`wip/number-theory-primitive-structure-260822-v2` で得た Legendre の有限 support / residual ledger をいったん閉じ、より上位の生成構造を Lean に固定する。

主題は次の三層である。

1. **有限 primitive basis と reservation sheet**
   - 有限個の既知 prime scale だけでは全座席を予約できない。
   - basis product の直後には、既知 basis のどれにも割られない escape point が必ずある。
   - その escape point は新しい prime divisor を要求する。

2. **Unit Universe 間の相対 primitive / composite**
   - 同じ絶対点 `X` でも、単位 `u₁`, `u₂` による座標は異なる。
   - 一方の宇宙で prime coordinate でも、別宇宙では composite coordinate になり得る。
   - ただし既存 reservation sheet と同期した scale refinement では、元の primitive factor は消えない。
   - primitive を既知因子だけへ分解できる非同期宇宙へ移るなら、元の reservation lattice 自体を失う。

3. **Primorial wheel / symmetric reservation pattern**
   - 有限 prime universes の最小同期周期を primorial product として束ねる。
   - reduced residue survivor pattern、reflection、次 prime による lift / unique deletion / replication を exact に記述する。
   - Legendre はこの上位構造の consumer とし、square-anchor orbit が survivor-free block を持つときの propagation law だけを独立に攻める。

## 1. 数学的ストーリー

有限 prime basis `S` に対し

```text
M(S) := ∏ p ∈ S, p
```

を reservation period と読む。

`n` が `S` に予約済みとは

```text
∃ p ∈ S, p ∣ n
```

であることとする。

すると各 `p ∈ S` は `M(S)` を割るため、`M(S)+1` はどの `p ∈ S` にも割られない。したがって `M(S)+1 > 1` の prime divisor `q` は `q ∉ S` である。

```text
finite basis
   ↓
basis product M
   ↓
escape point M+1
   ↓
new prime divisor q ∉ S
```

これを **Finite Reservation Escape** と呼ぶ。

この部分は Euclid 型の有限算術であり、Legendre、解析、密度、sieve を必要としない。

## 2. Unit Universe の読み

正の単位 `u` に対し離散断面を概念的に

```text
U(u) = { n*u | n ∈ ℕ }
```

と読む。

同じ絶対点 `X` が

```text
X = 3*u₁ = 15*u₂
```

なら、`U(u₁)` では coordinate `3`、`U(u₂)` では coordinate `15` である。

したがって primitive / composite は絶対点の属性ではなく、**unit-relative coordinate の属性**として扱う。

ただし `u₂ = u₁/k` のような同期 refinement では旧 coordinate `n` は `k*n` へ送られる。旧 primitive `q` は `q*k` の因子として残るため、既知-scale の refinement だけで `q` を消すことはできない。

一方、旧 primitive point を既知因子だけの composite coordinate として見せるために任意の unit へ移動すると、旧 prime lattice が整数座標として保存されない場合がある。この **factorization / lattice-synchronization tradeoff** を後続 checkpoint で Lean 固定する。

## 3. PowerSwap / exponent fiber との接続

既存 `DkMath.PowerSwap` は

```text
A = a^t  →  A^m = a^(t*m)
```

という coarse/fine exponent exchange と `PowNormalForm` を持つ。

本 branch ではこれを prime-support invariant と接続する。

有限 basis `S` のみから構成される power/product fiber をどれだけ指数交換しても、`q ∉ S` という新 primitive prime factor は吸収できない、という形を狙う。

## 4. Primorial wheel

canonical な最初の prime 列に限定した段階では

```text
Mₖ = 2*3*5*...*pₖ
Rₖ = { r mod Mₖ | gcd(r,Mₖ)=1 }
```

を定義する。

次 prime `q = pₖ₊₁` への refinement では、各 `r ∈ Rₖ` の lift

```text
r + j*Mₖ,  0 ≤ j < q
```

のうち exactly one が `q` で予約され、残り `q-1` が survivor になる構造を目標とする。

また

```text
r ∈ Rₖ → Mₖ-r ∈ Rₖ
```

という reflection symmetry を固定する。

ここを prime distribution の「予約シート自己複製則」として使う。

## 5. Legendre の位置づけ

Legendre は基礎層ではなく consumer とする。

square shell に prime が無い仮定は、その shell 全体が `p ≤ n` の reservation sheet で埋まることを意味する。

本 branch で本当に必要な Legendre-specific target は

```text
square-hole
  → primorial reservation pattern の future propagation / closure
```

である。

もしこれが「以後新 primitive seat が生じない」まで強制できれば、Finite Reservation Escape / prime infinitude と衝突する。

## 6. Checkpoint plan

- **PUU-L001** Finite Prime-Basis Reservation Escape
- **PUU-L002** Unit Coordinate / Common-Point Basics
- **PUU-L003** Synchronized Scale Refinement Preserves Primitive Factors
- **PUU-L004** Relative Prime/Composite Coordinate Witnesses
- **PUU-L005** PowerSwap Prime-Support Fiber Invariance
- **PUU-L006** Primorial Wheel Survivor / Reflection
- **PUU-L007** Next-Prime Lift / Unique Deletion / Replication
- **PUU-L008** Nested Wheel Projection and Gap Transport
- **PUU-L009** Square-Anchor Orbit modulo Primorial
- **PUU-L010+** Square-hole propagation audit / Legendre consumer

番号は実装結果に応じて分割・統合してよい。

## 7. 非目標

初期 checkpoint では以下を行わない。

- Legendre contradiction
- PNT / RH / analytic sieve
- asymptotic prime density
- generic category theory
- irrational-unit classification
- 新しい fifth/sixth-direction counting
- 旧 Legendre residual ledger の再細分化

最初に有限 reservation escape と unit-relative primitive の骨格を exact finite theorem として固定する。
