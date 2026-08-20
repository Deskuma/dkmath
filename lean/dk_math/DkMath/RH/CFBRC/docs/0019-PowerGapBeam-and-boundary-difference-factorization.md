# 0019 — PowerGapBeam と境界差の因数分解

## 1. この文書の位置づけ

`0018-General-CoreBeamGap-and-Cosmic-Formula-decomposition.md` では、一般次数の二項展開を

```text
Big
= Body + Gap
= Core + Beam + Gap
```

として読む `DkMath.CosmicFormula.CoreBeamGap` を整理した。

本稿では、同じ宇宙式思想の別の基本形である

```text
差
→ 境界 Gap
→ 残りの Beam
```

を扱う。

対象 module は

```text
DkMath.CosmicFormula.PowerGapBeam
```

である。

この module の中心は、冪差を exact に

$$
z^d-x^d=(z-x)\,\operatorname{powerBeam}_d(x,z)
$$

へ分解することである。

この構造は RH やゼータ関数を含まない純代数 Core であり、後に mirror difference や analytic divided-difference を読む際の原型になる。ただし、後者との接続はこの module 自身の theorem ではないので、本稿でも区別して扱う。

---

## 2. `powerGap` — 次数に依存しない境界差

定義は

```lean
def powerGap {R : Type*} [Ring R] (x z : R) : R :=
  z - x
```

である。

したがって `powerGap` は単に

$$
\operatorname{powerGap}(x,z)=z-x
$$

であり、次数 $d$ に依存しない。

これは重要である。

冪差

$$
z^d-x^d
$$

の次数依存性を境界差そのものへ押し込むのではなく、境界は常に `z - x` とし、残る次数情報を Beam 側へ集約する設計になっている。

DkMath の語彙では、まず「二つの境界状態がどれだけ離れているか」を Gap として取り出し、その差が高次世界でどのように増幅・伝播されるかを Beam が担う、と読める。

---

## 3. `powerBeam` — 冪差の divided-difference kernel

定義は

```lean
def powerBeam {R : Type*} [CommRing R]
    (d : ℕ) (x z : R) : R :=
  Finset.sum (Finset.range d) fun i =>
    z ^ (d - 1 - i) * x ^ i
```

である。

式では

$$
\operatorname{powerBeam}_d(x,z)
=
\sum_{i=0}^{d-1} z^{d-1-i}x^i.
$$

これは既存の `DkMath.Algebra.DiffPow.diffPowSum z x d` と definitionally 同じ object であり、module 内で

```lean
theorem powerBeam_eq_diffPowSum ...
```

として橋渡しされている。

従って `powerBeam` は新しい ad hoc quantity ではなく、標準的な冪差因数分解 kernel に Cosmic Formula の Beam という役割名を与えたものである。

---

## 4. 主定理 — 冪差は Gap × Beam

中心 theorem は

```lean
theorem pow_sub_pow_eq_gap_mul_powerBeam
    {R : Type*} [CommRing R]
    (d : ℕ) (x z : R) :
    z ^ d - x ^ d =
      powerGap x z * powerBeam d x z
```

である。

すなわち

$$
z^d-x^d
=
\operatorname{powerGap}(x,z)
\operatorname{powerBeam}_d(x,z).
$$

`powerGap = z-x` を代入すれば、通常の冪差公式

$$
z^d-x^d
=
(z-x)
\sum_{i=0}^{d-1}z^{d-1-i}x^i
$$

そのものである。

ここで DkMath 的に重要なのは、**差全体を一つの Gap と呼ばない**ことにある。

```text
whole difference = boundary Gap × propagation Beam
```

という役割分離を行っている。

したがって、ある差がゼロになる場合でも、直ちに Beam がゼロとは限らない。

$$
(z-x)\,\operatorname{powerBeam}_d(x,z)=0
$$

から得られるのは、環の条件に応じて

```text
boundary Gap がゼロ
または
Beam がゼロ
```

という分岐である。

この firewall は後の応用でも保持しなければならない。

---

## 5. 低次数での具体形

### 5.1 $d=0$

```lean
@[simp] theorem powerBeam_zero ...
```

により

$$
\operatorname{powerBeam}_0(x,z)=0.
$$

### 5.2 $d=1$

```lean
@[simp] theorem powerBeam_one ...
```

により

$$
\operatorname{powerBeam}_1(x,z)=1.
$$

従って

$$
z-x=(z-x)\cdot1.
$$

### 5.3 $d=2$

```lean
theorem powerBeam_two ...
```

により

$$
\operatorname{powerBeam}_2(x,z)=z+x.
$$

従って

$$
z^2-x^2=(z-x)(z+x).
$$

これは module 内で Pythagorean Beam として明示されている。

### 5.4 $d=3$

```lean
theorem powerBeam_three ...
```

により

$$
\operatorname{powerBeam}_3(x,z)
=
z^2+zx+x^2.
$$

従って

$$
z^3-x^3
=
(z-x)(z^2+zx+x^2).
$$

### 5.5 $d=4$

```lean
theorem powerBeam_four ...
```

により

$$
\operatorname{powerBeam}_4(x,z)
=
z^3+z^2x+zx^2+x^3.
$$

このように、境界 Gap は常に同じ `z-x` であり、次数が上がるほど Beam が高次 kernel へ成長する。

---

## 6. `CoreBeamGap` との違い

`0018` の `CoreBeamGap` は、和の冪

$$
(x+u)^d
$$

を

```text
Core + Beam + Gap
```

へ分解した。

一方 `PowerGapBeam` は、二つの冪の差

$$
z^d-x^d
$$

を

```text
boundary Gap × Beam
```

へ因数分解する。

したがって両者は異なる surface を扱う。

```text
CoreBeamGap:
  full binomial whole の additive decomposition

PowerGapBeam:
  endpoint power difference の multiplicative factorization
```

どちらも Beam を持つが、同じ定義ではない。

ここを名前だけで同一視してはならない。

`CoreBeamGap.Beam` は $(x+u)^d$ の中間二項係数項の総和であり、`PowerGapBeam.powerBeam` は $z^d-x^d$ の difference quotient kernel である。

---

## 7. FLT bridge は factorization の応用

module は Fermat 型方程式

$$
x^d+y^d=z^d
$$

から

$$
y^d
=
\operatorname{powerGap}(x,z)
\operatorname{powerBeam}_d(x,z)
$$

を導く theorem

```lean
theorem flt_eq_forces_powerGapBeam ...
```

を持つ。

対称形として

$$
x^d
=
\operatorname{powerGap}(y,z)
\operatorname{powerBeam}_d(y,z)
$$

もある。

重要なのは、この theorem 自身が FLT の不可能性を証明するわけではないことである。

証明されているのは、FLT-style equality が成立したなら、その一辺が Gap × Beam product として表現される、という exact algebraic bridge である。

---

## 8. RH / mirror route へ持ち込む際の読み方

この節は `PowerGapBeam.lean` の theorem そのものではなく、後続研究への構造的読み替えである。

RH 側ではしばしば involution

$$
s\longleftrightarrow1-s
$$

や same-height critical mirror によって、二つの observable の差

$$
f(1-s)-f(s)
$$

が現れる。

`PowerGapBeam` が示す一般原理は、**差を見たときに差全体を一つの mysterious defect と扱わず、まず endpoint difference と divided-difference kernel に分離せよ**、というものである。

多項式なら exact に

$$
f(z)-f(x)
=
(z-x)\,B(x,z)
$$

が得られる。

解析関数へ移る場合には同じ式が自動的に Lean Core として使えるわけではない。別途 analytic divided-difference theorem が必要である。

従って、例えば

$$
f(1-s)-f(s)
$$

に対して

$$
(1-2s)\,\mathcal B(s)
$$

という形を期待することは構造上自然だが、それは **PowerGapBeam の直接の結論ではない**。

この区別を維持する。

---

## 9. critical center との形式的対応

mirror endpoint を

$$
x=s,
\qquad
z=1-s
$$

と形式的に置けば、境界差は

$$
z-x
=
(1-s)-s
=
1-2s.
$$

中心座標

$$
\delta=s-\frac12
$$

を使えば

$$
1-2s=-2\delta.
$$

したがって、mirror difference を Gap × Beam へ因数分解できる observable が見つかった場合、その boundary Gap の zero locus は自然に

$$
\delta=0
$$

すなわち critical center に一致する。

ただし再度強調すると、**各具体的 RH observable が本当にこの factorization を持つかは別 theorem である。**

`PowerGapBeam` が提供するのは、その設計原型と純代数 Core までである。

---

## 10. Proof-audit ledger

### Core — 証明済み

- `powerGap x z = z - x`。
- `powerBeam` は finite power difference kernel。
- `powerBeam = diffPowSum`。
- 任意次数で

$$
z^d-x^d
=
(z-x)\operatorname{powerBeam}_d(x,z).
$$

- $d=2,3,4$ の具体形。
- FLT-style equality から Gap × Beam 表現を得る bridge。

### Beam — 後続へ使える構造

- endpoint difference を先に抽出する設計。
- zero locus と propagation kernel の役割分離。
- mirror difference / prime-side difference を divided-difference 化する際の algebraic prototype。

### Gap — この module では未証明

- standard zeta / eta / Xi / finite prime source が実際に `powerGap × powerBeam` 型へ factorize すること。
- analytic divided-difference の存在・正則性・非消滅性。
- mirror boundary Gap の zero から RH を導く bridge。
- prime-side Beam が centered-coordinate lower bound や zero-derived upper bound を供給すること。

### Obstruction / firewall

- `difference = 0` から自動的に `boundary Gap = 0` としてはならない。
- `CoreBeamGap.Beam` と `PowerGapBeam.powerBeam` を同一 object としてはならない。
- 多項式の factorization を解析関数へ無証明で移植してはならない。

---

## 11. まとめ

`PowerGapBeam` は DkMath の「差を見る」側の基本 Core である。

```text
power difference
  ↓
boundary Gap = z - x
  ×
power Beam = divided-difference kernel
```

という exact factorization により、境界の一致条件と、高次構造を運ぶ kernel を分離する。

これは `CoreBeamGap` の additive decomposition と相補的である。

```text
CoreBeamGap:
  Big を内部成分へ分解する

PowerGapBeam:
  difference を boundary Gap × Beam へ分解する
```

後続の RH / CFBRC 形式化では、この原型を根拠に mirror difference や prime-source difference の analytic factorization を探索できる。しかし、その analytic bridge は独立に証明されるまで Gap のままである。
