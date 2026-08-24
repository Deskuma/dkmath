# 0020 — PowerGapBeam GN / gcd / primitive arithmetic bridges

## 1. 目的

`0019` では一般環上の純代数として

$$
z^d-x^d=(z-x)\,\operatorname{powerBeam}_d(x,z)
$$

を固定した。

本節では、この factorization が自然数・整数の arithmetic layer へ入ったときに、

- 既存 `GN` beam とどう一致するか、
- primitive / coprime 条件が Gap と Beam の共通因子をどう制限するか、
- prime-adic valuation がどの factor 側へ載るか、
- primitive prime witness が contradiction machinery へどう輸送されるか、

を整理する。

ここで重要なのは、pure algebra の `PowerGapBeam` と、number-theoretic rigidity を混同しないことじゃ。

---

## 2. GN との exact bridge

`PowerGapBeamGN.lean` は heavy な `GN` dependency を pure `PowerGapBeam` 本体から分離し、低次数で explicit bridge を与える。

### degree 3

$$
\operatorname{powerBeam}_3(x,x+u)
=
\operatorname{GN}_3(u,x)
$$

また endpoint notation では

$$
\operatorname{powerBeam}_3(b,a)
=
\operatorname{GN}_3(a-b,b).
$$

### degree 4

同様に

$$
\operatorname{powerBeam}_4(x,x+u)
=
\operatorname{GN}_4(u,x),
$$

および

$$
\operatorname{powerBeam}_4(b,a)
=
\operatorname{GN}_4(a-b,b).
$$

つまり `GN` は別物の Beam ではなく、endpoint gap を座標として読み直した Power Beam と exact に一致する低次数 surface を持つ。

この bridge から divisibility、`padicValNat`、squarefree 性などを `GN` から Power Beam へそのまま輸送できる。

---

## 3. primitive context における gcd control

`PowerGapBeamGcd.lean` の中心 theorem は、整数 endpoint に対して

$$
\gcd(z,x)=1
$$

かつ $1\le d$ なら

$$
\gcd\bigl(\operatorname{powerGap}(x,z),
          \operatorname{powerBeam}_d(x,z)\bigr)
\mid d
$$

というものじゃ。

ここで

$$
\operatorname{powerGap}(x,z)=z-x.
$$

したがって primitive context では、Gap と Beam が大きな共通因子を自由に共有することはできず、その共有部分は degree $d$ に閉じ込められる。

特に prime $p$ が

$$
p\nmid d
$$

を満たすなら、同時に

$$
p\mid\operatorname{Gap}
$$

かつ

$$
p\mid\operatorname{Beam}
$$

となることは不可能じゃ。

これは `PowerGapBeam` の multiplicative decomposition に arithmetic separation を与える最初の rigidity である。

---

## 4. FLT-shaped equation が同じ factorization を要求する

FLT 型の式

$$
x^d+y^d=z^d
$$

からは exact に

$$
y^d
=
\operatorname{powerGap}(x,z)
\operatorname{powerBeam}_d(x,z)
$$

が得られる。

primitive condition を併せると、同じ observed side $y^d$ に対して

```text
product identity:
  y^d = Gap * Beam

gcd control:
  gcd(Gap, Beam) | d
```

が同時に成立する。

この同一対象性が後の valuation contradiction に必要じゃ。

---

## 5. prime valuation は Beam 側へ分離できる

prime $p$ が Beam を割り、かつ $p\nmid d$ なら、gcd control により $p$ は Gap を割れない。

したがって積

$$
\operatorname{Gap}\cdot\operatorname{Beam}
$$

の $p$-adic valuation は Beam の valuation だけになる。

Lean では概念的に

$$
v_p(\operatorname{Gap}\cdot\operatorname{Beam})
=
v_p(\operatorname{Beam})
$$

が証明される。

一方 FLT-shaped identity により積は $y^d$ なので、

$$
v_p(\operatorname{Beam})
=
d\,v_p(y).
$$

よって Beam valuation は degree $d$ の倍数として拘束される。

これは単なる divisibility ではなく、Power Beam が $d$-th power side の valuation を丸ごと引き受けることを意味する。

---

## 6. valuation upper bound / squarefree との collision

もし同じ Beam に対して別 source から

$$
v_p(\operatorname{Beam})\le1
$$

が得られ、さらに $p\mid\operatorname{Beam}$ なら

$$
1\le v_p(\operatorname{Beam})\le1.
$$

したがって valuation は $1$。

しかし $d\ge2$ なら

$$
v_p(\operatorname{Beam})
=
d\,v_p(y)
$$

という倍数条件と両立しない。

同様に Beam が squarefree であるという情報も、prime valuation が高くなるべき FLT 側条件と衝突させられる。

ここで contradiction は pure `PowerGapBeam` から出るのではない。

```text
exact factorization
+ primitive gcd separation
+ prime divisibility
+ independent valuation/squarefree bound
```

の合成で初めて生じる。

---

## 7. primitive prime witness の輸送

`PowerGapBeamPrimitive.lean` は `PrimitiveBeam` 側の

```lean
PrimitivePrimeFactorOfDiffPow q a b 3
```

を endpoint cubic Power Beam へ輸送する。

自然数 endpoint $b<a$ に対し、primitive prime witness $q$ から

$$
q\mid\left|\operatorname{powerBeam}_3(b,a)\right|
$$

を得る。

さらに $b<a$ なら cubic endpoint Beam 自身が非零であることも証明される。

これにより primitive witness は、valuation contradiction theorem が必要とする

```text
prime q
beam divisibility
beam nonzero
```

を concrete に供給できる。

---

## 8. ordinary cubic branch と exceptional prime

cubic degree では $d=3$ なので、prime $q$ に対する通常 branch は

$$
q\ne3
$$

である。

prime $q\ne3$ なら

$$
q\nmid3
$$

が得られるため、Gap / Beam separation を適用できる。

`CubicPrimitiveFLTContext` はこの ordinary cubic branch を bundle し、

- primitive prime witness,
- ordered endpoints,
- coprime condition,
- FLT-shaped equation,
- observed side nonzero,
- $q\ne3$,

を一つの context にまとめる。

一方 $q=3$ は exceptional branch として意図的に分離されており、通常 branch に吸収されていない。

---

## 9. Core / Beam / Gap 観点での意味

ここまでを DkMath 語彙でまとめると、

```text
PowerGapBeam pure algebra
  ↓
endpoint gap × degree beam
  ↓
primitive gcd control
  ↓
prime factor cannot live in both Gap and Beam
  ↓
valuation is forced onto Beam
  ↓
independent low-valuation / squarefree informationとcollision
```

となる。

つまり arithmetic layer では Beam は単なる「中間項」ではない。

> 境界 Gap から分離された prime-power burden を受け持つ arithmetic carrier

として振る舞う。

---

## 10. RH-CFBRC への監査上の注意

この arithmetic rigidity は FLT / primitive integer setting で成立するものじゃ。

したがって、RH-CFBRC の mirror difference や analytic divided-difference に対して、

```text
PowerGapBeam で prime separation が起きる
```

と自動的に移植してはならない。

RH 側で同種の構造を使うなら、少なくとも

1. analytic endpoint difference が exact に Gap × Beam へ因数分解されること、
2. arithmetic source がその Beam に本当に載ること、
3. Gap / Beam の独立性または共通因子制約に対応する analytic theorem があること、

を別途証明する必要がある。

`PowerGapBeamGN / Gcd / Primitive` は、そのような bridge を設計するときの arithmetic prototype であり、そのまま RH theorem ではない。

---

## 11. 現在の依存位置

```text
CoreBeamGap
   ↓
PowerGapBeam
   ↓
PowerGapBeamGN
   ↓
PowerGapBeamGcd
   ↓
PowerGapBeamPrimitive
```

この系列により、DkMath の `Gap × Beam` は

```text
pure factorization
→ GN coordinate
→ gcd separation
→ prime valuation
→ primitive-prime contradiction
```

まで一貫した arithmetic meaning を持つ。

次の層では、この prototype と RH-CFBRC の mirror / prime-mode 構造を混同せず、どこまで exact に対応づけられているかを監査する必要がある。
