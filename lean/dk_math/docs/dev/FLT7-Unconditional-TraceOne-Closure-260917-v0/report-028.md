# FLT7TC-005R22 — Smaller-norm successor audit

## A. New verified deductions

`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSuccessorAudit.lean` を追加し、
005R21 の `DirectOrbitPowerSplitPacket` から次を kernel-check した。

- `Int.natAbs (norm gapRoot) * Int.natAbs (norm quotientRoot) = a^6`。
  中間段階として `(G * Q)^7 = a^42` も公開した。
- `rho1-rho0`、`rho2-rho1`、`rho0-rho2` の3辺を、同じ
  `eisensteinAxis^(32+42*k)` と明示的な unit coefficient を用いて表した。
- telescoping により、unit coefficient を保持した exact な
  `eps0*g0^7 + eps1*g1^7 + eps2*g2^7 = 0` を証明した。
- `DirectRealCubicTwistedSeventhState` を定義し、root=`g`、回転 root、3つの
  unit coefficient、twisted equation、`0 < natAbs(norm root)` を保持する state を構成した。
- `directOrbit_twisted_state_measure_lt` により、構成した state の root norm が
  元の `r.summit.gapRoot` より小さいことを証明した。

ノルム補完は unit norms と `norm_intCast` だけを用い、element-level
coprimality から `gcd(G,Q)` は推論していない。

## B. Full three-edge unit-class analysis

production の係数は次の unit として保持した。ここで `P` は
`directOrbitPairAxisUnitOne`、`sigma` は `directOrbitRotateUnit`、
`e=32+42*k` である。

```text
eps0 = eta
eps1 = P^e * sigma(eta)
eps2 = P^e * sigma(eps1)
```

したがって、Astra-001 の予測した `projectiveLog eta = (2,4)` は、state を
構成するだけなら不要である。係数を unit のまま保存すれば、generator-independent
な eta の class theorem を新たに仮定せずに3辺方程式を得られる。

この checkpoint では、`sigma` の projectiveLog 上の線形作用と、上記3係数の
具体的な `ZMod 7` class equality は productionize していない。従って係数 triple
を source-independent な canonical triple に正規化したとは主張しない。

## C. Theta-adic factorization analysis

第1辺は既存 split と `gapCore_eq` から exact に得られ、第2辺と第3辺は
`rotateEquiv theta = theta * pairAxisUnit 1` の反復で同じ theta depth に揃えた。
各係数は unit typed であり、回転による unit action を捨てていない。

この state からは、new orbit gap の exact theta depth、homogeneous quotient の
common-prime localization、theta-free factor の seventh-power split はまだ導けない。
従って sign-free height inequality を state 単独から再適用する定理も未実装である。

## D. Candidate closure routes

1. **Cyclic twisted state route** — 3辺分解、telescoping、正の root norm、元の
   summit に対する strict measure decrease までが exact。最初の欠落は、任意の
   twisted state から新しい orbit gap に対して、元のものと同じ theta-depth と
   coprime quotient split を再構成する bridge。これは元の endpoint packet を
   state に戻していないので非循環である。
2. **Direct integer summit route** — `G<A` と正の root normだけは利用可能。
   `L'^7-R'^7=D'^7`、`L'-R'=7^6*A'^7`、cyclotomic factor、`D'=7*A'*B'`、
   endpoint coprimality、TraceOne root、exact norm は current data から構成できない。
   特に `A'=G` とは置いていない。
3. **Hybrid route** — twisted state に exact theta-depth、quotient coprimality、
   primitive/local data を追加してから integer summit へ戻す route。追加 invariant
   が未証明なので、現時点の closure route ではない。

## E. Rejected routes

- `G<A` だけから `G` を新しい `gapRoot` とする route。
- `gapCore` と `quotientCore` の element coprimalityから `G,Q` の整数 coprimalityを
  推論する route。
- twisted equation の unit coefficientsを消して canonical な係数を仮定する route。
- twisted state から同型 successor が得られると仮定して well-founded descent を
  宣言する route。
- historical receiver/routing packet を successor の前提にする route。

## F. Best next bounded checkpoint

`DirectRealCubicTwistedSeventhState` に対して、次の一つの bridge を独立に証明する。

```text
twisted state
  -> exact theta depth of root-rotate root gap
  -> homogeneous quotient coprimality/localization
  -> unit * seventh-power theta-free split
```

この bridge が得られるまで、`next : state -> state` や無限降下 consumer は追加しない。

Validation は順次実行し、production module、`DkMath.FLT.Seven` facade、API test、
axiom test の全てを build 済み。decisive declarations の axiom set は
`[propext, Classical.choice, Quot.sound]` であり、対象 source に
`sorry`、`sorryAx`、`admit`、`unsafe`、project axiom はない。

## G. Confidence

**B — strong route with one substantial bridge.**

正確な norm complement、3辺の共通 theta factor、unit-twisted cyclic equation、
strict smaller measure を得たため、Outcome B（cyclic twisted successor state green;
one precise self-similarity bridge remains）と判定する。完全な非循環 descent や
unconditional FLT7 はまだ主張しない。
