# Multi-Gauge Divisibility / Norm–Lattice Landing 研究計画

- cid: `6a9d5951-68dc-83ee-b422-0b21f77bac4a`
- Status: research plan / not implemented
- Date: 2026-09-12
- Branch at recording: `wip/ABC-GN-astra-260906-v1`
- Repository: `Deskuma/dkmath`
- Scope: DkMath generic arithmetic / CosmicFormula / quadratic-order infrastructure
- Origin: ABC-GN Astra v1 discussion, but this topic is **not ABC-specific**

## 1. 目的

本資料は、宇宙式 / GN の可除性を一段の固定単位 `u` だけで見るのではなく、
除算や正規化の後に単位ゲージを更新し、複数段の

```text
(x₁,u₁) -> (x₂,u₂) -> ...
```

を一つの可除性経路として扱う研究テーマを記録する。

その後、この多段可除性を quadratic-order の Norm と接続し、

```text
GN gcd sieve
  -> gauge-pair / gauge-path admissibility
  -> Norm divisibility
  -> coordinate divisibility
  -> integer-lattice landing
  -> power/Core-image landing
```

という階層的な「格子着地判定」へ進むことを目的とする。

ABC 予想はこの理論の応用候補の一つにすぎない。FLT、Zsigmondy、Petal、TraceOne quadratic arithmetic などにも再利用できる一般 API として設計する。

---

## 2. 既存 production fact: 一段 GN gcd firewall

`DkMath.Lib.Cosmic.GTailBoundary` には、一般 `GTail` に対して既に

$$
\gcd(x,GTail(d,r,x,u))=
\gcd\!\left(x,\binom dr u^{d-r}\right)
$$

がある。

`Nat.Coprime x u` の下では、

$$
\gcd(x,GTail(d,r,x,u))=
\gcd\!\left(x,\binom dr\right)
$$

まで縮約される。

特に `r = 1` の通常 GN では、

$$
\gcd(x,GN_d(x,u))=\gcd(x,d)
$$

となる。

既存 theorem:

```lean
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
gcd_GN_eq_gcd_of_one_le
```

素数指数 `p` ではさらに、

```lean
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

により、各段の boundary/GN 共通部分は `1` または `p` の二状態へ落ちる。

したがってこの層は既に PRODUCTION-PROVED であり、新研究では再証明しない。

---

## 3. 既存 production fact: Bezout / primitive separation

`DkMath.Petal.BezoutBridge` と下層 `UniqueFactorizationGN` には、

```text
body difference = boundary * GN
primitive witness avoids boundary
therefore primitive witness is observed on GN
```

という一段の Bezout/gcd 読みがある。

非例外素数 `q`, `q ∤ d` については、

$$
q\nmid\gcd(x,GN_d(x,u))
$$

が既に利用可能であり、valuation 版・prime-power 版も存在する。

代表 theorem:

```lean
prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
```

新研究の焦点は「一段 firewall の強化」ではなく、**複数段を transition で接続すること**である。

---

## 4. 欠けているもの: Gauge Transition

現状 `GTail_rec` は tail depth `r` を増やす再帰であり、同じ `(x,u)` の内部展開である。

今回必要なのは別種の遷移である。

```text
stage 1:
  object A₁
  coordinates (x₁,u₁)
  divisibility / quotient test

          ↓ divide / normalize / rescale

stage 2:
  object A₂
  coordinates (x₂,u₂)
  renewed divisibility test
```

すなわち、第1段の商や正規化結果から第2段の単位 `u₂` と boundary `x₂` がどのように生成されるかを明示する `GaugeTransition` が必要になる。

最初の型候補:

```lean
structure GNGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ
  coprime : Nat.Coprime x u

structure GNTwoStageGauge (d : ℕ) where
  first : GNGaugeStage d
  second : GNGaugeStage d
  transition : Prop -- exact relation to be designed
```

`transition` は最初から抽象 Prop として固定してよい。具体的な ABC / FLT / quadratic-order 応用は別 bridge で与える。

---

## 5. 二段 gcd sieve

二段について

$$
g_i:=\gcd(x_i,GN_d(x_i,u_i))
$$

と置く。

各段の `Coprime xᵢ uᵢ` から既存 theorem を二回適用すれば、

$$
g_1=\gcd(x_1,d),
\qquad
g_2=\gcd(x_2,d)
$$

が得られる。

最小 theorem 候補:

```lean
theorem twoStage_gcd_state ... :
  Nat.gcd s.first.x (GTail d 1 s.first.x s.first.u) = Nat.gcd s.first.x d ∧
  Nat.gcd s.second.x (GTail d 1 s.second.x s.second.u) = Nat.gcd s.second.x d
```

より意味論的な prime witness 版として、両段のいずれかで

```text
q | boundary
q | GN
```

が同時成立するなら、

$$
q\mid d
$$

へ押し込む theorem を作る。

候補:

```lean
theorem twoStage_commonPrime_dvd_exponent ...
```

素数指数 `p` なら各段の gcd state は `1` または `p` なので、二段状態は高々

```text
(1,1)
(p,1)
(1,p)
(p,p)
```

の4状態になる。

ここへ `transition` 固有条件を入れることで、実現不能な `(u₁,u₂)` ペアや gcd-state pair をさらに落とす。

この **transition-aware pruning** が新しい数学部分である。

---

## 6. 多段化

二段は最初の実装単位であり、本来の対象は有限列

```text
(x₀,u₀)
 -> (x₁,u₁)
 -> ...
 -> (xₙ,uₙ)
```

である。

素数指数 `p` なら、各 stage の gcd state は概念的に

```text
off-prime : 1
ramified  : p
```

の二状態となる。

従って gauge path は有限状態列として扱える可能性がある。

仮称:

```text
GN divisibility automaton
multi-gauge divisibility path
```

ただし automaton API は二段 theorem を固めた後に導入する。最初から一般化しすぎない。

---

## 7. Norm 層との接続

quadratic order で

$$
\alpha=\beta q
$$

が成立すれば、Norm multiplicativity により

$$
N(\alpha)=N(\beta)N(q)
$$

となる。

したがって、元素可除性

$$
\beta\mid\alpha
$$

から整数可除性

$$
N(\beta)\mid N(\alpha)
$$

が従う。

しかし逆は一般には成立しない。

```text
Norm divisibility
  is necessary
  but not sufficient
for element divisibility / lattice landing.
```

この「体積としては割れるが格子には着地しない」ケースを、次の coordinate divisibility 層で篩う。

既存の `TraceOneQuadratic.norm`、`traceOne_norm_mul`、および昇格済み `DkMath.Lib.NumberTheory.EisensteinCoordinates` を再利用する。

---

## 8. Eisenstein 整数での格子着地モデル

標準 Eisenstein 座標

$$
\alpha=a+b\omega,
\qquad
\beta=c+d\omega
$$

を考える。

Norm は

$$
N(\beta)=c^2-cd+d^2
$$

である。

共役を使えば

$$
\frac{\alpha}{\beta}=
\frac{\alpha\overline\beta}{N(\beta)}
$$

となり、分子の座標は

$$
\alpha\overline\beta=
(ac-ad+bd)+(bc-ad)\omega
$$

である。

従って `β ≠ 0` の下で、商が再び Eisenstein 整数格子へ着地するための自然な coordinate divisibility 条件は

$$
N(\beta)\mid(ac-ad+bd)
$$

かつ

$$
N(\beta)\mid(bc-ad)
$$

である。

最初の具体的な研究目標は、この条件を Lean 上で element divisibility / quotient existence と iff にすること。

候補 theorem:

```lean
theorem eisenstein_dvd_iff_norm_dvd_conjugate_coordinates ...

theorem eisenstein_latticeLanding_iff ...
```

重要:

```text
N(β) | N(α)
```

だけでは十分でないことを API 上でも明確に分離する。

---

## 9. 一般 TraceOne quadratic order への拡張

Eisenstein `s = -1` は最初の concrete model とする。

最終的には `TraceOneInt s` に対して、

```text
α * conj β
```

の二座標が `norm β` で割れることと、`β | α` または商の `TraceOneInt s` 着地を結ぶ一般 theorem を目標とする。

ここでは具体式を先に固定せず、既存 `TraceOneQuadratic.mul`, `conj`, `norm` を基準に設計する。

想定配置:

```text
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
```

または既存 `TraceOneQuadratic` の安定 API が十分であれば、その近傍へ配置する。

---

## 10. Power / Core landing

整数格子へ着地しただけでは「真魔核」への着地は保証されない。

第1段:

```text
β | α
```

から商

$$
q:=\alpha/\beta
$$

が quadratic-order 格子へ戻った後、さらに

$$
q=\gamma^r
$$

であるかを判定する層が必要になる。

平方の場合は

$$
q=\gamma^2
$$

であり、DkMath 語彙では `γ²` を平方 Core、`β` を residual / Gap 側と読む。

したがって全体の filter は

```text
1. GN gcd admissibility
2. gauge transition admissibility
3. Norm divisibility
4. coordinate divisibility
5. integer-lattice landing
6. r-th-power / Core-image landing
```

となる。

---

## 11. Big / Core / Gap 読み

研究上の概念対応:

```text
Big:
  whole algebraic element α
  conserved scalar observer: N(α)

Core:
  repeated power component γ^r

Gap / residual:
  β

Beam / compatibility:
  divisibility, coprimality, coordinate-integrality,
  gauge-transition constraints
```

`N(α)` が固定されても、任意の `β,γ` が許されるわけではない。

Norm product は必要な体積保存しか表さず、
GN gcd、座標可除性、格子着地、power-image 条件が実現可能な分配だけを残す。

---

## 12. ABC との関係

ABC-GN Astra v1 では

$$
(a+2)+\omega=\beta\gamma^2
$$

型の explicit factorization を仮定した conditional consequence API まで production 化した。

本研究は、その factorization existence を ABC 専用に攻めるものではない。

ABC へ戻る場合は、一般理論を使って

```text
candidate β / gauge pair
  -> GN gcd sieve
  -> Norm divisibility
  -> Eisenstein lattice landing
  -> square-image landing
```

を判定する応用 bridge を別途作る。

ABC の balanced-box counting や factorization existence は引き続き OPEN であり、本研究計画はそれらを証明したとは主張しない。

---

## 13. FLT / Zsigmondy / Petal との関係

この研究テーマは以下にも接続可能である。

### FLT

一般奇素数 `p` では GN gcd state が `1 / p` の二状態へ縮約されるため、多段 descent の gauge-state 解析に利用できる可能性がある。

### Zsigmondy

primitive divisor が visible boundary を避け residual GN 側へ移る既存 BezoutBridge と、多段 transition を組み合わせられる可能性がある。

### Petal

`Boundary / GN` 二チャネルを一段 observer ではなく経路 observer として拡張できる。

---

## 14. 実装フェーズ案

### Phase 0 — 二段 packet

新数学を最小化し、既存一段 theorem を束ねる。

```text
GNGaugeStage
GNTwoStageGauge
twoStage_gcd_state
prime two-stage state cases
```

### Phase 1 — transition semantics

実際の quotient / normalization に基づく `GaugeTransition` の最小公理を決める。

ここから先は新数学。

### Phase 2 — Eisenstein lattice landing

`DkMath.Lib.NumberTheory.EisensteinCoordinates` を用いて、

```text
coordinate divisibility
<->
quotient lands in TraceOneInt (-1)
```

を形式化する。

### Phase 3 — general TraceOne landing

`s = -1` の concrete theorem を `TraceOneInt s` へ一般化する。

### Phase 4 — power-image landing

格子商が平方・立方・一般 `r` 乗像に入るための API を追加する。

### Phase 5 — application bridges

ABC / FLT / Zsigmondy / Petal から必要なものだけ接続する。

---

## 15. 非目標

この文書だけでは以下を主張しない。

```text
ABC conjecture proof
new FLT proof
general factorization existence
UFD / PID not already available
Norm divisibility => element divisibility
all gauge transitions are realizable
balanced-box sparsity
```

特に、Norm 可除性と格子着地を同一視しない。

---

## 16. 現時点の評価

### PRODUCTION-PROVED

```text
one-stage GTail/GN gcd firewall
prime off/ramified gcd states
one-stage Bezout / primitive separation
one-stage congruence collapse
TraceOne norm multiplicativity
neutral Eisenstein coordinate algebra
```

### OPEN / NOT IMPLEMENTED

```text
multi-gauge transition object
(u₁,u₂) admissibility theorem
two-stage transition-aware sieve
finite gauge-path state theorem
Norm-to-coordinate divisibility bridge
integer-lattice landing iff theorem
general TraceOne lattice landing
power/Core-image landing after quotient
```

---

## 17. 最初の研究問い

次の順序で調べる。

1. `GNTwoStageGauge` は transition を持たない単なる pair packet としてどこまで有用か。
2. 実際の除算・正規化から得られる最小 `GaugeTransition` 条件は何か。
3. prime exponent `p` の4状態 `(1,1),(p,1),(1,p),(p,p)` のうち transition が排除する状態はあるか。
4. Eisenstein 商の coordinate divisibility iff を完全に形式化できるか。
5. その theorem を `TraceOneInt s` へ自然に一般化できるか。
6. GN sieve と lattice landing を一つの end-to-end theorem に接続できるか。

研究路の中心は、

```text
可除性経路を GN が篩い、
Norm が保存量を測り、
座標可除性が整数格子への着地を判定し、
power-image 条件が真の Core への着地を判定する。
```

という役割分担を Lean 上で分離・接続することである。
