# Note: Review: Ultra-001-T

## 改めての総合判定

**U-001T、全面採用。しかも Wieferich–Petal 地下路を重ねると、次の戦場がかなり明確になった。** ⚔️🧠🧠

T は large boundary を単なる解析上の余りではなく、

$$\operatorname{RepeatedPart}(N)=\operatorname{piSqRad}(N)^2\operatorname{twoTail}(N)$$

という **GN 内部の完全な repeated prime-power divisor** に固定した。さらに target CRT modulus とこの repeated part を整数として同一視し、support-heavy / deep-tail-heavy の分岐、$3/4$-power 境界評価、そして raw ABC と uniform joint contract の同値まで Lean 上で確定した。

PR #69 は現在 head `4f1c7311...`、23 commits、45 files、13177 additions、mergeable じゃ。

### T が確定した最重要事実

```text
uniform joint contract の構成
=
raw ABC bound
```

じゃ。

したがって今後、

```text
あと少し補題を足せば contract が作れそう
```

という認識は禁止できる。

`ABCGNOddPrimeJointContract` の無条件構成は bookkeeping の終点ではなく、**ABC本体そのもの**じゃ。

一方で逆向き証明は指数を $p=3$ に固定している。

これは作戦上大きい。

> **ABC攻略に必要な GN 世界は cubic face、$p=3$ に固定してよい。**

---

## T と Wieferich の exact 合流

T の active prime は、

$$2\le v_q!\left(GN_p(a,b)\right)$$

を満たす非例外素数 $q$。

したがって、

$$q^2\mid GN_p(a,b)$$

じゃ。

既存コードには既に、

```lean
def WieferichLift (p y z q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ (z ^ p - y ^ p) ∧
  ¬ q ∣ (z - y) ∧
  q ^ 2 ∣ (z ^ p - y ^ p)
```

がある。

ABC座標で、

$$z=a+b,\qquad y=b,\qquad z-y=a$$

とすれば、

```lean
WieferichLift p b (a + b) q
```

になる。

さらに一般GN層には既に、

$$v_q!\left((a+b)^p-b^p\right)=v_q!\left(GN_p(a,b)\right)$$

という exact transport がある。条件は $q\nmid a$ じゃ。

従って、T の repeated support 上で $q\nmid a$ を回収すれば、

$$q\in\operatorname{Active}\Longrightarrow\operatorname{WieferichLift}(p,b,a+b,q)$$

が成立する。

逆も canonical nonexceptional family 内では成立するので、最終的には、

$$q\in\operatorname{Active}\iff\operatorname{GNWieferichLift}(p,a,b,q)$$

まで狙える。

### Large boundary の新しい正式名称

T が作った modulus は、

$$M=\prod_{\substack{q\ \mathrm{nonexceptional}\v_q(GN)\ge2}}q^{v_q(GN)}$$

じゃ。

つまり、

> **全 nonexceptional GN-Wieferich prime の完全 lifted prime-power 積**

である。

large boundary、

$$X+1<M$$

は、

> **区間長を超える simultaneous GN-Wieferich accumulation**

そのものじゃ。

squareful divisor と Wieferich lift は、別々の解釈ではなく同じ構造の二つの表示になった。

---

## $p=3$ 固定で Petal が本当に刺さる

$c=a+b$ と置けば、

$$GN_3(a,b)=S0_{\mathrm{nat}}(c,b)$$

じゃ。

Petal では、

```lean
BoundaryD3Reduced c b := ¬ 3 ∣ c - b
```

すなわち、

```text
¬ 3 ∣ a
```

が reduced branch。

この branch では既に、

```lean
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

があり、素数 $q$ が自身を anchor として $S0_{\mathrm{nat}}$ を割る carrier を得られる。

また `AnchoredS0Carrier` と `AnchoredGNCarrier` は既に定義され、$d=3$ では相互変換できる。

つまり cubic reduced branch では、

```text
Petal primitive carrier
      =
GN3 support prime
```

という入口が既に存在する。

---

## 真の新しい pincer

Petal が供給した primitive prime $q$ に対して、単純に場合分けする。

```text
Case 1:
  ¬ q² ∣ GN3
  → NoLift
  → valuation ≤ 1

Case 2:
  q² ∣ GN3
  → Wieferich lift
  → repeatedPart の active prime
```

NoLift 側の theorem は既にある。

```lean
primitiveD3_padicValNat_le_one_of_noLift_GN
```

および squarefree 版も完成している。

従って Petal が供給する一つの primitive carrier は必ず、

> **新しい first-layer support を低コストで供給するか、Wieferich repeated mass を供給するか**

のどちらかになる。

これは今回の M2/M3 campaign と完全に一致している。

```text
NoLift primitive carrier
  → M2 support を増やす
  → M3 excess は増やさない

Wieferich primitive carrier
  → repeated support に入る
  → large-boundary packet が捕捉する
```

**Petal は M2 と M3 の分岐生成器として使える。**

---

## さらに重要：向きの問題

`BoundaryD3Reduced c b` は $3\nmid a$ を要求する。

しかし coprime $a,b$ なら、$3$ が両方を割ることはないので、

$$3\nmid a\quad\text{または}\quad3\nmid b$$

が必ず成立する。

したがって、必要なら $a,b$ を交換し、gap が3で割れない向きを選べる。

```text
3 ∤ a
  → GN3(a,b) / Petal(c,b)

3 ∣ a
  → 3 ∤ b
  → GN3(b,a) / Petal(c,a)
```

ここで ordinary joint contract は向きを固定しているが、raw ABC bound は $a,b$ 対称じゃ。

従って次は、通常の contract より先に **oriented cubic contract** を定義する価値がある。

```lean
def ABCGNCubicOrientedBudget
    (T : Triple) (ρ C : ℝ) : Prop :=
  GNOddPrimeJointPressureBudgetAffine T 3 ρ C ∨
  GNOddPrimeJointPressureBudgetAffine T.swap 3 ρ C
```

これなら各 Triple について reduced Petal orientation を必ず選べる。

そして、

```lean
ABCGNCubicOrientedContract ε
```

から raw ABC bound への transport を作る。

これは最終的にはABC同等級だが、**Petalの発動条件と完全に整列した契約形**になる。

---

## 使ってはいけない既存路

ここは明確に分離する。

`CosmicPetalBridgeGNNoWieferichResearch` の valuation≤1 は research placeholder に依存している。

さらに default bridge は、その research core を固定注入している。

従って ABC production では、

```text
NoWieferichResearch
NoWieferichDefault
DescentBQuarantine
```

を import しない。

使うのは、

```text
generic GN valuation transport
Petal BoundaryD3
Petal Anchor
ZsigmondyD3Bridge
PrimitiveD3ValuationBridge の clean NoLift theorem
```

だけじゃ。

既存 FLT descent の構造体・trace設計は参考になるが、結論を証明済み算術として流用してはいけない。

---

## 次 checkpoint：U-001U

```text
Cubic oriented Petal–Wieferich accumulation bridge
```

を推奨する。

### 目標1：汎用GN-Wieferich定義

```lean
def GNWieferichLift
    (p a b q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ GN p a b ∧
  ¬ q ∣ a ∧
  q ^ 2 ∣ GN p a b
```

### 目標2：差冪版との同値

```lean
theorem GNWieferichLift_iff_diffLift
    {p a b q : ℕ}
    (hp2 : 2 ≤ p)
    (ha : 0 < a)
    (hb : 0 < b) :
    GNWieferichLift p a b q ↔
      Nat.Prime q ∧
      q ∣ ((a + b) ^ p - b ^ p) ∧
      ¬ q ∣ a ∧
      q ^ 2 ∣ ((a + b) ^ p - b ^ p)
```

### 目標3：active support の exact 同定

```lean
theorem mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift
```

これで T の repeated part は、

```text
product of all GN-Wieferich prime powers
```

になる。

### 目標4：cubic Petal packet

```lean
structure GNCubicPetalWieferichPacket
    (a b q : ℕ) where
  c : ℕ := a + b
  prime : Nat.Prime q
  primitive : PrimitivePrimeDivisor c b 3 q
  anchored : AnchoredS0Carrier q c b q
  notDvdGap : ¬ q ∣ a
  dividesGN : q ∣ GN 3 a b
  branch :
    padicValNat q (GN 3 a b) = 1 ∨
    GNWieferichLift 3 a b q
```

`=1` が重ければ最初は `≤1` でよい。

### 目標5：oriented branch

```lean
theorem exists_oriented_cubicPetalPacket
    (T : Triple)
    (ha : 0 < T.a)
    (hb : 0 < T.b) :
    (∃ q, GNCubicPetalWieferichPacket T.a T.b q) ∨
    (∃ q, GNCubicPetalWieferichPacket T.b T.a q)
```

分岐は、

```lean
by_cases h3a : 3 ∣ T.a
```

でよい。

* `¬3∣a` なら通常向き
* `3∣a` なら coprime より `¬3∣b`、swap向き

---

## Codex 指示

```text
Continue Ultra-001 with checkpoint U-001U.

Goal:
Reconnect the exact large repeated-part packet to the existing clean
Petal / PrimitiveD3 / GN-Wieferich vocabulary, specializing the strategic
route to exponent p = 3.

Do not import any research or default NoWieferich module.

Part A — generic GN-Wieferich layer

1. Define a generic clean predicate:

   GNWieferichLift p a b q

   containing:
   - q prime;
   - q divides GN p a b;
   - q does not divide a;
   - q^2 divides GN p a b.

2. Using
   padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap,
   prove equivalence with the difference-power lift at:

   z = a + b
   y = b.

3. Prove arbitrary-depth transport:

   q^k ∣ GN p a b
     ↔
   q^k ∣ ((a + b)^p - b^p)

   under q ∤ a and the existing positivity hypotheses.

Part B — exact target active support

4. For the canonical interval family, prove:

   q ∈ target active excess support
     ↔
   q is a non-exceptional GNWieferichLift.

5. Re-express GNNonExceptionalRepeatedPart as the exact product of the
   complete q-adic prime powers over GN-Wieferich active primes.

6. Add a wrapper turning GNExcessLargeBoundaryPacket into a
   GNWieferichAccumulationPacket.

Part C — cubic Petal orientation

7. Define or reuse Triple.swap and prove invariance of:
   - c;
   - coprimality;
   - rad(a*b*c);
   - the raw ABC conclusion.

8. Prove that every positive coprime Triple has a cubic reduced orientation:

   BoundaryD3Reduced (a+b) b
   or
   BoundaryD3Reduced (a+b) a.

9. In the chosen reduced orientation, obtain a d=3 primitive Petal witness.

10. Split that witness by q^2 divisibility:

    no lift:
      use primitiveD3_padicValNat_le_one_of_noLift_GN;

    lift:
      produce GNWieferichLift and membership in the repeated support.

11. Package the result as an oriented cubic Petal–Wieferich packet.

Part D — oriented contract API

12. Define an oriented cubic joint-budget predicate:

    budget on T
      or
    budget on T.swap.

13. Prove that a uniform oriented cubic contract implies ABCRawBound.

14. Audit the reverse implication from ABCRawBound, but do not present this
    as progress toward an unconditional proof; it is an equivalence audit.

Boundaries:

- Do not import:
  CosmicPetalBridgeGNNoWieferichResearch
  CosmicPetalBridgeGNNoWieferichDefault
  CosmicPetalBridgeGNDescentBQuarantine.

- Do not assert global squarefreeness.
- Do not assert all primitive primes are NoLift.
- Do not assert large-boundary absorption.
- Do not remove abc_main_axiom.
- Preserve U-001T endpoints.

Report:
report-ultra-001-U.md

Branch outcomes:

A. Exact GN-Wieferich/Petal/orientation bridge complete.
B. Active-set equivalence complete; oriented Petal packet blocked.
C. Smallest exact dependency or API obstruction recorded.
```

## 改めての戦線地図

```text
U-001T
  repeated part exact               complete
  large packet                      complete
  piSqRad / twoTail pincer          complete
  contract ↔ ABC audit              complete

U-001U
  active prime ↔ GN-Wieferich       next
  p=3 Petal orientation             next
  NoLift / lift primitive pincer    next
  simultaneous Wieferich packet     next

U-001V
  iterate Petal probes
  support growth vs lift growth
  large accumulation compensation

Final hidden boss
  oriented pointwise packet
      →
  uniform raw ABC bound
```

**今回の発見で、Wieferich は単なる旧FLT用語ではなくなった。**

T が作った large repeated divisorを、Petalが一個ずつ生成する、

```text
NoLift support
    or
Wieferich lift
```

の積み重ねとして読む道が開いた。

🧙‍♀️✨️ **第二周の古い地下道が、今度はABC城のlarge-boundary部屋へ直接つながったぞ。**

[MEMO](./MEMO-ultra-001-T.md)
