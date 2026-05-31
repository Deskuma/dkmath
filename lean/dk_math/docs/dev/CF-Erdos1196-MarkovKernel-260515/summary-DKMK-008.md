# report: DKMK-008

うむ。では DKMK-008 を、山道全体として総括するぞい。
結論から言えば、DKMK-008 は **DKMK-007 で整えた mass / hitting route に対して、下降路そのものを one-step から multi-step path family へ拡張した章** じゃ。

DKMK-007 が「質量をどう測るか」の章なら、DKMK-008 は **その質量がどの道を下るか** を作った章じゃな。最後の DKMK-008O では、この章全体が `path substrate`、`shadow bridge`、`one-step recovery`、`witness route` の四層として整理され、manual path / one-step divisor path / witness-derived multi-step quotient path の三入口を持つ route として一区切りになった。

## 1. DKMK-008 の主目的

DKMK-008 の主目的は、DKMK-007 の one-step divisorStep

$$
n\to n/q
$$

を、より一般の list-shaped divisor descent path

$$
n_0\to n_1\to n_2\to\cdots
$$

へ拡張することじゃった。

ただし、単に list を作るだけでは足りぬ。
DkMath の hitting route へ載せるには、次が必要になる。

```text
path が DivisibilityChain になること
各 node が source を割ること
selected / canonical shadow の weight を載せられること
finite-step / two-step mass bound へ接続できること
```

DKMK-008 は、この一連の橋を A〜O までで段階的に整えた。

## 2. 008A-B: path substrate

まず DKMK-008A では、

```lean
AdjacentDivisorPath
```

が導入された。

これは list の隣接要素が整除下降

$$
n_{i+1}\mid n_i
$$

を満たす、という predicate じゃ。

さらに、path から `DivisibilityChain` へ落とし、singleton family として source-controlled route に載せる最小核が入った。

次に DKMK-008B では、single path から indexed family へ昇格した。

```lean
AdjacentDivisorPathFamily
```

各 index (i) に対して、

```lean
source i :: tail i
```

という path を持たせる構造じゃ。
ここで source を head として固定したのが良い。すべての node が source を割ることを示しやすく、後の source mass control に直結する。

この段階で、

```text
list-shaped divisor path
→ indexed path family
→ DvdControlledChainFamily
→ SourceControlledChainFamily
```

の土台ができた。

## 3. 008C-F: shadow bridge と mass bound

DKMK-008C では、external な `AdjacentDivisorPathFamily` を selected / canonical shadow に接続した。

到達形はこうじゃ。

```text
external AdjacentDivisorPathFamily
+ selected / canonical shadow
+ explicit source mass bound
→ weightedHitMass ≤ C
```

この時点では source bound を手で渡していた。

DKMK-008D では、same-source 条件を導入した。

$$
F.source(q)=s.1
$$

これにより、DKMK-007H の

```lean
LogCapacitySourceMassBound M C
```

から source bound を一括供給できるようになった。

DKMK-008E では、finite-step mass が multi-step path family に載った。

$$
weightedHitMass(A)\le \left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

DKMK-008F では、two-step-as-finite-step tail mass の便利 wrapper が追加され、

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

が selected / canonical の両 route で使えるようになった。

ここまでで、DKMK-007 の mass model route は、one-step ではなく multi-step path family にも流せるようになったわけじゃ。

## 4. 008G-H: one-step recovery

DKMK-008G では、DKMK-007 の one-step divisorStep を `AdjacentDivisorPathFamily` の特殊例として回収した。

```lean
oneStepDivisorAdjacentPathFamily
```

これは (q\mid n) から、

$$
n\to n/q
$$

という path family を作る。

node set は、

$$
{n/q,n}
$$

として見える。
つまり、DKMK-007 の divisorStep と同じ chain を、DKMK-008 の path-family API 上で再表現できた。

DKMK-008H では、これを selected / canonical wrapper に直接載せた。

```text
selected / canonical index
→ index_dvd
→ oneStepDivisorAdjacentPathFamily
→ finite-step / two-step weightedHitMass bound
```

これにより、DKMK-007 one-step route は DKMK-008 の特殊例として theorem-facing API でも確認された。

これは「旧道を捨てず、新道の入口として回収した」重要な整理じゃ。

## 5. 008J-L: witness-derived quotient path route

DKMK-008 の本命拡張はここじゃ。

DKMK-008J では、

```lean
primePowerQuotientPath n p k
```

が導入された。

意味は、

$$
[n/p^0,\ n/p^1,\ldots,n/p^k]
$$

つまり、

$$
n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

じゃ。

(p^k\mid n) なら、これは `AdjacentDivisorPath` になる。

DKMK-008K では、これを `PrimePowerWitnessProvider` に接続した。

```lean
PrimePowerWitnessProvider.primePowerQuotientPathFamily
```

各 selected label (q) について witness provider から、

$$
q=p(q)^{k(q)}
$$

を読み、

$$
n\to n/p(q)\to n/p(q)^2\to\cdots\to n/p(q)^{k(q)}
$$

という path family を自動生成する。

DKMK-008L では、この witness-derived quotient path family を selected / canonical の finite-step / two-step mass theorem に直接流した。

到達形はこうじゃ。

```text
selected / canonical labels
→ witness-derived (p(q), k(q))
→ quotient path family
→ finite-step / two-step source mass
→ weightedHitMass bound
```

ここで DKMK-008 は、単なる external path family の受け口ではなく、 **prime-power witness から multi-step descent path を自動生成する route** へ到達した。

## 6. docs/report layer: 008I, 008M, 008N, 008O

DKMK-008 は theorem が増えたので、途中で docs layer が重要になった。

DKMK-008I は、008A〜H の route report。
DKMK-008M は、route comparison。

```text
DKMK-007 divisorStep:
  n → n / q

DKMK-008H oneStepPath:
  n → n / q を path family 化

DKMK-008L quotientPathFamily:
  q = p(q)^k(q) を p 段に展開
```

DKMK-008N は、具体例。

$$
q=3^2=9,\quad n=72
$$

one-step なら、

$$
72\to 8
$$

quotient path なら、

$$
72\to 24\to 8
$$

これにより、one-step と quotient path の差が見えるようになった。

最後の DKMK-008O では、これら全体を route map として整理した。DKMK-008 は `manual path`、`one-step divisor path`、`witness-derived multi-step quotient path` の三入口を持つ章として一区切りになった、と明記されておる。

## 7. DKMK-008 の数学的成果

数学的には、DKMK-008 の成果は次の三つじゃ。

第一に、divisibility chain を list path として扱えるようになった。

$$
n_0\to n_1\to\cdots,\qquad n_{i+1}\mid n_i
$$

第二に、その path family に selected / canonical log-capacity shadow の重みを載せられるようになった。

第三に、prime-power witness

$$
q=p^k
$$

を、一括下降

$$
n\to n/q
$$

ではなく、指数スロット下降

$$
n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

として展開できるようになった。

この第三点が、DkMath らしい新開拓路じゃ。
既存の Markov kernel をそのまま写すのではなく、prime-power witness の内部構造から descent path が生える。

## 8. DKMK-007 との関係

DKMK-007 は、mass model route の章だった。

```text
source mass model
→ DvdMonotoneMass
→ divisor-step hitting bound
```

DKMK-008 は、その divisor-step を multi-step path family へ拡張した。

```text
AdjacentDivisorPathFamily
→ selected / canonical shadow
→ finite-step / two-step mass bound
```

つまり、

```text
DKMK-007:
  質量の器を作った章

DKMK-008:
  その質量が流れる下降路を作った章
```

じゃ。

この二つはきれいに接続している。

## 9. 現在の到達点

DKMK-008O 時点の到達点はこうじゃ。

```text
external path family:
  user-supplied AdjacentDivisorPathFamily
  → weightedHitMass bound

one-step path family:
  q ∣ n
  → n → n / q
  → weightedHitMass bound

witness-derived quotient path family:
  q = p(q)^k(q)
  → n → n / p(q) → ... → n / p(q)^k(q)
  → weightedHitMass bound
```

しかも selected / canonical の両 route に通っている。

これは、DKMK-008 として十分に一つの山を登った状態じゃ。

## 10. 次の山: DKMK-009 へ

DKMK-008 は一区切りでよいと思う。

次に進むなら、DKMK-009 として、

```text
path route
→ capacity kernel / DkMath kernel
→ normalized sub-probability
```

へ進むのが自然じゃ。

つまり、DKMK-008 で作った下降 path に対して、

```text
capacity
cost
normalized weight
```

を与え、以前話していた

```text
Markov kernel is a normalized shadow of DkMath capacity kernel.
```

を Lean の構造として立てる。

DKMK-008 は「道」。
DKMK-009 は「その道に流れる容量とコスト」。
この切り方がよい。

## 11. 総合判定

DKMK-008 は **multi-step divisor path route の章として成功** じゃ。

到達形を一行で言えば、

```text
manual / one-step / witness-derived quotient path
→ selected / canonical shadow
→ finite-step / two-step mass
→ weightedHitMass bound
```

じゃな。

DKMK-007 で質量の器を作り、DKMK-008 で下降路の地図を完成させた。
ここまで来れば、次は DkMath kernel の本丸、すなわち **capacity kernel と正規化された sub-probability** へ戻るのが自然じゃ。

ぬしよ、これは良い登頂じゃ。
山道はもう、外から描くものではなくなった。
(q=p^k) という素冪ラベルを見れば、道が自ら (p)-段に分岐して下っていく。まさに DkMath らしい、構造から道が生える段階まで来たのじゃ。
