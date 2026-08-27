# FLT7-FUSION-004B-N2 review

はい。**予定どおりです。いまが U モードの発射点です。** 😏👍️

N2 は単なる準備作業ではなく、こちらが ROADMAP で要求した「Ultra が迷わず掘り始められる発射台」を正確に完成させています。

PR #74 の最新 head は報告どおり `53dea79086b7bd1a861df9fbc2e8adc901a995e5`、Draft / open / mergeable です。

## 1. N2 は完全に予定どおり

想定していた N2 は、

```text
real-cubic global load factorization
  ↓
degree-six へ map
  ↓
各 real prime power を P / Pbar の pair power に展開
  ↓
finite global oriented factorization packet
```

でした。

実際に得た中心定理は、

```text
map(realKernel^e)
  =
orientedKernel^e * conjugateKernel^e
```

そして有限 support 全体で、

```text
globalDegreeSixOrientedFactorIdeal
  =
span(ofReal load)
```

です。

さらに異なる rational prime に属する pair power の comaximality まで保持されています。これは U1 の開始時に必要な「support・指数・prime address を失わない大域 packet」そのものです。実装差分でも、専用モジュール `SevenRamifiedFusionDegreeSixOrientedLoadFactorization.lean` と canonical packet が追加されています。

## 2. N2 は暴走していない

ここが非常に良い。

Codex は、

* oriented linear carrier の個別 valuation ownership
* element-level extraction
* full ring of integers
* PID
* additive chart
* strict decrease

へ勝手に進んでいません。

つまり、

```text
N2:
  pair-symmetric global ideal factorization
```

で正確に止まっています。

これは実行契約どおりです。

## 3. 本物の未知領域が露出した

現在わかっているのは、

```text
embedded real load ideal
  =
∏q (Pq^eq * Pbarq^eq)
```

です。

しかし、まだわからないのは、

```text
R - zeta L
```

が $P_q$ 側に何乗入り、

```text
R - zetaInv L
```

が $\overline P_q$ 側に何乗入るか、という**orientation ownership**です。

いまの factorization は共役 pair の積としては完全ですが、左右をまだ区別していません。

すなわち、次の敵は、

```text
unordered pair data
  ↓
oriented individual valuation
```

という**対称性の破れ**です。

前回の大躍進でも、

```text
unordered real-pair core
  ↓
degree-six orientation
```

が突破点でした。

今度はその orientation を、局所 kernel から大域 ideal valuation へ伝える段階です。

これはまさに Ultra を使う価値のある未知領域です。

## 4. U1.1 の coherence audit は発射前作業ではない

報告には、

```text
Galois rotation と quadratic conjugation の
大域的 coherence の追加確認
```

が残っています。

これは「Normal をもう一回挟むべき」という意味ではありません。

ROADMAP では最初から、

```text
U1.1
  global coherence audit
```

を Ultra の最初の Event として置いています。

したがって順序は、

```text
ULTRA / U1

U1.1
  address / Galois / conjugation coherence audit

U1.2
  oriented carrier valuation ownership
```

で正しい。

ここで通常 checkpoint を追加すると、Ultra が本来行う reconnaissance を細切れにしてしまいます。

## 5. 発射条件はすべて満たされた

Ultra 発動前に必要だった条件を確認すると、

| 発射条件                                      | 状態            |
| ----------------------------------------- | ------------- |
| exact local fibre equality                | 完了            |
| canonical oriented/conjugate primes       | 完了            |
| prime-power exponents preserved           | 完了            |
| finite global support                     | 完了            |
| global oriented pair product              | 完了            |
| distinct support の comaximality           | 完了            |
| principal embedded load ideal との equality | 完了            |
| actual carrier ownership                  | 未解決・Ultra の標的 |

完璧です。

「必要な道具が足りない」のではなく、

> **必要な道具が揃い、次に何が必要かがまだ分からない状態**

です。

これこそ Ultra 向きです。

## 6. U1 で最初に見るべき式

Ultra はまず、各 canonical address で、

```text
oriented carrier ∈ P
oriented carrier ∉ Pbar

conjugate carrier ∈ Pbar
conjugate carrier ∉ P
```

という既存の局所分離を、ideal multiplicity へ強化する必要があります。

単なる membership ではなく、

```text
v_P(R - zeta L)
v_Pbar(R - zeta L)

v_P(R - zetaInv L)
v_Pbar(R - zetaInv L)
```

を固定する。

理想形は、

```text
v_P(oriented carrier) = e
v_Pbar(oriented carrier) = 0

v_P(conjugate carrier) = 0
v_Pbar(conjugate carrier) = e
```

に相当する theorem です。

ただし、この指数 $e$ がそのまま cell exponent になるのか、carrier 側に別の residual seventh-power exponent が加わるのかは探索対象です。

ここを事前に決め打ちしないことが重要です。

## 7. Ultra が発見すべき分岐

U1.2 以降は、次のどれかになるでしょう。

### Outcome A

個別 valuation が完全に決まり、

```text
span(oriented carrier)
  =
oriented load factor * seventh-power ideal
```

が得られる。

これは最良の道です。

### Outcome B

ideal-level の七乗 residual は得られるが、元の七乗へ戻すため、

```text
class group
unit class
principal generator
```

のどれかが必要になる。

これも価値ある発見です。

### Outcome C

現在の quadratic carrier だけでは不足し、

```text
full cyclotomic integer ring
```

との同一視が必要になる。

これも exact obstruction として重要です。

### Outcome D

local ownership は取れるが、Galois / conjugation coherence が global chart を阻止する。

これも次の正しい問題設定になります。

つまり、どの outcome でも Ultra の成果になります。

## 8. 唯一の待機条件

最新 head に対する GitHub Lean CI は、現在まだ `in_progress` です。

ローカル全体 build は成功しているので数学的な発射判断は Go ですが、運用上は **CI が green になった直後に発動**が最もきれいです。

## Go サイン

CI 成功確認後、selector を次に変更してよいです。

```text
EXECUTION_MODE = ULTRA
ACTIVE_PHASE   = U1
STATUS         = ACTIVE
```

開始 commit は、

```text
53dea79086b7bd1a861df9fbc2e8adc901a995e5
```

です。

そして指示は、

```text
Begin with U1.1 coherence audit.
Proceed adaptively through U1.2 and later events.
Do not stop merely because the initially predicted route fails.
At every completed mathematical event:
- build,
- commit,
- write an exact boundary report,
- preserve all prior orientation and provenance data.
```

でよい。

**空気は整いました。**

前回は二セルの壁の向こうに degree-six 世界がありました。

今回は、

```text
pair-symmetric ideal factorization
```

の向こうに、

```text
oriented element-level reconstruction
```

があります。

ここから先は通常作業で一本道を指定するより、Ultra に地下道を探させる局面です。

🐺🧙‍♀️✨ **ULTRA / U1、発動可。**
