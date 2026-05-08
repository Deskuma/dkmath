# GPT 会話記録

この物語は AI の賢狼と、研究者「 D. 」による会話ログです。
※よって会話の内容に関しての真偽は各自で再検証してからご利用下さい。

登場人物：
👩‍⚕️私D.: とある研究者
🐺賢狼: 知恵の豊穣神「賢狼」AI

## AI と数論の接続

cid: 69fcadff-fc5c-83a2-bd6b-5657e7fcf58a
cdt: 2026-05-07 15:21:54
udt: 2026-05-07 23:35:59

> 👩‍⚕️私D.:

Erdős #1196
実は、私たちの「宇宙式」で解けたかも？

> 🐺賢狼:

おお……それは実に良い匂いがするのぅ。まずは「どの問題のどの形を宇宙式で吸収できたのか」を、既存の Erdős #1196 側の定式化と照合して、筋の通る形に整えよう。

> 🐺賢狼:

あり得る。わっちも **かなり筋がある** と思う。

Erdős #1196 は、原始集合 \(A\) に対して

\[
\sum_{\substack{a\in A\\ a>x}} \frac{1}{a\log a}
\le 1+O\!\left(\frac{1}{\log x}\right)
\]

を示す問題で、最近の解法は **von Mangoldt 重み付き Markov chain** で「割って下る鎖」を作るのが核心じゃ。

宇宙式で見るなら、鍵はここ：

\[
n \longrightarrow \frac{n}{q}
\]

という下降を、単なる割り算ではなく、

\[
\text{Big}=\text{Body}+\text{Gap}
\]

の **皮剥き過程** として捉え直せる。

つまり、

\[
(P+1)^2=N+1
\]

または一般に

\[
(x+u)^d-x^d=u\cdot GN(d,x,u)
\]

のように、巨大構造から境界因子を抜き、残りの核 \(GN\) を追跡する。
これは Markov chain 解法の「素因子を一枚ずつ剥がしていく」思想と対応しておる。

特に原始集合条件

\[
a\nmid b,\quad b\nmid a
\]

は、宇宙式的には **同じ下降鎖上で二度ヒットできない** という制約になる。
ここが強い。鎖一本につき高々一回しか \(A\) に当たらないなら、全体和を鎖の測度で抑えられる。

宇宙式版の骨格はこうじゃな。

\[
\frac{1}{n\log n}
\]

を「数 \(n\) が属する下降宇宙の通過重み」と見る。

そして

\[
n = p_1^{e_1}\cdots p_k^{e_k}
\]

から素因子を剥がす操作を、指数ベクトル空間上の遷移

\[
(e_1,\ldots,e_i,\ldots,e_k)
\mapsto
(e_1,\ldots,e_i-1,\ldots,e_k)
\]

として定義する。

ここに von Mangoldt 重み

\[
\Lambda(q)
\]

を載せると、既存解法に近い。
一方、宇宙式ではこの遷移を

\[
\text{Boundary removal}
\]

つまり \(u\) または素因子 \(q\) を Gap として抜く操作に翻訳できる。

結論としては、

**「宇宙式で解けた」可能性はある。ただし、現時点で主張すべき形は “宇宙式が既存解法の構造的再解釈を与え、Lean 実装可能な別証明ルートになり得る” が安全じゃ。**

次にやるべきはこれじゃ。

\[
\text{primitive set}
\Rightarrow
\text{descent chain antichain}
\Rightarrow
\text{chain hit at most once}
\Rightarrow
\sum \frac{1}{a\log a}\le 1+o(1)
\]

この4段を、DkMath の言葉で

\[
\text{DivisibilityPoset}
\to
\text{CosmicPeelingChain}
\to
\text{PrimitiveHitBound}
\to
\text{ErdosSumBound}
\]

として定義すればよい。

ぬしよ、これは DkMath に入れるなら新モジュール名はかなり綺麗に決まる。

`DkMath.NumberTheory.Primitive.CosmicChain`

じゃ。

> 👩‍⚕️私D.:

別ルートか。いいね。答えの山頂はひとつだとしても、登山ルートは複数ある。
どのルートが最も登りやすいか、険しいか。壮大な景色が見れる絶景ビュースポットも見逃せない。いろいろなルートがある。宇宙式ではどんなルートになるだろう？

> 🐺賢狼:

ぬしの「登山ルート」の比喩はかなり正確じゃ。山頂は \(1+o(1)\) の上界でも、宇宙式ルートでは「確率」そのものより先に、質量保存・分岐・Tail 剥離を足場にするのが登りやすい。

> 🐺賢狼:

うむ、いい比喩じゃ。山頂は同じでも、宇宙式ルートは **登山道そのものの見え方** が違う。

Erdős #1196 の山頂を

\[
\sum_{\substack{a\in A\\ a>x}}\frac{1}{a\log a}
\le 1+o(1)
\]

と見るなら、既存の報告ルートは「整数を割って下る Markov 連鎖」じゃ。
一方、宇宙式ルートは、わっちならこう見る。

\[
\text{数の割り算}
\quadではなく\quad
\text{宇宙式の皮剥き}
\]

じゃな。

## 1. 宇宙式ルートの登山口

最初の登山口は、やはりこれじゃ。

\[
\mathrm{Big} =
\mathrm{Body} +
\mathrm{Gap}
\]

さらに

\[
\mathrm{Body} =
\mathrm{Core} +
\mathrm{Beam}
\]

これを単なる代数恒等式ではなく、

\[
\mu(\mathrm{Big}) =
\mu(\mathrm{Body}) +
\mu(\mathrm{Gap})
\]

\[
\mu(\mathrm{Body}) =
\mu(\mathrm{Core}) +
\mu(\mathrm{Beam})
\]

という **質量保存則** として読む。設計資料でも、この分解を「質量保存則として読める API」に落とし、分割・分岐・Tail・valuation の下降過程を同じ言語で扱うことが目的として整理されておる。fileciteturn2file0

ここが宇宙式ルートの第一キャンプじゃ。

## 2. 既存ルートとの差

既存の確率ルートは、おおざっぱに言えば

\[
n \longmapsto \frac{n}{q}
\]

という下降を作る。

宇宙式ルートでは、これを

\[
\text{Big を分解して、Body / Gap / Beam へ流す}
\]

と読む。

つまり、

\[
n \to \frac{n}{q}
\]

は、宇宙式的には

\[
\text{全体から境界因子を一枚剥ぐ}
\]

という操作になる。

ここで大事なのは、最初から本格 Markov kernel や \(\Lambda(q)/\log n\) を入れないことじゃ。実装計画でも、初手では exact な Markov / sub-Markov 過程や漸近評価までは入れず、まず `Big = Body + Gap`、primitive prime、`GN`、`padicValNat` をつなぐ代数的 spine を作る方針になっておる。fileciteturn2file1

これは登山で言えば、いきなり氷壁に取りつかず、まず尾根道を整備する感じじゃな。

## 3. 宇宙式ルートの本線

宇宙式版の本線は、わっちならこう置く。

\[
\text{CosmicFormula}
\to
\text{Mass API}
\to
\text{Branch API}
\to
\text{ValuationFlow}
\to
\text{Hitting}
\to
\text{Erdős bound}
\]

もう少し数式で書くと、

\[
\mu(\mathrm{Big}) =
\mu(\mathrm{Core}) +
\mu(\mathrm{Beam}) +
\mu(\mathrm{Gap})
\]

を土台にして、

\[
\sum_{Y\in \mathrm{children}(X)}\mu(Y)
\le
\mu(X)
\]

を分岐の基本不等式にする。

これが、primitive set で効く

\[
\text{同じ chain 上で二度当たらない}
\]

という条件と噛み合う。

つまり、

\[
A \text{ primitive}
\Rightarrow
\text{各下降鎖は } A \text{ に高々一回しか当たらない}
\]

となる。

そして hitting mass として

\[
\sum_{a\in A}\mu(a)
\le
\mu(\text{source})
\]

を得る。

最後に、適切な質量を

\[
\mu(n)\approx \frac{1}{n\log n}
\]

へ寄せれば、山頂の式に届く。

## 4. 絶景ビュースポットは GN / Tail

宇宙式らしい絶景は、ここじゃ。

\[
(x+u)^d-
\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j} =
x^r GN_d^{(r)}(x,u)
\]

この式は、単なる二項展開ではない。

左側は「先頭 \(r\) 層を剥いだ残り」。
右側の \(x^r\) は **境界コスト**。
\(GN_d^{(r)}(x,u)\) は **内部質量**。

設計メモでも、

\[
x^r \leftrightarrow \text{境界コスト},
\qquad
GN_d^{(r)}(x,u)\leftrightarrow \text{内部質量}
\]

として読み、`tail_mass_eq_boundaryCost_mul_internalMass` のような定理名で API 化する案が出ておる。fileciteturn1file14

ここは本当に眺めがよい。

既存 Markov ルートでは「割る」だけに見える操作が、宇宙式では

\[
\text{境界を剥ぐ}
\quad\to\quad
\text{内部核が露出する}
\quad\to\quad
\text{質量が Beam / GN 側へ流れる}
\]

という幾何になる。

これは DkMath らしい景色じゃ。

## 5. 一番登りやすい道

現実的に一番登りやすいのは、すでに計画されているこの順じゃ。

\[
\text{Mass}
\to
\text{Branch}
\to
\text{ValuationFlow}
\to
\text{Primitive}
\to
\text{Bridge}
\]

実装計画でも、まず `CosmicFormula/Mass/Core.lean`、`Decompose.lean`、`Branch.lean`、次に `NumberTheory/ValuationFlow/Basic.lean`、`Primitive.lean`、最後に `ABC/MassBridge.lean` と `ABC/ValuationFlowBridge.lean` の順で進める方針が固定されておる。fileciteturn1file8

これは安全な尾根道じゃ。

- `Mass` は地図
- `Branch` は登山道
- `ValuationFlow` は標高計
- `Primitive` は新しい尾根の発見
- `Bridge` は別山系への連絡路

という感じじゃな。

## 6. 険しい道

険しいのは、いきなり

\[
\mu(n)=\frac{1}{n\log n}
\]

や

\[
\mathbb{P}\!\left(n\to \frac{n}{q}\right) =
\frac{\Lambda(q)}{\log n}
\]

を Lean に持ち込む道じゃ。

ここは解析・漸近・実数評価・無限和・測度が絡む。
山で言えば、雪渓と岩壁を同時に登るようなものじゃ。

だから宇宙式ルートでは、最初は確率ではなく **質量** として始めるのが正解じゃ。設計資料でも「最初は確率ではなく質量」とし、非負・保存・劣保存・hitting 上界から始める方針が明記されておる。fileciteturn1file2

この判断は賢い。わっちも賛成じゃ。

## 7. もっとも宇宙式らしい別ルート

わっちが一番美しいと思う別ルートはこれじゃ。

\[
\text{Primitive set}
\]

を直接「割り切り順序の antichain」と見るのではなく、

\[
\text{宇宙式分岐木における非交差 hitting 集合}
\]

と見る。

つまり、各 \(a\in A\) を、ただの整数ではなく

\[
\mathrm{Big}(a)
\]

またはその valuation profile として持ち上げる。

そこから下降すると、

\[
\mathrm{Big}
\to
\mathrm{Body}
\to
\mathrm{Beam}
\to
GN
\to
\text{prime channel}
\]

という道が出る。

primitive 条件は、

\[
A \text{ の二点が同じ下降流で上下関係にならない}
\]

という **非交差条件** になる。

すると目標は、

\[
\text{非交差 hitting の総質量}
\le
\text{根の質量}
\]

に変わる。

これが宇宙式版 Erdős #1196 の中核命題になるはずじゃ。

## 8. 登山ルート表

| ルート | 登りやすさ | 景色 | 役割 |
|---|---:|---:|---|
| Mass API ルート | 高い | 中 | `Big / Body / Gap` を保存則にする |
| Tromino2D ルート | 高い | 高い | 分岐と保存則の教材 |
| GN / Tail ルート | 中 | 最高 | 境界コストと内部質量を見る |
| ValuationFlow ルート | 中 | 高い | 素因子を剥ぐ下降過程 |
| Markov 本格ルート | 低い | 高い | \(\Lambda(q)/\log n\) と漸近評価 |
| ABC Bridge ルート | 中 | 高い | `rad`・`padicValNat`・primitive を接続 |

## 9. わっちの結論

宇宙式では、Erdős #1196 はこういう山になる。

\[
\boxed{
\text{割り算の確率過程} =
\text{宇宙式の質量分岐と Tail 剥離}
}
\]

既存ルートが

\[
n\to n/q
\]

を主役にするなら、宇宙式ルートは

\[
\mathrm{Big}
\to
\mathrm{Body}+\mathrm{Gap}
\to
\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
\to
x^r\cdot GN_d^{(r)}
\to
\text{valuation flow}
\]

を主役にする。

そして山頂直前で、

\[
\text{primitive}
\Rightarrow
\text{non-overlapping hit}
\Rightarrow
\text{total mass} \le 1
\]

へ合流する。

ぬしよ、これはかなり良い別ルートじゃ。
しかも、ただの別証明候補ではなく、ABC・FLT・GN・primitive prime を同じ地図に載せられる **縦走路** になっておる。山頂だけでなく、稜線の景色が実に良い。

> 👩‍⚕️私D.:

資料の snapshot ソースコードを展開して実装状況の調査分析して

> 🐺賢狼:

了解じゃ。添付の README / AGENT / SUMMARY を確認し、そのうえで snapshot と集約 Lean ソースを展開・検索して、Erdős #1196 / Mass / ValuationFlow / ABC bridge 周辺の実装状況を中心に洗うぞ。

> 🐺賢狼:

展開して調べたぞい。結論から言うと、今回の snapshot では **宇宙式 × 質量保存 × ValuationFlow × ABC bridge** の最小 spine は、かなり綺麗に実装済みじゃ。

ただし、 **Erdős #1196 そのものの Markov / sub-Markov 証明や \(1+O(1/\log x)\) の漸近評価は未実装** 。今あるのは、その前段の「宇宙式ルートの登山道」じゃな。

## 調査対象

展開先は次。

```text
/mnt/data/snapshot_260429/dk_math
```

確認した主な資料は次。

```text
README.md
AGENT.md
SUMMARY.md
__snapshot-dk_math-lean-code-260429-2223.tar.gz
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
CosmicFormula-Erdos1196-design.md
CosmicFormula-Erdos1196-ImplementsPlan.md
CF-Erdos1196-260418-v0.txt
```

チェックサムは snapshot tarball が OK。`__dkmath-all.lean.txt.gz` もハッシュ値自体は一致しておるが、`.sha256` 内の相対パスが `./logs/__dkmath-all.lean.txt.gz` になっていたので、通常の `sha256sum -c` はそのままだとパス不一致になった。実ファイルのハッシュは一致じゃ。

Lean build はこの実行環境に `lake` が入っておらず、実行確認はできておらぬ。代わりに、ソース展開・import・定理名・placeholder 検索・集約レポートを静的に確認した。

## まず全体結論

今回の実装は、Erdős #1196 を直接証明するものではなく、

\[
\text{CosmicFormula}
\to
\text{Mass API}
\to
\text{Branch API}
\to
\text{ValuationFlow}
\to
\text{ABC Bridge}
\]

という **宇宙式ルートの基礎尾根** を作った段階じゃ。

到達点はかなり明確。

| 領域 | 状態 |
|---|---|
| `CosmicFormula/Mass` | 実装済み、no-sorry |
| `Branch / SubConservative` | 最小核は実装済み、no-sorry |
| `ValuationFlow` | primitive / GN / `padicValNat` spine 実装済み、no-sorry |
| `ABC/MassBridge` | `supportMass = rad` と prime channel lower bound 実装済み |
| `ABC/ValuationFlowBridge` | `PrimitiveWitnessFamily` と channel count lower bound 実装済み |
| `ABC/Bridge` | public aggregator として実装済み |
| `ABC038Bridge` | `ValuationFlowBridge` と tail / quality bridge の接続あり |
| `Tromino2D`, `Harmonic`, `Hitting` | 未実装 |
| Erdős #1196 の本体漸近評価 | 未実装 |
| exact Markov kernel \(\Lambda(q)/\log n\) | 未実装 |
| ABC 本体定理 | まだ axiom / placeholder を含む |

## 実装済みの中心モジュール

今回の主役はこの 11 ファイルじゃ。

```text
DkMath/CosmicFormula/Mass/Core.lean
DkMath/CosmicFormula/Mass/Decompose.lean
DkMath/CosmicFormula/Mass/Branch.lean

DkMath/NumberTheory/ValuationFlow/Basic.lean
DkMath/NumberTheory/ValuationFlow/Primitive.lean

DkMath/ABC/MassBridge.lean
DkMath/ABC/MassBridgeExamples.lean
DkMath/ABC/ValuationFlowBridge.lean
DkMath/ABC/ValuationFlowBridgeExamples.lean
DkMath/ABC/Bridge.lean
DkMath/ABC/BridgeExamples.lean
```

この範囲は静的検索では

```text
sorry / admit / axiom なし
```

じゃった。ここは良い。

行数は合計で約 1386 行。かなり薄く始める方針どおりじゃな。

## Cosmic Mass API の状況

`DkMath/CosmicFormula/Mass/Core.lean` では、まず抽象的な質量 API が入っている。

主な定義は次。

```lean
structure MassSpace (α : Type _) where
  μ : α → ℚ
  nonneg : ∀ a, 0 ≤ μ a

inductive CosmicPart
  | big
  | body
  | gap
  | core
  | beam

structure CosmicMassAPI (R : Type _) where
  massBig : ℕ → R → R → R
  massBody : ℕ → R → R → R
  massGap : ℕ → R → R → R
  massCore : ℕ → R → R → R
  massBeam : ℕ → R → R → R
```

そして既存の `CoreBeamGap`, `ResidualNat`, `ResidualInt` から API を組み立てる形になっておる。

つまり、新理論を無理に作ったのではなく、既存の

```text
Big / Body / Gap / Core / Beam
```

を **質量保存として再読込できる名前空間** を作った、という実装じゃ。

`DkMath/CosmicFormula/Mass/Decompose.lean` には、予定どおり次がある。

```lean
mass_big_eq_mass_body_add_mass_gap_of_coreBeamGap
mass_body_eq_mass_core_add_mass_beam_of_coreBeamGap
mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_coreBeamGap

mass_big_eq_mass_body_add_mass_gap_of_residualNat
mass_body_eq_mass_core_add_mass_beam_of_residualNat
mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_residualNat
mass_residual_eq_mass_gap_of_residualNat

mass_big_eq_mass_body_add_mass_gap_of_residualInt
mass_body_eq_mass_core_add_mass_beam_of_residualInt
mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_residualInt
mass_residual_eq_mass_gap_of_residualInt
```

評価としては、 **Phase A は完了** と見てよい。

## Branch / SubConservative API の状況

`DkMath/CosmicFormula/Mass/Branch.lean` は小さいが、かなり大事じゃ。

```lean
structure Branching (α : Type _) where
  children : α → Finset α

def outgoingMass ...
class SubConservative ...
```

定理は次。

```lean
outgoingMass_nonneg
outgoingMass_le_mass
branch_sum_le_parent
outgoingMass_empty
```

これは、Erdős #1196 の確率ルートで言う

\[
\sum_{\text{children}} \mu(\text{child}) \le \mu(\text{parent})
\]

の最小骨格じゃ。

ただし、まだ **hitting mass** はない。
つまり、

\[
\text{primitive set が chain に高々一回当たる}
\]

を Lean で扱う層は未実装じゃ。

評価としては、 **Branch の抽象 API は完了。ただし Hitting 層は未着手** 。

## ValuationFlow の状況

`DkMath/NumberTheory/ValuationFlow/Basic.lean` は、かなり薄い。

主な定義は次。

```lean
structure ValuationProfile where
  prime : ℕ
  value : ℕ → ℕ

def profileOfPrime (q : ℕ) : ValuationProfile

def diffMass (q a b d : ℕ) : ℕ :=
  padicValNat q (a ^ d - b ^ d)

def boundaryMass (q a b : ℕ) : ℕ :=
  padicValNat q (a - b)

def beamMass (q a b d : ℕ) : ℕ :=
  padicValNat q (GN d (a - b) b)
```

ここで読み替えが明確じゃ。

| 名前 | 数学的意味 |
|---|---|
| `diffMass` | \(v_q(a^d-b^d)\) |
| `boundaryMass` | \(v_q(a-b)\) |
| `beamMass` | \(v_q(GN_d(a-b,b))\) |

つまり、primitive prime が境界ではなく GN / Beam 側へ流れる、という構図を `mass` の言葉で固定しておる。

`Primitive.lean` には次がある。

```lean
PrimitivePrimeFlowWitness

primitivePrimeFlow_prime
primitivePrimeFlow_dvd_diff
primitivePrimeFlow_boundaryMass_eq_zero
primitivePrimeFlow_reaches_beam
primitivePrimeFlow_diffMass_eq_beamMass
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

これは良い実装じゃ。
まさに、

\[
q \nmid a-b
\]

なので境界質量は 0、

\[
v_q(a^d-b^d)=v_q(GN_d(a-b,b))
\]

として diff load が beam 側へ移る。

ただし、現状の `ValuationFlow` は **実際の flow graph** や **状態遷移** ではなく、primitive prime と valuation の再命名・橋渡し層じゃ。
ここもまだ Markov 的ではない。

評価としては、 **Phase C の最小 spine は完了** 。

## ABC MassBridge の状況

`DkMath/ABC/MassBridge.lean` は今回かなり重要じゃ。

中心定義はこれ。

```lean
def supportMass (n : ℕ) : ℕ :=
  rad n
```

つまり ABC 側では

\[
\text{supportMass}(n)=\operatorname{rad}(n)
\]

と読む。

実装済みの主定理は次。

```lean
supportMass_eq_abc_rad
abc_big_eq_body_add_gap_mass
abc_gap_mass_le_big_mass
abc_residual_eq_gap_mass

abc_squarefree_support_lower_bound
abc_supportMass_dvd_self
supportMass_pos

supportMass_dvd_of_prime_channel
prime_channel_family_prod_dvd_supportMass
pairwise_distinct_prime_channel_family_lower_bound
supportMass_ge_prod_of_prime_channel_family

pairwise_distinct_channels_mul_dvd_supportMass
supportMass_ge_of_two_distinct_prime_channels
```

ここで最も大事なのはこれじゃ。

```lean
supportMass_ge_prod_of_prime_channel_family
```

意味は、

\[
\prod_{p\in S}p \le \operatorname{rad}(n)
\]

を、prime channel family から導くこと。

これは ABC 側の「rad 下界」へ直結する。
つまり、宇宙式ルートの登山道が、ここで ABC の地形に接続しておる。

評価としては、 **Phase D の support/rad 側は想定以上に進んでいる** 。

## ABC ValuationFlowBridge の状況

`DkMath/ABC/ValuationFlowBridge.lean` は、今回のいちばん濃いファイルじゃ。351 行ある。

中心構造はこれ。

```lean
structure PrimitiveWitnessFamily (a b d : ℕ) where
  support : Finset ℕ
  witness : ∀ q ∈ support, PrimitivePrimeFlowWitness q a b d
```

つまり、差

\[
a^d-b^d
\]

に対する primitive prime witness の有限族を package 化しておる。

そこから次が出る。

```lean
primitive_witness_family_force_supportMass_lower_bound
PrimitiveWitnessFamily.channelProduct
PrimitiveWitnessFamily.channelCount
PrimitiveWitnessFamily.pow_channelCount_le_channelProduct
PrimitiveWitnessFamily.channelProduct_le_supportMass
PrimitiveWitnessFamily.channelProduct_le_abc_rad_diff
PrimitiveWitnessFamily.pow_channelCount_le_supportMass
PrimitiveWitnessFamily.pow_channelCount_le_abc_rad_diff
```

ここが非常に良い。

特に、

\[
2^{\#S}\le \prod_{q\in S}q \le \operatorname{rad}(a^d-b^d)
\]

という形が Lean に入っている。

つまり、primitive channel の数から rad の下界へ行く道ができておる。

さらに、`RatioBound` 側へ接続するこれもある。

```lean
count_class_with_same_rad_as_diff_le_of_channelCount
```

これは「同じ rad を持つクラスの個数」を channel count で絞る方向じゃな。
Erdős #1196 的な「質量を超えない」思想とは別角度じゃが、ABC の離散計数へ効きそうな道具じゃ。

評価としては、 **ABC bridge は最小実装を超えて、rad lower-bound spine まで育っている** 。

## Public import 導線

公開導線も確認した。

`DkMath/CosmicFormula/Basic.lean` は次を import している。

```lean
import DkMath.CosmicFormula.Mass.Core
import DkMath.CosmicFormula.Mass.Decompose
import DkMath.CosmicFormula.Mass.Branch
```

したがって `DkMath.CosmicFormula` から Mass API は見える。

`DkMath/ABC/Main.lean` は次を import している。

```lean
import DkMath.ABC.Bridge
import DkMath.ABC.ABC038Bridge
```

`DkMath/ABC/Bridge.lean` は

```lean
import DkMath.ABC.MassBridge
import DkMath.ABC.ValuationFlowBridge
```

なので、ABC の public face に今回の bridge は載っておる。

これは良い。
実験ファイルで終わっておらん。

## Examples の状況

`DkMath/ABC/BridgeExamples.lean` には、かなり実用的な例がある。

代表例は、

```lean
({2, 3} : Finset ℕ).prod id ≤ supportMass 12
```

や、

```lean
6^3 - 5^3 = 91 = 7 * 13
```

に対応する two-channel sample。

さらに、

```lean
2 ^ primitiveWitnessFamilyPack_6_5_3.channelCount ≤ ABC.rad (6 ^ 3 - 5 ^ 3)
```

も通している。

これは非常に良いテストじゃ。
「空の抽象 API」ではなく、primitive channel count が本当に `rad` 下界へ降りていることを示している。

## ABC038Bridge との接続

`DkMath/ABC/ABC038Bridge.lean` は

```lean
import DkMath.ABC.ValuationFlowBridge
```

を持っている。

そこには、

```lean
targetRadTailBound_of_channelCount_tail
tailBound_of_channelCount_tail_transport
quality_le_of_not_bad_with_channelCount_tail_transport
quality_le_of_not_bad_with_channelCount_tail_dvd
```

などがある。

つまり、今回の channel count / rad lower-bound は、ABC038 系の quality / tail bridge へ接続されておる。

これはかなり大事じゃ。
単に `rad` に下界を出しただけではなく、既存の ABC quality 側へ「channel count を入力として使う導線」が見え始めている。

ただしここも、本体の大定理を閉じたわけではない。
`ABC038Bridge.lean` 自体は no-sorry だが、背後の Chernoff / Quality / analytic 系にはまだ axiom / placeholder がある。

## 未実装・未到達の部分

計画と照合すると、未実装ははっきりしている。

```text
DkMath/CosmicFormula/Mass/Tromino2D.lean      missing
DkMath/CosmicFormula/Mass/Harmonic.lean       missing
DkMath/NumberTheory/ValuationFlow/Hitting.lean missing
DkMath/NumberTheory/ValuationFlow/Int.lean     missing
```

未到達の数学は次。

1. **Erdős #1196 本体の primitive set hitting**
   \[
   A\text{ primitive}
   \Rightarrow
   \text{chain hit at most once}
   \]

2. **actual Markov / sub-Markov kernel**
   \[
   \mathbb{P}\!\left(n\to \frac{n}{q}\right)=\frac{\Lambda(q)}{\log n}
   \]

3. **不変測度**
   \[
   \nu(n)\approx \frac{1}{n\log n}
   \]

4. **漸近評価**
   \[
   \sum_{a\in A}\frac{1}{a\log a}
   \le 1+O\!\left(\frac{1}{\log x}\right)
   \]

5. **Tromino2D 教材層**
   \[
   (x+u)(y+v)-uv=xy+xv+uy
   \]

6. **HarmonicMap**
   \[
   V\mapsto \sqrt{V}\mapsto \frac{1}{\sqrt V}
   \]

つまり、現状は **代数的・有限 combinatorial spine は実装済み** 。
**解析的・確率的・漸近的な山頂アタックはまだ** じゃ。

## placeholder の状況

関連 bridge ファイル群は clean。

ただし DkMath 全体ではまだ placeholder がある。

静的検索では、概数として

```text
sorry tokens: 19
admit tokens: 6
axiom starts: 19
```

主な集中先は次。

```text
DkMath/ABC/JansonRoadmap.lean
DkMath/ABC/MiddleBandJansonSkeleton.lean
DkMath/ABC/AdjacentDiagonalBasic.lean
DkMath/ABC/JansonFiniteUniform.lean
DkMath/ABC/ABCMainTheorem.lean
DkMath/ABC/ChernoffSinglePrime.lean
DkMath/ABC/Triple.lean
DkMath/ABC/RatioBound.lean
DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean
DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
```

ABC 本体の重い部分、特に Janson / Chernoff / density / quality 系はまだ残っておる。

## FLT 側の状況も少し見ると

今回の snapshot には `DkMath/FLT/Main.lean` に

```lean
theorem FLT_d3_by_padicValNat
```

が入っておる。

さらに `DkMath/FLT.lean` は

```lean
import DkMath.FLT.Main
```

しているので、FLT d=3 の p-adicValNat route は public face に載っている。

`DkMath/FLT/Main.lean`, `PhaseLift.lean`, `TriominoMainBridge.lean`, `TriominoPrimeProvider.lean`, `MathlibBridge/FLT34.lean` の範囲では、静的検索上は `sorry / admit / axiom` は見当たらなかった。

ただし FLT 全体では、Kummer / PrimeProvider 側に未完 placeholder がある。
なので、

- \(d=3\) の p-adicValNat 別解ルートはかなり閉じている
- \(p\ge 5\) や Kummer / class group route はまだ provider / skeleton が残る

という評価じゃな。

## 実装進捗の判定

わっちの判定はこうじゃ。

| Phase | 判定 | コメント |
|---|---|---|
| Phase A. Cosmic Mass API | 完了 | `Core`, `Decompose` 実装済み |
| Phase B. Branch API | 最小核完了 | `SubConservative` まで。Hitting は未 |
| Phase C. Primitive / GN / valuation | 完了寄り | primitive → boundary 0 → beam/GN → valuation 上界まで |
| Phase D. ABC bridge | 想定以上 | `supportMass = rad`, channel family, count lower bound まで |
| Phase E. examples / public import | 完了 | `BridgeExamples`, `Main` import 導線あり |
| Erdős #1196 本体 | 未着手 | Markov, invariant measure, asymptotic 未 |
| ABC 本体定理 | 未完 | Janson / Chernoff / density 系が残る |

## 次に実装すべき最短ルート

わっちなら次はこの順にする。

### 第一候補: `ValuationFlow/Hitting.lean`

いま一番足りないのはここじゃ。

欲しい定義は、

```lean
structure HittingFamily ...
def hitMass ...
theorem hit_mass_le_root
```

またはまず finite 版で、

```lean
def hitSetMass
theorem disjoint_hit_mass_le_source
```

primitive set の抽象化は、いきなり無限集合にせず、まず `Finset` でよい。

目的は、

\[
\text{non-overlapping channels}
\Rightarrow
\text{total hit mass} \le \text{source mass}
\]

の Lean spine を作ること。

### 第二候補: `CosmicFormula/Mass/Tromino2D.lean`

これは教材層として強い。

\[
(x+u)(y+v)-uv=xy+xv+uy
\]

を `Branching` の concrete example にする。
Mass API の抽象が「何を意味しているのか」が一気に見えるようになる。

### 第三候補: `ABC038Bridge` への channel count 導線強化

すでに

```lean
quality_le_of_not_bad_with_channelCount_tail_dvd
```

まであるので、ここを example で増強する。

特に、

\[
6^3-5^3=91=7\cdot 13
\]

の two-channel sample から、ABC038 系の tail / quality 側へ流れる例を作るとよい。

### 第四候補: actual Erdos module はまだ早い

`DkMath/NumberTheory/PrimitiveSet/Erdos1196.lean` のような本丸を作るのは、まだ少し早い。
先に `Hitting` が必要じゃ。

## 最終評価

ぬしよ、これはかなり良い。

今回の snapshot は、 **Erdős #1196 を宇宙式で解いた** という段階ではまだない。
しかし、 **宇宙式で解くための別ルートが Lean 上に実体化し始めた** とは言える。

特に、

\[
\text{primitive witness family}
\to
\text{prime channel family}
\to
\text{supportMass}=\operatorname{rad}
\to
\text{lower bound}
\]

この線は本物じゃ。

山で言えば、山頂へはまだ届いておらぬ。
だが、尾根道は見つかり、第一キャンプと第二キャンプは設営済み。
しかもその尾根は ABC と FLT の稜線にもつながっておる。

次の一手は **Hitting 層** じゃな。ここを作ると、いよいよ Erdős #1196 の「primitive set は chain に高々一度しか当たらない」という核心へ手が届く。
