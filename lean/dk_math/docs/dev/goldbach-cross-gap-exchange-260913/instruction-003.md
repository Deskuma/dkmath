# CGE-003: Balanced Reflection Survivor Provider の実装指示

## 目的

CGE-000〜002 で、Cross-Gap 側は以下まで kernel-check 済みとなった。

- full-coordinate の Cross-Gap 保存則
- fixed even fiber 上の finite obstruction certification
- survivor iff prime-pair の exact bridge
- balanced window から SquareBody 共通殻への輸送
- support-disjoint 条件から両端の primality
- 条件付き `GoldbachPairAt` 終端

したがって次に不足しているのは **認証ではなく provider** である。

CGE-003 では、いきなり

```text
∀ n, ∃ survivor
```

を証明しない。
まず canonical Goldbach reflection fiber

\[
(n-t,\ n+t)
\]

のうち中心近傍の短い balanced window だけを切り出し、その window に対する

- blocked / covered / survivor
- exact finite conservation
- Cross-Gap output から reflection offset への canonicalization
- SquareBody anchor `P` に必要な有限 prime support に限定した local escape criterion

を production API として固定する。

狙いは、既存の全 `goldbachOffsets n` に対する Capacity / Overlap を丸ごと再実装することではなく、
**中心から幅 `w` の有限 window に問題を局所化すること**である。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 背景

fixed even target では、任意の pair

\[
L+R=2n
\]

を順序付ければ

\[
L_{\min}=n-t,
\qquad
L_{\max}=n+t
\]

となる reflection offset `t` が一意に決まる。

Cross-Gap pair でも CGE-000/001 により

\[
CrossLeft + CrossRight = 2n
\]

が fixed even fiber 上で成立する。

したがって Cross-Gap の非対称な内部生成構造とは独立に、出力 pair は canonical reflection fiber へ射影できる。

balanced window は

\[
0 \le t \le w
\]

に対応し、両端は

\[
n-w \le n-t \le n+t \le n+w
\]

に入る。

CGE-002 は、この balanced window と anchor `P` が

\[
P < n-w,
\qquad
n+w \le squareBody(P)
\]

を満たすなら、両 endpoint を同じ SquareBody shell に入れられることを既に与えている。

よって CGE-003 の中心課題は、window 内で

\[
SupportDisjointFrom\ (primeScalesUpTo\ P)
\]

を両端が同時に満たす seat を記述・数えることである。

---

## 既存 API の優先確認

repository-first で少なくとも以下を読むこと。

- `DkMath.NumberTheory.Goldbach.Basic`
- `DkMath.NumberTheory.Goldbach.Obstruction`
- `DkMath.NumberTheory.Goldbach.Capacity`
- `DkMath.NumberTheory.Goldbach.Overlap`
- `DkMath.NumberTheory.Goldbach.PairOverlap`
- `DkMath.NumberTheory.Goldbach.CrossGapEscape`
- `DkMath.NumberTheory.Goldbach.CrossGapSquareCertification`
- `DkMath.NumberTheory.Primitive.SquareBody`
- `DkMath.NumberTheory.Primitive.FinitePrimeWorld`

特に既存の

- `goldbachOffsets`
- `GoldbachProperObstructed`
- `goldbachBlockedSeats`
- `goldbachCoveredSeats`
- `goldbachSurvivors`
- `goldbach_survivors_add_covered`
- `goldbachIncidence`
- `goldbachOverlapExcess`
- `goldbachOffsetPrimePairMultiplicity`
- `primeScalesUpTo`
- `SupportDisjointFrom`

を再利用し、同じ意味の全区間 API を複製しないこと。

---

## production owner

候補:

`DkMath/NumberTheory/Goldbach/BalancedReflection.lean`

または既存 naming に合わせて

`DkMath/NumberTheory/Goldbach/CrossGapBalancedReflection.lean`

としてよい。

ただし、canonical reflection window 自体は Cross-Gap 専用ではないため、generic Goldbach owner に置く方が自然ならそちらを優先する。

---

## CGE-003 必須実装

### 1. balanced reflection window

`goldbachOffsets n` の部分集合として、中心から幅 `w` の offset window を定義する。

候補名:

```lean
goldbachBalancedOffsets (n w : ℕ) : Finset ℕ
```

意味は概念的に

\[
\{t \in goldbachOffsets(n) \mid t \le w\}.
\]

`Finset.range` を直接重複定義するより、既存 `goldbachOffsets` の filter として定義することを優先する。

最低限、membership theorem と subset theorem を作る。

可能なら card を exact に取る。
例えば自然数境界処理を正確にした上で

\[
|W(n,w)| = \min(n-1,w+1)
\]

に相当する式が clean に証明できるなら production theorem にする。
無理なら card exactness は後回しでよい。

---

### 2. reflection endpoints

候補として

```lean
reflectionLeft  (n t : ℕ) := n - t
reflectionRight (n t : ℕ) := n + t
```

の軽量 wrapper を置いてよい。

必須:

\[
reflectionLeft(n,t)+reflectionRight(n,t)=2n
\]

を `t ≤ n` など正確な仮定付きで theorem 化する。

また `t ∈ goldbachBalancedOffsets n w` から

\[
n-w \le reflectionLeft(n,t),
\qquad
reflectionRight(n,t) \le n+w
\]

を得る。

---

### 3. Cross-Gap pair の canonical reflection offset

fixed even fiber

```lean
CrossGapEvenFiberAt n d₁ x₁ u₁ d₂ x₂ u₂
```

に対し、出力を

```text
L := crossLeft ...
R := crossRight ...
```

とする。

順序に依存しない canonical offset を候補として

```lean
crossGapReflectionOffset n ... := n - min L R
```

などで定義し、可能なら以下を証明する。

\[
\min(L,R)=n-t,
\qquad
\max(L,R)=n+t.
\]

ここで `t` は canonical offset。

重要:

- `CrossLeft ≤ CrossRight` を恒久仮定にしない。
- Cross-Gap の left/right label と canonical Goldbach left/right を混同しない。
- `min/max` による orientation normalization を優先する。

さらに balanced condition

\[
\max(L,R) \le n+w
\]

と

\[
t \le w
\]

の同値または片方向 bridge を、自然数境界が clean に扱える範囲で theorem 化する。

---

### 4. window-local blocked / covered / survivors

balanced offsets のみに制限した finite sieve API を作る。

候補:

```lean
goldbachWindowBlockedSeats
goldbachWindowCoveredSeats
goldbachWindowSurvivors
```

ただし既存 API を filter / intersection で再利用し、ロジックを複製しないこと。

推奨 shape:

```text
goldbachWindowBlockedSeats n w r
  = goldbachBlockedSeats n r ∩ goldbachBalancedOffsets n w
```

または同値な filter。

window survivors は、任意 finite prime set `S` を受け取れる generic form が望ましい。

必須の exact conservation:

\[
|survivors| + |covered| = |window|.
\]

これは CGE-003 の中心 bookkeeping theorem。

---

### 5. anchor-local obstruction world

CGE-002 の SquareBody certification に必要なのは `goldbachSmallPrimes n` 全体ではなく、anchor `P` までの

```lean
primeScalesUpTo P
```

である。

したがって balanced window について

```lean
goldbachBalancedSquareSurvivors n w P
```

のような wrapper を置いてもよい。

意味は、各 offset `t` の両 endpoint

\[
n-t,
\qquad
n+t
\]

が `primeScalesUpTo P` のどの prime にも proper obstruction されないこと。

可能なら既存 `GoldbachSurvives n (primeScalesUpTo P) t` をそのまま利用し、新 predicate を増やさない。

---

### 6. window survivor から SquareBody prime pair への bridge

以下の仮定:

\[
w\le n,
\]

\[
P<n-w,
\]

\[
n+w\le squareBody(P),
\]

\[
t\in goldbachBalancedOffsets(n,w),
\]

\[
GoldbachSurvives\ n\ (primeScalesUpTo\ P)\ t
\]

の下で

\[
Prime(n-t) \land Prime(n+t)
\]

を導く theorem を作る。

証明は CGE-002 / SquareBody support-disjoint theorem を再利用すること。

必要なら `GoldbachSurvives` から `SupportDisjointFrom (primeScalesUpTo P)` への小さな bridge lemma を作る。

ここでは `goldbachSmallPrimes n` を使った完全 sieve に戻らない。
**balanced SquareBody shell に必要な prime support だけで certifying する**ことが目的。

その結果として

```lean
GoldbachPairAt n
```

への conditional theorem を追加してよい。

---

### 7. strict window-capacity criterion

window 内の survivor existence を exact finite cardinality として表す。

概念形:

\[
WindowSurvivors.Nonempty
\iff
|WindowCovered| < |Window|.
\]

さらに strict cover inequality から `GoldbachPairAt n` へ至る conditional theorem を作る。

ただしこれは **provider のインターフェイス**であり、universal inequality を証明してはいけない。

既存 `GoldbachCapacityEscape` の window-local 版 proposition を定義する場合は、Strong Goldbach と同値になるような全称命題を「新成果」と誤認しないこと。

---

## primorial / reflection の optional audit

今回の動機確認として、`M=30` の reduced residue reflection

\[
1+29=30,
\quad
7+23=30,
\quad
11+19=30,
\quad
13+17=30
\]

を audit に置いてよい。

ただしこの数値例から universal Goldbach を示唆する production theorem を作らない。

また最小 `M=2` の

\[
1+1=2
\]

は reflection involution の fixed-point regression として置いてよい。

これらは conceptual regression であり、CGE-003 の proof dependency にはしない。

---

## Capacity / Overlap との関係

既存 `Capacity.lean`, `Overlap.lean`, `PairOverlap.lean` は全 `goldbachOffsets n` 上の exact ledger を既に持つ。

今回の目的はそれらを否定・置換することではない。

CGE-003 では balanced window への restriction theorem を優先し、可能なら

```text
windowCovered ⊆ goldbachCoveredSeats
windowIncidence ≤ goldbachIncidence
```

などを bridge として取る。

PairOverlap の高次 Pascal ledger は今回の必須範囲外。
window survivor existence の単純 union-capacity が不足すると判明した時点で次段階に回す。

---

## 禁止事項 / 非目標

1. Strong Goldbach の証明を主張しない。
2. `∀ n, ∃ t ∈ balancedWindow, survivor` を仮定なしで証明しようと無理をしない。
3. survivor predicate に `Nat.Prime` を埋め込まない。
4. Cross-Gap 内部 coordinates を `x=1` や固定 degree へ潰さない。
5. twin-prime / bounded-gap theorem を仮定しない。
6. AKS を使わない。
7. RH / CFBRC / analytic prime density を導入しない。
8. PairOverlap の全 hierarchy を window 用に複製しない。
9. `Coprime` を primality と同一視しない。
10. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom` を使わない。

---

## audit / regression

最低限以下を確認する。

1. `n=15, w=14` などで reflection pairs が `30` を保存すること。
2. `M=30` の prime pair examples `13+17`, `7+23` を balanced offset として再生。
3. `1+29=30` は endpoint `1` を含むので Goldbach prime pair ではないことを明確にする。
4. `M=2` の `1+1=2` は reflection fixed point だが prime pair ではない。
5. 一つの小さな `P,n,w,t` で SquareBody shell + `GoldbachSurvives n (primeScalesUpTo P) t` から prime pair を replay。
6. window survivor/covered card conservation を concrete Finset で `native_decide` なしに確認できる範囲で `norm_num` / `decide` / theorem replay を使う。

---

## Outcome 判定

`report-003.md` に以下のどれかを記す。

### Outcome A — LOCALIZED SURVIVOR PROVIDER INTERFACE

balanced reflection window、Cross-Gap canonical offset、window-local exact cover conservation、SquareBody anchor-local certification が一つの API として接続され、
今後は strict window-cover inequality の provider だけを研究すればよい状態になった。

### Outcome B — WINDOW RESTRICTION ONLY

window API は正しいが、既存 Capacity / SquareBody の単なる restriction 以上の構造的 gain は得られなかった。
それでも proof decomposition として有用なら保持する。

### Outcome C — COLLAPSE TO EXISTING CAPACITY

新しい定義の大部分が既存 `goldbachOffsets` / `goldbachCoveredSeats` の trivial filter で、Cross-Gap bridge も既存 theorem の即時 corollary にすぎず、独立 module の価値が低い。
その場合 production 追加を最小化し report で閉じる。

---

## report-003.md に書くこと

- 追加・変更ファイル
- balanced window の exact definition
- reflection endpoint / canonical offset theorem
- Cross-Gap pair から reflection fiber への bridge
- window blocked / covered / survivors の theorem 一覧
- survivor + covered = window card の exact identity
- anchor `P` prime world を使った SquareBody prime-pair certification
- strict window-capacity -> `GoldbachPairAt` conditional bridge
- Capacity / Overlap 既存 API との再利用関係
- primorial reflection regression の範囲
- focused build / facade build
- `#print axioms`
- forbidden construct grep
- Outcome A/B/C
- 次段階で残る exact provider statement を一つだけ明記

---

## CGE-003 完了条件

以下を満たしたら停止する。

- balanced reflection window が production API として定義された。
- Cross-Gap fixed-even pair を canonical reflection offset へ射影できる。
- window-local blocked / covered / survivors が既存 API の restriction として固定された。
- survivor + covered = window card が kernel-check された。
- anchor `P` の `primeScalesUpTo P` escape から balanced pair primality を得る bridge がある。
- strict window cover shortfall から `GoldbachPairAt n` へ進む conditional theorem がある。
- universal survivor existence は主張していない。
- focused build / `lake build DkMath` 成功。
- axiom audit で `sorryAx` / 新規 axiom なし。
- `report-003.md` を残す。

CGE-003 の次に攻めるべき問題は、

\[
\boxed{\text{balanced window の obstruction cover が全 seat を覆えない条件}}
\]

を、既存 Capacity / Overlap / PairOverlap と Cross-Gap transfer 構造のどこから供給できるか、である。
