# PRIM-JAC-000 Jacobsthal / primorial coprime-gap frontier audit

日付: 2026-08-25
対象: `instruction-036.md`
対象ブランチ: `wip/number-theory-primitive-structure-260822-v2`
対象 toolchain: Lean / Mathlib v4.32.2

## 0. 結論

今回の checkpoint は、Lean source、theorem statement、docstring、import、依存関係、
toolchain、既存の Legendre frontier を変更しない report-only 調査である。

最終分類は **Outcome B — EXACT HARD-FRONTIER IDENTIFICATION** とする。

既存 DkMath API から、次の anchored statement は正確に得られる。

```text
LegendreConjecture
  ↔ ∀ n > 0, ∃ r, 1 ≤ r ∧ r ≤ 2*n ∧
      Nat.Coprime (n^2 + r) (primeWorldModulus (primeScalesUpTo n)).
```

ここで

```text
M(n) := primeWorldModulus (primeScalesUpTo n)
```

である。`M(n)` は `n` 以下の全素数の積であり、`n ≥ 2` なら「最大の素数
`p ≤ n` の primorial」、`n` 自身が素数なら通常の `n#` である。

しかしこの statement は、任意の開始点に対する global Jacobsthal bound

```text
j(M(n)) ≤ 2*n
```

とは異なる。後者は anchored statement を含意するが、はるかに強く、しかも
`n=227` で既知の primorial Jacobsthal 値 `j(227#)=742` に対して
`2*n=454` を超える。従って global bound はこの scale の provider にならない。

Jacobsthal の語彙は、現在の「square shell における bounded-prime wave の全被覆」
を「特定の開始点における primorial-coprime gap」として明確化する。しかし、
anchored square geometry を保ったまま全ての `n` を処理する独立 theorem/provider は
見つからなかった。

## 1. 調査対象と用語の正規化

### 1.1 DkMath の対象

`DkMath.NumberTheory.Primitive` では、

```lean
primeScalesUpTo n
primeWorldModulus S
SupportDisjointFrom S m
```

が有限 prime world とその積 modulus を表す。Legendre 層では、`n²+1` から
`n²+2n` までの `2n` 個の offset が `SquareOffset n r` で表される。

### 1.2 Jacobsthal の convention

このレポートでは、文献の次の convention を採用する。

```text
j(N) = 任意の j(N) 個の連続整数の中に
       N と互いに素な整数が存在するための最小の正整数。
```

この convention では、`j(30)=6` である。文献によっては「全てが非 coprime な
連続列の最大長」を `g(N)` と呼び、`g(N)=j(N)-1` とする。以下では必ず block
length convention の `j` に換算する。

外部文献と repository-derived facts は分離する。文献調査に用いた主な資料は次の通り。

- T. R. Hagedorn, *Computation of Jacobsthal's function h(n) for n < 50*,
  Mathematics of Computation 78 (2009), pp. 1073--1087。
  [PDF](https://hagedorn.pages.tcnj.edu/files/2022/08/Jacobsthal.pdf)
- L. Hajdu and N. Saradha, *Disproof of a Conjecture of Jacobsthal*。
  [PDF](https://math.unideb.hu/sites/default/files/inline-files/jacobsrevsaradha.pdf)
- F. Costello and P. Watts, *A short note on Jacobsthal's function*,
  arXiv:1306.1064。
  [paper](https://arxiv.org/abs/1306.1064)
- H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Mathematica (1978),
  DOI [10.1515/dema-1978-0121](https://doi.org/10.1515/dema-1978-0121)。

## 2. Q1: canonical modulus と primorial

### 2.1 repository-derived identity

`FinitePrimeWorld.lean` の定義は

```lean
def primeScalesUpTo (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter Nat.Prime

def primeWorldModulus (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p
```

である。従って定義展開と `mem_primeScalesUpTo` により、

```text
M(n)
 = ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p
 = product of all primes p with p ≤ n.
```

各素数は `Finset` の filter に一度だけ現れるので、`M(n)` は squarefree な
bounded-prime product である。

最小の既存 theorem chain は次の通り。

1. `primeWorldModulus` を unfold する。
2. `primeScalesUpTo` を unfold する。
3. `mem_primeScalesUpTo` により filter の support を `Nat.Prime p ∧ p ≤ n`
   と読む。
4. Finset product の filter 表示を、通常の「`p ≤ n` の素数上の積」と読む。

この chain を一つの primorial theorem にまとめた公開定理は、workspace の検索では
確認できなかった。instruction-036 の非目標に従い、その theorem や新しい primorial
definition は追加しない。

### 2.2 標準 primorial notation

`p_k` を第 `k` 素数、`p_k# = ∏_{i=1}^k p_i` とする。`n ≥ 2` に対して

```text
k = π(n),
p_k = largest prime ≤ n,
M(n) = p_k#.
```

従って `n` が素数なら `M(n)=n#` であり、任意の `n` について `n#` とみなしては
ならない。`n=0,1` では prime set が空なので `M(n)=1` であり、「最大の素数 ≤ n」
という表現はこの端点には適用しない。

### Q1 の分類

**EXACT EQUIVALENCE**。`M(n)` は primorial-like な比喩ではなく、有限 product の
定義展開によって全ての素数 `p ≤ n` の積と正確に一致する。ただし DkMath に標準
primorial の新しい名前を導入する必要はない。

## 3. Q2: support escape と coprimality

### 3.1 公開 theorem chain

`FinitePrimeWorld.lean` の

```lean
supportDisjointFrom_primeScalesUpTo_iff
```

は、

```text
SupportDisjointFrom (primeScalesUpTo n) m
  ↔ ∀ q, Nat.Prime q → q ≤ n → ¬ q ∣ m
```

を直接与える。

`PeriodicPrimeWorld.lean` の

```lean
supportDisjointFrom_iff_coprime_primeWorldModulus
```

は `knownPrimeScales_primeScalesUpTo n` を渡すことで、

```text
SupportDisjointFrom (primeScalesUpTo n) m
  ↔ Nat.Coprime m M(n)
```

を与える。

従って repository の公開 API だけで

```text
Nat.Coprime m M(n)
  ↔ SupportDisjointFrom (primeScalesUpTo n) m
  ↔ ∀ q, Nat.Prime q → q ≤ n → ¬ q ∣ m
```

を得られる。向きごとの推論を新たに証明する必要はない。三つを一つの名前で公開
する wrapper はないが、必要なら単なる composition であり、今回の report-only
checkpoint で実装する bridge ではない。

### Q2 の分類

各方向の数学的内容は **EXACT EQUIVALENCE**。単一 theorem 名への包装だけが薄い
API 整理事項であり、未解決の provider ではない。

## 4. Q3: exact anchored coprime-gap form

`Frontier.lean` の既存 chain は次の通りである。

```text
LegendreConjecture
  ↔ SquareAnchoredSupportEscape
  ↔ ∀ n > 0, ∃ r,
      SquareOffset n r ∧
      SupportDisjointFrom (primeScalesUpTo n) (n²+r).
```

該当する公開 theorem は、

```lean
legendreConjecture_iff_squareAnchoredSupportEscape
squareAnchoredSupportEscape_iff_raw
supportDisjointFrom_primeScalesUpTo_iff
supportDisjointFrom_iff_coprime_primeWorldModulus
```

である。`SquareOffset n r` は定義上 `1 ≤ r ∧ r ≤ 2*n` なので、rewrite のみで

```text
LegendreConjecture
  ↔ ∀ n > 0, ∃ r,
      1 ≤ r ∧ r ≤ 2*n ∧
      Nat.Coprime (n²+r) M(n).
```

を得る。

これは Legendre の新しい証明ではない。既存の support escape frontier を、bounded
prime divisibility と finite-world coprimality の語彙へ移した **exact reformulation**
である。

### Q3 の分類

**EXACT EQUIVALENCE**。`LegendreConjecture` と anchored bounded-prime coprime escape
は、既存 theorem chain の範囲で完全に同値である。

## 5. Q4: report-local anchored gap quantity

Lean definition は追加せず、分析用に次を置く。

```text
A(n) := min { r ∈ ℕ | 1 ≤ r ∧ Nat.Coprime (n²+r) M(n) }.
```

この集合は空ではない。`M(n)=1` なら `r=1` が使える。`M(n)>1` なら、`r` を
`n²+r ≡ 1 (mod M(n))` となる正の代表元から選べるので、少なくとも一つの正の
coprime offset がある。従って `A(n)` は有限の正整数として定義できる。

既存 frontier の `SquareOffset n r` は `1 ≤ r ∧ r ≤ 2*n` なので、正の `n` について

```text
LegendreConjecture ↔ ∀ n > 0, A(n) ≤ 2*n.
```

が成立する。`n=1` では `M(1)=1` かつ `A(1)=1` であり、端点にも問題はない。

### Q4 の分類

**EXACT EQUIVALENCE**。ただし `A(n)` は report-local notation であり、Lean 定義を
追加しない。

## 6. Q5: anchored gap と global Jacobsthal function

### 6.1 二つの statement

block length convention で

```text
j(M) := 最小の L であって、任意の開始点 a に対し
        a+1, ..., a+L の中に M と coprime な数がある。
```

とする。このとき DkMath の statement は、任意の `a` ではなく `a=n²` に対する

```text
A(n) ≤ 2*n
```

である。

### 6.2 含意関係

```text
j(M(n)) ≤ 2*n
  ⇒ A(n) ≤ 2*n
  ⇒ Legendre instance at n.
```

最初の含意は **SUFFICIENT BUT STRONGER**。global condition は square anchor 以外の
全開始点も制御するからである。

逆向きは一般には成立しない。例えば `M=30`、block length `5`、開始点 `0` なら
`1,2,3,4,5` の中に `30` と coprime な `1` があるが、`j(30)=6` なので全開始点
の length-5 statement は偽である。この例は anchored predicate が uniform predicate
より弱いという論理構造を示す。

この一般論から、DkMath の特定 modulus family について anchored predicate と global
predicate の真偽が異なるとまでは主張しない。ただし、次節の既知の primorial 値により
global bound 自体が `n=227` で失敗することは確認できる。

### 6.3 off-by-one

Hagedorn は `j(30)=6` とし、これは「最大の非-coprime run の長さ 5」ではなく、
coprime を必ず含む block length 6 である。従って DkMath の offset 個数 `2*n` と
比較するのは `j(M(n))` そのものであり、最大 run length を比較する場合は `+1` が
必要である。

### Q5 の分類

```text
j(M(n)) ≤ 2*n ⇒ anchored DkMath target
```

は **SUFFICIENT BUT STRONGER**。

```text
anchored DkMath target ⇒ j(M(n)) ≤ 2*n
```

は一般には **UNRELATED / WRONG TARGET** として扱うべきであり、DkMath の特定 family
についての converse は主張しない。

## 7. Q6: known bounds と required scale

ここでは文献の upper/lower bound を repository theorem と混同しない。
`k = ω(M(n)) = π(n)`、`p_k` を `k` 番目の素数とする。

### 7.1 Upper bounds

| 文献上の bound | parameter / constant | `j(M(n)) ≤ 2n` への判定 |
|---|---|---|
| Iwaniec: `j(m) ≪ (ω(m) log ω(m))²` | absolute implied constant は explicit provider ではない | **ASYMPTOTIC BUT CONSTANT UNCONTROLLED**。さらに `k=π(n)` では概ね `O(n²)` scale で線形 bound に届かない |
| Kanold: primorial `h(k)` の elementary explicit bound | Hagedorn の整理では exponential 型 `2^k` | **TOO WEAK AT THE REQUIRED SCALE** |
| Stevens: `h(k) ≤ 2 k^(2+2e log k)`（十分大きい k の explicit bound） | explicit だが exponent が大きい | **EXPLICIT AND POTENTIALLY SUFFICIENT** ではなく、実際には `2n` を示すには **TOO WEAK AT THE REQUIRED SCALE** |
| Costello--Watts, Eq. (1.8): `g(m) ≤ 2e^γ k^(5+5 log log k)` | `k=ω(m)`、explicit integer bound | **TOO WEAK AT THE REQUIRED SCALE** |

最後の二つは「explicit」ではあるが、explicit であることと required scale に届く
ことは別である。`k=π(n)` を代入しても `2n` 以下になる inequality chain は得られない。
Iwaniec の `O` bound も、指定された全ての `n` に対する explicit finite verification
へ落ちる形ではない。

### 7.2 Primorial lower bound と global condition の反例

Hagedorn の文献整理には、Pintz の primorial lower bound

```text
h(k) = j(p_k#)
  ≥ (2e^γ + o(1)) p_k log p_k
      · log_3(p_k) / (log_2(p_k))²
```

が記載されている。これは `p_k` に対して線形 scale より大きくなる因子を含む。
`p_{π(n)} ~ n` と合わせると、primorial modulus `M(n)` に対して global quantity は
漸近的に `2n` を超える側にある。

さらに、Hagedorn の Table 1 は

```text
h(49) = j(p_49#) = 742
```

を与える。`p_49=227` なので、DkMath の `n=227` では

```text
M(227) = 227#,
j(M(227)) = 742 > 454 = 2*227.
```

これは `j(M(n)) ≤ 2*n` が単に未証明なのではなく、global primorial route の
要求そのものがこの family で一般に成立しないことを示す具体的な反例である。
これは anchored square block `227²+1,...,227²+454` の coprime survivor の不存在を
意味しない。global bound の失敗と anchored Legendre instance は別の命題である。

### Q6 の分類

既知の upper bounds は required linear scale の provider ではなく、primorial lower bound
は global condition が強すぎることを示す。

```text
global Jacobsthal route: TOO WEAK / WRONG SCALE
anchored square route:  exact but still provider-free
```

従って Outcome A（global bound による直接 leverage）は選べない。

## 8. Q7: DkMath wave / carry / overlap stack との関係

既存の Legendre stack は、square anchor の位相を保持したまま次を扱う。

- `squareWaveOffsets`: 特定 modulus が shell のどの offset を覆うか。
- `squareWaveCarry`: occupancy の quotient difference と 0/1 carry。
- pair overlap: 複数波の共通座席と product divisibility。
- near/far split、localized obstruction ledger、packet cross geometry。
- `SquareOffsetsFullyCovered` と `SquareAnchoredSupportEscape` の exact frontier。

global Jacobsthal は、任意の開始点で prime residue waves が連続 block を覆わない
ことを要求する。したがって、Jacobsthal vocabulary は union-of-residue-waves problem
を最大 coprime gap の言葉で包装するが、`n²` の anchor phase と shell の endpoint
geometry を捨てる。

得られるものは次の三点である。

1. 外部文献の Jacobsthal bound を候補 provider として比較できる。
2. global condition が anchored condition より強いことを明示できる。
3. `M(n)` が product of bounded prime waves であることを一つの modulus に集約できる。

得られないものは、wave carry の新しい inequality、pair overlap の新しい ledger、
packet determinant の制約、または shell-specific survivor である。inclusion-exclusion、
Hall matching、analytic sieve を追加しない限り、global vocabulary は現行の有限被覆を
別の index で呼び直すだけである。

### Q7 の分類

**EXACT EQUIVALENCE / HARD-FRONTIER REPACKAGING**。外部 theorem family を参照する
入口は増えるが、DkMath の局所 geometry を強化する新定理は得られない。globalization
によって anchor 情報を失うため、現行 wave stack の代替 provider にはならない。

## 9. Q8: periodicity と modulo `M(n)`

`PeriodicPrimeWorld.lean` の公開 theorem は、少なくとも次の周期性を与える。

```lean
supportDisjointFrom_add_primeWorldModulus_iff
supportDisjointFrom_add_mul_primeWorldModulus_iff
supportDisjointFrom_mod_primeWorldModulus_iff
supportDisjointFrom_centered_mirror_iff
```

`S = primeScalesUpTo n` とし、Q2 の coprimality equivalence を通せば、

```text
Nat.Coprime m M(n)
  ↔ Nat.Coprime (m % M(n)) M(n)
```

という finite residue reduction を得る。したがって、固定 `n` の anchored shell は

```text
n²+1, ..., n²+2n mod M(n)
```

という有限 block の判定に正確に還元できる。

これは次を意味する。

- 固定 `n` では問題が有限になる。
- shell の各座席の support/coprime status は modulus residue で決まる。
- `M(n)` は `n` とともに変化するので、全 `n` を一つの finite automaton や一つの
  固定 modulus で処理することはできない。
- 周期性は survivor の存在を自動的には与えない。

`supportDisjointFrom_centered_mirror_iff` は `k*M(n)-r` と `k*M(n)+r` の support
状態を比較する。しかしこれは multiples of `M(n)` を中心とする一般的な反射であり、
具体的な anchor `n²` が `k*M(n)` になることを保証しない。`n²` の residue phase を
消去して shell に survivor を作る theorem は存在しない。

### Q8 の分類

有限 residue reduction は **EXACT EQUIVALENCE**。ただし、それは計算領域を有限化
するだけであり、uniform proof や survivor provider ではない。centered mirror も
現時点では **UNRELATED / WRONG TARGET** for the missing survivor claim である。

## 10. Q9: exact frontier classification

Jacobsthal viewpoint の成果は、

```text
Legendre
  ↔ anchored coprime escape for M(n)
```

という exact identification と、

```text
global j(M(n)) ≤ 2n
  ⇒ anchored escape
```

という stronger sufficient condition の明示である。一方、global condition は
`n=227` で既知の `j(227#)=742` により失敗するため、Legendre の証明 provider として
採用できない。

従ってこれは単なる redundant vocabulary ではない。残余問題が「bounded old-prime
waves が square anchor の `2n` seats を全被覆しない」という anchored primorial
coprime-gap problem であることを明確にし、同時に global Jacobsthal theorem をそのまま
代用できない理由を与える。

### 最終分類

**Outcome B — EXACT HARD-FRONTIER IDENTIFICATION**

Outcome A ではない理由は、required `2n` global bound が既知の explicit upper bound
から出ず、primorial family では具体的に破れるためである。Outcome C ではない理由は、
anchored/global の論理的区別、primorial modulus の exact identity、文献 bound の
scale failure が、現在の hard frontier の形をより精密に特定しているためである。

## 11. Q10: next-step decision

推奨は **1. stop Jacobsthal route; keep only the frontier identification**。

理由は次の通り。

- anchored coprime equivalence は既存 theorem の rewrite composition で既に得られる。
- 新しい Jacobsthal definition や primorial abstraction は不要である。
- global theorem は anchored geometry を失い、必要な `2n` scale にも適合しない。
- thin wrapper を追加しても、prime-wave/support/coverage の provider gap は埋まらない。
- 新たな進展には、anchor-specific な coprime survivor theorem、または現行 wave/overlap
  stack を使った独立の coverage obstruction が必要である。

次の checkpoint で Jacobsthal route を再開する場合も、まずこの二つのどちらかを
具体的な theorem statement として提示すべきである。

```text
1. anchored square block に特化した explicit coprime-gap bound;
2. SquareOffsetsFullyCovered から矛盾を導く finite support/overlap theorem.
```

これらがない状態で global Jacobsthal function、PNT/Mertens、sieve estimate、RH/CFBRC
provider を DkMath に導入してはならない。

## 12. 実装・docstring 境界

instruction-036 の hard boundary に従い、次を変更していない。

- Lean source と theorem statement
- Lean docstring と module documentation
- import、facade、依存関係、Lake 設定、`lean-toolchain`
- PRIM-C001/C002、PRIM-L022、既存 Legendre frontier
- Jacobsthal function / primorial の DkMath 定義
- inclusion-exclusion、Hall matching、analytic sieve、RH/CFBRC 依存

本ファイルのみを成果物とする。

## 13. 参照した主な repository declarations

```text
DkMath.NumberTheory.Primitive.primeScalesUpTo
DkMath.NumberTheory.Primitive.mem_primeScalesUpTo
DkMath.NumberTheory.Primitive.primeWorldModulus
DkMath.NumberTheory.Primitive.supportDisjointFrom_primeScalesUpTo_iff
DkMath.NumberTheory.Primitive.supportDisjointFrom_iff_coprime_primeWorldModulus
DkMath.NumberTheory.Primitive.supportDisjointFrom_mod_primeWorldModulus_iff
DkMath.NumberTheory.Primitive.supportDisjointFrom_centered_mirror_iff
DkMath.NumberTheory.Legendre.SquareOffset
DkMath.NumberTheory.Legendre.squareOffsetCovered_iff_exists_prime_dvd
DkMath.NumberTheory.Legendre.squareAnchoredSupportEscape_iff_raw
DkMath.NumberTheory.Legendre.legendreConjecture_iff_squareAnchoredSupportEscape
DkMath.NumberTheory.Legendre.legendreConjecture_iff_squareOffsets_not_fully_covered
DkMath.NumberTheory.Legendre.squareWaveOffsets
DkMath.NumberTheory.Legendre.squareWaveCarry
DkMath.NumberTheory.Legendre.SquareOffsetsFullyCovered
```
