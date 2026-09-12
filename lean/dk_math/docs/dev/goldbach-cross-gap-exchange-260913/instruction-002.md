# CGE-002: Balanced Square Certification と局所素数認証地平線の実装指示

## 目的

CGE-000 では full-coordinate Cross-Gap 保存則

\[
CrossLeft + CrossRight = PairedBig
\]

を固定した。
CGE-001 では fixed even fiber `PairedBig = 2*n` 上で、small-prime obstruction を全て回避した一点が prime pair である、という有限認証終端を整備する。

CGE-002 では、さらに DkMath 既存の `SquareBody` prime certification を Cross-Gap に接続し、**候補 pair が中心 `n` の近くにある場合、全体上限 `2*n` ではなく pair-local な平方境界で両 endpoint を認証できる構造**を固定する。

この段階でも survivor の全称存在は証明しない。
狙うのは、

> Cross-Gap pair がある平方殻の prime-certification horizon に入り、既知 prime support を避けているなら、両 endpoint は prime である

という exact bounded bridge である。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 最重要の解釈

`SquareBody` の degree `2` は、Cross-Gap を生成する宇宙の degree を `2` に固定する意味ではない。

Cross-Gap 側の

\[
(d_1,x_1,u_1),\qquad(d_2,x_2,u_2)
\]

は任意のまま保持する。

`SquareBody P = P^2 + 2P = (P+1)^2 - 1`

は **prime certification の外側 envelope / horizon** としてだけ使う。

したがって今回の構造は

\[
\text{arbitrary-degree Cross-Gap generator}
\longrightarrow
\text{degree-two square certification envelope}
\]

であり、`d₁=d₂=2` への特殊化ではない。

---

## AKSBridge についての firewall

`DkMath.NumberTheory.AKSBridge` は現状、prime 側の Frobenius / cyclic congruence bridge を持つが、完全な AKS primality criterion の converse までは提供していない。

特に現状の `AKSBound` は軽量 placeholder であり、これを「AKS 判定が完成している」と解釈してはいけない。

従って CGE-002 では AKS を primality certifier として使わない。
必要なら比較用コメントに留め、実際の prime certification は `Primitive.SquareBody` の kernel-checked theorem を使う。

---

## 既存 API の優先確認

必ず repository-first で次を確認すること。

- `DkMath.NumberTheory.Goldbach.CrossGapExchange`
- CGE-001 実装済みならその Cross-Gap escape / even-fiber API
- `DkMath.NumberTheory.Primitive.SquareBody`
- `DkMath.NumberTheory.Primitive.FinitePrimeWorld`
- `DkMath.NumberTheory.Goldbach.Obstruction`

特に既存の以下を再利用する。

- `squareBody`
- `squareBody_add_one_eq`
- `prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody`
- `primeScalesUpTo`
- `SupportDisjointFrom`

同値 theorem がすでに存在する場合は重複実装しない。

---

## production owner

候補:

`DkMath/NumberTheory/Goldbach/CrossGapSquareCertification.lean`

`CrossGapExchange.lean` は保存則 owner のままにする。
CGE-001 の module が存在する場合は、その認証 API を import してよい。

必要なら `DkMath/NumberTheory/Goldbach.lean` facade に import を追加する。

---

## CGE-002-A: generic square-shell prime iff support-disjoint

まず `SquareBody` 側に同値 theorem がまだ無い場合だけ、generic helper を適切な owner に追加する。

目標は概念的に、

\[
P < m \le squareBody(P)
\]

の範囲で

\[
\boxed{
Prime(m)
\iff
SupportDisjointFrom(primeScalesUpTo(P),m)
}
\]

を得ること。

逆向き

\[
SupportDisjoint \Rightarrow Prime
\]

は既存 `prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody` を使う。

順向きは、`m` 自身が `P` より大きいため `primeScalesUpTo P` に含まれず、prime divisor が `m` 自身に一致するしかないことから証明する。

注意:

- `P < m` を外さないこと。`m ≤ P` の prime は自分自身が old support に入るため `SupportDisjointFrom` ではない。
- 既存 theorem が同じ内容を既に持つなら新規追加しない。

---

## CGE-002-B: pair-local height

Cross-Gap pair の認証に必要な上限を pair-local に保持する。

候補定義:

```lean
crossPairHeight := max CrossLeft CrossRight
```

巨大な structure は不要。
単なる wrapper か theorem 内の `max` で十分なら定義しなくてよい。

最低限、

\[
CrossLeft \le H,
\qquad
CrossRight \le H
\]

を使いやすい形にする。

---

## CGE-002-C: square-certified Cross-Gap pair

prime を定義に入れない bounded certification predicate を作ってよい。

概念形:

\[
P < CrossLeft,
\qquad
P < CrossRight,
\]

\[
CrossLeft \le squareBody(P),
\qquad
CrossRight \le squareBody(P),
\]

かつ

\[
SupportDisjointFrom(primeScalesUpTo(P),CrossLeft),
\]

\[
SupportDisjointFrom(primeScalesUpTo(P),CrossRight).
\]

候補名:

```lean
CrossGapSquareCertified
```

ただし theorem hypotheses のままの方が簡潔なら predicate は作らなくてよい。

そして必須 theorem として

\[
\boxed{
CrossGapSquareCertified
\Longrightarrow
Prime(CrossLeft)\land Prime(CrossRight)
}
\]

を証明する。

これは `d₁,d₂` に制限を置かないこと。

---

## CGE-002-D: square certification から Goldbach への bridge

fixed even fiber

\[
PairedBig = 2n
\]

と CGE-000 の保存則から

\[
CrossLeft + CrossRight = 2n
\]

を使う。

CGE-002-C の square certification があるなら、

\[
GoldbachPairAt(n)
\]

を返す production theorem を作る。

これは existence provider ではない。
「この bounded configuration が与えられれば Goldbach witness になる」という終端 bridge である。

---

## CGE-002-E: balanced window から square shell への輸送

今回の新しい幾何的ポイント。

fixed even fiber 上で

\[
L:=CrossLeft,
\qquad
R:=CrossRight,
\qquad
L+R=2n
\]

とする。

ある window 幅 `w` に対して

\[
L \le n+w,
\qquad
R \le n+w
\]

かつ

\[
w\le n
\]

なら、保存則から

\[
n-w \le L,
\qquad
n-w \le R
\]

が従う。

そこで anchor `P` が

\[
P < n-w
\]

および

\[
n+w \le squareBody(P)
\]

を満たすなら、両 endpoint は自動的に同じ square shell

\[
P < L,R \le squareBody(P)
\]

へ入る。

この transport theorem を production にする。

その上で support-disjoint 条件を足せば、両 endpoint の primality を同時に認証できる corollary を作る。

この theorem が、「近い pair の方が認証 envelope を狭くできる」という直感を Lean 上で表現する中心である。

ただし計算量・高速化を証明したとは主張しない。

---

## CGE-002-F: global cutoff との比較は慎重に

既存 `goldbachSmallPrimes n` は endpoint の universal upper bound `2n` を使うため、全 seat に対して安全な cutoff を与える。

CGE-002 では near-balanced candidate の局所上限 `n+w` を使うことで、より小さい square horizon を使える可能性を整理する。

しかし次は主張しないこと。

- 「双子素数型 pair が必ず存在する」
- 「near-balanced pair が Goldbach を証明する」
- 「AKS より高速である」
- asymptotic complexity の改善

証明するのは bounded certification の条件関係だけ。

---

## optional: local cutoff theorem

簡潔に取れるなら、endpoint pair `(L,R)` に対して global `2n` ではなく

\[
H=\max(L,R)
\]

を使った small-prime witness theoremを generic helper として追加してよい。

概念的には、`2 ≤ m ≤ H` かつ `m` composite なら

\[
\exists q\text{ prime},\quad q^2\le H,\ q\mid m,\ m\ne q.
\]

ただし既存 `goldbach_small_prime_witness` の単なる引数置換で済むなら新しい API を増やしすぎないこと。

---

## audit / regression

最低限次を確認する。

1. `SquareBody` certification が generator degree と独立であること。
   - 少なくとも `d₁` または `d₂` が `2` でない具体的 Cross-Gap configuration を一つ使う。

2. near-balanced window の算術 regression。
   - `L+R=2n`
   - `L,R ≤ n+w`
   - `n-w ≤ L,R`
   を `norm_num` / `omega` で確認する小例。

3. support-disjoint を満たす小さな square-shell prime の replay。

4. support-disjoint を満たさない composite の firewall。

5. AKSBridge を prime certifier として利用していないこと。

無理に Cross-Gap parameter から特定 Goldbach pair を生成しなくてよい。

---

## 禁止事項 / 非目標

1. Strong Goldbach の証明。
2. near-balanced prime pair の存在 theorem。
3. Twin Prime conjecture の利用・主張。
4. `d₁=d₂=2` への generator 特殊化。
5. AKSBridge を完全 AKS primality test と見なすこと。
6. CFBRC / RH / prime density の導入。
7. CRT / Capacity / PairOverlap の再導入。
8. 大規模探索 Finset の作成。
9. `Coprime` のみから primality を導くこと。
10. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom`。

---

## Outcome 判定

実装後 `report-002.md` を作る。

### Outcome A — LOCAL SQUARE CERTIFICATION GAIN

near-balanced / pair-local bound により、Cross-Gap endpoint を generic `2n` cutoff より狭い square certification horizon へ運べる theorem が得られ、arbitrary-degree generator と SquareBody certifier の独立接続が production API として成立した。

### Outcome B — CORRECT BUT NO EFFECTIVE NARROWING

SquareBody bridge 自体は成立したが、実際には既存 `2n` cutoff の言い換えに近く、near-balanced 条件から有用な horizon narrowing を theorem として得られなかった。

### Outcome C — COLLAPSE / REDUNDANT

既存 `Obstruction` / `SquareBody` theorem の直接合成だけで十分で、新 module を維持する価値がほぼ無い。

Outcome A でも Goldbach existence の進展とは数えない。

---

## report-002.md に書くこと

- 追加・変更ファイル
- generic square-shell prime iff theorem を追加したか、既存再利用したか
- Cross-Gap square certification theorem の exact statement
- generator degree に制限がないこと
- balanced window -> square shell theorem
- `P < n-w` と `n+w ≤ squareBody P` の役割
- global `2n` cutoff と local horizon の違い
- AKSBridge を使わなかった理由
- regression
- focused build / facade build
- `#print axioms`
- 禁止構文 grep
- Outcome A/B/C

---

## CGE-002 完了条件

以下を満たしたら停止する。

- arbitrary-degree Cross-Gap pair を SquareBody prime certification に接続した。
- `P < m ≤ squareBody P` 範囲の prime/support-disjoint bridge を再利用または整備した。
- balanced window `n±w` から両 endpoint が同一 square shell に入る theorem を得た。
- square-certified configuration から `GoldbachPairAt n` への conditional bridge を得た。
- near-balanced pair の存在は主張していない。
- AKS を完成済み primality test と誤認していない。
- focused build 成功。
- axiom audit で `sorryAx` / 新規公理がない。
- `report-002.md` を残した。
