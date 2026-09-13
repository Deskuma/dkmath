# CGE-004: Balanced Window Capacity / Overlap の実装指示

## 目的

CGE-003 までに、固定中心 `n` の Goldbach offset fiber を中心近傍へ局所化した
balanced reflection window と、その window 上の exact survivor/cover ledger が production API として得られた。

既存の中心反射座標は

\[
(n-t,\;n+t)
\]

であり、balanced window は

\[
0\le t\le w
\]

に対応する。

CGE-003 では既に

\[
\#Survivors+\#Covered=\#Window
\]

および

\[
\#Covered<\#Window
\iff
\text{window survivor exists}
\]

が固定され、さらに anchor-local SquareBody 条件の下で survivor から `GoldbachPairAt n` へ到達できる。

CGE-004 では、**balanced window を各 prime obstruction が何席まで覆えるかを幅 `w` に依存する形で評価し、重複 obstruction を exact ledger として分離する**。

この段階でも universal survivor existence や Strong Goldbach を証明しない。
狙いは provider が次に証明すべき不等式を、

\[
\text{local capacity} - \text{overlap payment} < \#Window
\]

という形まで明示することである。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 既存 API の確認と再利用

repository-first で、少なくとも以下を確認してから実装すること。

- `DkMath.NumberTheory.Goldbach.BalancedReflection`
- `DkMath.NumberTheory.Goldbach.Capacity`
- `DkMath.NumberTheory.Goldbach.Overlap`
- `DkMath.NumberTheory.Goldbach.PairOverlap`
- `DkMath.NumberTheory.Goldbach.PrimeWorld`

CGE-003 で既に存在するもの:

- `goldbachBalancedOffsets`
- `card_goldbachBalancedOffsets`
- `goldbachWindowBlockedSeats`
- `goldbachWindowCoveredSeats`
- `goldbachWindowSurvivors`
- `goldbachWindowCoveredSeats_eq_biUnion`
- `goldbachWindow_survivors_add_covered`
- `goldbachWindowSurvivors_nonempty_iff_covered_card_lt`
- `goldbachPairAt_of_goldbachWindowSurvivor`
- `goldbachPairAt_of_goldbachWindow_cover_shortfall`

全 fiber 側には既に以下の exact ledger がある。

- `goldbachIncidence`
- `goldbach_covered_le_incidence`
- `goldbach_blocked_card_le_residue_capacity`
- `goldbachOverlapExcess`
- `goldbachIncidence_eq_covered_add_overlapExcess`
- `goldbachIncidenceConservation`
- `goldbachOffsetPrimePairMultiplicity`
- `goldbachPrimePairOverlapCount`

これらを window 全体についてコピーし直さず、**balanced window restriction として最小限の API を追加すること**。

---

## 数学的核

各 prime `r` に対して、canonical reflection seat `t` が block される条件は概念的に

\[
r\mid n-t
\quad\text{or}\quad
r\mid n+t.
\]

したがって modulo `r` では

\[
t\equiv n\pmod r
\quad\text{or}\quad
 t\equiv -n\pmod r.
\]

`r ∣ 2*n` の場合、この二つの forbidden residue は同一になり、そうでなければ二つである。

balanced window は `0 ≤ t ≤ w` なので、一つの residue class が window 内に現れる回数は高々

\[
\left\lfloor\frac{w}{r}\right\rfloor+1.
\]

従って期待する local capacity bound は

\[
\boxed{
\#Blocked_w(n,r)
\le
\begin{cases}
1 & r\mid 2n\\
2 & r\nmid 2n
\end{cases}
\left(\left\lfloor\frac wr\right\rfloor+1\right)
}
\]

である。

proper-divisor endpoint exception により実際の block 数はさらに減ることがあるが、今回の bound は upper bound でよい。

この `w` 依存 bound が、全 fiber の既存 bound

\[
\left(\left\lfloor\frac{n-2}{r}\right\rfloor+1\right)
\]

より局所化された新しい provider input になる。

---

## production owner

候補:

`DkMath/NumberTheory/Goldbach/BalancedCapacity.lean`

`BalancedReflection.lean` は reflection/window/certification owner のまま保つ。
CGE-004 の incidence / capacity / overlap ledger は別 module に置くことを推奨する。

必要なら facade `DkMath/NumberTheory/Goldbach.lean` に import を追加する。

---

## CGE-004 必須実装

### 1. window incidence

候補名:

```lean
goldbachWindowIncidence
```

概念:

\[
I_w(n,S)
:=
\sum_{r\in S}\#Blocked_w(n,r).
\]

既存 `goldbachWindowBlockedSeats` を使うこと。

少なくとも次を証明する。

\[
\#Covered_w(n,S)\le I_w(n,S).
\]

これは `Finset.card_biUnion_le` あるいは既存 capacity proof の window restriction でよい。

---

### 2. width-local per-prime capacity

今回の第一中心 theorem。

候補 statement:

```lean
theorem goldbachWindow_blocked_card_le_residue_capacity ...
```

意味:

\[
\#Blocked_w(n,r)
\le
\bigl(\text{if }r\mid2n\text{ then }1\text{ else }2\bigr)
\left(\frac wr+1\right).
\]

証明は既存 `goldbach_blocked_card_le_residue_capacity` を参照してよいが、
単にその theorem と subset から全 fiber bound を再利用して `n-2` のままにしないこと。
**必ず `w / r + 1` が theorem statement に現れる局所 bound を取ること。**

既存 `goldbachForbiddenResidues`, `goldbach_card_forbidden`, `goldbach_obstructed_iff_mem_forbidden` が使えるなら再利用する。

推奨 proof shape は、window seat `t` を

```text
((t : ZMod r), t / r)
```

へ inject し、

- 第一成分は forbidden residue set
- 第二成分は `range (w / r + 1)`

へ入ることを示す方法である。

既存 theorem 名を推測して使わず、実物を確認すること。

---

### 3. window incidence の concrete upper bound

任意有限 world `S` に対し、

\[
I_w(n,S)
\le
\sum_{r\in S}
\bigl(\text{if }r\mid2n\text{ then }1\text{ else }2\bigr)
\left(\frac wr+1\right)
\]

を証明する。

候補名:

```lean
goldbachWindow_incidence_le_residue_capacity
```

これは単純 sum upper bound であり、survivor existence を主張しない。

---

### 4. generic local obstruction support

window overlap ledger を arbitrary finite world `S` で扱うため、必要なら最小限の generic support を導入する。

候補:

```lean
goldbachObstructionSupportIn (n t : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun r => GoldbachProperObstructed n r t)
```

既存 `goldbachObstructionSupport` は `goldbachSmallPrimes n` に固定されているため、
`S = primeScalesUpTo P` の anchor-local world へそのまま使えない場合に限り、この generic wrapper を追加してよい。

巨大な abstraction hierarchy は作らない。

---

### 5. window overlap excess

候補:

```lean
goldbachWindowLocalOverlapExcess
goldbachWindowOverlapExcess
```

一 seat の obstruction support cardinality を `k` とすると、既存 full-fiber と同じく

\[
k = \mathbf 1_{k>0} + (k-1).
\]

window 上で総和し、exact に

\[
\boxed{
I_w(n,S)
=
\#Covered_w(n,S)+E_w(n,S)
}
\]

を証明する。

これが CGE-004 の第二中心 theorem。

重要:

- `E_w` は単なる定義上の調整項ではなく、**同じ seat が複数 prime obstruction によって重複して覆われた mass** として docstring に明記する。
- full-fiber `goldbachOverlapExcess` を破壊・置換しない。
- `S = goldbachSmallPrimes n` の場合に full-fiber restriction と一致する簡単な theorem が容易なら追加してよいが、必須ではない。

---

### 6. exact window incidence conservation

CGE-003 の

\[
\#Survivors+\#Covered=\#Window
\]

と今回の

\[
I_w=\#Covered+E_w
\]

から、

\[
\boxed{
\#Survivors + I_w
=
\#Window + E_w
}
\]

を証明する。

候補名:

```lean
goldbachWindowIncidenceConservation
```

さらに exact equivalence として

\[
\boxed{
\text{window survivor exists}
\iff
I_w < \#Window + E_w
}
\]

を取れるなら production theorem にする。

これは existence provider ではなく、provider が証明すべき inequality の exact normal form である。

---

### 7. supplied overlap lower bound を使う conditional provider

今後の研究で `E_w` 自体を直接計算せず、下界だけ供給できる場合を想定する。

任意の数 `e` について

\[
e\le E_w(n,S)
\]

かつ local-capacity sum `C` が

\[
I_w(n,S)\le C
\]

を満たし、さらに

\[
C<\#Window+e
\]

なら window survivor が存在する、という generic conditional theorem を作る。

概念:

```lean
window survivor from
  incidence upper bound
  + overlap lower bound
  + strict budget inequality
```

これを `S = primeScalesUpTo P` と CGE-003 の SquareBody hypotheses

\[
w\le n,
\qquad P<n-w,
\qquad n+w\le squareBody(P)
\]

へ接続し、`GoldbachPairAt n` を返す corollary を作ってよい。

ただし theorem statement に `GoldbachPairAt n` を仮定しないこと。

---

## 重要な firewall

### A. incidence-only は十分条件として強すぎる

単純に

\[
I_w<\#Window
\]

なら survivor は出るが、obstruction overlap がある場合には成立しなくても survivor は存在し得る。

したがって incidence-only criterion を最終 provider と見なさない。

### B. overlap は「負の obstruction」ではない

`E_w` は obstruction を消すものではなく、incidence が同じ covered seat を重複計上した分を支払う ledger である。

### C. pair overlap は必要なら後段

既存 `PairOverlap.lean` の Pascal hierarchy を window 化するのは、今回の exact first-overlap ledger が不足すると判明した場合だけにする。

CGE-004 で `choose k 2`, `r`-fold overlap まで全面展開しない。

---

## 数値 audit の推奨例: `2n = 30`

中心 `n = 15`, 幅 `w = 8`, anchor `P = 5` を優先 regression とする。

balanced seats は

\[
t=0,1,\ldots,8
\]

の 9 席。

reflection pair は

\[
(15-t,15+t).
\]

`primeScalesUpTo 5 = {2,3,5}` の obstruction を見ると、少なくとも概念的には

- `t=2` gives `13+17`
- `t=4` gives `11+19`
- `t=8` gives `7+23`

が survivor になる。

この例では obstruction support の重複が実際にあり、window incidence と covered card が一致しないことを audit できる。

期待される ledger の数値確認が容易なら、

\[
\#Window=9,
\qquad
\#Covered=6,
\qquad
I_w=9,
\qquad
E_w=3
\]

を `norm_num` 等で確認してよい。

この数値は production theorem の依存にしない。
Lean で実際の定義を評価して一致しない場合は report に正確な実値を書き、数学的意味を再確認すること。

また local capacity upper bound は概念上

\[
5+3+2=10
\]

程度となり、incidence-only の `10 < 9` は失敗する一方、overlap payment `3` を使えば

\[
10<9+3
\]

が成立する。

この regression は、**balanced localization だけではなく overlap accounting が必要**であることの監査に使える。

---

## この段階でやらないこと

1. `∀ n, ∃ survivor` の証明。
2. Strong Goldbach の証明。
3. universal `w(n)` の最適選択。
4. universal `P(n,w)` の最適 anchor 選択。
5. Mertens / Brun / Selberg sieve / analytic prime density の導入。
6. RH / CFBRC 接続。
7. AKS 接続。
8. full PairOverlap hierarchy の window 化。
9. Cross-Gap の新しい degree family の探索。
10. `Coprime` 単独による prime certification。
11. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom`。

今回は **window-local capacity と first-overlap ledger の exact 化**だけで停止する。

---

## Outcome 判定

実装後 `report-004.md` を作成し、以下のいずれかを判定する。

### Outcome A — WIDTH-LOCAL CAPACITY + EXACT OVERLAP LEDGER

`w / r + 1` を使う per-prime local capacity bound が得られ、window incidence / covered / overlap の exact conservation と conditional survivor criterion が production theorem として閉じた。

### Outcome B — WINDOW RESTRICTION ONLY

window ledger は実装できたが、per-prime bound が既存 full-fiber capacity より鋭くならず、`w` 固有の arithmetic gain が得られなかった。

### Outcome C — OVERLAP INTERFACE NOT USEFUL

exact ledger は作れるが、anchor-local world `primeScalesUpTo P` と接続すると provider criterion が既存 `goldbachPairAt` の単なる再表現に完全に潰れ、次段階の bound 探索に使える独立 input が残らない。

A を期待して無理に結論を作らないこと。

---

## report-004.md に書くこと

- 追加・変更ファイル
- production theorem 一覧
- `goldbachWindowIncidence` の定義
- width-local per-prime capacity theorem の exact statement
- window incidence upper bound
- overlap support / excess の exact definition
- `incidence = covered + overlap` theorem
- `survivors + incidence = window + overlap` theorem
- conditional survivor / Goldbach bridge を追加した場合はその exact hypotheses
- `n=15,w=8,P=5` audit の実値
- incidence-only bound が十分か否か
- focused build / facade build
- `#print axioms`
- 禁止構文 grep
- Outcome A/B/C
- 次段階に必要なものを一文で記す

次段階候補は、`E_w` の非自明な下界、または prime-pair overlap / CRT から overlap payment を供給する theorem である。

---

## CGE-004 完了条件

以下を満たしたら停止する。

- balanced window 用 incidence が定義された。
- `card windowCovered ≤ windowIncidence` が証明された。
- per-prime block card に `w / r + 1` が現れる local capacity bound が証明された。
- local capacity sum による window incidence upper bound がある。
- arbitrary finite world `S` について window overlap excess が定義された。
- `windowIncidence = card windowCovered + windowOverlapExcess` が kernel-check された。
- survivor / incidence / window / overlap の exact conservation がある。
- supplied overlap lower bound を使う conditional survivor criterion が、無理なく取れるなら追加された。
- universal survivor existence を主張していない。
- focused build 成功。
- axiom audit で `sorryAx` / 新規公理なし。
- `report-004.md` を残す。
