# PRIM-ST-000: square-shell exact wave transport / prime-world growth audit

日付: 2026-08-25
対象 branch: `wip/number-theory/primitive-structure-260822-v2`
環境: Lean / Mathlib v4.32.2

## 0. 監査の境界

この文書は、`n` から `n + 1` への square anchor の移動と、有限 prime world の
変化を既存 API 上で照合する read-only reconnaissance の結果である。Lean ソース、
定理文、import、facade、toolchain、Lake 設定、既存の Legendre 層は変更していない。
新しい shell-transport 定義や follow-up implementation も追加していない。

この監査でいう「正確」は、整数等式、合同式、既存の有限集合 API が直接表す内容に
限る。二つの shell の同じ cardinality、周期性、あるいは有限 prime world の抽象的な
refinement だけから、full cover の隣接 shell 間輸送や descent は推論しない。

## 1. Executive outcome

**Outcome C — TAUTOLOGICAL TRANSLATION / NO NEW LEVERAGE** と判定する。

得られた事実は次の三つに整理できる。

1. 禁止 residue の phase は
   `A_q(n) := squareAnchorForbiddenResidue n q` と置けば、
   `A_q(n+1) + (2*n+1) ≡ A_q(n) [MOD q]`、および
   `A_q(n+q) = A_q(n)` を満たす。
2. 点の恒等式
   `(n+1)^2 + r = n^2 + (2*n+1+r)` は exact だが、右辺の offset は旧 shell
   `1 .. 2*n` の外へ出る。したがってこれは extended offset window への
   書き換えであって、二つの `squareOffsets` 間の transport ではない。
3. `n+1` が prime の場合、`primeScalesUpTo` は一方向だけ refine される。既存の
   `PrimeWorldRefinement` はこの有限世界の child 座標を与えるが、その座標
   `r + j * primeWorldModulus S` は shell の移動量 `2*n+1` と一致しない。

従って、隣接 shell の二つの full-cover 仮定を結合する新しい deficit、旧 witness
の輸送、あるいは小さい fully-covered shell の再構成は得られない。推奨は **stop
route** である。上の recurrence と case split は report-level の exact coordinate
として保持できるが、この checkpoint で Lean 定義へ昇格させる理由はない。

## 2. Repository theorem inventory

### 2.1 Square-anchor / Legendre 層

`DkMath.NumberTheory.Legendre.Basic` で確認した主要な宣言は次の通りである。

| 宣言 | 監査での意味 |
| --- | --- |
| `SquareOffset n r` | `1 ≤ r ∧ r ≤ 2*n` という shell offset |
| `SquareOffsetForbiddenBy n q r` | `q ∣ n^2 + r` という一方向の禁止条件 |
| `squareOffsetCovered_iff_exists_prime_dvd` | shell seat の cover と prime divisor の存在の同値 |
| `supportDisjointFrom_primeScalesUpTo_square_add_iff_not_covered` | finite prime world と square shell の非 cover の同値 |
| `squareAnchorForbiddenResidue n q` | `q` に対する canonical forbidden residue |
| `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue` | `0 < q` のもとで `q ∣ n^2+r` と `r % q = squareAnchorForbiddenResidue n q` の同値 |

最後の定理が、phase を quadratic character へ落とさず exact residue のまま使う
既存の point of contact である。`Basic` の現行 import に、今回のための新しい
quadratic-reciprocity 層や `ZMod` 層はない。

### 2.2 Wave / packet 層

`DkMath.NumberTheory.Legendre.Wave` では、`squareWaveOffsets`、その membership、
`card_squareWaveOffsets_eq_div_sub_div`、および full-cover から得られる wave の
occupancy / carry inequality を確認した。これらは固定 anchor の wave ledger であり、
`n` と `n+1` の二つの shell を直接結ぶ successor theorem ではない。

`CoprimePacket` では次を確認した。

* `squareAnchorCoprimeOffsets` は `squareOffsets n` から `Nat.Coprime n r` の offset
  を抽出する。
* `card_squareAnchorCoprimeOffsets` は `0 < n` のもとで `2 * Nat.totient n` を与える。
* `squareAnchorCoprimeOffsets_eq_base_union_shift` は base と shifted packet の分解を与える。
* `squareOffsetCovered_iff_anchorNondivisor_of_coprime` は coprime seat の cover を
  anchor の nondivisor prime support に接続する。
* `squareOffsetAnchorNondivisorSupport` と
  `squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime` は、固定 shell 内の
  prime incidence を整理する。

`PacketCross` と `PacketCoprimality` では、packet の congruence、cross-factor の
  determinant、同じ packet point を同時に割れないことを確認した。これらは一つの
  anchor の packet 内構造であり、anchor を一つ進めたときの support-preserving map
  ではない。

`Frontier` の
`legendreConjecture_iff_squareAnchoredSupportEscape` と
`legendreConjecture_iff_squareOffsets_not_fully_covered` は、Legendre conjecture と
square-shell full cover の既存の frontier equivalence である。今回の recurrence
からこの frontier を越える定理は存在しない。

### 2.3 Finite prime-world 層

`FinitePrimeWorld` で確認した宣言は、

* `primeScalesUpTo P` と `mem_primeScalesUpTo`,
* `knownPrimeScales_primeScalesUpTo`,
* `supportDisjointFrom_primeScalesUpTo_iff`

である。`primeScalesUpTo P` は `q ≤ P` の prime の finite set である。

`PeriodicPrimeWorld` では `primeWorldModulus S` と、additive period、multiplicative
period、centered mirror、prime-world modulus による coprimality / residue periodicity
の API を確認した。これらは support の周期性を与えるが、square shell の interval
`1 .. 2*n` を successor shell の interval へ送る API ではない。

`PrimeWorldRefinement` では次の宣言を確認した。

* `supportDisjointFrom_insert_prime_iff`
* `knownPrimeScales_insert`
* `primeWorldModulus_insert`
* `prime_coprime_primeWorldModulus_of_not_mem`
* `primeWorldChild`, `primeWorldChildIndices`
* `reservedChildIndices`, `survivingChildIndices`
* `supportDisjointFrom_child_iff`
* `supportDisjointFrom_insert_prime_child_iff`
* `existsUnique_child_dvd_new_prime`
* `reservedChildIndices_eq_singleton`
* `card_survivingChildIndices`

ここで child は `r + j * primeWorldModulus S` であり、new prime direction が
有限 observer の child のうちちょうど一つを reserve する、という抽象的な refinement
である。`existsUnique_child_dvd_new_prime` も old certified world、fresh prime、
旧 modulus 内の base coordinate という仮定の定理であって、square-shell point の
定理ではない。

`PrimeWorldResidues` の
`exists_primeWorldChild_coordinates_of_lt_mul_modulus`、
`mem_refined_primeWorldResidues_iff`、`refinedSurvivingSeats_primeWorldResidues_eq`
も確認した。これらは有限 world residue の座標分解であり、shell point
`n^2+r` の座標分解を主張しない。

## 3. Q1 — exact forbidden-phase recurrence

### 3.1 report-local notation と最小の証明連鎖

以下で

```text
A_q(n) := squareAnchorForbiddenResidue n q.
```

と書く。定義は canonical representative

```text
A_q(n) = (q - (n^2 % q)) % q
```

という形である。`q > 0` のもとで平方の加法差
`(n+1)^2 = n^2 + (2*n+1)` と `Nat.ModEq` の加法・乗法互換性を順に使うと、

```text
A_q(n+1) + (2*n+1) ≡ A_q(n) [MOD q].
```

を得る。意味は、new-anchor の forbidden residue を old-anchor の residue に戻す
とき、increment `2*n+1` を引く、というものである。この向きは
`squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue` の phase と整合する。

### 3.2 canonical `%` equality

各 `A_q(k)` は `q` 未満の canonical residue なので、上の合同式は次の report-level
の自然数等式に変換できる。

```text
A_q(n) = (A_q(n+1) + (2*n+1)) % q.
```

ここでは右辺全体を `% q` に入れることが重要であり、mod を外した通常の等式とは
言っていない。逆向きの表現も、`(A_q(n) - ((2*n+1) % q)) % q` のように canonical
modulo の形でのみ安全である。

### 3.3 anchor period

同じ chain に `n+q ≡ n [MOD q]` を適用すると、canonicality により

```text
A_q(n+q) = A_q(n).
```

が exact equality になる。これは `A_q` を新しい API として導入しなくても、既存の
forbidden-residue theorem と自然数の modulo lemmas の thin composition で導ける。

### 3.4 classification

| 結果 | 分類 | 意味 |
| --- | --- | --- |
| phase recurrence | B | 既存の定義、平方差、`Nat.ModEq` の薄い合成。公開の successor theorem は未確認 |
| canonical `%` equality | B | `Nat.ModEq` と canonical residue の薄い合成 |
| `A_q(n+q)=A_q(n)` | B | modulo periodicity と canonicality の薄い合成 |

この recurrence 自体は exact だが、新しい semantic bridge ではない。

## 4. Q2 — exact point transport

整数等式としては

```text
(n+1)^2 + r = n^2 + (2*n+1+r).
```

が成立する。従って任意の自然数 `q` について、rewriting だけで

```text
q ∣ (n+1)^2 + r
  <-> q ∣ n^2 + (2*n+1+r)
```

を得る。これは fixed `q ≤ n` に対しても同じであり、既存の support predicate に
対しては「同じ整数を別の anchor と offset で表示した」だけである。

しかし `1 ≤ r ≤ 2*(n+1)` なら shifted offset は

```text
2*n+1+r ∈ [2*n+2, 4*n+4].
```

旧 `SquareOffset n s` の範囲は `1 ≤ s ≤ 2*n` なので、shifted coordinate は旧
shell の外にある。従って、次のような主張はこの恒等式からは出ない。

```text
r ∈ squareOffsets (n+1) -> 2*n+1+r ∈ squareOffsets n.
```

正しい分類は次の通りである。

* extended offset window への transport としては exact。
* point identity / divisibility rewriting としては tautological な B。
* 二つの実際の `squareOffsets` Finset を結ぶ transport としては C、すなわち semantic
  bridge がない。

特に shifted coordinate を旧 shell の offset と名前だけ変えて扱うことはできない。

## 5. Q3 — finite prime-world evolution

### 5.1 `n+1` が prime でない場合

`mem_primeScalesUpTo` により、任意の `p` について

```text
p ∈ primeScalesUpTo (n+1) <-> Nat.Prime p ∧ p ≤ n+1
p ∈ primeScalesUpTo n     <-> Nat.Prime p ∧ p ≤ n
```

である。`n+1` が prime でなければ、この membership characterization と `p ≤ n+1`
の場合分けから

```text
primeScalesUpTo (n+1) = primeScalesUpTo n.
```

が finset extensionality の薄い合成として得られる。これは world の exact equality
であるが、shell の point identity ではない。

### 5.2 `q := n+1` が prime の場合

`Nat.Prime q` と `q=n+1` なら `q ∉ primeScalesUpTo n` であり、membership
characterization から

```text
primeScalesUpTo q = insert q (primeScalesUpTo n).
```

が finset extensionality で得られる。既存の refinement API をそのまま適用できる。

```text
supportDisjointFrom_insert_prime_iff
primeWorldModulus_insert
existsUnique_child_dvd_new_prime
reservedChildIndices_eq_singleton
card_survivingChildIndices
```

ただし `primeWorldModulus_insert` には q の freshness が必要であり、上の `q=n+1`
と `q ∉ primeScalesUpTo n` がその仮定を供給する。これにより new q direction の
抽象 child 一つと surviving child `q-1` 個が記述される。

### 5.3 shell との alignment

world refinement の child は

```text
r + j * primeWorldModulus (primeScalesUpTo n),  0 ≤ j < q
```

である。一方、new shell の point movement は `2*n+1` であり、shell offset の
movement は `2*n+1+r` である。一般には `2*n+1` は old primorial modulus の倍数
ではなく、十分大きい `n` では modulus より小さいことすら通常である。従って既存
refinement theorem は finite world の refinement を与えるが、actual square-shell
position との alignment を与えない。

| step | prime-world movement | square-anchor movement | application-level alignment |
| --- | --- | --- | --- |
| non-prime `n+1` | 同じ `primeScalesUpTo` | `+2*n+1` | なし |
| prime `q=n+1` | `insert q`、modulus は fresh q 倍 | new shell は `q^2+1 .. (q+1)^2-1` | 一般にはなし |

## 6. Q4 — new-prime wave at a prime anchor

`q := n+1` が prime なら、anchor が q の shell では

```text
q ∣ q^2+r <-> q ∣ r.
```

新 shell の `1 ≤ r ≤ 2*q` では q の倍数は `q` と `2*q` のちょうど二つである。
従って新しい q-wave の incidence は正確に二つである。

これは「二つの seat が q によって新たに covered された」という意味ではない。旧
prime `p < q` の wave が q や `2*q` を既に cover する可能性があるため、new q-wave
の incidence と newly covered seat は別である。

逆に `Nat.Coprime q r` なら q は `q ∣ r` を満たさない。したがって new shell が
full covered であるという仮定の下では、coprime seat は q 以外の prime によって
cover される。有限 shell の divisor は `≤ q` であり、q 自身は coprime seat を
割らないので、その witness は必ず `p < q` である。これは
`squareOffsetCovered_iff_anchorNondivisor_of_coprime` と
`squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime` が既に表している
内容の q-prime specialization である。

なお q prime なら、coprime offsets の個数は
`2 * Nat.totient q = 2*(q-1)` である。これは exact ledger だが、old prime waves
がこの全体を同時に cover できないという new deficit までは与えない。

**分類:** A ではなく、既存定理への薄い specialization と B の算術書き換えである。

## 7. Q5 — shell `q-1` と prime shell `q` の coprime part

q prime のとき、cardinality は

```text
card (squareOffsets (q-1)) = 2*(q-1)
card (squareAnchorCoprimeOffsets q) = 2*Nat.totient q = 2*(q-1).
```

と一致する。しかし support-preserving matching は得られない。

旧 shell の offset は `1 .. 2*q-2` であり、そこには q が含まれる。新 shell の
coprime part は `1 .. 2*q` から q と `2*q` を除く。従って

```text
old-only = {q}
new-only = {2*q-1}
```

となり、共通部分は `1 .. 2*q-2` から q を除いたものにすぎない。q を `2*q-1`
へ置き換える set-theoretic bijection は作れるが、これは単なる cardinality の
補正である。

さらに actual points は

```text
old: (q-1)^2 + r
new: q^2 + s
```

であり、二つの intervals 自体が隣接しているだけで同じ point ではない。offset を
identity で対応させても、prime `p < q` に対する divisibility は anchor shift
`2*q-1` により変化する。q を別の offset に置き換える候補も、全 old-prime support
を保存する理由を持たない。

従って bare cardinality equality は matching theorem ではない。

**分類:** **C — no useful transport exists**。

## 8. Q6 — 固定 prime の anchor-phase orbit

固定 prime p に対して `A_p(n)` は `n mod p` だけに依存し、Q1 の periodicity

```text
A_p(n+p) = A_p(n)
```

を満たす。一周期 `0 ≤ n < p` における像は、p が奇 prime の場合、

```text
{-x^2 mod p | x ∈ F_p}
```

である。したがって次の通りである。

| phase の種類 | 個数 / multiplicity（奇 prime p） |
| --- | --- |
| distinct phase 全体 | `(p+1)/2` |
| zero phase | 1 個、multiplicity 1 |
| 非零で像に入る phase | `(p-1)/2` 個、各 multiplicity 2 |
| 非零で像に入らない phase | `(p-1)/2` 個 |

zero は `n ≡ 0 mod p` の一度だけ現れる。非零 phase は `n` と `-n` の二つの
anchor residue から来る。p=2 だけは二つの phase がそれぞれ一度現れる。

この像は square-residue projection の符号反転であり、quadratic-character audit が
既に失っていた exact wave 情報を回復するものではない。つまり、phase multiplicity
は「平方 residue が二回現れる」という既知の事実の再記述である。一周期を跨ぐ
二つの shell の full-cover を結ぶ新しい不等式や incompatibility は生じない。

**分類:** B の exact periodic coordinate だが、application leverage は redundant。

## 9. Q7 — consecutive full-cover transport test

監査上だけ

```text
SquareOffsetsFullyCovered n
SquareOffsetsFullyCovered (n+1)
```

を仮定する。二つの仮定はそれぞれ異なる interval の各 point に対する cover で
あり、Q1 の phase recurrence だけでは一方から他方への witness map にならない。

### 9.1 non-prime step

`n+1` が prime でなければ prime world は同じである。しかし new shell の seat `r`
に対する old-anchor coordinate は `2*n+1+r` であり、old shell の上限 `2*n` を越える。
同じ prime divisor q が両方の整数を割ることは点の恒等式から言えるが、old shell
の witness として再利用できるとは言えない。

### 9.2 prime insertion step

`q=n+1` が prime なら world は `insert q` で refine される。new q-wave は q と
`2*q` の二 incidence に限られ、残る coprime seats は old primes の cover を要求
する。しかし、これも q-shell の point ごとの statement であって、q-1 shell の
witness を q-shell へ送る statement ではない。`PrimeWorldRefinement` の surviving
child は shell seat ではない。

### 9.3 witness、fresh hole、packet、union count

* old support witness を transport するには、shifted offset が旧 shell に戻る map、
  または support を保存する point correspondence が必要だが、いずれもない。
* 一方の shell の fresh hole は、別の anchor で同じ residue phase を持つとは限らない。
  phase の周期性は anchor modulo q の一致であって、隣接 anchor の一致ではない。
* packet coprimality は同じ anchor の points 間の gcd / support 条件である。anchor
  shift は points と packet coordinates を同時に変えるため、shell 間の preserved
  packet theorem にはならない。
* 二 shell の cardinality を足しても、同じ prime wave が両 shell でどう overlap
  するかの upper/lower bound がない。既存の各 shell ledger を二つ並べる以上の
  strict count deficit は確認できない。

従って、二つの full-cover hypotheses はこの API inventory 上では独立な仮定のままで
あり、同時成立から新しい矛盾は得られない。

## 10. Q8 — least-counterexample / descent test

`n` を full cover を持つ least positive anchor と仮定しても、shell transport から
`m < n` の full cover は再構成できない。

不足しているものは明確である。

1. shifted coordinate `2*n+1+r` は旧 shell の bounded state ではない。
2. 同じ prime world、phase periodicity、あるいは `k ≤ n` の small-cofactor 情報は、
   小さい shell の全 seat の cover を保存しない。
3. `card (squareOffsets (q-1)) = card (squareAnchorCoprimeOffsets q)` は、support を
   保存する bijection でも point の再構成でもない。
4. strict measure の減少と、cover hypothesis を保存する reconstruction theorem が
   ない。

よって least-counterexample からの descent は invalid である。`SmallCofactor` にある
「old-generated または unique fresh nontrivial small cofactor」という分岐も、cofactor
の bound を与えるだけで、smaller fully-covered shell を与えない。

## 11. Q9 — `PrimeWorldRefinement` との相互作用

既存 refinement の canonical child は

```text
primeWorldChild S r j = r + j * primeWorldModulus S,
0 ≤ j < q.
```

である。Legendre の隣接 anchor の displacement は

```text
2*n+1.
```

であり、new shell の offset coordinate ではさらに `2*n+1+r` となる。この二つは
一般には同じ剰余類座標系ではない。特に `2*n+1` が old modulus の倍数だと仮定する
理由はなく、large `n` では通常 old modulus より小さい。

従って `PrimeWorldRefinement` の提供範囲は次のように分類される。

| 問い | 判定 |
| --- | --- |
| actual shell の direct transport | なし |
| finite world の abstract refinement | あり |
| prime insertion step での shell bridge | new q-wave の二 incidence と old-prime cover の分類までは可能だが、shell transport bridge ではない |

`existsUnique_child_dvd_new_prime` が与える一意性は、old certified world の residue
child 内の一意性である。これを q-shell の actual positions の一意性へ読み替える
ことはできない。

## 12. anchor movement と prime-world movement の分離

| 層 | exact movement | 既存 API で言えること | 言えないこと |
| --- | --- | --- | --- |
| anchor phase | `A_q(n+1)+(2*n+1) ≡ A_q(n)` | forbidden residue の canonical phase transport | shell full-cover の transport |
| anchor period | `A_q(n+q)=A_q(n)` | q 周期 | 隣接 shell の phase 一致 |
| point | `(n+1)^2+r=n^2+(2*n+1+r)` | 同じ integer の divisibility rewriting | shifted point が旧 shell に属すること |
| non-prime world | `primeScalesUpTo(n+1)=primeScalesUpTo n` | same finite prime world | same shell witness |
| prime world | `primeScalesUpTo q=insert q (...)` | new q の finite refinement | q-child と q-shell seat の一致 |
| q-wave | `q∣q^2+r ↔ q∣r` | `r=q,2*q` の二 incidence | 二 seat が newly covered であること |
| packet | `2*totient q=2*(q-1)` | coprime seat の count | old shell との support-preserving bijection |
| child coordinates | `r+j*M` | abstract finite-world residue refinement | shell displacement `2*n+1` との一般 alignment |

この分離が、今回の「anchor を動かす」視点で新たに確認できる主な境界である。

## 13. Rejected false transports

次の推論は、この監査では採用しない。

* `A_q(n+q)=A_q(n)` から、q 個隣の shell が同じ cover pattern を持つとすること。
  phase は一方向の residue であり、shell point interval と prime incidence 全体を
  同一視しない。
* `(n+1)^2+r=n^2+(2*n+1+r)` から、`r` を旧 `squareOffsets n` の seat とすること。
  shifted coordinate は旧 shell の外である。
* `primeScalesUpTo` の insertion と `PrimeWorldRefinement` の child を、q-shell の
  actual integer points と同一視すること。
* `2*(q-1)` の cardinality equality から、old shell と q-shell coprime part の
  support-preserving bijectionを推論すること。
* new q-wave の二 incidence から、二つの newly covered seats、または old primes の
  deficit を推論すること。
* `k ≤ n`、同じ prime world、bounded shifted offset、packet count のいずれかから、
  smaller full-covered shell を推論すること。
* 二つの独立 full-cover ledger を足すだけで、union 上の strict deficit が得られると
 すること。

## 14. Final recommendation

今回の結果は **Outcome C — TAUTOLOGICAL TRANSLATION / NO NEW LEVERAGE** である。

推奨は **stop route**。Q1 の recurrence、Q3 の prime/non-prime case split、Q4 の
new q-wave の二 incidence は、将来別の意味論的 bridge が見つかった場合に参照できる
exact coordinate としてこの report に保持する。ただし現時点でこれらを Lean の新しい
public definition / theorem に実装しても、既存の `Basic`、`Wave`、`CoprimePacket`、
`PrimeWorldRefinement` の内容を超える full-cover obstruction、descent、または
Legendre conjecture の証明には接続しない。

この checkpoint の成果物は本 report のみであり、Lean build は実施していない。
