# CGE-001: Even-Fiber Escape と完全有限素数認証の実装指示

## 目的

CGE-000 では、二つの full-coordinate 宇宙式

\[
Big_i = Body_i + Gap_i
\]

の Gap を交換したとき

\[
CrossLeft + CrossRight = PairedBig
\]

が厳密に保存されることを Lean に固定した。
また prime degree に対して foreign Gap が residue を輸送することも確認したが、
prime certification 自体は得られず、Outcome B — STRUCTURAL CONSERVATION ONLY で終了した。

CGE-001 では次の一段だけ進める。

**固定 even fiber `PairedBig = 2*n` 上で、Cross-Gap 出力が「全ての小素数 obstruction を回避した」ことと「両出力が prime である」ことの exact bridge を作る。**

この段階でも Strong Goldbach の全称存在証明は狙わない。
狙うのは、

> 各 even fiber に一つ survivor が存在すれば、その一点だけで Goldbach pair が得られる

という「one-hole principle」の認証側を、primality を定義に埋め込まずに形式化することである。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

---

## 背景と今回の視点

CGE-000 の定義をそのまま使う。

\[
Body_i := x_i GN_{d_i}(x_i,u_i)
\]

\[
Gap_i := u_i^{d_i}
\]

\[
Big_i := (x_i+u_i)^{d_i}
\]

\[
CrossLeft := Body_1 + Gap_2
\]

\[
CrossRight := Body_2 + Gap_1
\]

そして

\[
PairedBig := Big_1 + Big_2.
\]

CGE-000 により常に

\[
CrossLeft + CrossRight = PairedBig.
\]

したがって fixed even fiber

\[
PairedBig = 2n
\]

を仮定すれば

\[
CrossLeft + CrossRight = 2n.
\]

Goldbach は全 prime pair の分類を要求しない。
各 `n` に対して一つでも両出力が prime となる Cross-Gap configuration が存在すれば十分である。

今回の狙いはその prime pair の**存在を証明することではなく**、
「候補一点が composite obstruction をすべて回避したなら、その一点は本当に prime pair である」ことを exact theorem にすることである。

---

## 重要な区別

### 1. `Coprime` は prime pair ではない

例えば

\[
25+27=52,\qquad \gcd(25,27)=1
\]

だが両方 composite である。

したがって

\[
Nat.Coprime\; CrossLeft\; CrossRight
\]

だけを prime certification として使ってはいけない。

### 2. diagonal prime pair は coprime でない

例えば

\[
3+3=6
\]

は正しい Goldbach pair だが

\[
\gcd(3,3)=3.
\]

したがって「Goldbach pair = primitive pair」と同一視しない。
primitive / ABC-like viewpoint は off-diagonal prime pair の corollary として扱う。

### 3. obstruction は proper divisor でなければならない

既存 `GoldbachProperObstructed` と同様、
prime endpoint 自身による divisibility を obstruction と数えてはいけない。

例えば endpoint が `3` なら `3 ∣ 3` だが、これは composite obstruction ではない。

---

## 既存 API の優先再利用

必ず repository-first で以下を確認して使うこと。

- `DkMath.NumberTheory.Goldbach.CrossGapExchange`
- `DkMath.NumberTheory.Goldbach.Obstruction`
- `DkMath.NumberTheory.Goldbach.Basic`

特に `Obstruction.lean` の以下を再利用する。

- `goldbachSmallPrimes`
- `mem_goldbachSmallPrimes`
- `goldbach_small_prime_witness`
- `goldbach_no_proper_divisor_of_prime`
- 必要なら既存 `GoldbachProperObstructed`

既存 offset `u` 専用 theorem を無理に rewrite して使うより、
Cross-Gap endpoint に対する generic pair lemma を一段設けた方が綺麗ならそうしてよい。
ただし同じ small-prime argument を別名で大量複製しないこと。

---

## production owner

候補:

`DkMath/NumberTheory/Goldbach/CrossGapEscape.lean`

`CrossGapExchange.lean` は保存則 owner のまま保ち、
small-prime obstruction / escape / certification は別 module に分けることを推奨する。

必要なら facade `DkMath/NumberTheory/Goldbach.lean` に import を追加する。

---

## 最小 structural predicate

prime を定義に埋め込まない。

候補として fixed even fiber の structural condition を用意する。

```lean
CrossGapEvenFiberAt
```

概念的には

\[
PairedBig = 2n
\]

かつ prime-candidate endpoint として必要な

\[
2 \le CrossLeft,\qquad 2 \le CrossRight
\]

を保持する。

full coordinates `(d₁,x₁,u₁,d₂,x₂,u₂)` は維持する。
この段階で `x=1` に潰さない。

必要ならこの predicate を作らず theorem hypotheses のまま持ってもよい。
API の可読性を優先して判断すること。

---

## CGE-001 必須 theorem 群

### CGE-001-A: even-fiber endpoint bounds

fixed even fiber

\[
PairedBig = 2n
\]

と

\[
2\le CrossLeft,\qquad 2\le CrossRight
\]

から、保存則を使って

\[
CrossLeft\le 2n,\qquad CrossRight\le 2n
\]

を得る。

これは後段の `goldbach_small_prime_witness` の upper bound に使う。

---

### CGE-001-B: Cross-Gap proper obstruction

Cross-Gap endpoint 用に、必要なら次の意味の predicate を導入する。

\[
CrossGapProperObstructed(r)
\]

iff

\[
(r\mid CrossLeft \land CrossLeft\ne r)
\lor
(r\mid CrossRight \land CrossRight\ne r).
\]

候補名は自由だが、既存 `GoldbachProperObstructed` と意味がずれないようにする。

prime endpoint 自身を obstruction に数えないこと。

---

### CGE-001-C: failure iff finite obstruction

今回の中心 theorem。

fixed even fiber と endpoint lower bounds の下で、

\[
\neg(Prime(CrossLeft)\land Prime(CrossRight))
\]

iff

\[
\exists r\in goldbachSmallPrimes(n),\quad
CrossGapProperObstructed(r).
\]

を証明する。

これは既存 `goldbach_not_prime_pair_iff_obstructed` の Cross-Gap endpoint 版である。
ただし既存 theorem は canonical offset `(n-u,n+u)` 用なので、
Cross-Gap pair を無理に offset へ変換しなくてもよい。

証明の算術核は既存

`goldbach_small_prime_witness`

を使うこと。

---

### CGE-001-D: survivor predicate and exact certification

prime を直接含まない survivor predicate を用意する。

概念形:

\[
CrossGapSurvives(n,\ldots)
:\Longleftrightarrow
\forall r\in goldbachSmallPrimes(n),
\neg CrossGapProperObstructed(r).
\]

そして fixed even fiber 上で

\[
\boxed{
CrossGapSurvives
\iff
Prime(CrossLeft)\land Prime(CrossRight)
}
\]

を証明する。

これが CGE-001 の prime-certification endpoint である。

重要:

- survivor の**存在**は証明しない。
- survivor predicate に `Nat.Prime` を入れない。
- exact finite obstruction elimination から primality が後から出る形にする。

---

### CGE-001-E: one-hole implication to Goldbach

次の implication を production theorem にする。

fixed even fiber 上に Cross-Gap survivor が一つ与えられたなら

\[
GoldbachPairAt(n)
\]

が従う。

概念形:

```lean
CrossGapEvenFiberAt n ... ->
CrossGapSurvives n ... ->
GoldbachPairAt n
```

これは Strong Goldbach の証明ではない。
「一つ survivor があれば十分」という終端 bridge である。

可能なら theorem statement は `CrossLeft`, `CrossRight` を witness として直接返す形にする。

---

## off-diagonal primitive / ABC-like corollary

今回の本線ではないが、簡潔に取れるなら追加してよい。

fixed even fiber 上で両 cross outputs が prime かつ unequal なら

\[
\gcd(CrossLeft,CrossRight)=1.
\]

さらに

\[
CrossLeft+CrossRight=2n
\]

から

\[
\gcd(CrossLeft,2n)=1,
\qquad
\gcd(CrossRight,2n)=1
\]

を導けるなら theorem 化してよい。

これは

\[
a+b=c=2n
\]

の prime-prime even fiber が off-diagonal では primitive ABC triple 型になる、という補助的整理である。

ただし以下を明記すること。

- ABC 予想を使わない。
- ABC quality / radical bound を導入しない。
- diagonal `p+p=2p` は primitive triple ではない。
- `Coprime` から primality を逆向きに導かない。

---

## audit / regression

最低限以下を audit module で確認する。

1. `25 + 27 = 52` かつ `Nat.Coprime 25 27` だが両 prime ではない。
   - coprime-only firewall。

2. `3 + 3 = 6` は prime pair だが `Nat.Coprime 3 3` ではない。
   - diagonal firewall。

3. 一つ具体的な cross-gap configuration で
   - `CrossLeft + CrossRight = PairedBig`
   - pairedBig が偶数 target `2*n`
   - small-prime survivor theorem の hypotheses / conclusion
   を replay する。

具体的 configuration で prime survivor が簡単に作れない場合、無理に作らない。
条件付き theorem の replay だけでよい。

---

## この段階でやらないこと

1. Strong Goldbach の全称存在証明。
2. `∃ configuration, CrossGapSurvives` の無条件全称 theorem。
3. CRT / Capacity / PairOverlap の再導入。
4. Cross-Gap parameter space の巨大な Finset 列挙。
5. prime density / RH / CFBRC の接続。
6. SquareBody certification との接続。
7. equal-prime-degree residue surjectivity の深掘り。
8. ABC quality / radical 解析。
9. `Coprime` を prime certification として使うこと。
10. `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom`。

今回は**認証終端だけ**を固定する。
探索空間・存在 provider は次段階に分離する。

---

## 判定基準

実装後 `report-001.md` を作り、次のどれかを判定する。

### Outcome A — EXACT CROSS-GAP CERTIFICATION BRIDGE

Cross-Gap fixed-even fiber について、prime を定義に埋め込まず
small-prime obstruction escape と両 endpoint primality の exact equivalence が得られ、
`GoldbachPairAt` への one-hole implication が production theorem として閉じた。

これは Goldbach existence の進展とは数えないが、次段階の探索 provider に使える独立 API と評価する。

### Outcome B — GENERIC FINITE-SIEVE REPACKAGING

定理は正しいが、実質的には既存 `Obstruction.lean` の generic endpoint 版であり、
Cross-Gap 固有の新算術情報は増えていない。

この場合も API として有用なら保持してよい。

### Outcome C — COLLAPSE TO EXISTING OFFSET FIBER

Cross-Gap endpoint を canonical Goldbach offset に変換するだけで全 theorem が既存 API に完全吸収され、
新 module を維持する価値が低い。

この場合は production 追加を最小化し、report でその理由を明記する。

---

## report-001.md に書くこと

- 追加・変更ファイル
- theorem 一覧
- fixed-even fiber の exact hypotheses
- obstruction iff failure theorem の statement
- survivor iff prime-pair theorem の statement
- one-hole -> `GoldbachPairAt` bridge
- off-diagonal coprime corollary を追加した場合はその範囲
- coprime-only / diagonal firewall の regression
- focused build / facade build 結果
- `#print axioms`
- 禁止構文 grep
- Outcome A/B/C
- 次段階で必要な「survivor existence provider」が何であるかを一文で記す

---

## CGE-001 完了条件

以下を満たしたら停止する。

- `PairedBig = 2*n` から cross outputs の upper bound を得た。
- Cross-Gap proper obstruction を prime を使わず表現した。
- failure iff finite small-prime obstruction を kernel-check した。
- survivor iff both outputs prime を kernel-check した。
- survivor 一点から `GoldbachPairAt n` を得る theorem を作った。
- existence provider には踏み込んでいない。
- focused build 成功。
- axiom audit で `sorryAx` / 新規公理なし。
- `report-001.md` を残した。

次段階ではこの終端 bridge を前提に、**fixed even fiber の Cross-Gap parameter space に survivor が一つ残るための非自明な provider**だけを探索する。