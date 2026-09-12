# CGE-000: Cross-Gap Exchange 基礎構造の実装指示

## 目的

この campaign では、前 campaign `wip/fixed-big-arithmetic-gauge-260912-v0` で試した
`pairBody = 2n` 型の狭い固定をいったん離れ、**二つの宇宙式が持つ Gap を交換したときに
総 Big が保存される構造**を独立 API として Lean に固定する。

Goldbach の一般証明をこの段階で狙わない。
まずは、prime 仮定を入れずに成立する保存式・交換則・involution・residue transport を
production theorem として整備し、その後に prime certification の不足点を監査する。

作業 branch:

`wip/goldbach-cross-gap-exchange-260913-v0`

起点は現在の `develop` とする。

---

## 背景

単一の宇宙式は

\[
(x+u)^d = x\,GN_d(x,u) + u^d
\]

を持つ。

この campaign では以下を基本成分とする。

\[
Body(d,x,u) := x\,GN_d(x,u)
\]

\[
Gap(d,u) := u^d
\]

\[
Big(d,x,u) := (x+u)^d
\]

したがって常に

\[
Big = Body + Gap.
\]

二つの宇宙

\[
U_1=(d_1,x_1,u_1),\qquad U_2=(d_2,x_2,u_2)
\]

を重ねると、総保存量は

\[
PairedBig := Big_1 + Big_2.
\]

ここで Gap だけを交換して、二つの cross output を

\[
CrossLeft := Body_1 + Gap_2,
\]

\[
CrossRight := Body_2 + Gap_1
\]

と定義する。

核となる保存式は

\[
\boxed{
CrossLeft + CrossRight = Big_1 + Big_2
}
\]

である。

これは Goldbach を仮定しない純粋な代数恒等式である。

---

## 重要な解釈

この campaign では `2n` を `pairBody` に置かない。

必要であれば後段で

\[
2n = PairedBig
\]

と置き、その保存量を Gap 交換によって

\[
2n = CrossLeft + CrossRight
\]

へ再分解する。

したがって今回の prime 候補は GN 単体ではなく、概念的には

\[
x_1GN_{d_1}(x_1,u_1) + u_2^{d_2}
\]

および

\[
x_2GN_{d_2}(x_2,u_2) + u_1^{d_1}
\]

である。

前 campaign の `PairGN.lean` は unit-boundary `x=1` と `pairBody = 2n` を主に扱っていた。
今回の CGE では **full coordinate `(d,x,u)` を保つこと**。
`x=1` への特殊化は後段の corollary / regression に限定する。

---

## CGE-000 の実装範囲

### 1. production owner

新規 production module を Goldbach 配下に置く。
候補:

`DkMath/NumberTheory/Goldbach/CrossGapExchange.lean`

必要に応じて facade `DkMath/NumberTheory/Goldbach.lean` へ import を追加する。

既存の `BodyN`, `GN`, `cosmic_id_csr'` などを再利用し、同義定義を増やしすぎないこと。
ただし Cross-Gap API の可読性のために軽量 wrapper を置くことは可。

### 2. 最小定義

以下は候補名であり、既存名と衝突する場合は調整してよい。

```lean
crossGapBody
crossGapGap
crossGapBig
pairedBig
crossLeft
crossRight
```

可能なら 3-tuple / structure を導入せず、最初は単純な定義で進める。
抽象化は theorem shape が安定してから行う。

### 3. 必須 theorem

最低限、次を production theorem として証明する。

#### CGE-001: single-universe conservation

\[
Body_i + Gap_i = Big_i.
\]

既存 CosmicFormula theorem の単なる facade でよい。
新しい数学を作らない。

#### CGE-002: cross-gap total conservation

\[
CrossLeft + CrossRight = PairedBig.
\]

これが今回の中心定理。

#### CGE-003: paired decomposition

\[
PairedBig = Body_1 + Body_2 + Gap_1 + Gap_2
\]

加法結合順序は Lean 上扱いやすい形にしてよい。

#### CGE-004: swap symmetry / involution

二つの宇宙を入れ替えると `CrossLeft` と `CrossRight` が交換されること。
また Gap 交換を二度行うと元の割当へ戻ることを、無理なく表現できる範囲で theorem 化する。

巨大な permutation framework は不要。

#### CGE-005: fixed locus

少なくとも

\[
Gap_1 = Gap_2
\]

なら cross output が元の各 Big から Gap 差による移動を受けないことを整理する。
可能なら

\[
Body_1=Body_2 \land Gap_1=Gap_2
\]

のとき

\[
CrossLeft=CrossRight
\]

を固定点として theorem 化する。

### 4. signed transfer view

自然数減算で情報を失わないよう、必要なら `ℤ` へ持ち上げて

\[
\Delta := Gap_2 - Gap_1
\]

を定義または theorem 内だけで使う。

期待する関係は

\[
CrossLeft = Big_1 + \Delta,
\]

\[
CrossRight = Big_2 - \Delta
\]

に相当する整数等式。

`Nat.sub` の case split で API を汚すより、signed statement を別 theorem に切る方を優先する。

### 5. prime-degree residue transport の最小監査

この段階では prime certification を作らない。
既存 `WeightedGNBridge` の

\[
GN_p(x,u) \equiv x^{p-1} \pmod p
\]

を使って、prime degree `p` に対する Body の residue を整理する。

正の `x` で必要な条件が揃うなら、Fermat により

\[
x\,GN_p(x,u) \equiv x \pmod p
\]

へ落とせるか確認する。

その上で foreign Gap を足した

\[
CrossLeft = x_1GN_p(x_1,u_1) + u_2^{d_2}
\]

が

\[
CrossLeft \equiv x_1 + u_2^{d_2} \pmod p
\]

となる theorem を、仮定を正確に付けて実装する。

重要:
- `prime degree => cross output prime` は主張しない。
- residue freedom が増えたことと primality を混同しない。
- 前 campaign の `GN_p ≡ 1 (mod p)` 型 unit-boundary restriction が、foreign Gap によりどう変わるかを観測するだけ。

---

## 数値 regression

以下の整数分解は概念確認用であり、CosmicFormula parameter の存在を自動的に意味しない。
そのため、無理に production theorem にしない。

- `10 + 20 = 13 + 17` : transfer 3
- `8 + 2 = 7 + 3` : transfer 1
- `120 + 8 = 109 + 19` : transfer 11

まず一般恒等式を証明し、必要なら audit module で小さな具体例を追加する。

もしこれらを実際の `(Body_i, Gap_i)` として実現できる具体的 CosmicFormula coordinates が簡単に見つかるなら、別途 regression として追加してよい。
見つからない場合は無理に合わせないこと。

---

## 禁止事項 / 非目標

この指示では以下を行わない。

1. Strong Goldbach の証明を主張しない。
2. `CrossLeft`, `CrossRight` の primality を定義に埋め込まない。
3. prime output の存在を仮定して conditional theorem だけを量産しない。
4. `x=1` へ早期特殊化しない。
5. fixed degree `(2,3)` を universal carrier として再試行しない。
6. CRT / Capacity / PairOverlap をこの段階で再導入しない。
7. CFBRC / RH / analytic prime density を接続しない。
8. 大規模 abstract framework を先に作らない。
9. `sorry`, `admit`, `native_decide`, 新規 `axiom`, `unsafe` を使わない。
10. theorem 名や既存 API を推測せず、repository-first で確認する。

---

## 既存資産の優先確認

少なくとも次を確認してから実装すること。

- `DkMath.CosmicFormula.CosmicFormulaBinom`
- `DkMath.NumberTheory.WeightedGNBridge`
- `DkMath.NumberTheory.GNDegreeFactorization`
- `DkMath.NumberTheory.GNPrimeTargetResidue`
- `DkMath.NumberTheory.Goldbach.Basic`
- `DkMath.NumberTheory.Goldbach.PairGN`

特に前 campaign の `PairGN.lean` は参考にしてよいが、今回の owner をそのまま unit-boundary API の拡張にしないこと。
full-coordinate Cross-Gap API として分離する。

---

## 実装後の報告

`report-000.md` を同じ docs directory に作成し、以下を簡潔に報告する。

- 追加・変更ファイル
- 実装 theorem 一覧
- Cross-Gap 保存則が Lean でどう固定されたか
- residue theorem の exact hypotheses
- regression 結果
- build command と結果
- `#print axioms` の結果
- 禁止構文 grep の結果
- Outcome 判定

Outcome は次の3分類を使う。

### Outcome A — NEW ARITHMETIC FREEDOM

foreign Gap を入れたことで、既存 GN 単体には無かった arithmetic restriction / freedom が theorem として得られ、次の prime-certification 探索へ進む価値がある。

### Outcome B — STRUCTURAL CONSERVATION ONLY

Cross-Gap 保存則と residue transport は正しいが、新しい prime 情報は得られない。

### Outcome C — COLLAPSE / EQUIVALENT REPARAMETRIZATION

構造が既存 PairGN / Goldbach fiber の単なる言い換えに潰れる。

この段階では A を期待して無理に結論を作らない。
Lean の結果をそのまま報告すること。

---

## CGE-000 完了条件

以下を満たせば終了。

- full-coordinate Cross-Gap 定義が production module に存在する。
- `CrossLeft + CrossRight = PairedBig` が kernel-check される。
- swap / fixed-locus の最小 theorem がある。
- prime-degree residue transport を少なくとも1本 exact theorem にする。
- Goldbach 一般証明を主張していない。
- focused build 成功。
- axiom audit で `sorryAx` / 新規公理がない。
- `report-000.md` を残す。

次段階では、この report を読んでから `cross output` の prime certification 条件を一つずつ探索する。