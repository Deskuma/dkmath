# cyclotomicUnitNormalization_of_firstCase_of_pack_thin 依存分解メモ

## 1. 目的

このメモの目的は、`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` に残っている
`hProduct` 依存が

- 本当に数学的に必要なのか
- 旧設計の名残なのか
- local factorization core で代替できるのか

を、責務ごとに切り分けることにある。

現状の戦況としては、first-case の Stage 3 中核

- `CyclotomicNormEqGNFirstCasePackThinTarget`
- `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`

はどちらも interface レベルで `hProduct`-free になっている。  
したがって、`hProduct` が残る主要候補は unit-normalization chain と legacy one-shot 側に局在している、という見立てで進める。

---

## 2. 先に固定してよい事実

### 2.1. 再調査しない層

以下は、もう `hProduct` の主戦場ではないと見なす。

- `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
- `cyclotomicNormEqGN_concrete_firstCase_packThin`
- `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`
- `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
- y-branch contradiction
- first-case pairwise coprimality の product-free 版

つまり、Stage 3 本体の norm/GN chain と unit 吸収そのものは、もう再発明対象ではない。

### 2.2. いまの主戦場

再調査対象は主に次の 3 つ。

- `cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
- その直前の ideal/principalization chain
- `cyclotomicPrincipalization_of_classGroupPTorsionFree` など legacy one-shot の first-case 配線

---

## 3. 責務分解

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` を、proof の順ではなく責務の順で 4 つに分けて見る。

### 3.1. 責務 A. ideal-level の `p` 乗化

見たい形は、おおまかに

\[
\langle z - \zeta y \rangle = I^p
\]

あるいはそれに準ずる ideal equality じゃ。

確認したいこと:

- `hProduct` はこの ideal equality の構成に直接必要か
- 必要なら、full product identity そのものが要るのか
- local factorization core から得られる weaker な packaging で足りないか

### 3.2. 責務 B. chosen factor と tail / other factor の coprime 化

ここは旧 chain の惰性で `hProduct` を渡している可能性が高い。

確認したいこと:

- この coprime 証明は本当に full product identity を使うか
- `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct`
  で置き換え可能か
- y-branch contradiction 側は local factorization のみで十分か

### 3.3. 責務 C. principality から element equality への降下

最終的に欲しい形は

\[
z - \zeta y = u \cdot \beta^p
\]

じゃ。

確認したいこと:

- C 自体は `hProduct` を使うのか
- 実際には A の結果を受けるだけではないか
- もし C が受けるだけなら、`hProduct` 依存は A に閉じ込められる

### 3.4. 責務 D. first-case 条件 `¬ p ∣ gap` の使用点

これは `hProduct` とは別軸じゃが、依存の誤読を避けるために一緒に追う。

確認したいこと:

- `hProduct` が必要に見える箇所のうち、
  実際は `¬ p ∣ gap` と prime-over-`p` contradiction が本質ではないか
- first-case 条件だけで切れる補題に、product 系を混ぜていないか

---

## 4. 実作業チェックリスト

### 4.1. Step A. 依存表を作る

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の直依存 theorem を列挙する。

表の列はこれでよい。

| theorem 名 | 役割 | `hProduct` 直使用 | `hProduct` 間接使用 | local factorization 代替候補 |
|---|---|---:|---:|---|
| theoremA | ideal equality | yes/no | yes/no | 候補名 |
| theoremB | coprime | yes/no | yes/no | 候補名 |
| theoremC | principality | yes/no | yes/no | 候補名 |

この表が、次の全作業の地図になる。

### 4.1.1. 現時点の依存表（2026/04/08 04:12 JST 時点）

| theorem 名 | 役割 | `hProduct` 直使用 | `hProduct` 間接使用 | local factorization 代替候補 |
|---|---|---:|---:|---|
| `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` | A+B bridge | yes | no | A は `chosenLinearFactorMulTailEqSpanPow_of_productEq`、B は product-free 化済み |
| `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin` | A→C receiver | no | yes | `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` の isolated core 化 |
| `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` | C 本体 | no | yes | ideal-level `p` 乗化の入口が product-free なら自動で軽くなる |

補足:

- `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` の `hCoprime` leg は、
  `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack_withoutProduct`
  へ差し替え済み。
- よってこの theorem に残る `hProduct` は、chosen factor × tail ideal = `(x)^p`
  を与える `hMul` 側に局在したと見てよい。
- したがって現在の主戦場は、責務 A の ideal-level `p` 乗化入口じゃ。

### 4.1.2. 追加で確定したこと（2026/04/08 04:49 JST 時点）

- `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_of_mulTailEqSpanPow` を追加し、
  mul-tail ideal equality さえあれば Stage 1 explicit equality へ進めることを theorem 名で切り出した。
- さらに
  - `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin_of_mulTailEqSpanPow`
  - `cyclotomicUnitNormalization_of_firstCase_of_pack_thin_of_mulTailEqSpanPow`
  を追加し、receiver 側は完全に isolated になった。
- 一方、local factorization core からは
  - `chosenCyclotomicTailSumMulChosenLinearFactorEqSpanPow_of_counterexamplePack`
  - `exists_tailMulChosenLinearFactorEqSpanPow_of_counterexamplePack`
  が取れた。
- したがって新しい主要 gap は、`hProduct` そのものではなく
  **tail-sum ideal と chosen factor ideal の coprimality bridge** をどう supply するか、に縮んだと見てよい。

### 4.2. Step B. `hProduct` 使用箇所を色分けする

各 `have` / `obtain` / `exact` を次の 3 区分で分類する。

- **direct**: `hProduct` をその場で使っている
- **indirect**: `hProduct` 依存 theorem を呼んでいる
- **unnecessary**: 置換できそう

目的は「proof のどこで出たか」ではなく、

\[
\text{どの責務に属する use か}
\]

を確定することじゃ。

### 4.3. Step C. coprime 系を product-free 版へ差し替える

優先順位はここが最上位。

もし旧 chain が以下のどれかを `hProduct` つきで返しているなら、
まず product-free 版へ置換して build を確認する。

- y-branch contradiction
- chosen factor と他因子の common-prime 排除
- pairwise coprimality

候補:

- `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_counterexamplePack`
- `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct`

### 4.4. Step D. ideal-level `p` 乗化の入口だけを theorem 名で切り出す

A が残るなら、その核だけを isolated theorem として取り出す。

候補名の例:

```lean
theorem chosenFactorSpanEqPow_of_firstCase_<route> ...
theorem chosenFactorIdealPthPower_of_firstCase_<route> ...
```

ここでは、証明できるかどうかよりも theorem 境界を切ることが重要じゃ。
境界が切れれば、C と分離できる。

### 4.5. Step E. local factorization ベース代替核を試す

既存の

```lean
chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack
```

を起点に、full product identity の完全代替でなくてもよいので、
normalization 入口に足る weaker packaging が取れぬか試す。

狙いの形の例:

\[
\langle z - \zeta y \rangle \cdot J =
\langle x \rangle^p
\]

または

\[
(z - \zeta y)\cdot T = x^p
\]

から ideal-theoretic な `p` 乗構造へ入れる形じゃ。

---

## 5. 判定基準

### 5.1. 小勝利

依存表の結果、`hProduct` 使用が 1 箇所か 2 箇所に局所化した。

### 5.2. 中勝利

coprime / y-branch 系を product-free 版へ差し替えた結果、
`hProduct` が ideal-level `p` 乗化の入口にしか残らなくなった。

### 5.3. 大勝利

local factorization ベースの代替核が立ち、
unit-normalization chain 全体から `hProduct` を押し出せる見通しが立った。

現時点では、代替核そのものは theorem として立ったが、
まだ tail-sum ideal の coprimality bridge が不足しているため、
大勝利の一歩手前と評価するのが正確じゃ。

---

## 6. 今はやらないこと

### 6.1. global full product identity の canonical supply を先に掘る

以前は本命に見えたが、いまは優先度が下がる。  
理由は、Stage 3 本体と y-branch がすでに product-free 化しているからじゃ。

### 6.2. legacy route 本体を先に大改造する

`FLTPrimeGe5Target_of_kummerRoute` や
`cyclotomicPrincipalization_of_classGroupPTorsionFree`
を先に大改造すると、黒箱依存を抱えたまま proof が崩れる危険が高い。

### 6.3. `hLinNe` を blocker 扱いする

これはもう product identity から自動供給可能と整理済みであり、
現時点の本丸ではない。

---

## 7. 次の号令

1. `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の依存表を作る。  
2. `hProduct` 使用箇所を direct / indirect / unnecessary に色分けする。  
3. coprime / y-branch / pairwise reasoning に属するものは product-free theorem 群へ順に差し替える。  
4. 残った `hProduct` 使用箇所についてのみ、ideal-level `p` 乗化の isolated theorem を切り出す。  
5. `chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack` を起点に、local factorization ベースの normalization 代替核を探索する。

---

## 8. 一言まとめ

いまの本丸は

\[
\text{full product theorem を取ること}
\]

ではなく、

\[
\text{unit-normalization chain の中で `hProduct` が残る最小核を剥き出しにすること}
\]

じゃ。
