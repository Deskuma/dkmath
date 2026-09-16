# instruction-004 — GN balance と cubic shell の exact three-layer bridge

## 0. 目的

BCAL-003 では、prime $q$ の valuation depth $v=v_q$ に対する局所 balance が exact に

$$
Q_q=(2-v)\log q
$$

と表され、

- $v=1$ : positive / single-support layer
- $v=2$ : zero / neutral pivot layer
- $v\ge3$ : negative / over-depth layer

という三層構造が得られた。

BCAL-004 では、既存 ABC cubic-shell 系で用いられている repeated-part / squarefree-complement 分解が、この三層構造をどこまで保存しているかを監査し、exact に接続可能な範囲だけ production theorem として実装する。

この checkpoint の目的は数値評価ではない。

**cubic shell が BCAL balance と同じ valuation geometry を別座標で記述しているかを確定すること** が目的である。

## 1. 最初に必ず行う source audit

実装前に、現在の production API を調査すること。

特に以下を確認する。

1. cubic polynomial family

    $$
    F(a)=a^2+3a+3
    $$

    に対する repeated part / squarefree complement の現行定義。

2. `repeatedPrimePowerPart` と、それに関係する既存 factorization API。

3. `piSqRad` および `twoTail` の現行定義と theorem。

    既存コードには少なくとも概念的に

    $$
    \text{repeatedPrimePowerPart}(n)=\text{piSqRad}(n)^2\text{twoTail}(n)
    $$

    という exact decomposition が存在する。

    この既存 theorem を優先して再利用し、同型の新定義を重複して作らないこと。

4. squarefree complement が valuation $v=1$ の prime のみを保持しているのか、それとも別の情報も含むのか。

5. repeated part が単に

    $$
    v_q\ge2
    $$

    という support 情報だけを保持するのか、実際の exponent depth まで recover 可能なのか。

6. prime $3$ に exceptional handling が存在する場合、その条件・分岐・既存 theorem を明示的に確認すること。

推測で generic odd-prime theorem を適用しないこと。

## 2. BCAL-003 から得られた規格

valuation $v_q$ ごとの local contribution は

$$
(2-v_q)\log q.
$$

したがって、素因子を三種類に分けると

$$
v_q=1,\qquad v_q=2,\qquad v_q\ge3.
$$

このとき $v_q=2$ は balance に寄与しない。

したがって cubic shell を BCAL balance に接続する際、

```text
squarefree versus repeated
```

という二分だけでは不十分な可能性がある。

特に repeated part に

```text
v = 2
v ≥ 3
```

が同時に含まれる場合、BCAL の neutral pivot と negative over-depth が一つの量に潰れてしまう。

## 3. three-layer shell decomposition

既存 API が許すなら、次の三層を明示する。

```text
single layer
    valuation v = 1

pivot layer
    baseline q² for valuation v ≥ 2

over-depth layer
    excess q^(v-2) for valuation v ≥ 3
```

概念的には

$$
n=\text{single}(n)\text{pivot}(n)\text{overDepth}(n).
$$

既存 `repeatedPrimePowerPart` decomposition が利用できる場合、pivot と over-depth は原則として

$$
\text{pivot}(n)=\text{piSqRad}(n)^2
$$

および

$$
\text{overDepth}(n)=\text{twoTail}(n)
$$

に対応するはずである。

ただし、これは名前から推測して theorem 化してはならない。

既存定義を展開し、valuation theorem または既存 factorization theorem に基づいて確認すること。

## 4. 重要な bridge target

BCAL-003 の balance は、

$$
Q=\sum_q(2-v_q)\log q.
$$

三層分解が exact に成立する場合、neutral pivot は消去され、

$$
Q=\log(\text{single})-\log(\text{overDepth})
$$

という形になることを期待する。

これを今回の最重要 target とする。

特に既存 shell notation が

$$
F(a)=M_{\mathrm{shell}}S_{\mathrm{shell}}
$$

の形である場合、

$$
\log M_{\mathrm{shell}}-\log S_{\mathrm{shell}}
$$

を無条件に BCAL balance と同一視してはならない。

$M_{\mathrm{shell}}$ が

$$
\text{piSqRad}^2
$$

という neutral pivot mass を含む場合、この式は BCAL-003 の $Q$ とは異なる。

必要なら、

$$
M_{\mathrm{shell}}=M_{\mathrm{pivot}}M_{\mathrm{over}}
$$

と分解し、pivot を除去した量だけを balance に使用する。

## 5. 実装候補

新規 production module の候補：

```text
DkMath/ABC/GNBalanceCubicShell.lean
```

ただし既存 module hierarchy により、より自然な配置が明白ならそれを優先してよい。

新しい概念 API は必要最小限とする。

優先順位は、

1. 既存 theorem の rewrite
2. 既存 quantity 間の exact identity
3. valuation layer bridge
4. 新しい wrapper definition

の順とする。

単なる別名 API を増やさないこと。

## 6. 欲しい theorem 群

source audit の結果に応じ、以下のうち安全に証明できるものを実装する。

### A. repeated part internal decomposition

既存 API を直接 expose / specialize して、

$$
\text{repeatedPart}=\text{pivotPart}\text{overDepthPart}
$$

を得る。

既存 theorem がそのまま存在するなら新規 theorem は不要。

### B. pivot neutrality

BCAL balance において $q^2$ baseline が寄与ゼロであることを、BCAL-003 の local theorem へ接続する。

新しい解析的議論ではなく既存 local identity の corollary とする。

### C. single-layer identification

squarefree complement または shell complement が本当に $v=1$ layer と一致する場合、その exact identification を証明する。

一致しない場合は弱い inclusion / divisibility / support correspondence に留める。

### D. over-depth identification

`twoTail` が

$$
\prod_{v_q\ge3}q^{v_q-2}
$$

に対応することが既存 API から証明できるなら、BCAL repeated-depth layer と接続する。

### E. balance bridge

最終的に可能なら、

$$
Q_{\mathrm{BCAL}}=\log(\text{single})-\log(\text{twoTail})
$$

または現行 API に即した同値な exact theorem を production に置く。

符号規約は BCAL-003 を正本とする。

## 7. cubic family への specialization

generic natural-number bridge が成立した後にのみ、

$$
F(a)=a^2+3a+3
$$

へ specialize する。

generic theorem を cubic polynomial 固有の証明として再実装しないこと。

cubic shell 側ですでに canonical complement / repeated part theorem がある場合は、それを receiver として使用する。

prime $3$ に特殊事情がある場合、

```text
generic odd-prime layer
exceptional 3-layer
```

を混ぜず、必要なら theorem を分離する。

## 8. 今回やらないこと

以下は BCAL-004 の scope 外とする。

- Hensel lifting / Hensel transport
- valuation mutation
- $v\mapsto v+1$ の動力学
- global monotonicity
- descent
- optimality
- shell counting
- dyadic moment estimates
- incidence estimates
- numerical exponent optimization
- $0.435$ 等との比較
- ABC inequality の証明
- 新しい axiom
- uniform joint contract の仮定追加

特に

$$
Q_q\mapsto Q_q-\log q
$$

という Hensel/depth-step interpretation は次 checkpoint 候補であり、今回は theorem 化しない。

## 9. Outcome 判定

### Outcome A — EXACT BRIDGE

以下が kernel checked で得られた場合。

- shell/repeated decomposition と三層 valuation decomposition の exact connection
- neutral pivot の分離
- BCAL balance の `single - over-depth` rewrite
- cubic-family specialization

この場合 production export を行う。

### Outcome B — PARTIAL BRIDGE

shell API が exponent 情報の一部を失っている等の理由で full equality が得られないが、

- reusable exact lemma
- support correspondence
- pivot/over-depth の部分的分離
- 情報損失箇所の特定

まで得られた場合。

無理に equality を作らず、report に何が足りないかを明記する。

### Outcome C — AUDIT ONLY

既存 shell abstraction から BCAL-003 の三層を安全に recover できない場合。

production theorem は追加せず、

```text
which information is forgotten
where it is forgotten
what API would be required
```

を report に残す。

## 10. 検証

実装後、最低限以下を実行する。

```text
focused module build
DkMath/ABC.lean facade build
forbidden-word / placeholder inspection
axiom audit
git diff --check
```

新規 theorem の axiom set が既存 arithmetic infrastructure を越えて増えていないことを確認する。

## 11. report

以下を作成する。

```text
docs/dev/ABC-GN-balance-calibration-260915-v0/report-004.md
```

最低限記録する内容：

- Outcome A / B / C
- 調査した既存 shell API
- repeated part の内部 decomposition
- $v=2$ pivot が保持されるか
- `twoTail` と over-depth の対応
- squarefree complement と single layer の対応
- prime $3$ の扱い
- exact bridge theorem 一覧
- 証明できなかった候補
- 次 checkpoint で Hensel transport を調べる価値があるか

## 12. 判定原則

今回の中心原則は、

> repeated であること自体は imbalance ではない。

$v=2$ は repeated だが、

$$
(2-2)\log q=0
$$

なので完全に中立である。

負方向へ balance を動かすのは $v\ge3$ の **over-depth** だけである。

したがって cubic shell と GN balance の bridge は

```text
squarefree ↔ repeated
```

ではなく、

```text
single ↔ pivot ↔ over-depth
```

の三層を保存できるかどうかによって判定すること。
