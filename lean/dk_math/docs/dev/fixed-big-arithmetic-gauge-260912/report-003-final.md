# FBAG-003: Goldbach 証明実験の最終記録

日付: 2026-09-13

## 結果

**この試行では Strong Goldbach の証明も反証も得られなかった。**
会話ログの有限代数を Lean に固定し、単位変更による証明案が元の Goldbach 条件に戻ることを証明した。
production 4 module に35定理、audit 2 module に12定理を追加した。
この47定理には条件付き定理・同値定理・反例定理を含む。47個の独立した数論上の新結果という意味ではない。

主な成果は次の通り。

1. `u=R/k` による固定 Big 保存、Projection/CF2D、SquareBody、world-modulus refinement の exact bridge。
2. `P<m≤P²+2P` における完全な旧素数集合による素数認証、および正の面積単位での transport。
3. 実際に可視な child が3個あれば、高々二つの raw 禁止 index を避けられるという有限存在定理。
4. 可変 gauge の素数対は `GoldbachPairAt k` と同値であり、元の自然数中心 `n` の保存を要求すると `k=n, u=1` になるという監査定理。
5. full-period の survivor を短区間へ移せない反例が、全ての正の gauge に対して存続すること。

## 証明案をどこまで進めたか

ログに沿った試行は、次の分岐で決着した。

```text
固定 R、可変 k、単位 u=R/k
    ↓
Prime p, Prime q, (p+q)u=2R
    ↕ Lean: gaugePrimePairAt_iff
p+q=2k を満たす素数対
```

単に「適切な gauge が存在する」なら、全ての `R>0` に対して `k=2, p=q=2` で証明できた。
例えば `R=10` では physical length は左右とも10となる。ラベル2は素数だが10は合成数である。
これは20の素数分解の証明ではない。

元の自然数 `p+q=2n` と固定辺長 `R=n` を同時に守ると、正の単位を消去して `k=n` が従う。
このとき必要十分条件は既存の

\[
\#\operatorname{goldbachCoveredSeats}(n,\operatorname{goldbachSmallPrimes}(n))<n-1
\]

へ戻る。全ての `n≥2` でこの不等式を示す独立な証明は今回得られなかった。
`StrongGoldbach` は既存定義のまま、**証明された同値の対象**として登場する。
仮定から結論を導く theorem と、その仮定自体の無条件な証明を区別した。

## 真・偽・未確定

以下の「偽」は特定の推論や条件を省略した強化に対する判定であり、Goldbach 予想が偽という意味ではない。
ログが既に注意している条件も、実装上の境界として明示した。

| 対象 | 判定 | Lean の根拠・条件 |
|---|---|---|
| `k*u=R`, `k²*u²=R²` | 真 | `k>0`。`scale_unit_conservation`, `fixedBig_decomposition` |
| `u/R=1/k`, `(R²-u²)/u²=squareBody P` | 真 | 前者 `R≠0`、後者さらに `k=P+1` |
| 完全な `primeScalesUpTo P` での prime iff | 真 | `P<m≤squareBody P` |
| 同じ iff から strict lower bound を削除 | 偽 | `P=m=2` |
| 30以下の完全な prime world で961も認証 | 偽 | `961=31²` は旧 modulus と互いに素な合成数 |
| `{2,3,5}` と「30以下の全素数」を同一視 | 偽 | 49は前者を回避し後者の7で捕捉される |
| 30-wheel の鏡映対称性が prime label を保存 | 偽 | `479+481=960`、両者は30と互いに素だが481は合成数 |
| `M=30,q=7,n=10,r=29` の full survivors | 5 | 既存 paired child theorem で検証 |
| 同じ parent の実際の可視 child | 0 | `boundedChildIndices 10 30 29 7 = ∅` |
| 正の gauge がこの空の parent を救う | 偽 | `scaled_countermodel` は全ての `R>0,k>0,j` で区間外を証明 |
| boundary の成長が survivor の単調性を与える | 偽 | `M=30,q=7,r=1`, `n=12→13` で raw survivor は `{0}→∅` |
| 可視 child 3個と二穴から fresh survivor が出る | 真 | `bounded_paired_survivor`。他の素数に関する条件は別 |
| gauge を一つ選んで prime pair を得られる | 真 | `exists_gaugePrimePairAt`、全 `R>0`、証人 `k=2` |
| 元の中心を維持した gauge 判定は Goldbach と同値 | 真 | `strongGoldbach_iff_original_gauge` |
| 全中心で必要な短区間 survivor を供給できる | 未確定 | 独立した universal capacity/escape proof が残る |
| 平方の対称軸だけから PNT/RH/二点素数相関を導く | 今回未証明 | 解析的な bridge と仮定の検証がない |

`{6,14,21}` の product 1764、lcm 42、`squareBody 1764=3115224` も kernel 検証した。
ログの「最小 Big」には、どの整数を同期周期とし、何を最小化するかという admissibility の定義が必要である。
この例の数値検証を、任意の実数 gauge における最小 Big の存在定理とは扱わない。

## 有限 Goldbach 証明

既存の `goldbach_centers_two_through_one_hundred` を再利用して、
**全ての `2≤n≤100`（偶数対象4〜200）で元の gauge の素数対が存在する**ことを証明した。
新しい定理名は `original_gauge_centers_two_through_one_hundred`。
有限範囲を広げた結果ではなく、既存の kernel certificate を新 API に transport したものである。

## ソースと検証

production:

- `DkMath/NumberTheory/FixedBigGauge/Basic.lean`
- `DkMath/NumberTheory/FixedBigGauge/SquareCertificate.lean`
- `DkMath/NumberTheory/FixedBigGauge/Goldbach.lean`
- `DkMath/NumberTheory/FixedBigGauge/BoundedChildren.lean`

audit:

- `DkMathTest/NumberTheory/FixedBigGaugeAudit.lean`
- `DkMathTest/NumberTheory/FixedBigGoldbachAudit.lean`

これらは明示 import する module として追加した。依存元の確認は `report-000.md`、最初の実装は `report-001.md`、Goldbach 接続は `report-002.md` を参照。

再現 cwd は `lean/dk_math`。

```sh
./lean-build.sh DkMathTest.NumberTheory.FixedBigGoldbachAudit
lake env lean DkMathTest/NumberTheory/FixedBigGoldbachAudit.lean
git diff --check
```

focused build は成功。追加した全6 Lean ソースの直接検証ログを `validation-003.log` に保存した。
最終 audit は47定理全てに `#print axioms` を実行する。
許容する既存標準公理は `propext`, `Classical.choice`, `Quot.sound` のみであり、`sorryAx` や追加公理には依存しない。
ソースにも `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom` 宣言はない。
直接検証の warning/error は0件、`git diff --check` も成功。

この検証は上記 focused dependency closure の範囲であり、リポジトリ全体のビルド完了を意味しない。

## チェックポイント

指定 branch `wip/fixed-big-arithmetic-gauge-260912-v0` に以下を記録した。

- `1f2b592bb`: repository-first audit。
- `3436adf83`: 固定 Big と平方素数認証、ビルド成功。
- `62350bbcf`: Goldbach 同値・bounded child theorem、ビルド成功。
- 本レポートを含む最終チェックポイント: 全定理監査、具体的反例、有限証明の transport。

結論の強さは、**有限 exact algebra と判定基準、およびこの gauge 証明案の残余義務の特定**である。
一般の Goldbach に必要な新しい全称存在情報は得られていない。
