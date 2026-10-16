# FLT7：お手本との照合と降下状態の軌道修正

2026/10/17 JST

## 結論

次に必要なのは、元の自然数反例を毎回作り直すことではなく、**一般化された円分環上の方程式が深度降下で閉じること**である。
元の自然数反例は最初の一回だけこの状態へ入れればよい。

今回の [検証スクラッチ](scratch/FLT7RouteAudit.lean) では、次まで実際に証明した。

1. DkMath の任意の `CounterexamplePack` から、お手本と同じ形の正深度状態を構成できる。
2. その同じ状態の方程式を GN / GTail に翻訳できる。
3. 重み付き七乗式の係数比が七乗単元なら、同じ y,z を保持して標準形に戻せる。
4. 深度1の排除と一段の遷移を仮定すれば、正深度の全状態が存在しないという帰納法は閉じる。

**4の二仮定は今回証明していない。FLT7の無条件終点ではない。**
既存の補正項・ノルムパケットを完成させたこととも区別する。
スクラッチの外側の入力は正のprimitiveな `CounterexamplePack` である。
任意の自然数反例からgcdを除いてこのpackへ入れる外側の正規化と、
`FermatLastTheoremFor 7` への最終包装は今回の検証範囲に含めていない。

## 調査資料と照合範囲

ローカル入力は `../FLT7-Kummer-Anthropic-Bridge-261015-v0/` の4コピーである。

| コピー | 行数 | 確認した内容 |
| --- | ---: | --- |
| `__S_fermatLastTheoremSeven.lean.txt` | 15 | `flt_regular` と七次PIDから指数7へ特殊化 |
| `__S_IsCyclotomicExtension_Rat_seven_pid.lean.txt` | 84 | Minkowski上界、2と3の剰余次数からPID |
| `__S_flt_regular.lean.txt` | 4241 | 正則性、Case I、単元補題、Case II、帰納法、整数のCase分け |
| `__Util.lean.txt` | 127 | `p2m_*` の名前解決・export・型検査用マクロ |

コピーは入力資料として読み、書き換えず、外部モジュールとしてimportしていない。
ハッシュは [source manifest](evidence/source-flt7-proof-route-audit-sha256.txt) に保存した。
入力に取得時のcommit hashがないため、main上の全ソースとのbyte一致までは主張しない。

公開 [PROOF-PATH](https://github.com/anthropics/fermats-last-theorem/blob/main/PROOF-PATH.md) は、指数7・11・13に正則素数のKummer経路を使うと説明している。
[公開 `flt_regular` 宣言](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_flt_regular.lean) の仮定は、素数p、類群位数との互いに素性、p≠2であり、ローカルコピーの最終 `solution` と対応する。
公開元の [toolchain](https://github.com/anthropics/fermats-last-theorem/blob/main/lean-toolchain) は4.33.1、現在のDkMathは4.34.1。
今回、公開元全体のビルドや検証ツールの再実行はしていない。
ブラウザで取得できなかった `P2M/Sol` の個別ページについては、ユーザー提供コピーを分析の根拠にした。

## Big・Body・Gap の読み直し

`Big ≠ Body + Gap` を恒等式そのものの否定として採用することはできない。
宇宙式は、係数環や反例の有無にかかわらず成立する。

\[
x^7=(x+y)\,GN_7(x+y,-y)+(-y)^7
\]

を整理すると

\[
x^7+y^7=(x+y)\,GN_7(x+y,-y)
         =(x+y)\,GTail_{7,1}(x+y,-y).
\]

これはスクラッチの `seventh_sum_eq_gn` と `seventh_sum_eq_gtail` で検証した。
矛盾の対象は、この保存等式に **正の分岐深度・七乗右辺・非分岐性** を同時に課した状態である。
「Gap」という語で端点差 `x+y` と分岐冪 `lambda^m` を同一視しない。
両者は積の等式によって接続される異なるデータである。

## お手本が反復する状態

ローカルコピー3447行以降のCase IIは、`pi=ζ-1` を使って

\[
x^7+y^7=\varepsilon(\pi^{m+1}z)^7,
\qquad \pi\nmid y,\quad \pi\nmid z
\]

を入力とする。スクラッチの `State m` はDkMathの `lambda=1-ζ` で同じ形を保持する。
`State.pi_equation` は符号差を右辺の単元へ吸収し、深度mを変えずに変換する。
係数環は具体的な六次環Cのままであり、既存の `integralEquiv` が円分整数環との対応を提供する。
抽象円分環へ移植するときは、対応する原始根と符号をこの同型で固定する必要がある。

この状態に、元の自然数の正値性、元の端点名、あるいは大域的な `IsCoprime x y` は要求されていない。
特に `lambda∤y` は大域的な互いに素性を意味しない。
お手本は `gcd((x),(y))` を保持して、これを勝手に捨てない。

### 降下stepの内部

ユーザー提供コピーの行番号で対応を固定する。

| 箇所 | 役割 | GNとしての意味 |
| --- | --- | --- |
| 3447–3575 | 全七位相の因子と一段剥離商 | gapと全線形因子を保持 |
| 3677–3700 | 互いに素な残余イデアルの七乗抽出 | 共通gcdと分岐因子を剥離した積の冪配分 |
| 3710–3808 | 特別な位相η₀の深度、`one_le_m` | 一つの深い因子を他の浅い因子から区別 |
| 3860–3932 | イデアル根の比の主イデアル化、分子α・分母β | 同じ因子の元の等式を構成 |
| 3933–3946 `formula` | 三位相の厳密な加法関係 | 七乗式の新しい左右端点を作る核 |
| 3948–4008 `exists_solution` | 係数単元付き、同じ三つの新根の非分岐性 | 深度をm+1からmへ減らした重み付き状態 |
| 4010–4040 `exists_solution'` | 係数比の整数合同→Kummer単元補題 | 左辺二項の単元差を七乗根へ吸収し再入 |
| 4083–4095 `not_exists_solution` | 深度1の排除と自然数帰納法 | 正深度状態の不存在 |

Case II の元の数学的な比較元は [flt-regular の InductionStep](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/CaseII/InductionStep.lean) と [Statement](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/CaseII/Statement.lean)。
原始な整数反例からの符号変更・Case I/II の分岐は降下stepの外側に置かれている。

### 単元補題を使う正確な位置

お手本は新しい二根に対して

\[
\varepsilon_1X^7+\varepsilon_2Y^7
 =\varepsilon_3(\pi^m Z)^7
\]

を作った後、式全体の合同条件を使い `ε₁/ε₂` の整数合同を導く。
それからKummer単元補題を適用し `ε₁/ε₂=κ⁷` を得る。
**個々の位相単元を先に全て七乗と証明する設計ではない。**
スクラッチの `normalize_weighted` はこの最後の代数操作を検証し、
新状態の `x=κX`、`y=Y`、`z=Z` を同じ証人で返す。
係数比の七乗性はこの補題の明示的仮定であり、供給したことにはしていない。

## DkMathの現在地との対応

| 必要な部品 | 現在のDkMath | 判定 |
| --- | --- | --- |
| 七次PID・類数1 | `CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing`、`septic_classGroup_card_eq_one` | 既存。追加正則性の仮定は不要 |
| Cと円分整数環の同型 | `SevenPrimaryNorm.integralEquiv` | 既存。今回は公理を再確認 |
| 整数合同単元の七乗性 | `concrete_kummer_unit_power_criterion` | 既存。新しい係数比に整数合同を供給する必要がある |
| 元のprimitive反例のCase I排除 | `seven_dvd_some_endpoint_of_counterexample` | 既存。標準3公理のみと今回確認 |
| 三端点の符号正規化 | `nonempty_primitiveCounterexampleRamifiedProvenance` | 既存。任意のprimitive反例から構成 |
| 正深度の一般化状態への入口 | scratch `initial_state_of_counterexample` | 今回検証。実三次orbitやcommon-prime不要 |
| 一般化状態のGN/GTail表現 | scratch `State.gn_equation`、二つの和公式 | 今回検証 |
| 正深度の底の排除 | `one_le_m`に相当する一般C上の結果 | 本スクラッチでは未供給 |
| 全Stateに対する一段再構成 | `exists_solution'`に相当する結果 | 本スクラッチでは未供給 |
| step後の再入を含む整礎帰納法 | scratch `no_state_of_base_and_step` | 二仮定を明示して検証 |

既存の `CosmicRamifiedIdealPower` は一般の環にも使えるが、元のAPIには
`IsCoprime x u` や完全冪の積等式が必要である。
新しい一般化Stateは右辺に未解析の単元を持ち、大域gcd=1を仮定しない。
この二点を解消せずに、既存の整数入力の `GN_ideal_pow_of_ramified_case` を再帰的に適用してはいけない。
イデアル等式へ送れば単元は消えるので、その段階のAPIを一般化して再利用する道がある。

## 分岐の網羅性と common-prime の範囲

`CounterexampleRoute.away` の条件は `¬7∣z-y`。
古典的Case Iは `¬7∣xyz` であり、同じ分岐ではない。
DkMathの `primitiveSevenDivisibleEndpoint_of_counterexample` は、既存の座標正規化と
sum-sector排除を使い、x-only/y-only/z-onlyの三分岐へ到達する。
`seven_dvd_some_endpoint_of_counterexample` がその全primitive反例に対する帰結である。
これにより古典的Case Iは既存経路で排除されている。
単なるmod7のFrobeniusだけからこの結論を得ているわけではない。

`CurrentCommonPrimeCyclotomicPacket h q` の provider
`currentCommonPrime_cyclotomicAddress` は **q.Prime と q∣h.c** を要求する。
従って任意の反例から無条件に任意のqで得られるパケットではない。
`h.c=1` の場合にはそのようなqは存在せず、common-prime経路だけで全反例を覆ったとは言えない。
一方、既存の六因子族の一般providerは `DirectOrbitCanonicalCommonFactorPacket p` を入力とし、
common-primeパケットの選択を必要としない。この二つの範囲を混同しない。

## 今回実際に作れた初期状態

`PrimitiveRamifiedSummitPacket s` から、

\[
X=\operatorname{ofInt}(s.endpointLeft),\qquad
Y=-\operatorname{ofInt}(s.endpointRight),\qquad
D=\operatorname{ofInt}(s.distinguished)
\]

を使う。既存の `fermat_eq` は `X⁷+Y⁷=D⁷` を与える。
`distinguished=7*gapRoot*residualRoot` と両根の正値性によりDは非零で、lambdaがDを割る。
Cの既存UFD構造から有限重複度を取り、

\[
D=\lambda^m Z,\quad m\ge1,\quad \lambda\nmid Z
\]

と完全剥離する。Yの非分岐性は既存の整数端点条件から得る。
これで右辺単元1の `State m` に入る。
新しい公理、外部FLT終点、あるいは補正根の小ささは使わない。

スクラッチには `State 0` の実際の証人 `(0,1,1,1)` も置いた。
正深度というguardを外した「全State不存在」は偽であることが型検査できる。

## これまでの補正パケットをどう保存するか

- `θ_j⁷+ofReal ρ=U_j Γ⁷` は左辺第二項の七乗根を供給していない。
- 重み付き三位相式は係数比の七乗正規化と深い右辺の再構成が未供給。
- 根・イデアル・ノルムの既存等式は資産として保持するが、上記二つをState stepの証明として数えない。
- Gammaのノルムが小さいことも、今回必要な深度mの減少も別の命題である。

今回はこれらのproductionパケットを追加・変更せず、スクラッチと監査文書だけを追加した。

## 次の実装を最終経路へ限定する

1. `State (m+1)` から全七位相の一段剥離商を構成する。剰余体上の相異性・全射性で特別な位相を特定し、底の排除を証明する。
2. 共通gcdを保持したイデアル冪配分を作る。七次PIDは既存なので、元の等式を得るまで同じ証人を追う。
3. お手本 `formula` の三位相再構成をGNの因子恒等式として実装する。
4. 新しい係数比の整数合同を証明し、既存の具体的Kummer単元補題と今回の `normalize_weighted` へつなぐ。
5. ここで初めて `State (m+1) → Nonempty (State m)` のproviderを得て、検証済みの帰納法へ差し込む。

この経路なら、自然数の新反例を毎回構成するという追加条件を降下に課さずに済む。
ただし、一般化Stateのstepを証明する実作業自体は残る。

## 検証範囲

[検証記録](evidence/validation-flt7-proof-route-audit.txt) と
[Lean出力](evidence/flt7-proof-route-audit-scratch.txt) を参照。
スクラッチの条件付き閉包は底とstepを引数に残している。
既存の全体ビルドや外部リポジトリの証明を今回再検証したという主張ではない。
