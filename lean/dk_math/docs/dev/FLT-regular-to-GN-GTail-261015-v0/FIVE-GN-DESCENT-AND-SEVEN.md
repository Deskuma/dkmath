# FLT5：相対ノルムで同じ剥離商へ戻り、閉じた不変条件で降下する

2026-10-16。添付の FLT5 接続案を研究提案として照合し、五次の単元補題、
同じ β の根の復元、既存の黄金比降下への接続を実装した。
この章の前半は Lean の定理と実装の説明、後半はその結果からの研究考察である。
検証記録は [validation-five-gn.txt](evidence/validation-five-gn.txt)。

## 1. 今回の終点と再利用の範囲

新しい終点は `DkMath.FLT.Kummer.fermatFive_no_positive_solution_via_GN`。

```lean
(a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ 5 + b ^ 5 ≠ c ^ 5
```

具体的五次円分体を実際に供給するので、類数条件、単元補題、原始性、根の存在を
追加仮定として要求しない。既存の FLT5 完成済み終点を呼ぶ証明ではない。

既存の gcd 正規化、signed orientation、整数の五乗冪配分、GoldenInt の
一般的な単元分類、零セクター内の厳密降下を再利用する。
最初の **指定された同じ β の五乗根** は GN・円分イデアル・単元合同・相対ノルム
という新しい経路で供給する。単元分類への依存が証明全体から消えたとは主張しない。

## 2. 四つの整数座標を二つの黄金比整数にまとめる

[QuinticGoldenNorm.lean](../../../DkMath/Lib/NumberTheory/QuinticGoldenNorm.lean)
は FLT の仮定を使わない。黄金比の向きは

\[
 \phi=1+\zeta+\zeta^4=-\zeta^2-\zeta^3,\qquad \phi^2=\phi+1
\]

と固定する。整数冪基底の元を
`x=a₀+a₁ζ+a₂ζ²+a₃ζ³` と書くと

\[
 \begin{aligned}
 A&=(a_0-a_2+a_3)-a_3\phi,\\
 B&=(a_1-a_2+a_3)+(a_2-a_3)\phi,\\
 x&=A+B\zeta.
 \end{aligned}
\]

逆変換も整数係数である。`A=r+sφ, B=t+vφ` なら四次座標は
`(r+v,t+v,−s+v,−s)`。この行列変換の全単射性により

\[
 \operatorname{QuadraticAlgebra}(\operatorname{TraceOneInt}(1),-1,\phi-1)
 \simeq_{\rm ring}\mathcal O_K
\]

を構成する。二次モデルの生成元 ω は `ω²=(φ−1)ω−1` を満たし、ζ に写る。
GoldenInt と円分整数環を環同型だとする誤った次数の同一視は行わない。

## 3. 相対ノルムは本当にノルムである

二次モデルの左乗法行列は

\[
 \begin{pmatrix} A&-B\\B&A+(\phi-1)B\end{pmatrix}.
\]

その行列式は `A²+(φ−1)AB+B²`。このノルムを上の環同型で輸送し、
`quinticGoldenNorm_eq_algebraNorm` により `Algebra.norm` との一致を証明した。
整数性は結果の値を整数と仮定したものではなく、整数基底の同型から得られる。

相対共役 σ は ζ を ζ⁴ に送り、黄金比整数部分を固定する。
実装したノルムを埋め戻すと `x*σ(x)` になる。
既存 GoldenInt への輸送は
[FiveGoldenRelativeNorm.lean](../../../DkMath/FLT/Kummer/FiveGoldenRelativeNorm.lean)
で行う。黄金比共役を ι と書けば

\[
 \boxed{N(a+\zeta b)=\iota\langle a^2+b^2,-ab\rangle},\qquad
 \boxed{N(\zeta-1)=3-\phi=\iota(2+\phi)}.
\]

これはノルムの値5の比較ではなく、分岐因子そのものの元の等式である。
差の向き `a=w,b=−v` では交差座標は `wv`、和の向き `a=u,b=v` では `−uv`。
両者が既存の `SignedSquareGoldenSource` の規約と一致する。

## 4. 五次 Kummer 単元補題を実際に供給する

[FiveKummerUnit.lean](../../../DkMath/FLT/Kummer/FiveKummerUnit.lean) の
`quintic_kummer_unit_power_criterion` は

\[
 \delta\in\mathcal O_K^\times,\quad
 \delta\equiv n\pmod5\quad\Longrightarrow\quad
 \exists\kappa\in\mathcal O_K^\times,\ \delta=\kappa^5
\]

を証明する。外部の flt-regular や未証明 criterion を渡す必要はない。

まず二次ノルムの有限恒等式により `N(δ)≡n² mod 5`。
`N(δ)` は黄金比単元である。既存の `goldenUnitClassesModFifth` と、
パケットに依存しない単元の合同計算を使い、`N(δ)=v⁵` を得る。
この段階で使用するのは一般的な黄金比単元の分類であり、旧パケットの β の
五乗抽出・旧パケットの非零セクター排除ではない。

次に Mathlib の CM 体の定理 `unitsMulComplexConjInv` から
`ρ=δ/σ(δ)` が根付き単位であることを得る。
構成した相対共役が CM 共役と一致することも、整数冪基底の生成元で証明した。
五次円分体の根付き単位は `±ζʳ, 0≤r<5`。
整数合同から `ρ≡1 mod 5` となり、四次整数基底の係数を比較すると `ρ=1`。
非自明位相の係数 ±1,±2 は5で割れないからである。

従って `δ=σ(δ)`、`δ²=N(δ)`。v を円分整数環へ埋め込んだ単元を η とすれば
`δ²=η⁵` なので

\[
 \boxed{\kappa=\delta\eta^{-2},\qquad \kappa^5=\delta}
\]

と根を明示できる。mod λ の合同だけではこの補題の入力に足りない。
回帰例では `λ∣ζ−1` だが `5∤ζ−1` を検査している。

## 5. 同じ β への復元

[FiveGNSameBeta.lean](../../../DkMath/FLT/Kummer/FiveGNSameBeta.lean) では
Mathlib の `IsCyclotomicExtension.Rat.five_pid` から類数1を供給する。
GN の分岐イデアル冪抽出、主イデアル化、λ⁵ の単元合同、上の五次単元補題から

\[
 a+\zeta b=(\zeta-1)\theta^5
\]

を得る。その相対ノルムを取り、黄金比共役を戻すと

\[
 \alpha_G=(2+\phi)\,\iota(N\theta)^5.
\]

既存 q が保持する `q.alpha=(2+φ)*q.beta` と比較し、非零の同じ `2+φ` を消去する。
公開した局所終点は

```lean
exists_fifth_eq_stripped_beta_via_GN
  (q : SignedGoldenRamifierStrippedPacket u v w) :
  ∃ θ : GoldenInt, q.beta = θ ^ 5
```

であり、q の β を選び直さない。既存の根と今回の根が等しいと主張する必要もない。
元の座標・ノルム・第二座標・互いに素性は q に保持される。
和と差の両方で、平方境界 `(a+b)²=5⁸A¹⁰` から `5∣a+b`、原方程式から
`5∣c` を供給し、分岐側の条件も追加仮定にしない。

## 6. FLT5 で無限降下を可能にするもの

[FiveGNDescent.lean](../../../DkMath/FLT/Kummer/FiveGNDescent.lean) は
同じ β の五乗根 γ の第二座標とノルムから、既存の
`GoldenZeroSectorCandidate` と `GoldenZeroSectorDescentPacket` を実際に構成する。
その入力では `s*H(r,s)=−5⁶A¹⁰`、座標の互いに素性、十分な5進深度を保持する。

重要なのは、既存 `GoldenZeroSectorDescentPacket.strictDescent` が、
**同じ不変条件を満たす次のパケット**と、第二座標の絶対値の厳密減少を返すこと。
新しい強帰納法はこの一段の構成を繰り返して閉じる。
降下内部の lift の再五乗抽出と単元分類は引き続き使用する。

## 7. 二つの依存監査の意味

[FiveGNDependencyAudit.lean](../../../DkMathTest/FLT/Kummer/FiveGNDependencyAudit.lean)
は型、宣言本体、opaque 本体、帰納型の構築子を再帰的に検査する。

| 監査する境界 | 禁止・要求する内容 |
| --- | --- |
| 同じ β の五乗根 | 旧 GoldenInt の五乗抽出も禁止。GN イデアル冪・新しい単元補題・相対ノルムを要求 |
| 新しい FLT5 終点 | 旧 FLT5 完成済み終点と初期パケットのセクター排除を禁止。既存 lift の再抽出と厳密降下を要求 |

従って「最初の β の抽出を置き換えた」と「証明全体から黄金比単元分類を除去した」は
異なる主張である。今回証明したのは前者であり、一般単元分類は新しい単元補題にも使う。

16 件の回帰例と新規公開62宣言の公理監査に成功した。同じ β の根の依存監査は
74,704 宣言・72,020 本体、FLT5 終点の監査は75,120宣言・72,425本体を検査した。
公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。
公開入口・指定テストのビルドは10,515 jobs、終了コード0。`import DkMath` の smoke も成功した。
これは DkMathTest 全体の実行ではない。FLT3 の既存 GN 回帰と依存監査も同時に通した。

## 8. FLT7 の何が不足するか：現在のソースからの照合

以下の比較は既存ソースの確認と、その上での推論を区別する。

**ソースで確認した事実。** FLT7 側には既に次がある。

- [SevenRamifiedFusionCyclotomicDegreeSixCarrier](../../../DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean)：実三次環上の二次拡大、原始七乗根、向き付き因子とその共役の積の一致。
- [SevenRamifiedFusionCyclotomicDegreeSixPID](../../../DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean)：円分整数環からの写像の単射・全射と PID 性の輸送。
- [CurrentCarrierNormalizedPower](../../../DkMath/FLT/Seven/CurrentCarrierNormalizedPower.lean) の `currentCarrier_ramified_element_receiver`：現在の因子を分岐因子×単元×七乗へ戻す。元の Fermat 方程式も保持する。
- [SevenRealCubicUnitClass](../../../DkMath/FLT/Seven/SevenRealCubicUnitClass.lean) の `unit_isSeventhPower_iff_projectiveLog_eq_zero`：実三次単元が七乗であることと、二成分の射影対数が零であることの同値。
- [SevenRamifiedFusionStrictDescentFailureBoundary](../../../DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean)：内部座標の7進深度 `4<5` と、これを新しい反例の carrier に復元するための明示的な未充足の契約。

従って「FLT7 は類数が未解決」「実三次単元の七乗判定そのものが無い」という説明は
この checkout の到達点には合わない。

さらに [FiveSevenComparison.lean](../../../DkMathTest/FLT/Kummer/FiveSevenComparison.lean)
では、既存の実三次単元の判定を実際に使う限定的な照合を追加した。
実三次単元 u が整数と mod 7 で合同なら、非定数二係数が mod 7 で消え、
射影対数は零になる。その結果 u は七乗となる。
これは六次環の現在の単元について、その合同条件を供給したという定理ではない。

**今回の実装からの推論。** 優先する接続は次の三つに絞れる。

1. 現在の六次因子・分岐因子・単元を、同じ来歴のまま相対ノルムで実三次環へ運び、今回の primary 単元の入力条件との対応を証明する。
2. その実三次単元の射影対数が零になることを、現在の source と合同深度から供給する。相対ノルムは位相を失うので、六次へ戻すには共役比の位相も同時に解析する。
3. 得た根から、再び同じ条件で処理できる次の不変パケットと、整礎な測度の厳密減少を構成する。

一般の [GNRamifiedPrimary](../../../DkMath/FLT/Kummer/GNRamifiedPrimary.lean) は、
仮定を満たす標準 GN7 因子の primary 単元 δ について、既に整数との mod 7 合同を供給する。
現在の六次 carrier が保持する未解析単元 u と、その δ を元の等式で対応付けることが
必要である。u をそのまま δ と同一視して、合同条件を流用することはできない。

また今回の平方からの復元は、七次なら `δ²=η⁷` から
`(δ η⁻³)⁷=δ` という同じ群の計算になる。これは条件付きの代数計算であり、
現在の六次単元にその平方等式を供給したという実装結果ではない。

FLT5 の単元補題では、`N(δ)` の五乗性だけで止まらず、`δ/σδ=1` も証明した。
回帰例 `N(ζ)=N(1)=1` が示すとおり、相対ノルムだけでは位相を回復できない。
ここが FLT7 にも保持すべき情報である。

## 9. 教科書の一ページとしての結論：減る量だけでは降下にならない

| 次数 | 根の確定までの今回の接続 | 降下が閉じる不変条件 |
| --- | --- | --- |
| 3 | 円分整数環と Eisenstein 環の同型、同じ β の三乗根 | 次も正の原始 FLT3 解、積が減少 |
| 5 | 黄金比整数上の相対二次ノルム、同じ β の五乗根 | 次も黄金比の零セクターパケット、`|snd|` が減少 |
| 7 | イデアル冪・単元倍七乗・実三次単元判定の資産は既存 | 現在の source からの合同条件・位相解析と、次の不変パケットへの再入が研究対象 |

FLT5 は次の正の Fermat 三つ組を毎回構成する代わりに、内部の黄金比パケットで降下を閉じる。
これに倣い FLT7 でも、既存の「新しい反例への復元」契約を満たす経路に加え、
内部の算術パケットだけで閉じた降下を設計する余地がある。これは次の研究案であり、
今回構成・検証した FLT7 の降下ではない。

既存の深度 `5→4` は実際の減少だが、その一段で終わらず次にも同じ構成を適用できる
証明が必要である。根が取れること、量が減ること、次の入力が作れることを別々に保持し、
最後に同じパケットで結ぶ。この区別こそ、FLT3・FLT5 の実験から FLT7 へ持ち込める視点である。
