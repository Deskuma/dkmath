# NOTE-024: ノルム次数と無限遠点を含む付値輸送

日付: 2026-10-21。NOTE-022の同じ分子・商に対して、標数0、n≠0、nT=Oの下で

\[
\deg\operatorname{Norm} f_{n,T}=n^2-\mathbf1_{T=O},\qquad
\operatorname{ord}_O w_{n,T}=\begin{cases}-1&T\ne O,\\0&T=O\end{cases}
\]

を証明した。さらに任意の点P,Sと非零有理関数hについて

\[
v_P(\tau_S^*h)=v_{P+S}(h),\qquad
\operatorname{ord}_P(\tau_S^*h)=\operatorname{ord}_{P+S}(h)
\]

を、Oを移動元・移動先とする場合も含めて証明した。付値の公式は零関数にも成立する。
既存のWeil関数では、全点の位数が二つのファイバーの指示関数の差となり、nS=Oなら全点で位数が保存される。
比例定数c(S,T)・その乗法則・Weil対の存在や非退化性・円分行列式の無条件化は後続の境界である。

## 1. 公開入口と読み順

| モジュール | 教科書としての内容 |
| --- | --- |
| `EllipticPointIdealNorm` | CRTと剰余体の次元1から、相異なる有限点の積のノルム次数を数える |
| `EllipticInfinityValuation` | ノルム次数の付値を座標環から同じ関数体へ延長する |
| `EllipticWeilInfinity` | 同じWeil分子の次数、Oでの位数、全点の位数公式 |
| `DiscreteValuationRigidity` | 付値環の一致と値群への全射性から正規化まで一致させる |
| `EllipticValuationTransport` | 局所合同・点イデアル冪・局所環の分母表示による輸送 |
| `EllipticTranslationValuation` | 割線と接線による有限点間の付値輸送 |
| `EllipticInfinityClassification` | xが極を持つ場所の付値環を分類する |
| `EllipticTranslationInfinity` | −SからOへの例外輸送、任意の有理関数への拡張 |
| `EllipticWeilTransport` | 移動元Oも含めた統一APIと、torsion移動での保存 |
| `DkMath.FLT.FreyWeilTransport` | 同じSourceの曲線・分子・商へ接続する |

先頭9本は`DkMath.Lib`、最後は`DkMath.FLT`から公開し、ルート`DkMath`へ接続した。
新規Leanファイルには日本語の教科書docstringと、import後の正確な`#print "file: ..."`を置いた。
一般の付値構成・輸送は標数0を要求せず、Weil分子・商への適用で標数0を使う。
整数位数はh≠0を引数に持ち、log 0の便宜的な値を零関数の位数とは解釈しない。

## 2. 総付値の一般論をCRTで短縮する

相異なる点の有限集合sに対し、(r)=∏Q∈s m_Qなら、Oの単位イデアルを取り除き、

\[
A/(r)\simeq\prod_{Q\in s\setminus\{O\}}A/\mathfrak m_Q
\]

という実際の中国剰余同型を構成する。各剰余体は係数体と同型なので、その次元は1である。
Mathlibの`finrank_quotient_span_eq_natDegree_norm`と合わせると、ノルム次数は有限点の数になる。
点イデアルの積の非零性からr≠0も証明し、零元へ次数公式を誤適用しない。

これを`span_weilNumerator`の同じ生成イデアル等式へ適用する。
NOTE-022のファイバー点数n²と、Oがファイバーに入ることとT=Oの同値から

\[
\deg\operatorname{Norm} f_{n,T}+\mathbf1_{T=O}=n^2
\]

をまず自然数で示し、整数の減算式へ移す。n=1,T=Oの境界でも次数0が得られる。
参照実装の任意の素イデアル冪の濾過・重複度の無限総和は移植せず、今回の相異なる一重点に必要な範囲で証明を短縮した。

## 3. 無限遠点の位数は実際のValuationから読む

座標環の二元基底p(x)+q(x)yについて、ノルムの次数は偶数2deg pと、q≠0のときの奇数2deg q+3で支配される。q=0なら前者だけを使う。
この次数から、非零元rにexp(deg Norm r)、零元に0を与える付値を構成し、同じ分数体へ延長した。
乗法性・和の非Archimedes不等式・延長の条件を証明しており、次数差だけを記録する台帳ではない。
整数位数は−log vであり、分子と分母のn²が商で消えて、非零目標の一重極−1が残る。

`pointOrder_weilFunction`は、Oも含む全点Pで

\[
\operatorname{ord}_P w_{n,T}=\mathbf1_{[n]P=T}-\mathbf1_{[n]P=O}
\]

を与える。これは因子公式の点ごとの内容であり、形式的な因子型を新設したという主張ではない。
`pointValuation_weilFunction`は同じ公式を乗法的なexpの値としても与える。

## 4. 割線・接線・無限遠点をつなぐ

通常のP≠O、P+S≠Oでは、一般点とSの加法公式をPの局所環で評価する。
x座標が異なる割線の場合と、P=Sの接線の場合を分け、座標の局所合同を証明する。
素イデアル冪への帰納と局所環の分母表示で付値環の包含へ進み、離散付値の剛性から等号を得る。

例外P=−Sでは、移動後のxが極を持つことを証明する。
xを含まない付値環では、曲線方程式からv(y)²=v(x)³となり、二元基底の偶奇次数が相殺しないことから付値環を一意に定められる。
ただし付値環の一致だけでは正規化は確定しない。x,yのノルム次数2,3を使い、y/xの値exp(1)と整数冪から値群への全射性を証明する。
これで有限点−Sの引き戻し付値と、構成した無限遠点の付値そのものが一致する。
最後に座標環元の商表示で任意の有理関数に延長する。

移動元がOの場合は、−Sでの例外輸送を逆移動に適用し、自己同型の合成則で相殺する。
`pointValuation_transEquiv`はこの三つの場合を統一する。
`pointOrder_transEquiv_weilFunction_of_torsion`は、n(P+S)=nPから同じWeil関数の全点での位数保存を得る。

## 5. 回帰・監査・検証

`FreyWeilTransportTest`は既存のSource 2=(4,3,5)の同じ曲線を使う。
非零2-torsion点Tと2R=Tとなる実在する点Rについて、次数4と3、指数1の次数0、指数37の次数1368、
分子のOでの位数−4、商のOでの一重極−1、零目標の相殺を検査する。
T+T=Oとなる例外移動、Oからの移動、Rでの通常移動の一重零点、Source入口での全点の位数保存も検査する。

`Note024DependencyAudit`は新規本体90宣言・回帰12宣言の公理と、11経路の型・opaque本体の依存を調べる。
許可公理は`propext`・`Classical.choice`・`Quot.sound`のみ。
CRT、商次元とノルム次数、同じ生成イデアルとファイバー点数、局所化した付値、割線・接線、無限遠点の分類と正規化、
逆移動、実際のSourceを対応する経路で要求する。
選択経路では外部未移植provider・Weil対データ・旧FLT終点・大域Kummer入力を禁止する。
一般の環・付値輸送の経路ではDkMathのtorsion表現providerも禁止する。

検証結果は[validation-note024.txt](evidence/validation-note024.txt)、
ルートからの到達と公理表示は[RootSmokeNOTE024.lean](evidence/RootSmokeNOTE024.lean)に記録した。
focused buildは3201 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`は11625 jobsで成功した。
ルートsmokeと`lake env lean DkMathTest.lean`の直接検査も成功した。
新規モジュールに警告はなく、統合ビルドでは既存の別モジュールのsorry警告5件が再掲された。
trackerの照合、全新規Leanファイルのマーカー・空白・禁止構文・帰属先ファイルの検査、`git diff --check`も成功した。

## 6. 参照元と翻訳の帰属

Anthropicの実装を読み、P2Mのマクロ・未移植providerへの参照を除いて、DkMathの実証明へ接続した。
Apache-2.0の帰属、LICENSE/NOTICE参照、取得したblobと変更点を各翻訳ファイルに記した。
主な参照は次の通り。

- [引き戻しと局所合同](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean): blob `ce8783a9e9613db1c4c0323ce93fb0d89917ee65`。
- [無限遠点の付値構成](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm.lean): blob `bee7e29c4b6a040b634b7ba3d71e99df35d5ec15`。
- [無限遠点の付値環の分類](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_eq_valuationSubring_of_X_not_mem.lean): blob `77ec6596ddaf12e4de19635fcfd99853dfe90caa`。
- [付値の剛性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Valuation_eq_comap_of_valuationSubring_le_comap.lean): blob `69f526a63f694ae657c2cce36e1dfdde40e90c32`。
- [割線の輸送](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_le.lean): blob `40979bfb1f6b10e41bc74964bdacaa9ad0107795`。
- [接線の輸送](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_le_self.lean): blob `69bc96ee3ad715d6e8bb140d20e02817466e53d4`。
- [例外点での輸送](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap.lean): blob `0d75c45594a92350089fb4b7551926c1261e0e6b`。
- [Weil関数への輸送](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_weilFun.lean): blob `c0885c4b116e8e30adac07f430e44e2160b3f6f6`。

NOTE-024の二つの優先目標を対象とし、比例定数以降の未解決境界を保持する。
