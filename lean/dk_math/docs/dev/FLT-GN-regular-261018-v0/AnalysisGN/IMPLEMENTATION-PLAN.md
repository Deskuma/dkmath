# 実装計画 — 一般核の所有化とCompletionの教科書

2026-10-23。対象ブランチ：`lib/FLT-GN-Completion-261023-v0`。
本書は工程ごとの実装契約である。未着手工程にある新規モジュール名と宣言名は設計名である。
初回は[棚卸し](THEOREM-INVENTORY.md)と既存宣言の確認を行った。
GN-LIB-001・002・003aは実装済みであり、[001報告](IMPLEMENTATION-GN-LIB-001.md)・[002報告](IMPLEMENTATION-GN-LIB-002.md)・[003a報告](IMPLEMENTATION-GN-LIB-003a.md) に結果を記録する。

## 1. 所有層と数学の範囲

| 層                             | 所有するもの                                          | 逆importしないもの                  |
| ------------------------------ | ----------------------------------------------------- | ----------------------------------- |
| Mathlib / `DkMath.Lib.Algebra` | 一般環・半環の式、順序と正性、有限和                  | 個別研究のBody定義・素数世界        |
| `DkMath.Lib.Cosmic`            | GTail/GN、再帰、完成、gcd、位相との一般橋             | FLT、ABC、Legendre、CFBRC           |
| `DkMath.Lib.NumberTheory`      | 素数・乗法位数・二項係数・付値の中立核                | アプリ固有のcarrierや未証明provider |
| `DkMath.NumberTheory.*`        | 既存名の互換入口、prime world、平方殻、研究用consumer | 下位Libへアプリ意味論を押し戻さない |
| `DkMath.FLT.*` 等              | 同じSourceへの特殊化・実際の反例状態との接続          | 一般GN定理の別コピー                |

所有ファイルをLibへ移すことと、namespaceを全て`DkMath.Lib`へ改名することは別である。
`GTail`などの歴史的namespaceは保持する。既にLib配下の宣言は移動し直さない。

## 2. 最初の実装単位

### GN-LIB-001：既存の再帰と隣接素数支持をLib所有にする

対象：棚卸しB01–B05、`GapFocusing.Successor` と `Support` の必要な証明閉包。
配置済み：`DkMath/Lib/Cosmic/GNSuccessor.lean`、`GNSupport.lean`。
以下はこの移管で維持した契約である。

- 再帰の二表示、Natの隣接coprime、CommRingのIsCoprime版を元の仮定で移す。
- 次の次数の素因数が直前にないというB05の意味を保持する。全過去次数に対する原始素数存在へ強めない。
- 元の`DkMath.NumberTheory.GapFocusing` namespaceを維持し、旧所有モジュールは新所有モジュールをimportする互換入口にする方式を第一候補とする。
- 宣言を同じ全修飾名で二重定義しない。所有権を移す場合は旧本体を削除し、互換importと昇格説明を残す。
- `Phase`→`GNPhaseFactorization`の既存設計を先例にする。

完了条件：旧import・新importの双方から同じ型へ到達し、d=0、零座標、一般環の仮定を保持する。
新所有モジュールからアプリ層へ逆流しない。昇格マーカーは§5に従う。

### GN-LIB-002：Big・Body・Gapの三つのgcdを一つの契約にする

配置済み：`DkMath/Lib/Cosmic/CompletionCoprime.lean`。以下は実装で保持した契約である。
既存の`GTail`を使い、上位`CosmicFormula.Defs`のBigN/BodyNをimportしない。

自然数g,u,dについて

- Big=(g+u)^d、Body=g*GTail d 1 g u、Gap=u^d。
- 三つのgcdがgcd(g,u)^dになる等式。
- 原始座標での三者のpairwise coprime。
- gcd(g,u)=1、q素数かつq∣Bigならq∤Body、q∤Gap。
- d>0で、完成根g+uの素数支持とBigの素数支持の一致。
- g+u≠0を保持した、Bigの付値のd倍則は既存B18を使う薄い橋とする。

gcdの加法・冪に関する既存算術を先に確認して使う。一般GCDMonoidへの拡張はNat版の完成条件に含めない。
名前案は `completion_gcd_big_gap`、`completion_gcd_body_gap`、`completion_gcd_body_big`。
これらの名前で実装済み。公開API全体は [002報告](IMPLEMENTATION-GN-LIB-002.md) を参照。

回帰：(30,1,2)の960+1=961、非原始対(6,4,3)でgcdが8、d=0、零座標、完成根91の合成数例。
d>0、gcdの原始性、付値の非零条件を公開型に残す。

### GN-LIB-003：Pascal・交差項・平方完成の中立部分を抽出する

三つを別の確定単位に分ける。

1. **BinomTail（003a完了）**：A17の正性を含む5補題を `Lib.Algebra.BinomTail` へ移管済み。
   元の全修飾名を保持し、旧ファイルは互換importにした。
2. **平方完成**：A20,A21,A23から、旧`Gnomon`・`Primitive`定義を参照しない式を抽出する。
   例：x²+u(2x+u)=(x+u)²。A23の特例はこの一般式へのwrapperとして残す。
3. **二項係数付値**：A34と加法版をMathlibのfactorization定理から中立的な`Lib.NumberTheory`へ抽出する。
   `ABC.PadicValNat`は既にLibの互換入口なので、一般所有先ではLib名を使う。
   `UniformBeamHeight`などの旧carrier全体の移動を、この数式の昇格へ混ぜない。

B16の一般な素数行の正確な可除性も再利用対象である。
ただし`GNPrime37`全体は上位`CosmicFormula.Defs`をimportする。37の例と一般核の依存を分けてから最小facadeへ公開する。

## 3. 新規一般化を行う順序

### GN-LIB-004：R_nとD_nの教科書

配置候補：`Lib.Cosmic.PowerDifferenceCofactor`、`CompletionDefect`。

- 標準R_nは有限和。R_0=0、R_1=1、R_2=x+yを含める。
- B22を用い、環上でR_n(x,y)=GTail n 1 (x−y) yを証明する。
- Natの座標変換ではy≤xを保持する。有限和自体はx=yでも使える。
- 既存GN再帰から `R_(k+2)+xyR_k=(x+y)R_(k+1)` を作る。
- R_n≤(x+y)^(n−1)を先に証明し、自然数のD_nを導入する。
- `D_(k+3)=(x+y)D_(k+2)+xyR_(k+1)`、D_2=0、n≥3での正性を証明する。
- 一般環の符号付き不足と、非負のNat不足を区別する。

回帰：R_3(5,3)=49、D_3=15、R_3(18,1)=343、対角x=y、n=0,1,2。
「R_nは別の完全冪でもない」という定理は置かない。

### GN-LIB-005：gcdの偶奇と原始ABC三項

配置候補：`Lib.NumberTheory.PowerDifferenceCofactorGcd`、`Lib.Cosmic.CompletionLoan`。
依存順は次とする。

1. A10とB03/B04のR語彙への橋。
2. modulo x+yによる奇数次数のcoprimeと、gcd(R_n,D_n)=1。
3. R_(a+b)の加法公式と互除法から強可除性を再確認・構成する。
4. 奇数nで1、偶数nでx+yという、gcd(R_n,xyR_(n−2))の式。
5. h_nの分子可除性を証明し、n≥3で正のpairwise-coprimeなA+B=Cを作る。
6. R_(2m)=(x+y)R_m(x²,y²)、奇数次数の平方因子を持つ補填恒等式。
7. 偶数D_nの精密gcdは、LTEの依存が整ってから追加する。

2を3や7に依存させる必要はない。証明コストの低い奇数版を先に確定する。
追加する三項構造をABC予想の証明やFLT状態と同一視しない。

### GN-LIB-006：素数住所・付値を中立化する

棚卸しB08–B14の既存証明を再利用する。
`PrimeOrder`のZsigmondy import、`HomogeneousAddress`のCFBRC carrierをそのままLibへ逆輸入しない。
有限体の比・位数、斉次円分評価の中立的定義、アプリ固有の原始素数carrierを分ける。

- q素数、分母のq非可除性、必要な分子非可除性、n>0を保持する。
- r>1での全余因子の出現条件r∣nと、単一円分層の添字r q^kを別APIにする。
- r=1、q∣xy、q=2、n=0は独立の境界回帰にする。
- 基本住所での付値に上限1を仮定しない。R_3(18,1)=7³を回帰にする。
- 奇素数LTEと2進LTEの和の補正項を維持する。

型・opaque本体とimportグラフの双方を調べる。新しいcarrierへ移す場合は旧carrierとの同値・definitionalな互換性を先に設計する。

### GN-LIB-007：有限素数集合での補填と脱出（後続・独立）

最初はy=1の構成を対象とし、その後y>1へ進む。
任意yでの存在には、サイズ条件を入力に取る版と、その条件を満たす追加p乗因子を実際に選ぶ版を分ける。
小素数の正確な付値を維持するため、追加因子は制御対象の小素数とyへ互いに素でなければならない。

非完全冪であることを先に別の不等式で証明し、素因数分解から未完成付値の素数を抽出する構造である。
それを一般の完全冪等式の不存在証明として循環利用しない。
この工程は初回facadeや他の一般核の昇格の完了条件に含めない。

## 4. Facadeの設計とZIPの扱い

| 入口案                           | 内容                                                 | 配置時の注意                                       |
| -------------------------------- | ---------------------------------------------------- | -------------------------------------------------- |
| `DkMath.Lib.Cosmic.Completion`   | 既存Libと昇格済みの一般核                            | 下位数学だけ。一般定理の証明本体をfacadeへ置かない |
| `DkMath.NumberTheory.Completion` | Primitive、PrimorialUniverse、Legendreなどのconsumer | Libの依存先にしない                                |
| `DkMath.Completion`              | 研究用統合入口                                       | 重い応用を含む。通常の下位importに推奨しない       |

添付ZIPの11個のLib importは設計の出発点であり、全てが最小の利用者に必要とは限らない。
新規facadeは現行checkoutにはまだない。Zipの4つのLeanファイルは指定の`#print "file: ..."`を持たない。
実際の適用時にはマーカーを追加し、テストを通常入口へ登録する。
ZIP中のREADMEとAUDITをプロジェクトルートへ上書きしない。
既存の `DkMath.NumberTheory.GNPrime`、`GapFocusing` facadeとの重複を整理してから公開する。
ルート`DkMath`への重い研究facadeの自動追加は、依存とビルド負荷を確認して判断する。

## 5. `[DkMath.Lib]` 昇格マーカーの契約

マーカーは**検証済みの本体がLibに存在する**ことを示す。候補の目印には使わない。
現在既にLibにある宣言を確認しただけの状態も、今回の新規昇格とは数えない。

昇格先の定理docstringには次を含める。

```text
[DkMath.Lib] 昇格元: `元の全修飾名`（元ファイル）。
一般化: 係数型・次数・原始性など、変更した範囲。
保持条件: 正性、非零性、次数下限、素数性、零の付値規約。
互換入口: 旧モジュールと、旧名を保つ方法。
役割: この定理が保存するもの／追加の橋を必要とする結論。
```

旧名をwrapperとして残す場合、そのdocstringにも次を付ける。

```text
[DkMath.Lib] 昇格済み: `Lib側の全修飾名`。
この旧APIは従来の型を維持し、一般核を特殊化する互換入口である。
新しい一般consumerはLib側をimportする。条件を暗黙に削除しない。
```

同じ全修飾名のまま所有ファイルだけを移した場合は、新所有側の定理docstringへ昇格説明を付ける。
旧ファイルには同名の再定義をせず、import付近のモジュールコメントに移管先を示す。
物理移動と新canonical名への転送を混ぜて二重定義しない。

マーカー確認だけで完了とはしない。旧名→新所有→利用者の対応と検証結果を棚卸しへ追記する。

## 6. 各確定単位の検証

1. 下位所有モジュールだけをビルドし、元の型と仮定を確認する。
2. 旧importの互換回帰と、新importだけのスモークを別に確認する。
3. 具体例に加え、n=0,1,2、零座標、非原始対、q=2、位数1、完全冪余因子を境界にする。
4. 全新規公開宣言を公理検査し、主要経路の型とopaque本体を監査する。
5. importグラフで新しいLibから応用層への逆流・循環がないことを確認する。
6. `#print "file: ..."`、公開docstring、昇格マーカーと説明、`git diff --check`を確認する。
7. 公開facadeへ接続した段階で、対象facade、通常ルート、`DkMathTest`、直接スモークをそれぞれ検証する。

焦点を絞ったビルドの成功を、未確認の通常ルートやFLT終点の成功へ拡張しない。
条件付き定理は、その算術入力まで今回供給したかを必ず報告する。

## 7. 書き換えの単位

一つの数学的所有単位ごとに、下位本体、旧互換入口、回帰、昇格説明をまとめる。
Libの成功を確認してからconsumerのproofを一般核への呼出しへ置換する。
Legendre・Primitive・FLTの全ファイルを一括で移動しない。
確認済みの単位を小さく確定し、最後にfacadeと報告をまとめる。
032のhnoに関する新しい算術は、この一般核整備とは別の実装契約にする。
