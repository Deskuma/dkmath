# AnalysisGN — GN・完成・素数住所の再分析

2026-10-23。作業ブランチ：`lib/FLT-GN-Completion-261023-v0`。

032の `hno` に進む前に、会話資料の数学と現在のLean実装を照合するための入口である。
初回は資料整理と実装計画を作成した。続くGN-LIB-001で再帰・隣接支持の17定理をLibへ移管した。
続くGN-LIB-002で完成の三者gcd・素数支持・付値の一般橋を13宣言として固定した。
GN-LIB-003aではBinomTailの一般尾項・正性の5補題をLibへ移管した。
GN-LIB-003bでは平方完成・有限帯の一般核7定理と、旧carrierの7wrapperを固定した。
GN-LIB-003cでは素数冪二項係数の正確な付値と整除性の4定理を中立化し、旧4名をwrapperにした。
GN-LIB-004では有限和R_nと完成不足D_nの3定義・24定理を固定し、再帰・上界・正性を証明した。
GN-LIB-005aでは奇数・原始座標の完成不足coprimeと既存GNへの橋を12定理で固定した。
GN-LIB-005bでは加法公式・強可除性・正確な因子除去と原始三項を4定義・25定理で固定した。
GN-LIB-006aでは位数・円分根・LTEの25宣言を中立化し、全余因子の素数住所5定理を追加した。006a単位での結果を記録した。
GN-LIB-006bでは斉次評価・単一層住所・境界の25宣言を移管し、実座標の1定義・13定理を追加。006の一般核を完了した。
詳細は [001](IMPLEMENTATION-GN-LIB-001.md)・[002](IMPLEMENTATION-GN-LIB-002.md)・[003a](IMPLEMENTATION-GN-LIB-003a.md)・[003b](IMPLEMENTATION-GN-LIB-003b.md)・[003c](IMPLEMENTATION-GN-LIB-003c.md)・[004](IMPLEMENTATION-GN-LIB-004.md)・[005a](IMPLEMENTATION-GN-LIB-005a.md)・[005b](IMPLEMENTATION-GN-LIB-005b.md)・[006a](IMPLEMENTATION-GN-LIB-006a.md)・[006b](IMPLEMENTATION-GN-LIB-006b.md) の実装報告に記録する。
資料内のZIP配置手順や実装提案は設計資料として検討し、そのまま実行する指示とは扱わない。

## 読む順序

1. [再分析と数学的境界](REANALYSIS.md)：何を一般定理として固定でき、何がまだ橋を必要とするか。
2. [現行ソースの定理棚卸し](THEOREM-INVENTORY.md)：添付監査36宣言と追加22宣言、仮定、所有層、再利用先。
3. [実装計画・昇格規約](IMPLEMENTATION-PLAN.md)：配置、旧API、`[DkMath.Lib]` マーカー、検証契約。
4. [ROADMAP](ROADMAP.md)：工程別の依存、完了条件、次に実装する単位。

## 初回の整理で変わった点

- 添付監査の36宣言は現行ソースに存在し、うち16宣言は既にLib配下にある。追加調査を含め58宣言・42所有モジュールを棚卸しした。
- `GapFocusing.Successor/Support` の隣接次数再帰・互いに素性、円分住所、範囲付きLTEは既存である。これらを新規研究結果として重複実装しない。
- `R_n` は `GTail n 1 (x-y) y` に接続できるが、標準定義は除算不要の有限和を使う。`R_n` の不足と、GNのBodyに加えるGapは異なる量である。
- 最初の新規一般APIは、GNのBig・Body・Gapの三つのgcdを同時に扱う橋とする。次に既存の再帰から完成不足の漸化式へ進む。
- 素数住所の一般核は既存の応用層から抽出する。新しい原始素数の存在や付値1を、隣接次数の素因数分離から導かない。
- 昇格マーカーは実際にLibで証明・検証した後に付ける。候補だけには「昇格済み」を示すマーカーを付けない。

## 入力資料

| 資料                                                                      | 位置づけ                                                                              |
| ------------------------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| [会話記録](6ad8f60c_2026-1021-172741_指数ゲージとFLTのズレ+128249-776.md) | 5,080行。発想、修正された予想、実験、統合案を含む一次資料                             |
| [添付監査表](DkMath_Completion_Audit_20261023.md)                         | 2026-10-22 snapshotに対する36宣言・30ファイルの存在確認。元の監査ではLeanビルド未実施 |
| [Facade ZIP](DkMath_Completion_Facade_20261023.zip)                       | 未適用の設計素材。3 facadeと1テスト、README、AUDITを収録                              |
| [data-1](data-1/)                                                         | 初回実験のPythonとCSV                                                                 |
| [v2研究ノート](data-2/DkMath_gauge_v2_research_note.md)                   | 強可除性、付値補填、次数別gcd                                                         |
| [v3研究ノート](data-3/DkMath_gauge_v3_research_note.md)                   | 有限個の素数での局所完成、CRT、特殊な素数脱出構成                                     |
| [v4研究ノート](data-4/DkMath_gauge_v4_research_note.md)                   | 原始ABC三項、次数半減、y>1での構成                                                    |

提供資料は24ファイルで、CSVは14個ある。研究ノートが参照するCSVのうち5個は現在の資料群にない。
欠落分を推測で補わず、[データ再点検](evidence/data-review.json) に一覧化した。

## 証拠の区別

- 初回棚卸し時点の宣言・仮定・import確認：[source-inventory.json](evidence/source-inventory.json)。移管後の対応は [GN-LIB-001](evidence/gn-lib-001.json)、新しい完成の一般橋は [GN-LIB-002](evidence/gn-lib-002.json)、BinomTailの移管は [GN-LIB-003a](evidence/gn-lib-003a.json)。
- 有限CSVの具体例2,183行と、別の有限範囲2,587ケースの整数再計算：[data-review.json](evidence/data-review.json)。一般定理の証明ではない。
- 初回棚卸しの既存所有モジュールのビルドと宣言確認：[validation.txt](evidence/validation.txt)。新しいCompletion facadeや新規数学を検証したものではない。

## 検証分担の更新

003b以降はユーザー指定により、本体の対象モジュールだけを当方でビルドする。
フルビルドはユーザーが担当し、`DkMathTest`・`lake test` 側のビルドは省略する。
各報告書に対象範囲を明記する。

## FLTとの境界

031-005で `hcases` は供給済みである。残る `hno` は、同じ向き付きFrey SourceにCofixed安定直線が存在しないという主張である。
本計画のGN恒等式、素数住所、gcd、付値の整備からその主張へ至る接続は、まだ証明していない。
本ディレクトリの「Completion」は代数的な完成恒等式とその算術を指し、FLTの証明完了を意味しない。
