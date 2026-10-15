# History of FLT-regular-to-GN-GTail-261015-v0

## Log

### 日時: 2026/10/15 JST

1. 目的: GN・GTail から円分因子、イデアル、類群、単元へ進む教科書的な Lean 接続を作る。
2. 実施: 既存 Kummer / GapFocusing / neutral ideal APIs を調査。Phase の証明を Lib へ移し互換入口を保持。整数ノルム、主イデアル積、共通素イデアルの分類、非分岐側のイデアル冪抽出、正則性からの単元倍冪復元を実装。全切断の剰余主イデアル等式も追加。
3. 結論: `GN_kummer_structure_of_regular` が整数上の方程式・原始性・非分岐条件・類数条件から各円分因子の単元倍 p 乗表示を返す。FLT の最終矛盾ではない。
4. 検証: 実行コマンド・終了値・公理依存は `evidence/validation.txt` と `evidence/axioms.txt` に記録。回帰例と公理の自動 whitelist を追加。
5. 失敗事例: ノルムの整数環 coercion は `algebraMap (𝓞 K) K` の等式を明示して解消。イデアルの零冪は `zero_pow` ではなく `Ideal.bot_pow` を使う。整数環への FLT 輸送は環上の符号付き恒等式と `exact_mod_cast` で整理した。
6. 備考: Phase の移設は print label を除き元の証明テキストと一致。旧 Kummer の降下核にある既存 `sorry` と新しい証明群の依存を区別した。参照正本の定義・Case I/II 構成は外部ソースと照合した。
7. 次の課題: 標準 Case I 入力への adapter、単元の合同解析、分岐素イデアルの正確な冪除去、Case II の無限降下。Carry は別の定理群として未着手。
