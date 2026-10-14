# findings-013 — 法13の補因子 support 障害

2026-10-14。Outcome A。

実ソースと既存索引を調査した。`centeredSevenSextic`、`nestedAllocation_iff_centered`、一般 gap の法5 transport、cheap allocation、別条件の sixth-power sieve を再利用・参照した。索引の `FLT.Seven` / `thirteen` 検索は既存5宣言を返したが、今回の多項式非零性に相当するものはなかった。索引は新規モジュールを含まないため、実ソース検索でも重複を確認した。

任意の `d x : ZMod 13` に対する単一の有限全称命題を `decide` で証明し、自然数の cast と `ZMod.natCast_eq_zero_iff` により任意自然数 D,q へ移した。従って D の有限な範囲制約はない。指示書の Python 表は証明の仮定にしていない。この gate では Python の数学的事前検証を再実行していない。

`13∤r` から素数の積・冪の整除則で `13∤7^27*r^49` を導き、`13∣s` から target の13整除を導いた。既存 centered 同値の必要方向で同じ r と自然数商 M/r を保存し、64*7=448 を正規化して両 receiver を排除した。追加の positivity、coprimality、r∣M 仮定は不要だった。

M=3*13^12、r=3 の回帰定理は actual cheap 条件全体（divisor membership、coprimality、343*r^7<M、法42、GN側 branch-size）と literal sixth-power witness t=13^2 を検証した。q=2 の法5 image match は成立する。s≡1、r²≡4 (mod5) なので旧 square obstruction の十分条件は成立しない。それでも法13 support により両 exact receiver は不成立である。D≡2 の法13値域 {1,4,5,10,12} も Lean example で確認した。

初期 calibration は不存在の cast 補題名を使って exit 1。Mathlib の実際の `ZMod.natCast_eq_zero_iff` に修正して exit 0。有限全称命題自体は最初の試行から成立した。仮定の変更はしていない。

再開後の focused build と検証・公理監査はともに exit 0。3公開定理と1回帰定理の依存公理は propext、Classical.choice、Quot.sound のみ。

数学的な解釈として、法13で7乗写像が単射であることは差の7乗表示による説明と整合するが、その抽象的説明は今回形式化していない。形式証明は実多項式の有限体計算による。r=3 の排除から全 eligible divisor の排除、full-sieve 不存在、packet の存在・不存在、任意素数への一般化、FLT7 は導いていない。
