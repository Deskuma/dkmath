# findings-014 — small-coefficient prime-power ownership

2026-10-14。Outcome A。

## 既存定理の棚卸し

実ソースで `SixthPowerSievedNestedCondition` の divisor membership、商との coprimality、coarse size、exact GN/RHS disjunction を確認した。gate 012 の `eligible_primitive_divisor_two_prime_pow` は c=2 固有であり、その Euclid・商の分解手順を一般 c に適用した。gate 013 の同じ r に対する法13 support consumer と、divisor guard を明示的に要求する既存法42 consumer を再利用した。

既存 SQLite 索引では c=2 定理を確認した。`smallCoefficient` の検索は0件。索引の gate 013 consumer 検索も0件だったが、実ソースには存在するため、索引の不完全性を補って実宣言を確認した。新規定理名の実ソース検索で今回の宣言以外の重複はなかった。既存 production ファイルは変更していない。

## 数学的成立範囲

提案された generic theorem はそのまま成立した。p は素数、c≤343、実際の membership/coprimality/size だけから r∣c を証明した。p∤r なら r と p^n が互いに素なので Euclid により r∣c。p∣r なら coprimality により p∤t (t=M/r)、同様に t∣c。size から c>0 を導けるので t≤c≤343、実際の分解 M=r*t と r≤r^7 により M≤343*r^7 となり strict size に矛盾する。

c=0 は size と矛盾し、追加の c>0 仮定は不要。n=0 も generic theorem の範囲に含む。c≤343 の場合 n=0 の eligible witness は size 上存在できないが、証明は例外扱いや追加仮定を必要としない。DkMathTest に両境界の API 適用を置いた。

c=3,p=13 では r∣3 から r=1 または r=3。r=1 の商は3の倍数で、法42で1なら法3でも1となり矛盾する。ここには n の parity や residue class は不要。r=3 の商は13^n で、n>0 により13を含む一方13∤3。gate 013 が両 receiver を排除する。full-sieve witness の実際の guard を使い、別途 r=3 が全 n で eligible だとは仮定しない。

k↦3*13^(k+1) の単射性を、左の正整数係数の消去と `Nat.pow_right_injective` により証明した。全 k の排除と組み合わせて、相異なる抽象 core の無限族が得られる。n=12 の全 core 排除は今回の普遍定理から検証した。gate 013 の fixed-divisor cheap/sixth-power 回帰は従来の検証コードに保持されている。

## 試した命題と条件の必要性

c≤343 を完全に取り去った所有則は偽である。c=21953,p=2,n=1,r=2 は membership、coprimality、343*r^7<M を満たすが r∤c。この countermodel を Lean の `decide` で固定した。これは343という閾値が最適という主張でも exact endpoint の存在主張でもない。

初回 calibration は exit 0、unused simp argument の警告1件のみ。余分な `Nat.mul_mod` を除去した production focused build と検証モジュールは exit 0。新規4公開定理と countermodel の依存公理は propext、Classical.choice、Quot.sound のみだった。Python 数学 precheck は実行せず、数学的主張は Lean で検証した。

今回の結果はこの抽象 full-sieve の排除に限る。packet の存在・不存在、gate 005 の source–real-pair–chart bridge、任意 core 排除、unconditional FLT7 は証明していない。gate 014 で終了する。
