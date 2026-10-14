# findings-015 — prime-side avoidance and complementary support

2026-10-14。Outcome A。

## 棚卸しと証明経路

gate 014 の所有則の実際の証明、gate 013 の同じ r に対する法13 consumer、full-sieve の membership/coprimality/size/exact branch の実定義を確認した。既存索引の `smallCoefficient` 検索は0件であり索引は最新モジュールを含まない。実ソースで gate 014 の宣言を読み、新規 API の重複を確認した。既存の別用途の coprime prime-not-dvd 補題は、この係数・サイズ条件の結論とは異なる。

r∣c だけでは、p∣c の場合に p∤r は導けない。c=p=r=13 の整除関係を countermodel として Lean で固定した。これは eligible allocation の反例ではなく、整除関係だけからの不適切な推論の反例である。

gate 014 の捨てた p∣r 分岐の矛盾を、新しい standalone 定理で再利用した。t=(c*p^n)/r とすると、coprimality から p∤t、Euclid から t∣c。size から c>0 を導き、t≤c≤343 と実際の分解 M=r*t から M≤343*r≤343*r^7。strict size と矛盾する。従って p∤r。既存ファイルの refactor はしていない。

n>0 なら p∣p^n、従って p∣M。membership が与える r*(M/r)=M に prime の積整除則を適用し、p∤r と合わせて p∣M/r を得た。c と p の coprimality は不要であり、c に p が含まれていても成立する。

p=13 では full-sieve witness の実際の guard からこの support pair を得て、gate 013 consumer により両 exact receiver を排除した。法42、c の divisor 列挙、c の合同条件、指数上限、literal sixth-power witness は使っていない。

## 境界と回帰

prime avoidance 定理は n=0 も含む。c=0 は size と矛盾し、r=0 は divisor membership が禁じる。追加の positivity 仮定はない。補因子 support と主 exclusion では n>0 を明示した。n=0 の補因子 support を主張する API は追加していない。

c=1,3,13,343,0 の各 coefficient について任意正指数の exclusion を Lean example で検証した。c=13,n=2,r=1 は実際の membership、coprimality、coarse size を満たし、generic bridge から13∤rと13∣M/rを検証した。係数自体が13を含むケースの support は vacuous な適用だけではない。

3*13^12 の whole-core exclusion を今回の generic theorem から回復した。gate 013 test は test 側だけで import し、既存 fixed-r cheap/sixth-power passage と今回の whole-core exclusion の両立を named regression として確認した。全 c,n の cheap passage は主張していない。

係数343は t≤343 の比較に十分な上限であり、最適性の定理ではない。上限を完全に外した所有則の反例は gate 014 の既存 test に保持されている。

## 検証と範囲

DkMathTest calibration は exit 0、警告なし。focused build は exit 0、9093 jobs。新規 test は exit 0。3公開定理と3 named test 定理の依存公理はすべて propext、Classical.choice、Quot.sound のみ。数学的 Python precheck は実行せず、主張は Lean で検証した。

これは bounded c と unbounded positive n の抽象 core class に対する full-sieve 排除である。実際の source core がこの class に入ること、packet の存在・不存在、gate 005 bridge、FLT7 は証明していない。optional source corollary や all-n 拡張は追加せず、gate 015 で終了する。
