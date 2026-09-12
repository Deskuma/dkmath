# PAIR-GN-003: 二宇宙式の Lean 検証・審判

## 判決

**PairBody に `2n` を置く保存式は正しい。提示された円・混合二次曲線の式も正しい。**
しかし、それらから素数対の全称存在は導けていない。
特に、**固定 degree `(2,3)` を全中心の Goldbach carrier とする案は偽**である。
今回、`n≡8 (mod 9)` の全中心を失うことを Lean で証明した。

任意の prime degree を許す二宇宙式は `d=e=2` を含むため、例外 `2+2` を補えば元の Strong Goldbach と同値になる。
これは前回の fixed-Big gauge と同じ定義ではない。今回の PairBig/PairGap/PairBody を新たに定義し、そのモデル自身で判定した。

## 提示された主張の照合

| 主張 | 判定 | 根拠・正確な範囲 |
|---|---|---|
| Prime GN ⇒ prime degree | 正しい | 既存定理には `d≥2,x>0,u>0` が必要 |
| prime target `P` に対し `d∣P-1`, `d<P` | 正しい | 同じ正領域。既存 representation API を再利用 |
| prime degree ⇒ prime GN | 偽 | `GN 3 1 5=91=7*13` |
| 単一 unit-boundary Big の補数は `u^d` | 正しい | `singleBig_sub_GN` |
| 上記補数を prime とする (`d≥2`) | 不可能 | `single_complement_not_prime`。`u=0,1` も含む |
| `PairBody+PairGap=PairBig` | 正しい | 全ての自然数 degree/parameter。prime 仮定不要 |
| `PairBig-PairGap=PairBody` | 正しい | 自然数の減算を含めて証明 |
| `2n=PairBody` を target として定義する | 正当 | `UnitPairAt` で具体化 |
| `2n≠Big` が任意の単一 Big に対する数値的定理 | 偽 | `16=2*8=(1+3)^2` かつ `16=3+13` |
| 正の二宇宙式で `PairBody<PairBig` | 正しい | `pairBody_lt_pairBig`。上の単一 Big との区別が必要 |
| prime row で `GN p 1 u=1+pA` | 正しい | 既存 quotient witness を再利用 |
| weighted equation `pA+qB=2(n-1)` | 正しい | `n≥1`、二つの GN 表現等式を保持すれば exact iff |
| weighted equation だけで GN の存在が出る | 偽 | `A=1,B=4,p=2,q=3,n=8`。候補3と13はprimeだが13はcubic rowにない |
| cubic circle equation | 正しい | 減算のない版は全 `n`、提示された減算版は `n≥1` で固定 |
| cubic 同士では `n≡1 (mod 3)` | 正しい | primality 仮定なしで従う |
| mixed `(2,3)` の二次式 | 正しい | `2(n-1)=2u+3v(v+1)`、`n≥1` |
| 非対称にすれば全中心を表せる | 固定 `(2,3)` では偽 | `mixed_degrees_miss_progression` |
| degree-two は全素数の unit-boundary carrier | 要訂正 | 奇素数全体。素数2は含まれない |
| 必ず `d≠e` と要求しても Goldbach 全体を覆う | 偽 | target 6の唯一のprime pairは3+3で、両degreeは2に強制 |

「左右が異なってもよい」という許容と、「左右が異ならなければならない」という制限は別である。
後者の反例を、前者が主張されたことにして解釈していない。

## 三次 geometry が実際に追加した情報

三次の Beam quotient は

\[
A=u(u+1)
\]

である。従って、合同条件 `GN≡1 (mod 3)` だけに還元すると polynomial shell の情報を失う。
例えば13はprimeかつ1 modulo 3だが、`13=GN 3 1 v` を満たす自然数 `v` は存在しない。

今回の厳密な追加制約は

\[
GN_3(1,v)\equiv1\text{ または }7\pmod9
\]

である。
mixed `(2,3)` で `n≡2 (mod 3)` とし、degree-two 側をprimeとすると、それは3になり `u=1` が強制される。
よって

\[
2n=3+GN_3(1,v)
\]

しか残らない。
`n≡8 (mod 9)` では必要な右辺の出力 `2n-3` が4 modulo 9になるので、三次の出力条件と矛盾する。

これは「CRTの言い換えかどうか」という名称の判断ではなく、**合同条件より強い polynomial restriction が存在する**という Lean の結論である。
得られた強化の向きは候補の排除であり、全中心での prime pair の供給ではない。

## 具体的な可否

- `16=3+13`: Goldbach は真。しかし `UnitPairAt 8 2 3` とその左右交換 `UnitPairAt 8 3 2` は偽。
- `28=5+23`: Goldbach は真。しかし `UnitPairAt 14 2 3` は偽。左が3に強制されると右は合成数25になる。
- `10=3+7`: mixed `(2,3)` の正の成功例 (`u=v=1`)。
- `14=7+7`: cubic `(3,3)` の正の成功例 (`u=v=1`)。
- `182=91+91`: 両degreeは3で、正の整数座標 `u=v=5` は円の等式も満たすが、両出力は合成数。

これらは Lean theorem であり、単なる数値探索の出力ではない。
無限個の中心を落とす定理は、Goldbach 自体の反例が無限個あるという意味ではない。
落としているのは **この固定された mixed GN family** である。

## 無制限の degree family に戻した場合

`n≥3` において

\[
\operatorname{GoldbachPairAt}(n)
\iff \operatorname{UnitPairAt}(n,2,2)
\iff \exists d,e\text{ prime},\operatorname{UnitPairAt}(n,d,e).
\]

これを `goldbachPairAt_iff_unitPairAt_two_two` と `exists_prime_degrees_iff_goldbach` に固定した。
`strongGoldbach_iff_unitPairAt_two_two` は `n=2` の2+2を別途証明して全称命題を接続する。
新しい全称存在証明を仮定に隠してはいない。同値のいずれの側にも無条件の全称証明は与えていない。

従って、残る課題は単なる「幾何 theorem」という名前では特定できない。
次に必要な条件は、(1)両出力の素数性を実際に含意し、(2)必要な全中心でその条件を満たす座標が存在することを、独立に証明できるものでなければならない。
既に素数性や `UnitPairAt` を仮定に入れた条件付き theorem だけではこの義務は解消しない。

## 実装と検証

今回追加した theorem は計40個（production 29、audit 11）。
既存 API の合成、恒等式、条件付き・同値定理、反例定理を含む数であり、独立した深い新定理40個という意味ではない。

- `DkMath/NumberTheory/Goldbach/PairGN.lean`
- `DkMath/NumberTheory/Goldbach/PairGNCubic.lean`
- `DkMathTest/NumberTheory/GoldbachPairGNAudit.lean`

build cwd: `lean/dk_math`。

```sh
./lean-build.sh DkMathTest.NumberTheory.GoldbachPairGNAudit
lake env lean DkMathTest/NumberTheory/GoldbachPairGNAudit.lean
git diff --check
```

focused build は終了コード0。
追加・更新した上記3 Lean ソースを直接検証し、`validation-006.log` に出力を保存した。
最終 audit は今回の全40定理について `#print axioms` を実行する。
依存する公理は標準の `propext`, `Classical.choice`, `Quot.sound` の範囲内で、`sorryAx` や新規公理への依存はない。
追加ソースの `sorry`, `admit`, `native_decide`, `unsafe`, 新規 `axiom` 宣言は0件。直接検証の警告・エラー0件、diff check成功。
リポジトリ全体ではなく、上記 focused module とその依存範囲の検証である。

## コミット

指定 branch: `wip/fixed-big-arithmetic-gauge-260912-v0`。

- `561510e02`: 二宇宙保存式・weighted quotient・Goldbachとの同値。
- `5a93f33ff`: cubic circle・mixed degree の全称 obstruction。
- 本レポートを含む最終チェックポイント: 左右交換、正の総Gap、具体例、全40定理の axiom 監査。

前二段階の詳細は `report-004-pair-gn.md` と `report-005-pair-gn-cubic.md` に記録した。
