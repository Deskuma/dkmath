# NOTE-009 指標別位相輸送・反例入口の教科書実装

日付: 2026-10-19。NOTE-009のうち、既存の対象へ証明付きで接続できる
IRR-010、IRR-011の指標同定、および後半§4の `Source.ofCounterexample` を固定した。
ノート内の外部実装の比較・完成度の評価は検討記録として扱う。

## 1. 到達した範囲

| 項目 | 今回の公開定理 | 数学的な境界 |
| --- | --- | --- |
| 指標別位相輸送 | `observe_projector_galois`、`observe_nonzero_characterSupport_eq` | 新しい障害消滅条件ではない |
| 指標5の同定 | `character_generator_pow`、`bernoulli32_character` | 対象成分の非零性・Herbrand–Ribetは未供給 |
| 任意の整数反例の入口 | `Source.ofCounterexample`、`Source.ofCounterexample_spec` | p≥5の素数、三座標非零、冪和が前提 |
| 同じ曲線の局所算術 | `Source.ofCounterexample_local_profile` | ガロア表現・Artin導手・モジュラー性・レベル降下は別理論 |
| Legendre深度と容量 | 今回は追加定理なし | 深度公式から独立な被覆容量制約は供給していない |

本体3モジュール、回帰1モジュール、依存監査1モジュールを追加した。
各ファイルに教科書docstringと、import後の `#print "file: モジュール名"` を置いた。

## 2. IRR-010: 36指標ごとの同変性

`DkMath.Lib.NumberTheory.Cyclotomic37CharacterTransport` は、既存の実際の類群の
37-torsion空間、ガロア作用、補間射影をそのまま使う。

1. `action_apply_component`: 固有成分上では、全ガロア元aの作用がχμ(a)倍になる。
   生成元だけの条件から全群へ広げた既存の `mem_component_iff` を使う。
2. `projector_action_commute`: 全ガロア元は生成元の冪であり、補間射影は生成元作用素の
   多項式なので可換となる。可換な二多項式を同じ `aeval` へ写して証明する。
3. `projector_action`: 射影の値が固有成分に属することと上の可換性から、

\[
 P_\mu(\sigma_a x)=\chi_\mu(a)\,P_\mu(x)
\]

を得る。χμ(a)はF₃₇の単元なので、零性は作用で変わらない。

`characterSupport x` は `Pμ(x)≠0` となる指標ラベルの有限集合である。
成分空間全体の非零性や次元ではなく、指定した元xの支持を記録する。
`characterSupport_action` がこの集合のガロア不変性を証明する。

`DkMath.FLT.Kummer.IrregularCharacterTransport37` では、整数座標の仮想Stateの
記録済み障害をベクトル化する `observeVector` と、実際の `observe_galois` を接続する。
`observeVector_galois` は、同じ類を保った位相の再索引と線形作用の可換性を示す。
従って、全ての位相iとガロア単元aで

\[
 P_\mu(\omega_{ai})=\chi_\mu(a)P_\mu(\omega_i)
\]

となる。非零位相iはa·1として表せるので、

\[
 \operatorname{Supp}(\omega_i)=\operatorname{Supp}(\omega_1),\qquad i\ne0
\]

を得た。個々の指標についても非零射影の同値を公開している。
位相0の射影は別に全て零と証明する。i≠0の条件を落としてはいけない。
全ての位相輸送で、Stateのx,yが整数A,Bに由来する仮定を保持した。
非零位相が同じ支持を持つことは、その支持が空であることを意味しない。

## 3. IRR-011入口: Bernoulli32と指標5

任意の自然数rについて、生成元gに対する固有値ラベルg^rは冪指標a↦a^rを表す。
`character_generator_pow` は、生成元上での一致から全群上での準同型の一致を証明する。
このためgを具体的な整数2として選ぶ必要はない。

`bernoulli32Label := generator^5` と置き、

```lean
character bernoulli32Label = powMonoidHom 5
```

を証明した。指標は単元2で32を取り、自明指標とは異なる。
`bernoulli32_residual_exponent` は

\[
 1-32=5\quad\text{in }\mathbb Z/36\mathbb Z
\]

も明示する。`bernoulli32_target_certificate` は既存の `BernoulliIrregularPair 37 32` と
37−32=5および指標の同定を一つの論理積で提供する。

ここでの冪指標はF₃₇ˣ上の指標である。p進Teichmüller持ち上げそのものや、
この成分に非零類が存在する定理を構成したわけではない。
Herbrand–Ribetを仮定せず、有限なBernoulli証明書とラベル同定の範囲を固定した。
Stateの対象射影では、輸送係数がa⁵となることまで証明している。

## 4. 任意の整数反例からの原始化

`DkMath.FLT.FreyCounterexample` の `PrimitiveReduction p a b c` は、
共通因子dと原始座標A,B,Cについて次の情報を全て持つ。

- d≠0、A,B,C≠0。
- a=dA、b=dB、c=dC。
- `IsCoprime A B` と `A^p+B^p=C^p`。

`exists_primitiveReduction` は有限集合{a,b,c}の実際のgcdを抽出する。
三変数を同じdで割った等式から、非零なd^pを消去して冪和を得る。
原始三変数のgcdが1であることから二変数のBézout原始性を証明する際には、
A,Bの共通素因子は冪和によってCも割るためgcd=1に反することを使う。
この段階はp>0だけを要求し、pの素数性や奇数性を必要としない。

## 5. 偶奇・符号・分母条件を一つずつ運ぶ

`orient_parity` は奇数pの原始解を、第一座標奇数・第二座標偶数の順にする。

| 偶数座標の位置 | 新しい座標 |
| --- | --- |
| bが偶数 | (a,b,c) |
| aが偶数 | (b,a,c) |
| a,bが奇数 | (a,−c,−b) |

最後の場合、方程式からcが偶数となる。互いに素性は方程式から右辺へも運ぶ。
奇数冪の負号を利用するため、三番目の置換も同じ冪和方程式を満たす。
`ParityTrace` はこの三通りの等式を記録する。

`odd_mod_four_orientation` は、奇整数xならxまたは−xが3 mod4となることを示す。
必要なら三座標全ての符号を同時に変え、`4∣x+1` を実現する。
`OrientationTrace` は、共通の符号e=±1と、上記三種類の置換を正確な等式で保持する。
単に積や絶対値が同じという証拠に弱めてはいない。

`exists_source_of_coprime` は、こうして向けた座標を既存の `ofOriented` へ渡す。
既存の分母条件の定理が、偶数の第二座標のp乗に16が割り込み、
第一座標のp乗が−1 mod4となることを実際に証明する。
素数p≥5ならこの段階の条件を満たす。

## 6. 公開入口と同じSourceの半安定性

ノートで提案された型を実装した。

```lean
noncomputable def Source.ofCounterexample
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ p + b ^ p = c ^ p) : Source p
```

`Source.ofCounterexample_spec` は、選択した同じSourceの向き付け条件に加え、
元の反例の `PrimitiveReduction` と、その原始座標からSourceへの `OrientationTrace` を返す。
非原始の整数反例や負の座標も扱い、変換の証拠を失わない。

`Source.ofCounterexample_local_profile` は、その同じSourceの有理曲線について、
楕円曲線であることと、全素数ℓでの次の性質を同時に与える。

- 正式な `WeierstrassCurve.IsMinimal`。
- 正式な良還元または乗法的還元。
- `p∣vℓ(Δ_min) ↔ ℓ≠2`。

この入口は原始化・向き付けから構成しており、既存のFLT終点で入力を矛盾にして
空虚にSourceを作る証明を用いていない。反例の存在を主張するものでもない。
残余ガロア表現・Artin導手・モジュラー性・レベル降下との接続は依然として必要である。

## 7. 検証と残る研究

公開入口は `DkMath.Lib`、`DkMath.FLT.Kummer`、`DkMath.FLT` とルート `DkMath`。
回帰20件と監査は `DkMathTest.lean` に接続した。
監査対象は新規49宣言（原始化の構造体・コンストラクタ・射影を含む）と主要10依存経路。
原始化のgcd抽出、正規化分母条件、実際のガロア作用・補間射影、有限Bernoulli証明書、
同じSourceの正式な局所最小性を依存先として要求する。

Legendreの深度公式から独立な被覆容量の制約は、ノートでは研究課題として挙げられている。
今回の指標支持保存も新しい消滅条件ではなく、深度の再表示だけから容量排除や素数存在を
結論する定理は追加していない。

検証結果とコマンドは [検証証跡](evidence/validation-note009.txt) に記録した。
回帰build（9,007 jobs）、監査build（9,008 jobs）、統合build（11,525 jobs）、
ルートsmokeと統合build後の `DkMathTest.lean` 直接検査は全て成功した。
49宣言の公理監査、10経路の実依存監査、ファイルマーカーの整合性検査も通過した。
新規5モジュールの警告はなく、新規本体3モジュールでの `sorry`・`admit`・独自 `axiom`・
`native_decide` の不使用と `git diff --check` を確認した。
