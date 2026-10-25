# NOTE-032-005B — Cofixed直線の行列式作用と同じ実点の円分倍点

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `bfa6ece0d55c48ee65db86fba30dcef91402d635`、作業ツリーはcleanだった。
本体14定理を追加した。Cofixed直線上の作用を行列式倍として証明し、
構成済みの幾何学的Weil対から円分指標倍へ接続した。
同じ楕円曲線の実際の点群の倍点、同じpointSubgroup、同じFrey Sourceへ翻訳した。
005Bを完了とする。一般hno、商曲線・isogenyの構成は今回の結論ではない。

## 1. 到達点と仮定

| 層 | 所有モジュール | 今回証明した内容 |
| --- | --- | --- |
| 一般線形代数5定理 | CofixedDeterminant | 商を固定する自己準同型の直線上の作用＝行列式倍、指標への輸送、二次元の行列の形 |
| 一般楕円曲線3定理 | EllipticCofixedCyclotomic | 同じE[p]のCofixed直線上の円分作用、同じ実点・pointSubgroup上の倍点 |
| 同じFrey Source6定理 | FreyCofixedCyclotomic | 行列式・円分・倍点の照合、行列[χₚ,*;0,1]、候補E₀[p]への接続 |

一般核は有限次元V上の自己準同型fと一次元Lを扱う。
周囲の次元2、fの可逆性、標数の制限を要求しない。
楕円曲線の円分公式は標数0・楕円曲線性・素数pを要求し、Cofixed直線は明示入力に残す。
Source側では楕円曲線性・Weil対・円分行列式は既存の同じ曲線の証明から内部供給する。
p≥5と2上の住所は、最後の005AのE₀[p]への輸送でのみ追加する。

## 2. 商固定から直線のスカラーを決める

[CofixedDeterminant.lean](../../../DkMath/Lib/RepresentationTheory/CofixedDeterminant.lean)
では、まず群表現に限定しない自己準同型の定理を証明した。
全てのxについてf(x)−x∈Lなら、x∈Lに対して

```text
f(x) = (f(x)−x)+x ∈ L
```

なのでLはfで保存される。従って制限f|Lと商V/Lの作用を構成できる。
商ではf(x)とxが同じ類を表すため、商の作用は恒等写像となる。

Lは一次元なので、あるcについてf|L=c idとなる。
Mathlibの `LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one` でこのスカラーを取り、
`LinearMap.det_eq_det_mul_det` により

```text
det f = det(f|L) det(f on V/L)
      = c¹ · 1 = c
```

と同定する。これでL上のf(x)=det(f) xを得る。
基底を拡張して二次元へ埋め込む必要はなく、有限次元Vの任意の余次元に適用できる。
群表現ρではf=ρ(g)、差の所属は同じCofixed条件から供給する。

## 3. 円分指標は同じWeil対から供給する

[EllipticCofixedCyclotomic.lean](../../../DkMath/Lib/NumberTheory/EllipticCofixedCyclotomic.lean)
は標数0の任意の楕円曲線Eを扱う。
既存の `torsion_determinant_eq_cyclotomic` により、
同じ実際のE[p]の行列式指標はmod p円分指標χₚである。
この所有定理は同じ曲線の関数体・移動固有値から構成済みの幾何学的Weil対を使う。
今回の利用側へWeil対やその非退化性を追加の仮定として要求しない。

一般核へこの同定を渡すと、同じP∈Lについて

```text
ρ(σ)P = det(ρ(σ)) • P = χₚ(σ) • P
```

となる。逆指標χₚ⁻¹ではない。
Lの商が固定されることから、Lの各点自身が固定されると推論していない。

次にχₚ(σ)のZModスカラーを、その自然数代表のn倍写像へ戻す。
ZModの代表元のcastとスカラー倍の一般定理を使ってから、同じSubtype.valを射影する。

```text
pointAction E σ P.val = (χₚ(σ) : ZMod p).val • P.val
```

これは同じ曲線の実際の点群の倍点である。
既存のpointSubgroup E p Lの点Qは同じP.valで表せるので、その同じQにも公式を運ぶ。
この部分群の位数p・巡回性・安定性は既存の所有者と併用できる。
商楕円曲線やisogenyが存在することは、この群の構成だけからは結論しない。

## 4. 行列の右上成分を保持する

二次元で第一基底ベクトルがCofixed直線を張るとする。
商の第二座標へρ(g)b₁−b₁を射影すると、右下成分は1となる。
安定性から左下成分は0であり、既存の対角成分の積の公式から左上成分はdet(ρ(g))となる。

```text
ρ(g) = [ det(ρ(g))  * ]
       [     0      1 ]
```

右上の値は元の同じ行列の成分として保持する。
表現の分裂、適合基底での対角化、拡大類の消滅は証明していない。
Sourceでは構成済みの円分行列式を供給し、[χₚ,*;0,1]という同じGL₂行列の等式を得た。

## 5. 同じSourceとE₀[p]への翻訳

[FreyCofixedCyclotomic.lean](../../../DkMath/FLT/FreyCofixedCyclotomic.lean)
の最初の4定理は、同じ残余作用の行列式倍、円分倍、実点の倍点、pointSubgroupの倍点を公開する。
次の定理は適合基底での同じ行列の等式である。
これらにはa≡3,7 mod8やb偶数を要求しない。

最後の `residualZeroComponent_apply_eq_cyclotomic_smul_of_cofixed_line` は、
005Aの「大域Cofixed直線があればL=E₀[p]」へ接続する。
同じ2上の住所のP∈E₀[p]を、同じLの点として公式へ渡す。
大域Cofixed直線の存在・性質は仮定のまま保持し、
7側の分解群での局所Cofixed性だけから大域公式を得たとはしない。
E₀[p]とE₁[p]の定義も変更していない。

## 6. 境界例

[独立境界資料](evidence/Note032CofixedDeterminantBoundary.lean) は通常テストと同じ本体である。

- diag(2,3)は第一座標軸を保存するが、商を固定しない。軸上の作用2は行列式6と異なる。
  安定性だけに条件を弱められない。
- Lを二次元の全空間とすれば差の所属は自動となるが、同じ行列の作用は行列式倍ではない。
  一次元の条件が必要である。
- 有理単元uによる表現(u x+(u−1)y,y)では、商は固定され、行列式はuとなる。
  u=2で、軸上の作用2と逆指標1/2を区別し、同じ基底で行列[2,1;0,1]を確認した。
  この計算は、固定した基底の右上成分が零でない例である。抽象的な非分裂性の証明ではない。
- 三次元空間の第一座標だけを零へ送る射影に一般核を適用した。
  差の像は同じ一次元軸に含まれ、非零の核から行列式0を独立に確認した。
  周囲の次元2・作用素の可逆性が不要なことを実例で確認した。

[指数37のスモーク](evidence/Note032CofixedCyclotomicSmoke.lean) は4定理で、
同じSource・同じ点の三つの作用、核候補の実点、適合行列、同じE₀[37]への接続を確認する。
Cofixed直線の存在を仮定に残し、Source37・直線・isogenyを構成したとはしない。

## 7. 検証と次の005C

対象ビルドが通過した（4053 jobs、警告0）。

```text
lake build DkMath.Lib.RepresentationTheory.CofixedDeterminant \
  DkMath.Lib.NumberTheory.EllipticCofixedCyclotomic DkMath.FLT.FreyCofixedCyclotomic
```

境界8定理・4定義、Sourceスモーク4定理が通過した。
本体14定理と合わせた30宣言の `#print axioms` は標準3公理の範囲内だった。
新規コードの禁止構文、マーカー、Libの8公開定理の昇格マーカー、依存方向、
既存所有者の不変性、入口登録、文書リンク、差分空白を確認した。
詳細は [検証記録](evidence/validation-note032-005b.txt) と [機械可読記録](evidence/note032-005b.json)。
通常テストの同一本体を独立資料でLean検証し、集約入口の登録は静的に確認した。
フルビルド、集約ルート、DkMathTest、lake testのビルドはユーザー側の検証分担とした。

次の005Cは、この同じ核候補から商楕円曲線・isogeny・有理捩れを構成し、零成分の輸送を調べる単位である。
今回は商上の自明な作用と、元の曲線の核候補上の円分作用までを固定した。
一般hnoや005Aの大域的な脱出元は依然として未供給であり、
円分スカラー公式だけから直線を排除したとはしない。[ROADMAP](ROADMAP-NOTE032.md) に残す。
