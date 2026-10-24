# GN-LIB-007b — 一般yへの移動とサイズ条件付きの脱出

2026-10-25。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
007a後のフルビルド成功はユーザーから報告を受けた。
今回は [PrimePowerCompensationShift.lean](../../../../DkMath/Lib/NumberTheory/PrimePowerCompensationShift.lean)
に31定理・3定義・11例を実装し、Libの完成入口へ接続した。

## 二つの証明層

奇素数p、正のMに対しg=p^(p−1)M^p、x=g+y、K=R_p(x,y)/pとする。
名前空間は `DkMath.Lib.NumberTheory.PrimePowerCompensation.Shift`。

**局所算術**ではgとyが互いに素であることを入力に取る。
x>y、gcd(x,y)=1、v_p(R_p)=1、pK=R_p、K>0、v_p(K)=0、
`x^p−y^p=(pM)^p K` を証明した。
gapの素因数はKを割らず、yの素因数は冪差もKも割らない。
gap支持上では `v_q(x^p−y^p)=p*v_q(pM)` となる。
ここまでにサイズ条件は使っていない。

**非完全冪性と脱出**ではy>0に加え、次の条件を明示する。

```text
y^p < x^p−(x−1)^p
```

この入力から `(x−1)^p < x^p−y^p < x^p` を得る。
007aの隣接冪の定理を再利用して冪差がp乗でないことを証明し、再構成からKもp乗でないと示す。
この順序を守り、局所付値や脱出素数の存在を非完全冪性の証明へ循環利用しない。

## yを割る小素数を除外する構成

p∤yの下で標準制御積を

```text
M = ∏ {q≤B | q prime ∧ q≠p ∧ q∤y}
```

と定義した。全因子がyを割らない素数なのでMとyは互いに素。
p∤yを加えてpMとy、さらにgとyの原始性を構成した。
このためyの素因数をgapへ誤って混入させない。

全素数q≤Bについて正確に

```text
v_q(x^p−y^p) = if q∣y then 0 else p
```

を証明した。q=2も、奇素数LTEを無条件適用せず、支持除去とpMの付値から扱う。
Mの各因子が一度ずつ現れる有限集合の構造を使うため、正確な付値pまで到達する。
B≥pは不要である。

標準制御積の残余Kは全ての小素数を避ける。
サイズ条件の下でKがp乗でないことを使い、007aの素因数分解の定理から
q>B、q∣K、p∤v_q(K)となる素数を得た。
さらに原始性から分母yの単元性を証明して、
`primeOrder q x y=p` と `p∣q−1` を得る。

`finite_set_compensation_and_escape` は任意の有限集合Sの最大値を上限として同じ結論を返す。
Sの要素が全て素数である仮定は不要で、局所付値の結論はS内の素数について述べる。
サイズ条件はこの統合入口にも残る。

## 互換と教科書の例

- `base_one`・`residual_one`・`primeProduct_one` でy=1の場合を007aへ接続した。
  007aの定義・型・証明は変更していない。
- p=3、B=3、y=2ではM=1、x=11、K=49=7²。
  q=2で局所付値0、q=3で付値3、脱出先q=7では付値2、位数3となる。
  未完成付値が1とは限らないことを示す。
- p=3、B=5、y=5ではM=2、x=77。
- p=3、B=3、y=1001ではgとyの原始性は成立するがサイズ条件は成立しない。
  原始性だけからサイズ条件を結論しないことをLeanでも確認した。
- p∣yを許したy=3の例では、標準構成の原始性が壊れる。

全新規宣言に `[DkMath.Lib]` の教科書コメントを付け、import後にファイルマーカーを置いた。

## 公開と検証

`DkMath.Lib.Cosmic.Completion` は新所有者を直接importする。
現在は33直接所有者、Lib内依存閉包は入口を含め34モジュールである。

```text
lake build DkMath.Lib.NumberTheory.PrimePowerCompensationShift DkMath.Lib.Cosmic.Completion
```

は成功した（2847 jobs）。
[単独importのsmoke](evidence/GNShiftedPrimeCompensationSmoke.lean) で新規34宣言と従来70入口を確認した。
同じ104宣言の公理は標準論理公理のみだった。
既存32所有者の不変性、元資料24ファイルのSHA256、昇格マーカー、禁止構文、
import閉包、文書リンク、JSON、差分を確認した。
[機械可読証拠](evidence/gn-lib-007b.json) と [検証記録](evidence/validation-gn-lib-007b.txt) に範囲を記録する。

ユーザー指定によりフルビルド・集約ルート・DkMathTest・lake testのビルドは実施していない。

## 残る007c

サイズ条件を自動的に満たす追加p乗因子を、yと制御対象の小素数へ互いに素になるよう選ぶ。
今回はその存在を仮定も証明もしていない。007bは明示的なサイズ条件付きの定理である。
一般FLTの降下、hno接続、Legendreの素数存在は引き続き別契約のまま残す。
