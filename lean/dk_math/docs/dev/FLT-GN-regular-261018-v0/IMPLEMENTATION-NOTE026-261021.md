# NOTE-026: 右加法性・交代性・反対称性

日付: 2026-10-21。標数0、n≠0、S,T,R∈E[n]の下で、NOTE-025の同じ移動固有値について

\[
c(S,T+R)=c(S,T)c(S,R),\qquad c(T,T)=1,\qquad c(S,T)=c(T,S)^{-1}
\]

を証明した。値を別の形式的な対へ置き換えず、実際の関数体の同じWeil関数を測っている。
同じμₙ値の対を、外側が移動S、内側が目標Tである二重の`AddChar`として構成した。
**非退化性・ガロア同変性、WeilPairingDataの存在、円分行列式の無条件化は後続の境界である。**

## 1. モジュールと読み順

| モジュール | 内容 |
| --- | --- |
| `EllipticPointOrderAlgebra` | 全点での積・有限積の位数、一意な非零定数の復元 |
| `EllipticWeilRightAdd` | 引き戻しの可換性、倍写像の原像を使う右加法性 |
| `EllipticWeilAlternating` | 周期的差分の有限和、実際の軌道積の定数性、自己移動の固定性と交代性 |
| `EllipticWeilBicharacter` | 反対称性、μₙでの法則、同じ値を持つ交代的双指標 |
| `DkMath.FLT.FreyWeilBicharacter` | 同じSourceの比例定数と曲線への接続 |

先頭4本は`DkMath.Lib.NumberTheory`のモジュールである。
本体5モジュール・名前付き公開宣言28個に日本語の教科書docstringを付け、import後の正確な`#print "file: ..."`を保持した。
`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`へ公開し、回帰と監査を`DkMathTest`へ接続した。

## 2. 位数の積法則を全点で使う

`pointOrder_mul`は、実際の付値の乗法性と非零付値の`WithZero.log_mul`から

\[
\operatorname{ord}_P(fg)=\operatorname{ord}_P(f)+\operatorname{ord}_P(g)
\]

を証明する。有限点とOの定義を再び場合分けせず、NOTE-024の同じ全点付値を使う。
`pointOrder_prod`は有限積への帰納であり、全ての因子と積の非零性を保持する。
`existsUnique_unit_of_pointOrder_zero`は、全点で位数0の関数を関数1と比較し、NOTE-025の一意な比例定数判定を再利用する。
一般の位数の積法則と定数判定は標数0を要求せず、Weil関数への適用で標数0を使う。

## 3. 右加法性は二つの積の比較で閉じる

既存の倍写像の全射性からnU=Tとなる実際の点Uを選ぶ。

\[
h=w(n,T)\,\tau_{-U}^*w(n,R)
\]

と置く。全点の位数公式において

\[
[n](P-U)=R\iff[n]P=T+R,\qquad[n](P-U)=O\iff[n]P=T
\]

なので、中間のTファイバーの寄与が消え、hとw(n,T+R)の位数が一致する。
NOTE-025の`existsUnique_scalar_of_pointOrder_eq`からw(n,T+R)=a hとなる非零定数aを得る。

Sによる移動は係数体を固定し、二つの平行移動は可換なので、hの固有値はc(S,T)c(S,R)である。
定数倍aを通しても同じ固有値であり、既存の`weilTranslationUnit_unique`から右加法性を得る。
NOTE-024の例外点処理を全点位数として再利用するため、P=OやP-U=Oの例外を作り直していない。

## 4. 軌道積の望遠鏡型相殺で交代性を証明する

nU=Tを選び、実際の有限積

\[
H=\prod_{i=0}^{n-1}\tau_{iU}^*w(n,T)
\]

を`weilTranslateOrbitProduct`として構成する。各因子は非零関数の自己同型像なので、H≠0である。
各点Pで

\[
d(j)=\mathbf1_{[n]P+[j]T=O},\qquad
\operatorname{ord}_P(\tau_{iU}^*w(n,T))=d(i-1)-d(i)
\]

と書ける。nT=Oからd(j+n)=d(j)となり、`sum_range_periodic_difference`により有限和は0になる。
添字−1を整数で保持し、端点の周期性による一致を明示した。この差分補題はn=0にも成立するが、Weil関数の構成ではn≠0を保持する。

`pointOrder_weilTranslateOrbitProduct`はOを含む全点でHの位数0を証明し、
`existsUnique_unit_weilTranslateOrbitProduct`はHを一意な非零定数として復元する。
従ってτ_U*H=Hである。移動後の積は添字が一つずれ、共通するn−1個の非零因子を消去すると

\[
\tau_{nU}^*w(n,T)=w(n,T)
\]

となる。nU=Tより、`transEquiv_weilFunction_self`が自己移動の実際の固定性を与える。
固有値の一意性から`weilTranslationUnit_self`でc(T,T)=1を得る。
単なるc(T,T)^n=1や二乗1を、交代性と取り違えていない。

## 5. 反対称性と双指標

c(S+T,S+T)=1を両変数に展開し、対角項を1として消すとc(S,T)c(T,S)=1となる。
`weilTranslationUnit_swap`が反対称性を単元として与える。
同じ値をμₙの部分群型へ戻し、右加法性・交代性・交換則を証明した。

`weilTranslationRightCharacter S`は目標Tを動かす右指標である。
`weilAlternatingBicharacter`は

```
AddChar (Torsion E n)
  (AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K)))
```

という実際の対象で、外側Sが移動、内側Tが目標である。
`weilAlternatingBicharacter_apply`により、その値は前段の`weilTranslationCharacter T S`と定義的に同じである。
交代性と反対称性の定理も別途与えた。`AddChar`の型だけに交代性を仮定として隠していない。
非退化性とガロア同変性を要求する既存の`WeilPairingData`にはまだ変換しない。

## 6. 二つの実際の2-torsion点による回帰

`FreyWeilBicharacterTest`の22宣言は、既存のSource 2=(4,3,5)の同じ正規化曲線

\[
y^2+xy=x^3-2x^2-9x
\]

を使う。既存のT=(0,0)に加えてR=(4,−2)を構成し、非特異性、二倍零、非零性、Tとの相異性を証明した。
異なる二つの目標の右加法性、対角以外の交換則、両点での対角値1を回帰する。

既存の2U=Tとなる点Uから同じ軌道積を作り、非零性、Oと有限点Uでの位数0、一意な定数としての復元を検査した。
さらに実際の自己移動の固定性、Sourceの双指標と前段の同じ比例定数の一致、標準のAddCharの加法則、μ₂での自己・交換則を検査した。
指数1と、任意のT∈E[37]での交代性も検査する。37個の因子や巨大な多項式を展開する必要はない。
この回帰から非退化性や対の値の非自明性までは結論しない。

## 7. 依存監査と検証

`Note026DependencyAudit`は本体28宣言・回帰22宣言の公理と、14経路の型・opaque本体の依存を検査する。
許容公理は`propext`・`Classical.choice`・`Quot.sound`のみ。
実際の倍写像の全射性、全点の位数公式、定数比判定、周期的差分、非零積、固有値の一意性、既存の同じ値への接続を要求する。
選択経路では未構成のWeil対データ・旧FLT終点・外部未移植provider・大域Kummer入力を禁止する。

検証結果は[validation-note026.txt](evidence/validation-note026.txt)、
ルートからの到達と公理表示は[RootSmokeNOTE026.lean](evidence/RootSmokeNOTE026.lean)に記録した。
focused buildは3212 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`は11638 jobsで成功した。
ルートsmokeと`lake env lean DkMathTest.lean`の直接検査、tracker照合、マーカー・禁止構文・帰属先の検査、`git diff --check`も成功した。
新規モジュールに警告はなく、統合ビルドでは既存の別モジュールのsorry警告5件が再掲された。

## 8. 参照元と残る境界

次のAnthropicの証明を読み、DkMathの既存の全点位数・一意な比例定数・自然数torsionへ翻訳した。

- [右加法性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_add_right.lean): blob `b879635a2748bd9456704403fac7c8db141b2895`。
- [交代性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_self.lean): blob `9a0a55370677bf36f3a3b4e49cfc56626dd7c024`。

二つの翻訳ファイルにApache-2.0の帰属、LICENSE/NOTICE参照、blobと変更点を保持した。
参照元の剰余付値の比の計算を、整数位数の加法・周期的差分の和に置き換えて整理した。
P2Mマクロや外部未移植providerはimportしない。

次の境界はガロア同変性と非退化性である。
特に倍写像の引き戻しとtorsion平行移動の固定体の同定は今回実装していない。
交代的双指標の構成だけから、完全なWeil対・円分行列式・Frey表現の既約性・FLTの新たな閉鎖を結論しない。
