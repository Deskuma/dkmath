# NOTE-017: 実際のGL₂表現とガロア不変直線の判定基準

日付: 2026-10-21。NOTE-017の主目標を、既存のSource・残余空間・ガロア作用を保持して実装した。

```lean
S.ResidualIsIrreducible ↔
  ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
    Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L
```

素数pに対し、同じ実際の空間の二次元性から基底を選び、
`S.residualGL2 : G_ℚ →* GL₂(𝔽_p)` を構成する。
追加の位数・次元・独立二点の仮定はない。Weil対やMazur型定理も仮定していない。
この同値は判定基準であり、Frey表現の既約性そのものの証明ではない。

## 実装と入口

| モジュール | 役割 |
| --- | --- |
| `DkMath.Lib.RepresentationTheory.InvariantLine` | 真の非零部分空間の一次元性、既存の既約性と安定直線の不存在の同値 |
| `DkMath.Lib.RepresentationTheory.MatrixRealization` | 一般の有限基底でのGL実現、同変な座標表示、共役と不変量 |
| `DkMath.Lib.NumberTheory.EllipticTorsionGL2` | 実際のE[p]の基底・GL₂・開核・有限正規レベル・直線判定 |
| `DkMath.FLT.FreyResidualGL2` | 同じSourceの公開API、行列式指標、統合profile |

本体4モジュール407行、公開宣言45個。日本語の教科書docstringを付けた。
全新規Leanファイルでimport後に `#print "file: モジュール名"` を置く。
`DkMath.Lib`・`DkMath.FLT`・ルートの `DkMath` から公開し、回帰と監査を `DkMathTest` へ配線した。

## 二次元性が担う二つの役割

第一に、`Module.finBasisOfFinrankEq` をNOTE-016の `finrank_torsion_prime` に適用する。
選ばれる基底は非計算的であり、具体的な37-torsion点の座標を計算したという意味ではない。
元の表現の各作用素は群元の逆元によって可逆なので、`Representation.asGroupHom` と
`LinearMap.toMatrixAlgEquiv` によってGLへの群準同型を得る。
基底bと点Pについて、実際の作用との対応は

\[
M_b(\sigma)\,b(P)=b(\rho(\sigma)P)
\]

である。`matrixGroupHom_mulVec` と `residualGL2_mulVec` がこれを固定する。
列ベクトル上の `coordinateRepresentation` は同じ基底同型に沿う共役作用であり、
`coordinate_apply_eq_mulVec` により構成したGL行列の作用と一致する。

第二に、二次元空間の部分空間Lが非零かつ真なら、その次元は1に限られる。
次元の正値性・真部分空間の次元の狭義不等式から `proper_nonzero_iff_finrank_one` を証明した。
従って、全ての安定部分空間が零か全空間という既存の定義を、安定直線の不存在に翻訳できる。
空間の非自明性も次元2から得る。Frey側では既存の `ResidualIsIrreducible` と
`IsGaloisStable` の定義を変更せず、この一般定理を特殊化した。

## 基底を変えても保持する数学

bからcへの座標変換を `basisChange b c` とし、その行列を `c.toMatrix b` とする。
向きも含めて

\[
M_c(\sigma)=C M_b(\sigma)C^{-1}
\]

を証明した。逆行列は `b.toMatrix c` である。

- **核**: 行列化の単射性から `matrixGroupHom_ker`。同じSourceの残余核とGL₂の核は等しい。
- **行列式**: `LinearMap.det` と一致するので基底によらない。
- **行列式指標**: GLの行列式準同型を合成し、単なる値の等号だけでなく指標全体の基底不変性を証明する。
- **特性多項式**: 元の線形作用素の特性多項式と一致するので基底によらない。
- **既約性**: 元の空間と座標空間の同変線形同型によって同値となる。

核が同じなので、既存のKrull位相での開核と有限正規中間体をそのままGL₂へ運べる。
`residual_gl2_profile` は次元2、核の一致、有限正規レベル、直線判定を同じSourceからまとめて供給する。
これは中間体の固定部分群が核に入るという有限レベル条件であり、具体的な有限拡大の生成多項式の計算ではない。

## 回帰例と証明の境界

実在するSource 2の(4,3,5)のFrey曲線を用い、その**同じ曲線のE[37]** を行列化した。
仮想的なSource 37の存在には依存しない。
基底の0番と1番を交換し、二つの基底が異なることも証明した上で、
共役・行列式指標・特性多項式・既約性・核の不変性と、有限正規レベルを検査した。
全ガロア元について行列が異なるとは主張しない。例えば単位元の行列はどの基底でも単位行列である。
Source 37を入力する一般の直線判定も、位数や次元の追加仮定なしで検査した。

さらに、実在するSource 2のE[2]には、非零の有理点(0,0)が生成する安定直線がある。
生成元を全ガロア元が固定し、線形性によってそのspan全体が保存される。
`actual2_rank_two_reducible` は、同じ空間の次元が2でありながら既約でないことを証明する。
従って「二次元だから既約」という誤った飛躍は、この実際の幾何学的例でも排除される。

行列式指標は構成したが、**円分指標との一致は未証明**である。
Weil対の構成・ガロア同変性は別の幾何学的入力となる。
Frey表現の安定直線を算術的に排除する証明、Mazur型理論、局所慣性・Artin導手、
FLT37・一般FLTの終点も今回の結論には含めない。

## 検証

実行結果と主要依存経路は [検証記録](evidence/validation-note017.txt)、
ルートimportの確認コードは [RootSmokeNOTE017.lean](evidence/RootSmokeNOTE017.lean) に保存した。
`Note017DependencyAudit` は公開45宣言・回帰13宣言の公理を検査し、13経路で型とopaque本体を辿る。
標準論理公理3種だけを許し、実際の次元provider・ガロア作用・基底選択・核の輸送・
有限レベル・一般線形代数が使われることを要求する。
旧条件付き位数provider、外部未移植宣言、FLT終点、指定した類群providerへの迂回を禁止する。
一般ライブラリ側の経路ではFrey固有の宣言も禁止する。

実行結果はすべて成功した。

- `lake build DkMath.FLT.FreyResidualGL2`: 3180 jobs。
- `lake build DkMathTest.FLT.FreyResidualGL2`: 3182 jobs。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: 11574 jobs。
- ルートsmoke、`lake env lean DkMathTest.lean`、マーカー照合、静的検査、`git diff --check`。

新規6モジュールには警告・エラーなし。既存の別モジュールの歴史的な警告は残るが、
今回の45公開宣言・13回帰宣言の公理監査と13依存経路の検査はすべて通った。
