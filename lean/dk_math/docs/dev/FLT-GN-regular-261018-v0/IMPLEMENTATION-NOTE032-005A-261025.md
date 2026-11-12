# NOTE-032-005A — 7側の分裂接錐と一般hnoへの大域的な橋

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `69bc5ca9222e62181bb250a00c5e552051d0ac13`、作業ツリーはcleanだった。
本体19定理を追加した。7側で分解群が商E[p]/E₀[p]を固定すること、
その分解群内には3側で使った符号反転元が存在しないことを証明した。
一般Cofixed直線の候補を同じE₀[p]へ一意に絞り、一般hnoの未供給の入力を固定した。
032-005全体と一般hnoは未完了である。

## 1. 何を証明したか

| 層 | 今回固定した数学 | 仮定と境界 |
| --- | --- | --- |
| 整数算術2定理 | 分子≡0 mod8、整数a₂は偶数 | a≡7 mod8、b偶数、奇数n≥3。冪和方程式不要 |
| 剰余作用2定理 | z²+z=0ならz=0,1、分解群の変化量は非単元 | 剰余標数2、同じ付値環・整元 |
| 局所幾何4定理 | 方向の個別固定、全実点のσP−Pの滑らかな還元 | 同じモデル・中心・方向、分裂接錐の剰余条件 |
| Source接続11定理 | 7側の局所Cofixed性、局所枝交換の不存在、候補直線の同定 | 同じSource・素数p≥5・2上の住所。7側の結果にはa≡7 mod8 |

局所幾何の全点の定理は捩れ位数を使わない。
点そのものの固定、全ガロア群での商固定、7側の既約性を証明したとはしない。
E₀[p]と無限遠還元核E₁[p]の所有定義は変更していない。

## 2. 3側と7側を分ける算術

[FreySplitModEight.lean](../../../DkMath/Lib/NumberTheory/FreySplitModEight.lean)
では、7≡−1 mod8の奇数乗は−1であり、偶数bの3乗以上の冪は0となることを使う。

```text
3側: bⁿ−aⁿ−1 ≡ 4 mod8  →  a₂奇数  →  z²+z=1
7側: bⁿ−aⁿ−1 ≡ 0 mod8  →  a₂偶数  →  z²+z=0
```

整数除算の余りを保持し、分子が8kならa₂=2kと証明する。
指数37も一般の奇数指数の定理で扱い、大きな二項展開を必要としない。
Sourceのb偶数は、aが奇数であることと正規化の16∣aᵖbᵖから供給する。

同じ中心の剰余X座標は、003Cと同じY偏微分の短い経路で零となる。
従って剰余a₁=1,a₂=0,x₀=0となり、接錐と浅い中心傾きは分裂式を満たす。

## 3. 分裂式は分解群の全体で保存される

[ValuationSplitQuadratic.lean](../../../DkMath/Lib/NumberTheory/ValuationSplitQuadratic.lean)
は標数2でz²+z=z(z+1)を因数分解し、根を0,1へ分類する。
任意の剰余体自己同型は0,1を固定するので、実際の分解群元σに対し

```text
res(σz) = res(z)
σz−z ∈ A.nonunits
```

を得る。Frobenius所属にも慣性所属にも限定しない。
この合同だけから体内の等式σz=zを得たとはしない。

[EllipticSplitDyadic.lean](../../../DkMath/Lib/NumberTheory/EllipticSplitDyadic.lean)
では、同じ中心が分解群固定であることからσαも同じ接線二次式の根となる。
σαがβなら、α−βの付値は1だが、分裂式の剰余合同から同じ差が非単元となって矛盾する。
従ってσα=αとなり、根の和からσβ=βを得る。

浅い点の中心傾きにも同じ分裂式を適用する。
PとσPは中心からの深さが同じで、傾きの差は非単元だから、同じ枝の差の定理でσP−Pが滑らかに還元する。
臨界側の点では浅さを仮定せず、既存の臨界二点の和の定理を使う。
既に滑らかな点では加法閉性を使う。この三場合を合わせ、全ての実点について差の結論を得た。

## 4. 同じSourceの7側で局所枝交換は存在しない

[FreySplitDyadic.lean](../../../DkMath/FLT/FreySplitDyadic.lean) は

```text
residualZeroComponent_cofixed_decomposition_of_seven
```

によって、同じ残余表現の全分解群変化量が同じE₀[p]に入ることを供給する。
Frobenius元もこの分解群に含まれる。

もし同じ分解群の元σが全ての外側の点でρ(σ)P+PもE₀[p]へ送るなら、
003Bから構成した外側の実点Pに対して和と差の両方がE₀[p]に入る。
両者の差2PもE₀[p]へ入り、奇素数pでは2が可逆なのでP自身も入ってしまう。

```text
residual_no_decomposition_branch_swap_of_seven
```

はこの局所枝交換の不存在を証明する。
これは7側のSourceの不存在ではない。3側で用いた種類の局所証人を、7側では構成できないという境界である。

## 5. 一般hnoは、同じ零成分からの大域的な脱出へ絞られる

任意の大域Cofixed直線Lについて、032-002/003Bの非自明慣性元τと点Pを取る。
非零の変化量ρ(τ)P−PはCofixed性によりLへ、局所吸収によりE₀[p]へ入る。
一次元Lと同じE₀[p]の次元1から

```text
L ≤ E₀[p], dim L = dim E₀[p] = 1  →  L = E₀[p]
```

を得る。この候補の同定にはa≡7 mod8を要求しない。
これを使い、次の二つの同値を証明した。

```text
∃ 安定Cofixed直線  ↔  IsCofixedOn ρ E₀[p]
hno              ↔  ∃ σ P, ρ(σ)P−P ∉ E₀[p]
```

任意の直線の探索を、指定した同じ住所のE₀[p]へ絞ることができた。
ただし、右辺の脱出元の存在は証明していない。
7側では分解群全体が商を固定するため、もし脱出元があれば必ず分解群の外にあることも証明した。
局所Cofixed性から大域Cofixed性へ進める定理は置いていない。

## 6. 実際の曲線による境界確認

[通常テストと同じ独立資料](evidence/Note032SplitDyadicBoundary.lean) では、
整数曲線

```text
y²+xy=x³+2x,  Δ=−508, c₄=−95
```

を使う。これはa₂=0で2上の接錐が分裂する実際の楕円曲線である。
任意の2上の住所で同じ中心・方向・実際のFrobeniusを構成する。
実際の3捩れは9個、滑らかな捩れは高々3個なので、外側の実点Pが存在する。
その同じPと同じσで

```text
σα=α, σβ=β
σP−P は滑らかに還元する
σP+P は滑らかに還元しない
```

を証明した。最後は、和も滑らかなら2Pが滑らかとなる一方、3P=0から2P=−Pとなって外側条件に矛盾する。
Frey Sourceの存在仮定を用いない具体例である。
他に指数37の整数算術と、標数2を落とすと根−1が0,1に分類されない境界を確認した。

[Source37のスモーク](evidence/Note032SplitDyadicSmoke.lean) は5定理で、局所Cofixed性、
局所枝交換不存在、候補直線の同定、脱出との同値、脱出元の分解群外条件を確認する。
Source37・Cofixed直線・脱出元の存在を主張するものではない。

## 7. 模範解答と現checkoutの棚卸し

固定commit `6e837e75355538c7f80bab5b956861e86c4eacc2` の
[PROOF-PATHの既約性節](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md)
と [大指数hnoの組立て](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean)
を参照した。import一覧、候補部分群、商の零成分の輸送、捩れの塔の抜粋を確認した。
大指数の組立ては、商曲線の幾何、Mazur Step Three、安定な高位捩れ部分群の塔を使う。
[Step Threeの公開型](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean)
では、有理な位数pの点、2と3上の零成分外条件、整数モデルの還元条件が明示される。
参照側の依存全体の監査やビルドは今回の検証に含めていない。

現checkoutの所有者との対応は次のとおり。

| 必要な層 | 確認した所有者 | 現在の境界 |
| --- | --- | --- |
| 同じ実際のE[p]、位数p²・次元2 | EllipticTorsionRepresentation / EllipticTorsionRegularFiber | 実装済み |
| 全E[pᵐ]の位数とガロア同変な短完全列 | EllipticTorsionAllCard.card_torsion_pow / torsion_short_exact | 実装済み。選択した位数pᵐの巡回部分群の安定塔とは区別する |
| 実際のWeil対・円分行列式 | FreyGeometricWeilPairing.residual_determinant_eq_cyclotomic | 無条件の同定を実装済み。古い条件付き契約だけを見て未供給とはしない |
| 安定直線・位数pの巡回な実点部分群 | EllipticStableLine.pointSubgroup / card_pointSubgroup / pointSubgroup_stable | 実装済み。商曲線そのものは含まない |
| 2上の中心・非自明慣性・E₀[p]次元1 | 032-002/003A/B | 実装済み |
| 3側hno・既約性 | FreyModEightIrreducibility | 実装済み |
| 7側の全分解群での商固定、候補L=E₀[p] | 今回のFreySplitDyadic | 実装済み。脱出元は未供給 |
| Cofixed直線上の作用を円分スカラーへ同定 | StableLineMatrixの上三角化と既存の円分行列式が足場 | 次の005Bで同じ実点上へ接続する |
| 商楕円曲線・同じ核のisogeny・零成分の輸送 | DkMath.Lib.NumberTheory / FLTとMathlibのEllipticCurve配下を検索 | 該当する証明所有者を確認できなかった |
| Mazur Step Three・安定巡回p冪塔・対応する最終排除 | DkMath.Lib.NumberTheory / RepresentationTheory / FLTを検索 | 参照側の算術入力に対応する所有者を確認できなかった |
| GN一般核から同じSourceの脱出元へ | Lib.CosmicとNumberTheory/GN系を検索 | 同じResidualSpace・残余作用への接続を確認できなかった |

確認した検索範囲と参照URLを [機械可読記録](evidence/note032-005a.json) に残す。
「検索で所有者を確認できなかった」は、全数学からの不可能性の証明ではない。
全捩れの位数・倍写像の短完全列は既に供給済みである。
その全捩れの中から、指定した同じCofixed直線を保つ巡回部分群の塔を安定に選ぶ算術が別に残る。

## 8. 検証と次の単位

`lake build DkMath.FLT.FreySplitDyadic` が通過した（4050 jobs、警告0）。
新規Lib3モジュールもこの対象ビルドに含まれる。
独立境界4定理・1定義、Sourceスモーク5定理が通過した。
本体19定理と合わせた29宣言の `#print axioms` は標準3公理の範囲内だった。
新規コードの禁止構文、マーカー、Libの8公開定理の昇格マーカー、依存方向、
既存所有者の不変性、入口登録、文書リンク、差分空白を確認した。
詳細は [検証記録](evidence/validation-note032-005a.txt)。
通常テストの同一本体を独立資料で検証し、集約入口の登録は静的に確認した。
フルビルド、集約ルート、DkMathTest、lake testのビルドはユーザー側の検証分担とした。

次の005Bは、Cofixed直線上の作用を同じ表現の行列式、さらに円分指標のスカラー作用へ同定する単位である。
商曲線やMazur理論の存在を仮定として隠さず、まず証明できる線形代数と同じ実点への翻訳を完成させる。
その先の005C以降には別の算術実装が必要である。[ROADMAP](ROADMAP-NOTE032.md) に工程を分けた。
