# NOTE-029: 安定直線・固定点の降下・付値軌道の整数核

日付: 2026-10-21。
NOTE-029を検討資料として読み、現行のDkMathと上流の証明を調査して実装した。
029-Aは完成した。029-Bは定義・接続条件を固定した段階で、局所慣性からの二択は未証明。
029-Cは固定点の降下と整数漸化式の核を証明した段階で、Frey曲線の非零有理p-torsion排除は未証明である。
したがって無条件のFrey表現の既約性、一般FLTの新しい終点は追加していない。

## 1. 今回追加したもの

| モジュール（接頭辞 `DkMath.`） | 証明した内容 |
|---|---|
| `Lib.RepresentationTheory.FixedCofixed` | fixed/cofixedの区別、商の類による同値、安定性、可約性から直線抽出、条件付きcofixed抽出・既約性判定 |
| `Lib.NumberTheory.EllipticFixedTorsion` | ガロア固定点のKへの降下、n-torsion条件の降下、有理n-torsion排除と固定n-torsion排除の同値 |
| `Lib.NumberTheory.EllipticStableLine` | 一次元部分空間の点群内の像、位数p、巡回性、p倍零、ガロア安定性、実際のE[p]への接続 |
| `Lib.NumberTheory.FoldedValuationOrbit` | 奇素数の約分、折り返し合同軌道と付値型漸化式の矛盾、γ=pv−4への特殊化 |
| `FLT.FreyStableLine` | 同じSourceの実際の残余表現への接続、追加の対データなしの安定直線の円分行列式 |

本体5ファイルに公開された名前付き定義・定理34個を追加した。
各ファイルに日本語の教科書docstringと、import後の正確な`#print "file: ..."`を置いた。
本体を`DkMath.Lib`と`DkMath.FLT`へ、回帰と監査を`DkMathTest`へ接続した。

## 2. 029-A: 可約性から実際の位数pの部分群まで

`exists_stable_pointSubgroup_of_reducible`は標数0の楕円曲線E/Kと素数pに適用できる。
既存の幾何学的次元定理`finrank_torsion_prime`と、二次元の既約性判定を使い、
実際のE[p]の安定な一次元部分空間Lを取り出す。

`pointSubgroup E p L`は、Lをtorsion部分群の包含で**元の点群内へ写した像**である。
`pointSubgroupEquiv`がLとこの像の加法同型を与え、有限体上の次元公式から位数pを得る。
素数位数の群の巡回性、像の各点がp倍で消えること、ガロア安定性も証明した。
この部分はp≥5を要求せず、p=2にも正しく適用できる。

Source版は`residual_exists_stable_pointSubgroup`。
同じ`S.rationalCurve`と`S.ResidualSpace`を保持し、位数・次元のproviderは引数に取らない。
ただし可約性は仮定である。可約性自体を結論として供給する定理ではない。

位数pの安定部分群を構成したことと、有理p-isogenyを構成したことは区別する。
今回、商楕円曲線・Vélu公式・isogenyの射は実装していない。

## 3. fixed / cofixedを混同しない契約

`IsFixedOn ρ L`は全てのx∈Lについてρ(g)x=xという条件である。
`IsCofixedOn ρ L`は全てのx∈Vについてρ(g)x−x∈Lという条件である。
後者は`isCofixedOn_iff_mkQ`により、V/Lの類が作用の前後で変わらないことと同値。
いずれの条件からもLの安定性が従う。

`NoNonzeroFixed ρ`は非零固定ベクトルの不存在である。
これを証明できれば、非零Lのfixed/cofixed二択からfixed側を除ける。
`exists_cofixed_line_of_not_isIrreducible`はこの論理を実装した。
二択は定理の引数`hcases`として明示し、存在を仮定する大域instanceや独自axiomは設けていない。

最終的な`residual_isIrreducible_of_no_cofixed_line`には、次の三入力が残る。

1. 安定直線のfixed/cofixed二択。
2. 同じ有理Frey曲線の有理p-torsion排除。
3. cofixed安定直線の不存在。

2だけでは3は得られない。cofixedで固定されるのは商の元であり、元のE[p]の点とは限らない。

## 4. 029-Cの幾何学部分: 固定点の降下

`exists_baseChangePoint_of_fixed`は、標数0の体Kで、全絶対ガロア元に固定される
幾何学的な点PがK有理点Qの基底変換であることを証明する。

無限遠点はそのまま降下する。有限点ではx,y座標が全ガロア元に固定されるため、
Mathlibの`InfiniteGalois.mem_range_algebraMap_iff_fixed`から両座標がKに属する。
非特異性も単射な基底変換で引き戻して、元の曲線上の実際の点Qを構成する。

`exists_rational_torsion_of_fixed`はさらにnQ=0を証明する。
点群の基底変換を`baseChangePointHom`で加法準同型として固定し、
n倍写像との可換性と`baseChangePoint_injective`を利用する。
点群の演算に用いる`DecidableEq K`はこのAPIの引数に保持し、異なる判定器による演算の型の不一致を避けた。

得られる同値は

```text
NoNonzeroFixed (representation E n)
  ↔ ∀ Q : E(K), n • Q = 0 → Q = 0
```

である。素数性・楕円曲線性・次元2はこの一般的な降下には必要ない。
標数0と、有理点群の演算の条件は保持する。
この降下は関数体のWeil対を輸入せず、点の座標作用と無限ガロア理論だけを使う。

## 5. 029-Cの整数核: 円周上の合同軌道を折り返す

上流の有理p-torsion排除の証明には、純粋な整数漸化式の部分があった。
これを`no_folded_valuation_orbit`へ切り出し、上流のライセンス・blob・出典を保持した。

想定される解釈は、位数pの非零有理点Qに対して

```text
γ = p v₂(b) − 4
e(k) = v₂(x(kQ))
A(k) = v₂(x(kQ)x(Q) − a₄)
B(k) = v₂(x(kQ) − x(Q))
```

とするものである。ただし、**今回の整数列定理には実際の点は登場しない**。
この解釈で以下の入力が成立することは、まだDkMathで証明していない。

- 1≤k≤p−1で1≤e(k)≤γ−1。
- e(2)+2e(1)=2A₁。
- e(k+1)+e(k−1)+2B(k)=2A(k)。
- A,Bについて、比較する付値が異なる場合のmin公式と、等しい場合の下界。
- e(p−1)=e(1)。

等しい付値同士の差では打ち消しが起こり得るので、常にminと等しいとは仮定しない。
この区別をLeanの引数にも残した。

ε=e(1)とすると、漸化式から帰納的に

\[
\theta\equiv k\varepsilon\pmod{2\gamma},\quad
-\gamma<\theta\le\gamma,\quad e(k)=\theta\text{ または }-\theta
\]

を構成する。これは法2γの円周上の移動を、絶対値で区間へ折り返した表現である。
末尾条件からe(p−2)=0または2γ∣pεが生じる。前者は正の下界と矛盾し、
後者はpを約分すると0<ε<γと矛盾する。

約分は`cancel_prime_modulus`で独立に証明した。
γ=pv−4なら、奇素数pが2γを割ると8=2³を割ってしまうので不可能である。
`no_prime_shifted_valuation_orbit`はこの約分を一般の漸化式定理へ供給する。
そのため、この特殊化では約分providerを追加仮定にする必要がない。

これは2進付値による有理torsion排除を分割する有用な核だが、上記の付値入力を証明したものではない。
`residual_valuation_modulus_cancel`だけは、同じSourceのbに直接特殊化した。

## 6. 再利用できた既存定理と、今回の探索で見つからなかった接続

| 現行の資産 | 利用先・限界 |
|---|---|
| `InvariantLine`、`finrank_torsion_prime` | 029-Aを追加の算術入力なしで実装できた |
| `StableLineMatrix`、NOTE-028の実際のWeil対 | 安定直線に適合する基底の対角成分の積＝円分指標を、対データの追加入力なしで供給できた |
| `FreyCounterexample.exists_source_of_counterexample`、`Source.ofCounterexample_spec` | 次段階のa≡3 mod4・b偶数の向き付けを、元の反例との関係ごと取り出せる |
| `FreyTwo`、`FreyPrimeProfile` | 判別式・c₄・最小性・半安定還元の既存入力。点のx座標の付値や慣性作用とは別 |
| `PascalDifference`、`residual_difference_nilpotent` | ρ(gᵖ)=1を供給できれば差分のp乗が零。全ガロア群の二択は供給しない |
| GNの位相積・Kummerの類群／単元の定理 | 円分整数・位相の問題であり、楕円曲線の局所慣性へ渡す定理は今回の探索範囲では見つからなかった |
| 関数体の点イデアル付値・Weil付値 | 幾何学的な場所の付値。今回必要な有理座標のv₂とは区別する |

`DkMath/FLT/Frey*`と`DkMath/Lib/NumberTheory/Elliptic*`を検索した範囲では、
局所慣性群のE[p]への作用を、既存の半安定還元から導く実装は見つからなかった。
Mathlibの数体の分岐・慣性群の定義だけでは、その接続は完成しない。

また、裸の`Source p`にはp≥5や向き付けのフィールドはない。
上流の`FreyPackage`にある仮定を、そのまま全Sourceの定理へ読み替えることはできない。
今回のSource 2の回帰例ではa=4,b=3で、実際に非零有理2-torsionがある。

## 7. 上流で確認した証明の接続箇所

調査先は一次資料の[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)。
以下は今回取得したファイルのblobであり、リポジトリ全体の依存行数を測定したものではない。

| ファイル（リポジトリからの相対パス） | blob |
|---|---|
| [stable_submodule_fixed_or_cofixed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean) | `4ae2516ff54e967fa4da4c9bf096259d24f20420` |
| [torsion_fixed_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_torsion_fixed_eq_zero.lean) | `25c75c67bc281ba4ff3f7df0d8b4811aed747392` |
| [rational_p_torsion_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean) | `fe61fd5d4f94d55b5a9da38d1541903c84397df0` |
| [reducible_hasCofixedLine](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean) | `18a39aa93bf3be48e2ddbebcc1bebd440cd40447` |
| [no_cofixed_large](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean) | `16f282e721fd66e1593db1149266834bfd99af1a` |
| [Mazur_Frey](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_Mazur_Frey.lean) | `ffb1dcff0da7a417a7966d1a341d0340096b91ac` |

二択の上流証明は、pでの慣性が部分空間または商に自明に作用するという分岐を先に選び、
2、p、それ以外の有限素数について同じ側の慣性作用を自明にし、最後に大域化している。
「各素数でどちらかが自明」という独立の二択だけでは、この同じ側の大域化を代用できない。

上流の可約性→cofixedは、二択と固定torsion排除を結ぶ短い論理部分である。
今回、その論理部分はDkMathの一般表現APIとして実装した。
有理torsion排除の上流ファイルは2進付値・有限軌道による証明を含む。
今回取り込んだのは、その`S04.Arith`の整数部分と約分の再証明である。

その後のcofixed不存在は別の大きな段階である。上流の最終分岐は5,7,13、11、p≥17に分かれ、
大きな指数ではisogeny・modular curve・Mazur型の算術へ進む。
今回の純整数核をもって、その段階まで短縮できたとは主張しない。
別リポジトリの`flt-regular`は今回追加取得していない。

## 8. 次の実装計画

次は029-Cの有理点の2進付値を優先する。実装済みの整数核へ渡すべき条件が具体的に固定できたためである。

1. 向き付け付きSourceについて、a₂の2進整性とv₂(a₄)=γ=pv₂(b)−4を証明する。
   原始反例からの縮約・向き付けの記録は既存の`PrimitiveReduction`と`OrientationTrace`を保持する。
2. 非零有理p-torsion点Qの位数がpであること、1≤k≤p−1のkQが非零であること、
   各有限座標の分母・零座標の扱いを整える。その後、倍点・加法公式と有限軌道の最小付値を使い、
   **全ての**kについて1≤v₂(x(kQ))≤γ−1を証明する。
3. 実際の加法公式からA,Bのmin法則と漸化式を作り、負の点から末尾条件を証明する。
   `no_prime_shifted_valuation_orbit`へ接続して有理torsion排除を閉じ、今回の降下同値で固定torsion排除を得る。
4. 029-Bは別に、局所慣性作用の定義、ℓ≠2,pの不分岐性、2とpの局所補題、
   同じ側の局所自明性からの大域化、という順に実装する。
5. 二択と固定点排除が揃った時点で、今回の条件付きcofixed抽出を無条件化する。
   その後に、指数範囲を明示したcofixed不存在・有理isogenyの議論へ進む。

段階2の上下界が次の数学的な難所である。判別式の付値だけでその上下界が出たことにはしない。
029-Bも現時点では未解決であり、円分行列式やPascal恒等式だけで接続を省略しない。

## 9. 回帰と検証

`DkMathTest.FLT.FreyStableLine`に名前付き定義・定理17個を置いた。
実在するSource 2で、安定部分群の抽出、非零固定点の有理点への降下、固定点排除が偽であることを検査する。
同じ実在曲線のE[37]では、任意の一次元部分空間の像の位数37と降下同値を検査する。
約分は37で検査し、p=2,v=3,m=2では法4の約分が失敗することも確認する。

さらに有限群F₅ˣの二次元表現diag(g²,g³)を構成した。
その行列式は全てのgについてgであり、第一軸は実際に一次元で安定である。
しかしg=2が第一軸に4、商に3で作用するので、第一軸はfixedでもcofixedでもない。
これは行列式だけから二択を導けないことの境界反例であり、Frey表現の反例ではない。

`Note029DependencyAudit`は本体34個・回帰17個の公理を検査し、主要9経路では型・opaque本体も走査する。
旧FLT終点、外部P2M/P2MW/FltRegular、Kummer終点、`sorryAx`を禁止し、必要な既存providerの到達も確認する。
一般表現と整数核の経路では楕円曲線・Freyへの依存を禁止する。
許可する公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
条件付き定理の監査合格は、その引数の算術条件を証明したという意味ではない。

実行コマンド・結果・ルート到達性の記録は[evidence/validation-note029.txt](evidence/validation-note029.txt)に保存する。
