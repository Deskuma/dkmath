# NOTE-031 第1部: 有限ガロア拡大の慣性生成とFixed/Cofixed輸送

日付: 2026-10-22（JST）。**031-001の有限段階を031-001Aとして実装した。**
全5ステップのうち、今回は最初の一般核を、有限数体の算術と絶対慣性の持ち上げに分割した。
有限ガロア拡大K/ℚの全有限素点の慣性群が全群を生成することを証明し、
同じ表現・同じ部分加群のFixed/Cofixedへの輸送まで接続した。

031-001全体は未完了である。絶対ガロア群の開部分群に対する定理と、
代数閉包の付値環の慣性群との比較を031-001Bへ残す。
Freyの局所算術031-002〜004、集約031-005、hcases・hnoは今回供給していない。

本体3ファイルに公開宣言16個、回帰ファイルに25個を追加した。
全公開宣言に教科書docstring、全新規Leanファイルに指定の`#print "file: ..."`を付けた。
汎用核は`DkMath.Lib`、回帰・依存監査は`DkMathTest`の通常入口へ組み込んだ。

## 1. ファイルと公開API

| モジュール | 宣言数 | 内容 |
|---|---:|---|
| `DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration` | 4 | 固定体の不分岐性、次数1、部分群が全群、慣性群の上限が全群 |
| `DkMath.Lib.RepresentationTheory.LocalFixedCofixed` | 9 | 部分群上のFixed/Cofixed、固定部分群、生成された全群への輸送 |
| `DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation` | 3 | 実際の有限ガロア群の慣性群へ一般核を適用 |
| `DkMathTest.FLT.InertiaLocalGlobal` | 25 | 実際の次数2の円分体と、局所二択の側を交換できない境界例 |
| `DkMathTest.FLT.Note031FiniteInertiaDependencyAudit` | — | 全公開宣言の公理、主要9経路の型・本体、公開入力3件の監査 |

有限数体の中心定理は次である。

```text
K : Field, NumberField K, IsGalois ℚ K
────────────────────────────────────────────────────
⨆ P : {P : Ideal (𝓞 K) // P.IsMaximal},
  P.val.inertia (K ≃ₐ[ℚ] K) = ⊤
```

Leanでは左辺の上限全体を括弧で囲む。
生成性や不分岐拡大不存在を追加の仮定として要求しない。
慣性群は実際の整数環のイデアルに対するMathlibの`Ideal.inertia`である。

## 2. 教科書の算術経路: 固定体の全素点が不分岐になる理由

全慣性群を含む部分群Hを取り、F=Kᴴとする。Hの正規性は要求しない。
Fの整数環の任意の極大イデアルpについて、整数性からKの上の極大イデアルPを取る。
Pの慣性群をGal(K/ℚ)とHそれぞれの作用で計算する。

Hが全体の慣性群を含むので、部分群への制限による慣性群の位数は変わらない。
慣性群の位数と分岐指数の等式から、

\[
e(P/(p\cap\mathbf Z))=e(P/p)
\]

となる。一方、塔の乗法性により左辺は

\[
e(P/p)\,e(p/(p\cap\mathbf Z))
\]

である。e(P/p)≠0を明示的に証明して約分し、e(p/(p∩ℤ))=1を得る。
分岐指数の非零性を省いて自然数の約分を行わない。
最後に現在のMathlibの`Ideal.ramificationIdx_eq_one_iff`で不分岐性へ戻す。

この部分を`fixedField_unramifiedAt_int_of_inertia_le`として独立に読める定理へ分けた。
次に`NumberField.exists_not_isUnramifiedAt_int`を実際に使う。
これはMinkowskiの判別式評価から「次数1でない数体には分岐素点が存在する」を導く定理である。
Fの全素点が不分岐なので[F:ℚ]=1となる。

有限ガロア対応の位数公式と次数の塔から、

\[
|H|=[K:F]=[K:\mathbf Q]=|\operatorname{Gal}(K/\mathbf Q)|
\]

となり、H=⊤を得る。最後にHを全慣性群の上限とすれば生成定理となる。
有限ガロア拡大の計数を、絶対ガロア群にそのまま適用してはいない。

## 3. DkMathの一般核: 同じ表現・同じ部分加群のまま輸送する

R加群Vの表現ρと部分加群Nについて、局所部分群I上の条件を定義した。

```text
FixedOn ρ N I   := ∀ g∈I, ∀ x∈N, ρ(g)x = x
CofixedOn ρ N I := ∀ g∈I, ∀ x∈V, ρ(g)x − x ∈ N
```

前者を満たす群元は`fixedSubgroup`を、後者を満たす群元は`cofixedSubgroup`をなす。
Cofixed側の積の閉性は、

\[
\rho(ab)x-x=(\rho(a)(\rho(b)x)-\rho(b)x)+(\rho(b)x-x)
\]

から従う。逆元ではgの条件にρ(g⁻¹)xを代入して符号を反転する。
この証明自体にはNの安定性の追加仮定は不要である。
全群でCofixedが成立すれば、Nの元の像もNへ入るため安定性と両立する。

各Iᵢがこの固定部分群へ入れば、その上限も入る。
⨆Iᵢ=⊤なら既存の大域述語`IsFixedOn`・`IsCofixedOn`を得る。
純群論の層では生成性を明示入力に取り、数体の層では第2節の証明から実際に供給する。
係数環は可換環、Vは任意の加群でよく、Vの有限性・次元2を要求しない。

有限数体の`isFixedOn_of_inertia`と`isCofixedOn_of_inertia`に残る算術入力は、
**全極大イデアルの実際の慣性群で、同じ側の作用が自明であること**である。
生成性を別名のproviderとして仮定に隠していない。

## 4. 回帰: 二択の量化順序を守る

実在する数体`CyclotomicField 3 ℚ`について、次数φ(3)=2と慣性群の生成性を検査した。
さらに全慣性群が⊥なら生成定理とガロア群の位数2に反することから、
少なくとも一つの非自明な慣性群の存在を証明した。
この回帰では、具体的な分岐素数を同定したとはしない。
同じ数体の任意の表現・同じ部分加群へのFixed/Cofixed輸送も型検査した。

別の境界例として、

\[
G=\mathbf F_5^\times\times\mathbf F_5^\times,
\qquad \rho(a,b)=\operatorname{diag}(a,b),\qquad N=\mathbf F_5(1,0)
\]

を構成した。Nは実際に次元1で、G安定である。
第一因子だけの部分群では商が固定され、第二因子だけの部分群ではNが点ごとに固定される。
二つの部分群はG全体を生成する。
しかし(a,b)=(2,1)でNの固定が破れ、(1,2)で商の固定が破れる。
従って、

\[
\forall i,\;(\mathrm{Fixed}_i\lor\mathrm{Cofixed}_i)
\quad\not\Longrightarrow\quad
\mathrm{Fixed}_{G}\lor\mathrm{Cofixed}_{G}.
\]

必要な前提は(∀i,Fixedᵢ)∨(∀i,Cofixedᵢ)である。
この有限群をFreyの慣性群へ同一視してはいない。
031-004でpにおける側を選び、031-002・003で他の素数に同じ側を供給する順序を守るための回帰である。

## 5. 模範解答から取り込んだ範囲と出典

有限算術核はAnthropicのApache-2.0の
[有限数体の部分群定理](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_subgroup_eq_top_of_forall_inertia_le.lean)
を読み、固定体不分岐・次数1・全群・上限の4段階に再構成した。
現在のMathlibの分岐指数APIへ合わせ、旧エイリアスの非推奨警告も除いた。
当該ファイルのヘッダに著作権・変更内容・blob SHA・ライセンスとNOTICEの所在を記載した。
参照先は同じNumberTheory階層の`RegularKummer/LICENSE`と`RegularKummer/ANTHROPIC-NOTICE`であり、
RegularKummerのLeanコードをimportしたわけではない。

一般の部分群上のFixed/CofixedはDkMathの既存述語から構成した。
楕円曲線専用の局所大域定理をそのまま複製せず、有限生成族一般に使える核へ分けた。

調査した8ファイルのパス・取得時blob SHA・利用区分は
[出典台帳](evidence/upstream-note031-001A.json)に保存した。
有限算術核1ファイル以外は依存調査であり、実装済みと数えていない。
特に[絶対ガロア群の開部分群定理](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean)
の下には、次の二つの持ち上げがある。

1. [有限慣性元から代数閉包の整数閉包への持ち上げ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_exists_lift_mem_inertia_integralClosure.lean)。
   整数閉包の極大イデアル、剰余類への作用、profinite群の安定化群の全射性を使う。
2. [整数閉包から付値環の慣性群への接続](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn.lean)。
   素イデアルを中心とする付値環、DVRの分数表示、剰余体上の作用の比較を使う。

これらの実装を省いて「全ての絶対慣性群が生成する」と仮定すれば、今回の数学的課題を残したままになる。
今回は有限算術までを確実に閉じ、その比較を次の独立した教科書にする境界で区切った。

## 6. 五段階の現在地と次の着手点

| 段階 | 現在地・必要な接続 |
|---|---|
| 031-001A | **今回完了**。有限数体の実際の慣性生成、Fixed/Cofixed輸送 |
| 031-001B | 次回。絶対慣性の持ち上げ、開部分群=⊤、実際の絶対ガロア表現への適用 |
| 031-002 | 未実装。2,p以外の良還元・乗法的還元からE[p]の慣性自明性を供給 |
| 031-003 | 未実装。2で部分空間と商の両方が固定されること。野生慣性と共役の局所理論が必要 |
| 031-004 | 未実装。pで一貫した側の二択。吸収する真部分空間、局所還元と慣性持ち上げが必要 |
| 031-005 | 未実装。選んだ側を全素数で保持し、同じSourceのhcasesとcofixed抽出へ接続 |

031-001Bでは、既存の`EllipticTorsionFiniteLevel.representationKernel_isOpen`と
`exists_normal_finite_level`が、実際の有限torsion表現の開核・有限正規レベルを既に与える。
一方、それだけでは有限慣性群の各元が付値環の絶対慣性から来ることは得られない。
まず上記二つの持ち上げをDkMath.Libで証明し、その後に開部分群の議論を接続する。
付値環のdecomposition subgroup内の慣性群と、全絶対ガロア群への像を区別する。
この経路では、今回の`subgroup_eq_top_of_inertia_le`を有限段階の終点として再利用できる。

既存の`FreyLocalReduction`や`FreyTwoArithmetic`は係数・判別式・還元型の算術に使える。
しかし還元型の証明と実際のE[p]の慣性作用の自明性は別であり、031-002〜004の結論を代用しない。
今回の汎用核はSourceを構成し直さず、既存の正規化・共通因子・曲線・点のデータを変更しない。
NOTE-030のhrat供給済み入口は維持され、hcasesとhnoは引き続き未供給である。

## 7. 検証

個別のコマンド・結果は[検証記録](evidence/validation-note031-001A.txt)に記録した。
集中的な監査ビルドは3,616ジョブ、通常の本体・FLT・Lib・テスト入口のビルドは
11,699ジョブで成功した。さらに`lake env lean DkMathTest.lean`、
`import DkMath`から7入口を確認するスモーク、マーカー照合、`git diff --check`が成功した。
新規コードに警告はない。全体ビルドでは既存の無関係な5件のsorry警告が再掲された。
公理監査では新規16宣言・回帰25宣言の全てを検査し、許容公理は
`propext`・`Classical.choice`・`Quot.sound`のみである。
主要9経路では型とopaque本体を含む依存グラフを走査し、Minkowskiの判別式評価、
分岐指数の塔、慣性群の位数、有限ガロア対応への実際の到達を検査した。
公開入力3件では有限算術の生成性を外部仮定に戻していないことも確認した。

Frey・旧FLT終点・外部provider・Kummer・整数折り返し核への依存は禁止した。
一般の部分群輸送と境界例には、さらに数体・慣性・分岐のAPIへの依存がないことを検査した。
有限体の一般加群インスタンスが使う通常の環のイデアルは許す。
この監査は指定した新規経路の検査であり、リポジトリ全体の公理自由性を述べるものではない。
