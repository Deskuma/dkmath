# NOTE-032-002 — Kummer深さの一般核と同じFrey点の非自明慣性

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `a81c260ec01e6a25747f18cfd613d9f5d12e9559`、作業ツリーはcleanだった。
本体13定理を追加した。032-002の算術の核と、幾何入力を明示したSource接続を実装した。
**無条件の非自明慣性・hnoは未証明**であり、032-003と共通する幾何の存在証明が残る。

## 1. 今回の到達点

| 層 | 実装した内容 | 明示して残した入力 |
| --- | --- | --- |
| 一般の付値体 | 単元指数の根の分離、単元の冪を固定する慣性は元も固定 | 指数と元の単元性 |
| ℚの代数閉包 | sᵖ=qᵐ、p≠q、p∤mなら、指定したq上の慣性が同じsを動かす | 素数p,q、同じ付値環Aとその住所 |
| 付値だけの入力 | v(t)ᵖ=v(q)ᵐから同じ非自明作用を得る | p∤m |
| 同じFrey Source | 整数判別式の自然数深さのp非可除性、零成分外の点Pを動かす慣性 | C,D、C.xの慣性固定、Pの零成分外性 |
| 条件付きhno | 非自明慣性の独立providerを除去 | 中心・方向・中心固定、零成分外の点、枝交換 |

正則素数・類群の仮定はKummer核に現れない。指数37でも同じ核を適用できる。
一般FLT、a≡3 mod8からの枝交換、a≡7 mod8の排除を今回の結果とはしない。

## 2. 模範解答の再構成

前工程で取得した固定コミット
`6e837e75355538c7f80bab5b956861e86c4eacc2` の
[非自明慣性の参考証明](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_exists_inertia_not_fixed_at_two.lean)
をローカル資料として読んだ。出典・ライセンスを新しい一般核のヘッダへ記載した。
外部のDefinitions、Theorems、P2M.Utilはimportしていない。

参考証明の私的な2進Kummer補題を、相異なる素数p,qの一般定理に組み替えた。
奇数pの形p=2k+1を使う箇所は、pとqのBezout等式を整数環へ写す証明へ置き換えた。
有限慣性の持ち上げと付値環の共役は、031-001/004のDkMath所有者を再利用した。

## 3. 単元の冪の剛性

[ValuationInertiaPower.lean](../../../DkMath/Lib/NumberTheory/ValuationInertiaPower.lean)
は任意の付値体上の4定理である。公開候補のコメントに `[DkMath.Lib]` を付した。

非自明なn乗根ζに対して、二重幾何級数から

```text
n = (1−ζ) Σ(i<n) Σ(j<i) ζ^j
```

を証明する。nが単元なら左辺の付値は1で、右辺の両因子は整だから、v(ζ−1)=1となる。
慣性元τが単元wのn乗を固定すると、ζ=τ(w)/wはn乗根になる。
ζ≠1ならv(τ(w)−w)=1となるが、慣性の剰余合同はこれを1未満にするので矛盾する。
指数nの素数性は不要であり、単元性とn≠0だけを使う。

単元wの条件を落としてはならない。2の37乗根sは非単元であり、
τ(s³⁷)=s³⁷でもτ(s)≠sとなる慣性元を後述の境界例で構成した。

## 4. 分岐指数と深さの台帳

[KummerInertia.lean](../../../DkMath/Lib/NumberTheory/KummerInertia.lean)
は3定理を公開する。証明は次の五段階を保持した。

1. Xᵖ−qᵐの根で生成した有限分解体Lと、q上の整数環の素点Qを取る。
2. Qの全慣性がsを固定すると仮定する。剰余合同とp∉Qから全p乗根の1も固定される。
   他の根rはr/sが1のp乗根なので固定され、慣性群が自明になる。
3. 有限剰余体の完全性とMathlibの慣性群位数公式から、e(Q/q)=1を得る。
4. (s)ᵖ=(q)ᵐの素イデアルQの重複度を比較してp∣mを得て矛盾する。
5. 有限慣性元を絶対慣性へ持ち上げる。最初に得る付値環A₁を共役で指定したAへ戻す。
   g(s)/sが1のp乗根で慣性固定であることを使い、同じsが動くことを保証する。

結論で付値環や根を選び直す弱い主張にしていない。
`s^p=q^m` の代わりに付値の等式だけを与える定理では、
`t^p/q^m` のp乗根wを代数閉性から取り、v(w)=1を証明する。
もし全慣性がtを固定すれば、単元の冪の剛性でwも固定する。
するとs=t/wが慣性固定のKummer根となり、前定理に反する。
逆向きには、慣性固定ならp∣mという必要条件を公開した。十分条件は主張しない。

## 5. 同じSourceへの適用

[FreyDyadicNontrivial.lean](../../../DkMath/FLT/FreyDyadicNontrivial.lean)
には6定理を実装した。

まず同じ整数モデルと有理モデルの判別式から
`(padicValInt 2 S.curve.Δ : ℤ) = padicValRat 2 S.rationalCurve.Δ`
を証明し、既存の−8障害を自然数値の台帳へ移す。

同じp捩れ点Pが零成分外にあれば、無限遠点ではない。
同じC,Dで031-002の倍点軌道の定理を適用すると、あるjについて

```text
1 ≤ j, 2*j < p
v(x(P)−C.x)^p = v(equationDefect)^j = v(Δ)^j
```

を得る。ここでCの `defect_valuation` を使い、別の判別式へ交換しない。
pの素数性とjの範囲からp∤v₂(Δ)jとなるので、Kummer核はx(P)−C.xを動かす。
C.xが慣性固定なら、その元はP自体も動かす。
点の等式からX座標の等式を取り出し、同じ実際の残余表現と結んだ。

`residual_no_cofixed_line_of_dyadic_geometry` は032-001の組立てを再利用し、
非自明慣性を呼出し側の独立入力から除去した。
中心固定からの吸収も既存の証明を使う。
E₀[p]と無限遠還元核E₁[p]は今回も区別した。

## 6. 検証

次のproduction moduleだけをビルドした（4034 jobs、警告0）。

```text
lake build DkMath.Lib.NumberTheory.ValuationInertiaPower \
  DkMath.Lib.NumberTheory.KummerInertia DkMath.FLT.FreyDyadicNontrivial
```

[独立境界資料](evidence/Note032KummerBoundary.lean) の4定理をLeanで確認した。
登録した通常テストと同じ本体である。

- 指数37の根を代数閉性から取り、非単元の冪だけが固定される例を構成。
- q=3,p=5,m=2にも同じ一般核を適用。
- p∣mなら有理数s=qが全慣性に固定される境界。
- q=n=2、ζ=−1ではv(ζ−1)<1となり、指数の単元性が必要な境界。

[Sourceスモーク](evidence/Note032DyadicSmoke.lean) の4定理もLeanで確認した。
指数37の同じSourceに対して深さ・同じ点の非自明作用・条件付きhno・条件付き既約性を確認した。
Source37の存在を構成したとはしない。
本体13定理と境界4定理・スモーク4定理、合計21宣言の `#print axioms` は
`propext`、`Classical.choice`、`Quot.sound` の範囲内だった。

`DkMath.Lib`、`DkMath.FLT`、通常テスト入口への登録は静的に確認した。
Libの依存方向、マーカー、禁止構文、既存の証明所有者と元NOTEの不変性、
文書リンク、`git diff --check` も確認した。
詳細は [機械可読記録](evidence/note032-002.json) と [検証記録](evidence/validation-note032-002.txt)。
フルビルド、集約ルート、DkMathTest、lake testのビルドはユーザー側の検証分担とした。

## 7. 残る幾何と次の単位

[ROADMAP](ROADMAP-NOTE032.md) の032-003を次の単位に分けた。

1. **003A**: 同じ2上のモデルで臨界中心・接線方向を取り、中心の慣性固定を供給する。
   既存 `CriticalCentre.inertia_fixed` はv(2)=1を要求するため、2上へ流用できない。
2. **003B**: 同じE[p]に零成分外の点が存在することを証明する。
   実際のE[p]の位数p²と、剰余節点曲線の捩れ上界≤pを比較する経路を調査する。
   零成分上の還元の単射性が必要であり、位数の差だけでは結論しない。
3. **003C**: a≡3 mod8から枝交換元を構成する。

003A/Bを供給すると、今回の定理から非自明慣性の幾何入力を除ける。
003Cを合わせて初めてmod8の3側の直接hnoへ進める。
GNの付値一般核だけでは同じ曲線の中心固定や枝交換を供給できないため、
今回も完成恒等式とガロア作用の間の未証明の橋は残した。
