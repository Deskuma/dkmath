# GN-LIB-001 — GN再帰・隣接支持のLib所有化

2026-10-23。ブランチ：`lib/FLT-GN-Completion-261023-v0`。

既存17定理をLibへ移管し、旧全修飾名・型・証明本体を維持した。
新しい一般化定理は追加せず、次のCompletion・gcdの教科書が使う所有層を固定した。

## 所有者と互換入口

| 所有する内容 | 新所有モジュール | 旧互換入口 | 定理数 |
|---|---|---|---|
| 二つの再帰、単位anchor、Bézout、単位anchorのIsCoprime | `DkMath.Lib.Cosmic.GNSuccessor` | `DkMath.NumberTheory.GapFocusing.Successor` | 5 |
| 共通約数・素数支持、Nat/Int/一般環の隣接coprime、直前にない素数 | `DkMath.Lib.Cosmic.GNSupport` | `DkMath.NumberTheory.GapFocusing.Support` | 12 |

namespaceは `DkMath.NumberTheory.GapFocusing` のまま維持した。
旧ファイルは新所有者をimportする薄い互換入口であり、同名定理の再定義を置かない。
既存の `GapFocusing` facadeと `PolynomialSuccessor` は旧importのまま利用できる。

```lean
import DkMath.Lib.Cosmic.GNSupport

open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

example (d x u : ℕ) (h : x.Coprime u) :
    (GTail d 1 x u).Coprime (GTail (d + 1) 1 x u) :=
  nat_coprime_adjacent_GN d x u h
```

新規consumerは上のようにLibを直接importできる。
新所有者の17定理には `[DkMath.Lib]`、移管元、旧importの互換性、必要条件と証明の読み方をdocstringへ加えた。
所有者と互換入口の双方に `#print "file: モジュール名"` を保持した。

## 数学的な読み方

`G_d = GTail d 1 x u`、`v = x+u` と置けば

\[
G_{d+1}=uG_d+v^d=vG_d+u^d.
\]

共通約数はこの二表示から `u^d` と `v^d` を割る。
Natでは共通素数を両座標へ戻し、原始性から排除する。
一般可換環では座標冪のBézout関係を二つの再帰へ代入し、隣接GNのBézout関係を得る。
有限和と線形結合による証明なので、gapを約分したり整域性を追加したりしない。

維持した境界は次の通りである。

- 二つの再帰は任意の可換半環、全次数、零座標で成立する。
- 原始座標からの隣接coprimeは次数0も含み、Int版は負座標も許す。
- 原始性が必要条件になる逆向きは、従来どおり次数2以上である。
- 素数存在の定理は、前の次数と両座標の正性・原始性を必要とする。
- 存在する素数が出現しないのは直前の次数であり、全過去次数や付値1へ強めない。

既存の次数6の反例回帰も通した。`GN₆(1,1)=63` の素数は次数2または3に既出であっても、
直前の次数5には出現しない。この二つの意味を区別する。

## 検証

新旧所有者の4モジュール、既存の支持・successor・住所の回帰、`GapFocusing` facadeをビルドした。
新しい [Lib直接importの回帰](../../../../DkMathTest/Lib/Cosmic/GNSuccessorSupport.lean) では
零次数・零座標・非原始対・負座標・零因子を持つ `ZMod 6` を含む10例を確認する。
同じテストで17宣言の推移的公理を検査し、`propext`、`Classical.choice`、`Quot.sound` 以外ならエラーにする。

定理の型と証明本体は移管前後のテキストハッシュでも一致した。
下位依存閉包は4個のDkMath.Libモジュールで、応用層へのimportも循環もない。
テストを `DkMathTest.lean` の通常入口にも登録した。

実行コマンド、通常ライブラリとテスト入口の結果、既存警告の区別は
[validation-gn-lib-001.txt](evidence/validation-gn-lib-001.txt) に記録する。
17定理の旧所有者・新所有者・行・型・ハッシュ・依存グラフは
[gn-lib-001.json](evidence/gn-lib-001.json) に記録した。
初回の [source-inventory.json](evidence/source-inventory.json) は移管前の棚卸しとして保持する。

## 次の単位

GN-LIB-001の所有化と互換性を確定し、次はGN-LIB-002のBig・Body・Gapの三者gcdへ進む。
Completion facadeの新設、R_n/D_n、円分住所の中立化、hnoへの接続は後続の別工程である。
