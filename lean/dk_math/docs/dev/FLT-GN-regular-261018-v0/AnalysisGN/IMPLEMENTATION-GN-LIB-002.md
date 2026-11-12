# GN-LIB-002 — GN完成の三者gcd・素数支持・付値

2026-10-23。ブランチ：`lib/FLT-GN-Completion-261023-v0`。

[CompletionCoprime.lean](../../../../DkMath/Lib/Cosmic/CompletionCoprime.lean) に
13宣言を固定し、`DkMath.Lib` から公開した。
全宣言は `DkMath.Lib.Cosmic` namespaceにあり、教科書docstringと `[DkMath.Lib]` を持つ。
既存のGN完成等式・gcd算術・Libの冪付値定理を組み合わせた一般橋である。
既存定理の名前変更や証明の置換は行っていない。

## 1. 三者gcdの共通核

自然数g,u,dについて

\[
\mathrm{Big}=(g+u)^d,\quad
\mathrm{Body}=g\,\mathrm{GTail}(d,1,g,u),\quad
\mathrm{Gap}=u^d
\]

と読む。これらは説明用の略記であり、上位のBigN/BodyN carrierをimportしない。
Bodyは積のまま扱い、自然数の減算で定義しない。

既存のGN完成等式から `Body + Gap = Big` を得る。
gcdは相手の項を足しても変わらないため、Body/Gap、Body/Big、Big/Gapの三つは等しい。
最後に `Nat.pow_gcd_pow` と `gcd(g+u,u)=gcd(g,u)` を使って

\[
\gcd(\mathrm{Big},\mathrm{Gap})=
\gcd(\mathrm{Body},\mathrm{Gap})=
\gcd(\mathrm{Body},\mathrm{Big})=\gcd(g,u)^d
\]

を証明した。ここには原始性・正性・正次数の仮定がない。
非原始対を正規化して共通因子を捨てることなく、そのd乗を結論に残す。

## 2. 公開APIと保持条件

以下の名前には `DkMath.Lib.Cosmic.` を付ける。

| API | 条件と役割 |
|---|---|
| `completion_body_add_gap` | 全Nat座標・全次数。既存完成等式への向き付きの橋 |
| `completion_gcd_big_gap` | 全Nat座標・全次数。底のgcdのd乗 |
| `completion_gcd_body_gap` | 同じ値をBody/Gapへ運ぶ |
| `completion_gcd_body_big` | 同じ値をBody/Bigへ運ぶ |
| `completion_coprime_big_gap` | `g.Coprime u` を仮定 |
| `completion_coprime_body_gap` | 同じ原始性を仮定 |
| `completion_coprime_body_big` | 同じ原始性を仮定 |
| `completion_pairwise_coprime` | 上の三つをBody/Gap、Body/Big、Big/Gapの順に束ねる |
| `completion_prime_not_dvd_body_gap_of_dvd_big` | 原始性・q素数・q∣Big。BodyとGapへの出現を排除 |
| `completion_prime_dvd_big_iff_dvd_sum` | d>0・q素数。原始性不要でq∣Big ↔ q∣g+u |
| `completion_prime_not_dvd_body_gap_of_dvd_sum` | d>0・原始性・q素数・q∣g+uからの排除 |
| `completion_padicValNat_big` | q素数・g+u≠0。Bigの付値はd倍 |
| `completion_degree_dvd_padicValNat_big` | 同じ非零条件を保持。次数がBigの付値を割る |

完成の次数dは、素数・正則素数・非正則素数のいずれにも限定していない。
素数支持で使うqの素数性とは役割が違う。
付値のAPIは既存の `DkMath.Lib.NumberTheory.padicValNat_pow` を特殊化し、
設計どおり完成根の非零条件を公開型に保持した。
付値が0の素数も「dが付値を割る」を満たすので、この可除性だけで素数の出現は結論しない。

## 3. 境界例の読み方

[直接importの回帰](../../../../DkMathTest/Lib/Cosmic/CompletionCoprime.lean) に19例を置いた。

- `(g,u,d)=(30,1,2)`：Body=960、Gap=1、Big=961。
- `(6,4,3)`：Big=1000、Gap=64、Body=936、三つのgcdは全て8。共通因子2の3乗を保持する。
- d=0：全座標でBig=Gap=1、Body=0、三つのgcdは1。g=u=0も含む。
- 零座標：`(0,7,3)` ではBody/Gapのgcdは343、`(3,0,2)` ではBody/Bigのgcdは9。
- `(0,0,3)`：gcdは0。正性を暗黙に仮定しない。
- 完成根91：合成数だが、7と13はBigを割りBodyとGapを割らない。7付値は平方化により2になる。
- 非原始対 `(2,2,2)`：2がBig・Body・Gapを全て割る。素数排除の原始性を削除しない。
- d=0、g=u=1：完成根を2が割る一方、Big=1を割らずBody=0を割る。完成根からの橋には正次数が必要。
- 完成根0の正次数：支持一致は成立する。原始性や付値の非零条件とは別の境界である。

## 4. 公開経路と検証

```lean
import DkMath.Lib.Cosmic.CompletionCoprime

example (d g u : ℕ) :
    Nat.gcd (g * DkMath.CosmicFormula.GTail d 1 g u) (u ^ d) = Nat.gcd g u ^ d :=
  DkMath.Lib.Cosmic.completion_gcd_body_gap d g u
```

`DkMath.Lib.lean` に所有者のimportを一つ追加し、`DkMath.Lib` と通常ルート `DkMath` から到達できるようにした。
回帰は `DkMathTest.lean` に登録した。
新しいCompletion facadeの作成はGN-PUB-001へ残す。

所有者と回帰のビルド、13宣言の公理検査、下位依存の確認を行った。
所有者のDkMath内の推移的依存は3個のLibモジュールで、応用層へのimportと循環はない。
通常ライブラリ・テスト入口・公開スモークの結果と既存警告の区別は
[validation-gn-lib-002.txt](evidence/validation-gn-lib-002.txt) に記録する。
宣言の型・行・ハッシュ・依存グラフは [gn-lib-002.json](evidence/gn-lib-002.json) に保存する。

次の単位はGN-LIB-003aのBinomTailの中立核である。
今回のgcd・支持・付値の橋は一般GN算術として固定したもので、hnoの供給やFLTの証明完了を結論しない。
