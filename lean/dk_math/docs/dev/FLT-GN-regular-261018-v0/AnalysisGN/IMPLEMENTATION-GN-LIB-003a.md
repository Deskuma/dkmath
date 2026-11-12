# GN-LIB-003a — BinomTailの一般尾項と正性のLib所有化

2026-10-23。ブランチ：`lib/FLT-GN-Completion-261023-v0`。

既存の [BinomTail](../../../../DkMath/Algebra/BinomTail.lean) の5補題を
[Lib.Algebra.BinomTail](../../../../DkMath/Lib/Algebra/BinomTail.lean) へ移管した。
全修飾名・型・証明本体は維持し、旧ファイルをimportだけの互換入口にした。
実装・個別検証・通常入口の最終確認を完了した。
新規数学の追加ではなく、既存の一般核の所有層を固定する工程である。

## 1. 宣言の所有者と型の範囲

namespaceは全て `DkMath.Algebra.BinomTail` のままである。

| 補題 | 保持した範囲 |
|---|---|
| `add_pow_tail_exists` | 任意の可換半環、n≥2。零座標・零因子を許す尾項の存在形 |
| `binom_tail_nat_dvd` | 自然数、n≥2。二次以上の尾項がu²で割れる |
| `add_pow_gt_sum_pows_nat` | 正の自然数a,b、次数k+2での厳密不等式 |
| `add_pow_gt_sum_pows_nat_of_two_le` | 同じ正性を2≤nの型で公開 |
| `add_pow_ne_sum_pows_nat_of_two_le` | 同じ仮定で、底a+bの冪がa^n+b^nと異なる |

全5補題のdocstringへ `[DkMath.Lib]`、移管元、互換入口、型の範囲と証明の読み方を加えた。
新旧所有者にはそれぞれ正しい `#print "file: モジュール名"` を置く。
同名宣言を二重定義せず、新所有者から旧モジュールをimportしない。

## 2. 一般半環の尾項と、自然数の正性を分ける

n≥2に対し、証明が与える具体的な尾項は

\[
H=\sum_{k=0}^{n-2}\binom{n}{k+2}a^k b^{n-2-k}.
\]

二項展開の先頭二項を取り出し、残りの各項からa²を因数として分離すると

\[
(a+b)^n=b^n+n b^{n-1}a+a^2H
\]

となる。ここには減算もaによる約分もなく、一般可換半環で成立する。
このHは既存の証明内部の有限和であり、今回新しい公開定義は追加していない。
存在形からHの一意性や正性を結論することもない。

自然数の可除性版は、先に同じ加法等式を得てから切り捨て差を整理する。
自然数差の見た目だけから、存在しない逆演算を使って因数分解しない。

一方、厳密不等式

\[
a^n+b^n<(a+b)^n
\]

は正の自然数a,bとn≥2を仮定する。二乗の交差項2abの正性を出発点とし、次数で帰納する。
次数の素数性・正則性は仮定しない。
標数2で交差項が消える例と、零座標・次数0・1の境界を回帰に残した。

また、3²+4²=5²でありながら3²+4²<(3+4)²である。
底がa+bの場合の不一致を、別の底zの完全冪の排除へ拡張しない。

## 3. 公開経路と既存consumer

```lean
import DkMath.Lib.Algebra.BinomTail

example : (1 ^ 37 + 1 ^ 37 : ℕ) < (1 + 1) ^ 37 :=
  DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le
    1 1 (by decide) (by decide) (by decide)
```

次数37も一般定理の特殊化として扱い、二項係数を全展開する証明を追加しない。
`DkMath.Lib.lean` に新所有者を一度だけimportし、`DkMath.Lib` と `DkMath` から公開した。

既存の `CosmicFormula.CosmicFormulaBinom` と `FLT.Basic` は旧importのまま再ビルドした。
両consumerのソースは移管前と同一であり、proofの変更で互換性を補っていない。
旧importだけで5名を確認するスモークも別に用意した。
この工程で一般FLTやhnoの証明を変更していない。

## 4. 検証と後続

[Lib直接importの回帰](../../../../DkMathTest/Lib/Algebra/BinomTail.lean) に17例を置き、
`DkMathTest.lean` に登録した。一般可換半環、零座標、負整数、ZMod 4、
次数2・37、零次・一次の境界、標数2、別の底の平方を扱う。
全5補題の推移的公理を検査し、標準の `propext`、`Classical.choice`、`Quot.sound` 以外ならエラーにする。

新所有者が直接importするのはMathlib／Leanの7モジュールだけで、DkMath応用層への依存はない。
5補題の型と証明本体は移管前のGit baselineとテキストハッシュでも一致した。
公開型と移管対応は [gn-lib-003a.json](evidence/gn-lib-003a.json)、
実行したビルド・通常入口・スモークと警告の範囲は
[validation-gn-lib-003a.txt](evidence/validation-gn-lib-003a.txt) に記録した。

次はGN-LIB-003bの平方完成・有限帯の中立部分である。
二項係数付値の中立化は003c、R_n/D_nは004として別に進める。

## 5. 最終確認

ユーザーから `lake build`・`lake test` の完了通知を受け、残りの確認を再開した。
当方では以下を独立に確認した。

- `lake build DkMath.Lib DkMath DkMathTest`：キャッシュを利用して成功、11,796ジョブ、終了コード0。
- `lake env lean DkMathTest.lean`：通常テスト入口の直接検査に成功。
- `DkMath` 単独import：移管した5名すべての公開型を確認、成功。
- 旧import単独・`DkMath.Lib` 単独importの確認、型・証明本体のハッシュ比較、追跡チェッカー、資料保存の検査も通過。

新規コードの警告はない。全体ビルドには既存研究ファイルの `sorry` 警告5件が残るが、
今回の5補題の公理監査とは区別して記録した。
最終確認でLeanソースを追加修正する必要はなかった。
ROADMAPをGN-LIB-003a完了へ更新し、次はGN-LIB-003bとする。
