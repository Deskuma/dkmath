# GN-LIB-003c — 素数冪Pascal行の正確な付値

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
対象モジュール単位の実装・検証を完了した。

## 実装した一般核

新所有者は [Lib.NumberTheory.BinomialPrimePower](../../../../DkMath/Lib/NumberTheory/BinomialPrimePower.lean)。
既存のA34と加法版、および2つの整除性帰結の計4定理を、Lib名で固定した。

| Lib定理（namespace `DkMath.Lib.NumberTheory`） | 役割 |
| --- | --- |
| `padicValNat_choose_prime_pow` | `v_p(choose (p^n) k) = n - v_p(k)` |
| `padicValNat_choose_prime_pow_add_index` | `v_p(choose (p^n) k) + v_p(k) = n` |
| `prime_power_pow_dvd_choose_of_padicValNat_index` | `r + v_p(k) ≤ n` から `p^r` 整除を供給 |
| `prime_power_dvd_choose_of_not_dvd_index` | pを因子に持たない添字には全n層が残る |

新所有者はLibのPadicValNatとMathlibのChoose.Factorizationだけを直接importする。
付値の2公式はMathlibのfactorization定理を再利用し、整除性はLibの付値APIから導く。
教科書docstringには由来、保持条件、解釈と `[DkMath.Lib]` を記した。

## 数学的な保持条件

全公式で `p.Prime` と `0 < k ≤ p^n` を保持した。`k = p^n`、`n = 0, k = 1`、`p = 2` を含む。
ゼロ添字を許すと、`v_p(0) = 0` の規約により公式は壊れる。
範囲外の係数ゼロへも公式を延長していない。

一般核の8個のLean例は端点、次数0、行4の添字1と2で付値が2と1に分かれる例、
行9の加法保存、指数37、ゼロ添字の反例、単位添字の整除性を確認する。
素数冪行の支持と正確な付値は異なる。正則・非正則の区別はこの公式の仮定にない。
類群のねじれ、Kummer単数条件、FLTの非存在証明を供給する定理ではない。

## 既存コードへの接続

[旧BinomialPrimePower](../../../../DkMath/NumberTheory/BinomialPrimePower.lean) の4定理を、
全修飾名・公開型を保持するwrapperへ置き換えた。旧docstringにもLibの転送先と昇格説明を付けた。
`UniformBeamHeight`、`FilteredBeamHeight` など全既存定義・構造の本体は変更していない。
旧ファイルのABC importとABC名への参照を除き、Lib名を使う。

consumerのビルドで、[PascalPrimeDial](../../../../DkMath/NumberTheory/PascalPrimeDial.lean) が
推移的なABC importに頼る1箇所を検出した。同じ型のLib定理への呼出しに修正し、再ビルドが成功した。
他の子孫モジュールでABC付値名を使う9モジュールには、ABC.PadicValNatへの別のimport経路があることを静的確認した。
Lib集約入口とLib READMEにも新所有者を登録した。

## 検証結果

- 新所有者、旧所有者、WeightedBinomial、PascalPrimeDialの4本体ターゲット：8931 jobs、成功、警告0。
- 新旧8宣言の型照会と依存公理監査：成功。許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 旧4署名の同一性、全既存定義・構造の本文保持、3変更Leanファイルの禁止構文不在、ファイルマーカーを静的確認。
- 元資料24ファイルのSHA256を再確認し、初回棚卸しは保持して後続監査リンクを追記した。

ユーザー指定によりフルビルド・DkMathTest・lake testは実行していない。
集約入口の確認はimport登録の静的確認に限る。
検証の証跡は [対応・型・ハッシュ](evidence/gn-lib-003c.json) と
[検証記録](evidence/validation-gn-lib-003c.txt) にまとめた。

次の工程はGN-LIB-004：有限和によるR_n、完成不足D_n、再帰・上界・正性の教科書実装。
