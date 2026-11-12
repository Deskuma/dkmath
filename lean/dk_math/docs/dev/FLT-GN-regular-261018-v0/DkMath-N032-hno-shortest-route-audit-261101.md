# DkMath / NOTE-032 — 一般 `hno` 証明経路の縮約監査

基準日: 2026-11-01 JST  
ブランチ: `dev/FLT-GN-regular-261018-v0`  
入力: `__snapshot-dk_math-lean-code-261101-0817.tar.gz`  
入力 SHA256: `da5205837fafdf59b381a562fee61fa6bab0bd4a16f30da3ea4eae2571cc05a8`  
外部比較: `anthropics/fermats-last-theorem`、`P2M/Sol/` の公開ソース、同梱監査文書に記録された head と現行デフォルトブランチの照合。

## 1. 索引の再構築

- 元の `.dkmath-theorems.sqlite3` は 2026-10-13 に作成されたもの。
- `python3 dkmath_theorems.py --db <出力DB> build --root .` を現行ソースで実行。
- 新 DB: `dkmath-theorems-261101.sqlite3`。
- 構文索引: 2,362 Lean ファイル、587,370行、33,412名前付き宣言。
- 旧 DB: 1,813ファイル、29,292名前付き宣言。
- 新 DB: `PRAGMA integrity_check` = `ok`。
- 構文索引は Lean kernel の宣言型・依存公理の検証ではない。

ローカル `DkMath.*` モジュールだけに限定したソース import 閉包の独立監査:

| 終点 | ローカル import 閉包 | 有効コード中 `sorry/admit` | 独自 `axiom` 宣言 |
|---|---:|---:|---:|
| `DkMath.FLT.FreyMazurLocalInputs` | 391 | 0 | 0 |
| `DkMath.FLT.FreyStableLineDiscriminantCriterion` | 374 | 0 | 0 |
| `DkMath.FLT.FreyHnoSmallGoodPrime` | 382 | 0 | 0 |
| `DkMath.FLT.Kummer.ElevenThirteenFLT` | 72 | 0 | 0 |
| `DkMath.FLT.Five.Main` | 33 | 0 | 0 |

注意: この検査はローカル import のテキスト走査。`Mathlib` 内部の依存、Lean elaboration、opaque 宣言の公理依存には踏み込まない。ユーザー報告の `lake build` / `lake test` とも別の検査である。

## 2. 証明済み部分のうち、削除可能な探索対象

1. **安定直線の全探索は不要。** `FreyStableLineDiscriminantCriterion.residual_hno_iff_zeroComponent_not_stable_at_two`（`p≥5`, `Even S.b`）により、`hno` は二進零成分直線 `E₀[p]` が大域ガロア非安定であることと同値。`residual_hno_iff_exists_zeroComponent_line_escape` は具体的 `σ,P` の存在へ同値変換する。ただし存在は未証明であり、同値化は算術的困難を除去しない。
2. **`a ≡ 3 (mod 8)` は閉鎖済み。** `FreyModEightIrreducibility.residual_no_cofixed_line_of_a_mod_eight`。
3. **小指数 5,7,11,13 は FLT による空虚証明を構成可能。** 5: `DkMath.FLT.Five.fermatFive_no_positive_solution`、7: `DkMath.FLT.Kummer.SevenDescent.fermatLastTheoremFor_seven`、11,13: `DkMath.FLT.Kummer.fermatLastTheoremFor_eleven` / `_thirteen`。`Source p` は非零整数 `a,b,c` と冪方程式を含む。5については自然数の正解排除から整数版へ橋渡しする必要がある。これは既存 FLT を**使用する**方向なので、一般 FLT を導く同一証明で自己依存させてはならない。
4. **小さい良還元素数がある場合は閉鎖済み。** `FreyHnoSmallGoodPrime.residual_hno_of_small_good_prime`: 奇素数 `q<p` が `abc` を割らなければ `hno`。したがって Cofixed なら `primorial (p-1) ∣ abc` が既に証明済み (`residual_cofixed_forces_primorial_support`)。この可除性は矛盾ではない。
5. **`a ≡ 7 (mod 8)` の分解群内に脱出元はない。** `FreySplitDyadic.residualZeroComponent_cofixed_decomposition_of_seven` / `FreyStableLineDiscriminantCriterion.residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven`。脱出元を探すなら大域ガロア群の分解群外に限る。ただしその実在性は `hno` に同値であり、これを仮定として導入しても問題は閉じない。
6. **Cofixed から商曲線の `2p` 有理捩れ点へ。** `FreyRationalTwoPTorsion.residual_cofixed_implies_rational_two_p_torsion` が、同じ整数商モデル `W` 上に `addOrderOf Q = 2*p` を提供。
7. **局所2/3は完成。** `FreyMazurLocalInputs.residual_cofixed_implies_geometric_prime_torsion_local_inputs` で `P=baseChangePoint (2•Q)` の `ord(P)=p`、Galois 固定性、2・3上の全延長付値環の零成分外性を合流。

結論: 未解決の最小領域（Source の向き付けを前提）:

```text
p >= 17, p prime
S.a % 8 = 7
Even S.b
Cofixed stable L  (反証法)
primorial(p-1) | S.a*S.b*S.c
W = residualIntegerKernelModel L ...
Q in W(Q), addOrderOf Q = 2*p
P = baseChangePoint (2*Q), addOrderOf P = p, Galois fixed
P outside zero component at all valuations above 2 and 3

Goal: False; equivalently obtain E0[p] global escape.
```

`3 | abc` は primorial 条件に含まれる。「3 good」の矛盾はこの残存分岐では使えない。

## 3. 外部 Mazur Step Three の真の数学的コア

外部 `P2M/Sol/S_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean` の `core`（220–289 行付近）を直接監査。

- `x` : `X₀(p)` 上の Galois 固定の次数1 place。`j(W)` と `j(W/<P>)` に対応する moduli point。
- `y₀ = [x - cuspZero]` を Jacobian `J₀(p)` から Eisenstein 商 `J_eis` に射影する。
- 2進局所入力と specialization により、ある `a` で `2^a • π(y₀)=0`。
- 3進局所入力と specialization により、ある `b` で `3^b • π(y₀)=0`。
- `gcd(2^a,3^b)=1` より `π(y₀)=0`。
- さらに `ℓ != p` の悪い素数で `P` が零成分に属すると仮定すると、もう一方の cusp との差から cusp 類の Eisenstein 射影も消える。
- しかし `cuspidalClassSurvives` が cusp 類の非消滅を保証する。矛盾。

この論理コア自体は約70行ほど（既存証明の220–289行）。しかし前提の構成には次の六領域が必要:

- `heckeOperatorsCommuteBar`, `heckeModuleBar`
- `eisensteinQuotientInvariantsFiniteAt_heckeModuleBar`
- `cuspidalClassSurvives_heckeModuleBar`
- `mazurQuotientSpecialization_heckeModuleBar`
- `tateCuspCriterion_jQuotVelu`
- `moduliPointExists_jQuotVelu_of_mult_two`

これらは未移植の実数学であり、任意の `Provider` 引数を定義して `hno` としてよい訳ではない。`STATUS-N032-GLOBAL-HNO-PROOF-PATH-AUDIT.md` の 11,111 モジュールは構文 import 閉包で、最小移植量ではない。

## 4. Step Three は終点ではない

外部 `P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean` は1451行。公開 `solution` は682行から始まる。局所状況と Step Three のほかに:

- p進の stable subgroup filtration
- level `p^m` の torsion tower / extension vanishing
- 局所慣性の同じ側への輸送・大域化
- bad primes 上の零成分の扱い
- 最後に good prime を一つ選び、Frobenius Cayley–Hamilton と有限還元群の点数を用いた `p² ≤ p` の矛盾

が必要。したがって Step Three だけを外部から再証明・移植しても `hno` は完成しない。

## 5. 短い別ルートの候補と障害

**候補 A: 一般有理捩れ上界（Mazur）。** `Q` が有理点で `ord Q=2p`。`p>=17` では `2p>=34>16`。もし任意の `E/Q` の有理 torsion 部分群の濃度 `<=16` が既に形式化済みなら、Step Three と torsion tower をすべて飛ばせる。数学的には最短。ただし 2026年11月時点の Mathlib に一般 Mazur torsion theorem があるという証拠は得られず、Leanの形式化課題としてなお巨大。外部Anthropicの `Mazur_Frey` は一般有理捩れ分類定理を提供していない。`Axiom` として追加するのは不可。

**候補 B: Frey 特化の `2p` 有理捩れ排除。** モジュラー曲線全般でなく、現在の `W` にだけ必要な排除にする。Mathlib の既存還元・2進/3進局所 API を再利用できる。ただし、今の局所条件だけで大域矛盾が出る根拠はない。Frey 特化の新しい算術アイデアを発見できない限り、Mazurの大域数学を再実装する必要は残る。

**候補 C: 上流 Mazur Step Three を最小依存で部分移植。** 数学的リスクを最も制御しやすい。`core` の二アンカー矛盾だけ先に汎用群論へ切り出し、Hecke / Jacobian / cusp / specialization のうち最小限の実定理だけを構成する。全インポート閉包の逐語移植よりは設計上有利だが、深い算術を省略できる訳ではない。

**候補 D: `E₀[p]` 脱出証明。** 型としては最短で、一つの `σ` と `P` を得ればよい。しかし現在の結果から分解群外の元の存在は全く出ていない。`hno ↔ ∃ escape` を右から左へ使うことは、新しい算術的障害を自動消去しない。

## 6. 推奨する次の実装順序

1. `FreyHnoSmallIndex.lean`（薄い分岐のみ）: p=5,7,11,13 を既存 FLT から一括処理。5の自然数/整数入口を型検査で確定。結果は依存を明記して監査。
2. `FreyHnoHardCase.lean`（定理の**正規化**のみ）: `p>=17`, `a%8=7`, `primorial(p-1)|abc` に縮約する定理を、既存 `FreyModEightIrreducibility`, `FreyHnoSmallGoodPrime` で作る。ここに未証明 `hno` を渡すためだけの仮定は導入しない。
3. `MazurStepThreeTwoAnchor.lean`（小さな完成可能部分）: 有限加法群/商群の一般補題として `2^a*y=0, 3^b*y=0 => y=0` と `cusp survives` からの反証パターンを実装。既存 Mathlib の補題で閉じることを確認。これは Mathlib 群論部分の実装であり Mazur Step Three 完了ではない。
4. **厳しい stop/go 判定**: 直接 `W` 上の `2p` 有理捩れ排除が既存 DkMath の2進/3進局所計算だけで導ける新しい不変量が存在するか調査。具体的な非自明補題がなければ、この迂回路に長時間投資しない。
5. 残る大域部分は、上流 `MazurStepThree` の六領域と後半 tower の消費定理を **逆依存 DAG** で列挙し、数学的意味を保ちながら必要なものだけ移植。入口だけの conditional provider で完成判定しない。
6. 回帰条件: ターゲットの `#print axioms` が `[propext, Classical.choice, Quot.sound]` の範囲、`sorryAx` を含まない、外部 FLT 終点の循環参照なし、`lake build` と `lake test`、小指数と分解群外ケースの証明を分岐別監査。

## 7. 今回の検証能力の範囲

- 実施: アーカイブSHA256、展開、SQLite再構築・integrity check、全ソース宣言索引、主要モジュールの型宣言・ソース監査、ローカル import 閉包の禁止構文走査、GitHub上の外部 `core` と `solution` 照合。
- 未実施: この実行環境での Lean kernel `lake build` / `lake test` / `#print axioms`。`lake` 実行環境が同梱されていない。成功したビルドはユーザー報告に基づく。
- 今回の成果は、コード修正ではなく最短路の **証明義務縮約と監査用索引の再生成**。一般 `hno` を証明したものではない。

参照: `docs/dev/FLT-GN-regular-261018-v0/STATUS-N032-GLOBAL-HNO-PROOF-PATH-AUDIT.md`、`FreyStableLineDiscriminantCriterion.lean`、`FreyModEightIrreducibility.lean`、`FreySplitDyadic.lean`、`FreyHnoSmallGoodPrime.lean`、`FreyRationalTwoPTorsion.lean`、`FreyMazurLocalInputs.lean`。
