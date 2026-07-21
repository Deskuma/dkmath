# Agent: Code GPT-5.6 Sol/light

## Agent log

codex://threads/019f82f0-4f31-7950-b8c8-ed84dfca5aa3

`````md
# 対応を開始

> よろしくお願いします！
>
> User context
>
> Attachments:
> - codex-jacobian-counterexample-start-260721.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-counterexample-start-260721.md`

<details><summary>12 previous messages</summary>

> 指定のスタート文書を作業仕様として読み、関連する過去方針も軽く確認してから、そのまま最初のチェックポイントへ進めます。まず要求範囲と完了条件を整理します。
>
> <details><summary>Explored a file, a search, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-counterexample-start-260721.md`
>
> </details>
>
> - Ran `git status --short && rg --files lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721`
>
> <details><summary>Explored a search</summary>
>
> - Searched for `AGENTS.md` in `..`
>
> </details>
>
> </details>
>
> 仕様は明確です。今回は `JAC-001`（多項式構文）と `JAC-002`（3点の明示的衝突）だけを実装し、Jacobian 以降には踏み込みません。次に設計文書と近隣モジュールのヘッダー／import 慣例を合わせます。
>
> <details><summary>Explored 5 files, 6 searches, 2 lists, ran a command</summary>
>
> <details><summary>Explored 4 files, a search, a list</summary>
>
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/README.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-implementation-design-260721.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md`
> - Read `./docs/BookOfMagic/0001_三重魔核と一意性解除.md`
> - Searched for `MvPolynomial|Matrix.*notation|![[]` in `DkMath`
> - Listed files in `Hackathon`
>
> </details>
>
> - Ran `git branch --show-current && sed -n '280,620p' docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-implementation-design-260721.md`
>
> <details><summary>Explored a file, 5 searches, a list</summary>
>
> - Listed files
> - Searched for `0001_.*三重|BookOfMagic`
> - Searched for `MvPolynomial|Matrix.vecEmpty|![[]` in `DkMath`
> - Searched for `^import Mathlib.*MvPolynomial|MvPolynomial.eval` in `Mathlib`
> - Read `./docs/BookOfMagic/0001_三重魔核と一意性解除.md`
> - Searched for `MvPolynomial` in `DkMath`
> - Searched for `![` in `DkMath`
>
> </details>
>
> </details>
>
> 設計との整合を確認しました。`Basic` は型と座標順序、`PolynomialMap` は `MvPolynomial.eval` 由来の写像、`Collision` は有理点計算だけに限定します。まとめ定理は、6本の証明を単に束ねる短い conjunction として自然なら追加します。
>
> <details><summary>Created 3 files, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Basic.lean` (+20 -0)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean` (+69 -0)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean` (+40 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision`
>
> </details>
>
> 3ファイルを作成し、対象モジュールだけのビルドを開始しました。現在は Lean の評価正規化がそのまま通るかを確認中です。ここで失敗した場合も、補助公理ではなく局所的な `simp`／`norm_num` の範囲で直します。
>
> <details><summary>Edited a file, explored 2 searches, a list, ran 3 commands</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean` (+3 -0)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision`
>
> <details><summary>Explored 2 searches, a list</summary>
>
> - Listed files in `Mathlib`
> - Searched for `Matrix.*Notation|Vector.*Notation|Matrix/Basic`
> - Searched for `macro "!\["|syntax "!\["` in `Mathlib`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean` (+1 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean` (+2 -0)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision`
>
> </details>
>
> 最初のビルドで分かった摩擦は2点だけです。現行 Mathlib ではベクトル記法の import が設計案と異なり、また `norm_num` 単独では `![…] 2` を最後まで簡約しませんでした。前者は正しい import に修正済みで、後者は評価定義を `simp` で開いてから有理数計算へ渡す局所修正を入れます。
>
> <details><summary>Created a file, edited a file, ran 4 commands</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean` (+9 -6)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Collision`
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean` (+1 -2)
> - Wrote `/tmp/JacobianCounterexample3Check.lean` (+8 -0)
> - Ran `lake env lean /tmp/JacobianCounterexample3Check.lean`
> - Ran `git diff --check && git status --short && git diff --stat`
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision`
>
> </details>
>
> 対象3モジュールは警告なしでビルド成功し、指定された4つの `#check` もすべて解決しました。最後に一時チェックファイルを除去し、禁止事項（`sorry`、`native_decide`、Jacobian 実装）が混入していないことと差分体裁を確認します。
>
> <details><summary>Deleted a file, ran a command</summary>
>
> - Deleted `/tmp/JacobianCounterexample3Check.lean` (+0 -8)
> - Ran `rg -n "sorry|axiom|native_decide|pderiv|jacobian|determinant" DkMath/Hackathon/JacobianCounterexample3 || true
> sed -n '1,180p' DkMath/Hackathon/JacobianCounterexample3/Basic.lean
> sed -n '1,220p' DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean
> sed -n '1,260p' DkMath/Hackathon/JacobianCounterexample3/Collision.lean
> git diff --check
> git status --short`
>
> </details>
</details>

JAC-001 / JAC-002 の実装が完了しました。Jacobian 以降には進んでいません。

1. 作成ファイル

- [Basic.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Basic.lean)
- [PolynomialMap.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean)
- [Collision.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean)

2. 定義

`Var3`, `Poly3Q`, `Point3Q`, `x`, `y`, `z`, `counterexampleP`, `counterexampleQ`, `counterexampleR`, `counterexamplePoly`, `evalCounterexampleQ`, `p0Q`, `p1Q`, `p2Q`, `targetQ`

`evalCounterexampleQ` は手書き関数ではなく、指定どおり `MvPolynomial.eval` から構成しています。

3. 定理

- `eval_p0Q`
- `eval_p1Q`
- `eval_p2Q`
- `p0Q_ne_p1Q`
- `p0Q_ne_p2Q`
- `p1Q_ne_p2Q`
- `three_point_collision_Q` — 上記6事実を束ねたコンパクトな証明書

4. ビルド結果

```text
lake build \
  DkMath.Hackathon.JacobianCounterexample3.Basic \
  DkMath.Hackathon.JacobianCounterexample3.PolynomialMap \
  DkMath.Hackathon.JacobianCounterexample3.Collision
```

成功しました。最終ビルドは警告なしです。

指定された一時 `#check` もすべて成功しました。

5. 評価の正規化

特別な補助定理は不要でした。`MvPolynomial.eval` とベクトル添字を局所的な `simp` で展開し、残った有理数計算を `norm_num` で閉じています。グローバル simp 属性は追加していません。

6. import の摩擦

現行 Mathlib では、設計案の `Mathlib.Data.Matrix.Notation` ではなく次が必要でした。

```lean
import Mathlib.LinearAlgebra.Matrix.Notation
```

また、`MvPolynomial.X` に伴い `PolynomialMap.lean` を `noncomputable section` としています。

`sorry`、axiom、`native_decide`、偏微分、Jacobian、determinant の実装は含まれていません。

7. 次のチェックポイント

次回レビュー後の候補は `JAC-003 Formal Jacobian` です。`MvPolynomial.pderiv` から `jacobianMatrixQ` を生成し、明示した9成分との一致を証明する段階になります。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-003.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-003.md`

<details><summary>8 previous messages</summary>

> `JAC-003` の指示書を実装仕様として読み、現在の3モジュールとの接続と停止境界を確認してから進めます。今回は形式偏微分の checkpoint に範囲を固定します。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-003.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,220p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/PolynomialMap.lean && sed -n '1,260p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean`
>
> </details>
>
> 指示書どおり、`jacobianMatrixQ` を `pderiv` から直接生成し、別途その正規形を `explicitJacobianQ` に置きます。まず9成分を提示された形で実装し、単一の `ext i j; fin_cases` 証明が閉じるか試します。既存のユーザー追加文書は変更しません。
>
> <details><summary>Created a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+51 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> </details>
>
> 単一証明の形自体は保てそうですが、現行の simplifier は多項式内の数値リテラルを `C` と認識した後も、`pderiv 4` などの定数微分を自動消去していません。Mathlib の既存補題名を確認し、`pderiv_C` 系を局所 simp セットへ明示します。
>
> <details><summary>Edited a file, explored 2 files, 3 searches, ran 7 commands</summary>
>
> <details><summary>Explored 2 searches</summary>
>
> - Searched for `theorem pderiv_(C|nat|ofNat)|lemma pderiv_(C|nat|ofNat)|pderiv_C` in `MvPolynomial`
> - Searched for `pderiv.*(OfNat|NatCast|IntCast)|map_ofNat.*pderiv` in `MvPolynomial`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+1 -0)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> <details><summary>Explored a file, a search</summary>
>
> - Read `./.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/PDeriv.lean`
> - Searched for `pderiv.*map_natCast|map_natCast.*pderiv|pderiv.*natCast|pderiv.*ofNat` in `Mathlib`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+1 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+7 -2)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+14 -4)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> <details><summary>Explored a file</summary>
>
> - Read `./DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+4 -4)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+1 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean` (+1 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Jacobian`
>
> </details>
>
> 9成分すべてが閉じました。行補題は不要です。ひとつ注意点として、`ext i j` はこの Mathlib では多項式係数まで再帰的に extensionality を進めてしまうため、同じ単一証明を `funext i j; fin_cases` に限定すると安定して閉じました。定数 `2,3,4` の偏微分だけ private 補題で `MvPolynomial.C` に戻しています。
>
> <details><summary>Created a file, deleted a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC003Check.lean` (+7 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision DkMath.Hackathon.JacobianCounterexample3.Jacobian`
> - Ran `git diff --check && git status --short && rg -n "det|native_decide|sorry|axiom" DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean || true`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC003Check.lean`
> - Deleted `/tmp/JacobianCounterexample3JAC003Check.lean` (+0 -7)
>
> </details>
</details>

JAC-003 Formal Jacobian を完了しました。

作成ファイル: [Jacobian.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.PolynomialMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
```

2. 明示した9成分

```text
[ 3*y*(1+x*y)^2*z + y^3*(7+6*x*y),
  3*x*(1+x*y)^2*z
    + 2*y*(1+x*y)*(4+3*x*y)
    + x*y^2*(7+6*x*y),
  (1+x*y)^3 ]

[ 3*(1+x*y)^2*z
    + 6*x*y*(1+x*y)*z
    + 3*y^2*(4+3*x*y)
    + 9*x*y^3,
  1 + 6*x^2*(1+x*y)*z
    + 6*x*y*(4+3*x*y)
    + 9*x^2*y^2,
  3*x*(1+x*y)^2 ]

[ 2 - 6*x*y - 3*x^2*z,
  -3*x^2,
  -x^3 ]
```

3. 公開定義・定理

- `jacobianMatrixQ`
- `explicitJacobianQ`
- `jacobianMatrixQ_eq_explicit`

`jacobianMatrixQ` は指定どおり、直接 `pderiv` から生成しています。

4. 証明構成

単一の9成分証明で閉じました。

```lean
funext i j
fin_cases i <;> fin_cases j
simp [...]
ring_nf
```

`ext i j` は多項式の係数まで再帰的に展開したため、行列の2添字だけを展開する `funext i j` を採用しました。

5. `pderiv` の摩擦

現行 Mathlib では、式中の多項式リテラル `2`, `3`, `4` に対する `pderiv` が自動ではゼロへ簡約されませんでした。そのため、各定数を `MvPolynomial.C` と同一視する3本の private 補題を追加しました。

公開 API には露出していません。

6. row helper

行単位の補題は不要でした。9本の公開成分補題も追加していません。

7. 検証

指定された4モジュールのビルドに成功しました。

```text
Build completed successfully (3291 jobs).
```

警告なしです。3つの一時 `#check` も成功し、チェックファイルは削除済みです。`git diff --check` も成功しました。

8. 停止境界

determinant の定義・計算、`det = -2`、最終証明書、複素化、正規化には着手していません。JAC-003 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-004.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-004.md`

<details><summary>8 previous messages</summary>

> `JAC-004` の指示書を読み、determinant 証明だけを実装します。既存の `Jacobian.lean` の正規形を真実源として使い、次 checkpoint の非単射証明書などには進みません。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-004.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,240p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean && rg -n "det_fin_three" lean/dk_math/.lake/packages/mathlib/Mathlib | head -30`
>
> </details>
>
> 仕様は明確です。[Jacobian.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Jacobian.lean) の `jacobianMatrixQ_eq_explicit` で形式微分由来の行列へ接続し、`Matrix.det_fin_three` の6項展開を直接 `ring_nf` に渡す最短経路を試します。
>
> <details><summary>Created a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean` (+31 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Determinant`
>
> </details>
>
> `Matrix.det_fin_three` は直接 rewrite でき、6項展開と消去もすぐ完了しました。残ったのは数学的計算ではなく、左辺の多項式リテラル `-2` と右辺の `-C 2` の表現差だけです。最後に係数埋め込みの簡約を加えます。
>
> <details><summary>Created a file, edited a file, ran 5 commands</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean` (+1 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Determinant`
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean` (+1 -1)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Determinant`
> - Wrote `/tmp/JacobianCounterexample3JAC004Check.lean` (+6 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision DkMath.Hackathon.JacobianCounterexample3.Jacobian DkMath.Hackathon.JacobianCounterexample3.Determinant`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC004Check.lean`
> - Ran `git diff --check && git status --short && rg -n "evalCounterexampleQ_notInjective|Certificate|Complex|normalized|native_decide|sorry|axiom" DkMath/Hackathon/JacobianCounterexample3/Determinant.lean || true`
>
> </details>
>
> determinant identity・非零性ともに閉じ、指定5モジュールのビルドと `#check` に成功しました。最後に一時チェックを除去して、JAC-005 以降の名前や禁止事項が入っていない状態で引き渡します。
>
> <details><summary>Deleted a file</summary>
>
> - Deleted `/tmp/JacobianCounterexample3JAC004Check.lean` (+0 -6)
>
> </details>
</details>

JAC-004 Determinant Certificate を完了しました。

作成ファイル: [Determinant.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

2. 追加した定理

- `jacobianMatrixQ_det_eq_neg_two`
- `jacobianMatrixQ_det_ne_zero`

3. determinant の証明経路

```text
jacobianMatrixQ
→ jacobianMatrixQ_eq_explicit
→ explicitJacobianQ
→ Matrix.det_fin_three
→ simp による行列添字の簡約
→ ring_nf
→ C (-2)
```

4. `Matrix.det_fin_three`

次の直接 rewrite が成功しました。

```lean
rw [Matrix.det_fin_three]
```

5. 多項式恒等式

6項の determinant 展開は `ring_nf` で閉じました。最後に残った多項式リテラル `-2` と `MvPolynomial.C (-2)` の表現差のみ `rfl` で閉じています。

6. 摩擦・性能

大きな tactic state や性能問題はありませんでした。対象モジュールの初回成功ビルドは約3.6秒でした。private helper theorem も不要です。

7. ビルド

指定された5モジュールすべてに成功しました。

```text
Build completed successfully (3292 jobs).
```

警告なしです。指定された2つの一時 `#check` も成功し、チェックファイルは削除済みです。

8. 差分検査

`git diff --check` は成功しました。

9. 停止境界

JAC-005 の非単射性、最終 conjunction certificate、複素化、determinant-one 正規化、Book of Magic API には着手していません。JAC-004 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-005.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-005.md`

<details><summary>6 previous messages</summary>

> `JAC-005` の指示書を読み、既存の collision と determinant 証明を合流させる範囲だけ実装します。複素化や正規化など次 checkpoint には進みません。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-005.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,220p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Determinant.lean && sed -n '1,260p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Collision.lean`
>
> </details>
>
> 指示内容は既存 theorem を再利用する短い合流層です。`Counterexample.lean` には3定理だけを追加し、写像・衝突・Jacobian・determinant の再定義や再計算は行いません。
>
> <details><summary>Created a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean` (+39 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Counterexample`
>
> </details>
>
> 3定理は追加 import なしでそのままビルド成功しました。非単射性は `p0Q ≠ p1Q` と共通像だけ、左逆不存在は `LeftInverse.injective` だけを使っています。続けて指定6モジュールの一括ビルドと公開 theorem の `#check` を行います。
>
> <details><summary>Created a file, deleted a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC005Check.lean` (+7 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision DkMath.Hackathon.JacobianCounterexample3.Jacobian DkMath.Hackathon.JacobianCounterexample3.Determinant DkMath.Hackathon.JacobianCounterexample3.Counterexample`
> - Ran `git diff --check && git status --short && rg -n "Complex|Normalized|BookOfMagic|native_decide|sorry|axiom" DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean || true`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC005Check.lean`
> - Deleted `/tmp/JacobianCounterexample3JAC005Check.lean` (+0 -7)
>
> </details>
</details>

JAC-005 Rational Counterexample Certificate を完了しました。

作成ファイル: [Counterexample.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Collision
import DkMath.Hackathon.JacobianCounterexample3.Determinant
```

追加の Mathlib import は不要でした。

2. theorem statements

```lean
theorem evalCounterexampleQ_notInjective :
    ¬ Function.Injective evalCounterexampleQ
```

```lean
theorem evalCounterexampleQ_noLeftInverse :
    ¬ ∃ G : Point3Q → Point3Q,
      Function.LeftInverse G evalCounterexampleQ
```

```lean
theorem jacobianCounterexampleCertificateQ :
    jacobianMatrixQ.det = MvPolynomial.C (-2 : ℚ) ∧
    jacobianMatrixQ.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleQ
```

3. 非単射性

`p0Q_ne_p1Q` に対し、単射性を仮定して `eval_p0Q` と `eval_p1Q` の共通像を適用する最小経路です。

4. 左逆不存在

仮定した `Function.LeftInverse G evalCounterexampleQ` の `hG.injective` と、確立済みの非単射性を直接矛盾させています。

5. rational certificate

次の3事実を conjunction で束ねています。

- 実際の形式 Jacobian determinant が `C (-2)`
- その determinant が非零
- 実際の多項式評価写像が非単射

既存の `three_point_collision_Q` は重複定義していません。

6. ビルド

指定された6モジュールすべてに成功しました。

```text
Build completed successfully (3293 jobs).
```

警告なしです。指定された3つの `#check` も成功し、一時ファイルは削除済みです。

7. 差分検査

`git diff --check` は成功しました。

8. 停止境界

JAC-006 の複素化、determinant-one 正規化、Book of Magic API など後続 checkpoint には着手していません。JAC-005 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-006.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-006.md`

<details><summary>8 previous messages</summary>

> `JAC-006` の指示書を読み、複素数世界への接続方法と停止境界を確認します。既存の有理証明書を保ち、指示された範囲だけ実装・検証します。
>
> <details><summary>Explored 3 files, 2 searches, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-006.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,220p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Counterexample.lean && rg -n "MvPolynomial.map.*pderiv|pderiv_map|eval_map|eval₂_map" lean/dk_math/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial | head -100`
>
> <details><summary>Explored 3 files, 2 searches</summary>
>
> - Read `./.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`
> - Read `./.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
> - Searched for `theorem map_det|lemma map_det` in `Matrix`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-006.md`
> - Searched for `map_det` in `Determinant`
>
> </details>
>
> </details>
>
> 輸送 API を確認しました。評価は `eval_map` と `eval₂_comp`、微分は `pderiv_map`、determinant は `RingHom.map_det` が現行 Mathlib にあります。大きな式を複製せず、この3本の可換性を主経路にします。
>
> <details><summary>Created a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean` (+141 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.ComplexLift`
>
> </details>
>
> 初回ビルドで局所的なAPI形の差が2点出ました。評価輸送では `eval₂_comp` が要求する座標関数を明示的に `qToC ∘ p` へ `change` する必要があり、点の相異性では複素 cast の簡約後に元の有理点定義も展開する必要があります。いずれも輸送経路を保った局所修正です。
>
> <details><summary>Edited a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean` (+6 -5)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.ComplexLift`
>
> </details>
>
> 複素輸送モジュールはビルド成功しました。大きな多項式の再評価・再微分・determinant 再計算は使っていません。次に全7モジュール、6つの指定 `#check`、禁止範囲、差分体裁をまとめて検証します。
>
> <details><summary>Created a file, deleted a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC006Check.lean` (+10 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision DkMath.Hackathon.JacobianCounterexample3.Jacobian DkMath.Hackathon.JacobianCounterexample3.Determinant DkMath.Hackathon.JacobianCounterexample3.Counterexample DkMath.Hackathon.JacobianCounterexample3.ComplexLift`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC006Check.lean`
> - Ran `git diff --check && git status --short && rg -n "Normalized|det_eq_one|BookOfMagic|native_decide|sorry|axiom" DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean || true`
> - Deleted `/tmp/JacobianCounterexample3JAC006Check.lean` (+0 -10)
>
> </details>
</details>

JAC-006 Complex Scalar Lift を完了しました。

作成ファイル: [ComplexLift.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.Counterexample
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
```

2. 追加した定義

- `Poly3C`
- `Point3C`
- `qToC`
- `polyMapQC`
- `castPointQC`
- `p0C`, `p1C`, `p2C`, `targetC`
- `counterexamplePolyC`
- `evalCounterexampleC`
- `jacobianMatrixC`

3. 係数埋め込み

```lean
def qToC : ℚ →+* ℂ := algebraMap ℚ ℂ

def polyMapQC : Poly3Q →+* Poly3C :=
  MvPolynomial.map qToC
```

複素多項式の大きな式は再定義していません。

4. 評価輸送

```lean
theorem evalCounterexampleC_castPointQC (p : Point3Q) :
    evalCounterexampleC (castPointQC p) =
      castPointQC (evalCounterexampleQ p)
```

現行 Mathlib の `MvPolynomial.eval_map` と `MvPolynomial.eval₂_comp` を組み合わせました。`evalCounterexampleC` は複素多項式の実際の `MvPolynomial.eval` です。

5. collision theorem

- `eval_p0C`
- `eval_p1C`
- `eval_p2C`
- `p0C_ne_p1C`
- `p0C_ne_p2C`
- `p1C_ne_p2C`
- `three_point_collision_C`

評価式の再計算はせず、有理評価定理を輸送しています。

6. Jacobian 輸送

```lean
theorem jacobianMatrixC_eq_map :
    jacobianMatrixC = polyMapQC.mapMatrix jacobianMatrixQ
```

`jacobianMatrixC` は複素多項式に対する実際の `pderiv` から定義し、`MvPolynomial.pderiv_map` で有理 Jacobian の係数写像と一致させました。

7. determinant 輸送

追加定理:

- `jacobianMatrixC_det_eq_neg_two`
- `jacobianMatrixC_det_ne_zero`

証明経路は次のとおりです。

```text
jacobianMatrixC_eq_map
→ RingHom.map_det
→ jacobianMatrixQ_det_eq_neg_two
→ MvPolynomial.map_C
→ C (-2 : ℂ)
```

determinant の再展開や再計算はしていません。

8. API 適用状況

- 指示書の `MvPolynomial.map_eval` 相当は、現行APIの `MvPolynomial.eval_map` と `eval₂_comp` を使用
- `MvPolynomial.pderiv_map` は直接適用
- `RingHom.map_det` は直接 rewrite

評価輸送では `eval₂_comp` に合わせ、座標関数を `qToC ∘ p` へ明示する `change` が必要でした。

9. fallback

大きな式の直接計算、複素式の複製、複素 Jacobian の明示行列は使用していません。点の相異性だけは、各点の第0座標を `norm_num` で比較しています。

10. 最終証明書

```lean
theorem jacobianCounterexampleCertificateC :
    jacobianMatrixC.det = MvPolynomial.C (-2 : ℂ) ∧
    jacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalCounterexampleC
```

併せて `evalCounterexampleC_noLeftInverse` も証明しました。

11. ビルド

指定された全7モジュールに成功しました。

```text
Build completed successfully (3294 jobs).
```

警告なしです。指定された6つの `#check` も成功し、一時ファイルは削除済みです。

12. 差分検査

`git diff --check` は成功しました。

13. 停止境界

JAC-007 の determinant-one 正規化、Book of Magic API、展示・提出用アセットには着手していません。JAC-006 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-007.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-007.md`

<details><summary>8 previous messages</summary>

> `JAC-007` の指示書を読み、正規化する対象・証明経路・停止境界を確認します。JAC-006 の複素証明書を基礎に、指定された determinant-one 層だけを実装します。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-007.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,300p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/ComplexLift.lean`
>
> </details>
>
> 設計は構造的に閉じています。正規化多項式を第一出力の係数倍として定義し、実際に `pderiv` した Jacobian と「対角行列 × 旧 Jacobian」の一致を証明した後、`Matrix.det_mul` で determinant を1へ運びます。元の大式や6項 determinant は展開しません。
>
> <details><summary>Created a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean` (+132 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Normalized`
>
> </details>
>
> 初回ビルドでは、数学的な障害ではなく `Fin 3` 上の有限和・有限積が自動展開されませんでした。行スケール定理は対角行列積の既存 API、対角 determinant は `det_fin_three` の局所展開を調べ、最小の有限添字簡約を加えます。構造的 determinant 経路は維持します。
>
> <details><summary>Edited a file, explored 3 searches, ran 2 commands</summary>
>
> <details><summary>Explored 3 searches</summary>
>
> - Searched for `theorem diagonal_mul|lemma diagonal_mul|diagonal_mul_apply|mul_diagonal` in `Matrix`
> - Searched for `sum_fin_eq_sum_range|prod_fin_eq_prod_range|prod_univ_succ` in `Mathlib`
> - Searched for `theorem C_mul|lemma C_mul|\[simp\].*C_mul` in `MvPolynomial`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean` (+5 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Normalized`
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean` (+0 -1)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Normalized`
>
> </details>
>
> 正規化モジュールはビルド成功しました。`Matrix.det_mul` の構造的経路は直接通り、対角行列単体の determinant だけは有限積簡約より `Matrix.det_fin_three` の局所展開が安定したため、そこに限定して使いました。正規化 Jacobian 全体の determinant は展開していません。
>
> <details><summary>Created a file, deleted a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC007Check.lean` (+10 -0)
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3.Basic DkMath.Hackathon.JacobianCounterexample3.PolynomialMap DkMath.Hackathon.JacobianCounterexample3.Collision DkMath.Hackathon.JacobianCounterexample3.Jacobian DkMath.Hackathon.JacobianCounterexample3.Determinant DkMath.Hackathon.JacobianCounterexample3.Counterexample DkMath.Hackathon.JacobianCounterexample3.ComplexLift DkMath.Hackathon.JacobianCounterexample3.Normalized`
> - Ran `git diff --check && git status --short && rg -n "BookOfMagic|padding|Demo|native_decide|sorry|axiom" DkMath/Hackathon/JacobianCounterexample3/Normalized.lean || true`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC007Check.lean`
> - Deleted `/tmp/JacobianCounterexample3JAC007Check.lean` (+0 -10)
>
> </details>
</details>

JAC-007 Keller Normalization を完了しました。

作成ファイル: [Normalized.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean)

1. imports

```lean
import DkMath.Hackathon.JacobianCounterexample3.ComplexLift
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
```

2. 追加した定義

- `normalizeOutputC`
- `normalizedTargetC`
- `normalizedCounterexamplePolyC`
- `evalNormalizedCounterexampleC`
- `normalizedJacobianMatrixC`
- `outputScaleDiagonalC`

第一出力多項式だけを `C (-1/2)` 倍しており、元の大きな多項式式は複製していません。

3. 評価輸送

```lean
theorem evalNormalizedCounterexampleC_eq_normalizeOutput
    (p : Point3C) :
    evalNormalizedCounterexampleC p =
      normalizeOutputC (evalCounterexampleC p)
```

`MvPolynomial.eval` の定数・積の規則を `simp` で適用しました。

4. collision theorem

- `normalized_eval_p0C`
- `normalized_eval_p1C`
- `normalized_eval_p2C`
- `normalized_three_point_collision_C`

既存の複素 collision と点の相異性を再利用し、大式の再評価はしていません。

5. normalized formal Jacobian

```lean
def normalizedJacobianMatrixC :
    Matrix (Fin 3) (Fin 3) Poly3C :=
  fun i j ↦
    MvPolynomial.pderiv j
      (normalizedCounterexamplePolyC i)
```

スケール済み行列として定義せず、正規化多項式を実際に形式微分しています。

6. row-scaling theorem

```lean
theorem normalizedJacobianMatrixC_eq_scale_mul :
    normalizedJacobianMatrixC =
      outputScaleDiagonalC * jacobianMatrixC
```

`Fin 3` 上の行列積を展開し、第一行だけが `C (-1/2)` 倍されることを証明しました。

7. determinant proof

```text
normalizedJacobianMatrixC_eq_scale_mul
→ Matrix.det_mul
→ outputScaleDiagonalC_det
→ jacobianMatrixC_det_eq_neg_two
→ C(-1/2) * C(-2)
→ C(1)
```

`MvPolynomial.C_mul` と `norm_num` で最後の係数計算を閉じています。

8. determinant API

- `Matrix.det_mul` は直接適用できました。
- `Matrix.det_diagonal` の有限積は自動簡約されなかったため、`outputScaleDiagonalC` 単体に限って `Matrix.det_fin_three` を使用しました。

9. fallback

正規化 Jacobian 全体の6項 determinant 展開や再計算は行っていません。局所的に展開したのは対角行列の determinant だけです。

10. 最終証明書

```lean
theorem normalizedJacobianCounterexampleCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC
```

併せて次も証明しました。

- `normalizedJacobianMatrixC_det_ne_zero`
- `evalNormalizedCounterexampleC_notInjective`
- `evalNormalizedCounterexampleC_noLeftInverse`

11. ビルド

指定された全8モジュールに成功しました。

```text
Build completed successfully (3295 jobs).
```

警告なしです。指定された6つの `#check` も成功し、一時ファイルは削除済みです。

12. 差分検査

`git diff --check` は成功しました。

13. 停止境界

高次元 padding、Book of Magic API、Demo、提出・展示アセットには着手していません。JAC-007 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-008.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-008.md`

<details><summary>8 previous messages</summary>

> `JAC-008` の指示書を読み、今回の成果物と公開境界を確認します。既存8モジュールを保ったまま、指定 checkpoint の範囲だけ実装・検証します。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-008.md`
>
> </details>
>
> - Ran `git status --short && rg --files lean/dk_math/DkMath/Hackathon/JacobianCounterexample3 lean/dk_math/DkMath/BookOfMagic | sort | head -100 && sed -n '1,280p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Normalized.lean`
>
> </details>
>
> 今回は数学証明には触れず、公開 import と監査面だけを追加します。まず [DkMath.lean](./lean/dk_math/DkMath.lean) の Hackathon import 周辺と、`DkMathTest` のヘッダー／監査ファイル慣例を合わせます。
>
> <details><summary>Created 2 files, edited a file, explored a file, 2 searches, a list, ran a command</summary>
>
> <details><summary>Explored a file, 2 searches, a list</summary>
>
> - Searched for `#print axioms|#print \"file:` in `DkMath`
> - Searched for `Hackathon|FinitePrimeEscapeGN5` in `DkMath.lean`
> - Read `./DkMath.lean`
> - Listed files in `DkMathTest`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath.lean` (+2 -0)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean` (+9 -0)
> - Wrote `./lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean` (+13 -0)
>
> - Ran `lake build DkMath.Hackathon.JacobianCounterexample3 DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms`
>
> </details>
>
> 公開 aggregator と監査モジュールはビルド成功しました。3証明書はいずれも標準公理 `propext`, `Classical.choice`, `Quot.sound` のみに依存し、`sorryAx` やプロジェクト固有 axiom はありません。続けてルート `DkMath` と aggregator-only の公開面を検証します。
>
> <details><summary>Created a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC008PublicCheck.lean` (+7 -0)
> - Ran `lake build DkMath`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC008PublicCheck.lean`
> - Ran `git diff --check && git status --short && git diff -- DkMath.lean && rg -n "sorry|axiom|native_decide|BookOfMagic|GNFiniteDifference|Demo" DkMath/Hackathon/JacobianCounterexample3.lean DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean || true`
>
> </details>
>
> ルート `DkMath` と aggregator-only の5つの公開 `#check` も成功しました。ルートビルドには既存の無関係な2箇所の `sorry` 警告が再生されましたが、新規 Jacobian モジュール・監査モジュールには警告がありません。最後に一時チェックファイルを除去します。
>
> <details><summary>Deleted a file</summary>
>
> - Deleted `/tmp/JacobianCounterexample3JAC008PublicCheck.lean` (+0 -7)
>
> </details>
</details>

JAC-008 Public Import and Audit を完了しました。

1. ファイル

作成:

- [JacobianCounterexample3.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean)
- [CheckAxioms.lean](./lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean)

変更:

- [DkMath.lean](./lean/dk_math/DkMath.lean:33)

数学定義・定理は変更していません。

2. aggregator import

```lean
import DkMath.Hackathon.JacobianCounterexample3.Normalized
```

最終 leaf だけを import しています。広域の `DkMath/Hackathon.lean` は作成していません。

3. ルート公開位置

既存の `FinitePrimeEscapeGN5` import の直後に追加しました。

```lean
-- Hackathon finite-prime escape → GN5 clean-channel demo
import DkMath.Hackathon.FinitePrimeEscapeGN5
-- Hackathon Jacobian counterexample formal certificate
import DkMath.Hackathon.JacobianCounterexample3
```

4. axiom audit

3証明書すべて同一の結果でした。

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateQ'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianCounterexampleCertificateC'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

```text
'DkMath.Hackathon.JacobianCounterexample3.normalizedJacobianCounterexampleCertificateC'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

5. 監査判定

以下は現れませんでした。

- `sorryAx`
- DkMath 固有 axiom
- determinant や collision に関する未証明仮定
- `native_decide` 依存

現れたのは標準的な `propext`, `Classical.choice`, `Quot.sound` のみです。

6. public-surface checks

aggregator だけを import した状態で、次の5定理すべてが解決されました。

- `jacobianCounterexampleCertificateQ`
- `jacobianCounterexampleCertificateC`
- `normalizedJacobianCounterexampleCertificateC`
- `normalized_three_point_collision_C`
- `evalNormalizedCounterexampleC_noLeftInverse`

一時 `#check` ファイルは削除済みです。

7. ビルド

成功:

```text
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

aggregator と監査モジュールは警告なしです。

ルート `DkMath` は成功しましたが、既存の無関係な次の2ファイルから `sorry` 警告が再生されました。

- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152`
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5385`

今回の Jacobian 証明書の axiom audit には影響していません。

8. 差分検査

`git diff --check` は成功しました。

9. 停止境界

JAC-009、高次元 padding、Book of Magic API、GN bridge、Demo、提出文書には着手していません。JAC-008 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-009.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-009.md`

<details><summary>10 previous messages</summary>

> `JAC-009` の指示書を読み、成果物・禁止範囲・検証条件を確認します。公開済み証明チェーンを壊さず、今回指定された checkpoint のみ進めます。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-009.md`
>
> </details>
>
> - Ran `git status --short && rg --files lean/dk_math/DkMath/Hackathon/JacobianCounterexample3 lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3 | sort && sed -n '1,220p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean`
>
> </details>
>
> JAC-009 は二層です。まず Hackathon 非依存の dependent `Gap : Core → Type` API を作り、次に正規化済み衝突を「同じ Core に異なる入力 Gap が2つある」と解釈する薄い bridge を追加します。既存 certificate の証明本体は変更しません。
>
> <details><summary>Created 4 files, edited 2 files, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath.lean` (+1 -0)
> - Wrote `./lean/dk_math/DkMath/BookOfMagic.lean` (+10 -0)
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean` (+68 -0)
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean` (+39 -0)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean` (+1 -1)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean` (+45 -0)
> - Ran `lake build DkMath.BookOfMagic.UniqueGapContract DkMath.BookOfMagic.GapCrystal DkMath.BookOfMagic DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge DkMath.Hackathon.JacobianCounterexample3`
>
> </details>
>
> 最初の generic module は import をゼロにしすぎたため、この環境では `∃!` 記法が未導入でした。証明上の問題ではないので、`ExistsUnique` を提供する最小 Mathlib 論理 import を特定して追加します。ビルド中に表示された `sorry` 警告はパース失敗によるエラー回復生成で、ソースに `sorry` を入れたものではありません。
>
> <details><summary>Edited 2 files, explored 2 searches, ran 2 commands</summary>
>
> <details><summary>Explored 2 searches</summary>
>
> - Searched for `syntax.*∃!|macro.*∃!|notation.*∃!` in `Mathlib`
> - Searched for `def Unique.*∃!|∃!.*=>` in `Logic`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean` (+2 -0)
>
> - Ran `lake build DkMath.BookOfMagic.UniqueGapContract DkMath.BookOfMagic.GapCrystal DkMath.BookOfMagic DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge DkMath.Hackathon.JacobianCounterexample3`
>
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean` (+1 -2)
>
> - Ran `lake build DkMath.BookOfMagic.GapCrystal DkMath.BookOfMagic DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge DkMath.Hackathon.JacobianCounterexample3`
>
> </details>
>
> dependent crystal の等式処理は `injection hcrystal` で閉じました。これにより Core が同一な2つの dependent field `gap₁`, `gap₂` の等しさを kernel が抽出し、`hne` と矛盾します。generic API と Jacobian bridge は警告なしでビルド成功しています。
>
> <details><summary>Created a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC009PublicCheck.lean` (+12 -0)
> - Ran `lake build DkMath DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC009PublicCheck.lean`
> - Ran `git diff --check && git status --short && rg -n "sorry|native_decide|axiom|GNFiniteDifference|PrincipalPartCompletion|padding|Demo" DkMath/BookOfMagic DkMath/BookOfMagic.lean DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean || true && rg -n "Hackathon" DkMath/BookOfMagic DkMath/BookOfMagic.lean || true`
>
> </details>
>
> `import DkMath` だけの公開チェック10件はすべて成功し、依存方向も確認できました。`DkMath.BookOfMagic` 配下から Hackathon への参照はゼロで、bridge だけが generic API と既存 Normalized 層を結びます。一時チェックを除去して完了します。
>
> <details><summary>Deleted a file</summary>
>
> - Deleted `/tmp/JacobianCounterexample3JAC009PublicCheck.lean` (+0 -12)
>
> </details>
</details>

JAC-009 Book of Magic API and Jacobian Bridge を完了しました。

1. ファイル

作成:

- [UniqueGapContract.lean](./lean/dk_math/DkMath/BookOfMagic/UniqueGapContract.lean)
- [GapCrystal.lean](./lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean)
- [BookOfMagic.lean](./lean/dk_math/DkMath/BookOfMagic.lean)
- [GapCrystalBridge.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean)

変更:

- [JacobianCounterexample3.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean)
- [DkMath.lean](./lean/dk_math/DkMath.lean:31)

既存の多項式・衝突・Jacobian・determinant・certificate 証明は変更していません。

2. dependent signatures

```lean
def UniqueGap
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core) : Prop
```

```lean
def GapFiber
    (RestoreRel : (core : Core) → Gap core → Prop)
    (core : Core)
```

```lean
structure GapCrystal
    (Core : Type u)
    (Gap : Core → Type v)
    (RestoreRel : (core : Core) → Gap core → Prop)
```

`Gap` は要求どおり `Core → Type v` の dependent family です。

3. unique-gap proof

`not_uniqueGap_of_two` は `∃!` の唯一候補を取り出し、`gap₁` と `gap₂` がともにその候補と等しいことから `gap₁ = gap₂` を導いて `hne` と矛盾させています。

4. dependent crystal proof

`forgetGap_notInjective_of_two_gaps` では、同じ `core` と異なる `gap₁`, `gap₂` を持つ2つの crystal を構成しました。

```text
forgetGap crystal₁ = forgetGap crystal₂
→ injectivity
→ crystal₁ = crystal₂
→ injection hcrystal
→ gap₁ = gap₂
→ contradiction
```

dependent field の等式抽出には Lean の `injection` を使用しました。Gap family を非依存型へ弱めていません。

5. generic public API

- `UniqueGap`
- `not_uniqueGap_of_two`
- `GapFiber`
- `GapCrystal`
- `CrystalWorld`
- `forgetGap`
- `forgetGap_notInjective_of_two_gaps`

`DkMath.BookOfMagic` は Hackathon コードを一切 import・参照していません。

6. Jacobian bridge

```lean
abbrev NormalizedGapFamilyC : Point3C → Type :=
  fun _ ↦ Point3C
```

```lean
def normalizedRestoreRelC
    (core : Point3C)
    (gap : NormalizedGapFamilyC core) : Prop :=
  evalNormalizedCounterexampleC gap = core
```

追加定理:

- `normalizedTargetC_not_uniqueGap`
- `normalizedForgetGap_notInjective`

どちらも `p0C`, `p1C` と既存の正規化 collision を generic theorem に渡すだけの薄い bridge です。

7. import direction

```text
DkMath.BookOfMagic
        ↓
GapCrystalBridge
        ↓
Normalized
```

Hackathon aggregator は最終 leaf を次へ変更しました。

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

`DkMath.lean` には `DkMath.Petal` の直後で追加しています。

```lean
import DkMath.BookOfMagic
```

8. public checks

`import DkMath` だけで指定された10件すべてが解決しました。既存の summit theorem も引き続き公開されています。

```lean
#check normalizedJacobianCounterexampleCertificateC
```

9. ビルド

すべて成功しました。

```text
DkMath.BookOfMagic.UniqueGapContract
DkMath.BookOfMagic.GapCrystal
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
DkMath.Hackathon.JacobianCounterexample3
DkMath
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
```

新規モジュールは警告なしです。ルートビルドでは既存の無関係な `sorry` 警告が再生されましたが、今回のAPIやbridgeには `sorry`、axiom、`native_decide` はありません。

既存3証明書の axiom audit も変わらず、依存は次のみです。

```text
[propext, Classical.choice, Quot.sound]
```

10. 差分検査

`git diff --check` は成功しました。

11. 停止境界

GNFiniteDifference、PrincipalPartCompletion、高次元 padding、Demo、提出・展示アセットには着手していません。JAC-009 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-010.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-010.md`

<details><summary>10 previous messages</summary>

> `JAC-010` の指示書を読み、前段の Book of Magic bridge との接続と今回の停止境界を確認します。既存証明を保ったまま、指定成果物だけ実装・検証します。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-010.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,240p' lean/dk_math/DkMath/BookOfMagic/GapCrystal.lean && sed -n '1,220p' lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/GapCrystalBridge.lean && rg -n "GNFiniteDifference|finiteDifference|difference.*quotient" lean/dk_math/DkMath | head -100`
>
> </details>
>
> JAC-010 は generic Book of Magic 内の多項式有限差分層です。既存 `GN` と `cosmic_id_csr'` を唯一の冪差恒等式として使い、`Polynomial.sum` で全多項式へ線形に持ち上げます。まず現行 Mathlib の `sum_*` と `induction_on'` の正確な形を合わせます。
>
> <details><summary>Created a file, edited a file, explored 3 files, 5 searches, ran a command</summary>
>
> <details><summary>Explored 4 files, 5 searches</summary>
>
> - Searched for `theorem induction_on'|def induction_on'|induction_on'` in `Polynomial`
> - Searched for `theorem cosmic_id_csr'|cosmic_id_csr'` in `CosmicFormulaBinom.lean`
> - Searched for `theorem sum_(add_index|monomial_index)|lemma sum_(add_index|monomial_index)|sum_def` in `Polynomial`
> - Read `./.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean`
> - Searched for `sum_add_index|sum_monomial_index` in `Inductions.lean`
> - Read `./.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean`
> - Read `./.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean`
> - Read `./DkMath/CosmicFormula/CosmicFormulaBinom.lean`
> - Searched for `X_pow_eq_monomial|monomial.*X \^|X \^.*monomial` in `Basic.lean`
>
> </details>
>
> - Wrote `./lean/dk_math/DkMath/BookOfMagic.lean` (+1 -0)
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean` (+115 -0)
>
> - Ran `lake build DkMath.BookOfMagic.GNFiniteDifference`
>
> </details>
>
> 初回ビルドでは2点だけ調整が必要でした。加法 case は式の括弧配置のため induction hypothesis を直接 `rw` できないので、一度 ring で「差の和」へ並べ替えます。cubic example は広い `simp` が `GN` 本体まで展開したため、`X^3 = monomial 3 1` と monomial rule だけを限定使用します。主定理は `cosmic_id_csr'` のままです。
>
> <details><summary>Edited a file, ran a command</summary>
>
> - Wrote `./lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean` (+12 -4)
> - Ran `lake build DkMath.BookOfMagic.GNFiniteDifference`
>
> </details>
>
> GN finite-difference moduleはビルド成功しました。`Polynomial.induction_on'` はそのまま利用でき、monomial case は既存 `cosmic_id_csr'` を一度 rewrite しただけです。直接の二項展開や新しい GN 定義は使っていません。全公開面と既存 Jacobian audit を続けて確認します。
>
> <details><summary>Created a file, ran 3 commands</summary>
>
> - Wrote `/tmp/JacobianCounterexample3JAC010PublicCheck.lean` (+8 -0)
> - Ran `lake build DkMath.BookOfMagic DkMath.Hackathon.JacobianCounterexample3 DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms DkMath`
> - Ran `git diff --check && git status --short && rg -n "sorry|native_decide|axiom|PrincipalPartCompletion|padding|Demo" DkMath/BookOfMagic/GNFiniteDifference.lean || true && rg -n "Hackathon" DkMath/BookOfMagic/GNFiniteDifference.lean DkMath/BookOfMagic.lean || true`
> - Ran `lake env lean /tmp/JacobianCounterexample3JAC010PublicCheck.lean`
>
> </details>
>
> 公開チェック6件、Book of Magic aggregator、Jacobian 公開面、root `DkMath`、既存 axiom audit はすべて成功しました。新規有限差分モジュールから Hackathon への依存もありません。一時チェックを削除して JAC-010 で停止します。
>
> <details><summary>Deleted a file</summary>
>
> - Deleted `/tmp/JacobianCounterexample3JAC010PublicCheck.lean` (+0 -8)
>
> </details>
</details>

JAC-010 GN Finite Difference を完了しました。

1. ファイル

作成:

- [GNFiniteDifference.lean](./lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean)

変更:

- [BookOfMagic.lean](./lean/dk_math/DkMath/BookOfMagic.lean)

既存 Jacobian 証明は変更していません。

2. imports

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic
```

root `DkMath` や Hackathon module には依存していません。

3. 定義

```lean
def GNFiniteDifference
    {R : Type*}
    [CommSemiring R]
    (p : Polynomial R)
    (h t : R) : R :=
  p.sum fun n a ↦
    a * DkMath.CosmicFormulaBinom.GN n h t
```

手動の係数配列ではなく、実際の `Polynomial R` と `Polynomial.sum` を使用しています。

4. basic API

- `GNFiniteDifference_eq_support_sum`
- `GNFiniteDifference_zero`
- `GNFiniteDifference_add`
- `GNFiniteDifference_monomial`
- `GNFiniteDifference_C`

support-sum theorem は定義的等式なので `rfl` です。加法性には `Polynomial.sum_add_index`、monomial rule には `sum_monomial_index` の simp API を使っています。

5. division-free theorem

```lean
theorem eval_add_sub_eval_eq_mul_GNFiniteDifference
    {R : Type*}
    [CommRing R]
    (p : Polynomial R)
    (h t : R) :
    p.eval (t + h) - p.eval t =
      h * GNFiniteDifference p h t
```

`Polynomial.induction_on'` による証明です。

- add case: 差を2つの差の和へ `ring` で整理し、帰納法の仮定を適用
- monomial case: `cosmic_id_csr'` を適用し、最後の係数配置だけ `ring`

6. `cosmic_id_csr'`

monomial case で次を直接使用しています。

```lean
have hGN :=
  DkMath.CosmicFormulaBinom.cosmic_id_csr'
    (R := R) n h t
```

その後、`t + h = h + t` へ並べ替えて `rw [hGN]` しています。GN の二項恒等式は再証明していません。

7. quotient theorem

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*}
    [Field K]
    (p : Polynomial K)
    (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t
```

division-free theoremを書き換えた後、`simp [hh]` で `h` をキャンセルしました。`field_simp` は不要でした。

8. API friction

`Polynomial.induction_on'` 自体は直接使用できました。

加法 case では、評価式の括弧配置により帰納法の仮定を直接 `rw` できなかったため、ring で差の和へ一度正規化しました。

9. cubic verification

`X ^ 3 = monomial 3 1` と一般 theorem、monomial rule から cubic example を導出しました。三乗差を直接展開する fallback は使用していません。

10. public checks

`import DkMath` だけで指定された6件すべてが解決しました。

- `GNFiniteDifference`
- `GNFiniteDifference_eq_support_sum`
- `GNFiniteDifference_add`
- `GNFiniteDifference_monomial`
- `eval_add_sub_eval_eq_mul_GNFiniteDifference`
- `differenceQuotient_eq_GNFiniteDifference`

一時チェックファイルは削除済みです。

11. ビルド

成功:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

新規モジュールは警告なしです。root build では既存の無関係な `sorry` 警告が再生されました。

12. Jacobian axiom audit

既存3証明書の結果は変わりません。

```text
[propext, Classical.choice, Quot.sound]
```

`sorryAx` や DkMath 固有 axiom はありません。

13. 差分検査

`git diff --check` は成功しました。

14. 停止境界

JAC-011、PrincipalPartCompletion、高次元 padding、Demo、提出・展示アセットには着手していません。JAC-010 で停止しています。

> よろしくお願いします
>
> User context
>
> Attachments:
> - codex-jacobian-JAC-011.md: `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-011.md`

<details><summary>13 previous messages</summary>

> `JAC-011` の指示書を読み、GN finite-difference 層から今回追加する対象と停止境界を確認します。既存 Jacobian／Book of Magic API を保ったまま、指定 checkpoint のみ進めます。
>
> <details><summary>Explored a file, ran a command</summary>
>
> <details><summary>Explored a file</summary>
>
> - Read `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-011.md`
>
> </details>
>
> - Ran `git status --short && sed -n '1,260p' lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean && rg -n "PrincipalPart|principal part|Laurent|IsUnit.*Polynomial|div.*X" lean/dk_math/DkMath lean/dk_math/.lake/packages/mathlib/Mathlib/Algebra/Polynomial | head -140`
>
> </details>
>
> JAC-011 は新しい数学ではなく、既存 theorem の直通 alias、公開 aggregator、axiom audit、完成版ドキュメントの整備です。Provenance は推測禁止なので、まずリポジトリ内の一次情報記録（URL・投稿者・日付）を限定検索し、見つからない項目は明示的に未固定とします。
>
> <details><summary>Explored 2 files, 2 searches</summary>
>
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/README.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md`
> - Searched for `https?://|Jacobian|ヤコビアン|counterexample|反例|author|著者|投稿|published|publication|accessed|参照日` in `BookOfMagic`
> - Searched for `Jacobian conjecture|Jacobian Conjecture|counterexample|反例` in `docs`
>
> </details>
>
> Context compaction
>
> Source: automatic
> Status: completed
>
> JAC-011 の仕上げに入ります。まず既存 README／roadmap と、リポジトリ内に記録済みの出典情報を確認し、記録のない書誌事項は推測せず明示します。
>
> <details><summary>Explored 10 files, a search, a list</summary>
>
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/README.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/roadmap.md`
> - Read `~/develop/lean/dkmath/docs/BookOfMagic/0001_三重魔核と一意性解除.md`
> - Read `~/develop/lean/dkmath/docs/BookOfMagic/0001_三重魔核と一意性解除.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-011.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/codex-jacobian-JAC-011.md`
> - Listed files in `jacobian-counterexample-verification-260721`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md`
> - Read `./DkMath/Hackathon/JacobianCounterexample3.lean`
> - Read `./DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md`
> - Searched for `def normalized|theorem normalized|abbrev Point3C|normalizeOutputC|targetC|GNFiniteDifference` in `JacobianCounterexample3`
>
> </details>
>
> 出典記録から確認できた一次情報は、Levent Alpöge のアカウント名、投稿説明、URLのみです。正確な公開日とアクセス日は記録されていないため、PROVENANCE では両項目を指定どおり未確定表示にします。これから Demo と文書面をまとめて実装します。
>
> <details><summary>Created 5 files, edited 2 files</summary>
>
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean` (+1 -1)
> - Wrote `./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Demo.lean` (+56 -0)
> - Wrote `./lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean` (+1 -0)
> - Wrote `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md` (+46 -0)
> - Wrote `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md` (+36 -0)
> - Wrote `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md` (+138 -0)
> - Wrote `./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md` (+41 -0)
>
> </details>
>
> Demo の6定理はすべて既存定理を右辺に置く直接 alias として追加し、公開 aggregator を Demo 経由に切り替えました。次に対象ビルドと公開 import 検査を行い、実際の axiom 出力を回収します。
>
> <details><summary>Created a file, deleted a file, ran 2 commands</summary>
>
> - Ran `lake build DkMath.BookOfMagic.GNFiniteDifference DkMath.BookOfMagic DkMath.Hackathon.JacobianCounterexample3.Demo DkMath.Hackathon.JacobianCounterexample3 DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms`
> - Wrote `./lean/dk_math/JacobianDemoPublicCheck.lean` (+8 -0)
> - Ran `lake env lean JacobianDemoPublicCheck.lean`
> - Deleted `./lean/dk_math/JacobianDemoPublicCheck.lean` (+0 -8)
>
> </details>
>
> `import DkMath` だけの一時ファイルで6つの公開 theorem がすべて解決し、一時ファイルも削除済みです。対象 audit は4証明書すべて同じ `[propext, Classical.choice, Quot.sound]` でした。残る root build と差分健全性を確認します。
>
> <details><summary>Explored 5 files, ran 2 commands</summary>
>
> - Ran `lake build DkMath`
>
> - Ran `git diff --check; git status --short; git diff -- DkMath/Hackathon/JacobianCounterexample3.lean DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean docs/hackathon/jacobian-counterexample-verification-260721/README.md docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md; test ! -e JacobianDemoPublicCheck.lean`
>
> <details><summary>Explored 5 files</summary>
>
> - Read `./DkMath/Hackathon/JacobianCounterexample3/Demo.lean`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/README.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md`
> - Read `./docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md`
>
> </details>
>
> </details>
</details>

JAC-011 は完了しました。これで JAC-001〜JAC-011 の全チェックポイントが完了です。

### 実装

新規作成:

- [Demo.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Demo.lean:1)
- [DEMO_CONTRACT.md](./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md:1)
- [PROVENANCE.md](./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md:1)

更新:

- [JacobianCounterexample3.lean](./lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean:7)
- [CheckAxioms.lean](./lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean:11)
- [README.md](./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md:1)
- [roadmap](./lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md:1)

Demo の公開定理は次の6件です。

- `jacobianDemo_det_eq_one`
- `jacobianDemo_three_point_collision`
- `jacobianDemo_notInjective`
- `jacobianDemo_noLeftInverse`
- `jacobianDemo_target_notUniqueGap`
- `jacobianDemoCertificateC`

すべて既存証明への直接 alias であり、行列式・点評価・非単射性を再計算していません。

Aggregator は `GapCrystalBridge` の直接 import から `Demo` の import に変更しました。既存 theorem surface は `Demo → GapCrystalBridge` を通じて維持されています。

### Axiom audit

`jacobianDemoCertificateC` の正確な出力は次のとおりです。

```text
'DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`sorryAx`、DkMath 固有公理、予期しない theorem assumption はありません。既存3証明書も同じ出力でした。

### 文書パッケージ

README は完成済み landing page に改訂し、指定された全セクション、現在の theorem 一覧、正規化 target `(1/8, 0, 0)`、module map、build、trust boundary を収録しました。

DEMO_CONTRACT は以下の3分未満構成です。

- 0:00–0:45: 正規化多項式写像
- 0:45–1:25: determinant `1` と axiom audit
- 1:25–2:35: 三点衝突、非単射、left inverse 不存在
- 2:35–2:55: `UniqueGap` 解釈
- 2:55–3:00: summit frame

PROVENANCE で確認できたリポジトリ記録は以下です。

```text
Author/account: Levent Alpöge (@__alpoge__)
Post description: X post announcing the explicit map
URL: https://x.com/__alpoge__/status/2079028340955197566
```

正確な公開日とアクセス日はリポジトリ内に確定記録がなかったため、推測せず次のように記載しました。

```text
Not yet fixed in repository records
```

Roadmap は JAC-001〜JAC-011 をすべて `Complete` とし、最終状態を次のように固定しました。

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

### 検証結果

`import DkMath` のみの一時ファイルから、Demo の6 theorem すべてについて `#check` が成功しました。一時ファイルは削除済みです。

以下はすべて成功しています。

```text
lake build DkMath.BookOfMagic.GNFiniteDifference
lake build DkMath.BookOfMagic
lake build DkMath.Hackathon.JacobianCounterexample3.Demo
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMath
git diff --check
```

Root build には、Jacobian プロジェクト外に以前からある `sorry` 警告などが再表示されました。今回追加したモジュールには警告・`sorry` はありません。

高次元 padding、`PrincipalPartCompletion`、動画作成、提出、PR 操作など後続作業には着手していません。JAC-011 で停止しています。
`````
