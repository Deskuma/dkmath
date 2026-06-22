# History

cid: 6a2fd4ed-1c54-83ee-9348-aadb84257cf0

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [000](History-000.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (作業概要の見出し)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

### 2026/06/16  1:47

実装しました。

追加した入口は [Rotation.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation.lean:7) です。Lean では `2D` が通常識別子ではないため、import/module 名は `DkMath.CosmicFormula.Rotation.«2D»` として扱っています。物理パスは指定どおり `DkMath/CosmicFormula/Rotation/2D/...` です。

主な中身:

- [Basic.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/2D/Basic.lean:32): `Vec`, `q2`, `star`, `Vec.q2_star`, `UnitKernel`, `LevelSet`
- [Trig.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/2D/Trig.lean:35): 抽象的な `KernelFamily` から `C^2 + S^2 = 1`, `C_add`, `S_add`
- [Rotation2D-Implementation.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/Rotation2D-Implementation.md:1): 英語の実装結果ドキュメント
- [CosmicFormula.lean](/lean/dk_math/DkMath/CosmicFormula.lean:17): `DkMath.CosmicFormula.Rotation` を集約 import に追加

確認:

- `lake build DkMath.CosmicFormula.Rotation` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功

補足: `docs/not_implements/宇宙式で三角関数の証明.md` は作業前から未追跡の入力ファイルとして残っており、内容は変更していません。

---

おお。そうか `2D` は識別子とならないのか。
アルファベットから始めなければか。
`«2D»` → `CF2D`
に、リファクタリングしよう。
早い段階でやったほうが良い。

---

`«2D»` を `CF2D` にリファクタリングしました。

変更点:

- `Rotation/2D.lean` → `Rotation/CF2D.lean`
- `Rotation/2D/Basic.lean` → `Rotation/CF2D/Basic.lean`
- `Rotation/2D/Trig.lean` → `Rotation/CF2D/Trig.lean`
- namespace を `DkMath.CosmicFormula.Rotation.CF2D` に変更
- import を `DkMath.CosmicFormula.Rotation.CF2D...` に更新
- docs も escaped identifier 前提の説明から `CF2D` 前提へ更新

確認:

- `rg '«2D»|Rotation\\.2D|Rotation/2D' ...` で旧名なし
- `lake build DkMath.CosmicFormula.Rotation` 成功
- `lake build DkMath.CosmicFormula` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功

補足: 既に index に載っていた前回追加分があるため、`git status` では旧 staged との差分として `AM` と新 `CF2D` untracked が混ざって見えています。staging は触っていません。

### 2026/06/21 19:54 JST (Return to the trigonometric real-analysis route)

1. 目的:
   - `LinearOrder` と decidable comparison を独立保留課題とし、CF2D
     Phase 2 に必要な実数解析本線へ戻る。
   - 現場管理文書と TODO を再確認し、次の実装可能な checkpoint を定める。
2. 実施:
   - `DkMath.Analysis.DkReal.Semantic` を追加した。
   - lower endpoint の実数列を定義し、単調性と上方有界性を証明した。
   - semantic value を lower endpoint の上限として noncomputable に定義した。
   - semantic value が全 approximation interval に属することを証明した。
   - lower endpoint が semantic value へ単調収束することを証明した。
   - `task-trig-real-analysis-046.md` に semantic bridge の実装順を記録した。
3. 結論:
   - Route B の計算可能核を変更せず、Mathlib `Real` の completeness を
     semantic bridge にだけ導入できた。
   - 次の主課題は `DkReal.Equiv` による semantic value の不変性である。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.Semantic` 成功。
5. 失敗事例:
   - 最初のビルドでは `lowerReal` / `upperReal` が未展開のため
     `exact_mod_cast` が型一致しなかった。定義を明示展開して修正した。
6. 次の課題:
   - 全区間に属する実数点の一意性を証明する。
   - `Equiv x y -> semanticValue x = semanticValue y` を証明する。
   - その後 `DkNNRealQ` へ semantic map を降ろす。

### 2026/06/21 20:28 JST (Semantic uniqueness and quotient descent)

1. 目的:
   - review-trig-046 の指摘を反映し、semantic point の一意性と
     representative independence を閉じる。
   - `DkNNRealQ` へ semantic evaluation を降ろす。
2. 実施:
   - `widthReal` と `tendsto_widthReal_zero` を追加した。
   - 全 approximation interval に属する実数点の一意性を証明した。
   - `Equiv x y -> semanticValue x = semanticValue y` を証明した。
   - `DkNNRealQ.semanticValue` を quotient lift として定義した。
   - rational constants、zero、one、addition の semantic 保存を証明した。
   - 公開 import の計算可能性説明を semantic module 付きの現状へ修正した。
3. 結論:
   - DkReal representation から Mathlib Real への写像が quotient-compatible
     になった。
   - 次の解析本線は nonnegative multiplication、power、order bridge である。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.Semantic` 成功。
5. 失敗事例:
   - rational-to-real cast の composed function が簡約されず、関数外延性で
     cast 前後の式を明示的に一致させた。
   - quotient zero/one は `rfl` では閉じず、rational evaluation theorem を
     経由した。
6. 次の課題:
   - semantic multiplication と natural power preservation。
   - internal order と Mathlib Real order の保存・反映。
   - 保存量 `q2` の semantic bridge を最初の CF2D consumer とする。

### 2026/06/21 20:47 JST (Semantic semiring and order preservation)

1. 目的:
   - quotient semantic map の乗法・自然数冪保存を閉じる。
   - canonical Gap により内部順序から Mathlib Real 順序への保存を示す。
2. 実施:
   - 非負 representation の semantic nonnegativity を証明した。
   - `mulNonneg` と `powNonneg` の semantic 保存を証明した。
   - `DkNNRealQ.semanticValue_mul` と `semanticValue_pow` を追加した。
   - `y = x + z` という canonical Gap 分解から
     `DkNNRealQ.semanticValue_mono` を証明した。
   - task 046、初期層設計、公開入口の TODO を現在の到達点へ同期した。
3. 結論:
   - `semanticValue` は非負商半環から Mathlib Real への順序保存半環写像に
     必要な個別法則を備えた。
   - 順序保存には subtraction、decidable comparison、`LinearOrder` の
     いずれも不要であり、canonical Gap が直接の証明核となった。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.Semantic` 成功 (8271 jobs)。
5. 次の課題:
   - semantic order reflection を証明する。
   - CF2D の保存量 `q2` を最初の実数解析 consumer として接続する。

### 2026/06/21 23:18 JST (Bundled semantics and the first CF2D consumer)

1. 方針:
   - order reflection は専用課題として保留する。
   - 現在の半環保存則だけで到達できる CF2D bridge を先行する。
2. 実施:
   - `semanticValue` を `DkNNRealQ →+* ℝ` の `semanticRingHom` として束ねた。
   - `SemanticCF2D.lean` を新設し、CF2D 依存を意味論本体から隔離した。
   - `semanticVec` と `semanticValue_q2` を実装した。
   - 非負 DkMath unit kernel を実数 unit kernel へ運ぶ
     `semanticUnitKernel` を実装した。
3. 観測:
   - CF2D の抽象 `Semiring` 冪と DkNNRealQ の表現用 `Pow` は、型クラス上
     異なる経路を取る。
   - `q2` の二乗を積へ正規化すると、semantic multiplication だけで橋が
     閉じる。追加の冪同一視や解析定理は不要だった。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 05:38 JST (Exact order four on the plane action)

1. 実施:
   - `SemanticExactActionOrderFour` を定義した。
   - exact kernel order four と exact action order four の同値を証明した。
   - exact action order four と semantic core zero の同値を証明した。
2. 原理:
   - `q2 = 1` の保存核条件が kernel を unit locus に拘束する。
   - `star` の結合則と `act_star` が kernel 積を作用合成へ移す。
   - action の忠実性が作用等式から kernel 等式へ戻す。
3. 結論:
   - 保存則単独ではなく、保存核・加法則に相当する積・忠実作用・
     第一象限制約の組合せが、角度なしの有限位数分類を生んでいる。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
5. 次の課題:
   - transported real `UnitKernel` を最初の CF2D 解析定理へ接続する。
   - order reflection は subtraction や decidable comparison を導入せず、
     独立課題として検討する。

### 2026/06/21 23:29 JST (Real-side CF2D action without source subtraction)

1. 方針:
   - DkNNRealQ へ subtraction を追加せず、transport 後の `Real` 側でのみ
     CF2D action を使う。
2. 実施:
   - semantic unit kernel の core / beam 非負性を証明した。
   - semantic 座標について `C^2 + S^2 = 1` を証明した。
   - `semanticAct` とその core / beam 座標式を追加した。
   - 既存 `UnitKernel.q2_act` を直接消費し、`semanticAct_q2` と
     `semanticAct_preservesQ2` を証明した。
   - `Equiv.lean` と `RealBridge.lean` の完了済み future TODO を更新した。
3. 結論:
   - 非負区間世界から実数回転作用まで、source subtraction なしで接続した。
   - subtraction は意味論輸送後の既知の `Real` 構造にだけ現れる。
4. 境界:
   - source-level `Vec.star` と `KernelFamily` は ring を要求するため、
     signed DkReal 層まで保留する。
   - order reflection も独立した重い課題として維持する。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 05:27 JST (Exact order four)

1. 実施:
   - semantic core zero から beam one を導く補題を追加した。
   - core zero から order dividing four、および order dividing one,
     two, three の否定を個別に証明した。
   - `SemanticExactKernelOrderFour` を定義した。
   - exact order four と semantic core zero の同値を証明した。
2. 結論:
   - semantic coordinates `(0,1)` は候補ではなく、exact order four と
     確定した。
   - 逆に exact order four の transported first-quadrant kernel は
     `(0,1)` に限られる。
3. 設計上の意味:
   - 元 kernel は第一象限にあるが、中間 power は第一象限を出られる。
   - source 側へ積を押し込まず Real 側だけで power を扱う境界が必要である。
4. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 05:15 JST (Order dividing four classification)

1. 実施:
   - 四乗 kernel の core / beam 座標多項式を API 化した。
   - order dividing four と `semantic core = 1 or 0` の同値を証明した。
2. 証明:
   - 四乗 core 方程式と unit-square の二乗から `C^2*S^2 = 0` を得た。
   - `S = 0` 側は `C = 1`、`C = 0` 側は非負性から `S = 1` となる。
3. 結論:
   - order dividing one, two, three は identity のみだった。
   - order dividing four では初めて非 identity の `(0,1)` 分岐が残る。
   - これは transported first quadrant 内の exact order-four 候補である。
4. 境界:
   - 90 度という角度解釈は使用せず、有限積の座標多項式だけで分類した。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 05:02 JST (Order dividing three classification)

1. 実施:
   - `semanticKernelFiniteOrder_three_iff_identity` を追加した。
   - order dividing three を semantic core coordinate one とも同値にした。
2. 証明:
   - 三乗 beam 方程式を `S * (3*C^2 - S^2) = 0` と因数分解した。
   - `S = 0` 分岐は unit-square と core 非負性から `C = 1`。
   - 他方は `C^2 = 1/4`, `S^2 = 3/4`, `C = 1/2` となり、三乗 core
     方程式と矛盾する。
3. 結論:
   - transported first-quadrant kernel では、order dividing one, two,
     three のいずれも identity に潰れる。
   - exact order three の非自明 kernel は存在しない。
4. 境界:
   - 平方根、角度、連続性、signed source は使用していない。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:51 JST (Polynomial coordinates for powers two and three)

1. 方針:
   - order 3 の分類へ直接進む前に、低冪 kernel の座標式を公開 API として
     分離する。
2. 実施:
   - 二乗の core を `C^2 - S^2`、beam を `2*C*S` と証明した。
   - 三乗の core を `C^3 - 3*C*S^2`、beam を
     `3*C^2*S - S^3` と証明した。
   - order dividing two の分類を二乗 core API を利用する形へ整理した。
3. 意味:
   - これらは double-angle / triple-angle theorem ではなく、有限回の
     `Vec.star` 展開から得られる多項式恒等式である。
   - order dividing three の分類に必要な座標入力が揃った。
4. 境界:
   - source 側の積、角度、連続性は導入していない。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:42 JST (Low-order classification: orders one and two)

1. 修正:
   - semantic bridge 全体は noncomputable 文脈にあることを明記し、前節の
     `noncomputable` 不要という表現を限定した。
2. 実施:
   - kernel power one が transported kernel 自身であることを証明した。
   - order dividing one を identity および core coordinate one と分類した。
   - order dividing two も identity および core coordinate one と分類した。
3. 数学的理由:
   - 一般の Real unit kernel では `(-1, 0)` も二乗して中立核になる。
   - 今回は DkNNRealQ からの座標別 transport により core と beam がともに
     非負なので、この候補は排除される。
4. 結論:
   - transported first-quadrant kernel に非自明な order two は存在しない。
   - 証明は unit-square 恒等式と二乗積の core 座標だけで閉じ、角度や
     連続性を使用しない。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:09 JST (Minimal periods and finite-order divisibility)

1. 注意点:
   - `SemanticPeriodic r z n` の `n` は正とも最小とも限らず、角度周期でも
     ないことを docstring に明記した。
2. 実施:
   - finite action order の倍数伝播を証明した。
   - Mathlib `minimalPeriod` を包む `semanticMinimalPeriod` を追加した。
   - periodicity と minimal period divisibility の同値を公開した。
   - 任意の finite action order が全点の minimal period で割り切れることを
     証明した。
   - 正周期が存在すれば minimal period が正であることを証明した。
3. 規約:
   - periodic point の minimal period は最小正周期。
   - 非周期点では Mathlib 規約により minimal period は zero。
4. 結論:
   - orbit return、period divisibility、finite action order が Mathlib の
     標準周期 API 上で統一された。
5. 次の候補:
   - fixed point / finite-order action の分類。
   - source-level family は signed DkReal 層まで保留。
6. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:23 JST (Fixed-point classification without angles)

1. 目的:
   - transported action の非零 fixed point を座標的に分類する。
2. 実施:
   - `SemanticIdentityKernel` を real neutral kernel との等式として定義した。
   - semantic core が one なら `C^2 + S^2 = 1` から beam zero を証明した。
   - identity-kernel 条件と semantic core one の同値を証明した。
   - identity kernel が全実数 vector を固定することを証明した。
   - core が one でない kernel の fixed point 連立方程式から、行列式
     `(C - 1)^2 + S^2` を用いて両座標 zero を導いた。
   - 非 identity kernel の fixed point が原点と同値であることを証明した。
3. 結論:
   - identity kernel なら全点 fixed。
   - nonidentity transported kernel なら fixed point は原点のみ。
4. 使用していないもの:
   - angle、continuity、signed DkReal source。
5. 次の候補:
   - 明示的 semantic coordinate 条件下での finite-order classification。
6. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:17 JST (Fixed points and positive finite action order)

1. 方針:
   - fixed point は Mathlib `Function.IsFixedPt` を用いる。
   - zero iterate でも成立する弱い finite order と、正の witness を持つ版を
     分離する。
2. 実施:
   - `SemanticFixed` を追加した。
   - fixed point、period one、minimal period one の同値を公開した。
   - fixed point が任意 period の周期点になることを証明した。
   - 原点が全 transported action の fixed point であることを証明した。
   - `SemanticPositiveFiniteOrder` を追加した。
   - 正有限位数の正倍数伝播と、全点の minimal period positivity を証明した。
3. 注意:
   - positive finite order の `n` は正だが、作用の最小正位数とは限らない。
4. 結論:
   - fixed / periodic / minimal-period / finite-order の基本関係が標準 API
     上で揃った。
5. 次の候補:
   - 明示的 kernel 条件下での非零 fixed point の座標分類。
   - source-level family は signed DkReal 層まで保留。
6. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 03:50 JST (Periodic points and finite action order)

1. 方針:
   - 独自の周期点概念を作らず、Mathlib `Function.IsPeriodicPt` を用いる。
2. 実施:
   - `SemanticPeriodic` と orbit-return 同値を追加した。
   - `SemanticLevelPeriodic` を定義し、underlying plane point の周期性との
     同値を証明した。
   - `SemanticFiniteOrder` を action iterate が恒等写像となる性質として
     定義した。
   - finite order と全 plane point の周期性が同値であることを証明した。
   - finite order から任意 level-set point の周期性を導いた。
   - 周期が倍数へ伝播することを Mathlib の `trans_dvd` で公開した。
3. 結論:
   - 保存 orbit から periodic dynamics まで標準 Mathlib API に接続した。
   - 角度、連続性、signed source は依然として不要である。
4. 次の候補:
   - minimal period と finite-order divisibility。
   - source-level family は signed DkReal 層まで保留。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 02:30 JST (Bundled automorphisms and finite orbits)

1. 目的:
   - transported action の可逆性を bundled equivalence として公開する。
   - finite iterate と orbit の保存量を定理化する。
2. 実施:
   - `semanticActEquiv` と `semanticActLevelEquiv` を追加した。
   - plane / level-set action の全 finite iterate が bijective と証明した。
   - `semanticAct_iterate_q2` を帰納法で証明した。
   - `semanticOrbit` と `semanticLevelOrbit` を定義した。
   - orbit 全体で `q2` が初期値に等しいことを証明した。
   - level-set orbit の underlying vector が plane orbit と一致することを
     証明した。
3. 結論:
   - DkNNRealQ 由来 kernel は Real の各 `q2` level set 上に離散力学系を
     生成する。
   - signed source、角度復元、連続性を導入せず finite orbit まで到達した。
4. 次の候補:
   - periodic point / finite-order kernel の一般定理。
   - source-level family は signed DkReal 層まで保留。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 00:59 JST (Inverse kernels and level-set automorphisms)

1. 方針:
   - inverse は source に構成せず、transport 後の Real unit kernel の共役で
     与える。
2. 実施:
   - `semanticInverseKernel` と `semanticInverseAct` を追加した。
   - 左右の inverse action law を既存 `star_conj` / `conj_star` から証明した。
   - `semanticAct_bijective` を証明した。
   - level set 側にも inverse action を降ろし、
     `semanticActLevel_bijective` を証明した。
3. 結論:
   - DkNNRealQ 由来 kernel は Real 平面の `q2` 保存全単射を生成する。
   - 任意の実数 `q2` level set 上でも全単射となる。
4. 境界:
   - 共役 inverse は一般に beam 座標が負となるため、第一象限の source
     kernel へ戻るとは主張しない。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 00:49 JST (Real-side composition and level-set action)

1. 方針:
   - source-level kernel product は導入せず、二つの kernel を個別に Real へ
     輸送した後でのみ積を取る。
2. 実施:
   - `semanticKernelProduct` を real unit-kernel product として定義した。
   - `semanticAct_comp` で successive action と product action を接続した。
   - `semanticActLevel` を追加し、任意の実数 `q2` level set 上の自己写像を
     構成した。
   - `semanticActLevel_comp` で level-set action の合成を証明した。
   - `DkNNRealQ.lean` の semantic bridge TODO を実装済み状態へ更新した。
3. 結論:
   - DkNNRealQ 由来の kernel は、Real 上で合成可能な保存作用を生成する。
   - source semiring に subtraction や kernel product を要求しない。
4. 次の境界:
   - source-level `Vec.star` / `KernelFamily` は signed DkReal 待ち。
   - それまでは第一象限 kernel の Real 幾何 consumer を進められる。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。

### 2026/06/22 04:30 JST (Real-side kernel powers and finite-order equivalence)

1. 方針:
   - source 側の積は定義せず、transport 後の `UnitKernel Real` だけで
     kernel の反復積を構成する。
2. 実施:
   - `semanticKernelPower` を real-side の n-fold product として追加した。
   - `semanticKernelPower_act` で、その作用が `semanticAct` の n 回反復と
     一致することを証明した。
   - 単位ベクトルへの作用から kernel を復元する忠実性
     `unitKernel_eq_one_of_act_eq_id` を証明した。
   - `semanticKernelFiniteOrder_iff` により、反復積が中立核になる条件と
     finite action order が同値であることを証明した。
3. 結論:
   - finite order は、作用側と kernel 積側のどちらからでも同じ条件として
     扱える。
   - signed source、角度、連続性は不要。
   - semantic bridge 自体は noncomputable 文脈だが、この反復積の段階では
     新たな解析的 noncomputable 要素を増やしていない。
4. 境界:
   - この積は Real 側だけに存在し、非負 source の積を主張しない。
5. 検証:
   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
