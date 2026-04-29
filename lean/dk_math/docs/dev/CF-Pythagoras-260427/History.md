# History

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89

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

---

### 日時: 2026/04/27 15:01 JST (ピタゴラスの定理の Cosmic Formula 形式化)

1. 目的:
   - ピタゴラスの定理を宇宙式 (Cosmic Formula) の差分構造として形式化する
   - 研究ノート `69e72cfc_2026-0421-075513_ピタゴラスの差分解釈+126404-367.md` の内容を Lean で実装する

2. 実施:
   - 新規ファイル `DkMath/CosmicFormula/CosmicFormulaPythagoras.lean` を作成
   - 以下の定義と定理を実装:
     - `IsPythagoreanTriple`: ピタゴラス三つ組の述語
     - `PythagoreanDifference₁`, `PythagoreanDifference₂`: 差分構造 `c² - a²`, `c² - b²`
     - `PythagoreanCosmicForm`: 宇宙式的表現 `2au + u²`
     - `pythagoras_as_difference`: 古典的ピタゴラスと差分形式の等価性
     - `pythagoras_cosmic_form`: `c = a + u` のとき `(a+u)² - a² = 2au + u²`
     - `pythagoras_cosmic_unit_relation`: 単位宇宙式との関係
     - `pythagoras_gap_beam_interpretation`: Gap/Beam 解釈
     - 整数版ピタゴラス三つ組の定義と古典的な例 (3,4,5), (5,12,13), (8,15,17)
     - `PythagoreanParametrization`: 古典的パラメトリゼーション `(m²-n², 2mn, m²+n²)`
     - `parametrization_embeds_cosmic_structure`: パラメトリゼーションが差分構造を内包することの証明

3. 結論:
   - ピタゴラスの定理を宇宙式の差分構造として完全に形式化できた
   - 以下の重要な洞察を定理化:
     - ピタゴラスの定理は差分生成関係 `c² - a² = b²`, `c² - b² = a²` として表現できる
     - `c = a + u` のとき、短辺平方は `b² = 2au + u²` という「Beam 構造」で生成される
     - 古典的なパラメトリゼーション `a = m² - n²` 自体が既に差分構造（平方差）である
   - 研究ノートで議論された「各辺の平方が、他の二辺により決まる必然的差分量である」という解釈を厳密に証明

4. 検証:
   - `lake build` でビルド成功を確認
   - 以下のエラーを修正:
     - `pythagoras_cosmic_unit_connection`: 宇宙式 `u²` と Pythagorean form `2au + u²` は異なる差分構造であることを明示する定理に変更
     - `int_pythagoras_to_real`: 整数から実数へのキャスト証明を `norm_cast` で簡潔化
     - 未使用変数警告を解消
   - 古典的ピタゴラス三つ組 (3,4,5), (5,12,13), (8,15,17) の example で正当性を確認

5. 失敗事例:
   - 初回実装で `PythagoreanCosmicForm a u = cosmic_formula_unit a u` という誤った等式を立てた
     - 原因: 宇宙式 `(x+u)² - x(x+2u) = u²` と Pythagorean form `b² = 2au + u²` の構造的違いを見落とした
     - 修正: 両者は異なる差分構造であり、Pythagorean form は「Beam」、cosmic formula は恒等的に `u²` へ落ちることを明確化

6. 次の課題:
   - より高次元への拡張 (3D ピタゴラス定理など)
   - ピタゴラス三つ組の完全分類と宇宙式的解釈
   - Fermat の最終定理 (FLT) との関連: `a⁴ + b⁴ = c⁴` が解を持たないことと、4次宇宙式構造の関係
   - 研究ノートで示唆された「辺 = u²」解釈 (4次世界) への拡張可能性の探求

---

### 日時: 2026/04/27 15:26 JST (Cosmic Link Condition と構造体の実装)

1. 目的:
   - レビュー (review-001.md) の指示に従い、宇宙式リンク条件と CosmicPythagoreanTriple 構造体を実装する
   - `a = α u₁, b = β u₂, c = γ u₃` という形式でピタゴラス三つ組を表現する枠組みを構築
   - 具体例 (3,4,5), (5,12,13), (8,15,17) を実装し、宇宙式的解釈を検証

2. 実施:
   - **CosmicFormulaPythagoras.lean への追加**:
     - `CosmicLinkCondition α β γ u₁ u₂ u₃`: 宇宙式リンク条件 `α² u₁² + β² u₂² = γ² u₃²`
     - `CosmicLinkConditionInt`: 整数版リンク条件
     - `cosmic_link_to_pythagoras`: リンク条件からピタゴラス三つ組への変換定理
     - `pythagoras_to_cosmic_link`: ピタゴラス三つ組からリンク条件への逆変換
     - `cosmic_link_unit_one`: 単位代表がすべて 1 の場合の簡約形
     - **`CosmicPythagoreanTriple` 構造体**: 6 つのフィールド (α, β, γ, u₁, u₂, u₃) を持つ bundled 構造
     - `a`, `b`, `c`: 三辺を計算する定義
     - `IsLinked`: 構造体がリンク条件を満たすかの述語
     - `linked_satisfies_pythagoras`: リンクされた三つ組はピタゴラスの定理を満たす
     - `standard`: 単位代表がすべて 1 の標準表現
     - `standard_linked_iff`: 標準表現がリンクされる条件

   - **CosmicFormulaPythagorasExamples.lean の新規作成**:
     - 古典的ピタゴラス三つ組の検証:
       - (3,4,5), (5,12,13), (8,15,17) のリンク条件確認
       - 各三つ組を `CosmicPythagoreanTriple` として定義
     - スケール表現: (6,8,10) を `α=3, β=4, γ=5` と `u₁=u₂=u₃=2` で表現
     - 代替単位表現: 同じ三角形を異なる (α, u) の組み合わせで表現
     - パラメトリゼーション例: (m,n) から生成される三つ組の検証
     - 宇宙式差分構造の具体例: `c² - a² = b²` の数値確認
     - Cosmic Form `b² = 2au + u²` の具体例
     - Gap/Beam 因数分解 `b² = u × (2a + u)` の具体例

3. 結論:
   - **宇宙式ピタゴラス橋の第一基礎 API が完成**:
     - `a = α u₁, b = β u₂, c = γ u₃` という形式が Lean 上で実体化
     - リンク条件 `α² u₁² + β² u₂² = γ² u₃²` ↔ `a² + b² = c²` の等価性を証明
     - 構造体による bundled 化で、研究ノートの言葉に近い形式を実現
   - **研究ノートの主張を厳密に検証**:
     - 最小例 (3,4,5) を `u₁=u₂=u₃=1, α=3, β=4, γ=5` として実装・検証
     - 同じ幾何学的三角形を複数の宇宙式表現で記述できることを示した
     - 境界差生成式 `c² - a² = 2a(c-a) + (c-a)²` が具体例で機能することを確認

4. 検証:
   - `lake build` でビルド成功を確認
   - 以下のエラーを修正:
     - `cosmic_link_to_pythagoras`: `α² * u₁²` と `(α * u₁)²` の型不一致を `calc` と `ring` で解決
     - `linked_satisfies_pythagoras`: 同様の型不一致を `calc` で明示的に証明
     - `standard_linked_iff`: `simp only [one_pow, mul_one]` で簡約
     - Examples ファイル: `decide` の代わりに `norm_num` を使用（Decidable インスタンスが不足）
   - 全ての具体例 (3,4,5), (5,12,13), (8,15,17), (6,8,10) が正しく検証された

5. 失敗事例:
   - 初回実装で `mul_pow` の方向を誤解し、`simp only [mul_pow]` では型が一致しなかった
     - 原因: `(a * b)^n = a^n * b^n` と `a^n * b^n = (a * b)^n` の区別を曖昧にした
     - 修正: `calc` を使って `ring` で明示的に式変形を記述
   - `decide` タクティックが使えない場面があった
     - 原因: `IsLinked` や `CosmicLinkConditionInt` に Decidable インスタンスがない
     - 修正: `norm_num` や展開後の計算で証明

6. 次の課題:
   - 一般ピタゴラス三つ組のパラメトリゼーション `(m²-n², 2mn, m²+n²)` を宇宙式リンクで分析
   - 宇宙式単位系 `u₁, u₂, u₃` の選択自由度と幾何学的意味の関係を定理化
   - `(X+u)² - X² = 2Xu + u²` や `(x+u)² - x(x+2u) = u²` との橋渡し定理の追加
   - より高次元 (3D ピタゴラス定理) への拡張
   - Fermat の最終定理への応用可能性の探求

---

### 日時: 2026/04/27 16:27 JST (一般化と理論部品化完了)

1. 目的:
   - レビュー (review-002.md) の指示に従い、具体例から全称定理への昇格を実施
   - `CosmicLinkCondition` と `IsPythagoreanTriple` を CommRing 一般化
   - Gap/Beam の一般補題化
   - `PythagoreanParametrization` の全称定理化
   - 表現自由度 (Gauge Symmetry) の形式化

2. 実施:
   - **型の一般化**:
     - `IsPythagoreanTripleOver {R : Type*} [CommRing R]`: 一般環版のピタゴラス三つ組述語
     - `IsPythagoreanTriple` は実数版の abbrev として維持（互換性）
     - `CosmicLinkCondition {R : Type*} [CommRing R]`: 一般環版の宇宙式リンク条件
     - `CosmicLinkConditionReal`, `CosmicLinkConditionInt` を abbrev で提供

   - **Gap/Beam の一般化**:
     - `boundaryGap {R : Type*} [Ring R]`: 境界ギャップの定義
     - `pythagoreanBeam {R : Type*} [Ring R]`: ピタゴラスビームの定義
     - `sq_sub_sq_gap_beam`: `c² - a² = Gap × Beam` の一般定理
     - `sq_diff_of_gap`: `(a+u)² - a² = u × (2a + u)` の一般定理
     - `gap_beam_factorization`: Gap-Beam 分解の等価性

   - **パラメトリゼーションの全称定理化**:
     - `parametrization_cosmic_link`: (m,n) パラメトリゼーションが常にリンク条件を満たす全称定理
     - 定義順序の修正: `CosmicLinkCondition` 定義の後に配置

   - **表現自由度 (Gauge Symmetry)**:
     - `observed_edge_rescale`: 観測辺のリスケール保存
     - `cosmic_link_rescale`: リンク条件のリスケール保存（Field 上で証明完了）
     - `EquivRepresentation`: 同じ辺を生成する表現の等価性述語

3. 結論:
   - **宇宙式ピタゴラス橋が再利用可能な理論部品に昇格**:
     - ℤ, ℚ, ℝ, 多項式環など、任意の可換環で使用可能
     - 具体例が一般定理に裏付けられた形に
     - リンク条件の表現自由度（ゲージ対称性）を定理化
   - **研究上の意義**:
     - 同じ幾何学的三角形を複数の宇宙式表現で記述できることを証明
     - `(α, u)` の分解の非一意性を形式化
     - より高次元や他の環への拡張準備が整った

4. 検証:
   - `lake build` でビルド成功を確認
   - 以下の技術的問題を解決:
     - 定義順序の問題: `parametrization_cosmic_link` を `CosmicLinkCondition` 定義の後に移動
     - implicit parameter 解決: `@CosmicLinkCondition` 記法で明示的に型を指定
     - `field_simp` の挙動理解: 分数を消去して元の条件と同じ形にする
     - Examples ファイルで `CosmicLinkCondition` の展開を追加
   - 全ての定理が証明完了（sorry なし）
   - VSCode lint エラーは拡張機能のキャッシュ問題と判明（Issue-003.md に記録）

5. 失敗事例:
   - `cosmic_link_rescale` の証明で `field_simp` と `ring` の相互作用に苦戦
     - 原因: `field_simp` が分数を消去した後の式の形を正しく理解していなかった
     - 修正: `unfold` → `field_simp` → `exact h` のシンプルな流れで証明完了
   - `parametrization_cosmic_link` が "Unknown identifier" エラー
     - 原因: `CosmicLinkCondition` 定義の前に配置していた
     - 修正: 定義の後に移動することで解決

6. 次の課題:
   - 高次元への拡張: 3D ピタゴラス定理 `a² + b² + c² = d²` を宇宙式で表現
   - 他の環への応用: `ZMod p` 上でのリンク条件の性質解析
   - Fermat の最終定理との関連: `aⁿ + bⁿ = cⁿ` (n≥3) が宇宙式リンクで満たされない構造的理由の探求
   - 宇宙式単位系の幾何学的意味の解明: 単位代表の選択と幾何学的性質の対応関係

---

### 日時: 2026/04/27 21:36 JST (Representation Gauge and Gap/Beam API 固定完了)

1. 目的:
   - レビュー (review-003.md) の指示に従い、表現ゲージ自由度と Gap/Beam API を完成させる
   - `EquivRepresentation` を同値関係に昇格
   - 各辺別スケール操作 `rescaleEach` の実装
   - Gap/Beam を構造体 API に接続
   - CF-Pythagoras の第一章を完成させる

2. 実施:
   - **同値関係の形式化**:
     - `equivRepresentation_refl`: 反射律
     - `equivRepresentation_symm`: 対称律
     - `equivRepresentation_trans`: 推移律
     - これにより `EquivRepresentation` が真の同値関係として使用可能に

   - **三単位宇宙ゲージ自由度の完全形式化**:
     - `cosmic_link_rescale_each`: 各辺別スケール `(k₁, k₂, k₃)` でのリンク条件保存
     - 共通スケール `k` ではなく、各単位系独立のスケール `(k₁, k₂, k₃)` を許容
     - これは `(K×)³` 作用として、三単位宇宙の本質的な自由度を表現

   - **rescaleEach 操作**:
     - `rescaleEach`: 各辺を独立にスケールする構造体変換操作
     - `rescaleEach_equiv`: スケール後も同じ辺を表すことの証明
     - `rescaleEach_isLinked`: リンク性の保存証明
     - bundled 化により、ゲージ変換が構造体レベルで操作可能に

   - **Gap/Beam の構造体 API 化**:
     - `gapA (T)`: 構造体 T に対する Gap `c - a`
     - `beamA (T)`: 構造体 T に対する Beam `c + a`
     - `b_sq_eq_gapA_mul_beamA`: **短辺平方 = Gap × Beam** の中心定理
     - ピタゴラスの定理が完全に「差分生成構造」として表現された

3. 結論:
   - **宇宙式ピタゴラス橋の第一章が完成**:
     - リンク条件 `α² u₁² + β² u₂² = γ² u₃²`
     - ゲージ自由度 `(K×)³` 作用
     - Gap/Beam 生成 `b² = (c-a)(c+a)`
     - 三本柱が揃い、再利用可能な理論 API として完成

   - **研究上の意義**:
     - ピタゴラスの定理が「完成形 a²+b²=c²」ではなく「生成構造」として扱える
     - 単位宇宙の選択自由度が (K×)³ として明示化
     - Gap × Beam 因数分解が定理として証明され、宇宙式語彙と接続
     - より高次元（3D ピタゴラス）や FLT への拡張準備が完了

4. 検証:
   - `lake build` でビルド成功を確認
   - 以下の技術的問題を解決:
     - `b_sq_eq_gapA_mul_beamA` の証明で `linarith` が CommRing では動作しない
       - 原因: 一般可換環では線形算術の公理が完全には適用されない
       - 修正: `sub_eq_of_eq_add'` を使って手動で式変形
     - `rescaleEach_equiv` で `field_simp` を各辺に適用
     - コメント追加: `cosmic_link_rescale` に "After clearing denominators" の説明
   - 全ての定理が証明完了（sorry なし）
   - warning なし

5. 失敗事例:
   - `b_sq_eq_gapA_mul_beamA` で最初 `linarith` を使おうとして失敗
     - 原因: CommRing 上では `linarith` が `a + b = c` から `c - a = b` を導けない
     - 修正: `sub_eq_of_eq_add'` 補題を明示的に使用
   - 型の向きミス: `sub_eq_of_eq_add'` の結果に `.symm` が必要
     - 修正: 型を確認して `.symm` を追加

6. 次の課題:
   - 3D ピタゴラス定理 `a² + b² + c² = d²` への拡張
   - gapB, beamB (b と c の差分) の定義と対称性定理
   - 宇宙式パラメトリゼーション `(m²-n², 2mn, m²+n²)` を rescaleEach で分析
   - ZMod p 上での宇宙式リンク条件の性質探求
   - FLT (n≥3) が宇宙式リンクで満たされない構造的証明への挑戦

## CF-Pythagoras 第一章完成宣言

この時点で、宇宙式ピタゴラス橋の基礎理論は完成した。

**完成した API**:

- 型一般化 (CommRing/Field)
- リンク条件と Pythagorean 述語の橋
- 表現同値関係 (refl/symm/trans)
- ゲージ自由度 `(K×)³`
- Gap/Beam 因数分解

次のステップは、この基礎の上に以下を構築することになる:

1. 高次元化 (3D, nD)
2. パラメトリゼーション理論の深化
3. FLT への応用可能性の探求
4. 宇宙式的視点からの整数論的性質の解明

---

### 日時: 2026/04/27 22:45 JST (対称 Gap/Beam API と Power Gap/Beam 骨格の実装)

1. 目的:
   - review-004.md の提案に従い、Chapter 2 へ進む前段として対称的な Gap/Beam API を完成させる
   - 既存の `gapA` / `beamA` に対し、`b` 側基準の対称 API を追加する
   - rewriting 用の逆向き補題と、一般関数 `boundaryGap` / `pythagoreanBeam` への橋を用意する
   - 高次差冪へ拡張するための `PowerGapBeam.lean` を新設する

2. 実施:
   - **対称 Gap/Beam API の追加**:
     - `gapB T = T.c - T.b`
     - `beamB T = T.c + T.b`
     - `a_sq_eq_gapB_mul_beamB`: linked triple に対して `a² = (c-b)(c+b)` を証明

   - **rewriting 用の逆向き補題を追加**:
     - `gapA_mul_beamA_eq_b_sq`: `gapA T * beamA T = T.b²`
     - `gapB_mul_beamB_eq_a_sq`: `gapB T * beamB T = T.a²`

   - **一般関数との橋を追加**:
     - `gapA_eq_boundaryGap`
     - `beamA_eq_pythagoreanBeam`
     - `gapB_eq_boundaryGap`
     - `beamB_eq_pythagoreanBeam`

   - **Examples の拡充**:
     - `triple_3_4_5_rat`: ℚ 上の (3,4,5) triple を追加
     - `rescaleEach triple_3_4_5_rat 2 3 5` が同じ辺を表すことを確認
     - rescale 後も `IsLinked` が保存されることを確認
     - `(1/2, 1/2, 1/2)` による rescale 例を追加

   - **高次 Gap/Beam の骨格実装**:
     - 新規ファイル `DkMath/CosmicFormula/PowerGapBeam.lean` を作成
     - `powerGap x z := z - x`
     - `powerBeam d x z := ∑ i in Finset.range d, z^(d-1-i) * x^i`
     - `powerBeam_zero`, `powerBeam_one`, `powerBeam_two` を証明
     - `pow_two_sub_eq_pythagorean`: d=2 の通常因数分解 `z² - x² = (z-x)(z+x)` を証明
     - `powerBeam_two_eq_pythagorean_beam`: d=2 で高次 Beam が Pythagorean Beam と一致する補題を追加
     - `DkMath/CosmicFormula.lean` から `PowerGapBeam` を import

3. 結論:
   - **二次 Gap/Beam の左右対称 API が完成**:
     - `b² = (c-a)(c+a)` と `a² = (c-b)(c+b)` の両側が構造体 API として利用可能になった
     - rewrite 方向の補題により、後続証明で Gap/Beam 積と辺平方を相互に使いやすくなった
     - 一般補題 `boundaryGap` / `pythagoreanBeam` と構造体 API の接続が明示された

   - **高次差冪への橋が始まった**:
     - 二次の Beam `z+x` を、高次 Beam `∑ z^(d-1-i)x^i` に一般化する入口ができた
     - FLT 型の式 `x^d + y^d = z^d` を `Gap × Beam_d` 構造として読む準備が整った

4. 検証:
   - `lake build` でビルド成功を確認
   - `PowerGapBeam.lean` に計画的な `sorry` が 1 個残っている:
     - `pow_sub_pow_eq_gap_mul_powerBeam`
     - 既存の GN / diffPowSum 系補題を使って後続サイクルで証明予定
   - 対称 Gap/Beam API、逆向き補題、bridge 補題、Examples の rescale 例は証明完了

5. 失敗事例:
   - 高次主定理 `z^d - x^d = powerGap x z * powerBeam d x z` は、このサイクルでは骨格定義に留めた
     - 理由: Nat 減算を含む `powerBeam` の和の扱いを、既存の GN / diffPowSum 補題とどう接続するか確認が必要
     - 対応: `sorry` を明示的な TODO として残し、周辺の d=0,1,2 補題と二次因数分解を先に固定

6. 次の課題:
   - `pow_sub_pow_eq_gap_mul_powerBeam` の `sorry` を解消する
   - `powerBeam 2 x z = pythagoreanBeam x z` の bridge を既存 API 名に完全に接続する
   - `CosmicLinkConditionD` を定義し、高次リンク条件 `α^d u₁^d + β^d u₂^d = γ^d u₃^d` を導入する
   - FLT 型仮定 `x^d + y^d = z^d` から `y^d = powerGap x z * powerBeam d x z` を得る薄い bridge 補題を追加する
   - 高次 Beam と既存 GN / Tail / DiffPow 系 API の接続方針を決める

---

### 日時: 2026/04/28 16:38 JST (Power Gap/Beam 主定理の sorry 解消)

1. 目的:
   - review-005.md の S2-A 方針に従い、`PowerGapBeam.lean` に残っていた主定理の `sorry` を解消する
   - 高次差冪因数分解 `z^d - x^d = (z-x) * powerBeam d x z` を既存 API と接続して証明する

2. 実施:
   - 既存の差冪 API を確認し、`DkMath.Algebra.DiffPow` に以下が既に実装済みであることを確認:
     - `diffPowSum a b d = ∑ i ∈ range d, a^(d-1-i) * b^i`
     - `pow_sub_pow_factor`: `a^d - b^d = (a-b) * diffPowSum a b d`
   - `PowerGapBeam.lean` に `import DkMath.Algebra.DiffPow` を追加
   - `pow_sub_pow_eq_gap_mul_powerBeam` を `pow_sub_pow_factor (a := z) (b := x)` の wrapper として証明
   - `powerGap`, `powerBeam`, `DkMath.Algebra.DiffPow.diffPowSum` を `simpa` で展開し、独自定義と既存商の一致を利用

3. 結論:
   - `pow_sub_pow_eq_gap_mul_powerBeam` の `sorry` を解消した
   - `PowerGapBeam` は独自に帰納法を再実装せず、既存の `DiffPow` 基盤を再利用する薄い高次 Gap/Beam フロントエンドになった
   - Chapter 2 の入口である高次差冪の主因数分解が Lean 上で証明済みになった

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeam` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - `grep -n "sorry" lean/dk_math/DkMath/CosmicFormula/PowerGapBeam.lean` で対象ファイル内に `sorry` が残っていないことを確認

5. 失敗事例:
   - 直接帰納法による証明は採用しなかった
     - 理由: `d - 1 - i` を含む和の添字操作を再証明する必要があり、既存 `DiffPow` の証明と重複するため
     - 対応: `DiffPow.pow_sub_pow_factor` を正準補題として再利用し、`PowerGapBeam` 側は概念名の wrapper に徹した

6. 次の課題:
   - `PowerGapBeam` と Pythagorean API の bridge を整理し、`powerBeam 2 x z = pythagoreanBeam x z` を既存 API 名で明示する
   - `CosmicLinkConditionD` と `cosmicLinkConditionD_two_iff` を追加する
   - FLT 型仮定 `x^d + y^d = z^d` から `y^d = powerGap x z * powerBeam d x z` を得る bridge 補題を実装する
   - 必要に応じて `PowerGapBeam.lean` の依存を純代数層と Pythagoras bridge 層に分離する

---

### 日時: 2026/04/28 16:50 JST (S2-B: Higher Cosmic Link and FLT Gap/Beam Bridge)

1. 目的:
   - review-006.md の S2-B 方針に従い、高次宇宙リンク条件と FLT Gap/Beam bridge を実装する
   - `CosmicLinkCondition` の d 次版を導入し、d=2 で既存条件へ戻ることを確認する
   - 高次リンク条件から観測辺の高次冪方程式を導く
   - FLT 型仮定 `x^d + y^d = z^d` を Power Gap/Beam 積として観測する補題を追加する

2. 実施:
   - **高次宇宙リンク条件の追加** (`CosmicFormulaPythagoras.lean`):
     - `CosmicLinkConditionD d α β γ u₁ u₂ u₃`
     - 定義: `α^d * u₁^d + β^d * u₂^d = γ^d * u₃^d`
   - **d=2 での既存条件との接続**:
     - `cosmicLinkConditionD_two_iff`
     - `CosmicLinkConditionD 2 ... ↔ CosmicLinkCondition ...` を `rfl` で証明
   - **高次リンクから高次冪方程式への橋**:
     - `cosmic_linkD_to_power_equation`
     - `CosmicLinkConditionD d α β γ u₁ u₂ u₃` から `(α*u₁)^d + (β*u₂)^d = (γ*u₃)^d` を導出
     - `mul_pow` によりリンク条件と観測辺の冪を接続
   - **FLT Gap/Beam bridge の追加** (`PowerGapBeam.lean`):
     - `flt_eq_forces_powerGapBeam`
     - `x^d + y^d = z^d` から `y^d = powerGap x z * powerBeam d x z` を導出
     - `flt_eq_forces_powerGapBeam_symm`
     - 対称に `x^d = powerGap y z * powerBeam d y z` を導出

3. 結論:
   - Chapter 2 の高次宇宙リンク層が立ち上がった
   - d=2 の Pythagorean link は `CosmicLinkConditionD` の特殊例として位置づけられた
   - FLT 型方程式を、左右どちらの辺についても `Gap × Beam_d` の生成構造として扱えるようになった

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaPythagoras` 成功
   - `lake build DkMath.CosmicFormula.PowerGapBeam` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - `flt_eq_forces_powerGapBeam` では一般 `CommRing` 上の減法変形として `sub_eq_of_eq_add'` を使い、線形算術に依存しない形にした

6. 次の課題:
   - `powerBeam 2 x z = pythagoreanBeam x z` を既存 Pythagorean API と明示的に接続する bridge を整理する
   - S2-C として `gcd(powerGap, powerBeam_d) ∣ d` 型の制御、または既存 `GcdDiffPow` との接続へ進む
   - `PowerGapBeam` の純代数層と Pythagoras bridge 層を分離するか検討する

---

### 日時: 2026/04/28 17:05 JST (S2-C: Power Gap/Beam gcd control bridge)

1. 目的:
   - review-007.md の S2-C 方針に従い、Power Gap/Beam と既存 `GcdDiffPow` の gcd 制御を接続する
   - `gcd(powerGap, powerBeam_d) ∣ d` 型の wrapper を用意する
   - FLT bridge の次段で使う「d を割らない素数は Gap と Beam を同時に割れない」という形を追加する

2. 実施:
   - 新規ファイル `DkMath/CosmicFormula/PowerGapBeamGcd.lean` を作成
   - `PowerGapBeam.lean` 本体には数論依存を入れず、gcd 制御を bridge ファイルへ分離
   - `DkMath.NumberTheory.GcdDiffPow.gcd_divides_d` を再利用
   - `gcd_powerGap_powerBeam_dvd_d_of_coprime_int` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z x = 1`
     - 結論: `Int.gcd (powerGap x z) (powerBeam d x z) ∣ d`
   - `prime_not_dvd_d_not_dvd_powerGap_and_powerBeam` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z x = 1`, `¬ p ∣ d`
     - 結論: `p` は `(powerGap x z).natAbs` と `(powerBeam d x z).natAbs` を同時には割れない
   - `DkMath/CosmicFormula.lean` から `PowerGapBeamGcd` を import

3. 結論:
   - Power Gap/Beam が単なる差冪恒等式から、既存 FLT 幹線の gcd 制御層へ接続された
   - primitive 条件 `gcd(z,x)=1` の下で、Gap と Beam の共通因子が次数 `d` に押し込まれる形を得た
   - FLT 型方程式を `Gap × Beam_d` と見た後、p-adic / primitive prime 議論へ進むための入口ができた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - 当初は `PowerGapBeam.lean` 本体に gcd 補題を置く選択肢もあったが、依存を重くしすぎないため新規 bridge ファイルへ分離した

6. 次の課題:
   - `flt_eq_forces_powerGapBeam` と `gcd_powerGap_powerBeam_dvd_d_of_coprime_int` を組み合わせた FLT 専用 bridge を作る
   - `p ∤ d` の primitive prime が Beam 側へ現れる場合の valuation 制御へ接続する
   - Nat 版 / ℤ 版のどちらを標準 API にするか整理する
   - `powerBeam 2 x z = pythagoreanBeam x z` の Pythagorean bridge を別ファイルで明示する

---

### 日時: 2026/04/28 17:21 JST (S2-D: FLT Power Gap/Beam Datum Bridge)

1. 目的:
   - review-008.md の S2-D 方針に従い、FLT 型方程式から得る Power Gap/Beam 積分解と gcd 制御を同時に返す wrapper を作る
   - 左右対称に、`y` 側と `x` 側の両方を観測できる形にする
   - `p ∤ d` の素数が Beam 側に現れた場合、同じ素数が Gap 側に入らないことを FLT 文脈の補題として用意する

2. 実施:
   - `PowerGapBeamGcd.lean` に FLT datum bridge セクションを追加
   - `flt_eq_forces_powerGapBeam_and_gcd` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z x = 1`, `x^d + y^d = z^d`
     - 結論: `y^d = powerGap x z * powerBeam d x z` かつ `Int.gcd (powerGap x z) (powerBeam d x z) ∣ d`
   - `flt_eq_forces_powerGapBeam_and_gcd_symm` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z y = 1`, `x^d + y^d = z^d`
     - 結論: `x^d = powerGap y z * powerBeam d y z` かつ `Int.gcd (powerGap y z) (powerBeam d y z) ∣ d`
   - `flt_beam_prime_not_dvd_gap_of_not_dvd_d` を追加:
     - `p ∤ d` かつ `p ∣ (powerBeam d x z).natAbs` なら、`p ∤ (powerGap x z).natAbs`
   - `flt_beam_prime_not_dvd_gap_of_not_dvd_d_symm` を追加:
     - 対称に `y` 側基準の Beam / Gap で同じ性質を証明

3. 結論:
   - FLT 型仮定を、Power Gap/Beam の「積分解 + gcd 制御」データとして一括取得できるようになった
   - S2-B の因数分解 bridge と S2-C の gcd bridge が、S2-D で FLT 専用 API として統合された
   - 次段の p-adic / primitive prime 議論で、Beam 側の素因子が Gap 側と分離される入口ができた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - `FLTPowerGapBeamDatum` 構造体は今回は作らず、まずは使いやすい conjunction 形式の定理として実装した
     - 理由: 現段階では後続の valuation 補題が必要とするフィールド構成が未確定であり、構造体を早く固定しすぎない方がよい

6. 次の課題:
   - S2-E として、Beam 側の素因子を `padicValNat` の積分解・冪乗付値制約へ接続する
   - `p ∤ d` かつ `p ∣ Beam` のとき、`padicValNat p (Gap * Beam)` が Beam 側から来ることを示す wrapper を検討する
   - primitive prime / valuation 上界側の既存 API と接続する
   - 必要に応じて `FLTPowerGapBeamDatum` 構造体を導入する

---

### 日時: 2026/04/28 17:31 JST (S2-E: Power Gap/Beam valuation bridge)

1. 目的:
   - review-009.md の S2-E 方針に従い、Beam 側の素因子が積全体の p-adic valuation にそのまま反映される bridge を作る
   - `p ∤ Gap` から `v_p(|Gap * Beam|) = v_p(|Beam|)` を導く一般補題を用意する
   - FLT 文脈で `p ∤ d` かつ `p ∣ Beam` のとき、S2-D の Gap 非整除補題を介して valuation 等式を得る

2. 実施:
   - `PowerGapBeamGcd.lean` に Valuation Bridge セクションを追加
   - `padicValNat_natAbs_mul_eq_right_of_not_dvd_left` を追加:
     - 仮定: `Nat.Prime p`, `¬ p ∣ gap.natAbs`
     - 結論: `padicValNat p (gap * beam).natAbs = padicValNat p beam.natAbs`
     - `Int.natAbs_mul`, `padicValNat.mul`, `padicValNat.eq_zero_of_not_dvd` を使用
     - `beam = 0` の場合も分岐して処理
   - `flt_padicValNat_product_eq_beam_of_beam_prime` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z x = 1`, `x^d + y^d = z^d`, `Nat.Prime p`, `¬ p ∣ d`, `p ∣ (powerBeam d x z).natAbs`
     - 結論: `padicValNat p (powerGap x z * powerBeam d x z).natAbs = padicValNat p (powerBeam d x z).natAbs`
   - `flt_padicValNat_product_eq_beam_of_beam_prime_symm` を追加:
     - 対称に `y` 側基準の Gap / Beam で同じ valuation 等式を証明

3. 結論:
   - S2-D の「Beam prime は Gap に入らない」という補題が、p-adic valuation の等式へ接続された
   - FLT 型方程式から得た `Gap × Beam_d` の積に対して、`p ∤ d` の Beam 側素因子は valuation 上も Beam 側だけから来ることを Lean 上で扱えるようになった
   - primitive prime / squarefree 上界と衝突させるための valuation 入口ができた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - `padicValNat.mul` は非ゼロ仮定を要求するため、`beam.natAbs = 0` の場合を先に分岐した
   - `gap.natAbs ≠ 0` は `¬ p ∣ gap.natAbs` から導出した

6. 次の課題:
   - `y^d = Gap * Beam` と今回の valuation bridge を組み合わせ、`padicValNat p Beam = d * padicValNat p |y|` 型の補題へ進む
   - `padicValNat.pow` と `Int.natAbs_pow` を使って完全 d 乗側の valuation を取り出す
   - Beam 側の primitive prime / valuation 上界 API と接続する

---

### 日時: 2026/04/28 17:41 JST (S2-F: Beam valuation equals d times side valuation)

1. 目的:
   - review-010.md の S2-F 方針に従い、Beam 側 valuation が完全 d 乗側から `d * padicValNat p |side|` になることを証明する
   - S2-E の `v_p(|Gap * Beam|) = v_p(|Beam|)` と、FLT 積分解 `side^d = Gap * Beam` を合成する
   - 左右対称に `y` 側 / `x` 側の補題を用意する

2. 実施:
   - `PowerGapBeamGcd.lean` に Power Valuation Bridge セクションを追加
   - `flt_padicValNat_beam_eq_d_mul_y_of_beam_prime` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z x = 1`, `x^d + y^d = z^d`, `y.natAbs ≠ 0`, `Nat.Prime p`, `¬ p ∣ d`, `p ∣ (powerBeam d x z).natAbs`
     - 結論: `padicValNat p (powerBeam d x z).natAbs = d * padicValNat p y.natAbs`
   - `flt_padicValNat_beam_eq_d_mul_x_of_beam_prime_symm` を追加:
     - 仮定: `1 ≤ d`, `Int.gcd z y = 1`, `x^d + y^d = z^d`, `x.natAbs ≠ 0`, `Nat.Prime p`, `¬ p ∣ d`, `p ∣ (powerBeam d y z).natAbs`
     - 結論: `padicValNat p (powerBeam d y z).natAbs = d * padicValNat p x.natAbs`
   - 証明では以下を接続:
     - `flt_eq_forces_powerGapBeam` / 対称版
     - `flt_padicValNat_product_eq_beam_of_beam_prime` / 対称版
     - `Int.natAbs_pow`
     - `padicValNat.pow`

3. 結論:
   - Beam 側の `p`-進付値が、完全 d 乗の付値制約により `d` の倍数になることを Lean 上で扱えるようになった
   - S2-B から S2-F までで、FLT 方程式から `Gap × Beam` 分解、gcd 制御、Beam 側 valuation 制約までが一本につながった
   - primitive prime / squarefree 上界と衝突させるための直前段階が整った

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 当初は `p ∣ Beam` から観測辺 `y` / `x` の非ゼロ性を導こうとしたが、`Beam = 0` の可能性を排除できないため不十分だった
   - 修正として、`padicValNat.pow` に必要な仮定 `y.natAbs ≠ 0` / `x.natAbs ≠ 0` を定理の明示的な仮定に追加した

6. 次の課題:
   - S2-G として、`p ∣ Beam`, `padicValNat p Beam ≤ 1`, `2 ≤ d` と S2-F の等式から矛盾を導く補題を作る
   - Beam 側の primitive prime / squarefree 上界 API から `padicValNat p Beam ≤ 1` を供給する橋を探す
   - 必要なら非ゼロ仮定を FLT primitive package 側から供給する補助補題を整備する

---

### 日時: 2026/04/28 17:51 JST (S2-G: Beam valuation upper-bound contradiction)

1. 目的:
   - review-011.md の S2-G 方針に従い、Beam 側 valuation が `≤ 1` である場合に FLT 型の完全 d 乗制約と衝突する補題を作る
   - `p ∣ Beam`, `padicValNat p Beam ≤ 1`, `2 ≤ d` と S2-F の等式 `v_p(Beam)=d*v_p(side)` から矛盾を導く
   - 左右対称版も用意する

2. 実施:
   - `PowerGapBeamGcd.lean` に Valuation Contradiction Bridge セクションを追加
   - 一般算術補題 `padicValNat_eq_d_mul_and_le_one_contradiction` を追加:
     - 仮定: `2 ≤ d`, `1 ≤ v`, `v ≤ 1`, `v = d * k`
     - 結論: `False`
   - 補助補題 `one_le_padicValNat_of_prime_dvd` を追加:
     - 仮定: `Nat.Prime p`, `n ≠ 0`, `p ∣ n`
     - 結論: `1 ≤ padicValNat p n`
     - `padicValNat_dvd_iff_le` を使用
   - `flt_beam_prime_val_le_one_contradiction` を追加:
     - 仮定: `1 ≤ d`, `2 ≤ d`, `Int.gcd z x = 1`, `x^d + y^d = z^d`, `y.natAbs ≠ 0`, `Nat.Prime p`, `¬ p ∣ d`, `p ∣ Beam`, `Beam ≠ 0`, `v_p(Beam) ≤ 1`
     - 結論: `False`
   - `flt_beam_prime_val_le_one_contradiction_symm` を追加:
     - 対称に `x` 側基準の補題を実装

3. 結論:
   - Beam 側に現れた `p ∤ d` の素因子が valuation `≤ 1` であるなら、FLT 型方程式とは両立しないことを Lean 上で示せるようになった
   - S2-B から S2-G までで、FLT 方程式から Gap/Beam 分解、gcd 制御、valuation 抽出、valuation 上界との矛盾までが no-sorry で接続された
   - 残る主課題は、既存 primitive prime / squarefree API から `v_p(Beam) ≤ 1` を供給する bridge を作ることになった

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - `p ∣ Beam` だけでは `Beam = 0` を排除できないため、`one_le_padicValNat_of_prime_dvd` には `n ≠ 0` を明示仮定として入れた
   - そのため FLT wrapper 側にも `Beam.natAbs ≠ 0` を明示仮定として追加した
   - `padicValNat_dvd_iff_le` は通常の名前付き引数ではなく `@padicValNat_dvd_iff_le p (Fact.mk hp) n 1 hn` の形で適用した

6. 次の課題:
   - S2-H として、Beam 側の primitive prime / squarefree 上界 API から `padicValNat p Beam ≤ 1` を供給する bridge を実装する
   - `Beam.natAbs ≠ 0` と辺の非ゼロ仮定を FLT primitive package から自然に供給する補助補題を検討する
   - `FLTPowerGapBeamDatum` 構造体を導入するか、現行の wrapper 群を維持するか判断する

---

### 日時: 2026/04/28 17:58 JST (S2-H: Squarefree Beam valuation bridge)

1. 目的:
   - review-012.md の S2-H 方針に従い、Beam 側の squarefree 仮定から `padicValNat p Beam ≤ 1` を供給する bridge を作る
   - S2-G の `flt_beam_prime_val_le_one_contradiction` に squarefree route を接続する
   - 左右対称版も用意する

2. 実施:
   - `PowerGapBeamGcd.lean` に `DkMath.NumberTheory.ZsigmondyCyclotomicSquarefree` を import
   - 既存補題 `DkMath.NumberTheory.GcdNext.padicValNat_le_one_of_squarefree` を再利用
   - `powerBeam_padicValNat_le_one_of_squarefree` を追加:
     - 仮定: `Nat.Prime p`, `(powerBeam d x z).natAbs ≠ 0`, `Squarefree (powerBeam d x z).natAbs`
     - 結論: `padicValNat p (powerBeam d x z).natAbs ≤ 1`
   - `flt_beam_squarefree_prime_contradiction` を追加:
     - squarefree Beam 仮定から valuation 上界を供給し、S2-G の `flt_beam_prime_val_le_one_contradiction` に接続
   - `flt_beam_squarefree_prime_contradiction_symm` を追加:
     - 対称に `x` 側基準の squarefree route を実装

3. 結論:
   - S2-G の抽象矛盾補題に、具体的な上界供給ルートとして squarefree Beam 仮定を接続できた
   - FLT 型方程式 + primitive/coprime 条件 + `p ∤ d` + Beam prime + squarefree Beam から直接 `False` を得る API ができた
   - Chapter 2 の Power Gap/Beam valuation engine は、squarefree route について一通り no-sorry で閉じた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGcd` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - squarefree からの valuation 上界は自前で再証明せず、既存の `ZsigmondyCyclotomicSquarefree` 側の補題を薄く wrap した

6. 次の課題:
   - primitive prime / Zsigmondy route から `p ∣ Beam`, `p ∤ d`, `Squarefree Beam` または `padicValNat p Beam ≤ 1` を供給する bridge を検討する
   - `powerBeam` と既存 `GN d (a-b) b` / `diffPowSum` / `PrimitiveBeam` API の対応を明示する
   - Chapter 2 の wrapper 群が増えたため、`FLTPowerGapBeamDatum` 構造体を導入するか判断する

---

### 日時: 2026/04/28 18:10 JST (S2-I: PowerBeam diffPowSum/GN bridge)

1. 目的:
   - review-013.md の S2-I 方針に従い、`powerBeam` を既存の `diffPowSum` / `GN` API へ明示的に接続する
   - Power Gap/Beam 側で使っている境界差・差冪和の定義的対応を補題として固定する
   - 低次数の展開補題を用意し、特に 3 次 Beam と既存 `GN` 表現の橋を作る

2. 実施:
   - `PowerGapBeam.lean` に以下の基本 bridge を追加:
     - `powerGap_eq_sub`: `powerGap x z = z - x`
     - `powerBeam_eq_diffPowSum`: `powerBeam d x z = DkMath.Algebra.DiffPow.diffPowSum z x d`
   - 低次数展開として以下を追加:
     - `powerBeam_three`: `powerBeam 3 x z = z^2 + z*x + x^2`
     - `powerBeam_four`: `powerBeam 4 x z = z^3 + z^2*x + z*x^2 + x^3`
   - 新規ファイル `PowerGapBeamGN.lean` を追加:
     - `CosmicFormulaBinom` 依存を純粋な `PowerGapBeam.lean` から分離
     - `powerBeam_three_shift_eq_GN` を追加し、`powerBeam 3 x (x + u) = GN 3 u x` を証明
   - `CosmicFormula.lean` に `PowerGapBeamGN` の import を追加

3. 結論:
   - Chapter 2 の Power Gap/Beam API が、既存の差冪和 API と Lean 上で明示的に接続された
   - 3 次の場合について、shifted endpoint 表現 `x, x+u` と既存 `GN 3 u x` の一致を no-sorry で証明できた
   - `GN` 依存を別ファイルに切り出したため、基礎的な Gap/Beam module は軽い依存関係のまま維持できた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeam` 成功
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - `powerBeam_three_shift_eq_GN` の初回証明では、`GN` を直接簡約するだけでは目標形まで落ちなかった
   - 修正として `GN_eq_sum` を明示的に rewrite し、`Finset.range` を展開してから `norm_num` と `ring` で閉じた

6. 次の課題:
   - 一般次数の `powerBeam d x (x+u)` と `GN d u x` の bridge を検討する
   - `PrimitiveBeam` / Zsigmondy route から Chapter 2 の Beam prime 仮定へ接続する
   - `FLTPowerGapBeamDatum` 構造体導入の要否を、次段の wrapper 増加を見て判断する

---

### 日時: 2026/04/28 18:40 JST (S2-J: Quartic PowerBeam/GN bridge)

1. 目的:
   - review-014.md の S2-J 方針に従い、`powerBeam` と `GN` の bridge を d=4 まで拡張する
   - 一般次数 bridge `powerBeam d x (x+u) = GN d u x` が今すぐ薄く通る形か確認する
   - 後続の PrimitiveBeam / Zsigmondy route 接続に向けて、低次数の安定 API を増やす

2. 実施:
   - `CosmicFormulaBinom.GN_eq_sum` の形を確認:
     - `GN d x u` は `∑ k < d, choose d (k+1) * x^k * u^(d-1-k)` という二項係数展開
     - `powerBeam d x (x+u)` は endpoint 型の差冪和なので、一般次数 bridge には二項展開側の整理が必要
   - `PowerGapBeamGN.lean` に `powerBeam_four_shift_eq_GN` を追加:
     - `powerBeam 4 x (x + u) = DkMath.CosmicFormulaBinom.GN 4 u x`
   - `PrimitiveBeam.lean` / `Zsigmondy.lean` の既存 API を確認:
     - `primitive_prime_dvd_GN`
     - `primitive_prime_padic_eq_GN`
     - `primitive_prime_padic_bound_diff_of_squarefree_GN`
     - `primitivePrimeDivisor_body_three_imp_dvd_GN`

3. 結論:
   - d=3 に続き、d=4 でも shifted Power Beam と既存 `GN` 表現の一致を no-sorry で固定できた
   - 一般次数 bridge は数学的には自然だが、`GN` が二項係数展開であるため、単なる `rfl` / `simp` ではなく和変形または既存 GTail API の追加整備が必要と判断した
   - PrimitiveBeam / Zsigmondy 側には `GN` への divisibility / valuation API が既にあり、次段では `powerBeam` 側へ運ぶ thin wrapper を作る方針が見えた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題は no-sorry で証明完了

5. 失敗事例:
   - `powerBeam_four_shift_eq_GN` の初回証明では `Nat.choose 4 2` が `6` に正規化されず、`ring` が閉じなかった
   - 修正として `norm_num [Nat.choose]` を使い、二項係数を明示的に数値化してから `ring` で閉じた

6. 次の課題:
   - `PrimitiveBeam.primitive_prime_dvd_GN` を `powerBeam` 表現へ移す wrapper を作る
   - 特に `q ∣ GN d (a-b) b` から `q ∣ powerBeam d b a` へ接続する補題を検討する
   - 一般次数 bridge は、既存 `GTail` / `GN_eq_sum` の和変形補題を整えてから再挑戦する

---

### 日時: 2026/04/28 19:02 JST (S2-K: GN gap to endpoint PowerBeam wrappers)

1. 目的:
   - review-015.md の S2-K 方針に従い、`GN d (a-b) b` 側の情報を endpoint 型 `powerBeam d b a` へ移す bridge を作る
   - まず d=3, d=4 の等式 bridge を固定し、既存 PrimitiveBeam / Zsigmondy route の低次数情報を Chapter 2 の PowerBeam API へ流せるようにする
   - divisibility と p-adic valuation の移送に使う薄い wrapper を用意する

2. 実施:
   - `PowerGapBeamGN.lean` に以下の endpoint-gap 等式 bridge を追加:
     - `powerBeam_three_eq_GN_of_gap`: `powerBeam 3 b a = GN 3 (a - b) b`
     - `powerBeam_four_eq_GN_of_gap`: `powerBeam 4 b a = GN 4 (a - b) b`
   - d=3 の divisibility wrapper を追加:
     - `dvd_powerBeam_three_of_dvd_GN_gap`
     - `q ∣ GN 3 (a-b) b` から `q ∣ powerBeam 3 b a` を得る
   - d=3 の valuation wrapper を追加:
     - `powerBeam_three_padicValNat_eq_GN_gap`
     - `padicValNat p (powerBeam 3 b a).natAbs = padicValNat p (GN 3 (a-b) b).natAbs`

3. 結論:
   - shifted bridge `powerBeam d x (x+u) = GN d u x` に加えて、実際の endpoint `a,b` で使いやすい gap bridge が d=3,4 で揃った
   - 既存の `PrimitiveBeam.primitive_prime_dvd_GN` などが返す `q ∣ GN d (a-b) b` 型の情報を、少なくとも d=3 では直接 `powerBeam` 側へ移せるようになった
   - p-adic valuation についても、GN 側の上界や等式を PowerBeam 側へ運ぶ入口ができた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了

5. 失敗事例:
   - 大きな失敗はなし
   - endpoint-gap bridge は `GN_eq_sum` を展開し、低次数では `norm_num` / `norm_num [Nat.choose]` と `ring` で閉じられることを確認した

6. 次の課題:
   - d=4 についても必要なら divisibility / valuation wrapper を追加する
   - `PrimitiveBeam.primitive_prime_dvd_GN` から `q ∣ powerBeam 3 b a` へ進む specialized wrapper を作る
   - `GN` 側の squarefree / valuation 上界を `powerBeam` 側の S2-G/S2-H 矛盾 API へ接続する

---

### 日時: 2026/04/28 19:11 JST (S2-L: PrimitiveBeam to cubic PowerBeam bridge)

1. 目的:
   - review-016.md の S2-L 方針に従い、既存 `PrimitiveBeam` / `GN` 側の情報を d=3 の `powerBeam` 側へ直接運ぶ wrapper を作る
   - GN 側の valuation 上界・squarefree 仮定を PowerBeam 側へ移送する薄い補題を追加する
   - Nat API で得られる primitive prime divisibility を、整数 `powerBeam` の `natAbs` divisibility へ接続する

2. 実施:
   - `PowerGapBeamGN.lean` に `DkMath.NumberTheory.PrimitiveBeam` を import
   - d=3 の valuation 上界移送補題を追加:
     - `powerBeam_three_padicValNat_le_one_of_GN_le_one`
     - `padicValNat p (GN 3 (a-b) b).natAbs ≤ 1` から `padicValNat p (powerBeam 3 b a).natAbs ≤ 1` を得る
   - d=3 の squarefree 移送補題を追加:
     - `powerBeam_three_squarefree_of_GN_squarefree`
     - `Squarefree (GN 3 (a-b) b).natAbs` から `Squarefree (powerBeam 3 b a).natAbs` を得る
   - Nat `PrimitiveBeam` から整数 PowerBeam への divisibility wrapper を追加:
     - `primitive_prime_dvd_powerBeam_three_natAbs`
     - `PrimitivePrimeFactorOfDiffPow q a b 3` と `b < a` から `q ∣ (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs` を得る
     - `Nat.cast_sub` と `Int.natCast_dvd` で Nat `GN` の割り切りを Int `natAbs` へ移送

3. 結論:
   - `PrimitiveBeam.primitive_prime_dvd_GN` の出力を、Chapter 2 の valuation engine が直接使う `p ∣ (powerBeam 3 ...).natAbs` 型へ運べるようになった
   - GN 側の valuation 上界・squarefree 情報も d=3 PowerBeam 側へ薄く移せるため、S2-G/S2-H の矛盾 API へ接続する入口が広がった
   - Nat 側 primitive prime API と Int 側 FLT/PowerBeam API の型差を、専用 wrapper で吸収できた

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - Nat `GN` と Int `GN.natAbs` の等式を直接 `rw` / `ring` で処理しようとすると、和の展開と `natAbs` の正規形が噛み合わなかった
   - 修正として、`Nat.cast_sub` で gap を cast し、Nat divisibility を `exact_mod_cast` で Int divisibility に移してから `Int.natCast_dvd` で `natAbs` 側へ戻した

6. 次の課題:
   - GN 側 squarefree / valuation 上界を S2-G/S2-H の `flt_beam_*_contradiction` へ直接接続する d=3 wrapper を作る
   - `primitive_prime_dvd_powerBeam_three_natAbs` と `flt_beam_prime_val_le_one_contradiction` を合成する
   - `PrimitiveBeam` import によって `ZsigmondyCyclotomicResearch` の既存 `sorry` 警告が流入するため、必要なら bridge ファイル分割を検討する

---

### 日時: 2026/04/28 19:19 JST (S2-M: Cubic GN fuel to FLT contradiction)

1. 目的:
   - review-017.md の S2-M 方針に従い、GN 側の valuation 上界 / squarefree 仮定を S2-G/S2-H の FLT 矛盾 API へ直接接続する
   - d=3 の `GN 3 (z-x) x` 情報から、`powerBeam 3 x z` の valuation contradiction へ一発で進む wrapper を作る
   - Chapter 2 の `GN -> PowerBeam -> contradiction` 経路を明示 API として固定する

2. 実施:
   - `PowerGapBeamGN.lean` に `DkMath.CosmicFormula.PowerGapBeamGcd` を import
   - d=3 の GN valuation 上界版 contradiction wrapper を追加:
     - `flt_three_beam_GN_val_le_one_contradiction`
     - `padicValNat p (GN 3 (z-x) x).natAbs ≤ 1` を `powerBeam_three_padicValNat_le_one_of_GN_le_one` で Beam 側へ移し、`flt_beam_prime_val_le_one_contradiction` に渡す
   - d=3 の GN squarefree 版 contradiction wrapper を追加:
     - `flt_three_beam_GN_squarefree_contradiction`
     - `Squarefree (GN 3 (z-x) x).natAbs` を `powerBeam_three_squarefree_of_GN_squarefree` で Beam 側へ移し、`flt_beam_squarefree_prime_contradiction` に渡す

3. 結論:
   - GN 側で得られる valuation 上界または squarefree 仮定から、d=3 の FLT 型方程式に対する `False` までを直接導けるようになった
   - S2-K/S2-L で作った GN/PowerBeam bridge が、S2-G/S2-H の valuation contradiction engine と実際に接続された
   - Chapter 2 は d=3 について、`GN fuel -> PowerBeam valuation refuter` の薄い完成形に到達した

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - 大きな失敗はなし
   - `PowerGapBeamGcd` の既存 contradiction wrapper に、S2-L の valuation / squarefree 移送補題を渡すだけで閉じた

6. 次の課題:
   - `primitive_prime_dvd_powerBeam_three_natAbs` を使い、Nat primitive prime witness から d=3 contradiction wrapper の `hbeam` を供給する合成補題を検討する
   - `PowerGapBeamGN.lean` が `PrimitiveBeam` と `PowerGapBeamGcd` の両方を import して重くなってきたため、必要なら `PowerGapBeamPrimitive.lean` などへ分割する
   - `FLTPowerGapBeamDatum` 構造体を導入するか、wrapper 群のまま進めるか判断する

---

### 日時: 2026/04/29 19:29 JST (S2-N: Primitive witness to cubic GN contradiction)

1. 目的:
   - review-018.md の S2-N 方針に従い、Nat primitive prime witness から d=3 の FLT contradiction wrapper へ直接接続する
   - S2-L の `primitive_prime_dvd_powerBeam_three_natAbs` を使って、S2-M の `hbeam` 仮定を自動供給する
   - GN 側 valuation 上界版と squarefree 版の両方で、primitive witness 付きの一発 wrapper を作る

2. 実施:
   - `PowerGapBeamGN.lean` に以下の合成補題を追加:
     - `flt_three_primitive_GN_val_le_one_contradiction`
     - `flt_three_primitive_GN_squarefree_contradiction`
   - `PrimitivePrimeFactorOfDiffPow q a b 3` から `Nat.Prime q` は `hq.1` で取り出す形にした
   - `q ∣ (powerBeam 3 (b : ℤ) (a : ℤ)).natAbs` は `primitive_prime_dvd_powerBeam_three_natAbs hq hab_lt` で供給
   - `q ∤ 3` は primitive witness には含まれないため、明示仮定 `hqnd : ¬ q ∣ 3` として残した

3. 結論:
   - Nat 側 primitive prime witness から、d=3 の GN valuation / squarefree fuel を使った FLT contradiction までが直接つながった
   - Chapter 2 の d=3 route は、`PrimitiveBeam -> GN -> PowerBeam -> valuation contradiction` の合成 API まで到達した
   - 利用者は Nat/Int cast や `hbeam` 供給を手で行わず、primitive witness と GN 側上界情報を渡すだけで `False` を得られる

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - 大きな失敗はなし
   - S2-M の contradiction wrapper に、S2-L の primitive divisibility wrapper を渡すだけで閉じた

6. 次の課題:
   - `PowerGapBeamGN.lean` が重くなったため、軽量 GN bridge と primitive/gcd contradiction bridge をファイル分割するか検討する
   - `q ∤ 3` や `hbeam_ne` を既存 primitive / FLT 文脈から供給できる補助補題を検討する
   - `FLTPowerGapBeamDatum` 構造体の導入タイミングを判断する

---

### 日時: 2026/04/29 19:42 JST (S2-O: Split primitive bridge from PowerGapBeamGN)

1. 目的:
   - review-019.md の提案に従い、重くなった `PowerGapBeamGN.lean` を軽量 GN bridge に戻す
   - `PrimitiveBeam` と `PowerGapBeamGcd` に依存する contradiction wrapper 群を専用ファイルへ分離する
   - `PrimitiveBeam` 経由で流入する既存 `sorry` warning を、軽量 GN bridge から隔離する

2. 実施:
   - 新規ファイル `PowerGapBeamPrimitive.lean` を追加:
     - `DkMath.CosmicFormula.PowerGapBeamGN`
     - `DkMath.CosmicFormula.PowerGapBeamGcd`
     - `DkMath.NumberTheory.PrimitiveBeam`
     を import
   - `PowerGapBeamGN.lean` から以下の重い bridge を `PowerGapBeamPrimitive.lean` へ移動:
     - `primitive_prime_dvd_powerBeam_three_natAbs`
     - `flt_three_beam_GN_val_le_one_contradiction`
     - `flt_three_beam_GN_squarefree_contradiction`
     - `flt_three_primitive_GN_val_le_one_contradiction`
     - `flt_three_primitive_GN_squarefree_contradiction`
   - `PowerGapBeamGN.lean` から `PowerGapBeamGcd` / `PrimitiveBeam` import を削除
   - `CosmicFormula.lean` に `PowerGapBeamPrimitive` import を追加

3. 結論:
   - `PowerGapBeamGN.lean` は、低次数 GN bridge と valuation / squarefree の単純移送に責務を戻した
   - primitive witness と FLT contradiction まで含む重い API は `PowerGapBeamPrimitive.lean` に隔離された
   - モジュール境界が整理され、軽量 GN bridge を使うだけなら `PrimitiveBeam` / research warning に触れずに済む構造になった

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamGN` 成功
   - `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 移動した補題はすべて no-sorry のまま維持
   - `PowerGapBeamPrimitive` 側では、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示される

5. 失敗事例:
   - 大きな失敗はなし
   - 補題本体は変更せず、import 境界と配置だけを整理したため、証明はそのまま通った

6. 次の課題:
   - `q ∤ 3` を primitive witness または追加補題から供給できるか調査する
   - `hbeam_ne` を既存 positivity / nonzero API から供給できるか調査する
   - `FLTPowerGapBeamDatum` または cubic 専用 datum 構造体を導入するか判断する

---

### 日時: 2026/04/29 19:56 JST (S2-P: Cubic PowerBeam nonzero from ordered endpoints)

1. 目的:
   - review-020.md の提案に従い、d=3 primitive contradiction wrapper の明示仮定 `hbeam_ne` を削減する
   - `b < a` から `(powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0` を自動供給する補題を作る
   - 既存の primitive contradiction wrapper に、Beam 非ゼロ仮定を内部供給する使いやすい版を追加する

2. 実施:
   - `PowerGapBeamPrimitive.lean` に `powerBeam_three_natAbs_ne_zero_of_lt` を追加:
     - 仮定: `b < a`
     - 結論: `(powerBeam 3 (b : ℤ) (a : ℤ)).natAbs ≠ 0`
     - `powerBeam_three` で展開し、`a > 0` と `positivity` から Beam 正値性を示した
   - `hbeam_ne` を明示仮定に取らない wrapper を追加:
     - `flt_three_primitive_GN_val_le_one_contradiction_of_lt`
     - `flt_three_primitive_GN_squarefree_contradiction_of_lt`
   - 既存の `flt_three_primitive_GN_*_contradiction` は後方互換のため残し、新補題は `hab_lt` から `powerBeam_three_natAbs_ne_zero_of_lt` を呼び出す構成にした

3. 結論:
   - d=3 primitive contradiction wrapper の利用時に、Beam 非ゼロ性を手で渡す必要がなくなった
   - `b < a` は primitive / endpoint 文脈で既に自然に持っている仮定なので、API の実用性が上がった
   - `q ∤ 3` は cubic 例外と絡む可能性があるため、今回は明示仮定として維持した

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - 大きな失敗はなし
   - Int 上の三次 Beam を `powerBeam_three` で明示展開し、`positivity` で正値性を閉じられた

6. 次の課題:
   - `q ∤ 3` を primitive witness から無条件に出せるか、または cubic 例外として残すべきかを調査する
   - `hqnd` を維持する場合、名前付き wrapper / context 構造体で扱いやすくする
   - cubic 専用 datum 構造体を導入するか判断する

---

### 日時: 2026/04/29 20:04 JST (S2-Q: q ≠ 3 wrapper for cubic primitive route)

1. 目的:
   - review-021.md の提案に従い、明示仮定 `q ∤ 3` をより読みやすい十分条件 `q ≠ 3` から供給する
   - cubic では `q = 3` が特例になり得るため、primitive witness から無条件に `q ∤ 3` を消すことは避ける
   - 既存の `_of_lt` wrapper に、`q ≠ 3` 版の使いやすい入口を追加する

2. 実施:
   - `PowerGapBeamPrimitive.lean` に `prime_not_dvd_three_of_ne_three` を追加:
     - 仮定: `Nat.Prime q`, `q ≠ 3`
     - 結論: `¬ q ∣ 3`
     - `Nat.dvd_prime Nat.prime_three` で `q ∣ 3` から `q = 1 ∨ q = 3` を取り出し、素数性と `q ≠ 3` で矛盾させた
   - `q ≠ 3` を受け取る cubic primitive contradiction wrapper を追加:
     - `flt_three_primitive_GN_val_le_one_contradiction_of_lt_ne_three`
     - `flt_three_primitive_GN_squarefree_contradiction_of_lt_ne_three`
   - 新 wrapper は `hq.1 : Nat.Prime q` と `q ≠ 3` から `prime_not_dvd_three_of_ne_three` を呼び、既存の `_of_lt` 版へ接続する構成にした

3. 結論:
   - 利用者は `¬ q ∣ 3` を直接渡さず、より自然な `q ≠ 3` を渡せるようになった
   - cubic の特別素数 `3` を無理に排除せず、例外を明示的に分岐できる API になった
   - 既存の `hqnd` 明示版は維持しつつ、通常利用向けの読みやすい十分条件版が追加された

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - 初回は存在しない補題名 `Nat.Prime.dvd_prime_iff_eq` を使って失敗し、既存コードでも使われていた `Nat.dvd_prime` へ修正して解決した
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - `Nat.Prime.dvd_prime_iff_eq` は現環境に存在せず、ビルドに失敗した
   - 修正として `Nat.dvd_prime Nat.prime_three` を用い、`q ∣ 3` から `q = 1 ∨ q = 3` を得る形にした

6. 次の課題:
   - `q = 3` の cubic 特例を別ルートとして扱うべきか調査する
   - `hqnd` / `q ≠ 3` を含む cubic 専用 context 構造体を導入するか判断する
   - 既存 wrapper 群の標準入口を `_of_lt_ne_three` 版へ寄せるか検討する

---

### 日時: 2026/04/29 20:09 JST (S2-R: Cubic primitive FLT context)

1. 目的:
   - review-022.md の提案に従い、通常 branch (`q ≠ 3`) の cubic primitive route を束ねる context 構造体を試作する
   - 既存 wrapper の長い仮定列をまとめ、valuation / squarefree contradiction を context theorem として呼べるようにする
   - `q = 3` の exceptional branch は未解決のまま分離し、通常 branch の API を整理する

2. 実施:
   - `PowerGapBeamPrimitive.lean` に `CubicPrimitiveFLTContext` 構造体を追加:
     - `q a b : ℕ`
     - `y : ℤ`
     - `hprim : PrimitivePrimeFactorOfDiffPow q a b 3`
     - `hab_lt : b < a`
     - `hcop : Int.gcd (a : ℤ) (b : ℤ) = 1`
     - `hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3`
     - `hy_ne : y.natAbs ≠ 0`
     - `hq_ne_three : q ≠ 3`
   - `CubicPrimitiveFLTContext` namespace に以下を追加:
     - `val_le_one_contradiction`
     - `squarefree_contradiction`
   - どちらも既存の `_of_lt_ne_three` wrapper を呼ぶ薄い構成にした

3. 結論:
   - 通常 cubic primitive route の仮定群を一つの context として扱えるようになった
   - GN 側の valuation 上界または squarefree 仮定だけを追加で渡せば、context theorem から `False` を得られる
   - `q ≠ 3` は context の明示フィールドとして残し、cubic exceptional branch を無理に通常 route に混ぜない設計にした

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規構造体 / 補題は no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - 大きな失敗はなし
   - context theorem は既存 `_of_lt_ne_three` wrapper に委譲するだけで閉じた

6. 次の課題:
   - `q = 3` の cubic exceptional branch を別 context または別 wrapper として扱うか調査する
   - 通常 branch の標準入口を context theorem に寄せるか判断する
   - context に追加すべき導出補題（Beam divisibility / Beam nonzero など）を整理する

---

### 日時: 2026/04/29 20:14 JST (S2-S: Cubic context derived facts)

1. 目的:
   - review-023.md の提案に従い、`CubicPrimitiveFLTContext` を観測パックとして使いやすくする
   - context から頻繁に使う導出事実を namespace theorem として追加する
   - 通常 cubic branch の利用時に、primitive witness / endpoint 条件からの導出を毎回手で展開しなくてよいようにする

2. 実施:
   - `PowerGapBeamPrimitive.lean` の `CubicPrimitiveFLTContext` namespace に以下を追加:
     - `prime`: `Nat.Prime C.q`
     - `q_not_dvd_three`: `¬ C.q ∣ 3`
     - `beam_dvd`: `C.q ∣ (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs`
     - `beam_ne`: `(powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs ≠ 0`
   - 既存補題を薄く再利用:
     - `prime_not_dvd_three_of_ne_three`
     - `primitive_prime_dvd_powerBeam_three_natAbs`
     - `powerBeam_three_natAbs_ne_zero_of_lt`

3. 結論:
   - `CubicPrimitiveFLTContext` が、単なる仮定束ではなく、必要な観測事実を引き出せる API になった
   - 通常 branch で必要な prime / degree 非整除 / Beam divisibility / Beam nonzero が context から直接取得できる
   - 既存の contradiction theorem はそのまま維持し、context の利便性だけを増やした

4. 検証:
   - `lake build DkMath.CosmicFormula.PowerGapBeamPrimitive` 成功
   - `lake build DkMath.CosmicFormula` 成功
   - 新規補題はすべて no-sorry で証明完了
   - build warning として、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` 警告が再表示された

5. 失敗事例:
   - 大きな失敗はなし
   - すべて既存の wrapper / projection に委譲するだけで閉じた

6. 次の課題:
   - `q = 3` の cubic exceptional branch を別 context として切るか判断する
   - context theorem を通常 branch の標準入口として文書化する
   - context から GN 側 valuation / squarefree 仮定をどの形で供給するのが自然か検討する
