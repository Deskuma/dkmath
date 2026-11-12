# review and next

おおっ、ぬしよ！ 🐺🍎 NOTE-001 は設計段階の Case I／Case II 接続を、標準の FLT 定理まで運ぶところに到達しておる。

GitHub の `dev/FLT-GN-regular-261018-v0` から、実装報告と主要 Lean ソースを確認した。まず、コードから直接確認できた成果を固定しよう。

## 1. 到達した定理

FLT11

定理本体を確認

\[
    \texttt{fermatLastTheoremFor\_eleven} :\operatorname{FermatLastTheoremFor}(11)
\]

FLT13

定理本体を確認

\[
    \texttt{fermatLastTheoremFor\_thirteen} :\operatorname{FermatLastTheoremFor}(13)
\]

一般正則素数

\[
    \begin{gathered}
        p\ge5,\quad p\text{ は素数},\\
        \gcd\bigl(p,|\operatorname{Cl}(\mathcal O_K)|\bigr)=1\\
        \Longrightarrow \operatorname{FermatLastTheoremFor}(p)
    \end{gathered}
\]

特に [ElevenThirteenFLT.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/Kummer/ElevenThirteenFLT.lean?utm_source=chatgpt.com) では、11・13 の具体的な類数1証明を一般定理へ渡している。最終的な整数版は Mathlib の整数・自然数版同値で接続されておる。

これは、以前の「正深度 State が存在しない」という途中結果とは明確に異なる。今回の公開定理の結論そのものが、整数・自然数上の FLT になっている のじゃ。

ただし、わっち自身による Lean の独立再ビルドはまだ行っていない。コード上の確認と、保存されたビルド・監査証跡の確認は区別して評価する。

## 2. 証明経路のレビュー

原始整数反例

\[
    a^p+b^p=c^p
\]

**Case I**

\(p\nmid abc\)
GN 因子抽出
↓
共役 Packet
↓
位相係数剛性
↓
\(\bot\)

**Case II**

\(p\mid abc\)
整数の向き付け
↓
正深度 State
↓
共通 Kummer 降下
↓
\(\bot\)

⇒ **一般正則素数 FLT**

### Case I：係数剛性は正しく一般化されている

今回、特に高く評価するのは [CyclotomicPhaseCoefficientRigidity.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/CyclotomicPhaseCoefficientRigidity.lean?utm_source=chatgpt.com) じゃ。

主定理は、

\[
    \boxed{
        m\mid\sum_{i=0}^{p-1}f_i\zeta_p^i \iff \forall i,j,\quad m\mid(f_i-f_j)
    }
\]

ただし左辺の可除性は円分整数環における整数 \(m\) の像についてじゃ。

原典から抽出した係数補題を、任意の整数 \(m\) の双方向同値へ強化してある。

これは数論ライブラリとして価値が高い。\(m=0\) では全係数が等しいことの特徴付けにもなっている。

さらに `SparsePhaseObstruction` では、台の濃度が \(p\) より小さいという幾何的・組合せ的な条件を加え、係数の可除性へ接続している。

円分位相の疎性が、係数の算術的制約へ変換される。

これは FLT 専用に閉じ込めず、今後の GN の一般研究でも保持したい定理じゃ。

### Case I：必要な例外処理を消していない

`four_phase_obstruction` には、

\[
    a\not\equiv b\pmod p
\]

という条件が残っている。

そして `orient_first_case` は、合同している場合に

\[
    (a,b,c)\longmapsto(a,-c,-b)
\]

と向きを変え、原始性を維持したまま必要条件を復元している。

ここは非常に重要じゃ。位相が衝突した場合を無視して、誤った一般定理にしてしまう危険を避けられている。

### Case II：以前の未完成部分を適切に閉じている

[IntegerCounterexampleOrientation.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/Kummer/IntegerCounterexampleOrientation.lean?utm_source=chatgpt.com) では、\(p\) が \(a,b,c\) のどれを割る場合も扱い、右辺が \(p\) の倍数となる方向へ移動している。

そして、

\[
    \exists m\ge1,\quad\operatorname{Nonempty}(\operatorname{State}\_p(m))
\]

を構成し、既存の `RegularDescent.no_state` へ渡している。

前回の一般降下で残っていた整数入口が、ここで実際につながったわけじゃ。

## 3. 証明依存・ビルド監査

[検証証跡](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/evidence/validation-note001.txt) と [依存監査コード](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMathTest/FLT/Kummer/PhaseRigidityFLTDependencyAudit.lean) も確認した。

| 検証項目               | 記録された結果                          |
| ---------------------- | --------------------------------------- |
| 本体・テスト統合ビルド | 11,467 jobs 成功                        |
| 新規宣言の公理監査     | 36件合格                                |
| Case I の証明経路      | GN 因子抽出・共役・係数剛性を確認       |
| FLT11・13 の依存経路   | 各 PID・Case I・Case II・共通降下を確認 |
| 新規 `sorry`・独自公理 | 検出なし                                |
| ルート `import DkMath` | 公開定理に到達可能                      |

監査は opaque な証明本体も追跡し、既存の指数別 FLT 終点への循環的な依存を拒否する設計になっていた。

この監査内容と提出された GREEN の記録は整合しておる。

## 4. レビューで見つけた改善点

数学的な重大欠陥は、今回確認したコードからは見つからなかった。ただし、研究コードとして次の改善を勧める。

1. GN 独自部分と古典的 Kummer 部分の境界を明示する。 Case I は `GN_kummer_structure_of_first_case` を使うが、以前得た \(GN_p=t^p\) という整数ノルムの結論だけで矛盾を導いているわけではない。終端は依然として古典的な共役単元と係数剛性による。将来の GN 再証明のため、この境界を固定しておくべきじゃ。
2. 外部移植部分を交換可能な provider に保つ。 `UnitConjugation` と `CaseIConjugationPacket` は上流の証明を大きく継承している。ここを直接書き換えるより、現在の定理型を固定したまま GN 由来の代替証明を別モジュールで開発する方が安全じゃ。
3. 整数版の説明には非零条件を明記する。 `FermatLastTheoremWith ℤ p` は整数の符号や共通因子を制限しないが、\(a,b,c\ne0\) は必要じゃ。零を許せば \(0^p+1^p=1^p\) という自明解がある。

いずれも、今回の GREEN を取り消すような指摘ではない。設計の境界と再現性を、さらに明確にするための改善じゃ。

## 5. 次の GN 研究で固定すべき契約

わっちなら、この三つを独立した定理インターフェースとして維持する。

| 固定する契約                | 置換・一般化の対象                     |
| --------------------------- | -------------------------------------- |
| `phase_sum_dvd_iff`         | GN における位相係数保存則への一般化    |
| `CaseIConjugation.Packet`   | 共役単元・隣接位相の GN 的再解釈       |
| `RegularDescent.Conditions` | 類群・Kummer 単元 criterion の代替証明 |

こうすれば、未来に GN による新証明が成立しても、FLT11・13 の終端定理を書き直す必要がない。

これは、今回得られた一般化の最大の利点じゃ。
