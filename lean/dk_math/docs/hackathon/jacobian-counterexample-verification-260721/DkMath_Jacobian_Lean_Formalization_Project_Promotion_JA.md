# DkMath Breaking Math Verification

## ヤコビアン反例候補の Lean 形式検証と、Cosmic Framework による「一意性解除」の構造化

### キャッチコピー

**局所では完全に壊れていない。
それでも、大域では三つの住所が一つに重なる。**

DkMath は、公開された三次元複素多項式写像を Lean 4 + Mathlib で独立に形式化し、形式 Jacobian の行列式が恒等的に `1` でありながら、三つの相異なる入力点が同じ出力へ写ることを、有限の kernel-checkable certificate として固定しました。

---

## 一文紹介

**公開された重大な多項式写像を、AI・Codex・Lean によって短期間で分解・検証し、局所 Jacobian 情報と大域的一意性が一致しない構造を、DkMath の `UniqueGap` / `GapCrystal` API へ抽出したプロジェクトです。**

---

## 30秒紹介

このプロジェクトでは、三変数多項式写像を `MvPolynomial` として定義し、その形式偏微分から Jacobian 行列を生成しました。Lean は、その行列式が正規化後に恒等的に `1` であることを証明します。

一方、三つの相異なる複素点が同じ出力 `(1/8, 0, 0)` に写ることも、同じ多項式定義から直接証明されました。したがって写像は非単射であり、集合写像としての左逆すら持ちません。

DkMath はこの衝突を、「同じ Core を復元する正しい Gap が複数存在する」構造として一般化し、局所保存と大域的一意性の違いを再利用可能な Lean API にしました。

---

# 1. Lean 形式化で完成したもの

## 1.1. 多項式写像の唯一の真実源

対象となる写像は、まず有理係数三変数多項式として定義されました。

$$P=(1+xy)^3z+y^2(1+xy)(4+3xy)$$

$$Q=y+3x(1+xy)^2z+3xy^2(4+3xy)$$

$$R=2x-3x^2y-x^3z$$

Lean 上では、これらを `MvPolynomial (Fin 3) ℚ` として定義しています。

重要なのは、Jacobian 行列を手書きの九成分から定義していないことです。

```lean
def jacobianMatrixQ : Matrix (Fin 3) (Fin 3) Poly3Q :=
  fun i j ↦ MvPolynomial.pderiv j (counterexamplePoly i)
```

すなわち証明経路は、常に次です。

```text
元の多項式
→ 形式偏微分
→ Jacobian 行列
→ determinant
```

## 1.2. 明示的な三点衝突

次の三点を定義しました。

$$p_0=\left(0,0,-\frac14\right)$$

$$p_1=\left(1,-\frac32,\frac{13}{2}\right)$$

$$p_2=\left(-1,\frac32,\frac{13}{2}\right)$$

Lean は、これらが pairwise distinct でありながら、すべて同じ像

$$\left(-\frac14,0,0\right)$$

へ写ることを、有理数上の正確計算として証明しました。

## 1.3. determinant `-2`

形式 Jacobian を `Matrix.det_fin_three` で展開し、多項式恒等式として

$$\det J_F=-2$$

を証明しました。

これは特定の点での数値評価ではありません。三変数多項式として、変数依存がすべて相殺され、恒等的に定数 `-2` になることを示しています。

## 1.4. 有理数から複素数への構造輸送

複素版を大きな式のコピーとして作り直すことはしていません。

$$\mathbb Q\hookrightarrow\mathbb C$$

の係数埋め込みにより、

```text
有理多項式
→ 複素多項式

有理評価
→ 複素評価

有理形式偏微分
→ 複素形式偏微分

有理 determinant
→ 複素 determinant
```

をそれぞれ定理として輸送しました。

使用された中心 API は、評価の合成、`MvPolynomial.pderiv_map`、`RingHom.map_det` です。

## 1.5. Keller normalization

第一出力座標だけを `-1/2` 倍し、

$$\widetilde F=\left(-\frac12P,Q,R\right)$$

を定義しました。

正規化後の Jacobian も、スケール済み行列として仮定せず、正規化多項式を実際に `pderiv` して生成しています。

第一行のスケールを対角行列として分離し、

$$J_{\widetilde F}=D\,J_F$$

$$\det D=-\frac12$$

$$\det J_F=-2$$

から、

$$\det J_{\widetilde F}=1$$

を構造的に証明しました。

三点衝突はそのまま保存され、共通像は

$$\left(\frac18,0,0\right)$$

になります。

---

# 2. 数学的に明確となったこと

## 2.1. 局所非退化と大域的一意性は別の情報である

今回の最も重要な観測は、次の二つが同時に成立することです。

$$\det J_{\widetilde F}=1$$

$$\widetilde F(p_0)=\widetilde F(p_1)=\widetilde F(p_2)$$

determinant `1` は、各点で形式 Jacobian が非退化であるという局所情報です。

しかし三点衝突は、空間全体で入力住所を一意に復元できないという大域情報です。

したがって、今回の有限証明書は次を明確に分離しました。

```text
局所:
  微分可能な境界情報は失われていない

大域:
  入力住所の識別情報は失われている
```

## 2.2. 非単射性は明示的 witness で証明できる

非単射性を抽象的な存在定理として示したのではありません。

```text
p₀ ≠ p₁
F(p₀) = F(p₁)
```

という具体的 witness から、

```lean
¬ Function.Injective evalNormalizedCounterexampleC
```

を得ています。

さらに、左逆が存在すれば写像は単射になるため、

```lean
¬ ∃ G, Function.LeftInverse G evalNormalizedCounterexampleC
```

も証明されました。

これは「多項式逆写像が見つからない」という弱い主張ではありません。

**集合写像としての左逆すら存在しない**、という強い不可能性です。

## 2.3. 証明は有限の代数 certificate へ圧縮できる

この形式化に必要だった本質は、巨大な一般理論ではありませんでした。

```text
多項式の定義
形式偏微分
3×3 determinant
三点の正確評価
点の相異性
```

という有限データだけで、非単射性まで閉じることができました。

これは重大な数学的主張を監査するとき、まず「反証に必要な有限 certificate」を切り出すという方法が非常に強いことを示しています。

---

# 3. DkMath Cosmic Framework での解析

DkMath の基本語彙は、次の保存分解です。

$$\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}$$

$$\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}$$

今回の Jacobian 形式化では、この語彙が数値分解ではなく、**情報と住所の構造**として現れました。

## 3.1. 今回の対応辞書

### Core

この bridge での `Core` は、観測された出力点です。

```text
Core = output point
```

具体例では、

$$\operatorname{Core}=\left(\frac18,0,0\right)$$

です。

### Gap

`Gap` は、その Core を復元する入力住所です。

```text
Gap = input address
```

ここで Gap は「誤差」や「不足量」ではありません。

**観測結果だけからは見えなくなった、復元に必要な隠れた住所情報**です。

### RestoreRel

入力 Gap が本当に Core を復元するという証明関係を、

```lean
normalizedRestoreRelC core gap :=
  evalNormalizedCounterexampleC gap = core
```

と定義しました。

### GapCrystal

`GapCrystal` は、

```text
Core
Gap
その Gap が Core を復元する証明
```

を一つに束ねた証明付き構造です。

### CrystalWorld

すべての証明付き Core–Gap 対を集めた世界です。

Cosmic Framework 的には、これを「住所情報を失う前の完全世界」と読むことができます。

### forgetGap

`forgetGap` は、証明付き Core–Gap 対から Gap を捨てて Core だけを残す射影です。

```text
完全な Core–Gap 世界
→ 観測された Core 世界
```

これは、DkMath の反転射影・忘却射影の最小モデルになっています。

---

# 4. Gap が複数存在する構造とは何か

## 4.1. 一般数学では「fiber に複数の点がある」

写像 $F:X\to Y$ と出力 $c\in Y$ に対して、

$$F^{-1}(c)=\{x\in X\mid F(x)=c\}$$

を fiber と呼びます。

今回、

$$p_0,p_1,p_2\in\widetilde F^{-1}\left(\frac18,0,0\right)$$

であり、三点は相異なります。

したがって、この fiber には少なくとも三つの点があります。

## 4.2. DkMath では「正しい復元 Gap が複数ある」

DkMath の `UniqueGap` は、

```lean
∃! gap, RestoreRel core gap
```

という契約です。

つまり、一つの Core に対して、その Core を復元する Gap がただ一つ存在する、という条件です。

今回、

```text
p₀ は正しい Gap
p₁ も正しい Gap
p₀ ≠ p₁
```

が成立するため、

```lean
¬ UniqueGap normalizedRestoreRelC normalizedTargetC
```

となります。

これが **一意性解除** です。

## 4.3. 複数 Gap は「誤り」ではない

重要なのは、どちらか一方の Gap が誤っているわけではないことです。

両方とも証明書を持っています。

```text
Gap₁ + certificate₁
Gap₂ + certificate₂
Gap₁ ≠ Gap₂
```

したがって複数 Gap 構造とは、

> 一つの観測結果に対し、互いに異なる複数の正しい生成履歴・住所・復元候補が存在する構造

です。

これは単なる数値の重複ではなく、**観測射影によって履歴情報が失われた状態**です。

## 4.4. 忘却射影の非単射性

二つの異なる `GapCrystal` は、Gap を忘れると同じ Core になります。

したがって、

```lean
¬ Function.Injective forgetGap
```

が一般定理として証明されました。

これは Jacobian の特別な式に依存しません。

```text
同じ Core
+
異なる認証済み Gap
→ forgetGap は非単射
```

という、再利用可能な論理原理です。

---

# 5. GN / Cosmic Formula との接続

## 5.1. 標準 GN

DkMath の基本的な差冪構造は、

$$(t+h)^n-t^n=h\,GN_n(h,t)$$

です。

$GN_n$ は、差分から境界因子 $h$ を除いた有限差分核です。

## 5.2. 一般多項式への持ち上げ

今回、新たに一般多項式

$$p(T)=\sum_na_nT^n$$

に対して、

$$\operatorname{GNFiniteDifference}(p,h,t)=\sum_na_nGN_n(h,t)$$

を定義しました。

Lean は、

$$p(t+h)-p(t)=h\,\operatorname{GNFiniteDifference}(p,h,t)$$

を任意の可換環上で証明しました。

さらに体上で $h\ne0$ なら、

$$\frac{p(t+h)-p(t)}h=\operatorname{GNFiniteDifference}(p,h,t)$$

です。

## 5.3. この接続が意味するもの

Jacobian は局所微分情報を扱います。

GN は有限距離 $h$ における差分情報を扱います。

したがって、DkMath の観点では、

```text
GN:
  有限距離で住所がどのように変化するか

Jacobian:
  極限的な局所変化をどう観測するか

GapCrystal:
  その観測を通過した後も住所が一意に戻るか
```

という三層になります。

今回の形式化は、GN から Jacobian 反例を導出したわけではありません。

しかし、反例探索で中心となった「三次差分」「局所変化」「大域衝突」という構図を、一般多項式の有限差分 API として回収しました。

---

# 6. Cosmic Framework で新しく見えた構図

今回、Big / Body / Gap を情報構造として読む新しい候補が明確になりました。

```text
Big:
  Core・Gap・復元証明を保持した完全な CrystalWorld

Body:
  観測可能な Core と、そこへ至る評価関係

Core:
  実際に観測された出力

Beam:
  入力住所を Core へ運ぶ多項式評価・局所変化の経路

Gap:
  射影後には見えなくなる入力住所・生成履歴
```

この対応は、今回 `Big` / `Body` / `Beam` という名前で直接 Lean 定義されたものではありません。

しかし `GapCrystal`、`RestoreRel`、`forgetGap` の形式化によって、少なくとも次の骨格は厳密になりました。

```text
完全情報世界
→ 忘却射影
→ 観測 Core

異なる完全状態
→ 同じ観測 Core
→ 一意性解除
```

これは、DkMath Cosmic Framework を「量の余白」だけでなく、**情報の余白・住所の余白**へ拡張する入口です。

---

# 7. まだ見えていないこと

## 7.1. なぜこの具体式が現れたのか

Lean は、与えられた式が持つ性質を証明しました。

しかし、

```text
なぜこの式を思いつけるのか
どの構造から系統的に生成できるのか
どのパラメータ族の一例なのか
```

は証明していません。

反例生成アルゴリズムや探索空間の一般化は未着手です。

## 7.2. 複数 Gap を発生させる一般条件

現在の一般 API は、

```text
二つの異なる認証済み Gap があれば UniqueGap は破れる
```

という論理定理です。

しかし、

```text
どの多項式写像が複数 Gap を持つか
Jacobian 条件と fiber の大きさの関係
複数 Gap が生まれる最小次数・最小次元・最小構造
```

を分類する定理はありません。

## 7.3. 局所 Core から大域 Big を決める原理

今回の核心は、

```text
local determinant = 1
```

から、

```text
global unique address
```

が従わないことでした。

では、大域的一意性を保証するには、局所 Jacobian に何を加えればよいのか。

```text
properness
成長条件
無限遠での境界条件
fiber の有限性
degree / covering / monodromy 情報
```

などが候補になりますが、今回の Lean プロジェクトでは扱っていません。

DkMath 語彙なら、

> Core の完全性だけでは Big は閉じない。Beam と Gap の大域制御が必要である。

という段階です。

## 7.4. fiber の幾何学

三つの明示点は証明されましたが、

```text
この fiber に点が全部で何個あるか
他の出力点の fiber はどうなるか
衝突点の代数的・幾何学的意味
ramification や covering の構造
```

はまだ見えていません。

## 7.5. GN と Jacobian 反例の因果的接続

`GNFiniteDifference` は一般定理として完成しました。

しかし、

```text
GN 構造からこの反例式が必然的に生成される
GN の特定の保存則が複数 Gap を強制する
```

という因果的 theorem はありません。

現段階では、

```text
探索を支えた解釈
→ 一般有限差分 API として回収
```

までです。

## 7.6. `PrincipalPartCompletion` と高次元化

Laurent 主部補完の一般定理、高次元への恒等座標 padding は将来課題として保留されています。

## 7.7. 数学史・著者・外部評価

Lean が証明するのは表示された代数式です。

Lean は次を証明しません。

```text
誰が最初に発見したか
いつ発表されたか
査読・専門家評価がどう定着したか
数学史上どのように位置づけられるか
```

この信頼境界は、形式証明の強さを損なうものではありません。

むしろ、

```text
代数的真偽
歴史的帰属
社会的評価
```

を混ぜずに管理できることが、本プロジェクトの重要な成果です。

---

# 8. プロジェクトの価値

## 8.1. Breaking Math Verification

SNS や公開ノートに重大な数式が現れたとき、DkMath は次の流れを実行できます。

```text
主張を有限 certificate に分解
→ Lean 定義へ変換
→ 正確評価
→ 形式偏微分
→ determinant
→ 反例 witness
→ axiom audit
→ 公開 Demo
```

これは「AI が数学について語る」だけではありません。

**AI が実装計画を分解し、Codex が Lean コードを構築し、Lean kernel が最終的な真偽を裁く協働ワークフロー**です。

## 8.2. 再計算ではなく構造輸送

有理数から複素数、元の写像から正規化写像へ進む際、同じ大きな式を何度も展開していません。

```text
係数写像
評価可換性
偏微分可換性
determinant 可換性
行スケール
```

を証明して輸送しました。

この構造的証明は、単発の数値検算より再利用性と監査可能性が高いものです。

## 8.3. 具体例から一般 API へ

プロジェクトは反例 certificate だけで終了しませんでした。

具体的衝突から、

```text
UniqueGap
GapFiber
GapCrystal
forgetGap
```

を抽出し、さらに探索で使った差分構造から、

```text
GNFiniteDifference
```

を一般多項式 API として抽出しました。

```text
具体的事実
→ 抽象原理
→ 再利用可能なライブラリ
```

という DkMath の研究循環が実現しています。

---

# 9. 公開 theorem surface

主要な theorem は次です。

```lean
jacobianCounterexampleCertificateQ
jacobianCounterexampleCertificateC
normalizedJacobianCounterexampleCertificateC
jacobianDemoCertificateC
normalized_three_point_collision_C
evalNormalizedCounterexampleC_noLeftInverse
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
eval_add_sub_eval_eq_mul_GNFiniteDifference
differenceQuotient_eq_GNFiniteDifference
```

Demo 用の公開 alias は次です。

```lean
jacobianDemo_det_eq_one
jacobianDemo_three_point_collision
jacobianDemo_notInjective
jacobianDemo_noLeftInverse
jacobianDemo_target_notUniqueGap
jacobianDemoCertificateC
```

---

# 10. 信頼境界

完成証明書の axiom audit は、標準的な Lean / Mathlib 基礎依存だけを報告します。

```text
propext
Classical.choice
Quot.sound
```

次は含まれません。

```text
sorryAx
DkMath 固有 axiom
native_decide
外部 CAS の未検証証明書
determinant の仮定
collision の仮定
```

したがって、証明された代数的 certificate は Lean kernel が追跡できます。

---

# 11. プロモーション用要約

## 短い紹介文

DkMath Breaking Math Verification は、公開された三次元多項式写像を Lean 4 + Mathlib で独立検証したプロジェクトです。形式偏微分から Jacobian 行列を生成し、正規化後の determinant が恒等的に `1` であることを証明しました。同時に、三つの相異なる複素点が同じ出力へ写ることを正確に検証し、写像の非単射性と左逆不存在を kernel-checkable certificate として公開しています。

さらに DkMath は、この衝突を「一つの Core に複数の正しい Gap が対応する一意性解除」として一般化し、`UniqueGap`、`GapCrystal`、`forgetGap` を再利用可能な Lean API として抽出しました。

## 技術者向け紹介文

The project formalizes an explicit polynomial map using `MvPolynomial`, derives its Jacobian through `MvPolynomial.pderiv`, proves the determinant identity with `Matrix.det`, transports the complete certificate from `ℚ` to `ℂ`, and normalizes the first output coordinate to obtain determinant `1`. An explicit three-point fiber proves noninjectivity and rules out any set-theoretic left inverse. A separate dependent-type API captures the collision as failure of a unique restoring Gap.

## プロジェクトの主メッセージ

**局所的な完全保存は、大域的な住所の一意性を保証しない。**

Lean が証明したのは、まさにこの一点です。

そして DkMath が加えたのは、その現象を一つの例で終わらせず、

```text
Core
Gap
certificate
forgetful projection
```

という一般的な「一意性解除の術式」へ変換したことです。

---

# 12. Summit Frame

```text
Formal Jacobian determinant: 1
Explicit fiber size: at least 3
Injective: no
Set-theoretic left inverse: no
Unique restoring Gap: no
Lean sorryAx: none
DkMath-specific axioms: none
```

$$\boxed{\text{Local Core preserved. Global address uniqueness released.}}$$
