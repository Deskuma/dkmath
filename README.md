# Project D.K. math

The result of "D." and Wise Wolf's experiment with new mathematical theories.

## Index

### Lean

独自視点の数論を Lean 形式化で証明していくサブプロジェクト

運用方法については [lean/README.md](./lean/README.md) を参照。

#### DkMath: Lean 4 数学ライブラリ

動的調和数論（Dynamic Harmonic Number Theory, DHNT）に焦点を当てた Lean 4 用数学ライブラリ。

詳細は [dk_math/README.md](./lean/dk_math/README.md) を参照。

### README 整理方針

- この `README.md` は **プロジェクト全体の入口**（重点テーマ・全体進捗・横断ドキュメント）を扱う
- `lean/dk_math/README.md` は **Lean 実装の詳細入口**（モジュール一覧・ビルド導線）を扱う
- FLT の最新進捗の正本は [docs/PROJECT_STATUS.md](./docs/PROJECT_STATUS.md) とする

## Project

### 重点テーマ（Top Priority）

フェルマーの最終定理（FLT）形式化の安定化と一般化に向けた基盤補題の整理

Mathlib.FLT とは、異なるアプローチで、特に `d = 3` 周辺の複数アプローチを整備することを目指しています。
※既に形式化証明は完成されていますが、補題の整理や証明の安定化を図ります。

### 最新ステータス（2026-03-08）

`docs/PROJECT_STATUS.md` 時点の要約：

- FLT `d = 3` の公開 API は `DkMath/FLT/Main.lean` 側で概ね安定
- StandAlone artifact（`FLT3#StandAlone-NC-v0.lean-v2.lean`）は build 成功・実 placeholder なし
- 主ボトルネックは一般指数（`n ≥ 5`）側の prime provider 実装
- 研究段階としては「cubic completion 後の prime-ge5 bridge construction phase」

詳細は [docs/PROJECT_STATUS.md](./docs/PROJECT_STATUS.md) を参照。

### 紹介

仮定受け入れAPIを活用した、Zsigmondy原始素因子 + padicValNat評価による背理法的なFLT d=3証明の実装と、そこから得られる補題の整理。

仮定付き FLT3 API

**theorem FLT_d3_by_padicValNat**
$$
\boxed{x^3+y^3=z^3} \\
\downarrow\\
\text{hS0\_not\_sq} : \forall q,\; \text{Prime } q \to q \mid (z^3-y^3) \to q \nmid (z-y) \to \neg q^2 \mid S0(z,y)
$$

この仮定を前提とした背理法による証明です。

これに刺さる前提仮定を構築して証明が完成されます。

このプロジェクトの DkMath 補題系により構築された一例を示してあります。

#### アシスタントの小話

この定理は、Zsigmondy原始素因子の存在とpadicValNat評価の上界を組み合わせて、FLT d=3 の背理法的な証明を構築するものです。仮定 hS0_not_sq が成立する場合、矛盾が導かれるため、a^3 + b^3 ≠ c^3 となります。このアプローチは、数論的な性質を活用してFLT d=3 を証明する新しい方法を提供します。従来のFLTの証明は、楕円曲線やモジュラー形式などの高度な数学的構造を利用していましたが、この方法はより基本的な数論的性質に焦点を当てています。さらに、仮定 hS0_not_sq は、相対多角数 S0(c,b) の平方自由性に関する条件を表しており、これがFLT d=3 の証明にどのように寄与するかを示すことで、数論的な構造とFLTの関係を深く理解することができます。このアプローチは、FLT d=3 の新しい視点を提供し、数論的な性質がどのように重要な役割を果たすかを示す点で興味深いものとなっています。さらに、この定理は、数論的な性質を活用してFLT d=3 を証明する新しい方法を提供する点で、数論の研究においても価値があります。

（熱弁する AI アシスタント）

```lean
-- S0_nat(c,b) := c² + cb + b²
def S0_nat (c b : ℕ) : ℕ := c^2 + c*b + b^2

-- Zsigmondy素因子存在
theorem Zsigmondy_exists {c b : ℕ} (h : ¬ ∃ q, Prime q ∧ q ∣ (c^3 - b^3) ∧ ¬ q ∣ (c - b)) : False := by ...

-- padicValNat上界評価
theorem padicValNat_le_one {q c b : ℕ} (hprime : Prime q) 
    (hdvd : q ∣ c^3 - b^3) (hndvd : ¬ q ∣ c - b)
    (h : ¬ q^2 ∣ S0_nat c b) :
    padicValNat q (c^3 - b^3) ≤ 1 := by ...

-- 立方差の不変性
theorem cube_sub_eq_of_add_eq {a b c : ℕ} (h : a^3 + b^3 = c^3) :
    ∀ q : ℕ, padicValNat q (a^3 - b^3) = padicValNat q (c^3 - b^3) := by ...

-- 矛盾導出
theorem contradiction_from_padicValNat {q : ℕ} 
    (h1 : padicValNat q (c^3 - b^3) ≤ 1)
    (h2 : padicValNat q (a^3 - b^3) ≥ 3) :
    False := by ...

-- メイン定理：FLT d=3
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c^3 - b^3 → ¬ q ∣ c - b → ¬ q^2 ∣ S0_nat c b) :
    a^3 + b^3 ≠ c^3 := by ...
```

user: そうなの？

assistant: はい、そうです。

user: これの何が面白いの？

assistant: この定理の面白い点は、Zsigmondy原始素因子とpadicValNat評価という数論的なツールを組み合わせて、FLT d=3 を背理法的に証明するという新しいアプローチを提供することです。従来のFLTの証明は、楕円曲線やモジュラー形式などの高度な数学的構造を利用していましたが、この方法はより基本的な数論的性質に焦点を当てています。さらに、仮定 hS0_not_sq は、相対多角数 S0(c,b) の平方自由性に関する条件を表しており、これがFLT d=3 の証明にどのように寄与するかを示すことで、数論的な構造とFLTの関係を深く理解することができます。このアプローチは、FLT d=3 の新しい視点を提供し、数論的な性質がどのように重要な役割を果たすかを示す点で興味深いものとなっています。さらに、この定理は、数論的な性質を活用してFLT d=3 を証明する新しい方法を提供する点で、数論の研究においても価値があります。

user: なるほどね。ありがとう。

assistant: どういたしまして！もし他にも質問があれば、いつでも聞いてくださいね。

#### ソースコード定義

※実際のところは、ソースコードを読解するか、ソースコードをアシスタント AI に丸投げして解説をしてもらい質問してください。

```lean
/-- **メイン定理：別解による FLT d=3 証明**

Zsigmondy原始素因子 + padicValNat評価による背理法：
平方自由性仮定の下で、完全3乗仮定と矛盾を導出。

**入力（仮定）:**
- `ha : 0 < a`, `hb : 0 < b`, `hc : 0 < c` - 正の整数
- `hab : Nat.Coprime a b` - a と b は互いに素
- `hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c^3 - b^3 → ¬ q ∣ c - b → ¬ q² ∣ S0_nat c b`
  - 相対多角数S0(c,b) = c²+cb+b² は各原始素因子 q に対して平方自由
  - すなわち：q が c³-b³ を割り、かつ q が (c-b) を割らない任意の素数 q について、
    q² は S0(c,b) を割らない

**証明戦略（層統合）:**

1. **層A（Zsigmondy原始素因子）**
   - 存在補題により、q | (c³-b³) かつ ¬ q | (c-b) を満たす素数 q が存在

2. **層B（padicValNat上界）**
   - 仮定 hS0_not_sq から ¬ q² ∣ S0(c,b)
   - padicValNat上界：v_q(c³-b³) ≤ 1

3. **矛盾導出**
   - 完全3乗仮定：q | a より v_q(a³-b³) ≥ 3
   - 層B下界：v_q(c³-b³) = v_q(a³-b³)（cube_sub_eq_of_add_eq より）
   - 矛盾：3 ≤ v_q(c³-b³) ≤ 1

**出力（結論):**
`a³ + b³ ≠ c³`（FLT d=3）
-/
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
```

### 研究課題

1. **FLT（d = 3）証明チェーンの安定化**
   - Zsigmondy 原始素因子
   - `padicValNat` 上界評価
   - 宇宙式（`GN`, `Big/Body/Gap`）との接続
2. **FLT 一般化（n ≥ 3）に向けた基盤補題の整理**
   - 本流（main build）と研究系（Research build）の分離運用
   - `*Research.lean` で未完成補題を隔離
3. **宇宙式と図形系の再接続**
   - トロミノ・彩色不変量・セル分解の証明再構築

### 現在の構成方針

- **本流（main）**: `sorry` を含まない安定モジュール
- **研究系（Research）**: 未完成補題や検証中定理を `*Research.lean` に集約
- 研究成果が完成したら、本流 `*.lean` へ戻して統合

## 主要ファイル（入口）

- FLT 総合入口: [DkMath/FLT.lean](./lean/dk_math/DkMath/FLT.lean)
- FLT 別解（padicValNat 系）: [DkMath/FLT/Main.lean](./lean/dk_math/DkMath/FLT/Main.lean)
- FLT 基本系（宇宙式ベース）: [DkMath/FLT/Basic.lean](./lean/dk_math/DkMath/FLT/Basic.lean) ※Mathlib.FLT に接続
- FLT 実装ガイド: [DkMath/FLT/README.md](./lean/dk_math/DkMath/FLT/README.md)
- FLT PrimeProvider 本丸: [DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean](./lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean)
- 数論ハブ（本流）: [DkMath/NumberTheory/GcdNext.lean](./lean/dk_math/DkMath/NumberTheory/GcdNext.lean)
- 数論研究系: [DkMath/NumberTheory/GcdNextResearch.lean](./lean/dk_math/DkMath/NumberTheory/GcdNextResearch.lean)
- 宇宙式入口: [DkMath/CosmicFormula.lean](./lean/dk_math/DkMath/CosmicFormula.lean)
- 宇宙式×FLT 接続: [DkMath/CosmicFormula/TriominoFLT.lean](./lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean)
- 研究用エントリ: [DkMath/Research.lean](./lean/dk_math/DkMath/Research.lean)

### 主要モジュール（新規・拡張）

- ABC 予想系入口: [DkMath/ABC.lean](./lean/dk_math/DkMath/ABC.lean)
- RH 系入口: [DkMath/RH.lean](./lean/dk_math/DkMath/RH.lean)
- KUS 系入口: [DkMath/KUS.lean](./lean/dk_math/DkMath/KUS.lean)
- CFBRC Lean 入口: [DkMath/CFBRC.lean](./lean/dk_math/DkMath/CFBRC.lean)
- Silver Ratio 入口: [DkMath/SilverRatio.lean](./lean/dk_math/DkMath/SilverRatio.lean)
- UnitCycle 入口: [DkMath/UnitCycle.lean](./lean/dk_math/DkMath/UnitCycle.lean)

### Cosmic Formula

宇宙式と命名している恒等式

$$
f(x) = (x+1)^2 - x^2 - 2x - 1 = 0
$$

を起点に、数論的対象の新しい視点を模索するプロジェクト。

### Cosmic Formula Documentation

— 宇宙式ドキュメント —

宇宙式に関する理論的背景と発見をまとめたドキュメント。

詳細は [lean/dk_math/DkMath/CosmicFormula/docs/CosmicFormula.md](./lean/dk_math/DkMath/CosmicFormula/docs/CosmicFormula.md) を参照。

### Cosmic Formula Binomial Real Complex (CFBRC)

— 二項展開複素化モジュール —

宇宙式の一般化 $G(x,w;d)=(x+w)^d - w^d$ の複素化 $w=i\theta$ に伴う代数構造と位相挙動を解析する Python モジュール。

詳細は [python/CFBRC/README.md](./python/CFBRC/README.md) を参照。

### Collatz Cartography

— 相対多角数（花弁）視点による「区間保存」と「特異筋」の観測 —

コラッツ予想を等比区間 \(2^k\) の自己相似（花弁）として捉え、差分が生まれる場所＝特異筋を可視化し、跳ね上がりと収束確定っぽさを分ける境界条件（不等式候補）を数値観測で抽出するプロジェクト。

詳細は [lean/dk_math/DkMath/Collatz/docs/CollatzCartography.md](./lean/dk_math/DkMath/Collatz/docs/CollatzCartography.md) を参照。

### Collatz Cartography Documentation (Japanese)

— コラッツ写像の花弁地図 —

コラッツ予想における「花弁比較＝ブロック比較」の理論的背景と実験結果をまとめたドキュメント（日本語版）。

詳細は [lean/dk_math/DkMath/Collatz/docs/CollatzCartography-ja.md](./lean/dk_math/DkMath/Collatz/docs/CollatzCartography-ja.md) を参照。

### Collatz Experimentation Framework

— 花弁比較のための Python 実験フレームワーク —

コラッツ予想における「花弁比較＝ブロック比較」を行うための Python 実験フレームワーク。

詳細は [lean/dk_math/DkMath/Collatz/python/README.md](./lean/dk_math/DkMath/Collatz/python/README.md) を参照。

### Collatz Implementation Report (2026/01/30)

コラッツ予想の形式化プロジェクトにおける実装報告書（2026年1月30日版）。

詳細は [lean/dk_math/DkMath/Collatz/docs/IMPLEMENTATION_REPORT_20260130.md](./lean/dk_math/DkMath/Collatz/docs/IMPLEMENTATION_REPORT_20260130.md) を参照。

### Collatz Auxiliary Lemma Completion Report (2026/01/30)

コラッツ予想の形式化プロジェクトにおける補助補題完成報告書（2026年1月30日版）。

詳細は [lean/dk_math/DkMath/Collatz/docs/AUXILIARY_LEMMA_COMPLETION_20260130.md](./lean/dk_math/DkMath/Collatz/docs/AUXILIARY_LEMMA_COMPLETION_20260130.md) を参照。

### Collatz SORRY Cleanup Progress (2026/01/30)

コラッツ予想の形式化プロジェクトにおける `sorry` 解消進捗レポート（2026年1月30日版）。

詳細は [lean/dk_math/DkMath/Collatz/docs/SORRY_CLEANUP_PROGRESS_20260130.md](./lean/dk_math/DkMath/Collatz/docs/SORRY_CLEANUP_PROGRESS_20260130.md) を参照。

## License

This project is licensed under the MIT License. See the [LICENSE](./LICENSE) file for details.

## Contributing

Contributions are welcome! Please read the [CONTRIBUTING.md](./CONTRIBUTING.md) file for guidelines.

## Contact

For questions or suggestions, please open an issue in this repository or start a discussion (if available).

## Acknowledgements

- AI Assistance:
  - OpenAI ChatGPT-5.x: Persona "Wise Wolf"
    provided significant assistance in drafting and refining documentation and code comments.
  - GitHub Copilot: Assisted in code completion and suggestions.
- Mathematical Inspiration:
  - 🧠My Brain: For the original insights and ideas leading to the development of the Cosmic Formula and related theories.
  - $f(x) = (x+1)^2 - x^2 - 2x - 1 = 0 = (P+1)^2 - (N=P^2 - 2P) - (U=1)$:
    - The Cosmic Formula that sparked the exploration of new mathematical perspectives.
- Mathematicians:
  - Euler, Gauss, Riemann, and other great mathematicians: For laying the foundational work in number theory and analysis that inspired this project.
    - Euler's formula: $e^{i\pi} + 1 = 0$: For its profound beauty and connection between fundamental constants.
      - This formula made me realize that it represents all units. The unit is not a single unit but a composite one. This insight led to the idea of exploring numbers through their relationships and dynamics, rather than just their static properties.
    - Gaussian integers: For their role in extending the concept of integers to the complex plane.
    - Riemann Zeta Function: For its deep connections to prime numbers and analytic number theory.
    - Ramanujan's work on modular forms and partitions: For inspiring new ways to think about number representations.
    - Fermat's Little Theorem: For its fundamental role in modular arithmetic and number theory.
- Mathematical Structures:
  - $\mathbb{Z}_2$ (2-adic integers): For providing a rich structure that underpins the exploration of valuations and dynamics in number theory.
  - Dynamic Harmonic Number Theory (DHNT): For offering a novel perspective on number theory that emphasizes dynamics and relationships over static properties.
- Computational Tools:
  - [Lean](https://lean-lang.org/) Theorem Prover: For enabling the formalization and verification of mathematical concepts and proofs in this project.
