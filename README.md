# Project D.K. math

The result of "D." and Wise Wolf's experiment with new mathematical theories.

## Index

### Lean

独自視点の数論を Lean 形式化で証明していくサブプロジェクト

運用方法については [lean/README.md](./lean/README.md) を参照。

#### DkMath: Lean 4 数学ライブラリ

動的調和数論（Dynamic Harmonic Number Theory, DHNT）に焦点を当てた Lean 4 用数学ライブラリ。

詳細は [dk_math/README.md](./lean/dk_math/README.md) を参照。

## Project

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

## License

This project is licensed under the MIT License. See the [LICENSE](./LICENSE) file for details.

## Contributing

Contributions are welcome! Please read the [CONTRIBUTING.md](./CONTRIBUTING.md) file for guidelines.

## Contact

For questions or suggestions, please contact D. or Wise Wolf. (It's still a secret for now)

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
