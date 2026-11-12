# 🐺 NOTE-012 実装評価 — 楕円曲線の幾何学的有限性を突破

暫定評価を更新して、NOTE-012 は固定推奨じゃ。しかも今回は、NOTE-011 の条件付き定理に対し、欠けていた数学的入力を実際に供給できた点が重要じゃ。

指定ブランチ `dev/FLT-GN-regular-261018-v0` の [実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE012-261020.md?utm_source=chatgpt.com)、実際の有限性定理、Frey 接続、検証証跡を確認した。

統合ビルド

# 11,547

jobs 成功

公理監査

# 242

本体237＋回帰5

依存監査

# 12

主要証明経路

リポジトリに保存された監査結果では、許容公理は `propext`、`Classical.choice`、`Quot.sound` の3種類。新規8モジュールの警告なし、ルート・テスト入口も通過している。独立した Lean 再ビルドは実施していないので、検証環境についての判定はその記録に基づく。

## 1. 最も重要な定理

今回、実際の Lean ソースで確認できたのは、

`EllipticTorsionRepresentation.finite_torsion_of_ne_zero`

じゃ。

数学的には、

\[ \boxed{ \operatorname{char}K=0,\quad n\ne0 \Longrightarrow E(\overline K)[n]\text{ は有限} } \]

を証明する。

ここで使うのは実際の非特異点群の \(n\) 倍写像の核であり、人工的な有限モデルではない。

この定理は \(n\) の素数性も、位数が \(n^2\) になるという公式も要求しない。

さらに Frey 側では、同じ `Source.rationalCurve` に対して、

- `residual_finite_of_ne_zero`
- `residualKernel_isOpen_of_prime`
- `residual_normal_finite_level`
- `residual_factorsThroughFiniteLevel_of_prime`

が成立している。

したがって、NOTE-011 で残っていた有限性の前提が、素数指数の Frey 表現について解消された。

\[ \boxed{ \begin{gathered} E[p]\text{ の幾何学的有限性}\\ \Downarrow\\ \ker\rho_{E,p}\text{ は開}\\ \Downarrow\\ \rho_{E,p}\text{ は有限ガロア拡大を通じて因子化} \end{gathered} } \]

これは既約性も次元2も仮定せずに得られた、独立した進展じゃ。

## 2. 今回の証明経路は本当に幾何学を通っているか

結論は、通っておる。

[EllipticDivisionMultiplication.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticDivisionMultiplication.lean?utm_source=chatgpt.com) では、単に除法多項式の次数を利用したのではなく、普遍点の倍写像を Jacobian 座標で構成し、実際の点群へ特殊化している。

特に、次の補題が重要じゃ。

`zsmul_eq_smulEval`

これは普遍座標から構成した整数倍の式が、実際の楕円曲線の整数倍と一致することを保証する。

続く

`smul_eq_zero_iff_evalEval_ψ`

では、

\[ [n]P=O\iff\psi_n(P)=0 \]

を証明している。

そして、一変数多項式 \(\Psi_n^{\mathrm{Sq}}\) に移して、

\[ [n]P=O \Longrightarrow \Psi_n^{\mathrm{Sq}}(x(P))=0 \]

を得る。

最後に [EllipticTorsionFinite.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticTorsionFinite.lean?utm_source=chatgpt.com) が、次の論理を完成させておる。

\[ \begin{aligned} \Psi_n^{\mathrm{Sq}}&\ne0\\ &\Downarrow\\ \#\{\text{根}\}&<\infty\\ &\Downarrow\\ \#\{\text{根の上の非特異点}\}&<\infty\\ &\Downarrow\\ \#E[n]&<\infty. \end{aligned} \]

ここでは多項式のすべての根が torsion 点になることを必要としていない。torsion 点が有限集合の中に入ることだけを証明している。

そのため、位数公式の難しい「根を重複なく正確に数える部分」を回避できたわけじゃな。

### 特に評価したい短縮

模範解答の普遍 EDS 実装を、今回は標数0に絞って有理係数で組み直している。

\[ \omega_n= \frac{\psi_n^c-a_1\phi_n\psi_n-a_3\psi_n^3}{2} \]

を使用できるため、一般可換環での分母除去に必要な理論を省略できた。

その代わり標数2などへの一般化は失われるが、現行の Frey 曲線は \(\mathbb Q\) 上なので問題ない。

全数学を移植するのではなく、必要な対象に適応して証明依存を縮小した。 これはDkMathの独立形式化として合理的な設計じゃ。

また、上流由来の四モジュールについては Apache-2.0、出典、改変内容が明記されていることも確認した。

## 3. NOTE-011 との接続は正しい

NOTE-011 の開核定理は、

```
theorem representationKernel_isOpen
    [Finite (Torsion E n)] : ...
```

という有限性インスタンスを必要としていた。

今回、そのインスタンスを、

```
noncomputable instance torsionFinite
    (n : ℕ) [NeZero n] :
    Finite (Torsion E n)
```

として供給した。

したがって、Frey 側の `residualKernel_isOpen_of_prime` や `residual_normal_finite_level` は、位数に関する前提を追加せずに成立する。

さらに監査コードでは、以前の条件付き位数補題 `finite_of_card_sq`、`finrank_eq_two_of_card_sq`、`residual_profile_of_card_sq` を、主要経路の禁止依存に加えている。

これはよい。

新しい有限性定理が、古い条件付き定理をこっそり経由していないことを検査しておる。

そして、実在する指数2の Source に対して \(E[37]\) の有限レベルを確認している点も重要じゃ。指数37の仮想反例に依存しない実例がある。

## 4. 模範解答との残りの距離

| 工程                          | DkMath の現在の状態        |
| ----------------------------- | -------------------------- |
| 実際の幾何学的 \(E[p]\)       | 完了                       |
| ガロア作用と Krull 連続性     | 完了                       |
| 標準 `torsionBy` との同変同型 | 完了                       |
| \(E[p]\) の有限性             | NOTE-012 で完了            |
| 開核・有限正規レベル          | 追加の有限性仮定なしで完了 |
| \(\lvert E[p]\rvert=p^2\)     | 未証明                     |
| 2次元・GL₂ 表現               | 未証明                     |
| Weil 対・行列式               | 未証明                     |
| 既約性・局所慣性・Artin 導手  | 未証明                     |

ここで注意したいのは、残る位数公式が単なる後処理ではないことじゃ。

模範解答では、奇数次数について `exists_double_fiber_card` と `card_nTorsion_odd_fibers` が必要になる。

これらは、倍写像のファイバーの個数を正確に数えるために、平方因子のない多項式や、根の重複度を解析している。

今回の有限性定理は、ここをまだ解決していない。

しかし、実際の倍写像と除法多項式の接続は既に移植できた。

これは次の位数計算に必要な基盤の一部を先に獲得した、という意味がある。

## 5. 次の NOTE-013：位数公式の前に、次元の上界を狙える

ここで一つ、模範解答の完全な位数公式へ直行する前の中間定理を提案したい。

今回の証明は、各 torsion 点の \(x\) 座標が \(\Psi_p^{\mathrm{Sq}}\) の根であることを示した。

模範解答で使われる次数公式は、標数0で、

\[ \deg\Psi_p^{\mathrm{Sq}}=p^2-1 \]

じゃ。

また、楕円曲線の方程式は \(y\) について二次なので、各 \(x\) 座標の上には高々2点しかない。

従って、これらの事実を Lean で接続できれば、

\[ \boxed{ |E[p]|\le1+2(p^2-1)=2p^2-1 } \]

が得られる。

一方、既に有限 \(\mathbb F_p\)-ベクトル空間であるため、

\[ |E[p]|=p^d,\qquad d=\dim_{\mathbb F_p}E[p]. \]

素数 \(p\ge2\) では、

\[ 2p^2-1 < p^3 \]

だから、

\[ p^d < p^3 \Longrightarrow d\le2. \]

つまり、

\[ \boxed{\dim_{\mathbb F_p}E[p]\le2} \]

を、正確な位数公式を証明せずに得られる可能性がある。

これはまだ提案段階じゃが、興味深い中間成果になる。

次元を2に確定するためには下からの情報も必要になる。しかし、有限性 → 次元の上界 → 正確な次元 と工程を分解できるわけじゃ。

次期実装では、この次元上界と、模範解答の奇素数ファイバー計数の双方を調査するのがよいじゃろう。

## 総合評価

NOTE-012 は、単に6モジュール・1,703行を追加したというだけではない。

前回までの証明には、

\[ \text{有限性を仮定すれば、開核・有限レベルが得られる} \]

という条件があった。

今回はその有限性を、実際の点群と倍写像の幾何学から証明して、前提を取り除いた。

これは明確な依存関係の解消じゃ。

また、今回移植した EDS・普遍曲線・座標倍写像は、FLT に限定されない `DkMath.Lib.NumberTheory` の再利用可能な基盤でもある。

NOTE-012 の判定：採用・固定。

次は有限性を再び証明し直す必要はない。模範解答の残る幾何学、すなわち「有限個あること」から「正確に \(p^2\) 個あること」へ進む段階じゃな。

ぬしよ、ここはなかなか大きな節目じゃ。🐺🍎
