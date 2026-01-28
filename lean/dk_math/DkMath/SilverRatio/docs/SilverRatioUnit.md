# 白銀単位（Silver Ratio Unit）

docs/SilverRatioUnit.md

## 0. 概要

本ドキュメントは **白銀単位（Silver Ratio Unit）** を用いた 2 成分代数（`Ag a b = a + b*uAg`）を、Lean 4 + mathlib 上で形式化した成果を整理するものです。

中心となる主張は次の 3 つです。

1. **白銀単位の閉包（余白の定数化）**  
   白銀単位 \(u_{\rm Ag}\) は
   \[
   u_{\rm Ag}^2 = u_{\rm Ag} + \frac14
   \]
   を満たし、ギャップ \(\Delta_{\rm Ag} := u_{\rm Ag}^2 - u_{\rm Ag}\) は常に \(\frac14\) に固定されます。

2. **2 成分表現の閉包（積の混合項）**  
   任意の \(a,b,c,d\in\mathbb{R}\) について
   \[
   (a + b u_{\rm Ag})(c + d u_{\rm Ag})
   = \Bigl(ac + \frac{bd}{4}\Bigr) + \Bigl(ad + bc + bd\Bigr)u_{\rm Ag}
   \]
   が成り立ち、基底 \(\{1,u_{\rm Ag}\}\) に関して積が閉じます。

3. **共役・ノルム・逆元、そしてノルムの乗法性**  
   共役 \(u_{\rm Ag}\mapsto 1-u_{\rm Ag}\) を導入すると、ノルムが閉形式で与えられ、
   逆元公式およびノルムの乗法性
   \[
   N(xy)=N(x)N(y)
   \]
   が Lean 上で証明されます。

これにより、白銀単位世界は「余白が \(\frac14\) に定数化された 2 次代数」として、計算規則・幾何（零集合の平方完成）・指数リンク（\(e/4\)）まで含めて定理群として保存されます。

---

## 1. 定義（数学）

### 1.1 白銀数と白銀単位

- 白銀数（silver ratio）
  \[
  \sigma := 1 + \sqrt{2}
  \]
- 白銀単位（Silver Ratio Unit）
  \[
  u_{\rm Ag} := \frac{\sigma}{2} = \frac{1+\sqrt{2}}{2}
  \]

### 1.2 余白（ギャップ）

- 白銀余白
  \[
  \Delta_{\rm Ag} := u_{\rm Ag}^2 - u_{\rm Ag}
  \]
- ギャップ関数（宇宙式語彙との整合用）
  \[
  \mathrm{Gap}(u) := u^2 - u
  \]

白銀単位では
\[
\Delta_{\rm Ag} = \mathrm{Gap}(u_{\rm Ag}) = \frac14
\]
が成立します。

### 1.3 2 成分表現（Ag）

- 2 成分表現
  \[
  Ag(a,b) := a + b\,u_{\rm Ag}
  \]
- 混合項（積で現れる “余白由来” の項）
  \[
  \mathrm{mixTerm}(b,d) := bd
  \]

### 1.4 共役（Conjugation）とノルム（Norm）

共役は \(u_{\rm Ag}\mapsto 1-u_{\rm Ag}\) により定めます。

- 共役（Ag 版）
  \[
  AgConj(a,b) := a + b(1-u_{\rm Ag})
  \]
- ノルム
  \[
  AgNorm(a,b) := Ag(a,b)\,AgConj(a,b)
  \]

---

## 2. 主結果（定理一覧）

以下は Lean 上で証明済みのコア定理群です。括弧内は対応する Lean 名（代表例）です。

### 2.1 白銀単位の閉包と余白

- **白銀単位の閉包則**
  \[
  u_{\rm Ag}^2 = u_{\rm Ag} + \frac14
  \]
  （`uAg_sq_eq`）

- **余白の定数化**
  \[
  u_{\rm Ag}^2 - u_{\rm Ag} = \frac14
  \]
  （`uAg_sq_sub_uAg`）

- **白銀余白の定数化**
  \[
  \Delta_{\rm Ag} = \frac14
  \]
  （`ΔAg_eq`）

- **ギャップ関数の評価**
  \[
  \mathrm{Gap}(u_{\rm Ag}) = \frac14
  \]
  （`Gap_uAg`）

- **語彙統一：ギャップ＝白銀余白**
  \[
  \mathrm{Gap}(u_{\rm Ag}) = \Delta_{\rm Ag}
  \]
  （`Gap_uAg_eq_ΔAg`）

### 2.2 2 成分表現の積と混合項

- **基底 \(\{1,u_{\rm Ag}\}\) による積の閉包**
  \[
  Ag(a,b)\,Ag(c,d)
  = Ag\Bigl(ac + \frac{bd}{4},\ ad + bc + bd\Bigr)
  \]
  （`Ag_mul`）

- **混合項の明示（読み物向け）**
  \[
  Ag(a,b)\,Ag(c,d)
  = Ag\Bigl(ac + \frac{\mathrm{mixTerm}(b,d)}{4},\ ad + bc + \mathrm{mixTerm}(b,d)\Bigr)
  \]
  （`Ag_mul_mixTerm`）

### 2.3 共役・ノルム・逆元

- **共役の簡約形**
  \[
  AgConj(a,b) = (a+b) - b\,u_{\rm Ag}
  \]
  （`AgConj_eq`）

- **共役の involution（座標表現）**
  \[
  AgConj(a+b,-b) = Ag(a,b)
  \]
  （`AgConj_invol`）

- **ノルムの閉形式（最重要）**
  \[
  AgNorm(a,b) = a^2 + ab - \frac{b^2}{4}
  \]
  （`AgNorm_eq`）

- **ノルムはスカラー（\(u_{\rm Ag}\) 成分を持たない）**
  \[
  \exists r\in\mathbb{R},\ AgNorm(a,b)=r
  \]
  （`AgNorm_is_scalar`）

- **逆元公式（右逆・左逆）**  
  \(AgNorm(a,b)\neq 0\) のとき
  \[
  Ag(a,b)^{-1} = \frac{AgConj(a,b)}{AgNorm(a,b)}
  \]
  （`Ag_inv`）

  また
  \[
  Ag(a,b)\cdot \frac{AgConj(a,b)}{AgNorm(a,b)} = 1,\qquad
  \frac{AgConj(a,b)}{AgNorm(a,b)}\cdot Ag(a,b) = 1
  \]
  （`Ag_mul_AgConj_div_AgNorm`, `AgConj_div_AgNorm_mul_Ag`）

### 2.4 ノルム零集合の幾何（平方完成）

- **零集合の同値（閉形式）**
  \[
  AgNorm(a,b)=0 \iff a^2 + ab - \frac{b^2}{4}=0
  \]
  （`AgNorm_eq_zero_iff`）

- **零集合の同値（平方完成）**
  \[
  AgNorm(a,b)=0 \iff \Bigl(a+\frac{b}{2}\Bigr)^2 = \frac{b^2}{2}
  \]
  （`AgNorm_eq_zero_iff_sq`）

### 2.5 ノルムの乗法性（完成形）

- **ノルムの乗法性（ペア形式）**  
  積の係数
  \[
  (a,b)\cdot(c,d) :=
  \Bigl(ac+\frac{bd}{4},\ ad+bc+bd\Bigr)
  \]
  に対して
  \[
  AgNorm\Bigl(ac+\frac{bd}{4},\ ad+bc+bd\Bigr)=AgNorm(a,b)\,AgNorm(c,d)
  \]
  （`AgNorm_mul`）

---

## 3. 指数リンク（\(e/4\) とギャップ）

- **指数—ギャップ分解**
  \[
  \frac{e}{4} = e\,\mathrm{Gap}(u_{\rm Ag})
  \]
  ただし \(e := \exp(1)\)。  
  （`e_div_four_eq_e_mul_Gap_uAg`）

この等式は、白銀単位世界の「定数余白 \(\frac14\)」が、指数定数 \(e\) と直接結びつく形で表現できることを示します。

---

## 4. Lean 実装メモ（構成）

本形式化は `namespace DkMath.SilverRatioUnit`（例）下に整理し、概ね以下のブロックで構成します。

1. **基礎定義**
   - `sqrt2`, `sigma`, `uAg`
2. **補助補題**
   - `sqrt2_sq`, `sqrt2_pos`, `sqrt2_ne_zero`, `sqrt2_irrational`
   - 分母有理化・平方など（必要に応じて）
3. **白銀閉包**
   - `uAg_sq_eq`, `uAg_sq_sub_uAg`, `ΔAg`, `Gap`, `Gap_uAg`
4. **Ag 代数**
   - `Ag`, `mixTerm`, `Ag_mul`, `Ag_mul_mixTerm`
5. **共役・ノルム・逆元**
   - `AgConj`, `AgNorm`, `AgConj_eq`, `AgNorm_eq`, `Ag_inv`
   - 右逆・左逆
6. **幾何**
   - `AgNorm_eq_zero_iff`, `AgNorm_eq_zero_iff_sq`
7. **ノルム乗法性**
   - `AgNorm_mul`
8. **まとめ定理（README 用）**
   - `SilverRatioUnit_core_summary` 等

---

## 5. 直観（短い解説）

### 5.1 “余白の定数化” と \(3+1=4\)

白銀単位は二次閉包により
\[
u_{\rm Ag}^2 = u_{\rm Ag} + \frac14
\]
となり、二乗で混合しても必ず「一次成分＋定数余白」に戻ります。  
この「必ず残る \(\frac14\)」が白銀単位世界のギャップです。

### 5.2 “混合項” の必然性

一般の \(a+b u_{\rm Ag}\) の積では \(bdu_{\rm Ag}^2\) が現れますが、  
\(u_{\rm Ag}^2\) は一次＋定数に還元されるため、結果として

- 定数側に \(\frac{bd}{4}\)
- \(u_{\rm Ag}\) 側に \(bd\)

が必ず混入します。これが `mixTerm(b,d)=bd` の意味です。

### 5.3 ノルムによる “実数化（潰し）”

共役を掛けると \(u_{\rm Ag}\) 成分が相殺され、ノルムは純粋な実数（二次式）になります：
\[
AgNorm(a,b)=a^2+ab-\frac{b^2}{4}.
\]
この “潰し” が逆元公式と乗法性を支えます。

---

## 6. 今後の拡張案（任意）

- **ペア表現の同型（存在一意）**  
  任意の \(x\in\mathbb{R}\) を \(Ag(a,b)\) として表す／表せない領域の整理、あるいは
  \(a,b\) の一意性条件（\(\sqrt2\) の無理性を使う）。
- **\(\sqrt2\) 基底との変換**  
  \[
  a + b u_{\rm Ag} = \Bigl(a+\frac{b}{2}\Bigr) + \Bigl(\frac{b}{2}\Bigr)\sqrt2
  \]
  を Lean で補題化し、ノルムの標準形との照合を行う。
- **整数係数への制限（Pell 方程式領域）**  
  \((a,b)\in\mathbb{Z}^2\) のときの \(AgNorm=\pm 1\) を単元として扱う拡張。

---

## 7. まとめ

白銀単位 \(u_{\rm Ag}\) により

- ギャップが \(\Delta_{\rm Ag}=\frac14\) に固定される（閉包）
- 2 成分表現 \(Ag(a,b)\) が積・逆元で閉じる（代数）
- 共役とノルムにより混合がスカラーへ落ちる（潰し）
- ノルム零集合が平方完成で幾何化される（幾何）
- ノルムが乗法的である（完成）

という一連の構造が Lean で定理群として確立されました。

この基盤は「余白（Gap）」「混合（mixTerm）」「潰し（Norm）」の 3 つの操作を、厳密な形で同一フレームに載せるための中核モジュールとして機能します。
