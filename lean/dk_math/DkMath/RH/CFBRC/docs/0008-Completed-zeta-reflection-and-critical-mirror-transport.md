# 0008 — Completed zeta の反射と critical mirror transport

## 1. 目的

本書は、`CompletedZetaBridge.lean` と `CriticalMirrorGeometry.lean` の間にある対称性の種類を分離し、completed Riemann zeta の functional equation が与える零点反射と、CFBRC 側で用いる same-height critical mirror を混同しないための監査文書である。

この区別は RH-CFBRC 形式化において重要である。

completed zeta の functional equation が直接扱う写像は

$$
s\longmapsto 1-s
$$

である。一方、`criticalMirror` が表す写像は

$$
\sigma+it\longmapsto (1-\sigma)+it
$$

である。

後者は複素共役を用いれば

$$
\operatorname{criticalMirror}(s)=1-\overline{s}
$$

に対応するが、現行の `CompletedZetaBridge.lean` に同一高さへの mirror transport を直接述べる theorem は置かれていない。

したがって、本書では functional equation による反射までを Lean Core とし、same-height mirror transport は追加 bridge を要するものとして区別する。

---

## 2. 対象モジュール

主対象は次の二つである。

```text
DkMath.RH.CFBRC.CompletedZetaBridge
DkMath.RH.CFBRC.CriticalMirrorGeometry
```

関連する脅威モデルとして次も参照する。

```text
DkMath.RH.CFBRC.MirrorThreatModel
```

---

## 3. 標準ゼータ零点から completed zeta 零点への移送

`CompletedZetaBridge.lean` は、まず standard nontrivial zeta zero と completed Riemann zeta の零点条件を接続する。

### 3.1 非自明零点は `0` ではない

```lean
theorem nontrivialRiemannZetaZero_ne_zero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s ≠ 0
```

これは `riemannZeta_zero` を用い、`s = 0` が standard nontrivial zero にならないことを確認する補題である。

### 3.2 Gamma 因子の非消失

```lean
theorem gammaR_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    Complex.Gammaℝ s ≠ 0
```

completed zeta への移送で余分な零点を導入しないため、Deligne の real Gamma factor が対象点で消えないことを証明している。

### 3.3 standard zeta と completed zeta の零点条件

```lean
theorem riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hGamma : Complex.Gammaℝ s ≠ 0) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0
```

必要な非消失条件の下で、両者の零点条件は同値になる。

その帰結として、standard nontrivial zero から completed-zeta zero への直接定理が得られる。

```lean
theorem completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    completedRiemannZeta s = 0
```

ここは RH を仮定していない。

したがってこれは明確な **Core** である。

---

## 4. functional equation が与える零点反射

completed Riemann zeta について、現行実装には次がある。

```lean
theorem completedRiemannZeta_one_sub_eq_zero_iff (s : ℂ) :
    completedRiemannZeta (1 - s) = 0 ↔
      completedRiemannZeta s = 0
```

これは Mathlib の `completedRiemannZeta_one_sub` をそのまま零点条件へ落とした theorem である。

したがって completed-zeta zero set は

$$
s\longmapsto1-s
$$

に対して閉じている。

standard nontrivial zero からはさらに

```lean
theorem completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    completedRiemannZeta (1 - s) = 0
```

が得られる。

ここまでが現在の completed-zeta bridge に直接実装された反射 **Core** である。

---

## 5. `1 - s` は same-height mirror ではない

$s=\sigma+it$ とする。

functional equation の反射は

$$
1-s=(1-\sigma)-it
$$

である。

したがって実部だけでなく虚部の符号も反転する。

一方 `CriticalMirrorGeometry.lean` の定義は次である。

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩
```

これは

$$
\operatorname{criticalMirror}(\sigma+it)=(1-\sigma)+it
$$

であり、虚部を保存する。

よって

```text
functional-equation reflection : s ↦ 1 - s
critical mirror                : s ↦ 1 - conjugate(s)
```

という二種類の写像を区別しなければならない。

特に、`completedRiemannZeta_one_sub_eq_zero_iff` だけから

```lean
completedRiemannZeta (criticalMirror s) = 0
```

を結論することはできない。

---

## 6. same-height mirror transport に必要な追加橋

same-height mirror へ進む標準的な構造は二段階になる。

1. 共役対称性によって $s$ から $\overline{s}$ へ零点を移す。
2. functional equation によって $\overline{s}$ から $1-\overline{s}$ へ零点を移す。

すると

$$
1-\overline{s}=\operatorname{criticalMirror}(s)
$$

となる。

しかし、今回確認した `CompletedZetaBridge.lean` には、completed zeta の共役対称性を零点 transport として包んだ theorem は含まれていない。

したがって現行文書上の分類は次である。

**Core**

`completedRiemannZeta s = 0` から `completedRiemannZeta (1 - s) = 0` への functional-equation transport。

**Beam**

completed zeta の共役対称性を Lean theorem として明示し、functional equation と合成する。

**Gap**

`completedRiemannZeta s = 0` から `completedRiemannZeta (criticalMirror s) = 0` までを一つの theorem として閉じること。

この Gap は RH そのものではない。零点集合の既知対称性を same-height 座標へ再梱包する representation bridge である。

---

## 7. critical mirror の固定点幾何

`CriticalMirrorGeometry.lean` では次が証明されている。

```lean
theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s
```

さらに固定点集合は正確に critical line である。

```lean
theorem criticalMirror_eq_self_iff_re_eq_half (s : ℂ) :
    criticalMirror s = s ↔ s.re = (1 : ℝ) / 2
```

すなわち

$$
\operatorname{criticalMirror}(s)=s
\iff
\Re(s)=\frac12
$$

である。

この theorem 自体はゼータ関数を必要としない純粋な幾何 **Core** である。

---

## 8. 対称な零点対と固定点を混同しない

ここが本書の最重要監査点である。

仮に same-height mirror transport が完成し、

$$
Z(s)=0\Longrightarrow Z(\operatorname{criticalMirror}(s))=0
$$

を得たとしても、そこから

$$
\operatorname{criticalMirror}(s)=s
$$

は従わない。

左右に異なる二点が存在していても零点集合の mirror symmetry は成立するからである。

したがって

```text
zero-set symmetry
```

と

```text
pointwise fixedness
```

の間には、なお別の数学が必要である。

RH に必要なのは後者である。

これは CFBRC 形式化における重要な **Gap** である。

---

## 9. CFBRC の zero locus との違い

standard CFBRC 側では、正の degree に対して既に

```lean
offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

という exact zero-locus theorem がある。

したがって CFBRC 内部では、零点なら critical line という構造は閉じている。

しかし completed-zeta zero set の mirror symmetry は別の Lean object に関する事実である。

ゆえに、次の二文を連結なしに合成してはならない。

```text
completed-zeta zeros are mirror symmetric
```

```text
offCriticalCFBRC zeros lie exactly on σ = 1/2
```

実際に RH を閉じるには、同一の標準非自明ゼータ零点について CFBRC zero condition を得る load-bearing bridge が必要になる。

既存の universal `map_zero` 形式は RH と同値であるため、それを単に仮定するだけでは進展にならない。

---

## 10. `MirrorThreatModel` が示す注意点

`mirrorCFBRC` のように左右を対称にした多項式モデルでは、対称性そのものが中心固定を保証しない。

特に degree 3 では

$$
\operatorname{mirrorCFBRC}(3,X,\Theta)=0
$$

が

$$
X=0
\quad\text{または}\quad
X^2=3\Theta^2
$$

へ分岐することが既に証明されている。

したがって「mirror structure を導入したから off-critical branch が消える」という推論は不正である。

この counter-structure は **Obstruction / threat model** として保持する価値がある。

---

## 11. critical strip についての監査

標準 RH の議論では nontrivial zero の critical strip が重要になる。

ただし、今回直接確認した

```text
CompletedZetaBridge.lean
CriticalMirrorGeometry.lean
```

の theorem 群は、非自明零点について

$$
0<\Re(s)<1
$$

を証明するためのモジュールではない。

したがって、この不等式を本書では当該モジュールの Lean Core として数えない。

今後、DkMath または Mathlib の既存 theorem を明示的に接続した時点で、別途 Core として記録する。

この扱いにより、標準数学として知られている背景事実と、現在の RH-CFBRC dependency graph 内で実際に import・使用されている theorem を区別する。

---

## 12. 状態表

| 項目 | 状態 | 分類 |
|---|---|---|
| nontrivial zeta zero は `s ≠ 0` | 証明済み | Core |
| 対象点で `Gammaℝ s ≠ 0` | 証明済み | Core |
| standard zeta zero → completed-zeta zero | 証明済み | Core |
| completed-zeta zero の $s\mapsto1-s$ transport | 証明済み | Core |
| `criticalMirror` の involution | 証明済み | Core |
| `criticalMirror s = s ↔ Re(s)=1/2` | 証明済み | Core |
| completed-zeta zero の共役 transport | 本書で確認した bridge には未収録 | Beam |
| completed-zeta zero の same-height critical mirror transport | 直接 theorem は未確認 | Gap |
| mirror symmetry → fixed point | 導出不可 | Obstruction |
| standard zeta zero → standard CFBRC zero の非循環 bridge | 未閉鎖 | Big Gap |

---

## 13. 次の形式化候補

次の小さな実装単位として自然なのは、completed zeta の共役対称性が Mathlib で利用可能かを確認し、利用可能なら次の形へ包むことである。

```lean
completedRiemannZeta s = 0 →
  completedRiemannZeta (criticalMirror s) = 0
```

ただし、この theorem が得られても RH は閉じない。

その役割は、functional-equation reflection と CFBRC が使う same-height mirror geometry の座標を一致させることにある。

その後に問うべき load-bearing 問題は、mirror pair がなぜ異なる二点として残れないか、あるいは標準非自明ゼータ零点がなぜ standard CFBRC zero condition を満たすか、である。

---

## 14. 結論

現行実装から確実に言えることは次である。

1. standard nontrivial zeta zero は completed-zeta zero へ移送できる。
2. completed-zeta zero は functional equation により $1-s$ 側にも零点を持つ。
3. CFBRC の `criticalMirror` は同じ虚部を保つ $1-\overline{s}$ 型の反射である。
4. `criticalMirror` の固定点は厳密に $\Re(s)=1/2$ である。
5. functional-equation reflection と same-height critical mirror は同一ではない。
6. mirror symmetry だけでは fixed point、したがって RH は導けない。

よって `0007` で固定した critical mirror geometry に対し、本書 `0008` は解析側から到達している反射の正確な境界を与える。

現在の安全な接続図は

```text
NontrivialRiemannZetaZero
  → completedRiemannZeta zero
  → functional-equation reflected zero at 1 - s
  → [conjugation / same-height transport bridge]
  → criticalMirror zero pair
  → [fixed-point / collision mechanism]
  → Re(s) = 1/2
```

である。

角括弧部分を証明済み Core と誤認しないことが、RH-CFBRC 形式化の健全性を守る。
