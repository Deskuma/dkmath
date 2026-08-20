# Critical mirror の幾何と臨界線の固定点

## 1. この文書の位置

`0006-Completed-zeta-zero-transport-and-reflection.md` では、標準リーマンゼータ関数の非自明零点を completed zeta の零点へ移し、さらに functional equation によって `1 - s` 側へ零点条件を運べることを記録した。

この文書では、その次に必要となる **critical mirror** の幾何を独立に固定する。

対象 module は主に次の二つである。

```text
DkMath.RH.CFBRC.CriticalMirrorGeometry
DkMath.RH.CFBRC.MirrorThreatModel
```

ここで重要なのは、次の二つの反射を混同しないことである。

```text
functional reflection
  s ↦ 1 - s

critical mirror
  (σ, t) ↦ (1 - σ, t)
```

前者は虚部の符号も反転する。後者は虚部を保存し、同じ高さで臨界線 `Re(s) = 1 / 2` の反対側へ写す。

この区別は、後の eta paired-frame、completed-zeta mirror、moving-line、CF2D cycle-state の各議論で重要になる。

---

## 2. critical mirror の定義

Lean では critical mirror を次のように定義する。

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩
```

通常数学では、

$$
s=\sigma+it
$$

に対して、

$$
\operatorname{criticalMirror}(s)=(1-\sigma)+it
$$

である。

したがって、実部と虚部について、

$$
\Re(\operatorname{criticalMirror}(s))=1-\Re(s)
$$

$$
\Im(\operatorname{criticalMirror}(s))=\Im(s)
$$

が exact に成立する。

Lean theorem は次である。

```lean
criticalMirror_re
criticalMirror_im
```

この写像は、複素平面上で臨界線を軸とする同じ高さの反射を表している。

---

## 3. functional reflection との違い

completed zeta の functional equation で現れる反射は、

$$
s\longmapsto1-s
$$

である。

$s=\sigma+it$ なら、

$$
1-s=(1-\sigma)-it
$$

となる。

一方 critical mirror は、

$$
\operatorname{criticalMirror}(s)=(1-\sigma)+it
$$

である。

したがって両者の違いは虚部にある。

```text
1 - s
  real part: 1 - σ
  imag part: -t

criticalMirror s
  real part: 1 - σ
  imag part:  t
```

このため、completed-zeta functional equation がそのまま critical mirror 零点を与えるわけではない。

critical mirror 側へ零点を運ぶには、必要に応じて complex conjugation など別の bridge が必要になる。

この段階では、その analytic transport はまだ本題に含めない。

---

## 4. critical mirror は involution である

Lean では、

```lean
theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s
```

が証明されている。

通常数学では、実部について、

$$
1-(1-\sigma)=\sigma
$$

であり、虚部は最初から保存されるため、二回反射すれば元の点へ戻る。

したがって critical mirror は involution、すなわち自己逆写像である。

この事実により、臨界線の左右は一方向の写像ではなく、対になった二つの状態として扱える。

---

## 5. 固定点集合は臨界線そのもの

この層で最も重要な theorem は、

```lean
theorem criticalMirror_eq_self_iff_re_eq_half (s : ℂ) :
    criticalMirror s = s ↔ s.re = (1 : ℝ) / 2
```

である。

通常数学では、critical mirror の固定点条件は、

$$
(1-\sigma)+it=\sigma+it
$$

である。

虚部は自動的に一致するため、実部だけを比較して、

$$
1-\sigma=\sigma
$$

を得る。

したがって、

$$
\sigma=\frac12
$$

である。

逆に $\sigma=1/2$ なら、critical mirror はその点を動かさない。

よって、

$$
\boxed{
\operatorname{criticalMirror}(s)=s
\iff
\Re(s)=\frac12
}
$$

となる。

これは RH を証明しているのではない。

ここで証明したのは、**critical mirror という幾何写像の固定点集合が臨界線である**という純粋な幾何事実である。

---

## 6. centered complex coordinate

同じ module では、臨界線を中心とする複素座標も定義されている。

```lean
noncomputable def centeredComplex (s : ℂ) : ℂ :=
  ⟨s.re - (1 : ℝ) / 2, s.im⟩
```

したがって、

$$
\operatorname{centeredComplex}(s)
=
\left(\Re(s)-\frac12\right)+i\Im(s)
$$

である。

`0003` で導入した実数座標、

```lean
centeredSigma σ := σ - 1 / 2
```

を複素点全体へ拡張したものと読める。

Lean では、

```lean
centeredComplex_re
centeredComplex_im
```

により、その実部・虚部が固定されている。

この座標では臨界線は、

$$
\Re(\operatorname{centeredComplex}(s))=0
$$

という中心線になる。

---

## 7. mirror model の left state との一致

さらに、

```lean
theorem centeredComplex_eq_mirrorLeft (s : ℂ) :
    centeredComplex s = mirrorLeft (centeredSigma s.re) s.im
```

が証明されている。

これは `centeredSigma` と `centeredComplex` が、別々に導入された記号ではなく、mirror model の実際の state と exact に接続されていることを意味する。

概念的には、

```text
standard complex coordinate s
  ↓ center at Re(s) = 1/2
centeredComplex s
  ↓
mirrorLeft(centeredSigma s.re, s.im)
```

という同一対象の表現変更である。

ここでも、近似や可視化ではなく Lean の equality として固定されている。

---

## 8. standard CFBRC と mirror CFBRC を区別する

critical mirror の幾何を導入すると、左右対称な CFBRC polynomial を考えたくなる。

`MirrorThreatModel` では、

```lean
noncomputable def mirrorCFBRC (d : ℕ) (X Θ : ℝ) : ℂ :=
  ((X : ℂ) + Complex.I * (Θ : ℂ)) ^ d -
    ((-X : ℂ) + Complex.I * (Θ : ℂ)) ^ d
```

を導入している。

これは standard CFBRC、

```text
cfbrcR d X Θ
```

とは別の polynomial である。

この違いは証明上きわめて重要である。

standard positive-degree CFBRC については `0003` で、

$$
\operatorname{cfbrcR}(d,X,\Theta)=0
\iff
X=0
$$

が証明されている。

しかし mirror CFBRC では、degree 3 において、

$$
\operatorname{mirrorCFBRC}(3,X,\Theta)=0
$$

が、

$$
X=0
$$

だけでなく、

$$
X^2=3\Theta^2
$$

でも成立し得る。

Lean theorem は、

```lean
theorem mirrorCFBRC_three_eq_zero_iff (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ = 0 ↔ X = 0 ∨ X ^ 2 = 3 * Θ ^ 2
```

である。

したがって、

```text
critical mirror geometry
```

を導入したからといって、

```text
mirror CFBRC zero
```

をそのまま standard CFBRC zero として扱ってはならない。

この module が `MirrorThreatModel` と名付けられている理由はここにある。

---

## 9. mirror CFBRC の boundary × core 分解

mirror CFBRC は、

```lean
mirrorCFBRC_eq_boundary_mul_core
```

により、

$$
\operatorname{mirrorCFBRC}(d,X,\Theta)
=
2X\,\operatorname{mirrorCFBRCCore}(d,X,\Theta)
$$

と exact に因数分解される。

したがって mirror closure は、

```text
centered boundary
  X = 0

または

mirror cyclotomic core
  mirrorCFBRCCore = 0
```

の二つの可能性を持つ。

特に $X\ne0$ の場合は、

```lean
mirrorCFBRC_eq_zero_iff_core_eq_zero
```

によって、mirror zero が core zero と exact に同値になる。

DkMath 用語で言えば、これは「中心 Gap が消えた」場合と「内部 Core が消えた」場合を区別しなければならない、という監査結果である。

---

## 10. この段階で証明済みのこと

現在この層で Lean Core として固定されているのは、次である。

```text
criticalMirror preserves imaginary height
criticalMirror reflects σ to 1 - σ
criticalMirror is involutive
criticalMirror fixed points are exactly Re(s) = 1/2
centeredComplex is the complex extension of centeredSigma
centeredComplex equals the mirror model left state
mirrorCFBRC has an exact boundary × core factorization
mirrorCFBRC may have off-centered branches
```

特に、

$$
\operatorname{criticalMirror}(s)=s
\iff
\Re(s)=\frac12
$$

は完全証明済みである。

---

## 11. この段階で証明していないこと

この文書の事実だけから、次は導けない。

```text
NontrivialRiemannZetaZero s
→ criticalMirror s = s
```

また、

```text
completedRiemannZeta s = 0
→ criticalMirror s = s
```

も導けない。

completed-zeta functional equation が与えるのは、まず $s$ と $1-s$ の零点対称性である。

critical mirror の固定点条件は、それとは別に、対象点自身が同じ高さの mirror と一致することを要求する。

したがって、

```text
zero symmetry
```

と、

```text
zero fixedness
```

を混同してはならない。

この区別を失うと、対称性だけから RH を結論する循環または論理飛躍になる。

---

## 12. `0003` との接続

`0003` では、CFBRC 側の centered coordinate として、

$$
\operatorname{centeredSigma}(\sigma)=\sigma-\frac12
$$

を導入した。

この文書では、その幾何学的意味が、

```text
critical mirror の固定点からの signed displacement
```

として明確になった。

critical mirror により、

$$
\sigma-\frac12
$$

は反対側で、

$$
(1-\sigma)-\frac12
=
-\left(\sigma-\frac12\right)
$$

へ移る。

したがって CFBRC の centered coordinate は、critical mirror の左右を符号付きで記述する自然な実座標である。

---

## 13. 監査結論

この層の結論は次である。

```text
completed-zeta reflection
  s ↔ 1 - s

critical mirror geometry
  (σ,t) ↔ (1-σ,t)

critical fixed locus
  Re(s) = 1/2
```

これらは互いに関連するが、同一の主張ではない。

特に、critical line が mirror の固定点集合であることは完全に証明済みである一方、**標準ゼータのすべての非自明零点がその固定点集合に入ること**は、この幾何だけからは得られない。

今後の bridge は、この差を埋める新しい数学的内容を持たなければならない。
