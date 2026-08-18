# 0009 — Standard zeta の same-height critical mirror zero bridge

## 1. 目的

本書は、`0008-Completed-zeta-reflection-and-critical-mirror-transport.md` で追加 bridge として保留した same-height critical mirror transport が、現行 `DkMath.RH.CFBRC.CriticalMirrorZeroBridge` においてどこまで Lean Core として閉じているかを記録する。

結論を先に述べる。

現行実装では、standard nontrivial Riemann-zeta zero `s` から

$$
\operatorname{criticalMirror}(s)=1-\overline{s}
$$

へ standard zeta の零点を移送する theorem が証明済みである。

さらに、その mirror point が再び `NontrivialRiemannZetaZero` であることまで package されている。

したがって `0008` で Gap とした「same-height critical mirror zero transport」は、現行 dependency graph では **Core へ昇格** する。

ただし、mirror pair が同一点になること、すなわち

$$
\operatorname{criticalMirror}(s)=s
$$

はこの theorem 群からは従わない。

RH に向けた load-bearing Gap は、zero-set symmetry ではなく、その先の fixed-point / collision mechanism に残る。

---

## 2. 対象モジュール

主対象は次である。

```text
DkMath.RH.CFBRC.CriticalMirrorZeroBridge
```

直接依存する主要モジュールは次である。

```text
DkMath.RH.CFBRC.CriticalMirrorGeometry
DkMath.RH.CFBRC.CompletedZetaBridge
Mathlib.NumberTheory.Harmonic.ZetaAsymp
Mathlib.NumberTheory.LSeries.Nonvanishing
```

`CriticalMirrorZeroBridge.lean` は、completed-zeta functional equation、standard zeta の共役対称性、critical strip の非消失定理を組み合わせ、CFBRC が用いる same-height mirror geometry と standard zeta zero set を接続する。

---

## 3. functional-equation reflection を standard zeta へ戻す

`CompletedZetaBridge.lean` では、nontrivial zeta zero から

```lean
completedRiemannZeta (1 - s) = 0
```

までは既に得られていた。

`CriticalMirrorZeroBridge.lean` は、まず `1 - s` が `0` ではないことを示す。

```lean
theorem one_sub_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    1 - s ≠ 0
```

その上で standard zeta の定義へ戻し、次を証明する。

```lean
theorem riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (1 - s) = 0
```

ここで重要なのは、completed-zeta 上だけの零点反射ではなく、standard `riemannZeta` 自身の零点条件へ戻していることである。

依存の流れは次である。

```text
NontrivialRiemannZetaZero s
  → completedRiemannZeta (1 - s) = 0
  → 1 - s ≠ 0
  → riemannZeta (1 - s) = 0
```

これは RH を仮定しない **Core** である。

---

## 4. 非自明零点の open critical strip

同モジュールでは、standard nontrivial zero の実部境界も直接証明されている。

### 4.1 右境界

```lean
theorem nontrivialRiemannZetaZero_re_lt_one
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s.re < 1
```

証明は Mathlib の

```lean
riemannZeta_ne_zero_of_one_le_re
```

を用いる。

もし `1 ≤ s.re` なら `riemannZeta s ≠ 0` であり、`hs.1 : riemannZeta s = 0` と矛盾する。

### 4.2 左境界

```lean
theorem nontrivialRiemannZetaZero_re_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re
```

こちらは functional-equation reflection を利用する。

もし `s.re ≤ 0` なら

$$
\Re(1-s)\ge 1
$$

となる。

一方、前節で

```lean
riemannZeta (1 - s) = 0
```

を得ているため、再び `riemannZeta_ne_zero_of_one_le_re` と矛盾する。

### 4.3 package theorem

二つをまとめて次が得られる。

```lean
theorem nontrivialRiemannZetaZero_mem_openCriticalStrip
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re ∧ s.re < 1
```

したがって `0008` で「当該二モジュールでは未確認」とした

$$
0<\Re(s)<1
$$

は、`CriticalMirrorZeroBridge.lean` を dependency graph に加えた時点で明確な **Core** となる。

---

## 5. critical mirror と functional-equation reflection の正確な関係

`CriticalMirrorGeometry.lean` の定義は

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩
```

である。

`CriticalMirrorZeroBridge.lean` は、この写像を functional-equation reflection の共役として exact equality にする。

```lean
theorem criticalMirror_eq_star_one_sub (s : ℂ) :
    criticalMirror s = (starRingEnd ℂ) (1 - s)
```

複素数で `starRingEnd ℂ` は共役に対応するため、数学的には

$$
\operatorname{criticalMirror}(s)=\overline{1-s}=1-\overline{s}
$$

である。

$s=\sigma+it$ なら

$$
1-s=(1-\sigma)-it
$$

に対し

$$
\overline{1-s}=(1-\sigma)+it
$$

となるので、虚部の高さが元の `s` と一致する。

この theorem によって、`0008` で区別した二つの reflection の間に Lean 上の exact coordinate bridge が入った。

---

## 6. 共役対称性を使った same-height zero transport

中心 theorem は次である。

```lean
theorem riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (criticalMirror s) = 0
```

証明は三段階で構成される。

1. `criticalMirror_eq_star_one_sub` により mirror point を共役された `1 - s` と書き換える。
2. Mathlib の `riemannZeta_conj (1 - s)` により zeta と共役の交換を行う。
3. `riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs` を代入して零点を得る。

Lean 上の `calc` は概ね次の形である。

```lean
riemannZeta (criticalMirror s)
  = riemannZeta ((starRingEnd ℂ) (1 - s))
  = (starRingEnd ℂ) (riemannZeta (1 - s))
  = 0
```

したがって、`0008` で Beam / Gap とした

```text
functional equation
  + conjugation symmetry
  → same-height mirror zero
```

は、現行実装では既に閉じている。

これは **representation bridge としての Core** であり、RH そのものを仮定していない。

---

## 7. mirror point も open critical strip に残る

同モジュールは mirror point の実部についても直接証明する。

```lean
theorem criticalMirror_re_pos_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < (criticalMirror s).re
```

および

```lean
theorem criticalMirror_re_lt_one_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    (criticalMirror s).re < 1
```

である。

これらは

$$
\Re(\operatorname{criticalMirror}(s))=1-\Re(s)
$$

と元の open critical strip 条件から `linarith` で得られる。

よって mirror transport は critical strip の外へ出る操作ではなく、strip 内部の左右対称点を交換する involutive symmetry である。

---

## 8. `NontrivialRiemannZetaZero` 自体の mirror closure

零点方程式だけでなく、標準 nontrivial-zero predicate 全体が mirror に対して閉じていることまで証明されている。

```lean
theorem criticalMirror_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (criticalMirror s)
```

この proof では次の三条件を再構築する。

1. `riemannZeta (criticalMirror s) = 0`
2. mirror point は trivial negative-even zero ではない
3. mirror point は `1` ではない

特に 2 と 3 は mirror point の正の実部と元の `s.re > 0` を利用して排除される。

これにより、単なる zeta-zero transport より強い package が得られている。

```text
NontrivialRiemannZetaZero s
  → NontrivialRiemannZetaZero (criticalMirror s)
```

この closure theorem は、後続の paired-frame / mirror-pair 構成にとって自然な入口になる。

---

## 9. `0008` からの状態更新

`0008` の監査では、確認対象を `CompletedZetaBridge.lean` と `CriticalMirrorGeometry.lean` に限定したため、次を未確認としていた。

```text
completed/standard zeta zero の共役 transport
same-height critical mirror zero transport
nontrivial zero の open critical strip
```

`CriticalMirrorZeroBridge.lean` を確認した結果、状態は次へ更新される。

| 項目 | `0008` 時点 | `0009` 確認後 |
|---|---|---|
| `riemannZeta (1 - s) = 0` | completed-zeta 側まで確認 | Core |
| $0<\Re(s)<1$ | 当該対象では未確認 | Core |
| `criticalMirror s = conjugate (1 - s)` | 幾何的関係のみ | exact Lean theorem |
| standard zeta の共役 transport | Beam | Mathlib `riemannZeta_conj` を使用済み |
| `riemannZeta (criticalMirror s) = 0` | Gap | Core |
| `NontrivialRiemannZetaZero (criticalMirror s)` | 未確認 | Core |

ここで `0008` の記述が誤りだったわけではない。

`CompletedZetaBridge.lean` 単体には same-height transport theorem が無いという監査は正しい。

`0009` は、その追加 bridge が別モジュール `CriticalMirrorZeroBridge.lean` に既に実装されていたことを dependency graph 上で補完する文書である。

---

## 10. 何がまだ RH を閉じないのか

mirror closure が完成すると、非自明零点 `s` に対して同じ虚部を持つ

$$
s=\sigma+it
$$

と

$$
\operatorname{criticalMirror}(s)=(1-\sigma)+it
$$

の双方が nontrivial zero になる。

しかし、これは

$$
\sigma=1-\sigma
$$

を意味しない。

すなわち

$$
\sigma=\frac12
$$

はまだ得られない。

左右二点

$$
\sigma+it,
\qquad
(1-\sigma)+it
$$

が異なるまま共存しても、現在までの symmetry theorem と矛盾しない。

したがって次の推論は禁止される。

```text
mirror of a zero is a zero
therefore the zero is fixed by the mirror
```

これは論理的に無効である。

`criticalMirror_eq_self_iff_re_eq_half` は

```text
fixed point ↔ critical line
```

を与えるが、fixedness そのものを供給しない。

ここが引き続き **load-bearing Gap** である。

---

## 11. CFBRC zero locus との接続位置

CFBRC 側では正の degree に対して

```lean
offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

が既に証明されている。

standard zeta 側では本書により

```text
nontrivial zero
  → same-height mirror nontrivial zero
```

まで閉じた。

したがって現在の構造は

```text
standard zeta side
  s zero
  ↔ mirror-pair geometry available

CFBRC side
  CFBRC zero
  ↔ critical-line fixed coordinate
```

となる。

しかし二つは依然として異なる Lean object である。

mirror-pair symmetry を CFBRC zero-locus theorem に投入するだけでは RH は出ない。

必要なのは、同一の standard zeta zero に由来する paired-frame / interaction / collision quantity が、off-critical では成立不能であることを **非循環に** 証明する bridge である。

---

## 12. Core / Beam / Gap / Obstruction の分類

### Core

- `1 - s ≠ 0` for nontrivial zeta zero
- `riemannZeta (1 - s) = 0`
- `0 < s.re`
- `s.re < 1`
- `0 < s.re ∧ s.re < 1`
- `criticalMirror s = (starRingEnd ℂ) (1 - s)`
- `riemannZeta (criticalMirror s) = 0`
- mirror point の open-strip bounds
- `NontrivialRiemannZetaZero (criticalMirror s)`

### Beam

mirror-pair を後続の paired-frame / eta / CFBRC interaction object へ同一対象として運ぶ route。

### Gap

mirror pair が off-critical で distinct な二点として残れないことを示す load-bearing mechanism。

### Obstruction

zero-set symmetry だけから pointwise fixedness を導くことはできない。

この distinction は今後も維持する。

---

## 13. dependency graph

本書で確認された安全な流れは次である。

```text
NontrivialRiemannZetaZero s
  │
  ├─→ completedRiemannZeta s = 0
  │
  ├─→ completedRiemannZeta (1 - s) = 0
  │
  ├─→ riemannZeta (1 - s) = 0
  │
  ├─→ 0 < Re(s) < 1
  │
  ├─→ criticalMirror s = conjugate (1 - s)
  │
  ├─→ riemannZeta (criticalMirror s) = 0
  │
  └─→ NontrivialRiemannZetaZero (criticalMirror s)

criticalMirror s = s
  ↔ Re(s) = 1/2
```

ただし最後の二段はまだ接続されていない。

```text
NontrivialRiemannZetaZero s
  ──/──→ criticalMirror s = s
```

ここに slash を置くことが本書の最重要監査点である。

---

## 14. 次の文書候補

次は、この完成した mirror-pair zero closure を受けて、実際の RH-CFBRC 実装が mirror pair をどのような paired-frame object に載せているかを追うのが自然である。

特に候補は次である。

```text
EtaCriticalMirrorPairedFrame*
```

系列である。

次文書では、巨大な系列を一度に説明するのではなく、まず

```text
standard nontrivial zero pair
  → eta / paired-frame input
```

という最初の representation bridge を特定し、そこで導入される quantity、normalization、index、same-object 条件を監査する。

その後に moving frame、tail、Abel transform、collision obstruction へ進む。

---

## 15. まとめ

`CriticalMirrorZeroBridge.lean` により、`0008` で保留した same-height mirror transport は既に Lean Core として閉じている。

特に重要なのは次の theorem である。

```lean
criticalMirror_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (criticalMirror s)
```

したがって、standard nontrivial zeta zero set は CFBRC の `criticalMirror` に対して閉じている。

しかしこれは RH の fixed-point statement ではない。

現在の正確な境界は

```text
mirror symmetry: CLOSED
mirror fixedness: OPEN / load-bearing
```

である。

今後の文書は、この mirror pair を paired-frame / interaction object へ移し、distinct off-critical pair を排除するためにどの theorem が本当に load-bearing なのかを追跡する。