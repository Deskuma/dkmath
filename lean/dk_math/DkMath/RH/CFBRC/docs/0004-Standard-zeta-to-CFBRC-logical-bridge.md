# 標準ゼータ零点から CFBRC への論理 bridge

## 1. この文書の目的

この文書では、`DkMath.RH.CFBRC` において、Mathlib の標準リーマンゼータ関数と CFBRC の零点幾何がどのように接続されているかを整理する。

前文書 `0003-CFBRC-centered-coordinate-and-off-critical-zero-geometry.md` では、ゼータ関数を使わずに、正次数 CFBRC の零点が centered coordinate の原点、すなわち `σ = 1 / 2` に限られることを確認した。

本段階では、その純粋 CFBRC 側の事実へ、標準リーマンゼータ関数の非自明零点を接続する論理構造を記録する。

重要なのは、ここで bridge の「器」が完成していることと、標準ゼータ零点が実際に CFBRC 零点へ写ることを証明することは別問題である、という点である。

---

## 2. 対象 module

```text
DkMath.RH.CFBRC.StandardZetaBridge
```

主要識別子:

```lean
def NontrivialRiemannZetaZero

theorem riemannHypothesis_iff_nontrivialZero_re_eq_half

abbrev StandardZetaToCFBRCBridge

abbrev StandardZetaFiniteCenteredBridge

theorem riemannHypothesis_of_standardZetaToCFBRCBridge

theorem riemannHypothesis_of_standardZetaFiniteCenteredBridge

theorem riemannHypothesis_of_standardZeta_map_zero
```

---

## 3. 標準ゼータの非自明零点 predicate

DkMath 側では、Mathlib の `riemannZeta` を使って次を定義する。

```lean
def NontrivialRiemannZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1
```

これは次の三条件を同時に要求する。

1. `riemannZeta s = 0`
2. 負の偶数にある自明零点ではない
3. 極 `s = 1` ではない

したがって、DkMath 独自の別種の零点概念を導入しているわけではない。

ここで扱っているのは Mathlib の標準 `riemannZeta` の零点である。

---

## 4. Mathlib の RiemannHypothesis との整合

次の theorem が証明済みである。

```lean
theorem riemannHypothesis_iff_nontrivialZero_re_eq_half :
    RiemannHypothesis ↔
      ∀ s : ℂ, NontrivialRiemannZetaZero s → s.re = (1 : ℝ) / 2
```

すなわち DkMath 側では、Mathlib の `RiemannHypothesis` を、

$$
\forall s,\quad
\operatorname{NontrivialRiemannZetaZero}(s)
\Longrightarrow
\operatorname{Re}(s)=\frac12
$$

という形で直接扱える。

この theorem は新しい RH の定義を作っているのではない。

Mathlib の formal statement と DkMath 内部で使いやすい predicate 表現の間を往復しているだけである。

状態分類:

```text
Core
```

---

## 5. 一般 CFBRC bridge の標準ゼータ特化

`0003` で確認した一般構造、

```lean
structure ZeroToCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s →
    offCriticalCFBRC d s.re (phase s) = 0
```

に対して、`Zero` を標準ゼータの非自明零点 predicate に固定したものが、

```lean
abbrev StandardZetaToCFBRCBridge :=
  ZeroToCFBRCBridge NontrivialRiemannZetaZero
```

である。

この bridge は次の情報を持つ。

```text
正次数 d
正次数である証明 hd
各複素点へ与える phase coordinate
標準ゼータ零点を CFBRC 零点へ写す map_zero
```

特に重要なのは最後の `map_zero` である。

---

## 6. bridge から RH を得る theorem

次が証明済みである。

```lean
theorem riemannHypothesis_of_standardZetaToCFBRCBridge
    (bridge : StandardZetaToCFBRCBridge) :
    RiemannHypothesis
```

証明構造は短い。

```text
NontrivialRiemannZetaZero s
  ↓ bridge.map_zero
offCriticalCFBRC d s.re (phase s) = 0
  ↓ offCriticalCFBRC_eq_zero_iff_re_eq_half
s.re = 1 / 2
  ↓ riemannHypothesis_iff_nontrivialZero_re_eq_half
RiemannHypothesis
```

CFBRC 側の零点幾何そのものはすでに `0003` の段階で閉じている。

したがって、この theorem で新しく必要になる数学的内容は、標準ゼータ零点を CFBRC 零点へ写すことだけである。

状態分類:

```text
Core:
  bridge が与えられれば RH を導けること

Gap:
  bridge.map_zero の独立な供給
```

---

## 7. map_zero を直接書いた形

同じ内容を structure を介さず直接書いた theorem がある。

```lean
theorem riemannHypothesis_of_standardZeta_map_zero
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ)
    (map_zero : ∀ {s : ℂ}, NontrivialRiemannZetaZero s →
      offCriticalCFBRC d s.re (phase s) = 0) :
    RiemannHypothesis
```

これは現在の論理境界を最も明瞭に表す theorem である。

必要なのは、

$$
\operatorname{NontrivialRiemannZetaZero}(s)
\Longrightarrow
\operatorname{offCriticalCFBRC}
\bigl(d,\operatorname{Re}(s),\operatorname{phase}(s)\bigr)=0
$$

という写像則である。

これを与えれば RH は CFBRC の既存零点排除 theorem によって直ちに閉じる。

---

## 8. 何がまだ証明されていないか

ここで最も重要な監査を行う。

次の二つを混同してはならない。

```text
A.
CFBRC の零点は臨界線上にしかない

B.
標準ゼータの非自明零点は CFBRC 零点へ写る
```

A は証明済みである。

B はこの bridge の load-bearing field である。

したがって、単に `StandardZetaToCFBRCBridge` という structure が存在することや、`riemannHypothesis_of_standardZetaToCFBRCBridge` が証明済みであることをもって、RH が証明済みとは言えない。

`map_zero` を実際の数学から構成する必要がある。

---

## 9. finite centered bridge

標準ゼータ専用のもう一つの経路として、

```lean
abbrev StandardZetaFiniteCenteredBridge (ι : Type*) :=
  FiniteCenteredZeroBridge ι NontrivialRiemannZetaZero
```

がある。

これに対して、

```lean
theorem riemannHypothesis_of_standardZetaFiniteCenteredBridge
    {ι : Type*} (bridge : StandardZetaFiniteCenteredBridge ι) :
    RiemannHypothesis
```

も証明済みである。

この経路では、標準ゼータ零点を直接 CFBRC 零点へ写す代わりに、有限 centered realization を構成し、その中心が `centeredSigma s.re` と一致することを利用する。

source comment では load-bearing な内容として、

```text
center_identification
および genuine endpoint realization
```

が明示されている。

この finite centered route は、後続文書で eta finite closure とともに詳しく扱う。

---

## 10. 論理構造の要約

ここまでを三層で書けば次のようになる。

```text
Layer A — CFBRC 幾何

offCriticalCFBRC = 0
  ↔
Re(s) = 1 / 2

Layer B — zero-preserving bridge

standard zeta nontrivial zero
  →
CFBRC zero

Layer C — Mathlib RH

all nontrivial zeta zeros
  →
Re(s) = 1 / 2
```

Layer A は証明済み。

Layer A から Layer C への論理 wrapper も証明済み。

現在の数学的負荷は Layer B にある。

---

## 11. 妥当性監査

### 11.1 bridge theorem は RH の証明そのものではない

```lean
riemannHypothesis_of_standardZeta_map_zero
```

は、`map_zero` を仮定として受け取る theorem である。

したがって theorem 自体が Green であることは、`map_zero` が無条件で構成されたことを意味しない。

### 11.2 CFBRC の一本線性は独立 Core

一方、

```lean
offCriticalCFBRC_eq_zero_iff_re_eq_half
```

はゼータ零点を仮定しない。

したがって CFBRC 内部の零点幾何は、標準ゼータ bridge とは独立した Core として扱える。

### 11.3 今後の文書では bridge の供給源を追う

後続の eta、critical mirror、finite closure、paired frame、Prime / Pascal / Xi、CFZP 系は、最終的にはこの Layer B に新しい内容を供給できるかという観点から監査する。

ただし、後年に作られた theorem を使って過去の段階を先取りして説明しない。

各文書は、その段階までに固定された事実だけを依存順に記録する。

---

## 12. 現在の checkpoint

この段階で固定されたこと:

```text
Core:
  Mathlib の標準 zeta zero predicate との整合
  RiemannHypothesis の predicate 表現
  StandardZetaToCFBRCBridge の型
  bridge から RH を得る theorem
  finite centered bridge から RH を得る theorem

Gap:
  標準ゼータ非自明零点から CFBRC zero への実際の map_zero
  または同等の finite centered realization provider
```

次の文書では、finite centered route の基礎となる CFBRC finite closure と eta 側の構造を、実装依存順に確認する。
