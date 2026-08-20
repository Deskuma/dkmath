# 0018 — General CoreBeamGap and Cosmic Formula decomposition

## 1. この文書の位置

`0016` では二次の `ThreeElement` Core、`0017` ではその静的 `MagicCore` witness を整理した。

本章では一段上へ戻り、DkMath の一般次数宇宙式

```text
DkMath.CosmicFormula.CoreBeamGap
```

を正本として、二次 `ThreeElement` が何の特殊化であるかを明確にする。

重要な点は、

```text
Big = Core + Beam + Gap
```

が二次だけの偶然ではなく、任意の正次数 `d` の二項展開に対する exact decomposition であることである。

---

## 2. 一般次数の定義

`CoreBeamGap.lean` は、可換半環 `R` 上で次を定義する。

```lean
def Core (d : ℕ) (x : R) : R := x ^ d

def Gap (d : ℕ) (u : R) : R := u ^ d

def Beam (d : ℕ) (x u : R) : R :=
  match d with
  | 0 => 0
  | n + 1 =>
      ∑ k ∈ Finset.range n,
        (Nat.choose (n + 1) (k + 1) : R) *
          x ^ (k + 1) * u ^ (n - k)

def Big (d : ℕ) (x u : R) : R := BigN d x u
```

意味は明快である。

- `Core d x` は左端純冪 `x^d`
- `Gap d u` は右端純冪 `u^d`
- `Beam d x u` は両端純冪を除いた全中間二項係数項
- `Big d x u` は完全な `(x+u)^d`

したがって Beam は単一項とは限らない。一般次数では、複数の interaction 項の総和である。

---

## 3. Body は Core + Beam

正次数 `0 < d` に対して、Lean は

```lean
theorem body_eq_core_add_beam
    {d : ℕ} (hd : 0 < d) (x u : R) :
    BodyN d x u = Core d x + Beam d x u
```

を証明している。

従って DkMath の既存 `BodyN` は、新しい別量ではなく、

$$
\mathrm{Body}=\mathrm{Core}+\mathrm{Beam}
$$

という二層構造を持つ。

ここでいう Beam は「誤差」ではない。Big の内部に含まれる中間 interaction 全体である。

---

## 4. Big = Body + Gap

一般次数について、Lean の中心 theorem は

```lean
theorem big_eq_body_add_gap
    (d : ℕ) (x u : R) :
    Big d x u = BodyN d x u + Gap d u
```

である。

従って、DkMath の原型

$$
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}
$$

は exact identity である。

これは近似でも極限でもなく、有限代数段階で成立する。

---

## 5. Big = Core + Beam + Gap

前二定理を結合すると、正次数について

```lean
theorem big_eq_core_beam_gap
    {d : ℕ} (hd : 0 < d) (x u : R) :
    Big d x u = Core d x + Beam d x u + Gap d u
```

を得る。

すなわち、DkMath の基本三層構造は

$$
\mathrm{Big}
=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
$$

である。

ここで重要なのは、監査語彙の `Core / Beam / Gap / Big` と数学的対象名が偶然同じであっても、常に文脈を区別することである。

- audit 上の Core = Lean で確定した事実
- algebra 上の `Core d x` = 左端純冪

両者を混同しない。

---

## 6. CosmicFormulaBinom との関係

`CoreBeamGap` は既存 `CosmicFormulaBinom` の上に構築されている。

そこでは既に

```lean
Big d x u = (x + u)^d
Gap d u = u^d
Body d x u = x * G d x u
```

が置かれ、

```lean
theorem big_is_body_and_gap :
    Big d x u = Body d x u + Gap d u
```

および減算形

```lean
theorem cosmic_id :
    Big d x u - Body d x u = Gap d u
```

が証明されている。

従って `CoreBeamGap` の意義は、既存の

```text
Big / Body / Gap
```

を壊さず、その `Body` の内部をさらに

```text
Core + Beam
```

へ分解したことにある。

構造としては、

```text
Big
├─ Body
│  ├─ Core
│  └─ Beam
└─ Gap
```

と読むのが正確である。

---

## 7. 二次 ThreeElement は一般理論の特殊化

`d = 2` とすると、

$$
(x+u)^2=x^2+2xu+u^2
$$

なので、一般 `CoreBeamGap` は

$$
\mathrm{Core}=x^2
$$

$$
\mathrm{Beam}=2xu
$$

$$
\mathrm{Gap}=u^2
$$

へ縮退する。

ここで `ThreeElement.Basic` の

```lean
coreTerm x
interactionBeam x u
gapTerm u
```

と exact に同じ二次形が現れる。

従って `ThreeElement` は別理論ではない。

> 一般次数 `CoreBeamGap` のうち、interaction 部分が一つの cross term だけになる `d=2` の動的・極限向け API である。

と読むのが正しい。

---

## 8. 一般 Beam と interactionBeam の違い

ここは名前上の重要な firewall である。

一般次数では

```text
Beam d x u
```

は複数の中間二項項の和である。

一方、`ThreeElement` の

```text
interactionBeam x u
```

は二次の場合の単一 cross term

$$
2xu
$$

である。

したがって、一般 `Beam` を常に `2xu` と読むのは誤りである。

二次だけが特別に、

```text
middle interaction sum
=
single interaction term
```

となる。

---

## 9. Gap は外部補正ではない

宇宙式設計上もっとも重要な点の一つは、Gap を外から追加する補正項として扱わないことである。

一般 theorem が直接示すのは、

$$
\mathrm{Gap}=\mathrm{Big}-\mathrm{Body}
$$

である。

すなわち Gap は Big の内部から exact に回収される。

このため、RH / zeta projection 側で何か既存 remainder を見つけたとしても、それを先に `Gap` と命名してはならない。

安全な順序は、

```text
1. source 側で Big を構成
2. source 側で Body を構成
3. Big - Body として Gap を回収
4. 既知 observable との一致を後から証明
```

である。

これは CFZP 系で採用した「Gap firewall」と同じ原則である。

---

## 10. 極限論は別層

`CoreBeamGap.lean` 自体は純粋有限代数である。

ここには

```text
Filter.Tendsto
atTop
nhds
```

は登場しない。

従って

$$
\mathrm{Big}=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
$$

という exact decomposition から、各要素がある target へ同化することは自動ではない。

この静的・動的分離は、`0017` の MagicCore firewall と同じである。

- `CoreBeamGap` = 有限 exact decomposition
- `MagicCore` = 静的 target witness
- `Assimilation` = 動的 limit provider
- `Collision` = same-object limit contradiction

という四層を分けて扱う。

---

## 11. RH-CFBRC への意味

RH 側で三要素 collision を使う際、一般宇宙式から必要なものは既に存在する。

```text
finite exact decomposition
        ↓
CF2D d=2 specialization
        ↓
ThreeElementFlow
        ↓
pair assimilation
        ↓
interaction assimilation
        ↓
same-object collision
```

従って最終 Gap は一般代数の不足ではない。

`0015` で確認したとおり、RH 側で未解決なのは、実際の同じ carrier の interaction が同じ非零 target へ動的に同化することを、RH を仮定せず独立に供給する部分である。

一般 `CoreBeamGap` はその provider を仮定していないし、与えてもいない。

---

## 12. Audit ledger

### Core — CLOSED

- 任意次数の `Core`, `Beam`, `Gap`, `Big` 定義
- `Big = Body + Gap`
- 正次数で `Body = Core + Beam`
- 正次数で `Big = Core + Beam + Gap`
- `Gap = Big - Body` という exact 回収構造
- 二次 ThreeElement の代数的起源

### Beam — CLOSED

- 一般宇宙式から二次 CF2D / ThreeElement への概念的特殊化
- finite algebra と dynamic assimilation の層分離

### Gap — OPEN

- RH の具体 carrier に対する独立 interaction-assimilation provider
- 一般次数 Beam を zeta / prime source へ transport する場合の source-specific bridge

### Obstruction

一般代数 decomposition や静的 witness だけから動的 RH closure を導くことはできない。

---

## 13. 現在地

ここまでで依存地層は、

```text
general Cosmic Formula
  Big = Body + Gap
  Body = Core + Beam
        ↓
  Big = Core + Beam + Gap
        ↓
d = 2 specialization
        ↓
ThreeElement
        ↓
CF2D bridge
        ↓
RH dominant carrier
        ↓
same-object collision boundary
```

と一本につながった。

次に文書化すべき自然な層は、一般宇宙式のもう一つの基礎核である **差の因数分解 / PowerGapBeam** である。

そこでは

```text
z^d - x^d = (z - x) * Beam
```

という「Gap を境界差として先に抜き、残りを Beam と読む」構造を整理し、後の mirror difference / prime-side divided-difference へ接続する準備を行う。
