# GN / G Parameter-Order Investigation

Date: 2026-09-10
Status: design investigation only; no source implementation performed here
Source/build root: `lean/dk_math`

このメモは、ユーザー提供の `__git.diff` を指示書ではなく、試行変更の証拠として
調査した結果である。`analysis-001.md` / `analysis-002.md` の checkpoint 境界を
変更せず、今回の request に対する API 設計判断だけを記録する。

## 1. Conclusion

degree-bearing な API は `d x u` に揃えるのがよい。理由は、既に一般形の
`GTail d r x u` と legacy の `CosmicFormulaBinom.GN d x u` / `G d x u` がこの
順序であり、degree `d` が定義・定理・数論 consumer の看板引数になっているためで
ある。

ただし、単純な全置換は行わない。`GN` と `G` は namespace により意味が異なり、
`DkMath.CosmicFormulaBinom.G` と `DkMath.CosmicFormula.G` は同一の数学的 object
ではない。

## 2. Current semantic/API split

| declaration | current order | semantic role | recommended action |
|---|---|---|---|
| `DkMath.CosmicFormula.GTail` | `d r x u` | general tail | keep |
| `DkMath.CosmicFormula.GN` in `Defs` | `x u d` at HEAD; trial is `d x u` | `GTail d 1 x u`, gap-normalized | adopt `d x u` |
| `DkMath.CosmicFormula.GZ` in `Defs` | `x u d` | body-normalized kernel `x * GN` | separately migrate to `d x u` if desired |
| `DkMath.CosmicFormula.G` in `Defs` | `x u d` | legacy alias of `GZ` | keep only as `GZ` compatibility alias |
| `DkMath.CosmicFormulaBinom.GN` | `d x u` | legacy gap-normalized wrapper | keep order; target canonical `Defs.GN` |
| `DkMath.CosmicFormulaBinom.G` | `d x u` | pre-normalized gap kernel; `x * G = GZ` | do not target `Defs.G`; later target `GN` |

特に `CosmicFormulaBinom.G` と `CosmicFormula.G` の衝突が重要である。
前者は `GN` と `CommRing` 上で `GN_eq_G` により一致するが、後者は `GZ` の alias
であり、境界因子 `x` を既に含む。したがって `G -> GN` と `G -> GZ` を一つの
global rename として扱うと、型が通っても数式の意味を変える危険がある。

## 3. Evidence from the trial diff

### The order change itself

`Defs.GN` を `(R) d x u` に変更し、legacy wrapper を

```lean
DkMath.CosmicFormula.GN R d x u
```

へ変更する部分は、`GTail` の定義順および既存 `CosmicFormulaBinom.GN` と整合する。
`GTailCompatibility` の definitional compatibility もこの形で replay できた。

`SquareGnomon.squareGnomonKernel` の

```lean
DkMath.CosmicFormula.GN R 2 u x
```

への変更も、ここでは gnomon が `GTail 2 1 u x` を使うため、単なる順序変換として
意味が合っている。ただし、通常の `GN d x u` と引数を交換した gnomon 用途なので、
named arguments を使う方が読み違いを防ぎやすい。

### The apparent type-inference problem

試行 diff の `ZsigmondyCyclotomic.pow_sub_pow_factor_cosmic_N` は、定理が任意の
`{d : ℕ}` を受け取るのに、右辺だけを

```lean
DkMath.CosmicFormula.GN (d := 3) (x := a - b) (u := b)
```

へ固定していた。そのため build error は型推論ではなく、generic `d` と cubic
`3` の不一致として発生した。

実際の error は次の形である。

```text
target: a ^ d = (a - b) * CosmicFormula.GN ℕ 3 (a - b) b + b ^ d
hbig:  (a - b) * GN d (a - b) b + b ^ d
```

この theorem は直接 canonical 名へ書き換える場合も、`(d := d)` としなければ
ならない。`d = 3` の後続 theorem だけは `(d := 3)` で正しい。

### Focused validation

現状の試行変更に対して次を実行した。

```bash
cd lean/dk_math
lake build DkMath.CosmicFormula.Defs \
  DkMath.CosmicFormula.CosmicFormulaBinom \
  DkMath.CosmicFormula.SquareGnomon \
  DkMath.NumberTheory.ZsigmondyCyclotomic \
  DkMath.Zsigmondy \
  DkMathTest.CosmicFormula.GTailCompatibility
```

`Defs`、`CosmicFormulaBinom`、`SquareGnomon`、`GTailCompatibility` は replay できた。
`ZsigmondyCyclotomic` は上記の generic-`d` / fixed-`3` mismatch で失敗した。
従って、現試行をそのまま採用することはできないが、失敗原因は parameter-order
policy そのものではない。

## 4. Recommended migration shape

### Phase A: freeze the canonical order

canonical lower surface を次の形に固定する。

```lean
GTail d r x u
GN  (R) d x u
GZ  (R) d x u
```

`R` は現行どおり explicit に保ってもよい。型が `x` / `u` から一意に推論できる
通常の call は positional に

```lean
GN (R := ℕ) d x u
```

と書け、意味の取り違えが懸念される bridge では

```lean
GN (R := ℕ) (d := d) (x := x) (u := u)
```

と書ける。全 call site を named-argument 形式へ変換する必要はない。

`GZ` / `Defs.G` の d-first 化は `GN` と同じ checkpoint に詰め込まず、body-normalized
surface の独立した変更として行う。`Defs.G` を残す場合は `GZ` の compatibility alias
であることを docstring に明記する。

### Phase B: retain legacy wrappers without semantic collision

- `CosmicFormulaBinom.GN d x u` はそのまま残し、canonical `CosmicFormula.GN` へ
  deprecated 化する。
- `CosmicFormulaBinom.G d x u` は旧 gap-normalized vocabulary として残し、後で
  canonical `GN` へ staged deprecation する。
- `CosmicFormula.G` は旧 body-normalized alias として扱い、`GZ` への compatibility
  alias としてのみ整理する。`CosmicFormulaBinom.G` の replacement にしない。
- `GZ` / `GC` の移行は別 family として、各 owner と focused build を確認してから
  行う。

### Phase C: migrate direct canonical consumers

まず direct に `DkMath.CosmicFormula.GN` を呼ぶ少数の owner と regression だけを
移行し、generic theorem の `d` を固定しないことを確認する。その後、legacy
`CosmicFormulaBinom.GN` consumers は staged deprecation warning を build-log 順に
処理する。`GN d x u` の positional call は既に大量に存在するため、全 consumer を
named arguments に変換する必要はない。

## 5. Treatment of the current worktree

現在の trial diff は、`Defs.GN` の d-first 化という採用候補と、generic theorem の
誤った cubic 固定、canonical direct reference への大規模な置換を混在させている。
従って、そのまま積み上げず、設計確定後に trial source changes をいったん捨てて、
上記 Phase A の最小差分として作り直すのが安全である。

この調査では、ユーザー変更を保つため source の reset は実行していない。

## 6. Non-goals of this investigation

- `GN` / `G` consumer の global rename
- `G` と `GZ` の数学的同一視
- FLT / ABC / Zsigmondy / RH の一括 migration
- deprecation warning の全消去
- 新しい数学的 theorem の追加

## 7. Exact cause of the application type mismatch

この error の直接原因は、degree の順序だけではなく、型引数 `R` の explicit / implicit
属性の差である。

旧 wrapper は概念的に次の型を持つ。

```lean
@DkMath.CosmicFormulaBinom.GN :
  {R : Type u} → [CommSemiring R] → ℕ → R → R → R
```

そのため通常の `GN d x u` では、implicit な `R` が `x` / `u` から推論され、最初の
positional argument は `d` になる。

一方、試行中の canonical declaration は次の型である。

```lean
@DkMath.CosmicFormula.GN :
  (R : Type u) → [CommSemiring R] → ℕ → R → R → R
```

従って `DkMath.CosmicFormula.GN d x u` は elaborator には
`@DkMath.CosmicFormula.GN d ...` と見え、最初の `d : ℕ` を型引数 `R : Type u` に
渡そうとする。`__build.log` の

```text
argument d has type ℕ but is expected to have type Type ?u
in @CosmicFormula.GN d
```

はこの対応をそのまま表示している。error 中の `@` はユーザーが書いたものではなく、
Lean が implicit parameter を展開して表示しているものでもある。

したがって、現在の explicit-`R` API を維持するなら、次は正しい。

```lean
DkMath.CosmicFormula.GN (R := R) (d := d) (x := x) (u := u)
```

`x` / `u` から `R` が一意に推論できる箇所では、`(R := R)` を省略してもよい。

本当に単純な textual replacement
`GN d x u` → `DkMath.CosmicFormula.GN d x u` を成立させたい場合は、canonical
declaration の `R` を implicit にする必要がある。

```lean
@[simp] abbrev GN {R : Type*} [CommSemiring R]
    (d : ℕ) (x u : R) : R :=
  GTail d 1 x u
```

この変更を採用した場合、`DkMath.CosmicFormula.GN (R := R) d x u` はそのまま利用
でき、`DkMath.CosmicFormula.GN R d x u` と `DkMath.CosmicFormula.GN ℚ d x u` の
ように `R` を positional に渡していた箇所だけを更新する必要がある。

従って推奨は、`GN` については `R` implicit + `d x u` を canonical signature に
してから wrapper を置換すること、`G` については前節の semantic split を維持して
別 owner ごとに移行することである。
