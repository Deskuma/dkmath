# DkMath.ABC 現状調査メモ 001

## 1. 調査目的

`DkMath.ABC` リファクタリングの初手として、公開導線と kernel 候補の ownership のズレを確認する。
今回は「どこが重いか」「どこが重複しているか」を、import と定理配置の観点から固定する。

## 2. 公開導線の現状

現時点の入口は次の通り。

- `DkMath/ABC.lean`
  - `import DkMath.ABC.Main`
- `DkMath/ABC/Main.lean`
  - `import DkMath.ABC.ABC090`
  - `import DkMath.ABC.Bridge`
  - `import DkMath.ABC.ABC038Bridge`

したがって、現状では

```text
import DkMath.ABC
```

だけで、番号付き legacy chain と bridge 群をまとめて引く構造になっている。
これは `plan-refactoring.md` の「軽い公開面 / 重い full import の分離」という目標と一致していない。

## 3. kernel 候補の実測

### 3.1 `Core.lean`

`DkMath/ABC/Core.lean` は名前に反して、かなり混載している。

- `RpowExtras` namespace
  - `rpow_mul_nat`
  - `one_lt_rpow_two`
  - `denom_pos`
- ABC namespace の小補題
  - `three_pow_ge_linear`
  - `padicValNat_split`
  - `squarefree_prop`
  - `dvd_one_iff`
- さらに `rad_dvd_nonzero` もこのファイルに存在する

つまり `Core` は

```text
Real.rpow 補助
+ p-adic 補助
+ radical 補助
+ gcd / arithmetic 補助
```

の混合物になっている。

### 3.2 `Rad.lean`

`DkMath/ABC/Rad.lean` には

- `rad`
- `rad_zero`, `rad_one`
- `rad_dvd_nonzero`

がある。

つまり `rad_dvd_nonzero` は `Core` と `Rad` に重複している。
ownership の観点では、これは明らかに `Rad` 側へ寄せるべき候補である。

### 3.3 `Square.lean` と `Triple.lean`

`Square.lean` と `Triple.lean` は現在どちらも

```lean
import DkMath.ABC.Core
```

になっている。

だが実際には、

- `Square` は radical / squarefree 系が中心
- `Triple` は `Triple`, `Bad`, `BadCount`, `sliceBadCount` などの述語層

なので、少なくとも `rad` のためだけに `Core` を引いている構造は整理余地が大きい。

### 3.4 `PadicValNat.lean`

`DkMath/ABC/PadicValNat.lean` にも

- `padicValNat_split`

が存在する。

これは `Core.lean` にある同名補題と重複している。
したがって `padicValNat` 系の owner も現状では濁っている。

### 3.5 `Bridge.lean`

`DkMath/ABC/Bridge.lean` は薄い aggregator であり、

- `MassBridge`
- `ValuationFlowBridge`

のみを再公開している。

このファイル自体は軽い public-facing surface として設計意図が明確で、今回の refactor で壊す対象ではなく、むしろ守る対象である。

## 4. 現時点で見えている重複

今回の実測で、少なくとも以下の重複または ownership の曖昧さが確認できた。

### 4.1 radical 系

- `rad_dvd_nonzero`
  - `ABC/Core.lean`
  - `ABC/Rad.lean`

### 4.2 p-adic 系

- `padicValNat_split`
  - `ABC/Core.lean`
  - `ABC/PadicValNat.lean`

### 4.3 import ownership

- `Square.lean` が `Core` を import
- `Triple.lean` が `Core` を import

この 2 点は、`Core` が実質的に catch-all import になっている兆候である。

## 5. 第一段階の再編候補

現状から見て、最初に着手すべきなのは次の 3 点である。

1. `rad` の owner を `ABC.Rad` に固定する
2. `padicValNat` の owner を `ABC.PadicValNat` に固定する
3. `Core` を「本当に core かどうか」で分解する

より具体的には、

- `Square.lean` は `Rad` を直接引けるか検証
- `Triple.lean` は `Rad` と最小限の arithmetic helper に落とせるか検証
- `Core.lean` に残る `RpowExtras` 群は別ファイル化候補

という順で進めるのが自然である。

## 6. 今回の判断

`plan-refactoring.md` の大筋、すなわち

```text
rad を一本化
→ Kernel / Surface を新設
→ DkMath.ABC を軽量化
```

という方針は、今回の実測と整合している。

したがって次の作業では、

- まず radical/p-adic ownership の一本化
- その後に `Kernel.lean` / `Surface.lean` の導入

という順序を採るのが最善と判断する。
