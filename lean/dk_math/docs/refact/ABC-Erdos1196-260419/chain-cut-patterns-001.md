# ABC 連番チェイン切断メモ 001

## 目的

`ABC001.lean -> ABC002.lean -> ... -> ABC040.lean` の直列 import は、
分割時の保存を優先した結果であり、依存の最小化を反映していない。
このメモは、どの種類の依存が切りやすいか、どこが break point になりうるかを
次サイクルで再利用できる形に固定する。

## 現状の観測

- `ABC001` だけはすでに直列起点ではなく、
  `DkMath.ABC.Square` と `DkMath.ABC.RatioBound` を直接 import している。
- `ABC009` は `ABC008` に加えて `DkMath.ABC.Core` を直接 import している。
  これは `RpowExtras` owner がまだ `Core` に残っていることを示す。
- `ABC024`, `ABC025`, `ABC028` は
  `CountPowersDividing2n1` を直接 import しており、
  すでに serial chain を横切る seed になっている。
- `ABC025` はさらに
  `ABC025_bound2` と `PadicValNat` を直接 import している。
- `ABC002` 以降の多くの file は、
  依然として前番号 file を 1 本だけ import している。

## 切断パターン

### 1. Owner import 露出型

直列 predecessor を通じて見えていた補題が、
public entry build で unknown identifier として露出する型。

例:

- `coprime_succ` は `DkMath.Basic.Nat` owner
- `RpowExtras.rpow_mul_nat` は現状 `DkMath.ABC.Core` owner

処方:

- 使用 file に owner module を explicit import する
- 必要なら `open` または fully-qualified name に置き換える

効果:

- 直列 predecessor が「何となく持っていた」依存を可視化できる
- chain を切る前に、symbol owner の棚卸しが進む

### 2. Shared utility 横刺し型

複数の `ABC連番` file が同じ補題群を使うが、
それが predecessor を経由してしか見えていない型。

現時点の seed:

- `CountPowersDividing2n1`
- `PadicValNat`
- `Square`
- `RatioBound`

処方:

- serial predecessor ではなく utility module を直接 import する
- 同じ utility に依存する file 群を cluster として切り出す

効果:

- 「前番号だから import」ではなく
  「このテーマの kernel だから import」という構造へ寄せられる

### 3. Thin base + thematic band 型

連番の中に、同じテーマの帯が見えている。

候補:

- `ABC001`-`ABC009`:
  Adjacent / diagonal / middle-band 前段
- `ABC024`-`ABC028`:
  p-adic counting / layer-cake / MGF 帯
- `ABC031`-`ABC040`:
  tail / quality / Chernoff 接続帯

処方:

- 帯の先頭に utility import を寄せる
- 帯内部では predecessor import を減らし、
  帯の public seed file を 1 つ決める

効果:

- 40 本の鎖ではなく、数本の thematic chain に落とせる

## 次に試すと良い具体候補

### 候補 A: `RpowExtras` 専用 module 化

理由:

- `ABC009` が `Core` を直接 import する唯一の明確な理由が
  `RpowExtras.rpow_mul_nat` である
- ここを `ABC.RpowExtras` のような薄い module に切れば、
  `ABC009 -> Core` 依存を落とせる可能性が高い

期待効果:

- `Core` の catch-all 性をさらに削れる
- `ABC009` 以降の middle-band chain が `Core` 非依存に寄る

### 候補 B: `ABC024`-`ABC028` の utility-first 化

理由:

- すでに `CountPowersDividing2n1` と `PadicValNat` を直接 import し始めている
- serial predecessor が純粋な utility owner ではないことが可視化されている

期待効果:

- p-adic / layer-cake 帯の chain を短くできる
- `ABC025_bound2` を seed とする小 cluster 化がしやすい

進捗:

- 2026/04/21 の first cut で
  `ABC024.lean`
  から
  `import DkMath.ABC.ABC023`
  を外し、
  `ABC022` + `RatioBound` + `CountPowersDividing2n1`
  の direct import に置換した
- `ABC024`, `ABC025`, `ABC028`
  の build は成功
- この帯では
  empty relay
  を飛ばして owner import へ寄せるパターンが有効だと確認できた
- 次の観測点は、
  `ABC025` 以降で
  `ABC024`
  由来のものと
  `ABC025`
  自身の kernel をどう分離するか

### 候補 C: `ABC001`-`ABC003` の base seam 固定

理由:

- `ABC001` はすでに `Square`, `RatioBound` を直接 import している
- `ABC002`, `ABC003` で `coprime_succ` hidden import が露出し、
  owner import 明示化が始まった

期待効果:

- chain の先頭 3 本を「base combinatorial band」として扱える
- 以後の `ABC004+` から predecessor reliance を段階的に観測しやすい

## ノート

- `DkMath.ABC.Demo.*` は standalone / 非対象としてこのメモから除外する。
- `ABC090.lean` には comment block 内に `ABC041` 相当の残骸が見えるが、
  これは chain-cut とは別件の cleanup 候補である。
