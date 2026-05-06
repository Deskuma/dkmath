# リファクタ後構造設計: DkMath.Lib.Cosmic.GTail

## 目的

`GTail` 周辺の定理群は、純代数、Nat 可除性、合同、p-adic 付値が同じ旧ファイルに集まっていた。
今後 `DkMath.Lib.*` へ参照を置き換えていくため、分割後の構造を先に固定する。

この設計書の目的は次の 3 点。

- 分割先ファイルと依存方向を明確にする。
- 各 theorem をどの層へ置くかの判定基準を固定する。
- 旧 `DkMath.CosmicFormula.GTail` を downstream 互換の導線として残す方針を明確にする。

## 現在の入口構造

```text
import DkMath.Lib
  -> DkMath.Lib.Basic
  -> DkMath.Lib.Cosmic.GTail

import DkMath
  -> DkMath.Lib
  -> existing development modules

import DkMathlib
  -> DkMathlib.Basic
```

`DkMath.Lib` は開発側の再利用可能 Lib 入口。
`DkMathlib` は将来の公式公開入口であり、現時点では `DkMath` へ依存しない。

## 推奨ファイル構造

第一候補は、ファイル数を増やしすぎず、意味境界だけを切る次の構造。

```text
DkMath/Lib/Cosmic/GTail.lean
DkMath/Lib/Cosmic/GTailNat.lean
DkMath/Lib/Cosmic/GTailCongruence.lean
DkMath/Lib/Cosmic/GTailPadic.lean
```

旧ファイルは互換入口として残す。

```text
DkMath/CosmicFormula/GTail.lean
```

## 依存グラフ

推奨依存は次の形。

```text
DkMath.Lib.Cosmic.GTail
  -> DkMath.Lib.Cosmic.GTailNat
      -> DkMath.Lib.Cosmic.GTailCongruence
      -> DkMath.Lib.Cosmic.GTailPadic

DkMath.CosmicFormula.GTail
  -> DkMath.Lib.Cosmic.GTailNat
  -> DkMath.Lib.Cosmic.GTailCongruence
  -> DkMath.Lib.Cosmic.GTailPadic
```

重要な点:

- `GTail` は純代数コアなので `Mathlib` だけに閉じる。
- `GTailNat` は `Nat` の可除性・減算・素数条件までを扱う。
- `GTailCongruence` は `Nat.ModEq` と mod `p^2` / mod `p^3` の具体合同を扱う。
- `GTailPadic` は `DkMath.ABC.PadicValNat` に初めて依存する層。
- `GTailCongruence` と `GTailPadic` は兄弟層としておき、片方が片方へ依存しない設計を優先する。

## Namespace 方針

当面は既存 downstream 互換を優先し、Lib 配下ファイルでも namespace は維持する。

```lean
namespace DkMath.CosmicFormula
```

理由:

- 既存参照 `DkMath.CosmicFormula.GTail` を壊さない。
- 移行作業を import 差し替え中心で進められる。
- 大規模 rename を後段に分離できる。

将来 `DkMath.Lib.Cosmic` namespace へ移す場合は、今回の分割とは別タスクにする。

## 層ごとの配置

### DkMath.Lib.Cosmic.GTail

役割: 純代数コア。

許可依存:

```lean
import Mathlib
```

配置済みまたは配置対象:

```lean
GTail
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_self_eq_one
GTail_rec
GN_tail_rec
GN_tail_decomposition
Gbinom_tail_rec
GTail_one_eq_sum
GTail_eval_zero
GN_zero_eval
Gbinom_zero_eval
```

判定基準:

- 任意の `CommSemiring` / `CommRing` で述べられる。
- `Nat.ModEq`、`padicValNat`、`DkMath.ABC.*` を使わない。
- `ℕ` 専用の可除性を主張しない。

### DkMath.Lib.Cosmic.GTailNat

役割: `ℕ` 上の可除性・head-unit 非可除性。

想定 import:

```lean
import DkMath.Lib.Cosmic.GTail
```

配置対象:

```lean
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
```

判定基準:

- 型が `ℕ` に固定されている。
- `∣`、`Nat.Prime`、`Nat` 減算を使う。
- `Nat.ModEq` を主 API にしない。
- `padicValNat` を使わない。

注意:

`GTail_not_dvd_of_head_unit_of_prime_dvd_x` は名前上 p-adic 風だが、実体は divisibility のみなので `GTailNat` に置く。

### DkMath.Lib.Cosmic.GTailCongruence

役割: `Nat.ModEq` と具体的な mod head collapse。

想定 import:

```lean
import DkMath.Lib.Cosmic.GTailNat
```

配置対象:

```lean
sum_range_modEq
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
GN_modEq_choose_mul_pow_of_dvd_x
GN_modEq_head_of_dvd_x
GN_modEq_mul_pow_self_of_dvd_x
GN_modEq_head_mod_sq_of_prime_dvd_x
GN_mod_p2_head
GN_eq_head_add_p_sq_mul_of_prime_dvd_x
GN_mod_p3_head
GN_eq_head_add_p_cube_mul_of_dvd_tail
```

判定基準:

- 主結論が `≡ ... [MOD n]`。
- mod `p^2` / mod `p^3` など、合同から具体等式へ戻す補題。
- `padicValNat` へは依存しない。

注意:

`sum_range_modEq` は内部補題なら `private theorem` のままでよい。
他ファイルから再利用したくなった時点で公開名へ昇格する。

### DkMath.Lib.Cosmic.GTailPadic

役割: `padicValNat` による付値評価。

想定 import:

```lean
import DkMath.Lib.Cosmic.GTailNat
import DkMath.ABC.PadicValNat
```

配置対象:

```lean
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_higher_tail_lower_bound
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
```

判定基準:

- `padicValNat` が statement または proof に出る。
- `DkMath.ABC.padicValNat_*` 補題を使う。
- 合同ではなく付値の等式・不等式を主張する。

注意:

名前に `ABC` は入れない。
依存として `DkMath.ABC.PadicValNat` を使うが、内容は cosmic tail の p-adic API として Lib 側に置く。

## 旧 DkMath.CosmicFormula.GTail の扱い

旧ファイルは当面 compatibility shell にする。

```lean
import DkMath.Lib.Cosmic.GTailNat
import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.Lib.Cosmic.GTailPadic

#print "file: DkMath.CosmicFormula.GTail"

open scoped BigOperators

namespace DkMath.CosmicFormula

end DkMath.CosmicFormula
```

原則:

- theorem 本体は Lib 側へ移す。
- 旧ファイルに同名 wrapper は作らない。同じ namespace に同名定理を再定義できないため。
- downstream は `import DkMath.CosmicFormula.GTail` のままでも壊れない。
- 新規コードは `import DkMath.Lib.Cosmic.*` を使う。

## DkMath.Lib 入口の更新方針

最終的には `DkMath.Lib` から GTail 周辺の安定層をまとめて使えるようにする。

```lean
import DkMath.Lib.Basic
import DkMath.Lib.Cosmic.GTail
import DkMath.Lib.Cosmic.GTailNat
import DkMath.Lib.Cosmic.GTailCongruence
import DkMath.Lib.Cosmic.GTailPadic
```

ただし、`GTailPadic` は `DkMath.ABC.PadicValNat` へ依存するため、入口に含めるかは最後に判断する。

推奨:

- 第一段階: `GTail`、`GTailNat`、`GTailCongruence` までを `DkMath.Lib` に入れる。
- 第二段階: `GTailPadic` の import コストと公開方針を見てから追加する。

## 移行順

### Step 1. GTailNat

1. `DkMath/Lib/Cosmic/GTailNat.lean` を作る。
2. `pow_dvd_higher_tail`、head-unit 非可除性 2 本を移す。
3. `DkMath.CosmicFormula.GTail` から該当ブロックを削除し、`GTailNat` を import する。
4. build:

```sh
lake build DkMath.Lib.Cosmic.GTailNat
lake build DkMath.CosmicFormula.GTail
```

### Step 2. GTailCongruence

1. `DkMath/Lib/Cosmic/GTailCongruence.lean` を作る。
2. `Nat.ModEq` 系と mod `p^2` / mod `p^3` 系を移す。
3. 旧ファイルは import のみに寄せる。
4. build:

```sh
lake build DkMath.Lib.Cosmic.GTailCongruence
lake build DkMath.CosmicFormula.GTail
```

### Step 3. GTailPadic

1. `DkMath/Lib/Cosmic/GTailPadic.lean` を作る。
2. `padicValNat_*` 系を移す。
3. `DkMath.ABC.PadicValNat` 依存がこのファイルだけに閉じていることを確認する。
4. build:

```sh
lake build DkMath.Lib.Cosmic.GTailPadic
lake build DkMath.CosmicFormula.GTail
```

### Step 4. 入口更新

1. `DkMath/Lib.lean` の import を更新する。
2. `DkMath` 全体入口を確認する。
3. build:

```sh
lake build DkMath.Lib
lake build DkMath
```

## 完了条件

この分割リファクタは、次を満たした時点で完了とする。

- `DkMath.Lib.Cosmic.GTail` は純代数だけを含む。
- `DkMath.Lib.Cosmic.GTailNat` は `padicValNat` に依存しない。
- `DkMath.Lib.Cosmic.GTailCongruence` は `padicValNat` に依存しない。
- `DkMath.Lib.Cosmic.GTailPadic` だけが `DkMath.ABC.PadicValNat` に依存する。
- `DkMath.CosmicFormula.GTail` は compatibility import shell になる。
- 既存 downstream は namespace 変更なしで build できる。

## 保留事項

### GN 専用ファイル

将来、`r = 1` の薄い API が増えるなら次を検討する。

```text
DkMath/Lib/Cosmic/GN.lean
```

ただし現段階では `GTail` の specialization として同居させる。

### Directory 型への再編

定理数がさらに増える場合は、将来次の形へ移れる。

```text
DkMath/Lib/Cosmic/GTail/Basic.lean
DkMath/Lib/Cosmic/GTail/Nat.lean
DkMath/Lib/Cosmic/GTail/Congruence.lean
DkMath/Lib/Cosmic/GTail/Padic.lean
```

ただし現段階では `GTailNat` などの flat file 名の方が移行コストが低い。

### Namespace の Lib 化

`namespace DkMath.Lib.Cosmic` への移行は、今回のファイル分割とは分ける。
実施するなら alias / deprecation / downstream rewrite 方針を別設計書で扱う。
