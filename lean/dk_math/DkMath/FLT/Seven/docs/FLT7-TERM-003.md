# FLT7-TERM-003

## FLT7-TERM-002 レビュー結果

**更新内容は採用します。判定は Outcome C：receiver の縮約は成功、証明すべき正確な橋が判明。**

対象コミット：

```text
4f812225e36e251608aeda6270cacc4ecf09720f
```

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5075977729)

Lean CI run 335 は **success** です。

## 今回よくなった点

旧 receiver は実質的に、

```lean
RowYProfile → False
RowZProfile → False
RowSumProfile → False
```

という terminal exclusion の言い換えでした。

今回、それを次の二つへ分解しています。

```text
AwaySevenBaseTerminalDefectStrictBounds
AwaySevenBaseTerminalReconstructedRowMismatch
```

そして `terminal_exclusion_of_receiver` は実際に、

```text
reconstructed
  → row mismatch

obstructed
  → strict bounds により defect = 0
  → defect_ne_zero と矛盾
```

という LIFT-003 の二枝を使っています。単なる receiver の名前変更ではなく、row arithmetic と reconstruction outcome が初めて一つの証明経路に接続されました。

さらに、

```lean
no_terminal_base_layer_of_receiver
terminal_exclusion_statement_of_receiver
```

により、`AwaySevenBaseLayerPacket` から actual terminal packet を構成して既存 descent audit の obligation へ戻す橋も完成しています。

## ただし、二つの obligation はまだ直接証明できない

### 1. Strict defect bounds は centeredness からは出ない

現在証明済みなのは、`weighted`、`model`、`scale` の各代表が個別に centered interval に入ることです。

しかし defect は例えば、

```text
weighted.u - model.u * scale^3
```

です。

個々の値が $M/2$ 以下でも、積 `model.u * scale^3` は大きくなり得ます。

簡単な scalar 例として、

```text
M = 5
model = 2
scale = 2
weighted = 1
```

なら、

$$1\equiv2\cdot2^3\pmod5$$

ですが、

$$d=1-16=-15$$

なので、

$$5\mid d$$

である一方、

$$|d|<5$$

は偽です。

これは full FLT7 packet の反例ではありません。しかし、

```text
modular weighted identity
+
各値の centeredness
```

だけでは `DefectStrictBounds` を導けないことを示します。

したがって、現在の strict bounds には **terminal 固有の新しい大小評価** が必要です。

### 2. Reconstructed row mismatch はまだ row equation と接続されていない

global model packet が保持するのは、四座標が各 local model へ還元されるという coordinate compatibility だけです。

ファイル自身も、一つの column-independent polynomial system は保持しないと明記しています。

そのため、

```lean
signed.weighted =
  signed.model.weightedScale signed.scale
```

だけから、

```text
endpoint quotient equation
cubic-root load equation
Row Y / Z / Sum profile
```

との矛盾はまだ出ません。

`AwaySevenBaseTerminalReconstructedRowMismatch` の theorem shape は正しい候補ですが、現時点の packet fields だけでは証明材料が足りません。

## 最初に修復すべき coherence

### A. `terminal.core` と `routing.core`

receiver は、

```lean
terminal : AwaySevenBaseTerminalUnitSectorPacket ...
routing  : AwaySevenBaseTerminalRoutingPacket ...
```

を持ちます。

両方の `.core` は同じ型ですが、

```lean
routing.core = terminal.core
```

を保持していません。

row profile は `terminal.core` から作られ、CRT family は `routing.core` から作られます。したがって、現在の型だけでは「同じ terminal quotient core の二つの表現」として比較できません。

ただし、これは修復可能です。fixed routing constructor は与えられた core をそのまま field に入れて witness を作っています。

次のような coherent packet を作れます。

```lean
structure AwaySevenBaseTerminalCoherentRoutingPacket
    (terminal :
      AwaySevenBaseTerminalUnitSectorPacket source r p) : Type where
  routing :
    AwaySevenBaseTerminalRoutingPacket (source := source) p
  core_eq :
    routing.core = terminal.core
```

または、constructor 内で `routing := { core := terminal.core, ... }` と直接組み立ててもよいです。

### B. orbit actual と original actual

もっと重要な欠落です。

各 prime-power actual は本来、

```lean
r.cubic.rootTriple.normal.root.fst
r.cubic.rootTriple.normal.root.snd
y
z
```

を local modulus へ落としたものです。`toPrimePowerSolution` はまさにその定義になっています。

しかし、

```lean
AwaySevenBaseTerminalPrimePowerOrbitPacket
```

は、

```text
depthPacket
orbit
```

を別々に保持するだけで、

```lean
orbit.toProjection.actual =
  depthPacket.depth.toPrimePowerSolution
```

を field に持ちません。

MODEL-002 で追加した `IsOrbitCoherent` も、

```lean
projection = orbit.toProjection
```

までであり、orbit actual と depth actual の同一性は対象外です。

ここに次の coherence が必要です。

```lean
def AwaySevenBaseTerminalPrimePowerOrbitPacket.IsActualCoherent
    (orbitPacket : ...) : Prop :=
  orbitPacket.orbit.toProjection.actual =
    orbitPacket.depthPacket.depth.toPrimePowerSolution
```

`primePowerOrbitSource_of_depthPacket` の実装は各分岐で実際に `p.toPrimePowerSolution` を actual として使っているので、**材料は存在します**。ただし `Nonempty` の外へ equality を保存していないだけです。

## 本命の突破口：global actual-coordinate bridge

上の actual coherence を family 全体へ運べば、各 local actual が元の整数座標の reduction であると証明できます。

その後 CRT の単射性から、

```lean
candidate.weighted =
  {
    u := (root.fst : ZMod M)
    v := (root.snd : ZMod M)
    y := (y : ZMod M)
    z := (z : ZMod M)
  }
```

を証明できます。

これは非常に重要です。

現在は、

```text
global weighted candidate
  → local actual
```

までです。

突破口を入れると、

```text
global weighted candidate
  → original integral coordinates modulo M
```

まで到達します。

row profile は元の `y`, `z`, root data を使っているので、ここで初めて signed lift と terminal quotient arithmetic が同じ対象を参照します。

## Strict bounds より exact winding が先

LIFT-003 ですでに、

$$M\mid d_u,\qquad M\mid d_v,\qquad M\mid d_y,\qquad M\mid d_z$$

は証明済みです。

したがって、まず次を構成できます。

```lean
structure AwaySevenBaseTerminalWindingPacket ... where
  ku kv ky kz : ℤ

  defect_u_eq :
    signed.integerWeightedDefect.u = M * ku

  defect_v_eq :
    signed.integerWeightedDefect.v = M * kv

  defect_y_eq :
    signed.integerWeightedDefect.y = M * ky

  defect_z_eq :
    signed.integerWeightedDefect.z = M * kz
```

これなら新しい仮定は不要です。既存 divisibility の witness を取り出すだけです。

そのうえで row profile が持つ exact factorization を投入します。

```text
Y:
  M = carrierUnit * z * (y + z)

Z:
  M = y * carrierUnit * (y + z)

Sum:
  M = y * z * carrierUnit
```

これらは現在の profile にそのまま含まれています。

さらに、

```text
selected endpoint は 7 を含む
M は 7-adic unit
unselected endpoint は M を割る
selected endpoint は M を割らない
```

という分離もすでにあります。

したがって探索すべきものは、無理に `k=0` を仮定する bound ではなく、

```text
row ごとに winding k が取り得る値
endpoint factorization と両立する winding
nonzero winding が強制する divisibility
```

です。

## 現在の mismatch は結論を先取りしている可能性がある

`reconstructed` branch が必ず contradiction になるとは、まだ確定していません。

可能性は二つあります。

```text
A. reconstructed branch が row equation と矛盾
   → terminal exclusion

B. reconstructed branch から小さい CounterexamplePack を再構成
   → descent provider
```

ROADMAP も Phase G の結果として、

```text
direct terminal exclusion
strict smaller counterexample
remaining arithmetic receiver
```

の三形を許しています。

したがって、actual-coordinate bridge を作る前に `ReconstructedRowMismatch` を証明目標として固定しすぎない方が安全です。

## 推奨する次の実装順

```text
FLT7-TERM-003-A
  terminal.core = routing.core coherence

FLT7-TERM-003-B
  orbit actual = depth actual coherence

FLT7-TERM-003-C
  candidate.weighted =
    original coordinates in ZMod combinedModulus

FLT7-TERM-003-D
  exact winding packet

FLT7-TERM-003-E
  row-resolved winding equations
  → contradiction または descent provider
```

## 結論

```text
TERM-002 receiver 縮約             完成
obstruction/reconstruction 接続     完成
base-layer end-to-end bridge         完成

strict defect bounds                 現材料だけでは証明不可
reconstructed row mismatch           polynomial/actual bridge 不足

terminal-routing core coherence      材料あり
original-actual coherence             材料あり
global actual-coordinate CRT theorem  coherence 後に証明可能
exact winding extraction              既存 divisibility だけで可能
row-resolved winding analysis         次の本命
```

**突破口はあります。**

ただし魔核は `|defect| < M` を直接証明することではなく、

```text
CRT weighted tuple
    =
元の整数座標 modulo full load
```

を先に確定し、

```text
defect = full load × winding
```

として winding を row profile の exact product identity へ流し込むことです。
