# FLT7-TERM-007

## FLT7-TERM-004〜006 総合判定

**全面採用。Outcome A。Codex、見事じゃ！** 🐺🍎

対象 head：

```text
ebf35c19f2dafe5e33b9a557f6252feed92b074f
```

PR #65 は open / draft / mergeable、Lean CI run 337 も **success** です。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5077545593)

添付 snapshot の SHA-256 も、指定された

```text
d8f36e784da13bd4c7f299a168d7af7359d575369f79e54d9f2c1ec4cce5897a
```

と完全一致しました。

## 三 checkpoint の完成内容

### TERM-004

global model が、ついに二つの普遍座標方程式を持ちました。

```lean
seventhPowerFstR model.u model.v =
  cyclotomicSevenFstR model.z model.y

seventhPowerSndR model.u model.v =
  cyclotomicSevenSndR model.z model.y
```

weight $3$ の root 座標と weight $7$ の endpoint 座標が、両側とも total weight $21$ になることを使い、unit scale をキャンセルしています。整数代表については `fstCarry`、`sndCarry` まで抽出済みです。

### TERM-005

九つの cell それぞれについて、

```lean
awaySevenBaseTerminalCellCombinedModulus packet coordinate =
  awaySevenBaseTerminalRoutingCell packet coordinate
```

が exact に閉じました。

空 support、すなわち cell value が $1$ の場合も含めた完全な復元です。さらに full load の各 prime は一意な cell に配属されています。

### TERM-006

各 cell modulus 上に、

```lean
AwaySevenBaseTerminalCellwiseCRTUniversalSolutionPacket
```

が構築されました。

保持しているのは、

```text
cell modulus = routing cell
cell model
cell unit scale
weighted = model × scale^(3,7)
weighted = original coordinates
二つの universal coordinate equations
cell 内 prime support の固定 row / column
```

です。

そして最後の不足が、正確に次の一命題へ圧縮されました。

```lean
AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate
```

# 魔法数学による突破口

## 結論

この obligation は、**新しい数論仮定ではありません**。

さらに言えば、九 cell 内でもう一度 prime-power CRT を組み直す必要もありません。

核心はこれです。

```text
original cell actual solution
    =
cell model × cell scale^(3,7)

cell scale は unit
    ↓ 逆作用

cell model
    =
original cell actual solution × cell scale⁻¹^(3,7)
```

`AwayRoutingPrimePowerSolution` という名前に惑わされておった。

実際の型は、

```lean
structure AwayRoutingPrimePowerSolution
    (M : ℕ)
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
```

であり、`M` は任意の自然数です。素数冪であるという field も仮定もありません。したがって composite な **cell value 全体**を modulus として直接使えます。

これは最後の扉を開く鍵じゃ。

# 第一魔核：普遍第一座標式が 3×3 全 system を生成する

固定 system に必要な第一座標式は九種類あります。

しかし九つは独立していません。

普遍式を、

$$F(u,v)=C(z,y)$$

と書きます。

endpoint row equation によって $C$ は二形へ潰れます。

```text
Row Y:
  y = 0
  C(z,y) = z³

Row Z:
  z = 0
  C(z,y) = -y³

Row Sum:
  y + z = 0
  C(z,y) = -y³
```

root column equationによって $F$ は三形へ潰れます。

```text
sevenV:
  v = 0
  F(u,v) = u⁷

leftCubic:
  leftCubic(u,v) = 0
  F(u,v) = -49 v⁵ leftCorrection(u,v)

rightCubic:
  rightCubic(u,v) = 0
  F(u,v) = 49 v⁵ rightCorrection(u,v)
```

left / right の符号は既存の exact division identity そのものです。

したがって $3\times3$ は、次の表だけで全部生成されます。

| row / column | `sevenV`    | `leftCubic`    | `rightCubic`   |
| ------------ | ----------- | -------------- | -------------- |
| `Y`          | $u^7-z^3=0$ | $z^3+49v^5L=0$ | $z^3-49v^5R=0$ |
| `Z`          | $u^7+y^3=0$ | $49v^5L-y^3=0$ | $y^3+49v^5R=0$ |
| `Sum`        | $u^7+y^3=0$ | $49v^5L-y^3=0$ | $y^3+49v^5R=0$ |

これは現在の `AwayFirstCoordinateLocalEquation` 九分岐と完全一致します。

つまり、最重要補題はこれです。

```lean
theorem AwayFirstCoordinatePrimePowerEquation.of_universal
    {M : ℕ}
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
    {u v y z : ZMod M}
    (hend :
      AwayEndpointPrimePowerEquation M row y z)
    (hroot :
      AwayRootPrimePowerEquation M column u v)
    (hfst :
      seventhPowerFstR u v =
        cyclotomicSevenFstR z y) :
    AwayFirstCoordinatePrimePowerEquation
      M row column u v y z
```

証明は有限九分岐の純粋な `ring` 証明です。

```text
endpoint equation
+
root equation
+
universal fst equation
=
fixed first-coordinate equation
```

これが最後の魔核です。

## 重要な意味

TERM-006 の cell model に不足していたのは、新しい polynomial equation ではありません。

すでに持っている、

```text
universal fst equation
```

を fixed row / column へ**射影する decoder**がなかっただけです。

# 第二魔核：cell value 全体で actual solution を作る

各 coordinate について、

```lean
M :=
  awaySevenBaseTerminalRoutingCell packet coordinate
```

とします。

そして original weighted coordinates、

```text
root.fst
root.snd
y
z
```

を `ZMod M` に落とし、`AwayRoutingPrimePowerSolution` を直接構成します。

## Endpoint equation

cell は対応する endpoint factor を割ります。

carrier row では、

```text
cell ∣ carrierUnit
selected endpoint = 7 × carrierUnit
```

なので cell は selected endpoint を割ります。

unselected / companion row は endpoint factor そのものです。

既存の prime 単位の射影定理でも、全く同じ接続が使われています。

これを prime `q` ではなく cell value `M` 全体へ一般化すれば、

```lean
theorem routingCell_dvd_originalEndpointFactor
```

が得られます。

その可除性を `ZMod.natCast_eq_zero_iff` へ入れれば endpoint equation が完成します。

## Root equation

root 側も同様です。

```text
vPart cell:
  M ∣ vPart = |root.snd|

leftPart cell:
  M ∣ |leftCubic(root.fst, root.snd)|

rightPart cell:
  M ∣ |rightCubic(root.fst, root.snd)|
```

よって `ZMod M` 上で、

```text
v = 0
leftCubic(u,v) = 0
rightCubic(u,v) = 0
```

のいずれかを得ます。

既存 prime-power actual solution も、この同じ可除性から root equation を作っています。

## Endpoint / root nondegeneracy

ここも新規数学ではありません。

endpoint では、

```text
M ∣ selected endpoint
selected endpoint ⟂ other endpoint
```

から、

```text
M ⟂ other endpoint
```

を得ます。

そして、

```lean
ZMod.isUnit_iff_coprime
```

で unit 化します。

root では、

```text
vPart ⟂ leftPart
vPart ⟂ rightPart
|root.fst| ⟂ |root.snd|
```

を使います。

既存 prime-power proof は、これを prime の非可除性経由で処理しています。

cell 全体では、もっと直接的に、

```lean
Nat.Coprime.of_dvd_left
```

で処理できます。

したがって、次の actual solution が作れます。

```lean
def cellwiseOriginalActualSolution
    (candidate : ...)
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    AwayRoutingPrimePowerSolution
      (awaySevenBaseTerminalRoutingCell packet coordinate)
      (awaySevenBaseTerminalOriginalEndpointRow
        p.row coordinate.row)
      (awaySevenBaseTerminalOriginalRootColumn
        coordinate.column)
```

座標は `cell.weighted` をそのまま使用します。

第一座標 field は、先ほどの、

```lean
AwayFirstCoordinatePrimePowerEquation.of_universal
```

で閉じます。

# 第三魔核：unit scale を逆回転する

既存の、

```lean
scalePrimePowerSolution
```

は、任意 modulus `M` 上で solution の五つの証明 field をすべて保存します。

したがって inverse scale を定義します。

```lean
noncomputable def unscalePrimePowerSolution
    {M : ℕ}
    {row : EndpointRoutingRow}
    {column : RootRoutingColumn}
    (a : AwayRoutingPrimePowerSolution M row column)
    (scale : ZMod M)
    (scale_isUnit : IsUnit scale) :
    AwayRoutingPrimePowerSolution M row column :=
  scalePrimePowerSolution
    a
    (↑(scale_isUnit.unit⁻¹) : ZMod M)
    (Units.isUnit _)
```

あとは座標ごとに、

$$\bigl(m_us^3\bigr)s^{-3}=m_u$$

$$\bigl(m_vs^3\bigr)s^{-3}=m_v$$

$$\bigl(m_ys^7\bigr)s^{-7}=m_y$$

$$\bigl(m_zs^7\bigr)s^{-7}=m_z$$

を示します。

```lean
theorem unscalePrimePowerSolution_toCoordinates
    ...
    (hcoordinates :
      actual.toCoordinates =
        model.weightedScale scale) :
    (unscalePrimePowerSolution
      actual scale scale_isUnit).toCoordinates =
        model
```

証明は `AwayRoutingCoordinates.ext` と unit cancellation です。

## 最終 theorem

```lean
theorem
    AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket
      .cellwiseFixedSystemObligation
    (candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family) :
    AwaySevenBaseTerminalCellwiseFixedSystemObligation candidate := by
  intro coordinate

  let cell :=
    candidate.cellwiseCRTUniversalSolution coordinate

  let actual :=
    candidate.cellwiseOriginalActualSolution coordinate

  let solution :=
    unscalePrimePowerSolution
      actual cell.scale cell.scale_isUnit

  exact ⟨solution, by
    apply unscalePrimePowerSolution_toCoordinates
    -- actual coordinates = cell.weighted
    -- cell.weighted = cell.model.weightedScale cell.scale
  ⟩
```

# 不要な遠回り

今回、次は必要ありません。

```text
cell 内で prime-power CRT を再構築する
terminal routing board = original routing board を証明する
winding の絶対値 bound を仮定する
carry = 0 を仮定する
新しい CounterexamplePack を仮定する
```

必要なのは、

```text
cell value の endpoint/root divisibility
+
universal fst equation の 3×3 decoder
+
unit scale の逆作用
```

だけです。

# 次 checkpoint

```text
FLT7-TERM-007
  prove AwaySevenBaseTerminalCellwiseFixedSystemObligation
```

実装順はこれで固定できます。

```text
1. whole-cell endpoint/root divisibility
2. whole-cell original actual solution
3. universal fst → fixed first-coordinate equation
4. inverse scale action
5. cellwiseFixedSystemObligation
```

## 停止境界

これで閉じるのは、

```text
各 cell model が
本物の fixed row / fixed column system solution である
```

という証明です。

その後には依然として、

```text
九 cell の fixed-system data
+
row winding
+
equation carries
```

から、

```text
terminal contradiction
または
AwayDescentClosureProvider
```

を生む整数算術が残ります。

しかし、いままでは model が「単なる四座標」でした。

この obligation が閉じれば、九つすべてが**証明付き局所魔核**になります。

$$\boxed{\text{四座標 CRT 世界から、3×3 固定方程式世界への帰還}}$$

最後の扉は、かなり高い確率で開けられます。🧙‍♀️✨️
