# FLT7-TERM-008

## TERM-007 判定

**Outcome A。最後の型上の壁は閉じました。** 🧙‍♀️✨️

報告された最終定理、

```lean
candidate.cellwiseFixedSystemObligation
```

により、九つの cell model はすべて、

```text
固定 endpoint row
固定 root column
endpoint 非退化性
endpoint 方程式
root 非退化性
root 方程式
first-coordinate 方程式
```

を備えた真正な `AwayRoutingPrimePowerSolution` へ昇格しました。

これは重要です。TERM-006 時点では、cell model は二つの普遍方程式を持つ四座標でした。今回、それが九種類の明示的な局所 system へ戻りました。`AwayRoutingPrimePowerSolution` が要求する証明 field はこの五種類です。

また、突破方法も構造的に最短です。

```text
whole-cell original actual
        =
cell model × unit scale^(3,7)
        ↓ inverse unit action
cell model is a fixed-system solution
```

既存の `scalePrimePowerSolution` は任意 modulus 上で全 system field を保存するため、逆 unit action を使う設計は完全に正当です。

### 確認境界

TERM-007 は未 push なので、GitHub 上の独立コード監査はまだできません。現在公開されている PR head は TERM-004〜006 の、

```text
ebf35c19f2dafe5e33b9a557f6252feed92b074f
```

です。

したがって今回の Outcome A は、ローカル build・axiom 報告・提示された実装内容に基づく判定です。push 後に差分レビューできます。

---

## TERM-008 の本当の目的

提案された、

```text
cellwise fixed-system integer carry packet
```

は正しい実験です。

ただし、**carry を集めること自体をゴールにしてはいけません**。

第一座標式は TERM-007 で、

```text
universal fst equation
+
endpoint equation
+
root equation
```

から復元されています。

したがって first-coordinate carry も、おそらく、

```text
global universal carry
+
endpoint carry
+
root carry
```

の代数的結合にすぎません。

TERM-008 はこれを Lean に判定させる **独立性監査** にすべきです。

```text
carry が非自明な新条件を生む
  → contradiction / descent receiver へ進む

carry が恒等的に従属する
  → carry 路線を終了
  → canonical cell orbit compatibility へ移る
```

どちらに転んでも前進です。

## 推奨する TERM-008 の構造

### 1. 独立な cell centered representative を作らない

各 cell で `valMinAbs` を取り直すと、人工的な coordinate carry が増えます。

TERM-008 では、すでにある full-modulus signed model、

```lean
signed.model : AwayRoutingCoordinates ℤ
```

をそのまま各 cell modulus へ cast してください。

必要な橋は次です。

```lean
theorem signedModel_cast_cell
    (coordinate : AwaySevenBaseTerminalCellCoordinate) :
    signed.model.map
        (fun a : ℤ =>
          (a : ZMod
            (awaySevenBaseTerminalRoutingCell packet coordinate))) =
      (candidate.cellwiseCRTUniversalSolution coordinate).model
```

これなら九 cell が**同じ四つの整数代表**を共有します。

carry 間の比較が可能になります。

### 2. 三種類の residual を定義する

```lean
def AwayEndpointIntegerResidual
    (row : EndpointRoutingRow) (y z : ℤ) : ℤ :=
  match row with
  | .y   => y
  | .z   => z
  | .sum => y + z
```

```lean
def AwayRootIntegerResidual
    (column : RootRoutingColumn) (u v : ℤ) : ℤ :=
  match column with
  | .sevenV    => v
  | .leftCubic => seventhPowerSndLeftCubic u v
  | .rightCubic => seventhPowerSndRightCubic u v
```

```lean
def AwayFirstCoordinateIntegerResidual
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
    (u v y z : ℤ) : ℤ :=
  -- AwayFirstCoordinateLocalEquation の九分岐と同じ式
```

固定 system の九式はすでに明示されています。

### 3. cell carry packet

```lean
structure AwaySevenBaseTerminalCellIntegerCarryPacket
    (coordinate : AwaySevenBaseTerminalCellCoordinate) : Type where
  modulus : ℕ
  modulus_eq :
    modulus =
      awaySevenBaseTerminalRoutingCell packet coordinate

  endpointCarry : ℤ
  rootCarry : ℤ
  firstCarry : ℤ

  endpoint_eq :
    AwayEndpointIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        signed.model.y signed.model.z =
      modulus * endpointCarry

  root_eq :
    AwayRootIntegerResidual
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v =
      modulus * rootCarry

  first_eq :
    AwayFirstCoordinateIntegerResidual
        (awaySevenBaseTerminalOriginalEndpointRow p.row coordinate.row)
        (awaySevenBaseTerminalOriginalRootColumn coordinate.column)
        signed.model.u signed.model.v signed.model.y signed.model.z =
      modulus * firstCarry
```

三つの可除性は `candidate.cellwiseFixedSystemObligation` と `signedModel_cast_cell` から抽出できます。

---

## 中心となる魔法恒等式

TERM-008 で最初に証明すべきものは carry の存在ではなく、次の exact identity です。

```lean
theorem fixedFirstResidual_decomposition
    (row : EndpointRoutingRow)
    (column : RootRoutingColumn)
    (u v y z : ℤ) :
    AwayFirstCoordinateIntegerResidual row column u v y z =
      -- universal fst residual
      -- + endpoint residual × explicit coefficient
      -- + root residual × explicit coefficient
```

九分岐はすべて既存の恒等式から生成できます。

普遍 residual を、

$$U=F(u,v)-C(z,y)$$

と置きます。

### Row Y

$$C(z,y)-z^3=y(z-y)(z+y)$$

この恒等式は既存です。

### Row Z / Sum

$$C(z,y)+y^3=z^2(z+y)$$

これも既存です。

### Column sevenV

$$F(u,v)-u^7=v^2Q_V(u,v)$$

### Column leftCubic

$$F(u,v)=L(u,v)Q_L(u,v)-49v^5C_L(u,v)$$

### Column rightCubic

$$F(u,v)=R(u,v)Q_R(u,v)+49v^5C_R(u,v)$$

したがって九つの first residual はすべて、

$$\pm U+A(u,v,y,z),E+B(u,v,y,z),R$$

という形へ落ちます。

ここで $E$ は endpoint residual、$R$ は root residual です。

---

## carry dependency theorem

cell modulus を $m_c$、full combined modulus を $M$ とします。

すでに global equation carry により、

$$U=Mk_F$$

です。TERM-004 の packet がこれを保持しています。

また、各 cell は full load を割るため、

$$M=m_cQ_c$$

となる quotient $Q_c$ を取れます。

すると residual decomposition から、

$$m_c k_{\mathrm{first}}=\pm M k_F+A,m_c k_{\mathrm{endpoint}}+B,m_c k_{\mathrm{root}}$$

したがって $m_c\ne0$ を使ってキャンセルすれば、

$$k_{\mathrm{first}}=\pm Q_c k_F+A,k_{\mathrm{endpoint}}+B,k_{\mathrm{root}}$$

を得ます。

Lean の中心 theorem はこの形です。

```lean
theorem AwaySevenBaseTerminalCellIntegerCarryPacket.firstCarry_eq
    (cell : AwaySevenBaseTerminalCellIntegerCarryPacket ...)
    (global :
      AwaySevenBaseTerminalIntegerEquationCarryPacket signed) :
    cell.firstCarry =
      fixedUniversalSign coordinate *
          cell.fullModulusQuotient * global.fstCarry
        + fixedEndpointCoefficient ... * cell.endpointCarry
        + fixedRootCoefficient ... * cell.rootCarry
```

## 予想される判定

わっちの現在の予測は、

```text
first-coordinate carry は完全従属
```

です。

理由は、TERM-007 の decoder 自体が純粋な polynomial identity だからです。

つまり first carry は新しい魔核ではなく、既存三式の bookkeeping である可能性が高い。

これは失敗ではありません。

```text
first-coordinate carry に新情報なし
```

を Lean theorem として確定すれば、以後そこへ探索資源を使わずに済みます。

## 非自明な情報が残る可能性

carry の中で本当に独立し得るのは、

```text
endpoint carries
root carries
```

と、それらを九 cell で共有する global integer representatives です。

さらに重要なのは、carry equation 自体では使われていない次の情報です。

```text
endpoint/root nondegeneracy
scale is a unit
local canonical orbit
same global model の九 cell reduction
```

carry が恒等的に潰れた場合、次の本命は、

```text
cellwise fixed solution
        ↓
cellwise canonical composite orbit
        ↓
九 cell の canonical parameters の同時整合性
```

です。

特に left/right cell では、composite modulus 上でも、

```text
t = u * v⁻¹
cubic(t) = 0
correction(t) is a unit
```

が取れます。

Bezout 恒等式、

$$A(t)P(t)+B(t)C(t)=7$$

と $7$ が全 cell modulus で unit であることを使えば、correction の unit 性は prime-power に分解せず証明できます。既存の Bezout 恒等式はすでにあります。

これは carry より強い情報です。

## 次 checkpoint

```text
FLT7-TERM-008
cellwise fixed-system carry dependency audit
```

到達判定を二つにしてください。

```text
Outcome A
  first carry が endpoint/root/global carry から完全決定
  → carry は従属と確定
  → canonical composite orbit へ進む

Outcome B
  dependency identity 後にも独立条件が残る
  → exact contradiction/descent receiver として固定
```

## 現在地

```text
TERM-004  universal equations       完成
TERM-005  exact cell partition      完成
TERM-006  cellwise universal model  完成
TERM-007  cellwise fixed system     完成

残り：
  fixed-system data が
  新しい整数制約を持つかの判定
```

**九つの魔核はすべて開いた。**

次は中身が本当に九つの異なる魔法なのか、それとも一つの普遍魔法を九方向から見ただけなのかを Lean に裁かせる段階です。
