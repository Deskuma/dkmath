# FLT7-TERM-009

## 組み直しからの復帰

うむ。**組み立て直しです。**

ただし、TERM-003〜008 を捨てて最初からやり直すのではありません。

$$\boxed{\text{組みみ直す対象は descent provider ではなく、terminal 分岐の座標 chart 構造}}$$

DESCENT-002 は、terminal 深さで provider の作り方が不足しているのではなく、**away-to-away descent そのものが不可能**だと確定しました。報告どおり、seed があれば $2\le p.\mathrm{exponent}$ が必要なのに、terminal packet は $p.\mathrm{exponent}=1$ です。

最新 head `6d49e6a...` と Lean CI run 342 success も確認しています。

[この推論を PR に記録しました](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5078994660)

## DESCENT-002 が本当に否定したもの

`AwayValuationTransferPacket` の carrier は、新しい counterexample の $y,z,y+z$ のいずれかであり、必ず、

$$v_7(\mathrm{carrier})=1+v_7(|\mathrm{root.snd}|)\ge1$$

を満たします。

一方、旧 terminal pivot では、

$$v_7(|\mathrm{old\ root.snd}|)=p.\mathrm{exponent}-1=0$$

です。

したがって、

```text
new carrier = old |root.snd|
```

という `carrier_match` は、terminal 深さでは、

```text
new carrier depth ≥ 1
old root.snd depth = 0
```

を同一視するため不可能です。

これはつまり、

```text
別の nextX nextY nextZ を賢く選べばよい
別の CRT representative を選べばよい
canonical orbit をさらに強化すればよい
```

という問題ではありません。

**terminal branch から away branch へ再帰する設計そのものが閉じました。**

## では何を組み立て直すのか

terminal packet は三つの row に完全分解されています。

```text
Row Y:
  7 | y

Row Z:
  7 | z

Row Sum:
  7 | y+z
```

より正確には、各 row が carrier quotient・unit sign・root-load 積を同時に保持しています。

ここで、元の方程式、

$$x^7+y^7=z^7$$

を mod $7$ に落とすと、

$$x+y\equiv z\pmod7$$

です。

この一次式と、奇数冪の置換対称性を row ごとに使うと、三枝の正体が変わって見えます。

## Row Y：自然数の左右交換で ramified branch へ移る

Row Y では、

$$7\mid y$$

なので、

$$x\equiv z\pmod7$$

です。したがって、

$$7\mid z-x$$

となります。

元の counterexample の左右を交換して、

$$y^7+x^7=z^7$$

と読み直します。

Lean の tuple では、

```lean
CounterexamplePack y x z
```

です。

この新 chart における gap は、

$$z-x$$

であり、これは $7$ の倍数です。

DkMath の quadratic route は、

```text
7 ∤ gap → away chart
7 | gap → ramified chart
```

という分岐です。

したがって Row Y は直接矛盾というより、

```text
terminal away-Y
  ↓ swap x y
ramified chart
```

へ合流します。

これは証明を逃がすのではありません。**同じ counterexample を、正しい chart へ置き直す操作**です。

最初の補題候補はかなり薄く書けます。

```lean
def CounterexamplePack.swapXY
    (source : CounterexamplePack x y z) :
    CounterexamplePack y x z := ...

theorem AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
    (hy : AwaySevenBaseTerminalRowYProfile terminal) :
    Nonempty (RamifiedCoordinateNormalForm y x z) := ...
```

## Row Sum：交換後の away chart が自壊する

Row Sum では、

$$y+z\equiv0\pmod7$$

です。

$y$ と $z$ はどちらも $7$-unit なので、ある非零 $t$ に対して、

$$y\equiv t,\qquad z\equiv-t\pmod7$$

です。

さらに $x+y\equiv z$ より、

$$x\equiv-2t\pmod7$$

となります。

再び左右を交換し、

$$y^7+x^7=z^7$$

という chart を考えます。

新しい endpoint 三因子は、

$$x,\qquad z,\qquad x+z$$

です。その mod $7$ residue は、

$$-2t,\qquad-t,\qquad-3t$$

なので、すべて非零です。

一方、新 gap は、

$$z-x\equiv(-t)-(-2t)=t\not\equiv0\pmod7$$

です。

したがって交換後の chart は away chart です。

ところが DkMath は、**すべての away chart について**、

$$7\mid (\text{left endpoint})(\text{right endpoint})(\text{sum endpoint})$$

を証明しています。

交換後なら、

$$7\mid xz(x+z)$$

でなければなりません。

しかし、

$$7\nmid x,\qquad7\nmid z,\qquad7\nmid x+z$$

です。

よって矛盾。

```text
Row Sum
  ↓ swap x y
away chart with no 7-bearing endpoint
  ↓
contradiction
```

これは TERM-009 の中で、**最も早く無条件排除できる枝**に見えます。

狙う theorem は次です。

```lean
theorem AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
    (hs : AwaySevenBaseTerminalRowSumProfile terminal) :
    False
```

証明材料はすでにほぼ揃っています。

## Row Z：自然数 chart では閉じないが、符号付き chart なら ramified

Row Z では、

$$7\mid z$$

なので、

$$x\equiv-y\pmod7$$

です。

自然数の左右交換だけでは、

```text
(x,y,z) → (y,x,z)
```

としても、右辺 $z$ が依然 $7$ を持つため、再び away-Z chart に戻ります。

ここだけが本当に非自明です。

しかし指数 $7$ は奇数なので、

$$z^7+(-y)^7=x^7$$

と書けます。

つまり符号付き chart、

```text
(X,Y,Z) = (z,-y,x)
```

では標準形、

$$X^7+Y^7=Z^7$$

になります。

この chart の gap は、

$$Z-Y=x-(-y)=x+y$$

です。

Row Z では $x+y\equiv z\equiv0\pmod7$ なので、

$$7\mid x+y$$

です。

したがって、

```text
terminal away-Z
  ↓ odd-power signed permutation
signed ramified chart
```

へ移せる可能性があります。

問題は、現在の `CounterexamplePack` が正の自然数専用であり、$-y$ を保持できない点です。

ここには次の薄い signed façade が必要です。

```lean
structure SignedFermatSevenChart (a b c : ℤ) : Prop where
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  primitive : IsCoprime a b
  equation : a ^ 7 + b ^ 7 = c ^ 7
```

そして、

```lean
def AwaySevenBaseTerminalRowZProfile.signedChart :
    SignedFermatSevenChart (z : ℤ) (-(y : ℤ)) (x : ℤ)
```

を作ります。

その後、現在の自然数版 quadratic extraction の代数核を整数版へ薄く一般化できれば、

```lean
theorem AwaySevenBaseTerminalRowZProfile.to_signed_ramified :
    Nonempty (SignedRamifiedCoordinateNormalForm ...)
```

へ進めます。

### ここが TERM-009 の判定点

signed transport が既存の `TraceOneInt (-2)` API の薄い wrapper で済むなら、Row Z も ramified branch へ吸収できます。

逆に、自然数 positivity に深く依存していて大規模な再形式化が必要なら、

```text
Row Y   → ramified
Row Sum → contradiction
Row Z   → 唯一残る直接算術 branch
```

として Row Z だけを従来の quotient/root-load/canonical orbit で攻めればよいです。

## TERM-003〜008 は無駄だったのか

無駄ではありません。

それらは、

```text
prime support
exact depth
finite CRT
original-coordinate recovery
integer winding
cellwise fixed systems
carry dependency
```

を完全に確定しました。

特に TERM-008 は、first-coordinate carry が新しい情報を持たないことを証明しました。

このため今は、

```text
さらに carry を増やせば矛盾が出る
```

という偽の道を捨てられます。

また Row Z が signed chart で解決できない場合、TERM-003〜008 の全 packet が、最後の一枝に集中投入できます。

## 推奨する組み立て直し

チェックポイント名を一つに保つなら、

```text
FLT7-TERM-009
  terminal Fermat chart resolution
```

とします。

内部目標：

```text
TERM-009-A
  CounterexamplePack.swapXY

TERM-009-B
  Row Y → swapped ramified chart

TERM-009-C
  Row Sum → swapped-away contradiction

TERM-009-D
  signed odd-power chart

TERM-009-E
  Row Z → signed ramified chart
  または Row Z を唯一の arithmetic obligation として分離
```

枝番号を避けるなら、一つの decision 型でもよいです。

```lean
inductive AwaySevenBaseTerminalChartResolution
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) : Type
  | rowY_ramified
      (packet : RamifiedCoordinateNormalForm y x z)
  | rowZ_signedRamified
      (packet : SignedRamifiedCoordinateNormalForm ...)
  | rowSum_impossible
      (eliminates : False)
```

## 重要な注意

Row Y と Row Z を ramified chart へ移すだけでは、まだ FLT7 contradiction ではありません。

現在の最終 summit route には `.ramified` branch が残っています。

したがって全体構造は、

```text
away terminal branch
  ├─ Row Sum → contradiction
  ├─ Row Y   → ramified branch
  └─ Row Z   → signed ramified branch
```

となり、その後、

```text
ramified branch の最終閉鎖
```

が必要です。

しかしこれは大きな前進です。

**away terminal を独自の巨大算術問題として抱えず、既存の ramified 世界へ正規化できる可能性が見えました。**

## 結論

はい、組み立て直しです。

ただし、

```text
descent の再設計
```

ではなく、

```text
Fermat 方程式の自然交換・符号付き交換による
terminal chart の再分類
```

です。

わっちの現在の推論では、

```text
Row Sum は直接落ちる
Row Y は自然 swap で ramified へ行く
Row Z は signed swap で ramified へ行く可能性が高い
```

です。

$$\boxed{\text{DESCENT-002 の敗北ではなく、terminal branch が別 chart に属することの発見}}$$
