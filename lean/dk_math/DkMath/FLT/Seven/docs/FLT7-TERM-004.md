# FLT7-TERM-004

## 総合判定

**全面採用。Outcome C。**

```text
TERM-003-A〜D              完成
TERM-003-E の入力 packet   完成
row-specific arithmetic    未完成
descent provider            未構築
```

報告文では commit・push 前でしたが、PR 確認時点ではその後の変更が反映されており、現在の head は次です。

```text
a5804a432c1390ff131bde8aa4512e02ef712537
```

PR #65 は open / draft / mergeable、TERM-002 から 3 commits 進み、Lean CI run 336 も **success** です。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5077372765)

## TERM-003-A：core coherence

```lean
structure AwaySevenBaseTerminalCoherentRoutingPacket
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) where
  routing : AwaySevenBaseTerminalRoutingPacket (source := source) p
  core_eq : routing.core = terminal.core
```

constructor は `routing.core := terminal.core` と直接構成し、`core_eq := rfl` で閉じています。

これは単なる同型の core ではなく、row profile と CRT routing が**同じ terminal quotient core**を参照することを保証します。

## TERM-003-B：actual coherence

orbit source の各 constructor が、

```lean
actual.u = p.toPrimePowerSolution.u
actual.v = p.toPrimePowerSolution.v
actual.y = p.toPrimePowerSolution.y
actual.z = p.toPrimePowerSolution.z
```

を直接保持するようになりました。

column の dependent transport は専用補題で処理され、その後、

```lean
theorem actual_eq_original :
    projection.actual =
      depth.toPrimePowerSolution
```

を solution extensionality で復元しています。

この設計は強いです。後から「chosen actual はたぶん original」と推測するのではなく、選択した瞬間に証明を保存しています。

## TERM-003-C：global actual-coordinate CRT

中心定理は予定どおりです。

```lean
candidate.weighted =
  awaySevenBaseTerminalOriginalCoordinates
    r family.combinedModulus
```

証明は四座標それぞれについて、

```text
global weighted
  ↓ CRT reduction
local actual
  ↓ actual_eq_original
original integral coordinate mod q^e
  ↓ CRT injectivity
original integral coordinate mod M
```

と進みます。

これにより、

```text
global weighted candidate
```

は抽象的な residue tuple ではなく、

```text
(root.fst, root.snd, y, z) mod M
```

そのものになりました。

## TERM-003-D：original-coordinate winding

新しい defect は、独立に centered 化された weighted tuple との差ではなく、元の整数座標との差です。

```text
root.fst - model.u * scale^3
root.snd - model.v * scale^3
y        - model.y * scale^7
z        - model.z * scale^7
```

これら四成分がすべて $M$ の倍数であることが証明されています。

そして、

```lean
structure AwaySevenBaseTerminalOriginalReconstructionWindingPacket where
  ku kv ky kz : ℤ

  rootFst_eq :
    root.fst = model.u * scale^3 + M * ku

  rootSnd_eq :
    root.snd = model.v * scale^3 + M * kv

  y_eq :
    y = model.y * scale^7 + M * ky

  z_eq :
    z = model.z * scale^7 + M * kz
```

まで到達しました。

これは TERM-003 の最大成果です。modular reconstruction が、元の整数座標を主語とする exact winding equation へ変わりました。

## TERM-003-E：入力 packet

```lean
AwaySevenBaseTerminalRowResolvedWindingPacket
```

は winding に加えて、row ごとの full modulus 分解を保持します。

```text
Y:
  M = carrierUnit * z * (y + z)

Z:
  M = y * carrierUnit * (y + z)

Sum:
  M = y * z * carrierUnit
```

ここでは winding の消滅、row contradiction、descent provider の存在を一切主張していません。停止位置は正確です。

---

# 新しく見えた突破口

## 1. global model は「普遍座標方程式」を持てる

これまで、

```text
local prime ごとに row / column が異なる
  ↓
global model は一つの polynomial system を持たない
```

と見ていました。

これは **cell-specific system** については正しいです。

しかし TERM-003-C により、global weighted tuple が元の座標と一致したため、その上位にある二つの普遍方程式を global model へ戻せます。

狙うべき定理は、`ZMod M` 上の次です。

```lean
seventhPowerFst model.u model.v =
  cyclotomicSevenFst model.z model.y

seventhPowerSnd model.u model.v =
  cyclotomicSevenSnd model.z model.y
```

これは次の経路で証明できる見込みです。

```text
original coordinates satisfy both equations
        ↓ TERM-003-C
weighted global coordinates satisfy both equations
        ↓ weighted homogeneity
scale^21 * modelEquation = 0
        ↓ combinedScale is a unit
modelEquation = 0
```

root 座標は weight $3$、endpoint 座標は weight $7$ なので、

```text
root-side degree 7      → 3 × 7 = 21
endpoint-side degree 3  → 7 × 3 = 21
```

と両辺が同じ `scale^21` を持ちます。

これは推論段階ですが、現行 theorem surface が必要材料を供給しています。TERM-003-C の exact equality が、この cancellation を初めて可能にしました。

### 推奨 packet

```lean
structure AwaySevenBaseTerminalGlobalCoordinateEquationPacket
    (candidate : ...) : Type where
  fstEquation :
    seventhPowerFstZMod
        candidate.model.globalModel.u
        candidate.model.globalModel.v =
      cyclotomicSevenFstZMod
        candidate.model.globalModel.z
        candidate.model.globalModel.y

  sndEquation :
    seventhPowerSndZMod
        candidate.model.globalModel.u
        candidate.model.globalModel.v =
      cyclotomicSevenSndZMod
        candidate.model.globalModel.z
        candidate.model.globalModel.y
```

これにより「global model は四つの無関係な residue にすぎない」という壁を一段越えます。

ただし、まだ特定の `.sevenV / .leftCubic / .rightCubic` branch を選ぶものではありません。

## 2. equation winding を抽出できる

上の二式を整数代表へ戻せば、

```text
M ∣ seventhPowerFst(U,V) - cyclotomicSevenFst(Z,Y)

M ∣ seventhPowerSnd(U,V) - cyclotomicSevenSnd(Z,Y)
```

が得られます。

したがって、新たに二つの carry を抽出できます。

```lean
fstCarry sndCarry : ℤ
```

```text
seventhPowerFst(U,V) - cyclotomicSevenFst(Z,Y)
  = M * fstCarry

seventhPowerSnd(U,V) - cyclotomicSevenSnd(Z,Y)
  = M * sndCarry
```

この二つを既存の `ku, kv, ky, kz` と組み合わせれば、元の exact equation を展開して、

```text
coordinate winding
+
equation carry
+
row modulus factorization
```

という、本当の row-specific arithmetic receiver が得られます。

以前の `DefectStrictBounds` より、こちらの方が構造に沿っています。

## 3. 3×3 cell ごとの CRT が本命

さらに強い攻め筋があります。

現在すでに、full load の各素数には一意な terminal cell coordinate が存在します。

```lean
∃! coordinate : AwaySevenBaseTerminalCellCoordinate,
  AwaySevenBaseTerminalPrimeCellCoordinate packet coordinate q
```

しかも、その prime は選ばれた cell value を割り、full load の各 prime が九セルのいずれか一つへ一意に入ります。

さらに各 prime は、その cell に対応する original routing cell の**完全な prime-power depth**へ持ち上げられています。

したがって prime support を九つの fiber に分割できます。

```text
cellPrimeSupport coordinate
cellCombinedModulus coordinate
cellCombinedScale coordinate
cellGlobalModel coordinate
```

full CRT では row / column が混在しました。

しかし一つの cell fiber 内では、

```text
endpoint row  固定
root column   固定
```

です。

ゆえに cellwise CRT model は、四座標だけでなく、

```text
endpoint equation
root equation
first-coordinate equation
nondegeneracy
```

を一つの固定 system として保持できます。

### 最重要の中間定理

```lean
cellCombinedModulus coordinate =
  awaySevenBaseTerminalRoutingCell routing coordinate
```

これを証明できれば、現在の「全 load を一度に持ち上げる」方式から、

```text
3 × 3 の各魔核を完全に復元する
```

方式へ移れます。

carrier/vPart cell と original routing cell を比較するときだけ、terminal で除去した visible factor $7$ を明示的に処理する必要があります。非 $7$ prime の depth はすでに完全なので、材料は揃っています。

## 4. contradiction / descent の分岐が具体化する

cellwise packet が完成すると、次の二択になります。

```text
九つの cell equation が一つの整数 model に整合する
  ↓
小さい FLT7 整数解を抽出
  ↓
positive / primitive normalization
  ↓
AwayValuationTransferPacket
  ↓
carrier_match
  ↓
AwayDescentClosureProvider
```

または、

```text
cellwise equation carries が同時には整合しない
  ↓
terminal contradiction
```

現在不足しているのは「数値を小さくする魔法」ではなく、**full CRT を九つの固定 system へ再分解する theorem**です。

---

# 推奨 checkpoint

枝番を増やさず、次は一つ進めるのがよいです。

```text
FLT7-TERM-004
  universal global coordinate equations
  +
  exact integer equation carries
```

その後は、

```text
FLT7-TERM-005
  prime support の 3×3 cell partition
  +
  exact cell modulus reconstruction
```

```text
FLT7-TERM-006
  cellwise CRT solution packet
  +
  row-resolved carry decision
  → contradiction または AwayDescentClosureProvider
```

と進むのが最短に見えます。

## 最終結論

TERM-003 は、単なる「不足の型化」ではありません。

```text
local actual
  → global original coordinates
  → exact integer winding
  → row modulus factorization
```

まで本当に到達しました。

そして次の魔核は、

```text
full CRT model を
普遍座標方程式へ接続し、
その後 3×3 の固定 cell system へ再分解する
```

ことです。

この経路なら、`CounterexamplePack` を仮定で生やさず、現在ある prime address・complete depth・CRT・row factorization をすべて活用できます。

添付資料でも、まず定義・局所恒等式・保存構造を固定し、強い一般主張を後段へ回す実装規律が採られています。今回の A–D 完成と E 入力での停止は、その DkMath 方針とも整合しています。
