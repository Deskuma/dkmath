# GTCORE-008 — FLT7 re-entry report

Date: 2026-09-10  
Status: situation and boundary triage complete; FLT7 source migration not started; deprecation deferred  
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`  
Source/build root: `lean/dk_math`  
Inspection commit: `e08b71c05`

この checkpoint は、`analysis-001.md` が指定する GTCORE-008
「FLT7 dependency graph と新しい GTail core の比較」を行う report である。
FLT7 の実装、global rename、旧 GN の削除、`@[deprecated]` の導入、FLT7 の数学的結論の
追加は行っていない。

## 1. Verification

次の direct target を実行した。

```bash
cd lean/dk_math
lake build DkMath.FLT.Seven DkMathTest.FLT.Seven.CheckAxioms
```

結果は次の通りである。

```text
Build completed successfully (8810 jobs).
```

`DkMathTest.FLT.Seven.CheckAxioms` は `#print axioms` を含む監査 target である。
成功は declaration の依存公理を無くしたことを意味しない。出力された
`propext`、`Classical.choice`、`Quot.sound` 等の既存依存は監査情報として扱い、
新しい GTail theorem の正当化や FLT7 の完成根拠にはしない。

GTCORE-007 の full cross-project replay と full `DkMath` build も直前の checkpoint で
成功しており、今回の direct target はその結果を FLT7 入口で再確認するものである。

## 2. FLT7 と GTail の現在位置

`DkMath.FLT.Seven` は多数の `DkMath.FLT.Seven.*` モジュールを集約する umbrella
module である。現行の full `DkMath` import graph には既に含まれているため、FLT7 は
GTCORE-007 の replay から除外されていたわけではない。ただし、FLT7 source 自身が
canonical GTail API を直接使っている状態ではない。

`DkMath/FLT/Seven` と `DkMathTest/FLT/Seven` の Lean source に対する今回の字面検索は
次の通りである。件数は declaration、docstring、test を含む字面件数であり、consumer
数や theorem dependency の件数ではない。

| Search pattern | Occurrences |
|---|---:|
| `DkMath.CosmicFormulaBinom.GN` | 3 |
| `GN 7` | 70 |
| `DkMath.CosmicFormula.GN` | 0 |
| `GTail` | 0 |
| `cosmic_id_csr` | 1 |

したがって現在の切り分けは次のようになる。

```text
canonical GTail core      : build/replay 済み
FLT7 import/build         : build 済み
FLT7 direct GTail usage   : まだ無い
FLT7 direct legacy GN use : 算術入口に限定して残る
FLT7 source migration     : 未着手
```

これは core 側が FLT7 を受け付けないという意味ではない。FLT7 がまだ旧 `GN` surface
を用いており、GTail への再入場橋をまだ選定・実装していないという意味である。

## 3. Legacy GN の直接使用領域

直接使用は、FLT7 全体に均一に広がっているのではなく、次の局所領域に集中している。

### 3.1 Counterexample routing

`DkMath/FLT/Seven/CounterexampleRouting.lean` は

```lean
def Body7 (g y : ℕ) : ℕ := g * GN 7 g y
```

を起点に、`cosmic_id_csr'`、正値性、gcd 分岐、7-adic valuation、factor split を
組み立てている。ここでの第一候補は、旧 `GN` の単純な名前置換ではなく、canonical
`DkMath.CosmicFormula.GN` と factor identity の対応を型付きの小さな bridge として
固定することである。

### 3.2 Primitive / 7-adic boundary

次のファイルは `GN 7` の局所算術を直接扱う。

- `PrimitiveCyclotomicDepth.lean`
- `AxisDivisibility.lean`
- `SevenAdicPowerSplit.lean`

ここでは、単に引数順序を変えるだけではなく、

- gap と endpoint の役割
- `GN 7 (a - b) b` の意味
- `padicValNat` と `7 ∣` / `49 ∣` の境界
- Nat subtraction と cast の証明形

が同時に現れる。従って bulk replacement の安全性は未確認である。

### 3.3 Quadratic / trace-norm boundary

次のファイルでは `GN 7` が TraceOne の norm や二次形式の residual と接続される。

- `QuadraticBridge.lean`
- `QuadraticResidualPacket.lean`
- `QuadraticConjugateCoprime.lean`

特に `QuadraticBridge.lean` は `DkMath.CosmicFormula.CosmicFormulaBinom` を直接
import する。ここは canonical GN の endpoint theorem を検討できる候補だが、
quadratic norm 側の意味を GTail の一般定理と同一視してはならない。

### 3.4 Terminal packet boundary

次の terminal packet も legacy GN endpoint を参照する。

- `AwaySecondCoordinateLoad.lean`
- `SevenBaseTerminalRamifiedSummit.lean`

ここでの GN は、単なる展開式ではなく、terminal routing と ramified chart のデータに
埋め込まれている。先に packet の意味境界を保った bridge を作る必要があり、一括置換の
対象ではない。

## 4. GTail へ再利用できそうな範囲

GTail の一般形から再利用候補となるのは、まず次の算術的境界である。

1. `GN 7` の展開・factor identity。
2. prime-degree boundary の coefficient / divisibility statement。
3. `r = 1` または prime exponent に対応する tail valuation の局所形。
4. cyclotomic shell へ渡す前の gap/end-point normalization。

これらは「FLT7 の既存 theorem が既に GTail theorem の corollary である」と確定した
ことを意味しない。現段階では dependency comparison の候補であり、実際の置換には
型、引数順序、Nat/Int cast、proof shape の focused experiment が必要である。

特に、FLT7 の `GN 7` identity が持つ次の downstream facts は、GTail の名前を付けた
ことだけでは得られない。

- `Nat.gcd` の branch classification
- exact `padicValNat` depth
- `7` / `49` の divisibility split
- quadratic TraceOne norm の factorization
- terminal packet の carrier / provenance compatibility

従って、現段階で安全な結論は「一般 core に接続できる算術入口がある」であり、
「FLT7 の GN 固有理論を削除できる」ではない。

## 5. GTail では置換できない未解決境界

FLT7 の主要な未解決点は、GTail API の不足ではなく、局所データを新しい整数
counterexample または厳密降下へ戻す reconstruction である。

既存 FLT7 status が列挙する open obligations は次の通りである。

1. finite/global simultaneous scale gluing
2. canonical-model compatibility across prime-power cells
3. lifted signed reconstruction from local residue data
4. terminal arithmetic exclusion
5. unconditional away-depth descent closure
6. recursive closure
7. final FLT7 contradiction

既存の `AwayDescentReconstructionSeed` は
`AwayDescentClosureProvider` と同値な契約として整理されているが、その seed/provider
自体の inhabitation は得られていない。terminal exponent one では seed/provider が
存在しないことを示す結果もあり、これは元の `CounterexamplePack` の否定や FLT7 の
証明ではなく、その descent branch が閉じないことを示す。

さらに U1.5/U1.6 の既存境界では、次が確認されている。

- coordinate operations から additive Fermat identity は得られない。
- concrete cyclotomic carrier から `ℤ` への unital ring homomorphism は得られない。
- `root` と `ζ * root` の phase ambiguity により、現在の chart は canonical でない。
- internal depth-four carrier と outer depth-five carrier の `4 < 5` はあるが、
  それを実際の `AwayValuationTransferPacket` に再構成する obligation は未充足である。
- real-cubic norm について、一般に `Norm(XR) - Norm(XL)` は `Norm(XR - XL)` ではない。

従って、これらを GTail の一般化または旧 GN の deprecated 化で解決できるとは扱わない。

## 6. Re-entry の判定

### 判定

GTCORE-008 の「状況把握と切り分け」は完了とする。FLT7 への再入場は可能だが、
次の意味に限定する。

- FLT7 の legacy GN 算術入口を dependency slice として調べる。
- generic GTail theorem と一致する最小 bridge 候補を一つずつ検証する。
- bridge の focused build と既存 theorem の意味保存を確認する。
- その後、局所的な source migration の可否を判断する。

次の意味では、まだ再入場しない。

- FLT7 全体の global rename
- `GN_eq_sum` / `cosmic_id_csr'` の一括置換
- FLT7 の cyclotomic / ramified / quadratic machinery の一括削除
- `@[deprecated]` による warning migration
- reconstruction seed の仮定による descent closure
- finite CRT、norm、depth inequality からの FLT7 結論

## 7. 次の安全な作業単位

次段階では、FLT7 全体を移行するのではなく、次の順序で一つの dependency slice を
扱うのが妥当である。

1. `CounterexampleRouting` の `GN 7` と `cosmic_id_csr'` の最小 bridge を抽出する。
2. canonical `DkMath.CosmicFormula.GN` の d-first signature と、旧 wrapper の
   positional/implicit `R` の差を明示する。
3. `PrimitiveCyclotomicDepth` と `AxisDivisibility` で、同じ数学的意味を保った
   focused replacement が可能か検証する。
4. quadratic/ramified/terminal packet は別 slice として保留する。
5. 各 slice の検証前に global rename や `@[deprecated]` を開始しない。

この作業単位は、GTCORE-006/007 の compatibility 方針を保持し、FLT7 の未解決数学を
API migration の成功と混同しないためのものである。

## 8. Not done

- FLT7 source の変更
- canonical GTail の新 theorem 実装
- legacy GN の global rename
- legacy wrapper の削除
- `@[deprecated]` の追加
- `AwayDescentReconstructionSeed` / `AwayDescentClosureProvider` の inhabitation
- lifted reconstruction、recursive descent、terminal exclusion、FLT7 theorem
