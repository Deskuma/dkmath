# Step032 — exact reconstruction frontier

2026-10-11。Source-only audit of old packets；新規 import/inhabit/edit は行わない。
旧 carrier からの既存 transitive dependencies は追加せず維持する。

## 実際の away closure provider

DescentClosureAudit の exact fields：

```lean
structure AwayDescentClosureProvider
    (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type where
  nextX : ℕ
  nextY : ℕ
  nextZ : ℕ
  nextPack : CounterexamplePack nextX nextY nextZ
  nextRoute : AwayValuationTransferPacket nextX nextY nextZ
  carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd
```

away_depth_descent_of_closureProvider p c はこの carrier_match を使って
`padicValNat 7 c.nextRoute.carrier < padicValNat 7 p.carrier` を得る。
nextPack は元 equation と positive primitive source data を要求する。
current smaller g、q43 ideal factor、even scalar exponent は nextX/Y/Z、nextPack、nextRoute、
carrier_match を構成しない。q43 depth は、この theorem が比較する7-depthとも異なる。
MissingClosureProviderStatement は reconstructionObligation **という命題を保存**する。
それを inhabit する proof でも reconstruction 不可能性の proof でもない。

## 実際の ramified signed-root packet

RamifiedSignedRootDepthPacket の全 field obligations：

| Field | Exact requirement |
|---|---|
| balanced | RamifiedRealCubicBalancedAxisSplitPacket |
| signedLeftRoot / signedRightRoot | ℤ values |
| signedLeftRoot_eq / signedRightRoot_eq | balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.leftRoot/rightRoot と一致 |
| signedRoots_isCoprime | IsCoprime signedLeftRoot signedRightRoot |
| gapRoot / quotientRoot | ℤ values |
| signedGap_eq | signedRightRoot−signedLeftRoot = 7^4*gapRoot |
| signedQuotient_eq | signedSeventhQuotient signedRightRoot signedLeftRoot = 7*quotientRoot |
| gapRoot_not_seven_dvd / quotientRoot_not_seven_dvd | 7∤両 roots |
| normalizedEquation | gapRoot*quotientRoot = u*(u+v)*innerSndRoot^7 |

ここで u,v は同じ balanced packet の
`axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst/snd`、
innerSndRoot も同じ normPacket の field。単なる existential roots と一致させていない。
Steps018–032 の bare natural c,g と q≠7 Tail residue はこの whole balanced packet、
source-linked signed roots、7-primary normalized equation を構成しない。

SevenRamifiedFusionOrientedCarrierValuationOwnership の
`orientedKernelPower_dvd_span_carrier (s : PrimeSupport family p)` は
`s.orientedKernelPower ∣ Ideal.span {p.signedDepth.cyclotomicDegreeSixCarrier}`。
quotientExponent を使う後段もその signed source と real-load family を要求する。
今回 F_i(1858,1165) の selected ideal depth と packet carrier の depth を同一視しない。
shared finite-field codomain、degree-six の名前、同じ整数付値だけでは carrier equality がない。

## 現在証明されている maps/equalities と追加義務

| Current premise | Typed conclusion / owner | Countermodel sensitivity | Lost data / extra proof needed |
|---|---|---|---|
| hfocus | NAT shell, GTailBridge | new witness でも true | shell は hEq を含まない。exact interior balance は別 |
| hfocus+hEq | NAT gT=7ab(a+b)Q²；新 iff は reverse も証明 | new witness で false | q-local budget からこれを得る global equality proof が欠ける |
| hfocus+hEq | INT gT=7ab(a+b)norm(α²), GTailNormReadoutAudit / new iff | new witness で false | cast transport は exact equalityを保持するが局所条件から作らない |
| any a,b | E normα=Q,normα²=Q², GTailSevenNormReadout | witness でも true | <u>norm は integral coordinates / orientation / unit を捨てる</u> |
| t quadratic root | E→ZMod43 evaluation / P_t kernel | t37 で true | <u>finite-field reduction は integer lift と integral relations の逆方向を捨てる</u> |
| any c,g | ∏F_i=(T:R), GTailCyclotomicTailFactorProduct | witness でも true | product から個別 element と E norm element の同一性は出ない |
| seventh root r | R→ZMod43 evaluations / sixRootKernel | r11 で true | <u>共有 codomain では source ring E/R の型の違いを解消できない</u> |
| source units/support | E square address と R K²/K³/K⁴ receivers | witness は E square/R exact second depth | local ideal membership から global scalar balance は出ない |
| nextPack,nextRoute,carrier_match | actual away depth drop, DescentClosureAudit | witness はこの premise を持たない | 新 primitive counterexample の source reconstruction が必要 |

二つの finite-field roots の間に canonical formula は主張しない。
情報不足の ledger は、将来どんな bridge も作れないという不可能性 theorem ではない。
現在の source contracts が missing provider を inhabit していない、という bounded finding。

## 今後の提案を評価する契約

次の arithmetic proposal は、source を明示された local contract、target を exact NAT balance
とし、new noncircular global premise とその証明をまず特定すべき。既存 consumer は新 NAT iff。
同じ結論を premise に入れても新 arithmetic input にはならない。
provider reconstruction proposal は source を actual AwayValuationTransferPacket、target を
AwayDescentClosureProvider とし、上表の全 next fields と carrier_match を埋める必要がある。

仮に E→R algebraic proposal を検討するなら source E、target R、1↦1 と quadratic generator
u↦e∈R の具体値、e²−e+1=0 の preserved relation、ℤ scalar compatibility、integrality、
ideal image/conjugation とどの signed carrier equality に使うかを別々に示す必要がある。
現 source にその e や消費用 transport theorem はない。candidate map は今回提示・実装していない。
finite-field root を e の integral lift と宣言するだけでは満たさない。

STOP032。次の construction 選択は、この exact missing equality/provider fields と
本当に新しい algebraic input を比較した後に行う。
