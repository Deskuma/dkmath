# Step033 — proved no-direct-map frontier

2026-10-11。E=TraceOneInt(-1)、R=SevenCyclotomicDegreeSixInt.Ring。
ここで「map」は、存在／非存在の対象ごとに型を明示する。

| Claim | Mathematical status / checked owner | Precise boundary |
|---|---|---|
| direct unital E→+*R | **Impossible** / not_nonempty_eisenstein_to_seven_cyclotomic | q29 actual R residue map にcomposeすると E generator relationのno-rootに反する |
| direct unital R→+*E | **Impossible** / not_nonempty_seven_cyclotomic_to_eisenstein | q13 actual E residue map にcomposeすると完全なΦ7 no-rootに反する |
| separate E/R→+*ZMod43 | possible / existing actual residue RingHoms, new typed test | 同じcodomainでも source間mapは作らない |
| E norm values / R natural Tail product | proved / Steps012,023,032 | norm scalar equality はRingHom E→Rでもelement equalityでもない |
| embeddings into some larger common ring | **not ruled out** | 本 task の2 no-hom statementsのtargetではない。construction/injectivityは別 |
| ℤ-module maps / bilinear pairings / tensor-compositum bridge | **not ruled out**, not constructed | unital RingHom の generator relations 保存とは異なるcontract |
| nonunital morphisms / additive morphisms | **not covered** | proof は map_one を使う |
| signed-depth provider reconstruction / FLT7 descent | **not supplied** | next primitive packet / source equality を構成しない |

Step032 までの「direct mapを現在のsource契約から供給できない」という missing-information
findingを、**この二つの実 integral orders間の unital direct mapは存在しない**という theoremに
強めた。これを arbitrary coefficient extensions や全てのpossible richer bridgesの不可能性に
拡張しない。新 structural order theorem であるが classificationは Outcome B。

## Finite-field proof の論理

q29では actual ev29:R→+*ZMod29 がある。仮想 f:E→+*R とcomposeすると
h:E→+*ZMod29。Eのτ²−τ+1=0をmap_pow/sub/add/one/zeroで写すと
hτがZMod29のquadratic rootとなるが、全29 residuesでno-rootをdecide検証した。
このproofはfのinjectivityやsurjectivityを要求せず、どんなunital homも排除する。

q13ではactual ev13:E→+*ZMod13 がある。仮想 f:R→+*E とcomposeし、
ζの**7項完全関係**を写す。全13 residuesでΦ7にrootなし。
fζまたはev13(fζ)のnontrivialityは仮定しない。像1もΦ7(1)=7≠0なので排除される。
ζ⁷=1だけのtransportでは像1を排除できず、今回のrelationが必要。

両proofにFermat7Equation、positive primitive tuple、GTail q-support、budgetの仮定はない。
q29/q13 に架空のTail tupleを作らない。q13 Gap-only calibrationは別のnumeric契約。

## Discriminant−7 companion との型の区別

QuadraticBridge.cyclotomicSevenToTraceOne (z y:ℤ) : TraceOneInt(-2) は
explicit cubic coordinate pairであり、cyclotomicSeven z y=norm(coord)を証明する。
そのdiscriminantは−7。一方E=TraceOneInt(-1)のdiscriminantは−3。
このcoordinate functionはunital E↔R RingHomという型を持たない。
既存−7 norm companionの存在と、新しい−3 no-direct-map theoremは矛盾しない。
CyclotomicQRTraceOneBridgeのPrimeTraceOneCoordinatePacket.coordも
TraceOneInt(signedPrimeParameter p)をtargetにするconditional coordinate/norm API。
parameter/sourceを消してEへのintegral mapと解釈しない。

## 次に提案する algebraic input の必要契約

| Proposed input | Required exact proof/data | Existing potential consumer / missing link |
|---|---|---|
| common receiving ring C | ring type C、actual E→+*C/R→+*C、τ/ζ generator images、両defining relations、integrality、必要ならinjectivity | direct mapは今回排除；third targetは別設計。今回は構築しない |
| nontrivial common identity | 任意のimage pairより強い、source-linked element/scalar identityとその独立proof | Step032 NAT/norm iffへのglobal balanceが必要。sharedcodomainだけでは不足 |
| prime ideal transport | proved map、proper target prime、Ideal.map/comap、norm relation、contraction、kernel/nonzero、必要power equalityの正確なhypotheses | formal ideal imagesだけからdepth/contraction同値やsource element equalityを推定しない |
| FLT descent reconstruction | nextX/Y/Z、new CounterexamplePack、nextRoute、actual carrier_match | AwayDescentClosureProvider；no-hom theoremはこのfieldsを一つも生成しない |

tensor product/compositumは両sourceから第三ringへのmapsを受ける候補であり、E→Rを復活させる
道具ではない。receiving ringを得てもideal powersのexact informationや元Fermat equationは
自動で戻らない。signedRootDepth/carrierの同一性を別のproofなしに与えない。

STOP033。common ring、tensor、21st cyclotomic order、class/unit theory、signed packet、
new primitive descent、unconditional FLT7 conclusionは今回実装していない。
