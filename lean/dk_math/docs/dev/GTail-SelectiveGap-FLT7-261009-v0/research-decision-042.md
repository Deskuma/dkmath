# Step042 research decision — no new proof target selected

2026-10-11。Outcome B: source-backed research audit / STOP042。
[source inventory](source-inventory-042.md) の actual signatures と branch ledger に基づく。

**判断: Step043 の実装対象を今回は選ばず停止を推奨する。**
Candidate I の提示された extraction は既に証明済み。Candidate II は新 primitive triple の
具体的代数写像がなく、Candidate III は original bounds とその後の row obstruction の
独立導出がない。三候補から恣意的に一つを「証明可能」と選ぶ根拠は現時点で得られなかった。
これは instruction-042 §4/§5 の「plausible independent route がなければ stopping」の分岐。
新たな FLT7 不可能性定理ではない。

## Proof direction reset

Step040 `full_quadratic_defect_zero_certificate` の結論は hEq であり False ではない。
CounterexamplePack の hEq から Δ=0 は直接従う。そこから support / size を得て再び hEq を
証明するだけでは矛盾が生じない。次の進展には、source から導かれる二つの非両立な帰結、
または実際の indexed primitive counterexample を well-founded global measure の下で
遷移させる構成が必要。終端分岐を処理しない away 内部の depth drop はその代用にならない。

## Candidate I — terminal Row-Z signed arithmetic closure

(a) Exact owner/input は `SevenBaseTerminalFermatChartResolution` の
`AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation`。
implicit `{x y z : ℕ} {source : CounterexamplePack x y z} {r : AwayCubicRoutingPacket x y z}
{p : AwaySevenPivotDepthPacket r} {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}`、
explicit `(hz : AwaySevenBaseTerminalRowZProfile terminal)`。
しかし `SevenBaseTerminalRowZSignedResidualCore:211` が Nonempty を証明済み、223行に inhabitant、
233行に signedRamified がある。I を「new extraction proof」として採用しない。

(b) Ring は discriminant−7 の TraceOneInt(-2)。target は
`cyclotomicSevenToTraceOne (x:ℤ) (-(y:ℤ)) = sevenAxis * root^7`。
Step034 の E=TraceOneInt(-1) や C の API を cast することはない。

(c) Existing arithmetic technique は実装まで追跡した:
positive alternating factor の exact split → signed sevenAxis peel → terminal residual core、
norm=b^7 → signed cubic-coordinate coprimality → gcd(core,conj core) isUnit →
Euclidean-domain coprime power extraction → units ±1 の odd seventh-power absorption。
ただの「hEq から extraction」という循環的仮定ではなく、必要な integrality/unit 条件を全て
actual owners が証明している。さらに Y/Z の common PrimitiveRamifiedSummitPacket も構成済み。

(d) 現在 missing なのは extraction の premise ではなく、ramified summit からの
source-compatible terminal contradiction または primitive chart reconstruction。
Row-Z packet の nonexistence 自体は今回証明しない。signed root の存在も仮定で補わない。

(e) New arithmetic technique の候補として元の source row を保つ invariant extractor を考えられるが、
現在の loaded cyclotomic equation は additive integer seventh-power identity を出さない。
visible signed roots を直接 chart に使う案は exact depth5 により既に否定。
ideal と root^7 だけで全 root coordinates を復号する decoder も既に否定されている。
具体的な invariant extractor と加法式の導出を提示できていない。

(f) 「primitive signed cubic coordinates が coprime」「terminal residual norm=b^7」「core=seventh power」
を最初の local lemma とする案は全て既証明なので棄却。
将来 extractor X,Y,Z を明示できたとき、最初の falsifiable lemma はその具体式について
`X^7+Y^7=Z^7` を loaded source から導くこと。現在はその式そのものが未提示であり、
架空の Lean signature を作らない。

(g) extraction success は既に signed normal form / summit を与えるが False は与えない。
terminal False または全分岐を繋ぐ indexed descent が別途必要。
(h) 現行 I は TERM-010 と重複。後続 gate は U1.5/U1.6 boundary に残る。
(i) extraction を再検証するなら最小 TERM-010 target でよいが、新 implementation の価値はない。
後続 FUSION route は real-cubic/cyclotomic PID を含む重い closure。新 cost は未測定。
不正な direct chart / universal coordinate decoder を目標にすると Outcome C/D となる。

## Candidate II — lifted-away primitive reconstruction

(a) Existing owner は `SevenBaseTerminalDescentProvider:20`。
actual target は `Nonempty (AwayDescentReconstructionSeed r.cubic.transfer)`、
input は real `{r : AwayCubicRoutingPacket x y z}`、explicit `(p : AwaySevenPivotDepthPacket r)`、
**`1 < p.exponent`**。exponent=1 を statement から除外する。
`SevenBaseTerminalDescentSeedExclusion:16` は seed→2≤exponent の必要条件のみ。
逆 implication はない。

(b) Natural target triple の normal.root は TraceOneInt(-2)。seed の fields は
nextX/Y/Z、nextNormal:AwayCoordinateNormalForm nextX nextY nextZ、
target_source:AwayExceptionalCarrierSource nextY nextZ (Int.natAbs old.root.snd)。
new normal に positivity、coprimality、Fermat equation、away guard、coordinate seventh-power
identity が含まれる。target_source は newY/newZ/newY+newZ のどれかが exact carrier に等しいこと。

(c) Existing seed↔provider、seed.toClosureProvider、strict carrier depth drop は完成済み。
lifted branch の local unit orbit / rootFst unit / rootSnd seventh-power zero は完成済み。
`SevenBaseTerminalLiftedReconstruction` は名前に Lifted を含むが、その型は **terminal routing** に
indexed。`SevenBaseTerminalExclusion` の False も terminal receiver の bounds/mismatch を入力する。
これらによる exponent≥2 の universal exclusion は存在すると確認できなかった。

(d) Missing premise は actual next primitive triple / nextNormal / target_source の構成。
「Nonempty seed」を別 field/Prop に格納するだけでは証明にならない。
2≤exponent は valuation-compatible であるだけで、primitive additive equation を供給しない。

(e) 必要な algebraic triple map は現在見つかっていない。
既存 gcd routing から factor 根を取る手法は multiplicative ledger までであり、
それを next Fermat summands にするときの additive seventh-power identity がない。
元の |root.snd| を new carrier に宣言するだけでは map にならない。

(f) 将来 map F_X,F_Y,F_Z を提示する場合、最初の falsifiable lemma は
その三つの明示的整数/自然式から `F_X^7+F_Y^7=F_Z^7` と positivity/coprimality の少なくとも
主要 guard を source equation から導くこと。exact exceptional source identity も続いて必要。
現在 F_X/Y/Z は未提示なので「第一 lemma を実装できる」という判定はしない。

(g) source-match ができれば既存 seed.toClosureProvider で新 CounterexamplePack と away depth drop
が得られる。ただし new route を同じ state space に戻す遷移、terminal exponent1 exclusion、
ramified branch の処理、global natural measure の減少が揃わなければ FLT7 contradiction ではない。
(h) 既存 theorem は terminal seed を否定し、lifted seed を保証しない。新 triple の欠落は既存 routing
同値によって解消しない。
(i) 高難度。seed owner は terminal CRT/carry imports を推移的に含むので lightweight と断定しない。
将来検証は map owner と seed consumer の focused targets、terminal negation の direct regression。
非 primitive / nonpositive / source carrier mismatch / additive identity failure なら Outcome C。

## Candidate III — original-integer CRT bound and row contradiction

(a) Exact owner は `SevenBaseTerminalLiftedReconstruction:378,396` の
`originalReconstructionDefect` / `modulus_dvd_originalReconstructionDefect`。
implicit source,r,p,terminal routing,family,candidate と explicit signed representative が input。
`integerWeightedDefect` に置き換えない。

(b) original residuals は ℤ の四座標、M=family.combinedModulus:ℕ。
original=(old root.fst,old root.snd,y,z)、scaled model=(model.u*s³,model.v*s³,model.y*s⁷,model.z*s⁷)。
(c) original/centered residual の M-divisibility と各 winding parameterization は proved。
fixedFirstResidual_decomposition は universal/endpoint/root residual の従属式。
(d) missing independent input は四つの actual `|original residual_i|<(M:ℤ)`、または genuinely new
原座標拘束。centered individual scale/model/weighted の半幅 bounds はこの入力ではない。

(e) 新技法として archimedean estimate を用いるなら、実際の original root/endpoints と s³/s⁷ を
同じ normalization で比較する explicit inequality が必要。CRT だけでは lifts が一意な整数に
ならず、model/scale の積は centered interval を大きく超え得る。
Row resolved M-factorization から実際にどう estimate を得るかは未導出。

(f) 将来の最初の falsifiable lemma は、正確な signed candidate と row を固定した上で
一つの **original** residual の strict bound を source から導くこと。
「M∣residual と |residual|<M なら zero」は既証明で新 lemma に数えない。
今回その independent inequality は見つかっていない。

(g) 四 bounds が通れば original=model.weightedScale scale を得る。
既存 receiver は centered weighted=model.weightedScale scale を使うため、
original=weighted bridge または **original equality に対する新 row-specific mismatch** がさらに必要。
Row-Sum は既に False、Row-Y は ramified、Row-Z は signed ramified に達している。
同じ original coordinates を再現するだけでは surviving Y/Z を排除しない。
(h) 既存 strictBounds/rowMismatch は conditional fields であり inhabitants ではない。
九つの dependent residual をもう一度証明しても magnitude や row mismatch は出ない。
(i) 高難度。必要 imports は既存 terminal CRT owner 群で足りる可能性があるが、
将来の新 bound technique による cost は未測定。focused exact residual owner と conditional
receiver regression を用い、original/centered 混同なら Outcome C。

## Ranking and stop gate

| Candidate | Assessment | Later proof priority |
|---|---|---|
| I: supplied Row-Z extractor | **Already proved**。new target に選ばない | 後続 global ramified obstruction に具体的 invariant が見つかれば再評価 |
| II: lifted seed | 真の未解決 reconstruction target。explicit triple map が欠落 | 未解決二候補の中では1位、ただし implementation-ready ではない |
| III: original CRT bound | independent bound と row contradiction の二段階が欠落 | 2位、source-derived estimate の具体式が出るまで採用しない |

Step043 theorem-sized target の選択数は **0**。bounded audit の許容 stopping 分岐を選んだ。
単なる conditional field の再包装、already-proved extraction、impossible terminal seed、
full support+size→hEq は採用しない。
次の separately scoped instruction が必要なら、まず explicit new arithmetic map / inequality / invariant
を提示して source 非循環性を評価できる内容にする。Step042 から自動実装しない。
