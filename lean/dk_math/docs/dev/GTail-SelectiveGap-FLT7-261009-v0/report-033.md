# Step033 — no direct unital Eisenstein/cyclotomic RingHom

2026-10-11。**COMPLETE / Outcome B**。Step033 で停止。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD `343827dc291fed225dd2f3cd36faa56794d49448`。

実際の E=TraceOneInt(-1) と R=SevenCyclotomicDegreeSixInt.Ring の間で、
**E→+*R も R→+*E も存在しない**ことを Lean で証明した。
q29 では actual R residue evaluation と Eisenstein polynomial の no-root、
q13 では actual E residue evaluation と complete Φ7 polynomial の no-root を使う。
これは二つの orders間の直接 unital map の構造的な非存在定理であり、
FLT7 arithmetic obstruction/descent や richer bridges の不可能性ではない。

## Source contracts と gate の実行順

[Source inventory](source-inventory-033.md) は実source/target types、unital premise、
actual τ/ζ relations、既存 residue RingHoms、Mathlib comp/map/cast APIs を比較する。
review032 はstatic inspection、今回のfocused buildsとは区別。
新 production direct import は Step032 一つ。root hom / relation owners はその既存
transitive closure にあるため、extra targeted import は不要だった。
旧 QuadraticBridge/CyclotomicQRTraceOneBridge は型診断のみ、新import/変更なし。

1. source01で4つの有限体 facts と **E→R非存在だけ**を先にbuild成功。
2. source01 の唯一の warning は proposition-proof 内の `letI` に対するstyle警告。
   global optionsを変更せず `let : Fact (Nat.Prime 29)` に改め、source02でwarning0。
3. **Gate2成功後に** reverse R→E theoremを追加。source03で両方向成功、warning0。
4. test04で全24 examples、7 library #checks と6 public axiom printoutsが成功。
5. Step032/031 selected regressions05/06が成功。

失敗したproof/elaboration/buildはない。中間01のstyle警告のみを修正した。
finite decide に resource-limit override/native_decide を使用していない。

## 実際の proof chain

Eのactual τはTraceOneQuadratic.tau(-1)。private relationは
`rw [pow_two, traceOne_tau_sq]` の後actual coordinates/ofIntを正規化し
τ²−τ+1=0を証明する。新 generator relationを仮定していない。

仮想 f:E→+*R に対して
`ev29 := evalCyclotomicFromSeventhRoot (7:ZMod29) hr0 hr7 hr1`、
`h := ev29.comp f` を構成。congrArg h τ_relation と
map_pow/map_sub/map_add/map_one/map_zero で hτ の finite quadratic relationを得る。
全29 residuesで root不存在なので矛盾。injectivity/surjectivityは仮定しない。

仮想 f:R→+*E に対して
`ev13 := eisensteinResidueRingHom (4:ZMod13) ht`、`h := ev13.comp f`。
congrArg h zeta_geom_sum を map_add/map_pow/map_one/map_zero で正規化し、
1+hζ+(hζ)²+…+(hζ)⁶=0。全13 residuesの no-root と矛盾。
fζやhζがnontrivialなことを要求しない。像1もΦ7(1)=7≠0なので排除する。
ζ⁷=1だけでは1を排除できない点を別numeric exampleで確認。

両proofに Fermat7Equation、hfocus、positivity、primitive、native Tail、q-local budget、
old signed packet/descent provider の仮定はない。unital map_one が不可欠なので
additive/module/nonunital mapsへの一般化は主張しない。

## 全公開6定理の正確な署名

namespace DkMath.FLT.Seven。
open TraceOneQuadratic / Lib.NumberTheory / SevenCyclotomicDegreeSixInt。

```lean
theorem seven_root_zmod29 : (7 : ZMod 29) ≠ 0 ∧ (7 : ZMod 29) ^ 7 = 1 ∧
    (7 : ZMod 29) ≠ 1
```

```lean
theorem no_eisenstein_root_zmod29 (x : ZMod 29) : x ^ 2 - x + 1 ≠ 0
```

```lean
theorem eisenstein_root_zmod13 : (4 : ZMod 13) ^ 2 - 4 + 1 = 0
```

```lean
theorem no_seven_geom_root_zmod13 (x : ZMod 13) :
    1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 ≠ 0
```

```lean
theorem not_nonempty_eisenstein_to_seven_cyclotomic :
    ¬ Nonempty (TraceOneInt (-1) →+* SevenCyclotomicDegreeSixInt.Ring)
```

```lean
theorem not_nonempty_seven_cyclotomic_to_eisenstein :
    ¬ Nonempty (SevenCyclotomicDegreeSixInt.Ring →+* TraceOneInt (-1))
```

## 全24 examples と finite numeric evidence

| Checked object | Actual result |
|---|---|
| prime29 | Fact (Nat.Prime29) by decide |
| r7 in ZMod29 | r⁷=1,r≠1,r≠0 |
| ZMod29 quadratic | ∀x,x²−x+1≠0 |
| all nontrivial seventh roots in ZMod29 | exactly 7,16,20,23,24,25, universal iff by decide |
| t4 in ZMod13 | t²−t+1=0 |
| all Eisenstein roots in ZMod13 | exactly4,10, universal iff by decide |
| ZMod13 seventh cyclotomic | ∀x,1+x+x²+x³+x⁴+x⁵+x⁶≠0 |
| image1 contrast | 1⁷=1 but Φ7(1)≠0 in ZMod13 |
| actual R→ZMod29 evaluation | Nonempty typed RingHom and ζ↦7 |
| actual E→ZMod13 evaluation | Nonempty typed RingHom and τ↦4 |
| no E→R / no R→E | two endpoint signature examples |
| q43 coexistence | actual E→+*ZMod43 at37 and R→+*ZMod43 at11; typed Nonempty pair |
| q43 root values | quadratic root37 and nontrivial seventh root11、37≠11 |
| old −7 companion | cyclotomicSevenToTraceOne z y is explicitly TraceOneInt(-2) |
| actual E coordinate | gtailSevenNormCoord a b is explicitly TraceOneInt(-1) |
| parameter diagnostic | discr(-1)=−3,discr(-2)=−7; normτ(-1)=1,normτ(-2)=2 |
| Step032 compatibility | universal NAT iff; tuple(1166,1857,1858,1165) satisfiesfocus but nothEq |
| boundary contrasts | q3 repeated quadratic root；q7 no nonidentity seventh root；q13Gap13 but notTail(13,30) |

q13 Eisenstein residue RingHom は root premiseだけで定義され、prime Factを必要としない。
q13 Gap-only numeric exampleとgenerator evaluationを混同しない。
q29/q13に架空のnative Tail tupleを作っていない。
Step032 selected regressionは38例のbudget/strict geometry/actual E/R ideal compatibilityと
exact balance failureを保持。Step031 selected regressionは26例の条件付きreceiverを保持。
旧 (5,8,9,4) の focus correction 等の歴史記録はそのまま。

## 実行コマンド・終了コード・警告

作業ディレクトリ lean/dk_math。Lakeコマンドは逐次、process-local LEAN_NUM_THREADS=2。
ログと runs.json は `.lake/build/gtail-step033/`。

| Log | Exact command | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 18.3 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 16.52 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 15.73 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` | 0 | 16.16 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall` | 0 | 9.25 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 8.82 |

01はstyle warning1、02/03/04/05/06はwarning0、すべてexit0。
最終 productionは03、testは04。LakeのReplayedを含むfocused buildであり、
全suite/clean recompilation と主張しない。

## 実際の公理出力とimport/source/style監査

04-build.log の全6 public `#print axioms` 出力：

```text
'DkMath.FLT.Seven.seven_root_zmod29' depends on axioms: [propext, Quot.sound]
'DkMath.FLT.Seven.no_eisenstein_root_zmod29' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.eisenstein_root_zmod13' depends on axioms: [propext, Quot.sound]
'DkMath.FLT.Seven.no_seven_geom_root_zmod13' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.not_nonempty_eisenstein_to_seven_cyclotomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.not_nonempty_seven_cyclotomic_to_eisenstein' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

propext、Classical.choice、Quot.sound の範囲内。新axiomはない。
#check RingHom.comp/comp_apply、map_pow/sub/add/one/intCast も04で確認した。

Source closure8948/local168、test8949/local169、local union169、cycle0。
Step032比new owner1のみ、Mathlib追加0、削除0。
neutral RealTrace closure1907/local20からFLT到達0；新source到達範囲内の
全27 neutral Lib ownersからもFLT到達0。
FLT.Seven façade、degree-six domain、global oriented factorization、oriented valuation ownership、
Kummer principalization、CyclotomicQRTraceOneBridgeはnewsource/testclosureにない。
既存carrier closure由来の旧signed/depth/descent modulesの一部は維持されるが、
新proofはactualgeneratorrelation/residuehom/finitefactsだけを使用し、FLTclosureを使用しない。

comment/stringを除去した新Lean2ファイルのforbidden scanで
sorry/admit/axiom/unsafe/native_decide/set_option/explicit False.elimは0。
MIT2026 D. and Wise Wolf header、imports後のmodule file-print、既存indentation/source lintを確認。
新5ファイルとROADMAP追加部分のtabs/trailing whitespace/final newline検査とgit diff --check成功。
ROADMAPはHEAD版のbyte prefixを保持。既存3行目のMarkdown hard-break末尾2空白を保存する。
tracked変更はROADMAPappendのみ；以前のorders/owners/packets/facades/reports/reviews/ledger/statusを
変更していない。imports.json/import-impact.json/audit.jsonに監査証拠。

## Lean結果からの気づき・試した命題・今後の提案

1. direct mapは単なる未実装の契約ではなく、このactual E/R間では**unitalに存在しない**。
   finite-field compositionだけで、domain/DVR/number-field embedding理論なしに示せた。
   これはStep032のmissing-information findingより強いstructural frontier。
2. 同じZMod43に両ordersを写せることとsource間mapの非存在は両立する。
   共通codomainへのmapsは、どちらかを逆向きにliftするmapを供給しない。
3. 追加で試したfinite root集合の完全列挙も成立。q29のnontrivial seventh rootsは6個、
   q13のquadratic rootsは2個。今回必要なpositive/negative witnessesを独立にcalibrateできた。
4. Φ7(1)≠0のexampleはreverse proofで完全なrelationが必要な理由を示す。
   primitive-root/nontrivialityをmap先でも維持するという誤った追加仮定は不要だった。
5. −7 companionのnorm-coordinate mapと−3 Eisenstein ringを型注釈で区別した。
   quadraticという次数だけからsubring/mapを推測しない。
6. 次の候補はthird receiving ring Cへのactual maps、checked generator images/relations、
   source-linked common identity、proper ideal transport/contractionとkernel/nonzero/power条件。
   それを構築すること自体は元global balanceやsigned carrier equalityを供給しない。
   [frontier-033.md](frontier-033.md) にpositive alternativesとmissing provider fieldsを整理した。
   generic finite-no-root helper抽出は今後再利用例が生じた場合に検討し、今回抽象layerを増やしていない。

STOP033。Outcome Bは二方向のdirect unital maps非存在。
compositum/tensor/21st-order、new signed packet、new primitive counterexample、FLT7descentや
unconditional contradictionは得ていないし実装していない。
