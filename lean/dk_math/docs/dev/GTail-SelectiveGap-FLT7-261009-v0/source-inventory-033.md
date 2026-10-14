# Step033 — direct unital RingHom feasibility inventory

2026-10-11。Base HEAD `343827dc291fed225dd2f3cd36faa56794d49448`。
review032/report032/inventory032/frontier032 と現行ソースの型を比較。
review032 は静的レビューであり、独立の Lean build 証拠ではない。

## Exact source / target contracts

| Object/API | Exact source | Exact target | Required relation / premise | Meaning |
|---|---|---|---|---|
| TraceOneQuadratic.tau (-1) | E=TraceOneInt(-1) | E | traceOne_tau_sq: τ*τ=τ+ofInt(-1)(-1) | τ²−τ+1=0、discriminant−3 |
| eisensteinResidueRingHom t ht | E | ZMod q | ht:t²−t+1=0；このhom定義自体にprime仮定は不要 | actual **unital** residue RingHom、τ↦t |
| SevenCyclotomicDegreeSixInt.zeta | R=actual degree-six Ring | R | zeta_geom_sum: 1+ζ+ζ²+ζ³+ζ⁴+ζ⁵+ζ⁶=0 | integral polynomial relation |
| evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 | R | ZMod q | Fact primeq、r≠0、r⁷=1、r≠1 | actual **unital** RingHom、ζ↦r |
| hypothetical f | E | R | f:E→+*R；unital性は bundled type の一部 | compose actual ev29 とすると矛盾 |
| hypothetical f | R | E | f:R→+*E；unital性は bundled type の一部 | compose actual ev13 とすると矛盾 |
| old cyclotomicSevenToTraceOne z y | two integers | TraceOneInt(-2) | explicit cubic coordinate pair；cyclotomicSeven_eq_traceOneNorm_negTwo | discriminant−7 companion；Eではなく、関数の型はRingHomでもない |
| old PrimeTraceOneCoordinatePacket.coord | packet + z,y:ℤ | TraceOneInt(signedPrimeParameter p) | Field/Algebra/IsCyclotomicExtension/primitive-root/Fact prime packet | conditional norm-coordinate API、E↔R RingHom ではない |

TraceOneInt は two signed integral coordinates と parameter-dependent multiplicationを持つ。
traceOneCommRing / intCast は actual source instances。ofInt s n=⟨n,0⟩。
private τ relation は traceOne_tau_sq と pow_two を使ってから座標正規化する。
新しい source ring 定義、quotient ring、field embedding は導入しない。

## Residue obligations

| Characteristic | Existing receiving RingHom | Positive finite witness | Negative finite witness | Result |
|---|---|---|---|---|
| 29 | R→+*ZMod29 | r7≠0、r7⁷=1、r7≠1、prime29 | ∀x:ZMod29,x²−x+1≠0 | E→R の unital map は存在しない |
| 13 | E→+*ZMod13 | t4²−t4+1=0 | ∀x:ZMod13,1+x+x²+x³+x⁴+x⁵+x⁶≠0 | R→E の unital map は存在しない |
| 43 | separate E/R→+*ZMod43 | t37 and r11 | negative relationなし | 同一codomainへの2 mapsは上の非存在と両立 |

Finite no-root lemmas は Fintype ZMod29/ZMod13 の universal proposition に decide を使用。
29/13 Tail c,g tuple の存在や整除は仮定しない。q13 Gap-only calibration と今回の
任意generatorに対する finite-field evaluation は別契約。
逆方向は完全なΦ7関係を保存する。ζ⁷=1の保存だけでは像1を除外できない。

## Checked library APIs / overlap

RingHom.comp : (B→+*C)→(A→+*B)→(A→+*C)、comp_apply の型を
Mathlib/Algebra/Ring/Hom/Defs.lean で確認。congrArg composite generator relation の後、
map_pow/map_sub/map_add/map_one/map_zero で有限体の polynomial equality を得る。
map_intCast と integer-cast normalization は repository-local #check testでも確認。
これらの unital identities を外して非unital mapまで排除する主張はしない。

GTailGlobalBalanceFirewall の hfocus-only iff は contextのみ。no-hom proofに hEq、hfocus、
positivity、primitive、scalar budget、descent provider の仮定は一切ない。
QuadraticBridge と CyclotomicQRTraceOneBridge は型比較のみ、変更や新importなし。
前者は既存carrier closureに含まれ、後者のheavy field ownerは新rootから到達しない。

新 owner direct import は Step032 一つ。root RingHom / zeta relation owners は既存
closureにあるため targeted extra import不要。testも新owner一つだけ。
測定 closure、公理、gate別のbuild結果は report-033.md。歴史的sources/recordsは保持。
STOP033：compositum、tensor、21st-cyclotomic ring、ideal class、signed packet、descentを追加しない。
