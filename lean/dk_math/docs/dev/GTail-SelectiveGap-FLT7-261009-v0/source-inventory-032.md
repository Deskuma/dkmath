# Step032 — necessary versus sufficient contract inventory

2026-10-11。Base HEAD `777f79eaaf63f42e96e7afc8424473dbb98ed2e5`。
review031/report031/inventory031 と実 owner の型・proof routes を確認。
review031 は static review であり、今回の focused build と区別する。

## 必要条件と十分条件の正確な区別

Q=a²+ab+b²、T=GTail 7 1 g c、E=TraceOneInt(-1)、R=SevenCyclotomicDegreeSixInt.Ring。

| Row | Source carrier/type | Actual theorem / contract | Premises | Lost data | hfocus 下で hEq に十分か |
|---|---|---|---|---|---|
| A | ℕ, Fermat7Equation a b c | Basic: a^7+b^7=c^7 | exact equality | positivity/primitive は equation 単独には含まれない | はい、元の equation |
| B | ℕ geometry / Coprime | fermat7_focused_bounds, focused_gap_lt_coordinates | 正a,bとhEqから strict bounds；gapは focus も使用 | inequalities は powers の exact equality を保持しない | いいえ、new numeric witness が全結論を満たす |
| C | ZMod q, prime/unit/order | gtailSeven_paired_residue, root polynomial/pow_seven, order APIs | prime q≠7,q∣Q,T,q∤b,c,g | reduction は integer lift と source ring を保持しない | いいえ、q43 witness |
| D | ℕ, padicValNat q | padicValNat_focused_quadratic_budget; scalar_budget_depth_readouts | FLT-facing はha,hb,hcop,hEq,hfocus,hq,hq7,hQ；abstract は明示 budget,unit,nonzero | q-local exponents は global equality を保持しない | いいえ、同じ budget と偶数depthを witness が満たす |
| E | Ideal E / Ideal R, α² / F_i | gtailSevenNormCoord_split_square_address; mem_square/cube/fourth_iff | Eは q≠3,hQ,b-unit；Rは c/g-units,hT | norm と residue membership は different source element の同一性を与えない | いいえ、actual E square/R exact second depth を witness が満たす |
| F | ℕ または ℤ norm value | 新 fermat7Equation_iff_focused_scalar_balance / iff_focused_norm_balance | **hfocus だけ** | exact balance は元 equation と同値；local contract より強い | **はい、A↔Fを証明** |
| G | old signed packet / closure provider | RamifiedSignedRootDepthPacket; AwayDescentClosureProvider | balanced signed roots, exact normalization；new CounterexamplePack/route/carrier_match | current natural tuple はその data を持たない | local readout から構成する API はない。provider 自体はnextPackにhEqを要求 |

GTailBridge.gtail_seven_shell は CommSemiring で hfocus のみから
`g*T+c^7=(a^7+b^7)+7ab(a+b)Q²`。ℕ の reverse balance iff は同じ interior の
addition cancellation で成立し、positivity/prime/coprimality を要求しない。
Forward は gtail_seven_eq_of_fermat7Equation を再利用。
Integer norm iff は focused_gtail_eq_norm_square を forward に用い、reverse は
norm_gtailSevenNormCoord_sq により norm(α²)=(Q²:ℤ)、exact_mod_cast で NAT equality。
α²∈E と F_i∈R の element equality はない。

Step031 endpoint の hEq を、そこから得た unit/budget/ideal conclusion の集合で置き換える
ことはできない。new witness はその明示的 q43 conclusion の集合を満たすが hEq が false。
これは全既知必要条件や全素数での budget の充足を主張するものではない。
特に seven_dvd_focused_gap の結論7∣gは new g1165 で false（追加 example）。

## 数値指示の検証による訂正

Instruction032 の旧 (5,8,9,4) が additive focus を失敗するという文は誤り。
Lean decide はその否定を false と検出し、`5+8=9+4` を証明した。
旧 tuple は strict geometry も満たす。new tuple の強化点は focus/geometry ではなく
**exact q43 doubled budget と actual R K² membership**。旧 tuple の Tail は depth1。
候補 (1166,1857,1858,1165) の指定値・geometry・primitive・units・depth はすべて Lean 検証。
候補そのものの変更は不要だった。過去 report/review と instruction は歴史記録として未変更。

## Direct imports / existing ownership

新 production は Step031 一つだけを import。GTailBridge、norm owners、ConstraintAudit、
paired residues、ideal receivers は既存 transitive closure にあり targeted extra import は不要。
新 test も新 production 一つのみ。新 signed/oriented owner import は追加しない。
旧 descent/signed packet signatures は source-read のみ（frontier-032.md に正確なfields）。
`docs/STATUS.md` は Lake root に存在しなかったため、実ファイル
`DkMath/FLT/Seven/docs/STATUS.md` を読んだ。July2026 の historical status と現行 sourceを区別し、
公開 repository status は変更しない。

Import DAG の実測値と全公理・forbidden/style/whitespace audits は report-032.md に記録。
既存 carrier 由来の broad closure を新 proof の unconditional closure 使用と混同しない。
STOP032：new descent provider、E→R map、signed packet、K⁵/all-k は実装しない。
