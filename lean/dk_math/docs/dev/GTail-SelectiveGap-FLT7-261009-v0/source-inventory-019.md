# Step 019 — source inventory

Date: 2026-10-10. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD: `19c6e67080859ba71ef95a86c87c3f1fb9739956`.
review-018 / report-018 / source-inventory-018 を確認。review は static inspection で、独立 Lean 実行ではない。

## Four carriers

| Type | Defining equations | Available evaluation | Remaining boundary |
| --- | --- | --- | --- |
| `TraceOneInt (-1)` | τ²=τ−1、norm⟨a,b⟩=Q | Step014 `eisensteinResidueRingHom t ht`、kernel、Step017 oriented square | degree-six source への integral map / ideal transfer はない |
| `SevenRealCubicInt` | signed integral triple、alpha³=2alpha²+alpha−1 | packet address `evalAlphaRoot`、今回の bare-root `evalRealFromSeventhRoot` | signed packet reconstruction を結論しない |
| `SevenCyclotomicDegreeSixInt.Ring` | `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`、ζ²=−1+(alpha−1)ζ、ζ⁷=1 | `ofReal`、packet `localEval`、今回の bare-root evaluation | source-ring identification / ideal equality / unit class は別課題 |
| `ZMod q` | Fact q-prime の field | r、inverse、β=1+r+r⁻¹、Step018 の t | 共通 codomain から source rings 間の map は得られない |

## Exact source prerequisites and reuse

- `GTailSevenPairedResidue`: `gtailSevenTailRatio` と pow_seven/ne_one/ne_zero は q∤c、q|T、q∤g に分割される。`seven_geom_sum_eq_zero_of_pow_eq_one` は r≠1 を要する。今回 cubic で直接再利用。
- `GTailSevenPrimeOrder`: 7|q−1、3|q−1、21|q−1 の既存証明。新しい order proof は作らない。
- `GTailSevenResidueIdeal` / `GTailSevenIdealSquareAddress`: root-guarded Eisenstein RingHom、α の向き付き支持と α² の支持。別の source ring の既存成果として保持。
- `SevenRealCubicInt`: `fst/snd/thd` は ℤ。mul の constant coefficient は x0*y0−(x1*y2+x2*y1)−2*x2*y2、alpha coefficient は x0*y1+x1*y0+(x1*y2+x2*y1)+x2*y2、alpha² coefficient は x0*y2+x1*y1+x2*y0+2*(x1*y2+x2*y1)+5*x2*y2。実際の coordinate lemmas を使う。
- `QuotientPrimeMuSevenAddress.beta_cubic_relation`: seventh-root conditions から geometric sum、field_simp、linear_combination。`evalAlphaRoot` はこの三次関係を乗法に利用する実 RingHom。ただし interface は `p : RamifiedSignedRootDepthPacket` と `q|p.quotientRoot` を持つ address。今回これらを仮定・構成しない。
- `SevenCyclotomicDegreeSixInt.localEval`: `evalAlphaRoot x.re + ratio*evalAlphaRoot x.im`。private `ratio_quadratic_relation` は ratio²=−1+(evalAlphaRoot alpha−1)*ratio を証明。今回同じ符号を neutral `seventhRootBeta_quadratic` から直接検証する。
- `SevenRamifiedFusionCyclotomicRamifiedPrime.ramifiedEval`: 別途 q7 に ζ↦1。r=1 は char43 では β cubic に失敗するが char7 では β3 が根になる。

関連 source を検索した範囲では、既存 bundled degree-six residue evaluation は packet-indexed `localEval` と q7 `ramifiedEval`。
`SevenRealCubicResidueCriterion.cubicRoot_to_primitiveSeventhRoot` も確認：cubic root から algebraic closure 内の primitive seventh root を作る逆向きの criterion で、bare-r から integral cubic/degree-six RingHom を作る API ではない。
今回の receiver は既存 packet API を変更せず追加する。

## Mathlib and dependency order

`ZMod.natCast_eq_zero_iff`、`mul_inv_cancel₀`、`inv_eq_of_mul_eq_one_right`、RingHom の map_intCast/map_natCast/map_mul と
`QuadraticAlgebra.re_mul/im_mul` を実証明で利用。
`Mathlib/Algebra/QuadraticAlgebra/Basic.lean` の `QuadraticAlgebra.lift` もソース確認したが、base algebra instance を追加するより coordinate proof が小さいため利用しない。
neutral trace module は Step018 のみ import。FLT owner は既存 degree-six owner と neutral trace の二 import。
既存 degree-six owner 自体が signed-fusion source closure を持つが、今回の新署名には packet 依存がない。
full Seven facade は直接 import しない。closure の実測値は report に記録する。

実装順：neutral cubic → signed cubic RingHom → quadratic degree-six RingHom → actual Tail factor kernel。
unsupported: Eisenstein→degree-six integral RingHom、両 source の ideal equality、既存 signed packet の linear carrier と今回 F(c,g) の一致。
