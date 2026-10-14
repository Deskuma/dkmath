# Step 024 — native Tail first-order depth inventory

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `bbad4a0924db50073d8a18660cbac9c418e77d93`.
review-023 / report-023 / source-inventory-023 を確認。review は static review、独立 build ではない。

## Actual carrier and input contract

R は既存 `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`。
`coordinates : R ≃+ (Fin6→ℤ)` は additive equivalence、順序 (x0,x1,x2,y0,y1,y2)。
Step022 `coordinates_natCast_mul` は actual scalar multiplication の座標互換性を証明済み。
同 owner の scalar ideal coordinate criterion、six-kernel product=(q) を再利用。
Step023 の F_i は natural c,g から actual R に cast した linear factors。
その element product=original GTail と inverse-slot incidence を使う。
Step020/021 の maximal kernels と integer contraction は packet-free roots を受け取る。
scalar membership の contraction は actual RingHom の `map_natCast` と
`ZMod.natCast_eq_zero_iff` から直接読み取れる。signed-packet の kernel に読み替えない。

## Mathematical preflight and minimal Lean gates

紙上の route: selected F_i が J_i² に入れば、残り factors の membership を掛けて
∏F ∈ (∏J)*J_i。J_i=K_(sixInverseSlot i) で involution による reindexing が∏J=∏K=(q)。
scalar n∈(q)*K は principal-product membership により n=q*y, y∈K。
座標0から q|n を読み、n=q*m の natural quotient を作る。
各 signed coordinate で非零整数 q を消去して actual source y=(m:R) を証明。
RingHom contraction から q|m、従って q²|n。
逆に q²|n なら y=q*k は K に入るため n=q*y∈(q)*K。
これは scalar iff であり **(q)*K=(q²) という ideal equality ではない**。

初期 owner を scalar cancellation/contraction の最小 Lean sandbox として使い、
その focused gate が通るまで finite-product/depth receiver を追加しない。
source の IsDomain instance は存在するが、今回の整数 scalar cancellation は signed coordinates だけで十分。
PID/UFD/class-group structure を仮定しない。

## Checked actual Mathlib APIs

- `Ideal.mem_span_singleton_mul`: x∈span{y}*I iff ∃z∈I,y*z=x。
  任意 ideal multiplication membership を single product と仮定するのでなく、この principal case theorem を適用。
- `Ideal.mul_mem_mul`, `Ideal.prod_mem_prod`: genuine multiplication/finite-family membership。
- `Finset.prod_erase_mul`: prod(erase i)*f i=prod(all) when i∈all。
  elements と ideals 両方に適用して selected square の余分な一コピーを保持。
- `pow_two`, `mul_assoc`: J_i² の掛け合わせを (∏J)*J_i に整形。
- explicit `Equiv` with both inverse proofs, `Equiv.prod_comp`: verified inverse-slot involution で finite family を reindex。
- `mul_right_inj'`: 非零 left scalar q の整数 multiplication injectivity。
- `ZMod.natCast_eq_zero_iff`, `map_natCast`, `Nat.cast_mul`, `Int.natCast_dvd_natCast`：
  natural/integer divisibility、actual quotient witness と casts。
- `Ideal.span_singleton_mul_span_singleton` / `Ideal.mul_le_left` も source確認したが、
  mandatory proof は上の principal membership / finite product APIs が最小。

## Existing July 2026 oriented valuation owner

Read `DkMath/FLT/Seven/SevenRamifiedFusionOrientedCarrierValuationOwnership.lean` and
`DkMath/FLT/Seven/docs/FLT7-FUSION-004B-U1-2-ORIENTED-CARRIER-VALUATION-OWNERSHIP-REPORT.md`
(Date2026-07-30)。既に exact local-power cutoff が repository にある。
`carrier_mem_orientedKernelPower_iff (s:p.QuotientPrimeSupport) (k:ℕ)` は
`p.signedDepth.cyclotomicDegreeSixCarrier ∈ s.orientedKernel^k ↔ k≤s.quotientExponent`。
quotientExponent は `padicValNat s.1 (Int.natAbs p.signedDepth.quotientRoot)`。
対象は supplied signed-depth fusion packet、support prime、oriented quotient root address。
faithfully-flat contraction、real-core cutoff と conjugate carrier、ramified-axis coprimality を使う既存 theorem。

今回 F_i(c,g) の natural endpoints とその signed carrier の typed equality、
canonical bare root kernel と s.orientedKernel の equality、GTail と signed quotientRoot の valuation alignment はない。
従って旧 exact iff を F_i に直接適用できない。今回の成果を「repository初の local valuation theorem」と呼ばない。

## Dependency and proof budget

新 owner は Step023 direct import 一つ、新 test はその owner 一つ。
旧 oriented valuation owner / Domain / full FLT facade を追加 import しない。
scalar gate → finite excess-product gate → guarded cutoff → numeric controls → audits の順で進める。
process-local LEAN_NUM_THREADS=2 の逐次 focused builds。no full clean build / additional proof-limit options。
旧 ring definitions、signed owners、drivers、ledger は変更しない。
q²∤T を FLT equation から導かず、optional FLT reader は追加しない。
深い multiplicity、unit/class extraction、signed packet reconstruction、primitive tuple/descent は対象外。
