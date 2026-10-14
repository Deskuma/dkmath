# Step040 source inventory / capacity contract

2026-10-11。Base HEAD `58f3761acb336aaf41d378b86b26be1ddb8e4984`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
review-039 / report-039 / source-inventory-039 / frontier-039 と現行 owners を確認した。
新 production は Step039 owner 一つのみ direct import。必要な factorization / GCD BigOperators / Int APIs は既存 closure にある。

## Types / extra assumptions

Δ=focusedFermatDefect a b c:ℤ、Q=a²+ab+b²:ℕ、S:Finset ℕ。
M_S=∏p∈S,p²:ℕ。S は distinct elements を持つが prime certificates は別の仮定。
M_S= (S.prod id)²、S=∅ は M_S=1。

| Data | Actual source / output | Additional or missing premise |
|---|---|---|
| selected q²∣Δ | Step039 defect_square_iff_product_nat / defect_square_prime_route | 他の primes の support は出ない |
| collective S support | ∀p∈S,Prime p and (p:ℤ)²∣Δ | new collective premise。Step039 から一括して得たとしない |
| aggregated divisor | M_S∣Δ in ℤ ↔ every selected prime square divides | distinct prime squares の coprimality を使用 |
| strict magnitude | Δ.natAbs<M_S | independent Archimedean premise。focus/primitive から導かない |
| zero / Fermat | aggregate divisor + strict bound → Δ=0 → Fermat7Equation | hEq / Δ=0 を入口で仮定しない |
| canonical Q support | Nat.primeFactors Q, Q≠0 | all-prime support と size の二つの追加前提を公開 |
| capacity | M_Q∣Q² / M_Q≤Q² | bound on ∣Δ∣ そのものではない |
| old reconstruction | signed/provider field contract | local modulus/zero certificate は再帰 provider construction ではない |

Step039 focusedFermatDefect_zero_iff は focus なしで Δ=0 iff hEq。
Step032 fermat7Equation_iff_focused_scalar_balance は hfocus の下で hEq iff exact balance。
GTailBridge.gtail_seven_defect は arbitrary CommRing / focus の identity。
今回 square-depth / C ideals の API を拡張しない。

## Verified library ownership / actual #check

`.lake/build/gtail-step040/api-probe-all.log`（actual #check、exit0、warning0）:

```lean
Nat.mem_primeFactors : p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n ∧ n ≠ 0
Nat.mem_primeFactors_of_ne_zero (hn : n ≠ 0) : p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n
Nat.primeFactors_mul (ha : a ≠ 0) (hb : b ≠ 0) : (a*b).primeFactors = a.primeFactors ∪ b.primeFactors
Nat.Prime.primeFactors (hp : Nat.Prime p) : p.primeFactors = {p}
Nat.prod_primeFactors_dvd (n : ℕ) : (∏ p ∈ n.primeFactors, p) ∣ n
Nat.support_factorization (n : ℕ) : n.factorization.support = n.primeFactors
Finset.prod_pow (S) (2) (id) : (∏ p ∈ S, p ^ 2) = (∏ p ∈ S, p) ^ 2
Nat.coprime_primes (hp : Nat.Prime p) (hr : Nat.Prime r) : Nat.Coprime p r ↔ p ≠ r
Nat.Coprime.pow_left / pow_right
Nat.coprime_prod_right_iff : x.Coprime (∏ i ∈ S, f i) ↔ ∀ i ∈ S, x.Coprime (f i)
Nat.Coprime.mul_dvd_of_dvd_of_dvd : Coprime m n → m ∣ a → n ∣ a → m*n ∣ a
Int.natCast_dvd : (m : ℤ) ∣ z ↔ m ∣ z.natAbs
Int.natAbs_le_of_dvd_ne_zero : m ∣ z → z ≠ 0 → m.natAbs ≤ z.natAbs
Int.eq_zero_of_dvd_of_natAbs_lt_natAbs : d ∣ z → z.natAbs < d.natAbs → z = 0
Int.natAbs_pos : 0 < z.natAbs ↔ z ≠ 0
```

Finset.prod_dvd_prod_of_dvd / dvd_prod_of_mem、Nat.prod_factorization_pow_eq_self も確認した。
これらは factorwise divisibility から arbitrary product divisor を与える API ではない。
実装の private finite induction は distinct primes に coprime_primes を適用し、
pow_left/pow_right 2 と coprime_prod_right_iff で square vs remaining product の coprimality を得る。

Int の generic threshold / lower-bound APIs は m>0 なしでも成立する stronger signature。
有限 prime modulus の strict positivity は別途証明するので required positive-modulus usage を満たす。
負の z に対し z<m を使わず natAbs を使う。

## Existing radical owner / import impact

DkMath.ABC.Rad.rad n は既存 `n.factorization.support.prod (fun p => p)`。
rad_dvd_nonzero と mem_support_factorization_iff も実在する。
Rad owner の direct imports は DkMath.Basic、Mathlib.Data.Nat.Factorization.Basic、Mathlib.Tactic。
これら三つ自体は現在の Step039 closure に既に存在する。
したがって Rad を追加しても既存 module set に対する増分はその owner 一つであり、
今回大きい import regression が実測されたと主張しない。
それでも新 FLT→ABC owner dependency は不要なため追加しなかった。
Mathlib の prod_primeFactors_dvd を直接使い、二つ目の general radical library を作らない。

Mathematical identification は Nat.support_factorization と rad の実際の定義から
(S_Q.prod id)²=rad(Q)²。test で factorization.support product との expression equality を確認する。
ABC.rad という named constant 自体の bridge theorem は import しないので追加しない。

Nat.primeFactors 0 / 1 は empty、対応する square modulus は1。
prod_primeFactors_dvd は n=0 にも成立するが、M_Q≤Q² は Q=0 で1≤0となるため Q≠0 が必須。
canonical certificate は Q≠0 を明示し、edge convention を global magnitude bound と混同しない。

## Read-only reconstruction boundary

AwayDescentClosureProvider は nextX/Y/Z、CounterexamplePack、AwayValuationTransferPacket、
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd`。
RamifiedSignedRootDepthPacket は balanced signed-root identities、coprimality、gap/quotient roots、
7-unit guards、normalizedEquation。今回の divisor/size lemma はこれらの field を構成しない。
旧 signed modules を direct import しない。
