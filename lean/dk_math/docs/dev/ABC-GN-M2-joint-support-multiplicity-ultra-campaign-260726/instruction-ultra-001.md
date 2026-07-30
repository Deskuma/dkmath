# Codex Instruction ultra-001

Theme: ABC-GN joint support-multiplicity climax campaign

作業 branch:

```text
wip/ABC-GN-M2-joint-support-multiplicity-ultra-campaign-260726-v1
```

作戦室:

```text
lean/dk_math/docs/dev/ABC-GN-M2-joint-support-multiplicity-ultra-campaign-260726/
```

## 1. Absolute objective

The final target is the existing public theorem:

```lean
theorem DkMath.ABC.abc_main (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℝ, (1 : ℝ) ≤ K ∧
    ∀ (a b c : ℕ), a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)
```

Current source proves it by:

```lean
abc_main_axiom ε hε
```

The campaign must replace that proof with a Lean theorem chain and then delete `abc_main_axiom` from production source.

Do not weaken the statement. Do not introduce a replacement axiom. Do not stop at a conditional contract theorem and call it victory.

## 2. Confirmed starting Core

M1 is merged and closed.

For every ABC triple `T` and odd prime exponent `p`:

```lean
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
```

Hence:

```text
exceptional excess = 0
τe = 0
De = 0
full excess budget = non-exceptional excess budget
```

The current final bridge already contains:

```lean
GNValuationExcessBudgetAffine
GNNonExceptionalExcessBudgetAffine
GNValuationExcessBudgetAffine.of_split
Triple.log_c_mul_pred_le_of_support_and_excessBudget
Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
Triple.abc_bound_of_liftGrowth_and_excessBudget
ABCGNFinalBudgetContract
abc_positive_of_GNFinalBudgetContract
```

The exact support/excess identity is also available:

```lean
log_eq_log_rad_add_valuationExcess
log_GN_eq_log_rad_add_GNValuationExcess
Triple.log_GN_eq_log_rad_add_GNValuationExcess
```

Fresh support return is available through:

```lean
GNNonExceptionalSupport
GNNonExceptionalSupportProduct
Triple.nonExceptionalSupport_fresh
Triple.rad_mul_nonExceptionalProduct_dvd_lift_rad
Triple.log_rad_add_log_nonExceptional_le_log_lift_rad
GNLiftRadicalGrowthBudgetAffine
Triple.GNSupportBudgetAffine_of_liftGrowth
```

Search current source and verify every theorem name, namespace, import, and assumption before use.

## 3. Strategic correction

Do not attack M2 and M3 as two unrelated estimates.

For a non-exceptional GN prime `q` with valuation `v_q`:

```text
support width         = log q
multiplicity depth    = (v_q - 1) * log q
total channel mass    = v_q * log q
```

Thus:

$$\log q+(v_q-1)\log q=v_q\log q$$

M2 is the first support layer. M3 is the stack of all higher support layers.

The central campaign object is the joint non-exceptional pressure, not two separately maximized budgets.

Use the notation conceptually:

```text
R = log rad(T.a * T.b * T.c)
L = log rad(lifted ABC product)
S = log GNNonExceptionalSupportProduct
E = GNNonExceptionalValuationExcess
G = log GN
```

The starting inequalities suggest:

```text
G <= log(rad p) + (L - R) + E
R + S <= L
```

and, if the exact radical identity is proved:

```text
L - R = S
G = log(rad p) + S + E
```

up to the exact equality/inequality direction established in Lean.

## 4. Checkpoint U-001A - exact odd-prime normal form

First close all deterministic accounting needed by the campaign.

Recommended module:

```text
lean/dk_math/DkMath/ABC/GNJointPressureOddPrime.lean
```

A better current dependency location may be used if justified.

Prove an odd-prime normal form combining:

```text
exceptional excess = 0
support split
exact log GN identity
fresh non-exceptional support
```

Target theorem shapes may include:

```lean
theorem Triple.log_GN_eq_log_rad_add_nonExceptionalExcess_of_oddPrime
    (T : Triple) {p : ℕ}
    (hp : Nat.Prime p) (hpOdd : Odd p)
    (hpTwo : 2 ≤ p) (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log ((GN p T.a T.b : ℕ) : ℝ) =
      Real.log (rad (GN p T.a T.b) : ℝ) +
        GNNonExceptionalValuationExcess p T.a T.b
```

and a joint upper accounting theorem of the form:

```text
log GN
<= log(rad p)
 + (log liftRad - log originalRad)
 + nonExceptionalExcess
```

Do not introduce a budget assumption to prove an identity or deterministic inequality.

## 5. Checkpoint U-001B - joint pressure contract and direct bridge

Define a joint affine predicate that keeps support growth and non-exceptional depth together.

Recommended shape:

```lean
def GNOddPrimeJointPressureBudgetAffine
    (T : Triple) (p : ℕ) (ρ C : ℝ) : Prop :=
  Real.log (rad ((T.gnPowerLift p).a *
      (T.gnPowerLift p).b * (T.gnPowerLift p).c) : ℝ) +
      GNNonExceptionalValuationExcess p T.a T.b
    <=
  (1 + ρ) * Real.log (rad (T.a * T.b * T.c) : ℝ) + C
```

Adjust syntax and ownership to current style.

Prove:

```text
lift-growth budget (σ, Cs)
+
non-exceptional excess budget (τ, D)
->
joint budget (σ + τ, Cs + D)
```

Then prove a direct odd-prime height bridge from the joint predicate without splitting it back into independent M2/M3 goals.

Expected shape:

```lean
theorem Triple.log_c_mul_pred_le_of_oddPrime_jointPressure
    ... :
    (((p - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) <=
      ρ * Real.log (rad (T.a * T.b * T.c) : ℝ) +
        (C + Real.log (rad p : ℝ))
```

Then provide a pointwise ABC wrapper with an explicit constant depending only on campaign-uniform parameters, never on `T`.

This bridge is a deterministic transport theorem. Complete it before spending Ultra reasoning on arithmetic scarcity.

## 6. Checkpoint U-001C - exact odd-prime lift-radical identity

Audit and attack the exact identity:

```lean
rad ((T.gnPowerLift p).a *
     (T.gnPowerLift p).b *
     (T.gnPowerLift p).c)
  =
rad (T.a * T.b * T.c) *
  GNNonExceptionalSupportProduct p T.a T.b
```

Expected mechanism:

```text
lift product support
=
original ABC support
union
GN support not already in original ABC support

non-exceptional GN support is fresh from a*b*c

odd-prime exceptional GN support collapses to p
and p | GN -> p | T.a
so exceptional support is already in original ABC support
```

Prove both divisibility directions or prove equality through factorization support extensionality.

Do not assume the equality merely because the existing one-way divisibility theorem suggests it.

If exact equality needs positivity or `2 <= p`, expose the minimal assumptions precisely.

A successful equality changes the joint quantity from:

```text
(L - R) + E
```

into the exact support-depth mass:

```text
S + E
```

## 7. Checkpoint U-001D - valuation-excess layer-cake

Re-express non-exceptional valuation excess as higher-depth support layers.

For each non-exceptional support prime `q`:

$$\left(v_q-1\right)\log q=\sum_{k=2}^{v_q}\log q$$

Introduce a finite depth-support API only if it improves the proof surface.

Possible definitions:

```lean
def GNNonExceptionalDepthSupport
    (p a b k : ℕ) : Finset ℕ :=
  GNNonExceptionalSupport p a b |>.filter
    (fun q => k <= (GN p a b).factorization q)
```

Possible target:

```text
GNNonExceptionalValuationExcess
=
sum over depth k >= 2 of
  log(product of non-exceptional primes surviving to depth k)
```

Choose a finite outer range derived from factorization support or a maximum valuation. Do not introduce an infinite series when a finite identity is available.

This layer-cake theorem is intended to convert M3 into the same support language as M2.

## 8. Checkpoint U-001E - support-heavy / multiplicity-heavy pincer

Prove a rigorous finite weighted dichotomy.

The intended statement is:

```text
Either:
  non-exceptional excess <= (K - 1) * non-exceptional support mass

Or:
  there exists a non-exceptional support prime q
  with factorization exponent at least K + 1
```

Use positive log weights of prime support and a weighted-average argument.

Do not rely on informal averaging. Handle empty support, `K = 0`, natural subtraction, and cast boundaries explicitly.

Translate the concentration witness into the strongest available arithmetic packet:

```text
q.Prime
q ∤ p
q ∣ GN p T.a T.b
K + 1 <= factorization q
q^(K+1) ∣ GN p T.a T.b
q^(K+1) ∣ T.c^p - T.b^p
q ∤ T.a * T.b * T.c
```

Reuse existing high-lift APIs before introducing duplicates.

## 9. Checkpoint U-001F - Ultra arithmetic assault

After the deterministic accounting, exact identity, layer-cake, and pincer are available, run the arithmetic fronts in parallel.

### Lane E1 - exact multiplicative order

For non-exceptional `q` dividing `GN p T.a T.b`, prove the strongest exact order statement supported by current assumptions.

Expected route in `ZMod q` or a unit group:

```text
T.c^p = T.b^p mod q
q ∤ T.b
q ∤ T.c
T.c != T.b mod q because q ∤ T.a
p is prime
-> order(T.c / T.b) = p
-> p | q - 1
-> q ≡ 1 mod p
```

Audit whether existing DkMath order, cyclotomic, primitive-divisor, or ZMod lemmas already provide this packet.

### Lane E2 - deep lift classification

For `q^k | GN`, transport to `q^k | T.c^p - T.b^p` and classify the root lift.

Investigate:

```text
simple derivative because q ∤ p*T.b*T.c
unique Hensel lift of the nontrivial p-th root
Teichmuller-type stability
Wieferich-type congruence constraints
```

A simple root does not by itself forbid arbitrarily deep lifts. Do not claim exclusion from Hensel uniqueness alone. Extract the exact additional arithmetic obligation.

### Lane E3 - primitive divisor and fresh support

Search and reuse:

```text
PrimitiveSet
Petal
BezoutBridge
ErdosBridge
ValuationFlowBridge
FullChannelLogSum
primitive divisor / Zsigmondy APIs
```

Determine whether fresh-prime existence, order `p`, and layer depth can force a joint bound even when neither M2 nor M3 has a strong independent bound.

### Lane E4 - repeated and adjacent lifts

Investigate whether deep concentration at one `q` consumes support or valuation capacity in:

```text
adjacent exponents
repeated GN power lifts
nested Petal addresses
finite-prime synchronization worlds
```

Formalize only routes that create a real inequality, finiteness theorem, or contradiction packet.

### Lane E5 - computational reconnaissance

Finite experiments may guide theorem discovery and locate counterexamples to proposed intermediate lemmas.

They may not be used as the general proof of the final theorem.

Record failed conjectures immediately so other lanes do not reuse them.

## 10. Checkpoint U-001G - uniform joint budget synthesis

The final arithmetic target is an unconditional uniform joint contract strong enough for every `ε > 0`.

A possible structure is:

```lean
structure ABCGNOddPrimeJointContract (ε : ℝ) where
  hε : 0 < ε
  p : ℕ
  hp : Nat.Prime p
  hpOdd : Odd p
  ρ : ℝ
  C : ℝ
  margin : ρ <= ((p - 1 : ℕ) : ℝ) * (1 + ε)
  jointBudget :
    ∀ T : Triple, 0 < T.a -> 0 < T.b ->
      GNOddPrimeJointPressureBudgetAffine T p ρ C
```

This is only a suggested transport package, not the final theorem.

The required mathematical victory is to construct the contract unconditionally from proved arithmetic facts, with parameters depending only on `ε` and the chosen exponent, not on `T`.

Do not leave this contract as a new hypothesis of `abc_main`.

Try both directions:

```text
choose one fixed odd prime exponent p as a universal probe
or
choose p as a controlled function of ε
```

Audit coefficient margin carefully. A large exponent may increase return `(p-1)` but can also change constants and support channels.

## 11. Checkpoint U-001H - raw-variable endpoint and abc_main replacement

Once positive triples are closed uniformly, bridge to the exact raw-variable surface:

```lean
∀ a b c : ℕ,
  a + b = c ->
  Nat.Coprime a b ->
  ...
```

Handle separately:

```text
a = 0
b = 0
0 < a and 0 < b
```

For zero-coordinate cases, derive the exact coprime consequences and inspect the repository definition of `rad 0`. Do not assume endpoint simplification without checking.

Then modify:

```text
lean/dk_math/DkMath/ABC/ABCMainTheorem.lean
```

Final required state:

```lean
theorem abc_main (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℝ, (1 : ℝ) <= K ∧
    ∀ (a b c : ℕ), a + b = c -> Nat.Coprime a b ->
      (c : ℝ) <= K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  -- theorem proof, no project axiom
```

After this theorem builds:

```text
delete abc_main_axiom
remove obsolete placeholder commentary
remove or repurpose K_eps only if genuinely unused
update imports without introducing cycles
```

Do not delete the axiom first and leave the branch broken. Replace the theorem proof, verify it, then remove the axiom in the same coherent closure change.

## 12. Ultra continuation policy

Checkpoints are telemetry, not stop conditions.

After each checkpoint:

```text
write report-ultra-001-<checkpoint>.md
review the new mathematical state
continue to the strongest next route
```

Do not return merely because:

```text
a joint predicate was defined
a direct bridge was proved
a reduction proposition was isolated
one arithmetic lane failed
a checkpoint report was written
```

Share successful lemmas across lanes and keep attacking until the public theorem is closed or the active Ultra run is externally interrupted.

If one proposed statement is false, preserve the counterexample or failed proof analysis, weaken only that intermediate statement, and continue toward the unchanged final theorem.

## 13. Trust and dependency boundaries

```text
no new axiom
no sorry
no native_decide
no finite enumeration as a general proof
no hidden assumption equivalent to abc_main
no weakening of abc_main
no circular import through ABCMainTheorem
no use of abc_main or abc_main_axiom in the new arithmetic chain
no ABC -> FLT5 production dependency
no FLT7 WIP dependency
no unrelated refactor
```

Allowed final operation:

```text
replace abc_main proof
remove abc_main_axiom
```

but only after the theorem chain is complete.

## 14. Validation and final flag

Run focused builds continuously, then final integration checks.

Required final audit:

```text
lake build DkMath.ABC.<new modules>
lake build DkMath.ABC
lake build DkMath
#print axioms DkMath.ABC.abc_main
git diff --check
```

The final axiom audit must not contain a DkMath project axiom.

Create:

```text
ULTRA_FINAL_REPORT.md
```

The final report must record:

```text
completed theorem chain
joint pressure definition and exact identities
support-depth pincer
arithmetic theorem that supplies the uniform joint budget
zero-coordinate endpoint treatment
final K construction
abc_main replacement diff
abc_main_axiom deletion
axiom audit
build results
```

At final victory, update the campaign README and `CODEX_START.md` with:

```text
ABC-GN joint support-multiplicity campaign: complete
abc_main_axiom: removed
abc_main: theorem-proved
```

## 15. Begin Ultra mode

Start with current-source reconnaissance and U-001A exact odd-prime accounting.

Build the deterministic joint bridge rapidly, then spend the Ultra reasoning budget on the arithmetic obstruction. Run all useful fronts, reuse every discovered theorem, and continue through the `abc_main` replacement.
