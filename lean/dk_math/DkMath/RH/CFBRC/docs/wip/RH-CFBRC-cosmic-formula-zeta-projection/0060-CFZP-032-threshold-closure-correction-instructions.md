# CFZP-0060 / CFZP-032 correction

## close the internal large-cell threshold before advancing to CFZP-033

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

対象 module:

`DkMath.RH.CFBRC.CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit`

CFZP-032 の主要数学は Green:

- direct `EfficiencyLedger -> radial endpoint`
- Good efficiency = prefactor efficiency × phase efficiency
- phase-envelope monotonicity
- common quadratic coefficient `q(α)=1+2α-α²`
- conditional uniform floor
- weighted reference-mass split
- finite weighted coverage endpoint

ただし original CFZP-032 completion gate では、large-cell threshold は Lean 内で閉じて CFZP-028 cofinal hit に吸収する必要があった。
現実装の

```lean
(hlarge : ∃ J₀ K₀ : ℕ, ∀ j k : ℕ,
  J₀ ≤ j → K₀ ≤ k → Cfzp032UniformReadyCell ε W p j k τ)
```

は外部 hypothesis のままなので、これを除去する。
CFZP-033 にはまだ進まない。

---

## Gate R1 — prove the large-cell phase contract internally

Preferred explicit threshold:

```text
1 ≤ k
```

under

```text
0 ≤ α
α < 1
0 ≤ τ
τ ≤ π/4
```

Aim for:

```lean
theorem cfzp032LargeCellEfficiencyReady_of_one_le
    {α τ : ℝ} {k : ℕ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hτ0 : 0 ≤ τ) (hτ4 : τ ≤ Real.pi / 4)
    (hk : 1 ≤ k) :
    Cfzp032LargeCellEfficiencyReady α k τ
```

Useful facts:

```text
L = π + 2πk + τ
R = 3π/2 + 2πk - τ
q(α) ≥ 1
α ≤ 1
R ≤ L + π/2
R ≤ 2L
L ≥ 3π > 9          when k ≥ 1, τ ≥ 0
```

Use standard exact bounds such as `Real.pi_gt_three` if helpful.
The two quadratic-vs-linear inequalities have ample slack at `k ≥ 1`; sharp constants are unnecessary.

If `k ≥ 1` becomes brittle in Lean, do **not** reintroduce a hypothesis. Instead prove internally:

```lean
∃ K₀ : ℕ, ∀ k ≥ K₀,
  Cfzp032LargeCellEfficiencyReady α k τ
```

using the explicit polynomial formulas / `Tendsto` already used in CFZP-027.
The completion condition is an actual theorem producing `K₀`, not a caller-supplied `hlarge`.

---

## Gate R2 — prove the prefactor-left threshold internally

Preferred explicit exponent threshold:

```text
3 ≤ j
```

For a prime `p` and safe epsilon, prove:

```lean
theorem cfzp032_two_epsilon_le_phaseMagnitudeLeft_of_three_le
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 3 ≤ j) :
    2 * ε ≤ cfzpPrimePowerPhaseMagnitudeLeft ε p j
```

Proof idea:

```text
p ≥ 2
log 2 ≤ log p
ε < log 2
3ε < 3 log 2 ≤ j log p
phaseMagnitudeLeft = j log p - ε
```

Prefer an explicit `j ≥ 3` theorem if it is clean. Otherwise prove an internal eventual exponent threshold `∃ J₀, ...`; again, no external threshold hypothesis.

---

## Gate R3 — automatic `UniformReadyCell`

Combine R1 and R2.

Preferred API:

```lean
theorem cfzp032UniformReadyCell_of_large_indices
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j k : ℕ} {τ : ℝ}
    (hp : Nat.Prime p)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hj : 3 ≤ j) (hk : 1 ≤ k) :
    Cfzp032UniformReadyCell ε W p j k τ
```

If R1/R2 use existential thresholds, expose a theorem producing the combined finite `J₀,K₀` internally.

---

## Gate R4 — remove `hlarge` from cofinal uniformly-efficient transport

Strengthen or replace the current theorem so the caller only supplies the already-existing cofinal ready-hit provider.

Target:

```lean
theorem cfzp032_exists_uniformly_efficient_ready_hit_of_cofinal
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ} {τ : ℝ}
    (hp : Nat.Prime p)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hτ : 0 < τ) (hτ4 : τ ≤ Real.pi / 4)
    (hcofinal : Cfzp027CofinalReadyThirdQuadrantHitsForPrime ε W p τ) :
    ∀ J K : ℕ, ∃ j k : ℕ,
      J ≤ j ∧ K ≤ k ∧
      Cfzp027PrimePowerReadyThirdQuadrantHit ε W p j k τ ∧
      cfzp032UniformReadyGoodEfficiencyFloor ε W τ ≤
        cfzp031ReadyGoodEfficiency ε W p j k τ
```

With explicit thresholds, call `hcofinal (max J 3) (max K 1)` and discharge `UniformReadyCell` by R3.

**No `hlarge`, `J₀`, `K₀` argument may remain in the public theorem.**

---

## Gate R5 — direct irrational-rotation adapter

Compose R4 with CFZP-028 so the conditional dynamical theorem is directly usable:

```lean
theorem cfzp032_exists_uniformly_efficient_ready_hit_of_irrationalRotation
    ...
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ)
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    ∀ J K, ∃ j k, ...
```

Use

```text
cfzp028CofinalReadyThirdQuadrantHitsForPrime_of_irrationalRotation
```

then R4.

This remains conditional on the existing subcriticality and irrationality hypotheses; do not add any new provider.

---

## Gate R6 — optional specialized weighted coverage endpoint

If short, expose the final finite criterion with

```text
ρ₀ := cfzp032UniformReadyGoodEfficiencyFloor ε W τ
```

and per-Good `UniformReadyCell` / ready-hit facts, so callers need not manually provide `hfloor`.

Do not delay threshold closure for this optional wrapper.

---

## Roadmap correction

Update CFZP-032 section after the threshold theorem is closed.

The Green classification should then say:

```text
direct EfficiencyLedger endpoint adapter: CLOSED
prefactor/phase efficiency factorization: CLOSED
phase-envelope right-endpoint monotonicity: CLOSED
common subcritical quadratic coefficient: CLOSED
internal finite large-cell threshold: CLOSED
uniform positive efficiency floor independent of p,j: CLOSED
CFZP-028 cofinal hit -> cofinal uniformly-efficient hit: CLOSED / irrationality-conditional
weighted reference-mass split and ledger lower bound: CLOSED
weighted coverage endpoint criterion: CLOSED
weighted Good reference-mass coverage provider: OPEN / GAP
```

Do not describe the threshold as caller-supplied once R1-R4 are closed.

---

## Firewall

Still do not introduce:

- weighted density / mass-share provider
- equidistribution -> weighted dominance shortcut
- PNT / Mertens
- infinite prime-power sums
- limit exchange
- automatic subcriticality
- automatic prime-phase irrationality
- CFZP-018 unconditional provider
- RH conclusion

---

## Completion

- amend existing CFZP-032 module (no new numbered mathematical checkpoint)
- focused build
- `lake env lean DkMath/RH.lean`
- full `lake build`
- `git diff --check`
- no `sorry` / `axiom` / `native_decide`
- roadmap CFZP-032 status updated

Only after this correction is reviewed Green should CFZP-033 be issued.
