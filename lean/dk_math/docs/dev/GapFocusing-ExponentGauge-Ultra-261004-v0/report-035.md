# Instruction 035 report

Outcome B. Adaptive square-root roughness exhausts all surviving composites with the existing semiprime and ordered three-prime images. The corrected singleton envelope equals Q. This recovers the exact old ledger; no universal strict inequality or new unconditional prime-existence range is claimed.

## Basis and audited dependencies

The production module is [GnomonCofactorAdaptiveRoughness.lean](../../../DkMath/NumberTheory/Legendre/GnomonCofactorAdaptiveRoughness.lean), exported by the Legendre facade. It imports the existing 034 carrier and ParitySafePrimeAnchorCap. The latter supplies the already proved sqrtCutoff_power_four_gt. The 031 wheel bridge, 032 least-factor normal form, and 033 pair image are reused through 034. Primitive.FinitePrimeWorld supplies primeScalesUpTo. Existing ParitySafeSqrtRoughFactorization was inspected for its rough-divisor and fourth-power argument; its distinct active-label carriers were not reused because repeated prime factors matter here.

S(n) = primeScalesUpTo (Nat.sqrt n). Every member is prime, every prime at most Nat.sqrt n is included, and each member is at most n, hence at most 2*n. Desired singleton primes above 2*n therefore remain available. These are separate proved properties, not an inference from minFac being outside S.

The public roughness bridge works with any finite prime basis S covering all primes at most c. Every prime divisor p of a wheel survivor satisfies c < p: otherwise p belongs to S and reserves the candidate, contradicting the 031 membership bridge.

## Structural exhaustion

The general exclusion theorem assumes B < (c+1)^4. Four factors each greater than c have product at least (c+1)^4, even when factors repeat. No four-prime carrier is introduced.

For a composite q, the 032 normal form gives q = r*m with r prime, r <= m, and r no larger than any prime divisor of m. If m is prime, the existing canonical pair belongs to the semiprime image. Otherwise write m = s*t using its least factor, obtaining r <= s <= t. If t were composite, write t = u*v with u prime and u <= v. Coverage forces r,s,u > c and hence v > c. Then q = r*s*u*v contradicts the endpoint. Thus t is prime. A private endpoint membership adapter places (r,s,t) in the existing 034 triple carrier.

This is a bounded least-factor argument with a geometric contradiction, not complete target factorization or an arbitrary-depth hierarchy. The existing reverse inclusion and disjointness yield exact carrier exhaustion. The general theorem takes explicit basis coverage and fourth-power endpoint hypotheses.

For c = Nat.sqrt n, the existing theorem gives n^2+2*n < (c+1)^4. Since B = (n^2+2*n)/k <= n^2+2*n, exhaustion holds for every n and k, including empty quotient windows. Weighted summation gives D3 = E. For n >= 3, the existing lower bound Q <= Y together with Y <= V-D3 = Q gives Y = Q.

The exact budget identity becomes:

    small carry + repeated large carry + adaptive Y + higher correction
      = oldBudget.

Thus singleton approximation slack is completely removed. Strict comparison with log(cell) is still exactly the old-budget comparison; the identity provides no independent estimate for that comparison.

## Regressions and bounded diagnostics

The calibration module imports the retained 034 fixed-wheel regressions. At n=32 the adaptive basis equals {2,3,5}, and both triple products 539 and 343 remain checked. At n=69 the old {2,3,5} basis still admits 2401=7^4 outside the combined image. Adaptively, sqrt(69)=8 and coverage includes 7. The proved prime-divisor lower bound excludes 2401 from every quotient window because 7 divides it. This removal is structural, not a recomputed factorization claim.

The large anchors instantiate universal carrier and budget theorems in Lean. The independent Python diagnostic checks endpoint pair/triple images against actual composite survivor sets for all n=3..300 and n=1031,5000: 300 sampled n values. It verifies injectivity, disjointness and equality at each window. Floating weights and inherited exact-ledger margins are diagnostics only, not proof premises. The source SHA-256 is recorded in diagnostics-035.json. No unsampled range or first global failure is claimed.

| n | cutoff | composites | pairs | triples | E = D3 approx | old margin approx |
|---|---|---|---|---|---|---|
| 32 | 5 | 13 | 11 | 2 | 73.373415 | 62.639084 |
| 69 | 8 | 31 | 30 | 1 | 201.735006 | 110.257087 |
| 210 | 14 | 115 | 112 | 3 | 969.833490 | 406.547983 |
| 297 | 17 | 158 | 154 | 4 | 1427.733453 | 512.592717 |
| 1031 | 32 | 674 | 657 | 17 | 7435.474575 | 2220.404276 |
| 5000 | 70 | 3716 | 3609 | 107 | 50265.323756 | 10442.199332 |

All sampled adaptive residuals vanish. All sampled old-ledger margins are positive numerically. In particular, n=5000 recovers its positive old margin after the fixed-wheel 034 approximation had a negative corrected margin. This is restoration of the retained exact ledger, not a new certified prime-existence range. Fixed-wheel higher-factor examples remain counterexamples to exhaustion without adequate coverage.

## Validation and scope

All builds used LEAN_NUM_THREADS=2. The focused build checks production and calibration. The axiom audit prints all 11 new public production declarations (one definition and ten theorems); only propext, Classical.choice and Quot.sound occur. The private membership helper is covered through the public exhaustion dependency. New Lean files contain no forbidden proof constructs and retain the unified header and immediate file marker. git diff --check passed. Build timings are incremental measurements, not clean-build comparisons.

| Build | Exit | Seconds | Peak RSS KiB | Swaps |
|---|---|---|---|---|
| focused | 0 | 21.339 | 6790032 | 0 |
| axiom-audit | 0 | 12.736 | 6727112 | 0 |
| facade | 0 | 12.676 | 6747988 | 0 |
| root | 0 | 13.408 | 7111192 | 0 |

The imported PacketCross.lean:285 unused-variable warning is retained. The root build also reports pre-existing sorry declarations in ZsigmondyCyclotomicResearch:147, TriominoFLT:1919, TriominoCosmicBranchA:4187, GcdNextResearch:850, and CyclotomicPrincipalization:5389. These are outside the new declaration audit; this report does not claim a repository-wide absence of sorry. No memory failure occurred.

Artifacts: [coverage](logs/coverage-035.json), [diagnostics](logs/diagnostics-035.json), [focused](logs/focused-035.txt), [axiom audit](logs/axiom-audit-035.txt), [facade](logs/facade-035.txt), [root](logs/root-035.txt), and [artifact check](logs/artifact-check-035.txt). Reproduction scripts are checks/build-035.py, checks/diagnostics-035.py, and checks/check-035.py. The build driver takes focused, axiom-audit, facade, and root labels.

## Stopping decision and next implementation proposal

Close the finite factor-depth campaign: the two existing carriers already exhaust all adaptive survivors. Four-, five-, and higher-prime enumerators would add no missing mass under these hypotheses.

The next natural frontier is the exact old-budget inequality. A useful implementation proposal is to expose the deficit after substituting Y=Q as a decomposition into small carry, repeated large carry, higher correction, and Q, with an exact equivalence to the existing prime-existence criterion. Then seek a separately justified uniform estimate for one of those terms, retaining the explicit deficit and endpoint hypotheses. Such an estimate must be mathematically new; renaming exact terms or deepening composite carriers cannot supply it. The non-singleton carry and higher-shell terms are plausible inspection targets, but their improvement is not proved here. No PNT, RH, new analytic assumption, or design for Instruction 036 is introduced.
