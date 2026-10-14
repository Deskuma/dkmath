"""Write the report from completed diagnostic and validation artifacts."""
from pathlib import Path
import json,unicodedata,subprocess
base=Path(__file__).resolve().parent.parent
rows={r['n']:r for r in json.loads((base/'logs/diagnostics-036.json').read_text())['rows']}
stats={label:json.loads((base/f'logs/performance-{label}-036.json').read_text()) for label in ['focused','axiom-audit','facade','root']}
assert all(s['exit_code']==0 for s in stats.values())
s="""# Instruction 036 report

Outcome B. An independent compression of the exact non-singleton correction is proved, with a finite prefix budget and an explicit linear leading scale. Q is the largest retained-anchor term. Universal strict closure is not proved, and correction-envelope slack still matters to the sufficient criterion.

## Exact correction and audit

The new [GnomonNonSingletonCorrection module](../../../DkMath/NumberTheory/Legendre/GnomonNonSingletonCorrection.lean) defines

    C_ns = small carry + repeated large carry + higher correction.

For n >= 3 the exact identity oldBudget = Q + C_ns follows from 035 and the old ledger. This equality is a starting point, not the claimed compression.

The audit covered the 028 small/large carry definitions and modular carry bit, the 029 same-base/exponent fiber results, the 030 repeated/singleton split, the 026 odd-depth localization, and the 027 reciprocal/log-log bounds. The existing finite reciprocal budget is stronger than its log-log relaxation, so the new bound uses reciprocal directly. No singleton carrier or budget from the closed 029-035 branch is modified.

Mathlib supplies finite Chebyshev psi and theta, prime von Mangoldt weights, global Chebyshev upper bounds and the Costa-Pereira inequality for psi-theta. These are existing proved global prefix estimates, not PNT or RH inputs. The 029 occupied fiber bound depends on occupied shell targets and does not by itself give the independent prefix compression sought here.

## Component and combined bounds

Small carry has a phase-filtered prime-power carrier below 2*n. Nonnegativity and inclusion give small <= psi(2*n), without inspecting shell primes. This is the natural phase-free bound implemented separately; the exact event sum is not renamed as an upper bound.

Repeated large carry contains only nonprime prime powers below n^2. Inclusion gives repeated <= psi(n^2)-theta(n^2). A private finite identity identifies that difference with the global nonprime von Mangoldt sum. The bound drops carry phase and the lower cutoff, so it may have substantial slack. Exponent >= 2 is already encoded in the nonprime prime-power weight; the proof does not revisit singleton fibers.

The combined bound is stronger than summing those separate bounds. Small and repeated events are disjoint because they lie on opposite sides of 2*n. Their nonprime labels can therefore be charged once to the global nonprime prefix. Their prime labels can only come from the small band and are charged to theta(2*n). Hence

    small + repeated <= theta(2*n) + psi(n^2)-theta(n^2).

Together with the reused higher <= reciprocalBudget theorem, this gives the genuinely independent budget

    B(n) = theta(2*n) + psi(n^2)-theta(n^2) + reciprocalBudget(n),
    C_ns(n) <= B(n)     (n >= 3).

The budget contains no Q, carry predicate, shell event inventory, desired theta increment, old-budget strictness assumption or prime-existence conclusion. The prime inventory inside theta is a global prefix below the width; psi-theta counts only higher powers below the square boundary. This is assembled from existing estimates with a new disjoint-band compression theorem. The improvement over the naive separate psi bound is exactly the omitted low-prefix higher-power mass psi(2*n)-theta(2*n).

## Independent scale and sufficient provider

Let L = log(4), N = n^2 and Hrec = reciprocalBudget(n). Using theta(x) <= L*x, the Costa-Pereira inequality, and psi(x) <= (L+4)*x, Lean proves

    B(n) <= 2*L*n + (L+4)*(N^(1/2)+N^(1/3)+N^(1/5)) + Hrec.

For positive n the leading algebraic scale is linear: N^(1/2)=n, with the other powers n^(2/3) and n^(2/5). The existing reciprocal/log-log gauge controls Hrec. The exported theorem is this explicit inequality, not a newly proved Big-O declaration. The finite B is sharper numerically than this relaxed scale bound.

The new conditional consumer proves

    Q + B(n) < log(cell) -> a prime exists in SquareCell n.

It is sufficient, not an equivalence. Its proof uses the independent correction upper bound and the existing exact old-budget criterion. No bound for Q or universal strict inequality is supplied.

## Retained-anchor diagnostics

The diagnostic enumerates global prefix prime powers independently, computes actual modular carry events for comparison, and checks all component/combined inequalities. It reuses Q and log(cell) from the retained 031 diagnostic, whose SHA-256 is recorded. It covers n=3..300 plus 1031 and 5000 (300 samples). Floating calculations are not Lean premises. The calibration checks repeated labels {81,343,361,529} at n=32, band separation, and universal compression/split instances at all listed anchors.

| n | exact C_ns approx | B approx | Q approx | old margin approx | reduced margin approx | Q/B |
|---|---|---|---|---|---|---|
"""
for n in [32,69,210,297,1031,5000]:
    r=rows[n]
    s+=f"| {n} | {r['correction_approx']:.6f} | {r['budget_approx']:.6f} | {r['singleton_approx']:.6f} | {r['old_margin_approx']:.6f} | {r['reduced_margin_approx']:.6f} | {r['Q_over_B_approx']:.3f} |"+chr(10)
s+="""
All sampled correction bounds hold numerically. The reduced criterion passes numerically at 32 and 1031, but fails at 69,210,297 and 5000 despite their positive exact old margins. At 5000, exact small = 4287.167674, repeated = 79.216579, higher = 0; the phase-free nonprime prefix is 5311.188994 and the width theta is 9895.991379. The resulting B=15228.036962 exceeds the permitted correction allowance by about 419.453377. Therefore compression is structurally useful but still too slack to restore every retained exact-ledger success. These are failures of a sufficient diagnostic, not counterexamples to prime existence or to the proved bound.

Q/B rises from about 3.07 at 297 to 4.82 at 5000, so Q is the principal size frontier at the large anchors. It is not justified to call it the sole remaining obstacle: the correction slack is decisive where the reduced margin is negative. No global assertion about Q dominance or unsampled first failure is made.

## Validation

All four builds use LEAN_NUM_THREADS=2. The axiom audit covers all eight public production declarations, with private helpers covered transitively by their consumers. Only propext, Classical.choice and Quot.sound occur; no sorryAx or new axiom is introduced. New source scans and unified import/file-marker checks pass. git diff --check passes. Timings below are incremental GNU time measurements, not clean-build benchmarks.

| Build | Exit | Seconds | Peak RSS KiB | Swaps |
|---|---|---|---|---|
"""
for label,r in stats.items():
    s+=f"| {label} | {r['exit_code']} | {r['elapsed_seconds']} | {r['maximum_resident_set_kbytes']} | {r['swap_count']} |"+chr(10)
s+="""
The imported PacketCross:285 unused-variable warning remains. The root also reports pre-existing sorry declarations in ZsigmondyCyclotomicResearch:147, TriominoFLT:1919, TriominoCosmicBranchA:4187, GcdNextResearch:850 and CyclotomicPrincipalization:5389. These are outside the new-declaration audit; no repository-wide sorry-free claim is made. No memory failure occurred.

Artifacts: [coverage](logs/coverage-036.json), [diagnostics](logs/diagnostics-036.json), [focused](logs/focused-036.txt), [axiom audit](logs/axiom-audit-036.txt), [facade](logs/facade-036.txt), [root](logs/root-036.txt), [source inventory](source-inventory-036.md), and [artifact check](logs/artifact-check-036.txt). Reproduce with checks/build-036.py (focused axiom-audit facade root), checks/diagnostics-036.py and checks/check-036.py.

## Next natural frontier and implementation proposal

Keep the singleton factor-depth campaign closed. The exact Q term remains the principal short-window quantity, while the independent non-singleton part now has a certified prefix-only scale.

A useful next implementation proposal is a two-dimensional provider accepting an independent upper estimate for Q and a correction envelope: prove that their sum below log(cell) implies prime existence, and retain an explicit slack split between the Q estimate and the correction estimate. For correction precision, the modular small-carry phase and the very sparse repeated large powers are the natural targets; a bound respecting their phase could improve over the global prefix envelope without querying shell primes. For Q, the cofactor windows require a genuine uniform short-window or shell-structure estimate. Neither improvement follows from the present identities. Diagnostic margin failures show why merely declaring Q to be the only obstacle would be premature. No design for Instruction 037, analytic hypothesis, or new unconditional prime range is asserted.
"""
(base/'report-036.md').write_text(s)
for f in (base/'logs').glob('*036*.txt'):
    raw=unicodedata.normalize('NFKD',f.read_text()).encode('ascii','replace').decode()
    f.write_text(raw.replace(chr(92),' setminus '))
with (base/'logs/artifact-check-036.txt').open('w') as out:
    result=subprocess.run(['python3',str(base/'checks/check-036.py')],stdout=out,stderr=subprocess.STDOUT)
assert result.returncode==0,(base/'logs/artifact-check-036.txt').read_text()
print('Report and artifact audit complete.')
