# Findings 025

## Preflight 024 support verification

Neither alleged transcription mismatch is present in the live checkout.

- report-024.md line 208 has terminal support {59,79} and continuing support {19}; together these give {19,59,79} at 297 squared plus 350.
- report-024.md line 210 has terminal support {241,401} and continuing support {11}; together these give {11,241,401} at 1031 squared plus 90.
- LegendreTerminalProductCalibration.support297_shared_checked at line 113 uses {19,59,79}. continuing297_shared_checked uses {19}.
- LegendreTerminalProductCalibration.support1031_checked at line 190 uses {11,241,401}. continuing1031_checked uses {11}.
- New report024_arithmetic_checked proves both point values and factorizations in Lean: 88559 = 19*59*79 and 1063051 = 11*241*401. Independent integer diagnostics agree.

No 024 report or calibration was changed. The apparent 41 and 37 substitutions were not confirmed. Existing kernel carriers were preserved.

## Exact boundary

For all natural d and m, PascalPrebirthAlternationMod d m is equivalent to AllInnerChooseDivisible (d+1) m. Moduli zero and one are permitted. Modulus two also works: minus one equals one, so the alternating phase collapses without invalidating cancellation.

For prime p and N > 1, common p divisibility holds exactly when N is a positive p-power. The common inner gcd is the base prime at a prime power and one otherwise. For N > 1, common divisibility by N itself is exactly primality. Consequently row N-1 alternation modulo N characterizes prime N.

## Defect diagnostics

The scan uses prime bases through 31 and positive powers at most 128. It checks 138 prime-target transitions and 663 higher-power-target transitions. Rows start at one; transition endpoints are strictly before the target row. Smallest means first in the recorded order: base prime, exponent, row. No universal minimality theorem is claimed.

Raw quantities are adjacent nonzero count A, phase mismatch count M, and centered adjacent residue sum C. Normalized quantities are A/d, M/(d+1), C/d, with d >= 1. All ratios in diagnostics are exact fractions.

| Family | Observable | Target | Rows | Values |
| --- | --- | --- | --- | --- |
| Prime | A | 5 | 1 to 2 | 1 to 2 |
| Prime | M | 5 | 2 to 3 | 1 to 3 |
| Prime | C | 5 | 1 to 2 | 2 to 4 |
| Prime | M/(d+1) | 5 | 2 to 3 | 1/3 to 3/4 |
| Prime | C/d | 7 | 1 to 2 | 2 to 3 |
| Higher power | A | 4, base 2 | 1 to 2 | 0 to 2 |
| Higher power | M | 4, base 2 | 1 to 2 | 0 to 1 |
| Higher power | C | 4, base 2 | 1 to 2 | 0 to 2 |
| Higher power | A/d | 4, base 2 | 1 to 2 | 0 to 1 |
| Higher power | M/(d+1) | 4, base 2 | 1 to 2 | 0 to 1/3 |
| Higher power | C/d | 4, base 2 | 1 to 2 | 0 to 1 |

These increases have named Lean regressions. A/d has no increase for prime targets: before the first boundary each in-range adjacent defect is nonzero, by pascalCancellationDefect_ne_zero_of_next_row_lt, and at row p-1 all defects vanish. Thus its exact prime-target pattern is one followed by zero, rather than gradual decay. No generic Antitone theorem is added. All six candidate quantities fail decreasing behavior for higher powers.

## Exact fresh ledger

For n >= 3, a prime p above n squared divides GnomonPascalCell n exactly when SquareCell n p. Its height is exactly one. Nonprime coordinates have factorization height zero. Therefore the fresh carry log ledger equals the shell prime-only birth mass term by term.

The full exact identity is:

log GnomonPascalCell n = gnomonPascalOldLogBudget n + gnomonPascalShellBirthLogMass n.

There are no extra fresh cancellation terms. All old repeated-prime contributions and factorial cancellations are retained in the binomial carry height. The old-coordinate cutoff here is n squared, not the capacity stack's old-wave cutoff n.

The missing theorem is a strict bound on the old budget. The new global equivalence identifies that strict inequality for every n >= 3 with LegendreConjecture; anchors one and two are separately checked. This names the unresolved problem and does not prove it.

Full diagnostics are [pascal-diagnostics-025.json](logs/pascal-diagnostics-025.json); compact readouts are [pascal-diagnostics-025.txt](logs/pascal-diagnostics-025.txt). All integer factorizations, counts, heights and ratios are exact. Real log readouts are explicitly approximate and are not proof evidence for a strict inequality.
