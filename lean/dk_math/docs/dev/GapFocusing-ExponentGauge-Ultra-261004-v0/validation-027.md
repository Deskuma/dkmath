# Validation 027

All final measured builds passed with LEAN_NUM_THREADS=2.

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 37.859 | 7495276 | 0 | 599702 | 0 |
| facade | 0 | 12.24 | 6740292 | 0 | 201388 | 0 |
| root | 0 | 13.043 | 7107420 | 0 | 201903 | 0 |
| axiom-audit | 0 | 12.294 | 6681060 | 0 | 194998 | 0 |

Full named public axiom coverage includes 53 production
declarations (30 newly added) in both changed production
modules and 19 new calibration declarations, 72 total.
Only propext, Classical.choice and Quot.sound are permitted by the complete
checker; no new sorryAx dependencies occur.

The focused target set is OddReciprocal, SquareShellPrimePowerGauge, and
SquareShellReciprocalCalibration. The existing SquareShellPrimePowerCalibration
was rebuilt as a dependency and passed. The Legendre facade and DkMath root
were built in full. Their source files were not changed: the existing Gauge
import exports this extension and its neutral dependency.

The final focused and axiom logs contain no warnings. The facade replayed
the existing PacketCross unused-variable warning. Existing unrelated root
warnings were replayed:

- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

## Process telemetry

All four final builds were measured with /usr/bin/time -v and
LEAN_NUM_THREADS=2. The requested process metrics are:

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 37.859 | 7495276 | 0 | 599702 | 0 |
| facade | 0 | 12.24 | 6740292 | 0 | 201388 | 0 |
| root | 0 | 13.043 | 7107420 | 0 | 201903 | 0 |
| axiom-audit | 0 | 12.294 | 6681060 | 0 | 194998 | 0 |

The largest reported peak RSS was 7495276 kbytes, about 7.148 GiB.
Major page faults and reported swap counts were zero in all four measurements.
Minor faults are reported separately in the table. GNU time measures the Lake
invocation and waited descendants; these are process measurements, not total
concurrent host memory or a complete machine-wide swap monitor. Cache replay
and actual compilation are both present. The final focused run rebuilt Gauge
and both the inherited 026 and new 027 calibrations after the module doc edit.

[Telemetry and validation](validation-027.md) retains the raw output and
structured records. The measurements do not give an upper bound for every
future repository build.

- [focused raw telemetry](logs/telemetry-focused-027.txt), [structured record](logs/performance-focused-027.json), [build log](logs/focused-027.txt).
- [facade raw telemetry](logs/telemetry-facade-027.txt), [structured record](logs/performance-facade-027.json), [build log](logs/facade-027.txt).
- [root raw telemetry](logs/telemetry-root-027.txt), [structured record](logs/performance-root-027.json), [build log](logs/root-027.txt).
- [axiom-audit raw telemetry](logs/telemetry-axiom-audit-027.txt), [structured record](logs/performance-axiom-audit-027.json), [build log](logs/axiom-audit-027.txt).

All process exits were zero; no killed process, timeout, manual termination,
or actual OOM failure occurred. The two-thread choice follows the checkpoint
setup and is not an OOM diagnosis. Reported swap count zero is a GNU time
field, rather than a separate global swap-usage measurement.

## Audits and artifacts

The final checker covers all named public declarations in both changed
production sources and the new calibration, unified headers and immediate
file markers, forbidden constructs, dependency direction, tracked and untracked
Lean whitespace, the 5000-shell diagnostic extension, exact rational sums,
20 report answers, the next-frontier proposal and parser-safe ASCII artifacts.
The neutral OddReciprocal module imports no Legendre, RH or L-series module.
No RH or L-series import was added to Gauge.

All real logarithm diagnostics and strict numerical comparisons are explicitly
approximate and were not used as theorem premises. Structural kernel examples
cover the requested multiple and high-depth patterns and large preserved anchors.
The source inventory was written before production changes.

[Final checker output](logs/checks-027.txt) records the completed audits.
[Declaration coverage](logs/declaration-coverage-027.json) lists every printed
declaration. The build-027-*.txt files retain exploratory focused elaborations;
the final four labeled logs and telemetry records carry current build status.
