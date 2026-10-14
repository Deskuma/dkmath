# Validation 029

All final measured commands used LEAN_NUM_THREADS=2 and exited successfully.

- focused: lake build DkMath.NumberTheory.Legendre.GnomonCarryFiber DkMathTest.NumberTheory.GnomonCarryFiberCalibration
- facade: lake build DkMath.NumberTheory.Legendre
- root: lake build DkMath
- axiom: lake build DkMathTest.NumberTheory.GnomonCarryFiberAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 20.175 | 6763740 | 0 | 371758 | 0 |
| facade | 0 | 12.57 | 6744744 | 0 | 201160 | 0 |
| root | 0 | 13.278 | 7107944 | 0 | 210353 | 0 |
| axiom-audit | 0 | 12.654 | 6686128 | 0 | 197013 | 0 |

The final focused run rebuilt the new production and calibration after a
comment-only cleanup and replayed imported dependencies. GNU time metrics cover Lake and
waited descendants, not total host memory. Raw text and structured telemetry
remain in logs with suffix 029. No observed OOM, kill or timeout occurred.

Complete coverage is 18 production and 14 calibration declarations, total 32.
The dynamic producer checks the entire new module and calibration. The audit
accepts only standard logical axioms and no sorryAx dependencies. No forbidden
proof construct or reversed facade dependency was introduced. All three new
Lean files and the changed facade have the standard header and file marker.
Both tracked and untracked Lean whitespace are checked.

Exact bounded diagnostics reuse the hashed 028 inventory, n=3..5000. Every
same-base exponent fiber is compared with an independently computed cutoff
and valuation interval and direct power divisibility. Singleton prime weights
are reconstructed from the original prime-label delta stream. Logs and strict
provider tests are floating diagnostics, not proof premises. Mandatory earlier
anchor data, ten-exponent collision, first cutoff slack and the smallest mixed
base counterexample remain represented.

Kernel calibration fixes finite exponent carriers, exact symbolic weights,
strict slack at the first example, the mixed-base counterexample and the failure
of one log per target. No large transcendental computation is kernel evaluated.
The existing PacketCross facade warning and five unrelated root sorry warnings
remain. Neither contributes a sorry axiom to the new declaration audit.

Reproduction scripts: coverage-029.py, build-029.py, diagnostics-029.py,
plain-logs-029.py, finish-029.py and check-029.py under checks. The final checker
prints its scope and results in logs/check-029.txt.
