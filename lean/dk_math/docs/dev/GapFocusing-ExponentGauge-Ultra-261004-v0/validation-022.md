# Validation 022

All required validation processes completed successfully with LEAN_NUM_THREADS=2
for the final and large builds. No memory fault occurred. Scope is the exact
production and calibration modules listed below; axiom checks are declaration
specific, rather than an audit of every declaration imported by the root.

## Checked implementation surface

- Production: FinsetSupportPacking, CoarseTownSurvivorCapacity,
  CoarseTownDeletionConservation.
- New finite modules: LegendreConservationRegression,
  LegendreSurvivor297Calibration, LegendreSurvivor1031Calibration.
- Public audit module: LegendreConservationAxiomAudit.
- Preserved explicit endpoint: LegendreCapacity297Calibration.
- Rebuilt 021 prerequisites: LegendreDeletion1031Data,
  LegendreDeletion1031Calibration, LegendreFullTownRegression.
- Facade imports the two new production modules only after focused success.

## Build evidence

| Target | Status | Elapsed seconds | Peak RSS KiB | Evidence |
| --- | --- | ---: | ---: | --- |
| Final focused module set | PASS | 31.41 | 7300380 | logs/focused-022.txt |
| Legendre facade | PASS | 13.02 | 6712968 | logs/facade-022.txt |
| DkMath root | PASS | 13.93 | 7062268 | logs/root-022.txt |
| Public axiom audit | PASS | 13.50 | 6723256 | logs/axiom-audit-022.txt |
| Initial 1031 prerequisites | PASS | 169.63 | 18220928 | logs/build-022-1031-prerequisites.txt |
| New 1031 calibration | PASS | 39.73 | 7912680 | logs/build-022-1031.txt |
| Initial successful 297 and small anchors | PASS | 30.78 | 7441552 | logs/build-022-297.txt |

The five existing root sorry warnings remain at ZsigmondyCyclotomicResearch,
TriominoCosmicBranchA, GcdNextResearch, TriominoFLT and
CyclotomicPrincipalization. Existing PacketCross has an unused hrs warning.
No new implementation declaration uses sorry, admit, axiom, native_decide,
unsafe or implemented_by.

## Complete public declaration coverage

The generated manifest logs/declaration-coverage-022.json covers 125 public
declarations, each checked by both check and print axioms:

- 22 neutral declarations: 1 new capacity theorem and 21 retained packing APIs.
- 17 survivor-capacity declarations, all new.
- 43 conservation declarations, all new.
- 20 small regression declarations, all new.
- 14 n=297 calibration declarations, all new.
- 7 n=1031 calibration declarations, all new.
- 2 retained endpoints: explicit n=297 and original old-world n=1031.

Every audited dependency set is contained in propext, Classical.choice and
Quot.sound. There is no sorryAx dependency or computational trust extension.
Finite carrier equality and divisibility checks use decide +kernel. Named
endpoints consume production capacity and existing Frontier arithmetic, with
no tested prime witness supplied by diagnostics.

## Mathematical and artifact checks

checks/check-022.py verifies complete axiom manifest coverage, exact standard
headers and file print markers, forbidden tokens, neutral import direction,
and git diff --check including untracked Lean files. It independently rebuilds
the 602-row worlds through oriented edges, rather than trusting the discovery
fiber union, and verifies support, activity, uncovered seats, incidence,
multiplicity, both orientation ledgers, loss coordinates and threshold flags.
Mandatory anchors are present. The smallest false-equivalence example is
kernel-certified at n=1; a nonempty active world at n=5 is also certified.

The final report has all 17 answers and exactly the required Outcome A ending.
New findings, source inventory, report, validation and completed text logs
are ASCII with no backslash notation. checks/plain-logs-022.py normalizes
compiler display glyphs only after their writers have completed, preserving
declaration names, axiom names and success evidence. Discovery is diagnostic
and is never a theorem premise.

## Semantic judgment

The new deterministic n=297 endpoint and full conservation close Outcome A.
The additionally proved unconditional O<=X rejects the proposed uncovered-free
strict provider. The corrected exact loss frontier retains U; no universal
provider, optimal packing, wave independence or Legendre conjecture is proved.

Final independent checker result: PASS. Evidence:
[checks-022.txt](logs/checks-022.txt).
