# ROADMAP — FLT7 Kummer × GN

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Status: **001 B accepted; 002 A accepted; 003 authorized; subsequent gates pending**.

| Gate | Objective | Status |
|---|---|---|
| 000 | Branch and minimal instructions | Complete |
| 001 | 17-row source/theorem match; locate true missing construction | **Accepted B** |
| 002 | G1 CM phase, G2 real-unit seventh power, G3 concrete unit lemma | **Accepted A** |
| 003 | Ensure normal CI reachability; GN7 / cyclotomic norm / uniformizer bridge and true new obstruction audit | **Authorized** |
| 004 | Design same-source enlarged state retaining GN-ledger and ramifier valuation, or exact obstruction | Pending new instruction |
| 005 | Strict successor construction or principled blocker | Pending |
| 006 | Independent endpoint and non-circular dependency audit | Pending |

Gate 003 is defined in [instruction-003.md](instruction-003.md); do not
continue autonomously to Gate 004. The previous “principalization + chosen
factor integration” Gate 003 plan was redundant: those results are already
proven in the existing chosen packet.

### Lean trust

- GitHub `Deskuma/dkmath` is canonical; run from `lean/dk_math`.
- Keep source/test imports appropriately wired so that ordinary CI targets
  genuinely compile newly introduced theorems.
- Kernel-check required theorems; use `#print axioms` locally and ensure no
  `sorryAx` or nonstandard axiom dependencies in new public results.
- **No persisted build output, evidence logs, transcript dumps, copied
  dependencies or temporary reference files.** Keep concise theorem-level
  reports only, with stable source references.
- No fixed `LEAN_NUM_THREADS`; build strategy belongs to the runtime.
- No external finished FLT endpoints, invented descent witness,
  vacuous `True` specs, or automatic upgrade of research-only theorems
  to `DkMath.Lib`.
