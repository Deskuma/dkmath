# FLT7 Complete-Support Ultra Research — 2026-10-04

Branch: **research/FLT7-CompleteSupport-Ultra-261004-v0**

Base: **develop** at **82dd73bed85ff6c75fa1a8318ebafb08e7faab21**

## Purpose

This research checkpoint attacks the exact FLT7 frontier left by DRC-008:

```lean
∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
  7 ∣ exponent (carrierIdeal c) v
```

for a fixed current phase-corrected degree-six carrier.

The selected current oriented prime already has exact exponent `14e`.
The unresolved issue is the complementary complete support.

The goal is not to force FLT7 closure. The goal is to determine, with the
strongest available reasoning and repository-wide audit, whether the current
stack already controls all complementary support, and if not, to isolate the
smallest genuine missing theorem.

## Operating rule

This run is intentionally **checkpoint-heavy**.

Do not keep important discoveries only in chat/session memory.

Use:

- `instruction-001.md` — research task and safety boundaries;
- `findings-001.md` — durable incremental research log;
- `report-001.md` — final synthesis only if/when the run reaches a stable end.

The incremental findings log is mandatory and should be updated throughout the
run, before large builds and before moving between major proof routes.

If the model/session limit is reached, `findings-001.md` must still contain
enough information for another session to continue without repeating the whole
audit.
