# Evidence policy

This directory contains **small, durable, decision-relevant evidence**:
exact theorem names/statements, axiom audit excerpts, source or commit
provenance, reproducible validation command *descriptions* and exit
statuses, and minimal counterexamples that distinguish valid/invalid
generalizations.

`logs/` is temporary and ignored by Git. Raw build logs, failed tactic
transcripts, large generated traces, and repeated command output should
remain disposable. Summarize conclusions in the report; retain only
the shortest decisive excerpts here when needed for later independent
review.

Evidence must label its origin (`Codex-reported` vs `independently
reproduced`), and must not call a Python calculation a Lean proof.
Never claim a theorem is kernel-checked solely from source-index output.
