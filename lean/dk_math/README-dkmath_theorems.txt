DkMath 2026-10-12 snapshot search toolkit
========================================
Snapshot sha256: a9b6938f2e8fee26b261c673926259cf58bf0e917c66bcebdd82a818992d1b1f

Files:
- dkmath_theorems.py             Python 3 / SQLite theorem source finder
- dkmath-theorems.sqlite3        Indexed source data from this exact snapshot
- create-dkmath-all-lean.sh      Standalone, deterministic replacement

Install by copying the Python script (and optionally the shell script) to your
local dk_math repository root. Python 3 + sqlite3 is enough for searching.

Examples from repository root:
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 stats
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search focused_gap
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search --name selectedBody_transport --full
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search --module FLT.Seven --kind theorem reconstruction
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 show seven_dvd_focused_gap
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 export theorem-catalog.jsonl
  bash create-dkmath-all-lean.sh --root . --output ./logs/all-dkmath.lean.txt.gz

Quick offline use with the bundled database:
  python3 dkmath_theorems.py --db dkmath-theorems.sqlite3 search GTail

Limitations:
* Source-based scan, not Lean parser/elaborator; declaration extraction and
  namespace qualification are heuristic. It may miss attributes/syntax
  and misinterpret unusual Lean constructs.
* A declaration in the index is NOT evidence that the relevant theorem is
  axiom-free, free of sorry, inhabited, or usable under intended premises.
* Not a substitute for `lake env lean`, `#check`, `#print axioms`, or a build.
* No imports from Mathlib are enumerated in this index: only local DkMath.
* Snapshot is detached; no branch/build provenance was independently verified.

Fast token-prefix lookup (SQLite FTS5):
  python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search focused --fts

The bundled SQLite file can be searched immediately without unpacking the
entire DkMath source tree, but its source excerpts do not contain full proofs.
Use the matching checked-out source or the aggregated .lean.txt.gz for context.
