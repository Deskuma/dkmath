# Merge preparation: reproducible evidence-log archive for PR #113

**Scope: archival / merge hygiene only.** Do not reopen research Instruction 052, change any Lean theorem, refactor project sources, alter the mathematical claims in reports, or merge this PR.

## Context and objective

PR #113 targets `develop` from `research/GapFocusing-ExponentGauge-Ultra-261004-v0`.
The research is frozen at Instruction 051 (Outcome C), with 001-051 reports and `JOURNEY-001-051.md`.

The PR currently contains 1,364 changed files, including 753 files under this checkpoint directory's `logs/`. It has over two million added lines, largely from diagnostics, old validation evidence, and generated artifacts. These are retained audit records, not actively edited sources.

**Objective:** replace the already-tracked plain-text evidence files under `logs/` with reproducible, integrity-checked compressed binary archives, while keeping the full evidence recoverable and all surviving relative links and check scripts usable after deliberate restoration. Reduce the permanent diff for `develop` without discarding any original bytes.

All paths below are relative to:
`lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/`.

## Guardrails: inspect before changing anything

1. Confirm clean or understood local working tree, correct source branch, and PR #113 base `develop`. Record HEAD and a baseline count/byte total of tracked `logs/**`. Do not touch unrelated changes.
2. Inventory every tracked file under `logs/`, including subdirectories and unusual extensions. Search all `checks/*.py`, Markdown files, GitHub Actions configs, and other scripts for `logs/` references. Specifically audit `checks/check-050.py` and `checks/check-051.py`: they use literal `logs/coverage-050.json`, `logs/axiom-audit-050.txt`, `logs/*-050.txt`, `logs/source-audit-051.json`, etc.
3. Note which reports link directly to logs. A compressed file alone cannot satisfy such links; prepare an archive index or corresponding *minimal* link updates. Never leave links silently broken.
4. Confirm whether existing checks are snapshot-bound to old Git commit fingerprints or expected filenames; distinguish a real validation failure from an intentionally archived resource that has not yet been restored.

## Archive layout

Keep in Git as ordinary reviewable text:
- all `DkMath/**/*.lean`, `DkMathTest/**/*.lean`, facade files;
- `instruction-*.md`, `report-*.md`, `JOURNEY-001-051.md`, source inventories, findings, validations and README;
- `checks/*.py` and any other verification source code;
- a brief human-readable `evidence/README.md`, `evidence/MANIFEST.md`, machine-readable `evidence/manifest.json`, and `evidence/SHA256SUMS`.

Store the original tracked evidence bytes in `evidence/*.tar.gz`.
Prefer ten-checkpoint groups such as `evidence/logs-001-010.tar.gz` through `logs-041-050.tar.gz`, plus `logs-051-and-misc.tar.gz`; derive membership from actual filenames rather than assuming all names are numbered. Ensure every original tracked log occurs **exactly once** in an archive. For unnumbered or ambiguous names, give them an explicit misc group and record their assignment.

Archives must restore original paths under `logs/`, not flatten basenames. Preserve content bytes exactly; do not regenerate older logs from newer builds, reformat JSON, normalize CRLF, discard duplicates, or substitute synthesized summaries. Remove tracked originals only **after** full byte-for-byte archive validation.

If a proposed archive approaches 50 MiB, split into deterministic numbered shards and write those shard memberships into the manifest. Stay comfortably below GitHub's 100 MiB hard file limit; fail rather than committing oversized blobs. Do not introduce Git LFS unless separately authorized.

## Reproducibility and integrity

Implement a small maintainable Python standard-library tool in `checks/archive_evidence.py` with documented modes to create, inspect/verify, and restore the archives (the precise CLI is up to you).

- Sort input names lexicographically. Normalize archive entry metadata (stable timestamps, owners, mode, gzip header mtime) so the same bytes and manifest reproduce the same `.tar.gz` checksum on the same Python toolchain.
- Manifest: for each original file record relative `logs/...` path, byte length, SHA-256, archive/shard name; for each archive record compressed byte length and SHA-256. Include inventory totals and archive format/tool version.
- Verification must inspect *every archive member*, detect missing/extra/duplicate members, compare content SHA-256 and byte lengths, and compare archive checksums. Check that restoring reproduces the original path tree and its exact bytes.
- Extraction must reject unsafe tar entries (absolute paths, `..` traversal, symlinks/hardlinks, devices, duplicate members) and never overwrite a different existing file without an explicit opt-in. An untrusted tar must never be blindly extracted by a convenience command.
- Treat checksum manifests as audit evidence, not cryptographic signing. A manifest in the same commit detects corruption/missing files; it does not authenticate an adversarially rewritten commit.

Use a temporary isolated directory or worktree for round-trip testing. Preserve the working .lake build environment and avoid creating thousands of untracked files in the main checkout after packing.

## References and verification compatibility

Old `checks/check-NNN.py` scripts assume `logs/*` exists. Retain their original semantics where possible; do not modify old test assertions merely to make the archive pass.

Provide a clear one-command restoration workflow that reconstitutes `logs/` *before* calling the existing checks. If a thin wrapper like `checks/restore_and_verify_evidence.py` is useful, implement it without masking check failures. Keep `logs/README.md` as a small pointer if that directory needs to exist in the committed tree.

Audit relative Markdown links. Prefer pointing archive-only evidence links to a per-file index entry identifying the exact archive and restoration command. Avoid mass rewriting narrative prose. The index should make it possible to answer: "Where did logs/root-050.txt go?" without extracting everything.

Verify post-restore at least:
- all original tracked log files exactly reconstructed against the pre-pack manifest;
- `python3 checks/check-050.py` and `python3 checks/check-051.py` from a suitable restored checkout, with results honestly classified (source-bound scripts may need restored HEAD context);
- representative check scripts from earlier checkpoint ranges, selecting ones that can validly be replayed on current source;
- any CI workflow that currently reads the raw logs, or adjust the workflow to restore first (do not remove tests).

If a historical `check-NNN.py` fails for genuine old-snapshot reasons even with intact logs, document that explicitly; do not silently weaken it.

## Git procedure

- Do not force-push or rewrite existing research commits without separate approval.
- Do not use `git rm` until archives, manifests, and extraction have passed complete round-trip verification in a temporary location.
- After validation, stage archive blobs + manifest/index/tools + removal of archived tracked logs + minimal documentation reference fixes; check for accidental source/Lean changes.
- Run `git diff --check` and confirm 051 report/source/Lean files are otherwise unmodified.
- Commit this as a separate merge-prep archival commit on the feature branch so PR #113 updates automatically.
- Do not merge PR #113; do not mark it ready for review until CI and evidence inspection pass.
- A later *squash merge*, if chosen by the reviewer, will keep raw evidence commits out of the ordinary `develop` first-parent history. It does not immediately erase the feature branch/PR's old Git objects.

## Required delivery: merge preparation report

Create `MERGE-PREP-EVIDENCE-ARCHIVE-REPORT.md` beside this instruction. Include:
- HEAD before and after; exact counts and total uncompressed/compressed bytes;
- archive names, SHA-256, number of original files per archive, and path-index location;
- proof of 100% byte-preserving round-trip;
- verification of links and working/archived check scripts;
- results of available CI/Lean builds; distinguish reused build logs from freshly executed builds;
- changed/removed files inventory and whether any direct log links remain;
- PR changed-file/line delta before vs after, if available;
- any errors, limitations, or follow-up needed for merger;
- explicit statement that FLT7/Legendre research conclusions remain unchanged.

**Outcome success:** every tracked evidence file is recoverable byte-for-byte and verifiably indexed, CI and supported audit replay work after restoration, PR diff is substantially reduced, and the PR remains an unmerged Draft.
