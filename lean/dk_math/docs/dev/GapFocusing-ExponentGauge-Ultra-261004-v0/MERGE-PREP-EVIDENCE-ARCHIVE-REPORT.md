# Merge preparation - evidence archive report

## Result and scope

The 753 originally tracked evidence files are now retained in six
reproducible, integrity-checked binary archives. All 135,114,977 original
bytes were recovered in two isolated locations and compared literally
against the original working files. The compressed archives total
21,975,523 bytes, a reduction of 113,139,454 bytes (83.74%). The largest
archive is 16,683,111 bytes, below 16 MiB; no shards or Git LFS were needed.

The FLT7 Outcome C and Legendre research conclusions are unchanged.
No Lean source, theorem, facade, old verification script, or mathematical
report claim was changed. Existing Markdown edits change evidence link
URLs only, with a recovery pointer added to the checkpoint README.

Baseline HEAD: `fce6559a761c9cfc53ebb36114e00bd1cd926f06`.
HEAD after artifact creation and validation, before the archival commit:
`fce6559a761c9cfc53ebb36114e00bd1cd926f06` (no branch movement during those operations).
The separate archival commit is identified by subject
`docs: archive GapFocusing research evidence for merge preparation`.
Its immutable final HEAD is reported in the delivery message and can be
resolved with `git log -1 --format=%H --grep='archive GapFocusing research evidence'`.
A commit cannot embed its own resulting hash; this report avoids a fabricated
self-reference. Only the normal feature branch is updated; no history rewrite
or merge is part of this operation.

## Archives and path index

All paths in this table are under `evidence/`.
The complete per-file inventory is [MANIFEST.md](evidence/MANIFEST.md),
with [manifest.json](evidence/manifest.json) and
[SHA256SUMS](evidence/SHA256SUMS). Every original path appears exactly once.
Unnumbered files and checkpoint 051 are explicitly assigned to the misc
archive, with an assignment reason in each manifest entry.

| Archive | Original files | Compressed bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `logs-001-010.tar.gz` | 95 | 420,557 | `787d02a7065ebfc431de00c2e8e6ada762e517bbd6e1d7187f55f6d149fa2ab6` |
| `logs-011-020.tar.gz` | 131 | 1,839,724 | `340215e7b71eccc6bd47f35aa4136695669af2b66153b01fcd34af4c2bc88c21` |
| `logs-021-030.tar.gz` | 194 | 16,683,111 | `3a36b58d10160be2d63294dde143e8de480a9116985cc467e5ad231527a232ee` |
| `logs-031-040.tar.gz` | 171 | 2,376,776 | `0cf04ab9e39afe155062e8b660c00a896f3522645555ffa221cbb74ad37f35d4` |
| `logs-041-050.tar.gz` | 152 | 613,216 | `fde1849ededec56e8a182e1649f2279905b777d9db5bed77d2e13d5e6be4ae69` |
| `logs-051-and-misc.tar.gz` | 10 | 42,139 | `99840e1f0b8a627726a7d4aaabc063f5b7632e467ed084644e6f6ee29068d950` |

## Recovery, reproducibility and safety

From this checkpoint directory, one command restores the original path tree:

```sh
python3 checks/archive_evidence.py restore
```

[The recovery README](evidence/README.md) documents inspect, verify, restore,
and deterministic recreation from the manifest. Archive metadata and gzip
headers are normalized, paths sorted, and Python/zlib versions recorded.
All six recreated archives, the JSON manifest, SHA256SUMS and Markdown index
were compared byte-for-byte with the initial outputs on this toolchain.

Verification reads every archive member and checks missing, extra and duplicate
members, content lengths and SHA-256, archive lengths/checksums and totals.
The extraction tool does not use `extractall`: it rejects unsafe names,
links/devices, file/directory collisions and symlink destinations, and
preflights all existing-file conflicts before writing. Different existing
files require an explicit `--overwrite`; identical existing files are left
alone. Archive sizes at or above 45 MiB cause deterministic membership
splitting, or an error if an individual file cannot be split safely.

The extraction safety suite covers exact binary/CRLF bytes, idempotent
restoration, refused overwrites, explicit overwrites, traversal and absolute
paths, symbolic/hard links, devices, duplicate/extra/missing members,
content/archive corruption, file/directory collisions and destination
conflicts. It is run with `python3 checks/test_archive_evidence.py`.
Checksums authenticate neither a rewritten manifest nor an adversarial commit;
they are integrity evidence, not signatures.

Round-trip verification completed before `git rm` removed any original log.
The temporary directories were outside the checkout; `.lake` was preserved.
The full-source replay checkout used the existing dependency environment to
read Mathlib files. No thousands-file restoration was left in the main tree.
`logs/README.md` points to recovery and `logs/.gitignore` keeps deliberately
restored raw evidence out of subsequent accidental staging.

## References and historical check replay

The baseline scan covered every tracked log, Python check source, Markdown
file, GitHub Actions workflow, and other tracked Python/shell/JSON/TOML/YAML
scripts with checkpoint references. It found 237 reference-bearing text
files, all within the checkpoint: 345 direct archive-only evidence links in
79 Markdown documents. Those URLs now target the exact per-file index
entry, retaining their link labels and surrounding prose. No direct link
to an archived original remains in surviving tracked Markdown. The archive
index resolves each entry to its exact archive and a restoration command.
[archive-validation.json](evidence/archive-validation.json) retains the
baseline reference inventory and detailed replay output.

`check-050.py` still reads coverage, axiom, performance and source logs by
the original literal filenames. `check-051.py` retains its source-preservation
checks and report reference validation. No assertion was weakened.
The scripts below were executed in a restored full-source checkout:

| Check | Result | Classification |
| --- | --- | --- |
| 010 | PASS | Representative supported check from 001-010. An initial incomplete-document replay found a not-yet-created merge report link; the final complete-document replay passes all local links. |
| 019 | PASS | Representative supported check from 011-020. |
| 020 | FAIL | Historical source snapshot mismatch: archived declaration coverage contains 85 records; current source enumeration contains 104. Failure occurs at the exact coverage equality, line 37, with intact archived logs. |
| 030 | PASS | Representative supported check from 021-030. |
| 039 | PASS | Representative supported check from 031-040. |
| 040 | FAIL | Historical failed build evidence: original `performance-focused-040.json` has `exit_code=1`; original focused log records a kernel deterministic timeout and build failure. The success assertion at line 29 correctly rejects that evidence. This is not classified as archive corruption or silently converted to a passing log. |
| 050 | PASS | Current scope, source fingerprints, axiom evidence and stored build evidence verified after recovery. |
| 051 | PASS | Current source preservation and report references verified after recovery. |

These are Python audit replays, not fresh Lean builds. Some checks write
outputs into `logs/`; in particular, 051 rewrites its HEAD-bearing audit JSON.
Byte recovery was checked before running them. Afterwards the original log
bytes were restored again with explicit overwrite and reverified. The
archives were never regenerated from these new check outputs.
The 020 source difference and the 040 historical failure remain explicit
limitations for reviewers wishing to replay every old checkpoint on current
sources. Their original records are preserved without substitution.

## CI and merge status

At baseline PR #113 was OPEN, Draft, targeted `develop`, and used the current
feature branch. Its latest available Lean CI run was SUCCESS:
[Build DkMath](https://github.com/Deskuma/dkmath/actions/runs/37816121870/job/113445090441).
Both workflow files were inspected. Lean CI invokes the Lake project build;
the dependency-update workflow invokes Mathlib's update/build action.
Neither reads these checkpoint raw logs, so no workflow adjustment or test
removal was needed.

No fresh local Lean compilation was necessary for this source-preserving
archive change. Stored build logs are reused evidence only. CI for the new
archival commit, if available after publication, is reported separately in
the delivery; the baseline CI result is not presented as that new run.
PR #113 remains unmerged and Draft; it is not marked ready for review.

## Changed files and diff reduction

Removed tracked originals: exactly the 753 manifest-listed `logs/...` files,
including every original extension and path. Added: six archives, the
reviewable manifest/index/checksum/recovery documents, archival validation
record, two Python tools, this report, and the small logs pointer/ignore file.
Modified existing documents: 79 files with 345 URL replacements, plus the
checkpoint README recovery section. Old check scripts remain byte-identical;
all Lean files, source inventories' prose, and the 051 report's non-link
content remain unchanged.

Baseline PR diff: 1,365 files, 2,058,435 added text lines, 66 deleted lines.
The final prospective diff against the same local `origin/develop` base is
recorded in the validation JSON after staging; binary blobs have no text
line counts. The final published PR counters are checked separately.

Prospective counters: 628 files, 104,822 added text lines, 66 deleted lines and 6 binary archives.
Ordinary `develop` first-parent history can omit the raw evidence commits
if the reviewer later chooses a squash merge. This archive commit alone
does not erase the feature branch or PR's older Git objects.

Required checks: full archive verification, exact recovery, byte-identical
recreation, extraction safety suite, supported restored checks, link/index
validation, source/check-script preservation and `git diff --check`.
No research Instruction 052 work, new modular filter, mathematical change,
force-push, merge, or readiness change is included.
