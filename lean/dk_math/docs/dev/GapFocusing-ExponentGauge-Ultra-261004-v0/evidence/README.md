# Recoverable evidence archive

The 753 tracked evidence files present at the archive baseline are preserved
byte-for-byte in six `tar.gz` archives. [MANIFEST.md](MANIFEST.md) indexes
every original path, its archive, length and SHA-256.
[manifest.json](manifest.json) is the machine-readable inventory;
[SHA256SUMS](SHA256SUMS) records archive checksums.

Run these commands **from this checkpoint directory**:

```sh
# Inspect and verify every archive member without restoring files.
python3 checks/archive_evidence.py inspect

# One-command restoration to the original logs/... paths.
python3 checks/archive_evidence.py restore

# Confirm that the restored files match the archived bytes.
python3 checks/archive_evidence.py verify --originals .

# Replay supported checks only after restoration. Failures are not suppressed.
python3 checks/check-050.py && python3 checks/check-051.py
```

Restoration first checks every archive and member, then preflights every
destination. Absolute/traversal paths, links, devices, extra/duplicate/missing
members and different existing files are rejected. Matching existing files
are left alone. `--overwrite` explicitly permits replacement of differing
regular files; it never permits unsafe paths or symbolic links.

For an isolated recovery, `restore --dest /tmp/my-checkpoint` creates only
the original `logs/` path tree there. To replay the historical scripts, use
a complete checkout, copy this evidence directory into its checkpoint, and
restore there. Scripts derive their source root from their own location;
an isolated logs directory alone is not a source checkout. Some checks read
local Mathlib sources from `.lake/packages/mathlib`, so that dependency
environment must also be available. Restoration does not touch `.lake`.

Historical checks are intentionally unchanged. They may be bound to old
source hashes, declaration inventories, facade counts or report formatting.
A restored log does not make an incompatible newer source snapshot pass.
Missing archived resources must first be restored; assertion failures after
restoration must be investigated separately. The merge preparation report
lists the checks replayed and their actual results.

Some checks, notably `check-051.py`, **write** audit outputs under `logs/`.
Run byte-integrity verification before replay. To recover original evidence
after a replay changes outputs, restore with `--overwrite` in an isolated
checkout. Such generated outputs are new validation results, not replacements
for the archived original evidence. Restored files in the working checkout
are ignored by Git; the archive manifest, not directory enumeration, defines
the preserved inventory.

To reproduce archives on the same Python/zlib toolchain, first restore the
original bytes, then write to an empty output directory:

```sh
python3 checks/archive_evidence.py create --source . \
  --from-manifest evidence/manifest.json --evidence /tmp/reproduced-evidence
```

Input paths and members are sorted. Tar metadata uses mode 0644, zero
timestamps/UID/GID and empty owner names. Gzip uses level 9, an empty filename
and zero header time. The manifest records Python and zlib versions. Archive
outputs at or above 45 MiB are deterministically split by sorted membership;
a single oversized member or unreproducible existing shard fails instead.
All six archives in this inventory are below 16 MiB; no sharding or Git LFS
was necessary.

Checksums detect corruption and missing bytes relative to this inventory.
The manifest and archives in the same commit are **not cryptographic signing**
and do not authenticate an adversarially rewritten commit.

The Lean CI workflow builds the project and does not read these raw logs;
no CI test was removed or changed. Earlier stored Lean build logs remain
historical evidence. Archive verification and Python check replay are not
fresh Lean compilations. FLT7 and Legendre research conclusions are unchanged.
