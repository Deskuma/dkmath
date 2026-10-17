#!/usr/bin/env python3
"""Back up a Git worktree's local files in three searchable tar.gz archives.

Requires Python 3.9+ and Git. Does not modify the source worktree.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shlex
import stat
import subprocess
import sys
import tarfile


def git(root: Path, *args: str, output=None) -> bytes:
    cmd = ["git", "-C", str(root), *args]
    if output is None:
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode:
            raise RuntimeError(
                f"git failed: {' '.join(args)}\n{result.stderr.decode(errors='replace')}"
            )
        return result.stdout
    result = subprocess.run(cmd, stdout=output, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(
            f"git failed: {' '.join(args)}\n{result.stderr.decode(errors='replace')}"
        )
    return b""


def paths(root: Path, *args: str) -> set[str]:
    raw = git(root, *args, "-z")
    return {os.fsdecode(x) for x in raw.split(b"\0") if x}


def displayed(path: str) -> str:
    # Human-greppable, one entry per line even if file names include newline.
    # Escape control chars and backslashes; keep Japanese/Unicode readable.
    return json.dumps(path, ensure_ascii=False)[1:-1]


def text_list(dest: Path, names) -> None:
    with dest.open("w", encoding="utf-8", errors="backslashreplace") as out:
        for name in sorted(names):
            out.write(displayed(name) + "\n")


def categories(root: Path) -> tuple[dict[str, set[str]], set[str]]:
    # git diff --cached covers staged-only edits; git diff covers unstaged edits.
    # --no-renames ensures that a moved file's new path is archived.
    diffopts = (
        "--no-ext-diff",
        "--no-textconv",
        "--no-renames",
        "--name-only",
        "--diff-filter=ACMRTUXB",
    )
    changed = (
        paths(root, "ls-files", "--modified")
        | paths(root, "diff", *diffopts)
        | paths(root, "diff", "--cached", *diffopts)
    )
    untracked = paths(root, "ls-files", "--others", "--exclude-standard")
    ignored = paths(root, "ls-files", "--others", "--ignored", "--exclude-standard")
    deleted = paths(root, "ls-files", "--deleted") | paths(
        root, "diff", "--cached", "--no-renames", "--name-only", "--diff-filter=D"
    )
    return {
        "tracked-changed": changed,
        "untracked": untracked,
        "ignored": ignored,
    }, deleted


def is_excluded(name: str, patterns: list[str]) -> bool:
    clean = name.rstrip("/")
    return any(
        fnmatch.fnmatchcase(clean, pat) or pat in clean.split("/") for pat in patterns
    )


def expanded_inputs(root: Path, candidates: set[str]) -> list[str]:
    """Omit vanished files, dedupe entries beneath Git-reported directories."""
    ordered = sorted(
        (p.rstrip("/") for p in candidates), key=lambda p: (p.count("/"), p)
    )
    included: list[str] = []
    parents: list[str] = []
    for name in ordered:
        if name.startswith("/") or ".." in name.split("/") or name in ("", "."):
            raise RuntimeError(f"Unexpected git path: {name!r}")
        if any(name.startswith(d + "/") for d in parents):
            continue
        source = root / name
        if not os.path.lexists(source):
            continue
        included.append(name)
        # Git sometimes reports a nested repository as a single directory.
        if source.is_dir() and not source.is_symlink():
            parents.append(name)
    return included


def archive_one(root: Path, dest: Path, label: str, candidates: set[str]) -> dict:
    archive_file = dest / f"{label}.tar.gz"
    chosen = expanded_inputs(root, candidates)
    with tarfile.open(
        archive_file, mode="w:gz", format=tarfile.PAX_FORMAT, dereference=False
    ) as arc:
        for name in chosen:
            src = root / name
            if stat.S_ISSOCK(src.lstat().st_mode):
                raise RuntimeError(f"Unix socket cannot be archived: {name!r}")
            # recursive=True is intentional for directories containing nested repos.
            arc.add(str(src), arcname=name, recursive=True)
        written = [m.name for m in arc.getmembers()]
    text_list(dest / f"{label}.list.txt", written)
    # Read the entire archive, including file payloads, to detect gzip/tar damage.
    with tarfile.open(archive_file, mode="r:gz") as arc:
        members = arc.getmembers()
        verified = [m.name for m in members]
        if verified != written:
            raise RuntimeError(f"Archive index mismatch: {archive_file}")
        for m in members:
            if m.isfile():
                reader = arc.extractfile(m)
                if reader is None:
                    raise RuntimeError(f"Could not read member {m.name!r}")
                with reader:
                    while reader.read(1024 * 1024):
                        pass
    return {
        "archive": archive_file.name,
        "index": f"{label}.list.txt",
        "git_entries": len(chosen),
        "archive_members": len(written),
        "archive_bytes": archive_file.stat().st_size,
    }


def write_file_from_git(root: Path, dest: Path, filename: str, *args: str) -> None:
    with (dest / filename).open("wb") as out:
        git(root, *args, output=out)


def write_checksums(dest: Path) -> None:
    with (dest / "SHA256SUMS").open("w", encoding="utf-8") as out:
        for file in sorted(dest.iterdir()):
            if not file.is_file() or file.name == "SHA256SUMS":
                continue
            h = hashlib.sha256()
            with file.open("rb") as src:
                for chunk in iter(lambda: src.read(1024 * 1024), b""):
                    h.update(chunk)
            out.write(f"{h.hexdigest()}  {file.name}\n")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Archive tracked changes, untracked files, and ignored files separately."
    )
    parser.add_argument(
        "-o",
        "--output",
        default="~/workspace-rescue",
        help="Destination base (default: ~/workspace-rescue)",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="PATTERN",
        help="Optional filename/path pattern; repeated uses allowed (DANGEROUS: skips files)",
    )
    parser.add_argument(
        "--allow-submodules",
        action="store_true",
        help="Continue despite submodules (their own Git state is NOT fully backed up)",
    )
    parser.add_argument(
        "--no-bundle",
        action="store_true",
        help="Skip git bundle (not safe for local-only Git commits/stashes)",
    )
    args = parser.parse_args()
    os.umask(0o077)

    try:
        top = (
            subprocess.run(
                ["git", "rev-parse", "--show-toplevel"], check=True, capture_output=True
            )
            .stdout.decode(errors="surrogateescape")
            .strip()
        )
    except subprocess.CalledProcessError:
        parser.error("Run this command inside a non-bare Git worktree.")
    root = Path(top).resolve()
    base = Path(args.output).expanduser().resolve()
    if os.path.commonpath([str(root), str(base)]) == str(root):
        parser.error("The output destination must be OUTSIDE the source worktree.")

    # A top-level bundle cannot preserve submodule commits; refuse by default.
    index_records = git(root, "ls-files", "--stage", "-z").split(b"\0")
    submodules = []
    for rec in index_records:
        if rec.startswith(b"160000 ") and b"\t" in rec:
            submodules.append(os.fsdecode(rec.split(b"\t", 1)[1]))
    if submodules and not args.allow_submodules:
        print(
            "ERROR: Submodules found: "
            + ", ".join(map(displayed, submodules))
            + ". Back them up separately, then retry with --allow-submodules.",
            file=sys.stderr,
        )
        return 2

    now = dt.datetime.now().astimezone()
    stamp = now.strftime("%Y%m%d-%H%M%S-%f%z")
    project_parent = base / root.name
    unfinished = project_parent / (stamp + ".incomplete")
    finished = project_parent / stamp
    unfinished.mkdir(parents=True, exist_ok=False)
    print(f"Source: {root}", flush=True)
    print(f"Backup in progress: {unfinished}", flush=True)
    try:
        groups, deleted = categories(root)
        exclusions = set()
        for key in groups:
            omitted = {name for name in groups[key] if is_excluded(name, args.exclude)}
            exclusions.update(omitted)
            groups[key] -= omitted
        text_list(unfinished / "excluded.list.txt", exclusions)
        text_list(unfinished / "tracked-deleted.list.txt", deleted)
        result = {}
        for key in ("tracked-changed", "untracked", "ignored"):
            print(f"Archiving {key}: {len(groups[key])} Git entries", flush=True)
            result[key] = archive_one(root, unfinished, key, groups[key])

        write_file_from_git(
            root,
            unfinished,
            "staged.patch",
            "diff",
            "--cached",
            "--binary",
            "--no-ext-diff",
            "--no-textconv",
            "--no-renames",
        )
        write_file_from_git(
            root,
            unfinished,
            "unstaged.patch",
            "diff",
            "--binary",
            "--no-ext-diff",
            "--no-textconv",
            "--no-renames",
        )
        write_file_from_git(
            root,
            unfinished,
            "git-status.txt",
            "status",
            "--short",
            "--untracked-files=all",
        )
        write_file_from_git(root, unfinished, "git-stashes.txt", "stash", "list")

        bundle_status = "disabled with --no-bundle"
        if not args.no_bundle:
            # --all preserves local branch/tag/remote refs and reachable stash objects.
            refs = git(root, "for-each-ref", "--format=%(refname)").strip()
            if refs:
                bundle_path = unfinished / "repository.bundle"
                print(
                    "Saving Git refs, commits and stashes in repository.bundle",
                    flush=True,
                )
                git(root, "bundle", "create", str(bundle_path), "--all")
                check = subprocess.run(
                    ["git", "-C", str(root), "bundle", "verify", str(bundle_path)],
                    capture_output=True,
                )
                (unfinished / "bundle-verify.txt").write_bytes(
                    check.stdout + check.stderr
                )
                if check.returncode:
                    raise RuntimeError("Git bundle verify failed")
                bundle_status = "created and verified"
            else:
                bundle_status = "no refs yet (empty/unborn repository)"
        # Detect newly created/removed categories during backup. Content edits
        # without path changes still require the worktree to be quiescent.
        after, after_deleted = categories(root)
        if (
            any(
                (after[k] - {p for p in after[k] if is_excluded(p, args.exclude)})
                != groups[k]
                for k in groups
            )
            or after_deleted != deleted
        ):
            raise RuntimeError(
                "Git path lists changed during backup; retry with a quiet worktree"
            )

        head = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True
        )
        info = {
            "created_at": now.isoformat(),
            "source_root": str(root),
            "git_head": head.stdout.decode().strip() if head.returncode == 0 else None,
            "git_branch": git(root, "branch", "--show-current")
            .decode(errors="replace")
            .strip(),
            "categories": result,
            "deleted_tracked_paths": len(deleted),
            "excluded_git_entries": len(exclusions),
            "exclusions": args.exclude,
            "bundle": bundle_status,
            "submodules": submodules,
        }
        (unfinished / "backup-info.json").write_text(
            json.dumps(info, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        (unfinished / "README.txt").write_text(
            f"Git ワークスペース救出バックアップ\n対象: {root}\n作成: {now.isoformat()}\n\n"
            "■ 3種類のアーカイブと同名の一覧\n"
            "tracked-changed.tar.gz / .list.txt : 追跡中で変更されたファイル（現在の実体）\n"
            "untracked.tar.gz / .list.txt      : ignore されていない未追跡ファイル\n"
            "ignored.tar.gz / .list.txt        : .gitignore 等により無視されたファイル\n"
            "一覧はアーカイブ内の実際のパスを収録。改行等をエスケープして1行1件。\n\n"
            "検索: grep -nF '探す語' *.list.txt\n"
            "一覧: tar -tzf ignored.tar.gz\n"
            "復元: mkdir -p restored && tar -xzf ignored.tar.gz -C restored\n"
            "整合性検査: sha256sum -c SHA256SUMS\n\n"
            "■ その他\n"
            "staged.patch / unstaged.patch : ステージ済み／未ステージのGit差分\n"
            "tracked-deleted.list.txt      : 削除された追跡対象パス（実体は収録不可）\n"
            "repository.bundle             : ブランチ・タグ・stash等の到達可能なGitオブジェクト\n"
            "git-status.txt / git-stashes.txt / backup-info.json : 監査情報\n"
            "excluded.list.txt             : --exclude による除外対象\n\n"
            "【重要な制限】\n"
            "Git bundleは .git 設定、reflogからしか辿れないコミット、到達不能な\n"
            "オブジェクト、サブモジュール側の履歴まで完全に保護しません。\n"
            "外部を指すシンボリックリンクの参照先、空の未追跡ディレクトリ、\n"
            "ACLや拡張属性も完全には保護しません。稼働中の同時書き込みに対して\n"
            "原子的スナップショットを保証するものではありません。\n"
            "Git列挙では表に出ない未追跡ディレクトリ等があり得るため、\n"
            "削除前に元ワークスペースと回収結果を実際に突き合わせてください。\n"
            "元の作業ツリーは本ツールによって削除・復元されません。\n"
            "重要な私的メモの復元テストを済ませるまで元環境を消さないこと。\n",
            encoding="utf-8",
        )
        write_checksums(unfinished)
        unfinished.rename(finished)
        print(f"SUCCESS: {finished}")
        print(f"Verify: cd {shlex.quote(str(finished))} && sha256sum -c SHA256SUMS")
        return 0
    except (OSError, RuntimeError, tarfile.TarError) as exc:
        print(
            f"FAILED: {exc}\nINCOMPLETE data retained at: {unfinished}", file=sys.stderr
        )
        return 1


if __name__ == "__main__":
    sys.exit(main())
