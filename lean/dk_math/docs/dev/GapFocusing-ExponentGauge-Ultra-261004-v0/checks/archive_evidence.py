"""Deterministic, standard-library evidence archives. See evidence/README.md.

create inventories tracked logs (or reproduces --from-manifest); verify reads
every member; restore verifies first and rejects unsafe paths and conflicts.
No extractall, research regeneration, Git mutation, or network access is used.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
import tarfile
import tempfile
import zlib

BASE = Path(__file__).resolve().parent.parent
VERSION = 1
LIMIT = 45 * 1024 * 1024


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def safe_log(name):
    p = PurePosixPath(name)
    if (not isinstance(name, str) or p.is_absolute() or len(p.parts) < 2
            or p.parts[0] != 'logs' or '..' in p.parts or '\\' in name
            or str(p) != name):
        raise ValueError(f'Unsafe log path: {name!r}')
    return p


def safe_archive(name):
    if not re.fullmatch(r'logs-[a-z0-9-]+\.tar\.gz', name):
        raise ValueError(f'Unsafe archive name: {name!r}')
    return name


def target(root, name):
    p = safe_log(name)
    if root.is_symlink():
        raise ValueError(f'Symlink destination: {root}')
    current = root
    for component in p.parts:
        current = current / component
        if current.is_symlink():
            raise ValueError(f'Symlink destination: {current}')
    return current


def group(name):
    numbers = sorted({int(n) for n in re.findall(r'(?<!\d)(\d{3})(?!\d)',
                                                PurePosixPath(name).name)
                      if 1 <= int(n) <= 51})
    if len(numbers) == 1 and numbers[0] <= 50:
        start = ((numbers[0] - 1) // 10) * 10 + 1
        return f'{start:03d}-{start+9:03d}', f'checkpoint {numbers[0]:03d}'
    reason = ('checkpoint 051' if numbers == [51] else
              'unnumbered' if not numbers else f'ambiguous checkpoints {numbers}')
    return '051-and-misc', reason


def write_tar(path, files, source):
    with path.open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0,
                           compresslevel=9) as compressed:
            with tarfile.open(fileobj=compressed, mode='w', format=tarfile.PAX_FORMAT) as tar:
                for record in sorted(files, key=lambda f: f['path']):
                    original = target(source, record['path'])
                    if (not original.is_file() or original.stat().st_size != record['bytes']
                            or digest(original) != record['sha256']):
                        raise ValueError(f'Original changed: {original}')
                    info = tarfile.TarInfo(record['path'])
                    info.size = record['bytes']
                    info.mode, info.mtime, info.uid, info.gid = 0o644, 0, 0, 0
                    info.uname = info.gname = ''
                    with original.open('rb') as content:
                        tar.addfile(info, content)


def load(evidence):
    data = json.loads((evidence / 'manifest.json').read_text())
    if data['format_version'] != VERSION:
        raise ValueError('Unsupported manifest version')
    files, archives = {}, {}
    for record in data['files']:
        name = record['path']
        safe_log(name)
        if name in files:
            raise ValueError(f'Duplicate manifest file: {name}')
        files[name] = record
    for record in data['archives']:
        name = safe_archive(record['name'])
        if name in archives or record['bytes'] >= LIMIT:
            raise ValueError(f'Duplicate or oversized archive: {name}')
        archives[name] = record
    for record in files.values():
        if record['archive'] not in archives:
            raise ValueError(f'Unknown archive for {record["path"]}')
        if any(str(parent) in files for parent in PurePosixPath(record['path']).parents):
            raise ValueError(f'File used as a directory: {record["path"]}')
    if (data['totals']['files'] != len(files)
            or data['totals']['uncompressed_bytes'] != sum(f['bytes'] for f in files.values())
            or data['totals']['compressed_bytes'] != sum(a['bytes'] for a in archives.values())):
        raise ValueError('Incorrect manifest totals')
    return data, files, archives


def verify(evidence, originals=None):
    data, files, archives = load(evidence)
    if {p.name for p in evidence.glob('*.tar.gz')} != set(archives):
        raise ValueError('Extra or missing archive files')
    seen = set()
    for name, archive in archives.items():
        path = evidence / name
        if path.is_symlink() or path.stat().st_size != archive['bytes'] or digest(path) != archive['sha256']:
            raise ValueError(f'Archive checksum/length mismatch: {name}')
        count = 0
        with tarfile.open(path, 'r:gz') as tar:
            for member in tar:
                safe_log(member.name)
                if not member.isreg() or member.type not in (tarfile.REGTYPE, tarfile.AREGTYPE):
                    raise ValueError(f'Nonregular member: {member.name}')
                if member.name in seen or member.name not in files:
                    raise ValueError(f'Duplicate/extra member: {member.name}')
                record = files[member.name]
                if record['archive'] != name or member.size != record['bytes']:
                    raise ValueError(f'Wrong membership/length: {member.name}')
                with tar.extractfile(member) as content:
                    if hashlib.file_digest(content, 'sha256').hexdigest() != record['sha256']:
                        raise ValueError(f'Member checksum mismatch: {member.name}')
                seen.add(member.name)
                count += 1
        if count != archive['files']:
            raise ValueError(f'Archive file count mismatch: {name}')
    if seen != set(files):
        raise ValueError(f'Missing members: {set(files) - seen}')
    if originals is not None:
        for name, record in files.items():
            p = target(originals, name)
            if not p.is_file() or p.stat().st_size != record['bytes'] or digest(p) != record['sha256']:
                raise ValueError(f'Restored/original bytes differ: {name}')
    expected = ''.join(f'{a["sha256"]}  {a["name"]}\n' for a in data['archives'])
    if (evidence / 'SHA256SUMS').read_text() != expected:
        raise ValueError('SHA256SUMS differs from manifest')
    print(f'PASS: {len(files)} files, {len(archives)} archives; all members, lengths and SHA-256 checked.')
    return data


def restore(evidence, destination, overwrite):
    data = verify(evidence)
    files = {record['path']: record for record in data['files']}
    # Preflight every conflict before writing any file.
    for record in data['files']:
        p = target(destination, record['path'])
        for parent in p.parents:
            if parent == destination.parent:
                break
            if parent.exists() and not parent.is_dir():
                raise ValueError(f'Non-directory parent: {parent}')
        if p.exists() and (not p.is_file() or
                          (digest(p) != record['sha256'] and not overwrite)):
            raise ValueError(f'Existing different file (use --overwrite explicitly): {p}')
    seen = set()
    for archive in data['archives']:
        with tarfile.open(evidence / archive['name'], 'r:gz') as tar:
            for member in tar:
                p = target(destination, member.name)
                if (not member.isreg() or member.type not in (tarfile.REGTYPE, tarfile.AREGTYPE)
                        or member.name in seen or member.name not in files
                        or files[member.name]['archive'] != archive['name']):
                    raise ValueError(f'Archive changed or unsafe member: {member.name}')
                seen.add(member.name)
                if p.is_file() and digest(p) == files[member.name]['sha256']:
                    continue
                p.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as content:
                    fd, temporary = tempfile.mkstemp(prefix='.evidence-', dir=p.parent)
                    try:
                        with os.fdopen(fd, 'wb') as out:
                            while chunk := content.read(1024 * 1024):
                                out.write(chunk)
                        if (Path(temporary).stat().st_size != files[member.name]['bytes']
                                or digest(Path(temporary)) != files[member.name]['sha256']):
                            raise ValueError(f'Archive content changed during restoration: {member.name}')
                        os.chmod(temporary, 0o644)
                        os.replace(temporary, p)
                    finally:
                        Path(temporary).unlink(missing_ok=True)
    verify(evidence, destination)


def create(source, evidence, from_manifest):
    if from_manifest:
        data = json.loads(from_manifest.read_text())
        records = data['files']
        # Reproduction uses the original inventory and toolchain metadata.
    else:
        gitroot = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=source).decode().strip())
        prefix = str(source.relative_to(gitroot)) + '/'
        names = subprocess.check_output(['git', 'ls-files', '-z', prefix + 'logs/'], cwd=gitroot).decode().split('\0')[:-1]
        records = []
        for name in sorted(names):
            relative = name.removeprefix(prefix)
            p = target(source, relative)
            grouping, reason = group(relative)
            if not p.is_file():
                raise ValueError(f'Not a regular original: {p}')
            records.append({'path': relative, 'bytes': p.stat().st_size,
                            'sha256': digest(p), 'group': grouping, 'assignment': reason})
        if not records:
            raise ValueError('No tracked logs; use --from-manifest after restoration')
        data = {'format_version': VERSION, 'tool': 'archive_evidence.py v1',
                'archive_format': 'PAX tar + gzip level 9; sorted paths; uid/gid/mtime=0; mode=0644; empty owner names and gzip filename',
                'toolchain': {'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION},
                'source_HEAD': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source).decode().strip()}
    evidence.mkdir(parents=True, exist_ok=True)
    if any(evidence.glob('*.tar.gz')):
        raise ValueError('Output already contains archives; choose an empty output directory')
    archives = []
    if from_manifest:
        groups = [(a['name'], [f for f in records if f['archive'] == a['name']]) for a in data['archives']]
    else:
        groups = [(f'logs-{g}.tar.gz', [f for f in records if f['group'] == g])
                  for g in sorted({f['group'] for f in records})]

    def pack(name, members):
        safe_archive(name)
        path = evidence / name
        write_tar(path, members, source)
        if path.stat().st_size >= LIMIT:
            path.unlink()
            if from_manifest or len(members) == 1:
                raise ValueError('Archive exceeds 45 MiB; cannot reproduce/split a single file')
            middle = len(members) // 2
            stem = name.removesuffix('.tar.gz')
            pack(stem + '-part-01.tar.gz', members[:middle])
            pack(stem + '-part-02.tar.gz', members[middle:])
            return
        for member in members:
            member['archive'] = name
        archives.append({'name': name, 'bytes': path.stat().st_size,
                         'sha256': digest(path), 'files': len(members)})

    for name, members in groups:
        pack(name, sorted(members, key=lambda f: f['path']))
    data['files'] = sorted(records, key=lambda f: f['path'])
    data['archives'] = sorted(archives, key=lambda a: a['name'])
    data['totals'] = {'files': len(records), 'uncompressed_bytes': sum(f['bytes'] for f in records),
                      'compressed_bytes': sum(a['bytes'] for a in archives)}
    (evidence / 'manifest.json').write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    (evidence / 'SHA256SUMS').write_text(''.join(f'{a["sha256"]}  {a["name"]}\n' for a in data['archives']))
    lines = ['# Evidence path index', '', 'Original bytes are retained in the archives below.',
             'Restore all original paths from the checkpoint directory:', '',
             '```sh', 'python3 checks/archive_evidence.py restore', '```', '',
             'See [README.md](README.md) for verification, isolated replay and reproducibility.', '',
             '| Archive | Original files | Compressed bytes | SHA-256 |', '| --- | ---: | ---: | --- |']
    for a in data['archives']:
        lines.append(f'| [{a["name"]}]({a["name"]}) | {a["files"]} | {a["bytes"]} | `{a["sha256"]}` |')
    lines += ['', '## Original paths', '', 'Each heading is a stable per-file link target. Paths retain their original spelling.', '']
    for f in data['files']:
        lines += [f'<a id="{anchor(f["path"])}"></a>', f'### `{f["path"]}`', '',
                  f'Archive: [{f["archive"]}]({f["archive"]}); bytes: {f["bytes"]}; assignment: {f["assignment"]}.',
                  f'SHA-256: `{f["sha256"]}`.', '']
    (evidence / 'MANIFEST.md').write_text('\n'.join(lines))
    verify(evidence, source)


def anchor(name):
    return 'log-' + hashlib.sha256(name.encode()).hexdigest()[:16]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['create', 'inspect', 'verify', 'restore'])
    parser.add_argument('--evidence', type=Path, default=BASE / 'evidence')
    parser.add_argument('--source', type=Path, default=BASE)
    parser.add_argument('--from-manifest', type=Path)
    parser.add_argument('--originals', type=Path, help='Also compare original/restored file bytes')
    parser.add_argument('--dest', type=Path, default=BASE, help='Checkpoint directory to restore into')
    parser.add_argument('--overwrite', action='store_true', help='Explicitly replace differing regular files')
    args = parser.parse_args()
    if args.mode == 'create':
        create(args.source.absolute(), args.evidence.absolute(), args.from_manifest)
    elif args.mode == 'restore':
        restore(args.evidence.absolute(), args.dest.absolute(), args.overwrite)
    else:
        data = verify(args.evidence.absolute(), args.originals)
        if args.mode == 'inspect':
            print(json.dumps({'source_HEAD': data['source_HEAD'], 'totals': data['totals'],
                              'archives': data['archives']}, indent=2))


if __name__ == '__main__':
    main()
