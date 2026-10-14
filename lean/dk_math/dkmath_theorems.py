#!/usr/bin/env python3
"""DkMath source-wide Lean declaration finder. Standard library only.

This is a SOURCE inventory, not Lean elaboration: namespace resolution and
signature extraction are best-effort. Verify facts with Lean kernel.
"""
from __future__ import annotations

import argparse
from collections import Counter
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import sys

DECL = re.compile(r'^\s*(?:(?:private|protected|noncomputable|irreducible|partial|unsafe|local|scoped)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|constant|instance|example)\s+([^\s(:\[{]+)?')
NAMESPACE = re.compile(r'^\s*(namespace|section)\s*([^\n]*)$')
END = re.compile(r'^\s*end(?:\s+([^\s]+))?\s*$')
IMPORT = re.compile(r'^\s*import\s+(.+)$')
MAX_HEADER_LINES = 45


def remove_comments(text: str) -> str:
    """Preserve line count while stripping Lean's nested comments and quoted strings."""
    result = []
    i, depth, in_string = 0, 0, False
    while i < len(text):
        ch = text[i]
        following = text[i:i+2]
        if depth:
            if following == '/-':
                depth += 1; result.extend('  '); i += 2; continue
            if following == '-/':
                depth -= 1; result.extend('  '); i += 2; continue
            result.append('\n' if ch == '\n' else ' ')
            i += 1; continue
        if in_string:
            if ch == '\\' and i + 1 < len(text):
                result.extend('  '); i += 2; continue
            if ch == '"':
                in_string = False
            result.append('\n' if ch == '\n' else ' ')
            i += 1; continue
        if following == '/-':
            depth = 1; result.extend('  '); i += 2; continue
        if following == '--':
            while i < len(text) and text[i] != '\n':
                result.append(' '); i += 1
            continue
        if ch == '"':
            in_string = True
            result.append(' '); i += 1; continue
        result.append(ch); i += 1
    return ''.join(result)


def scan(file: Path, root: Path):
    raw = file.read_text(encoding='utf-8', errors='replace')
    lines = raw.splitlines()
    cleaned = remove_comments(raw).splitlines()
    path = file.relative_to(root).as_posix()
    module = path[:-5].replace('/', '.')
    imports = []
    for l in cleaned:
        m = IMPORT.match(l)
        if m:
            imports.extend(m.group(1).strip().split())
    # Frames [name, kind] allow balanced sections and nested namespaces.
    frames = []
    declarations = []
    for ix, line in enumerate(cleaned):
        nm = NAMESPACE.match(line)
        if nm:
            kind, name = nm.group(1), nm.group(2).strip()
            frames.append((name, kind))
            continue
        em = END.match(line)
        if em:
            name = em.group(1)
            if name:
                pos = next((i for i in range(len(frames)-1, -1, -1)
                            if frames[i][0] == name), None)
                if pos is not None:
                    frames = frames[:pos]
            elif frames:
                frames.pop()
            continue
        m = DECL.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2) or ''
        if not name or name in ('where', ':=', 'by'):
            # Some instances are unnamed; don't invent their identity.
            continue
        names = [n for n, k in frames if k == 'namespace' and n]
        qualified = '.'.join(names + [name])
        # Take signature up to proof body; never claim this is elaborated type.
        header_lines = []
        for j in range(ix, min(ix + MAX_HEADER_LINES, len(lines))):
            code = cleaned[j]
            orig = lines[j]
            cut = code.find(':=')
            if cut >= 0:
                header_lines.append(orig[:cut + 2])
                break
            header_lines.append(orig)
            if j > ix and (code.strip().startswith('| ') or code.strip() == 'where'):
                break
        signature = '\n'.join(header_lines).strip()
        declarations.append((qualified, name, kind, path, module, ix + 1,
                             signature, '\n'.join(lines[ix: min(ix+6, len(lines))])))
    return declarations, imports, len(lines), hashlib.sha256(raw.encode('utf-8')).hexdigest()


def connect(path: Path):
    c = sqlite3.connect(path)
    c.row_factory = sqlite3.Row
    return c


def build(args):
    root = args.root.resolve()
    if not (root / 'DkMath').is_dir():
        raise ValueError(f'Not a DkMath repository root: {root}')
    db = args.db.resolve()
    db.parent.mkdir(parents=True, exist_ok=True)
    if db.exists():
        db.unlink()
    c = connect(db)
    c.executescript('''
        CREATE TABLE declarations (
            id INTEGER PRIMARY KEY, qualified TEXT, name TEXT, kind TEXT,
            path TEXT, module TEXT, line INTEGER, signature TEXT, excerpt TEXT);
        CREATE TABLE modules (
            path TEXT PRIMARY KEY, module TEXT, line_count INTEGER,
            sha256 TEXT, imports_json TEXT);
        CREATE INDEX ix_name ON declarations(name);
        CREATE INDEX ix_qualified ON declarations(qualified);
        CREATE INDEX ix_path ON declarations(path);
        CREATE INDEX ix_kind ON declarations(kind);
        CREATE VIRTUAL TABLE declarations_fts USING fts5(
            qualified, name, module, signature,
            content='declarations', content_rowid='id', tokenize='unicode61');
        CREATE TABLE metadata (key TEXT PRIMARY KEY, value TEXT);
    ''')
    nfiles = ndecl = 0
    for file in sorted((root / 'DkMath').rglob('*.lean')):
        decs, imports, line_count, digest = scan(file, root)
        c.executemany('''INSERT INTO declarations
           (qualified,name,kind,path,module,line,signature,excerpt)
           VALUES (?,?,?,?,?,?,?,?)''', decs)
        rel = file.relative_to(root).as_posix()
        c.execute('INSERT INTO modules VALUES (?,?,?,?,?)',
                  (rel, rel[:-5].replace('/', '.'), line_count, digest, json.dumps(imports)))
        nfiles += 1; ndecl += len(decs)
    c.execute("INSERT INTO declarations_fts(declarations_fts) VALUES('rebuild')")
    c.executemany('INSERT INTO metadata VALUES (?,?)', [
        ('root', str(root)), ('built_at', dt.datetime.now(dt.timezone.utc).isoformat()),
        ('source_kind', 'Lean source heuristic (not kernel checked)'),
    ])
    c.commit(); c.close()
    print(f'Indexed {nfiles:,} Lean files, {ndecl:,} named declarations → {db}')


def print_row(row, full=False):
    print(f"{row['qualified']} [{row['kind']}]  {row['path']}:{row['line']}")
    if full:
        print(row['signature'] or '(no signature recovered)')
        print()


def search(args):
    c = connect(args.db)
    wheres, vals = [], []
    if args.text:
        words = args.text.split()
        for word in words:
            wheres.append('(declarations.qualified LIKE ? OR declarations.name LIKE ? OR declarations.signature LIKE ? OR declarations.module LIKE ?)')
            vals.extend([f'%{word}%'] * 4)
    if args.name:
        wheres.append('declarations.name LIKE ?'); vals.append('%' + args.name + '%')
    if args.module:
        wheres.append('declarations.module LIKE ?'); vals.append('%' + args.module + '%')
    if args.kind:
        wheres.append('declarations.kind = ?'); vals.append(args.kind)
    fts_join = ''
    if args.fts and args.text:
        tokens = re.findall(r'\w+', args.text, flags=re.UNICODE)
        if tokens:
            fts_join = ' JOIN declarations_fts ON declarations.id = declarations_fts.rowid'
            wheres.append('declarations_fts MATCH ?')
            vals.append(' AND '.join('\"' + word.replace('\"', '') + '\"*' for word in tokens))
    sql = 'SELECT declarations.* FROM declarations' + fts_join
    if wheres:
        sql += ' WHERE ' + ' AND '.join(wheres)
    sql += ' ORDER BY CASE WHEN declarations.name = ? THEN 0 ELSE 1 END, length(declarations.name), declarations.path, declarations.line LIMIT ?'
    vals += [args.text or args.name or '', args.limit]
    rows = c.execute(sql, vals).fetchall()
    for row in rows: print_row(row, args.full)
    print(f'{len(rows)} shown (limit {args.limit})')


def show(args):
    c = connect(args.db)
    rows = c.execute('''SELECT * FROM declarations
        WHERE qualified = ? OR name = ? ORDER BY path,line''',
        (args.symbol, args.symbol)).fetchall()
    if not rows:
        print('Symbol not found:', args.symbol, file=sys.stderr); sys.exit(1)
    for row in rows: print_row(row, True)


def stats(args):
    c = connect(args.db)
    n = c.execute('SELECT count(*) FROM declarations').fetchone()[0]
    nf, nl = c.execute('SELECT count(*),sum(line_count) FROM modules').fetchone()
    print(f'Lean modules: {nf:,}; source lines: {nl:,}; named declarations (heuristic): {n:,}')
    print('By kind:')
    for kind, count in c.execute('SELECT kind,count(*) FROM declarations GROUP BY kind ORDER BY count(*) DESC'):
        print(f'  {kind:12} {count:6,}')
    print('By top-level directory:')
    for branch, count in c.execute('''SELECT substr(path,8,instr(substr(path,8),'/')-1) AS branch,
        count(*) FROM declarations WHERE path LIKE 'DkMath/%/%' GROUP BY branch
        ORDER BY count(*) DESC LIMIT 25'''):
        print(f'  {branch:18} {count:6,}')


def export(args):
    c = connect(args.db)
    rows = c.execute('SELECT * FROM declarations ORDER BY path,line')
    # JSONL supports multiline signatures and easy import by Codex / jq.
    with args.output.open('w', encoding='utf-8') as out:
        for r in rows:
            out.write(json.dumps({k: r[k] for k in r.keys() if k != 'excerpt'},
                                 ensure_ascii=False) + '\n')
    print(f'Exported {args.output}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--db', type=Path, default=Path('dkmath-theorems.sqlite3'))
    sub = parser.add_subparsers(dest='command', required=True)
    b = sub.add_parser('build', help='index a local DkMath repository')
    b.add_argument('--root', type=Path, required=True)
    s = sub.add_parser('search', help='case-insensitive substring search on signatures and names')
    s.add_argument('text', nargs='?', default='')
    s.add_argument('--name'); s.add_argument('--module'); s.add_argument('--kind')
    s.add_argument('--fts', action='store_true', help='also require indexed FTS5 term-prefix matching')
    s.add_argument('--limit', type=int, default=30); s.add_argument('--full', action='store_true')
    h = sub.add_parser('show', help='print a declaration source header')
    h.add_argument('symbol')
    sub.add_parser('stats', help='inventory summary')
    e = sub.add_parser('export', help='export declarations as newline-delimited JSON')
    e.add_argument('output', type=Path)
    args = parser.parse_args()
    try:
        {'build': build, 'search': search, 'show': show, 'stats': stats, 'export': export}[args.command](args)
    except (sqlite3.Error, OSError, ValueError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
